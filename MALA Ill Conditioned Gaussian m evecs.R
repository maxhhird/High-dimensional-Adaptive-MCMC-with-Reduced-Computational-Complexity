require(mvtnorm)
require(pracma)
require(expm)
require(coda)
require(sjPlot)
require(ggplot2)

hard_gaussian_covariance_by_spectrum <- function(d, spectrum) {
  if (d == 1) {
    return(matrix(spectrum, nrow = 1, ncol = 1))
  }
  v_1 <- (d ^ (-0.5)) * rep(1, d);
  vs <- matrix(v_1, nrow = d, ncol = 1)
  D <- diag(spectrum)
  Q <- svd(vs, nu = d)$u
  Sigma <- Q %*% D %*% t(Q)
  return(Sigma)
}

sin_squared_distance <- function(v, w) {
  # normalise:
  v <- v / sqrt(sum(v ^ 2))
  w <- w / sqrt(sum(w ^ 2))
  
  return(1 - sum(v * w) ^ 2)
}

Q_m <- function(vs) {
  vs <- as.matrix(vs)
  d <- nrow(vs); m <- ncol(vs)
  if (d == m) {
    return(vs)
  }
  Q_m <- diag(d)
  for (i in 1:m) {
    # e_i <- diag(d)[, i]; diff <- (Q_m %*% e_i) - vs[, i]
    e_i <- diag(d)[, i]; diff <- Q_m[, i] - vs[, i]
    # Q_m <- (diag(d) - 2 * (1 / sum(diff ^ 2)) * tcrossprod(diff)) %*% Q_m
    Q_m <- Q_m - (2 / sum(diff ^ 2)) * (diff %*% crossprod(diff, Q_m))
  }
  return(Q_m)
}

ESS_k_chains <- function(chains) {
  d <- nrow(chains[, , 1]); k <- ncol(chains[, , 1]);
  nits <- dim(chains)[3]
  # check whether k = 1
  if (is.null(d)) {
    d <- length(chains[, , 1])
    k <- 1
  }
  ESSs <- rep(0, d)
  for (i in 1:k) {
    chain <- chains[1:d, i, floor(nits / 2):nits]
    ESSs <- ESSs + effectiveSize(as.mcmc(t(chain)))
  }
  return(ESSs)
}

grad_log_pi_normal <- function(X, mu_pi, Sigma_pi_inv) {
  # X is an d x k matrix whose columns are the states at which to evaluate the density
  centred_X <- X - mu_pi
  return(-Sigma_pi_inv %*% centred_X)
}

mala_proposal_ratio <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, LLT_inv) {
  # X is an d x k matrix whose columns are the states
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  I_1 <- diag(t(D_1) %*% LLT_inv %*% D_1)
  I_2 <- diag(t(D_2) %*% LLT_inv %*% D_2)
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
}

mala_proposal_ratio_Q_D <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, Q, D) {
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  I_1 <- diag(t(D_1) %*% Q %*% ((D ^ (-1)) * t(Q)) %*% D_1)
  I_2 <- diag(t(D_2) %*% Q %*% ((D ^ (-1)) * t(Q)) %*% D_2)
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
}

mala_normal <- function(X, sigma, mu_pi, Sigma_pi, Sigma_pi_inv, nits, v_1, v_2, v_3) {
  d <- nrow(X); k <- ncol(X)
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  
  chains <- array(dim = c(d, k, nits + 1))
  sigmas <- vector(length = nits + 1)
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  chains[, , 1] <- X
  sigmas[1] <- sigma
  sin_squareds[1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                         sin_squared_distance(diag(d)[, 1], v_2),
                         sin_squared_distance(diag(d)[, 1], v_3))
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * grad_log_pi_X
    xi <- matrix(rnorm(d * k), nrow = d)
    X_prop <- X + drift + sigma * xi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    
    # Accept/Reject
    target_ratios <- pi_props / pi_currs
    proposal_ratios <- mala_proposal_ratio(X, X_prop, sigma, xi, grad_log_pi_X_prop, diag(d))
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    # global scale adaptation
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- X
    sigmas[i + 1] <- sigma
    sin_squareds[i + 1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                           sin_squared_distance(diag(d)[, 1], v_2),
                           sin_squared_distance(diag(d)[, 1], v_3))
  }
  return(list(chains = chains, sigmas = sigmas, sin_squareds = sin_squareds))
}

mala_normal_diagonal <- function(X, sigma, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3) {
  d <- nrow(X); k <- ncol(X)
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  mu <- rowMeans(X)
  
  chains <- array(dim = c(d, k, nits + 1))
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  chains[, , 1] <- X
  sin_squareds[1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                         sin_squared_distance(diag(d)[, 1], v_2),
                         sin_squared_distance(diag(d)[, 1], v_3))
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * D * grad_log_pi_X
    Lxi <- sqrt(D) * matrix(rnorm(d * k), nrow = d)
    X_prop <- X + drift + sigma * Lxi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    LLTgrad_log_pi_X_prop <- D * grad_log_pi_X_prop
    
    # Accept/Reject
    target_ratios <- pi_props / pi_currs
    proposal_ratios <- mala_proposal_ratio(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, diag(D ^ -1))
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    # Adaptation
    mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(X) - mu)
    gradient <- rep(0, d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (X[, j] - mu) ^ 2
    }
    D <- D + (1 / (i + 1) ^ kappa) * (gradient - D)
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- X
    sin_squareds[i + 1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                               sin_squared_distance(diag(d)[, 1], v_2),
                               sin_squared_distance(diag(d)[, 1], v_3))
  }
  return(list(chains = chains, D = D, mu = mu, sin_squareds = sin_squareds))
}

mala_normal_diag_plus_LR <- function(X, sigma, D, V, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3) {
  d <- nrow(X); k <- ncol(X)
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  
  L <- D + V %*% t(V); LLT <- L %*% L
  LLT_inv <- solve(L) %*% solve(L)
  eigen_object <- eigen(LLT); v_1_LLT <- eigen_object$vectors[, 1];
  v_2_LLT <- eigen_object$vectors[, 2]; v_3_LLT <- eigen_object$vectors[, 3]

  sin_dist_1 <- sin_squared_distance(v_1, v_1_LLT)
  sin_dist_2 <- sin_squared_distance(v_2, v_2_LLT)
  sin_dist_3 <- sin_squared_distance(v_3, v_3_LLT)
  
  chains <- array(dim = c(d, k, nits + 1))
  sigmas <- vector(length = nits + 1)
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  
  chains[, , 1] <- X; sigmas[1] <- sigma;
  sin_squareds[1, ] <- c(sin_dist_1,
                         sin_dist_2,
                         sin_dist_3)
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * ((D ^ 2) %*% grad_log_pi_X + D %*% (V %*% (t(V) %*% grad_log_pi_X)) + V %*% (t(V) %*% (D %*% grad_log_pi_X)) + V %*% ((t(V) %*% V) %*% (t(V) %*% grad_log_pi_X)))
    xi <- matrix(rnorm(d * k), nrow = d)
    Lxi <- D %*% xi + V %*% (t(V) %*% xi)
    X_prop <- X + drift + sigma * Lxi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    LLTgrad_log_pi_X_prop <- (D ^ 2) %*% grad_log_pi_X_prop + D %*% (V %*% (t(V) %*% grad_log_pi_X_prop)) + V %*% (t(V) %*% (D %*% grad_log_pi_X_prop)) + V %*% ((t(V) %*% V) %*% (t(V) %*% grad_log_pi_X_prop))
    
    target_ratios <- pi_props / pi_currs
    proposal_ratios <- mala_proposal_ratio(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, LLT_inv)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    # global scale adaptation
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- X
    sigmas[i + 1] <- sigma
    sin_squareds[i + 1, ] <- c(sin_dist_1,
                               sin_dist_2,
                               sin_dist_3)
  }
  return(list(chains = chains, sigmas = sigmas, sin_squareds = sin_squareds))
}

mala_normal_dense <- function(X, sigma, L, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3, adapt) {
  d <- nrow(X); k <- ncol(X)
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  mu <- rowMeans(X); LLT <- L %*% t(L)
  
  eigen_object <- eigen(LLT); v_1_LLT <- eigen_object$vectors[, 1];
  v_2_LLT <- eigen_object$vectors[, 2]; v_3_LLT <- eigen_object$vectors[, 3]
  sin_dist_1 <- sin_squared_distance(v_1, v_1_LLT)
  sin_dist_2 <- sin_squared_distance(v_2, v_2_LLT)
  sin_dist_3 <- sin_squared_distance(v_3, v_3_LLT)
  
  chains <- array(dim = c(d, k, nits + 1))
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_offs <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  
  chains[, , 1] <- X
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * LLT[1, 1]
  Sigma_offs[1] <- (sigma ^ 2) * LLT[3, 4]
  Sigma_ds[1] <- (sigma ^ 2) * LLT[d, d]
  mus[1, ] <- mu
  sin_squareds[1, ] <- c(sin_dist_1,
                         sin_dist_2,
                         sin_dist_3)
  
  for (i in 1:nits) {
    L_inv <- solve(L); LLT_inv <- t(L_inv) %*% L_inv
    
    # Propose
    drift <- ((sigma ^ 2) / 2) * (LLT %*% grad_log_pi_X)
    Lxi <- L %*% matrix(rnorm(d * k), nrow = d)
    X_prop <- X + drift + sigma * Lxi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    LLTgrad_log_pi_X_prop <- LLT %*% grad_log_pi_X_prop
    
    # Accept/Reject
    target_ratios <- pi_props / pi_currs
    proposal_ratios <- mala_proposal_ratio(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, LLT_inv)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    if (adapt) {
      # Adapt
      mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(X) - mu)
      gradient <- matrix(0, nrow = d, ncol = d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * (X[, j] - mu) %*% t(X[, j] - mu)
      }
      LLT <- LLT + (1 / (i + 1) ^ kappa) * (gradient - LLT)
      min_eval <- min(eigen(LLT, symmetric = TRUE, only.values = TRUE)$values)
      if (min_eval < 0) {
        LLT <- LLT + (abs(min_eval) + 0.1) * diag(d)
      }
      L <- t(chol(LLT))
    }
    
    # adapt the global scale
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- X
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * LLT[1, 1]
    Sigma_offs[i + 1] <- (sigma ^ 2) * LLT[3, 4]
    Sigma_ds[i + 1] <- (sigma ^ 2) * LLT[d, d]
    mus[i + 1, ] <- mu
    
    # eigen_object <- eigen(LLT); v_1_LLT <- eigen_object$vectors[, 1];
    # v_2_LLT <- eigen_object$vectors[, 2]; v_3_LLT <- eigen_object$vectors[, 3]
    # sin_dist_1 <- sin_squared_distance(v_1, v_1_LLT)
    # sin_dist_2 <- sin_squared_distance(v_2, v_2_LLT)
    # sin_dist_3 <- sin_squared_distance(v_3, v_3_LLT)
    # 
    # sin_squareds[i + 1, ] <- c(sin_dist_1,
    #                        sin_dist_2,
    #                        sin_dist_3)
  }
  return(list(chains = chains, LLT = LLT, mu = mu, sigmas = sigmas, Sigma_ones = Sigma_ones, Sigma_offs = Sigma_offs, mus = mus, Sigma_ds = Sigma_ds, sin_squareds = sin_squareds))
}

mala_normal_m_evecs <- function(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3) {
  d <- nrow(X); k <- ncol(X);
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  mu <- rowMeans(X); tilde_Q <- Q; tilde_D <- D
  
  chains <- array(dim = c(d, k, nits + 1))
  Ds <- matrix(nrow = nits + 1, ncol = d)
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  Sigma_offs <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  v1s <- matrix(nrow = nits + 1, ncol = d)
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  chains[, , 1] <- X
  Ds[1, ] <- D
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
  Sigma_ds[1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
  Sigma_offs[1] <- (sigma ^ 2) * sum(Q[3, ] * D * Q[4, ])
  mus[1, ] <- mu
  v1s[1, ] <- Q[, 1]
  sin_squareds[1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                                           sin_squared_distance(diag(d)[, 2], v_2),
                                           sin_squared_distance(diag(d)[, 3], v_3))
  
  for (i in 1:nits) {
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_X))
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    X_prop <- X + drift + sigma * Lxi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    LLTgrad_log_pi_X_prop <- Q %*% (D * crossprod(Q, grad_log_pi_X_prop))
    
    # Accept/Reject
    target_ratios <- pi_props / pi_currs;
    proposal_ratios <- mala_proposal_ratio_Q_D(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, Q, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    # Adapt
    mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(X) - mu)
    gradient <- matrix(0, ncol = d, nrow = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * tcrossprod(X[, j] - mu, X[, j] - mu)
    }
    gamma <- c / (i ^ kappa)
    
    tilde_Q[, 1:m] <- tilde_Q[, 1:m] + gamma * crossprod(gradient, tilde_Q[, 1:m])
    if (m == 1) {
      tilde_Q[, 1] <- tilde_Q[, 1] / sqrt(sum(tilde_Q[, 1] ^ 2))
    } else {
      tilde_Q[, 1:m] <- t((sqrt(colSums(tilde_Q[, 1:m] * tilde_Q[, 1:m])) ^ (-1)) * t(tilde_Q[, 1:m]))
    }
    if (m > 1 & i %% p == 0) {
      # Orthonormalise the first 1 to m columns
      tilde_Q[, 1:m] <- gramSchmidt(tilde_Q[, 1:m])$Q
    }
    # Orthonormalise fully
    tilde_Q <- Q_m(tilde_Q[, 1:m])
    
    # Scale and diagonal
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    X_tilde <- crossprod(tilde_Q, X)
    mu_tilde <- crossprod(tilde_Q, mu)
    gradient <- rep(0, d)
    # 
    # # Q_inv <- solve(Q)
    # # Theta_tilde <- Q_inv %*% Theta
    # # mu_tilde <- Q_inv %*% mu
    # # gradient <- rep(0, d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (X_tilde[, j] - mu_tilde) ^ 2
    }
    tilde_D <- as.vector(tilde_D + (1 / (i + 1) ^ kappa) * (gradient - tilde_D))
    if (i %% I == 0) {
      D <- tilde_D; Q <- tilde_Q
    }
    # Storage
    chains[, , i + 1] <- X
    # if (i > 9500) {browser()}
    Ds[i + 1, ] <- D
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
    Sigma_ds[i + 1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
    Sigma_offs[i + 1] <- (sigma ^ 2) * sum(Q[3, ] * D * Q[4, ])
    mus[i + 1, ] <- mu
    v1s[i + 1, ] <- Q[, 1]
    sin_squareds[i + 1, ] <- c(sin_squared_distance(Q[, 1], v_1),
                           sin_squared_distance(Q[, 2], v_2),
                           sin_squared_distance(Q[, 3], v_3))
  }
  return(list(chains = chains, Ds = Ds, sigmas = sigmas, Sigma_ones = Sigma_ones, Sigma_ds = Sigma_ds, Sigma_offs = Sigma_offs, mus = mus, v1s = v1s, sin_squareds = sin_squareds))
}

mala_normal_m_evecs_identity <- function(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3) {
  d <- nrow(X); k <- ncol(X);
  pi_currs <- dmvnorm(t(X), mean = mu_pi, sigma = Sigma_pi)
  grad_log_pi_X <- grad_log_pi_normal(X, mu_pi, Sigma_pi_inv)
  mu <- rowMeans(X); tilde_Q <- Q; tilde_D <- D
  
  chains <- array(dim = c(d, k, nits + 1))
  Ds <- matrix(nrow = nits + 1, ncol = d)
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  Sigma_offs <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  v1s <- matrix(nrow = nits + 1, ncol = d)
  sin_squareds <- matrix(nrow = nits + 1, ncol = 3)
  chains[, , 1] <- X
  Ds[1, ] <- D
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
  Sigma_ds[1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
  Sigma_offs[1] <- (sigma ^ 2) * sum(Q[3, ] * D * Q[4, ])
  mus[1, ] <- mu
  v1s[1, ] <- Q[, 1]
  sin_squareds[1, ] <- c(sin_squared_distance(diag(d)[, 1], v_1),
                         sin_squared_distance(diag(d)[, 2], v_2),
                         sin_squared_distance(diag(d)[, 3], v_3))
  
  for (i in 1:nits) {
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_X))
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    X_prop <- X + drift + sigma * Lxi
    pi_props <- dmvnorm(t(X_prop), mean = mu_pi, sigma = Sigma_pi)
    grad_log_pi_X_prop <- grad_log_pi_normal(X_prop, mu_pi, Sigma_pi_inv)
    LLTgrad_log_pi_X_prop <- Q %*% (D * crossprod(Q, grad_log_pi_X_prop))
    
    # Accept/Reject
    target_ratios <- pi_props / pi_currs;
    proposal_ratios <- mala_proposal_ratio_Q_D(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, Q, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    Us <- runif(k); mask <- Us < alphas
    
    X[, mask] <- X_prop[, mask]; pi_currs[mask] <- pi_props[mask]
    grad_log_pi_X[, mask] <- grad_log_pi_X_prop[, mask]
    
    # Adapt
    mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(X) - mu)
    gradient <- matrix(0, ncol = d, nrow = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * tcrossprod(X[, j] - mu, X[, j] - mu)
    }
    gamma <- c / (i ^ kappa)
    
    tilde_Q[, 1:m] <- tilde_Q[, 1:m] + gamma * crossprod(gradient, tilde_Q[, 1:m])
    if (m == 1) {
      tilde_Q[, 1] <- tilde_Q[, 1] / sqrt(sum(tilde_Q[, 1] ^ 2))
    } else {
      tilde_Q[, 1:m] <- t((sqrt(colSums(tilde_Q[, 1:m] * tilde_Q[, 1:m])) ^ (-1)) * t(tilde_Q[, 1:m]))
    }
    if (m > 1 & i %% p == 0) {
      # Orthonormalise the first 1 to m columns
      tilde_Q[, 1:m] <- gramSchmidt(tilde_Q[, 1:m])$Q
    }
    # Orthonormalise fully
    tilde_Q <- Q_m(tilde_Q[, 1:m])
    
    # Scale and diagonal
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    X_tilde <- crossprod(tilde_Q, X)
    mu_tilde <- crossprod(tilde_Q, mu)
    gradient <- rep(0, d)
    # 
    # # Q_inv <- solve(Q)
    # # Theta_tilde <- Q_inv %*% Theta
    # # mu_tilde <- Q_inv %*% mu
    # # gradient <- rep(0, d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (X_tilde[, j] - mu_tilde) ^ 2
    }
    tilde_D <- as.vector(tilde_D + (1 / (i + 1) ^ kappa) * (gradient - tilde_D))
    # Make the final d - m diagonal elements of D equal to 1
    tilde_D[(m + 1):d] <- 1
    if (i %% I == 0) {
      D <- tilde_D; Q <- tilde_Q
    }
    # Storage
    chains[, , i + 1] <- X
    # if (i > 9500) {browser()}
    Ds[i + 1, ] <- D
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
    Sigma_ds[i + 1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
    Sigma_offs[i + 1] <- (sigma ^ 2) * sum(Q[3, ] * D * Q[4, ])
    mus[i + 1, ] <- mu
    v1s[i + 1, ] <- Q[, 1]
    sin_squareds[i + 1, ] <- c(sin_squared_distance(Q[, 1], v_1),
                               sin_squared_distance(Q[, 2], v_2),
                               sin_squared_distance(Q[, 3], v_3))
  }
  return(list(chains = chains, Ds = Ds, sigmas = sigmas, Sigma_ones = Sigma_ones, Sigma_ds = Sigma_ds, Sigma_offs = Sigma_offs, mus = mus, v1s = v1s, sin_squareds = sin_squareds))
}

reverse_KL <- function(batch, mu, D, V, mu_pi, Sigma_pi) {
  LLT <- D ^ 2 + V %*% (t(V) %*% D) + (D %*% V) %*% t(V) + V %*% (t(V) %*% V) %*% t(V)
  # estimate the reverse KL
  batch_size <- nrow(batch)
  log_ratios <- dmvnorm(batch, mean = mu, sigma = LLT, log = TRUE) - dmvnorm(batch, mean = mu_pi, sigma = Sigma_pi, log = TRUE)
  return(mean(log_ratios))
}

KL_exact <- function(mu_1, Sigma_1, mu_2, Sigma_2) {
  Sigma_2_inv <- solve(Sigma_2)
  d <- length(mu_1)
  return(0.5 * (Trace(Sigma_2_inv %*% Sigma_1) - d + t(mu_2 - mu_1) %*% Sigma_2_inv %*% (mu_2 - mu_1) + log(det(Sigma_2)) - log(det(Sigma_1))))
}

reverse_KL_gradient_descent <- function(batch_size, mu, D, V, mu_pi, Sigma_pi, d, nits, mu_learn, delta_learn, V_learn) {
  KLs <- vector(length = nits); Sigma_pi_inv <- solve(Sigma_pi)
  lambda <- diag(D); delta <- sqrt(lambda)
  for (i in 1:nits) {
    L_inv <- diag_plus_LR_inverse(D, V)
    standard_batch <- matrix(rnorm(batch_size * d), ncol = batch_size)
    batch <- t(as.vector(mu) + D %*% standard_batch + V %*% (t(V) %*% standard_batch))
    
    L_grad <- reverse_KL_L_grad(batch, mu_pi, Sigma_pi_inv, L_inv)
    #L_grad <- reverse_KL_L_grad_true(Sigma_pi_inv, L_inv, D, V)
    mu <- mu - mu_learn * reverse_KL_mu_grad(batch, mu_pi, Sigma_pi_inv)
    delta <- delta - delta_learn * (delta * diag(L_grad))
    lambda <- delta ^ 2
    V <- V - V_learn * (L_grad + t(L_grad)) %*% V
    D <- diag(lambda)
    
    #KLs[i] <- reverse_KL(batch, mu, D, V, mu_pi, Sigma_pi)
  }
  return(list(KLs = KLs, mu = mu, D = D, V = V))
}

reverse_KL_L_grad <- function(batch, mu_pi, Sigma_pi_inv, L_inv) {
  batch_size <- nrow(batch); d <- length(mu_pi)
  grad <- matrix(0, ncol = d, nrow = d)
  for (b in 1:batch_size) {
    grad <- grad - outer(as.vector(grad_log_pi_normal(batch[b, ], mu_pi, Sigma_pi_inv)), as.vector(batch[b, ]))
  }
  grad <- grad - L_inv
  return(grad)
}

reverse_KL_L_grad_true <- function(Sigma_pi_inv, L_inv, D, V) {
  return(D %*% Sigma_pi_inv + V %*% (t(V) %*% Sigma_pi_inv) - L_inv)
}

reverse_KL_mu_grad <- function(batch, mu_pi, Sigma_pi_inv) {
  batch_size <- nrow(batch); d <- length(mu_pi)
  grad <- rep(0, d)
  for (b in 1:batch_size) {
    grad <- grad - (1 / batch_size) * grad_log_pi_normal(batch[b, ], mu_pi, Sigma_pi_inv)
  }
  return(grad)
}

diag_plus_LR_inverse <- function(D, V) {
  # Use the Woodbury Identity
  D_inv <- solve(D); m <- ncol(V);
  inner_inverse <- solve(diag(m) + t(V) %*% D_inv %*% V)
  return(D_inv - D_inv %*% V %*% inner_inverse %*% t(V) %*% D_inv)
}

BPaM <- function(bigT, B = 32, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi, lambda_0 = 1) {
  exact_KLs <- vector(length = bigT)
  d <- length(mu); K <- ncol(Lambda)
  for (t in 1:bigT) {
    lambda <- lambda_0 / t
    # 3:
    Z <- t(rmvnorm(n = B, mean = mu, sigma = Sigma))
    # 4:
    G <- grad_log_pi_normal(Z, mu_pi, Sigma_pi_inv)
    # 5:
    z_bar <- rowMeans(Z); g_bar <- rowMeans(G)
    # Subtraction works columnwise
    Z_centred <- Z - z_bar; G_centred <- G - g_bar
    C <- cov(t(Z)); Gamma <- cov(t(G))
    # 6:
    Q <- sqrt(lambda / B) * G_centred; Q <- cbind(Q, sqrt(lambda / (1 + lambda)) * g_bar)
    V <- Sigma + lambda * C + (lambda / (1 + lambda)) * outer(mu - z_bar, mu - z_bar)
    # 7:
    Sigma <- V - t(V) %*% Q %*% (pracma::pinv(0.5 * diag(B + 1) + expm::sqrtm(t(Q) %*% V %*% Q + 0.25 * diag(B + 1))) %^% 2) %*% t(Q) %*% V
    patch_out <- patch(Sigma, Lambda, Psi)
    Psi <- patch_out$Psi; Lambda <- patch_out$Lambda
    Sigma <- Psi + Lambda %*% t(Lambda)
    mu <- as.vector((1 / (lambda + 1)) * mu + (lambda / (lambda + 1)) * (Sigma %*% g_bar + z_bar))
    
    exact_KLs[t] <- KL_exact(mu, Sigma, mu_pi, Sigma_pi)
  }
  return(list(mu = mu, Sigma = Sigma, exact_KLs = exact_KLs, Psi = Psi, Lambda = Lambda))
}

BPaM_optimised <- function(bigT, B = 32, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi, lambda_0 = 10) {
  exact_KLs <- vector(length = bigT)
  d <- length(mu); K <- ncol(Lambda)
  for (t in 1:bigT) {
    lambda <- lambda_0
    # 3:
    # use the formula from Ong, Nott, and Smith 2018
    Z <- mu + sqrt(Psi) %*% t(rmvnorm(n = B, mean = rep(0, d), sigma = diag(d))) + Lambda %*% t(rmvnorm(n = B, mean = rep(0, K), sigma = diag(K)))
    # 4:
    G <- grad_log_pi_normal(Z, mu_pi, Sigma_pi_inv)
    # 5:
    z_bar <- rowMeans(Z); g_bar <- rowMeans(G)
    # Subtraction works columnwise
    Z_centred <- Z - z_bar; G_centred <- G - g_bar
    C <- cov(t(Z)); Gamma <- cov(t(G))
    # 6:
    Q <- sqrt(lambda / B) * G_centred; Q <- cbind(Q, sqrt(lambda / (1 + lambda)) * g_bar)
    R <- Lambda; R <- cbind(R, sqrt(lambda / B) * Z_centred); R <- cbind(R, sqrt(lambda / (1 + lambda)) * (mu - z_bar));
    H <- t(Psi) %*% Q + R %*% (t(R) %*% Q)
    M <- pracma::pinv(0.5 * diag(B + 1) + expm::sqrtm(t(H) %*% Q + 0.25 * diag(B + 1))) %^% 2
    patch_out <- patch_optimised(R, H, M, Lambda, Psi)
    Psi <- patch_out$Psi; Lambda <- patch_out$Lambda
    mu <- as.vector((1 / (lambda + 1)) * mu + (lambda / (lambda + 1)) * (Psi %*% g_bar + Lambda %*% (t(Lambda) %*% g_bar) + z_bar))
    
    #exact_KLs[t] <- KL_exact(mu, Psi + Lambda %*% t(Lambda), mu_pi, Sigma_pi)
  }
  return(list(mu = mu, Sigma = Psi + Lambda %*% t(Lambda), exact_KLs = exact_KLs, Psi = Psi, Lambda = Lambda))
}

patch_optimised <- function(R, H, M, Lambda, Psi, eta = 1.2, epsilon = 1e-4, N = 500) {
  d <- ncol(Sigma); K <- ncol(Lambda)
  Psi_old <- Psi
  initial_inverse <- solve(Psi + Lambda %*% t(Lambda))
  KL_old <- log(det(Lambda %*% t(Lambda) + Psi)) + Trace(initial_inverse %*% Psi_old + (initial_inverse %*% R) %*% t(R) - (initial_inverse %*% H) %*% (M %*% t(H)))
  for (tau in 1:N) {
    Psi_inv <- diag(1 / diag(Psi))
    beta <- t(Lambda) %*% Psi_inv %*% (diag(d) - Lambda %*% solve(diag(K) + t(Lambda) %*% Psi_inv %*% Lambda) %*% t(Lambda) %*% Psi_inv)
    Lambda_aux <- Psi_old %*% t(beta) + R %*% (t(R) %*% t(beta)) - H %*% (M %*% (t(H) %*% t(beta)))
    Lambda_new <- Lambda_aux %*% solve(beta %*% Lambda_aux + diag(K) - beta %*% Lambda)
    Psi_new <- diag(diag(Psi_old)) - diag(diag(Lambda_new %*% t(Lambda_aux)))
    for (i in 1:d) {
      Psi_new[i, i] <- Psi_new[i, i] + sum(R[i, ] ^ 2) - sum(H[i, ] * (M %*% H[i, ]))
    }
    Lambda <- (1 - eta) * Lambda + eta * Lambda_new
    Psi <- (1 - eta) * Psi + eta * Psi_new
    for (i in 1:d) {
      if (Psi[i, i] <= 0) {Psi[i, i] <- 1e-8;}
    }
    
    initial_inverse <- solve(Psi + Lambda %*% t(Lambda))
    
    KL_new <- log(det(Lambda %*% t(Lambda) + Psi)) + Trace(initial_inverse %*% Psi_old + (initial_inverse %*% R) %*% t(R) - (initial_inverse %*% H) %*% (M %*% t(H)))
    
    if (is.na(KL_new)) {browser()}
    if (abs(KL_new - KL_old) < epsilon) {
      break
    }
    KL_old <- KL_new
  }
  return(list(Psi = Psi, Lambda = Lambda))
}

patch <- function(Sigma, Lambda, Psi, eta = 1.2, epsilon = 1e-4, N = 500) {
  d <- ncol(Sigma); K <- ncol(Lambda)
  # 2:
  KL_old <- log(det(Lambda %*% t(Lambda) + Psi)) + Trace(solve(Lambda %*% t(Lambda) + Psi) %*% Sigma)
  # 3:
  for (tau in 1:N) {
    Psi_inv <- diag(1 / diag(Psi))
    # 4:
    beta <- t(Lambda) %*% Psi_inv %*% (diag(d) - Lambda %*% solve(diag(K) + t(Lambda) %*% Psi_inv %*% Lambda) %*% t(Lambda) %*% Psi_inv)
    # 5:
    Lambda_new <- Sigma %*% t(beta) %*% solve(beta %*% Sigma %*% t(beta) + diag(K) - beta %*% Lambda)
    # 6:
    Psi_new <- diag(diag((diag(d) - Lambda %*% beta) %*% Sigma))
    # 7:
    Lambda <- (1 - eta) * Lambda + eta * Lambda_new
    # 8:
    Psi <- (1 - eta) * Psi + eta * Psi_new
    for (i in 1:d) {
      if (Psi[i, i] <= 0) {Psi[i, i] <- 1e-8}
    }
    # 9:
    KL_new <- log(det(Lambda %*% t(Lambda) + Psi)) + Trace(solve(Lambda %*% t(Lambda) + Psi) %*% Sigma)
    # 10:
    if (is.na(KL_new)) {browser()}
    if (abs(KL_new - KL_old) < epsilon) {
      break
    }
    KL_old <- KL_new
  }
  return(list(Psi = Psi, Lambda = Lambda))
}

# Target Setup
d <- 200; no_significant_evals <- 3; significant_eval <- 100
significant_evals <- significant_eval + (significant_eval / (10 ^ 3)) * rnorm(no_significant_evals)
spectrum <- c(significant_evals, rep(0.1, d - no_significant_evals))

mu_pi <- rep(5, d); Sigma_pi <- hard_gaussian_covariance_by_spectrum(d, spectrum)
v_1 <- eigen(Sigma_pi)$vectors[, 1]; v_2 <- eigen(Sigma_pi)$vectors[, 2]; v_3 <- eigen(Sigma_pi)$vectors[, 3]
sqrt_Sigma_pi <- expm::sqrtm(Sigma_pi); Sigma_pi_inv <- solve(Sigma_pi)

# Diagonal + LR Target Setup
d <- 200; mu_pi <- rnorm(d); Psi_pi <- diag(runif(d)); K <- 32
Lambda_pi <- matrix(rnorm(K * d), nrow = d, ncol = K)
Sigma_pi <- Psi_pi + Lambda_pi %*% t(Lambda_pi)
v_1 <- eigen(Sigma_pi)$vectors[, 1]; v_2 <- eigen(Sigma_pi)$vectors[, 2]; v_3 <- eigen(Sigma_pi)$vectors[, 3]
sqrt_Sigma_pi <- expm::sqrtm(Sigma_pi); Sigma_pi_inv <- solve(Sigma_pi)
evals_pi <- eigen(Sigma_pi)$values
print("Target condition:")
print(max(evals_pi) / min(evals_pi))

df <- data.frame(target_evals = evals_pi, number = 1:d)

p <- ggplot(df, aes(x = number, y = log10(target_evals))) +
  geom_point(color = 'darkgreen') +
  labs(x = 'target eigenvalue', y = 'log_10(value)') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log_10(target covariance eigenvalues), d = 200")
p

save_plot('target_evals.svg', fig = p, width = 13, height = 6)

# Initialise the Markov chain
k <- 2; X <- matrix(mu_pi, ncol = k, nrow = d) + sqrt_Sigma_pi %*% matrix(rnorm(d * k), nrow = d)
nits_coeff <- 1000; nits <- max(10000, nits_coeff * d ^ 0.5); kappa <- 0.7; sigma <- 0.5 / (d ^ (1 / 4));

# No Adaptation
start_time <- Sys.time()
out1 <- mala_normal(X, sigma, mu_pi, Sigma_pi, Sigma_pi_inv, nits, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out1$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out1$sigmas)
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
plot(1:(nits + 1), out1$sin_squareds[, 1])
plot(1:(nits + 1), out1$sin_squareds[, 2])
plot(1:(nits + 1), out1$sin_squareds[, 3])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# Diagonal Adaptation
D <- rep(1, d)
start_time <- Sys.time()
out2 <- mala_normal_diagonal(X, sigma, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out2$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
plot(1:(nits + 1), out2$sin_squareds[, 1])
plot(1:(nits + 1), out2$sin_squareds[, 2])
plot(1:(nits + 1), out2$sin_squareds[, 3])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# Diagonal plus Low Rank adaptation
# [[d = 50 : delta_learn = 0.0005, V_learn = 0.00001], [d = 100 : delta_learn = 0.00001, V_learn = 0.000001], [d = 150 : delta_learn = 0.00001, V_learn = 0.000001], [d = 200 : delta_learn = 0.00001, V_learn = 0.000001]]
m <- 32; D <- diag(d); V <- matrix(0.1, nrow = d, ncol = m); batch_size <- 10; mu <- rep(0, d);
KL_nits <- 1000; mu_learn <- 0.001; delta_learn <- 0.00001; V_learn <- 0.000001

start_time <- Sys.time()
descent_out <- reverse_KL_gradient_descent(batch_size, mu, D, V, mu_pi, Sigma_pi, d, KL_nits, mu_learn, delta_learn, V_learn)

plot(x = 1:KL_nits, y = descent_out$KLs)
descent_LLT <- (descent_out$D + descent_out$V %*% t(descent_out$V)) %*% t(descent_out$D + descent_out$V %*% t(descent_out$V))
sin_squared_distance(v_1, eigen(descent_LLT)$vectors[, 1]);
sin_squared_distance(v_2, eigen(descent_LLT)$vectors[, 2]);
sin_squared_distance(v_3, eigen(descent_LLT)$vectors[, 3]);
eigen(descent_LLT)$values

outd <- mala_normal_diag_plus_LR(X, sigma, descent_out$D, descent_out$V, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- outd$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), outd$sigmas)
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
plot(1:(nits + 1), outd$sin_squareds[, 1])
plot(1:(nits + 1), outd$sin_squareds[, 2])
plot(1:(nits + 1), outd$sin_squareds[, 3])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# BPaM Adaptation
# [[d = 50 : lambda_0 = 10, bigT = 100], [d = 100 : lambda_0 = 10, bigT = 100], [d = 150 : lambda_10 = 10, bigT = 100], [d = 200 : lambda_0 = 10, bigT = 100]]
mu <- rep(0, d); Psi <- diag(runif(d)); m <- 32; lambda_0 <- 10
Lambda <- 0.01 * matrix(rnorm(m * d), ncol = m)
Sigma <- Psi + Lambda %*% t(Lambda);
bigT <- 100; B <- 32;

start_time <- Sys.time()
BPaM_out <- BPaM_optimised(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi, lambda_0)

plot(1:bigT, log10(BPaM_out$exact_KLs))
ssd <- sin_squared_distance(v_1, eigen(BPaM_out$Sigma)$vectors[, 1]);
sin_squared_distance(v_2, eigen(BPaM_out$Sigma)$vectors[, 2]);
sin_squared_distance(v_3, eigen(BPaM_out$Sigma)$vectors[, 3]);

outB <- mala_normal_diag_plus_LR(X, sigma, BPaM_out$Psi, BPaM_out$Lambda, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- outB$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), outB$sigmas)
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
plot(1:(nits + 1), outB$sin_squareds[, 1])
plot(1:(nits + 1), outB$sin_squareds[, 2])
plot(1:(nits + 1), outB$sin_squareds[, 3])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# Dense Adaptation
L <- diag(d)
start_time <- Sys.time()
out3 <- mala_normal_dense(X, sigma, L, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3, TRUE)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out3$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out3$sigmas)
plot(1:(nits + 1), out3$mus[, 1])
plot(1:(nits + 1), out3$Sigma_ones)
plot(1:(nits + 1), out3$Sigma_offs)
plot(1:(nits + 1), out3$Sigma_ds)
acf(as.mcmc(out3$chain[1, 1, 1:(nits + 1)]))
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
plot(1:(nits + 1), out3$sin_squareds[, 1])
plot(1:(nits + 1), out3$sin_squareds[, 2])
plot(1:(nits + 1), out3$sin_squareds[, 3])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# Eigen Adaptation
D <- rep(1, d); Q <- diag(d); c <- 1; p <- 1; m <- 3; I <- 1
start_time <- Sys.time()
out4 <- mala_normal_m_evecs(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out4$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out4$sigmas)
plot(1:(nits + 1), out4$mus[, 1])
plot(1:(nits + 1), out4$Sigma_ones)
plot(1:(nits + 1), out4$Sigma_offs)
plot(1:(nits + 1), out4$Sigma_ds)
plot(1:(nits + 1), out4$Ds[, 1])
plot(1:(nits + 1), out4$v1s[, 1])
plot(1:(nits + 1), out4$sin_squareds[, 1])
plot(1:(nits + 1), out4$sin_squareds[, 2])
plot(1:(nits + 1), out4$sin_squareds[, 3])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

# Eigen Adaptation, final d - m elements of D are fixed @ 1
D <- rep(1, d); Q <- diag(d); c <- 1; p <- 1; m <- 3; I <- 1
start_time <- Sys.time()
out5 <- mala_normal_m_evecs_identity(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out5$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out5$sigmas)
plot(1:(nits + 1), out5$mus[, 1])
plot(1:(nits + 1), out5$Sigma_ones)
plot(1:(nits + 1), out5$Sigma_offs)
plot(1:(nits + 1), out5$Sigma_ds)
plot(1:(nits + 1), out5$Ds[, 1])
plot(1:(nits + 1), out5$v1s[, 1])
plot(1:(nits + 1), out5$sin_squareds[, 1])
plot(1:(nits + 1), out5$sin_squareds[, 2])
plot(1:(nits + 1), out5$sin_squareds[, 3])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

df <- data.frame(type = c(rep('none', nits + 1),
                          rep('diagonal', nits + 1),
                          rep('diagonal + LR', nits + 1),
                          rep('BPaM', nits + 1),
                          rep('dense', nits + 1),
                          rep('eigen', nits + 1),
                          rep('eigen_identity', nits + 1)),
                 sin_squared = c(out1$sin_squareds[, 1],
                                 out2$sin_squareds[, 1],
                                 outd$sin_squareds[, 1],
                                 rep(ssd, nits + 1),
                                 out3$sin_squareds[, 1],
                                 out4$sin_squareds[, 1],
                                 out5$sin_squareds[, 1]),
                 iteration = c(1:(nits + 1),
                               1:(nits + 1),
                               1:(nits + 1),
                               1:(nits + 1),
                               1:(nits + 1),
                               1:(nits + 1),
                               1:(nits + 1)))

load(file = '/Users/maxhird/Dropbox/Max PhD/Leading Eigenbasis plus Diagonal Preconditioning/results/MALA Ill Conditioned Gaussian m evecs/BPaM/sin_squareds.RData')
df <- rbind(df, data.frame(type = rep('BPaM', nits + 1), sin_squared = rep(ssd, nits + 1),
                           iteration = 1:(nits + 1)))
save(df, file = 'sin_squareds.RData')

p <- ggplot(df, aes(x = iteration, y = log10(sin_squared), color = type)) +
  geom_point(alpha = 0.7) +
  labs(x = 'iteration', y = 'log10(sin_squared)') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log10(sin squared distance)")
p

save_plot('log_sin_squareds.svg', fig = p, width = 16 * 0.9, height = 7 * 0.9)

ds <- c(50, 100, 150, 200); ms <- c(3, 10, 32)
replications <- 15; types <- c('pBaM', 'diagonal_plus_LR')

column_names <- c('minESS', 'medESS', 'time', 'minESSperSec', 'medESSperSec', 'type', 'no_evecs', 'dimension')
df <- data.frame(matrix(ncol = length(column_names), nrow = 0))
colnames(df) <- column_names

v <- 0
for (d in ds) {
  for (replication in 1:replications) {
    # set up target
    # no_significant_evals <- 3; significant_eval <- 100
    # significant_evals <- significant_eval + (significant_eval / (10 ^ 3)) * rnorm(no_significant_evals)
    # spectrum <- c(significant_evals, rep(0.1, d - no_significant_evals))
    # 
    # mu_pi <- rep(5, d); Sigma_pi <- hard_gaussian_covariance_by_spectrum(d, spectrum)
    # v_1 <- eigen(Sigma_pi)$vectors[, 1]; v_2 <- eigen(Sigma_pi)$vectors[, 2];
    # v_3 <- eigen(Sigma_pi)$vectors[, 3]
    # sqrt_Sigma_pi <- sqrtm(Sigma_pi); Sigma_pi_inv <- solve(Sigma_pi)
    
    mu_pi <- rnorm(d); Psi_pi <- diag(runif(d)); K <- 32
    Lambda_pi <- matrix(rnorm(K * d), nrow = d, ncol = K)
    Sigma_pi <- Psi_pi + Lambda_pi %*% t(Lambda_pi)
    v_1 <- eigen(Sigma_pi)$vectors[, 1]; v_2 <- eigen(Sigma_pi)$vectors[, 2]; v_3 <- eigen(Sigma_pi)$vectors[, 3]
    sqrt_Sigma_pi <- expm::sqrtm(Sigma_pi); Sigma_pi_inv <- solve(Sigma_pi)
    evals_pi <- eigen(Sigma_pi)$values
    print("Target condition:")
    print(max(evals_pi) / min(evals_pi))
    
    # Initialise the Markov chain
    k <- 2; X <- matrix(mu_pi, ncol = k, nrow = d) + sqrt_Sigma_pi %*% matrix(rnorm(d * k), nrow = d)
    nits_coeff <- 1000; nits <- nits_coeff * d ^ 0.5; kappa <- 0.7; sigma <- 0.5 / (d ^ (1 / 4));
    for (type in types) {
      if (type == 'none') {
        start_time <- Sys.time()
        out <- mala_normal(X, sigma, mu_pi, Sigma_pi, Sigma_pi_inv, nits, v_1, v_2, v_3)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d)
        
      } else if (type == 'diagonal') {
        D <- rep(1, d)
        start_time <- Sys.time()
        out <- mala_normal_diagonal(X, sigma, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d)
        
      } else if (type == 'dense') {
        L <- diag(d)
        start_time <- Sys.time()
        out <- mala_normal_dense(X, sigma, L, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3, TRUE)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d)
        
      } else if (type == 'eigen') {
        for (m in ms) {
          D <- rep(1, d); Q <- diag(d); c <- 1; p <- 1; I <- 1
          start_time <- Sys.time()
          out <- mala_normal_m_evecs(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, m, d)
          
        }
      } else if (type == 'eigen_identity') {
        for (m in ms) {
          D <- rep(1, d); Q <- diag(d); c <- 1; p <- 1; I <- 1
          start_time <- Sys.time()
          out <- mala_normal_m_evecs_identity(X, sigma, Q, D, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, c, p, m, I, v_1, v_2, v_3)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, m, d)
          
        }
      } else if (type == 'diagonal_plus_LR') {
        K <- 32
          D <- diag(d); V <- matrix(0.1, nrow = d, ncol = K); batch_size <- 10; mu <- rep(0, d);
          KL_nits <- 5000; mu_learn <- 0.001; delta_learn <- 0.00001; V_learn <- 0.000001
          
          start_time <- Sys.time()
          descent_out <- reverse_KL_gradient_descent(batch_size, mu, D, V, mu_pi, Sigma_pi, d, KL_nits, mu_learn, delta_learn, V_learn)
          
          plot(x = 1:KL_nits, y = descent_out$KLs)
          descent_LLT <- (descent_out$D + descent_out$V %*% t(descent_out$V)) %*% t(descent_out$D + descent_out$V %*% t(descent_out$V))
          
          out <- mala_normal_diag_plus_LR(X, sigma, descent_out$D, descent_out$V, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d)
      } else if (type == 'pBaM') {
          K <- 32; lambda_0 <- 10; bigT <- 100;
          mu <- rep(0, d); Psi <- diag(runif(d));
          Lambda <- 0.01 * matrix(rnorm(K * d), ncol = K)
          Sigma <- Psi + Lambda %*% t(Lambda);
          B <- 32;
          
          start_time <- Sys.time()
          BPaM_out <- BPaM_optimised(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi, lambda_0)
          print(BPaM_out$Psi + BPaM_out$Lambda %*% t(BPaM_out$Lambda))
          out <- mala_normal_diag_plus_LR(X, sigma, BPaM_out$Psi, BPaM_out$Lambda, mu_pi, Sigma_pi, Sigma_pi_inv, nits, kappa, v_1, v_2, v_3)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d)
      }
    }
  }
  print(v)
  v <- v + 1
}

save(df, file = 'ill_conditioned_gaussian_many_evecs.RData')
load(file = 'ill_conditioned_gaussian_many_evecs_identity.RData')

df$minESS <- as.numeric(df$minESS); df$medESS <- as.numeric(df$medESS)
df$time <- as.numeric(df$time); df$minESSperSec <- as.numeric(df$minESSperSec)
df$medESSperSec <- as.numeric(df$medESSperSec)
df$no_evecs <- as.numeric(df$no_evecs); df$dimension <- as.numeric(df$dimension)

p <- ggplot(df[df$no_evecs > 0 & df$dimension > 10 & df$type == 'BPaM', ], aes(x = as.factor(dimension), y = minESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESS, various m's, BPaM")
p

save_plot('minESS_various_ms_BPaM.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[df$no_evecs > 0 & df$dimension > 10 & df$type == 'BPaM', ], aes(x = as.factor(dimension), y = medESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESS, various m's, BPaM")
p

save_plot('medESS_various_ms_BPaM.svg', fig = p, width = 16 * 0.7, height = 13 * 0.7)

p <- ggplot(df[df$no_evecs > 0 & df$dimension > 10 & df$type == 'diagonal_plus_LR', ], aes(x = as.factor(dimension), y = minESSperSec, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESSperSec, various m's, diagonal + LR")
p

save_plot('minESSperSec_various_ms_diag_plus_LR.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[df$no_evecs > 0 & df$dimension > 10 & df$type == 'diagonal_plus_LR', ], aes(x = as.factor(dimension), y = medESSperSec, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESSperSec, various m's, diagonal + LR")
p

save_plot('medESSperSec_various_ms_diag_plus_LR.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 10 | df$no_evecs == 0) & df$dimension > 10, ], aes(x = as.factor(dimension), y = log10(minESS), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'type') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log10(minESS)")
p

save_plot('minESS.svg', fig = p, width = 16, height = 13)

cbPalette <- c("#999999", "#E69F00", "#56B4E9", "#009E73", "#000000", "#0072B2", "#D55E00", "#CC79A7")

p <- ggplot(df[(df$no_evecs == 32 | df$no_evecs == 0) & df$dimension > 10, ], aes(x = as.factor(dimension), y = log10(medESS), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'type') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log10(medESS), m = 32")
p

save_plot('log_medESS_m_32.svg', fig = p, width = 16, height = 9)

p <- ggplot(df[(df$no_evecs == 3 | df$no_evecs == 0) & df$dimension > 10, ], aes(x = as.factor(dimension), y = log10(minESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'type') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log10(minESSperSec)")
p

save_plot('log_minESSperSec.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 32 | df$no_evecs == 0) & df$dimension > 10, ], aes(x = as.factor(dimension), y = log10(medESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'type') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log10(medESSperSec), m = 32")
p

save_plot('log_medESSperSec_m_32.svg', fig = p, width = 16, height = 9)

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# BPaM Modi et al. 2024

K_pi <- 3;d <- 5
mu_pi <- rnorm(d); Lambda_pi <- matrix(rnorm(K_pi * d), ncol = K_pi)
Sigma_pi <- diag(runif(d)) + Lambda_pi %*% t(Lambda_pi)
Sigma_pi_inv <- solve(Sigma_pi); v_1 <- eigen(Sigma_pi)$vectors[, 1]
Sigma <- diag(d); mu <- rep(0, d); Psi <- diag(runif(d)); K <- 3
Lambda <- 0.1 * matrix(rnorm(K * d), ncol = K)
bigT <- 1000; B <- 32;

out <- BPaM(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi)

plot(1:bigT, log10(out$exact_KLs))
sin_squared_distance(v_1, eigen(out$Sigma)$vectors[, 1]);

Sigma <- diag(d); mu <- rep(0, d); Psi <- diag(runif(d)); K <- 6
Lambda <- 0.1 * matrix(rnorm(K * d), ncol = K)
bigT <- 1000; B <- 32;

start_time <- Sys.time()
out <- BPaM(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

plot(1:bigT, log10(out$exact_KLs))
sin_squared_distance(v_1, eigen(out$Sigma)$vectors[, 1]);

mu <- rep(0, d); Psi <- diag(runif(d)); K <- 6
Lambda <- 0.01 * matrix(rnorm(K * d), ncol = K)
Sigma <- Psi + Lambda %*% t(Lambda);
bigT <- 1000; B <- 32;

start_time <- Sys.time()
out <- BPaM_optimised(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

plot(1:bigT, log(out$exact_KLs))
sin_squared_distance(v_1, eigen(out$Sigma)$vectors[, 1]);
sin_squared_distance(v_2, eigen(out$Sigma)$vectors[, 2]);
sin_squared_distance(v_3, eigen(out$Sigma)$vectors[, 3]);
eigen(out$Sigma)$values

K_pi <- 1; d <- 5
mu_pi <- rnorm(d); Lambda_pi <- matrix(rnorm(K_pi * d), ncol = K_pi)
Sigma_pi <- diag(runif(d)) + Lambda_pi %*% t(Lambda_pi)
Sigma_pi_inv <- solve(Sigma_pi); v_1 <- eigen(Sigma_pi)$vectors[, 1]
mu <- rep(0, d); Psi <- diag(runif(d)); K <- 1
Lambda <- 0.1 * matrix(rnorm(K * d), ncol = K)
Sigma <- Psi + Lambda %*% t(Lambda)
bigT <- 1000; B <- 32;

out <- BPaM_optimised(bigT, B, mu, Sigma, mu_pi, Sigma_pi_inv, Lambda, Psi)

plot(1:bigT, log10(out$exact_KLs))
sin_squared_distance(v_1, eigen(out$Sigma)$vectors[, 1]);

{# From their codebase:
em_exact <- function(llambda, psi, mu, Cov) {
  r <- ncol(llambda); psi_inv <- diag(diag(psi) ^ -1); d <- nrow(psi)
  alpha <- t(llambda) %*% psi_inv
  beta <- pracma::pinv(diag(r) + alpha %*% llambda)
  
  gamma <- Cov %*% (t(alpha) %*% t(beta))
  llambda_update <- gamma %*% pracma::pinv(beta + beta %*% alpha %*% gamma)
  
  A <- diag(d) - llambda_update %*% beta %*% t(lambda) %*% psi_inv
  M <- A %*% Cov %*% t(A) + llambda_update %*% beta %*% t(lambda_update)
  psi_update = diag(diag(M))
  
  return(list(llambda_update = llambda_update, psi_update = psi_update))
}

lower_bound_kl <- function(Cov, psi, llambda) {
  A <- psi + llambda %*% t(llambda)
  logabsdet <- log(abs(det(A)))
  kl <- Trace(Cov %*% pracma::pinv(A)) + logabsdet
  return(kl)
}

fit_lr_gaussian2 <- function(data, mu, Cov, num_of_latents, eta = 1.0, tolerance = 0.001, num_of_itr = 100, diagnosis = F, llambda = NaN, psi = NaN) {
  d <- length(mu)
  
  if (is.na(llambda)) {
    llambda <- 0.1 * matrix(rnorm(d * K), nrow = d)
  }
  if (is.na(psi)) {
    psi = diag(runif(d))
  }
  
  lower_bound_old <- NaN; lower_bound <- NaN; counter <- 1
  losses <- vector(length = num_of_itr); psis <- matrix(0, ncol = d, nrow = num_of_itr)
  llambdas <- array(dim = c(d, K, num_of_itr))
  
  while (counter < num_of_itr + 1) {
    em_out <- em_exact(llambda, psi, mu, Cov)
    psi <- (1 - eta) * psi + eta * em_out$psi_update
    llambda <- (1 - eta) * llambda + eta * em_out$llambda_update
    lower_bound_old <- lower_bound
    lower_bound <- lower_bound_kl(Cov, psi, llambda)
    
    if (!is.na(lower_bound_old) & abs((lower_bound / lower_bound_old) - 1) < tolerance) {
      if (diagnosis) {
        print(counter)
        print('iterations to reach convergence')
        return(list(mu = mu, llambda = llambda, psi = psi, psis = psis, llambdas == lambdas, losses = losses))
      }
    }
    
    llambdas[, , counter] <- llambda; psis[counter, ] <- diag(psi)
    losses[counter] <- lower_bound
    counter <- counter + 1
  }
  if (diagnosis) {
    print(counter)
    print('iterations to reach convergence')
  }
  return(list(mu = mu, llambda = llambda, psi = psi, psis = psis, llambdas == lambdas, losses = losses))
}

fg_bam_update <- function(lp, lp_g, samples, mu0, S0, reg) {
  B <- nrow(samples)
  
  zbar <- colMeans(samples); C <- cov(samples)
  gbar <- colMeans(grad_log_pi_normal(t(samples), mu_pi, Sigma_pi))
}
}