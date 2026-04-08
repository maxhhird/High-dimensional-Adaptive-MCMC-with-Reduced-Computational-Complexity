require(mvtnorm)
require(expm)
require(coda)
require(profvis)
require(pracma)
require(ggplot2)
require(sjPlot)
# Here we implement our adaptive algorithm on the mean-field XY model

XY_potential <- function(Theta, J) {
  first_vec <- diag(t(cos(Theta)) %*% J %*% cos(Theta))
  second_vec <- diag(t(sin(Theta)) %*% J %*% sin(Theta))
  return(-0.5 * (first_vec + second_vec))
}

XY_gradient <- function(Theta, J) {
  first_mat <- sin(Theta) * ((J + t(J)) %*% cos(Theta))
  second_mat <- cos(Theta) * ((J + t(J)) %*% sin(Theta))
  return(0.5 * (first_mat - second_mat))
}

sin_squared_distance <- function(v, w) {
  # normalise:
  v <- v / sqrt(sum(v ^ 2))
  w <- w / sqrt(sum(w ^ 2))
  
  return(1 - sum(v * w) ^ 2)
}

XY_Hessian <- function(theta, J) {
  first_vec <- cos(theta) * ((J + t(J)) %*% cos(theta))
  second_vec <- sin(theta) * ((J + t(J)) %*% sin(theta))
  diagonal <- 0.5 * (first_vec + second_vec) - diag(J)
  off_diagonal <- -0.5 * (J + t(J)) %*% ((cos(theta) %*% t(cos(theta))) + (sin(theta) %*% t(sin(theta))))
  off_diagonal <- off_diagonal - diag(diag(off_diagonal))
  return(diag(diagonal) + off_diagonal)
}

Q_m <- function(vs) {
  vs <- as.matrix(vs)
  d <- nrow(vs); m <- ncol(vs)
  if (d == m) {
    return(vs)
  }
  Q_m <- diag(d)
  for (i in 1:m) {
    e_i <- diag(d)[, i]; diff <- Q_m[, i] - vs[, i]
    if (sum(abs(diff)) < 1e-5) {next}
    Q_m <- Q_m - (2 / sum(diff ^ 2)) * (diff %*% crossprod(diff, Q_m))
  }
  return(Q_m)
}

get_estimate <- function(chains, nits, k, d) {
  return(1 / ((nits + 1) * k * d) * sum(chains))
}

mala_proposal_ratio_preconditioned_mv <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, LLT_inv) {
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  I_1 <- diag(D_1 %*% LLT_inv %*% t(D_1))
  I_2 <- diag(D_2 %*% LLT_inv %*% t(D_2))
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
}

mala_proposal_ratio_diag_plus_LR_chol <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, D, V) {
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  I_1 <- diag(D_1 %*% diag_plus_LR_inverse_multiply(D, V, diag_plus_LR_inverse_multiply(D, V, t(D_1))))
  I_2 <- diag(D_2 %*% diag_plus_LR_inverse_multiply(D, V, diag_plus_LR_inverse_multiply(D, V, t(D_2))))
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
}

mala_proposal_ratio_diag_plus_LR <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, D, V) {
  m <- ncol(V); inner_matrix <- solve(diag(m) + t(V) %*% ((diag(D) ^ (-1)) * V))
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  right_1 <- (diag(D) ^ (-1)) * t(D_1) - (diag(D) ^ (-1)) * (V %*% (inner_matrix %*% (t(V) %*% ((diag(D) ^ (-1)) * t(D_1)))))
  right_2 <- (diag(D) ^ (-1)) * t(D_2) - (diag(D) ^ (-1)) * (V %*% (inner_matrix %*% (t(V) %*% ((diag(D) ^ (-1)) * t(D_2)))))
  # right_1 <- diag(diag(D) ^ (-1)) %*% t(D_1) - diag(diag(D) ^ (-1)) %*% (V %*% (inner_matrix %*% (t(V) %*% (diag(diag(D) ^ (-1)) %*% t(D_1)))))
  # right_2 <- diag(diag(D) ^ (-1)) %*% t(D_2) - diag(diag(D) ^ (-1)) %*% (V %*% (inner_matrix %*% (t(V) %*% (diag(diag(D) ^ (-1)) %*% t(D_2)))))
  
  I_1 <- diag(D_1 %*% right_1)
  I_2 <- diag(D_2 %*% right_2)
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
}

mala_proposal_ratio_preconditioned_mv_no_LLTinv <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, Q, D) {
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  # I_1 <- diag(D_1 %*% Q %*% ((D ^ (-1)) * t(Q)) %*% t(D_1))
  # I_2 <- diag(D_2 %*% Q %*% ((D ^ (-1)) * t(Q)) %*% t(D_2))
  I_1 <- diag(tcrossprod(D_1 %*% Q, D_1 %*% Q %*% diag(D ^ (-1))))
  I_2 <- diag(tcrossprod(D_2 %*% Q, D_2 %*% Q %*% diag(D ^ (-1))))
  
  return(exp(-(1 / (2 * (sigma ^ 2)) * (I_1 - I_2))))
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

BPaM_optimised <- function(bigT, B = 32, mu, Sigma, J, beta, Lambda, Psi, lambda_0 = 10) {
  KLs <- vector(length = bigT)
  d <- length(mu); K <- ncol(Lambda)
  for (t in 1:bigT) {
    lambda_learn <- lambda_0
    # 3:
    # use the formula from Ong, Nott, and Smith 2018
    Z <- mu + sqrt(Psi) %*% t(rmvnorm(n = B, mean = rep(0, d), sigma = diag(d))) + Lambda %*% t(rmvnorm(n = B, mean = rep(0, K), sigma = diag(K)))
    # 4:
    # G <- grad_log_pi_normal(Z, mu_pi, Sigma_pi_inv)
    # G <- -logistic_gradient_mv(Y, X, Z, Sigma_X, lambda)
    G <- -beta * XY_gradient(Z, J)
    # 5:
    z_bar <- rowMeans(Z); g_bar <- rowMeans(G)
    # Subtraction works columnwise
    Z_centred <- Z - z_bar; G_centred <- G - g_bar
    C <- cov(t(Z)); Gamma <- cov(t(G))
    # 6:
    Q <- sqrt(lambda_learn / B) * G_centred; Q <- cbind(Q, sqrt(lambda_learn / (1 + lambda_learn)) * g_bar)
    R <- Lambda; R <- cbind(R, sqrt(lambda_learn / B) * Z_centred); R <- cbind(R, sqrt(lambda_learn / (1 + lambda_learn)) * (mu - z_bar));
    H <- t(Psi) %*% Q + R %*% (t(R) %*% Q)
    M <- pracma::pinv(0.5 * diag(B + 1) + expm::sqrtm(t(H) %*% Q + 0.25 * diag(B + 1))) %^% 2
    patch_out <- patch_optimised(R, H, M, Lambda, Psi)
    Psi <- patch_out$Psi; Lambda <- patch_out$Lambda
    mu <- as.vector((1 / (lambda_learn + 1)) * mu + (lambda_learn / (lambda_learn + 1)) * (Psi %*% g_bar + Lambda %*% (t(Lambda) %*% g_bar) + z_bar))
    
    # KLs[t] <- reverse_KL(t(Z), mu, Psi, Lambda, J, beta)
  }
  return(list(mu = mu, Sigma = Psi + Lambda %*% t(Lambda), KLs = KLs, Psi = Psi, Lambda = Lambda))
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
    if (KL_old / KL_new < 1 + epsilon) {
      break
    }
    KL_old <- KL_new
  }
  return(list(Psi = Psi, Lambda = Lambda))
}

mala_XY <- function(Theta, sigma, J, beta, nits, kappa) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * grad_log_pi_Theta
    xi <- matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * xi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv(t(Theta), t(Theta_prop), sigma, t(xi), t(grad_log_pi_Theta_prop), diag(d))
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_uniform <- function(Theta, sigma, J, beta, nits, kappa) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  sigma <- min(sigma, pi / sqrt(d))
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * grad_log_pi_Theta
    xi <- matrix(runif(d * k), nrow = d)
    Theta_prop <- (Theta + drift + sigma * xi) %% (2 * pi)
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    sigma <- min(sigma, pi / sqrt(d))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_diagonal <- function(Theta, sigma, J, beta, nits, kappa, D) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # D is a diagonal preconditioner
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  adaptive_mu <- rowMeans(Theta)
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * D * grad_log_pi_Theta
    Lxi <- sqrt(D) * matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- D * grad_log_pi_Theta_prop
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), diag(D ^ -1))
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    adaptive_mu <- adaptive_mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - adaptive_mu)
    adaptive_mu <- adaptive_mu %% (2 * pi)
    gradient <- rep(0, d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (Theta[, j] - adaptive_mu) ^ 2
    }
    D <- D + (1 / (i + 1) ^ kappa) * (gradient - D)
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_dense <- function(Theta, sigma, J, beta, nits, kappa, L) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # L is a dense preconditioner
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  adaptive_mu <- rowMeans(Theta); LLT <- L %*% t(L)
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    L_inv <- solve(L); LLT_inv <- t(L_inv) %*% L_inv
    # Propose
    drift <- ((sigma ^ 2) / 2) * LLT %*% grad_log_pi_Theta
    Lxi <- L %*% matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- LLT %*% grad_log_pi_Theta_prop
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), LLT_inv)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    adaptive_mu <- adaptive_mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - adaptive_mu)
    adaptive_mu <- adaptive_mu %% (2 * pi)
    gradient <- matrix(0, nrow = d, ncol = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (Theta[, j] - adaptive_mu) %*% t(Theta[, j] - adaptive_mu)
    }
    LLT <- LLT + (1 / (i + 1) ^ kappa) * (gradient - LLT)
    min_eval <- min(eigen(LLT, symmetric = TRUE, only.values = TRUE)$values)
    leading_evec <- eigen(LLT, symmetric = TRUE)$vectors[, 1]
    if (min_eval < 0) {
      LLT <- LLT + (abs(min_eval) + 1) * diag(d)
    }
    L <- t(chol(LLT))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_dense_uniform <- function(Theta, sigma, J, beta, nits, kappa, L) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # L is a dense preconditioner
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  adaptive_mu <- rowMeans(Theta); LLT <- L %*% t(L)
  sigma <- min(sigma, pi / sqrt(d))
  L <- diag(1 / sqrt(rowSums(L ^ 2))) %*% L
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    L_inv <- solve(L); LLT_inv <- t(L_inv) %*% L_inv
    # Propose
    drift <- ((sigma ^ 2) / 2) * LLT %*% grad_log_pi_Theta
    xi <- matrix(runif(d * k), nrow = d)
    Lxi <- L %*% xi
    Theta_prop <- (Theta + drift + sigma * Lxi) %% (2 * pi)
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- LLT %*% grad_log_pi_Theta_prop
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    sigma <- min(sigma, pi / sqrt(d))
    
    adaptive_mu <- adaptive_mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - adaptive_mu)
    adaptive_mu <- adaptive_mu %% (2 * pi)
    gradient <- matrix(0, nrow = d, ncol = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (Theta[, j] - adaptive_mu) %*% t(Theta[, j] - adaptive_mu)
    }
    LLT <- LLT + (1 / (i + 1) ^ kappa) * (gradient - LLT)
    min_eval <- min(eigen(LLT, symmetric = TRUE, only.values = TRUE)$values)
    leading_evec <- eigen(LLT, symmetric = TRUE)$vectors[, 1]
    if (min_eval < 0) {
      LLT <- LLT + (abs(min_eval) + 1) * diag(d)
    }
    L <- t(chol(LLT))
    L <- diag(1 / sqrt(rowSums(L ^ 2))) %*% L
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_eigen <- function(Theta, sigma, J, beta, nits, kappa, Q, D, c, m) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # QD is the preconditioner (Q is orthogonal, D diagonal)
  # c governs the learning rate of the eigeninformation
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  adaptive_mu <- rowMeans(Theta);
  sigma <- min(sigma, pi / sqrt(d))
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_Theta)) 
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- Q %*% (D * crossprod(Q, grad_log_pi_Theta_prop))
    
    # Accept-reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv_no_LLTinv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), Q, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    # adapt
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    adaptive_mu <- adaptive_mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - adaptive_mu)
    
    gradient <- matrix(0, ncol = d, nrow = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * tcrossprod(Theta[, j] - adaptive_mu, Theta[, j] - adaptive_mu)
    }
    gamma <- c / (i ^ kappa)
    
    Q[, 1:m] <- Q[, 1:m] + gamma * crossprod(gradient, Q[, 1:m])
    if (m == 1) {
      Q[, 1] <- Q[, 1] / sqrt(sum(Q[, 1] ^ 2))
    } else {
      Q[, 1:m] <- t((sqrt(colSums(Q[, 1:m] * Q[, 1:m])) ^ (-1)) * t(Q[, 1:m]))
    }
    if (m > 1) {
      # Orthonormalise the first 1 to m columns
      Q[, 1:m] <- gramSchmidt(Q[, 1:m])$Q
    }
    # Orthonormalise fully
    Q <- Q_m(Q[, 1:m])
    
    Theta_tilde <- crossprod(Q, Theta)
    mu_tilde <- crossprod(Q, adaptive_mu)
    gradient <- rep(0, d)
    
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (Theta_tilde[, j] - mu_tilde) ^ 2
    }
    D <- as.vector(D + (1 / (i + 1) ^ kappa) * (gradient - D))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_eigen_uniform <- function(Theta, sigma, J, beta, nits, kappa, Q, D, c, m) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # QD is the preconditioner (Q is orthogonal, D diagonal)
  # c governs the learning rate of the eigeninformation
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  adaptive_mu <- rowMeans(Theta);
  sigma <- min(sigma, pi / sqrt(d))
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_Theta))
    xi <- matrix(runif(d * k), nrow = d)
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    Theta_prop <- (Theta + drift + sigma * Lxi) %% (2 * pi)
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- Q %*% (D * crossprod(Q, grad_log_pi_Theta_prop))
    
    # Accept-reject
    target_ratios <- exp(logpi_props - logpi_currs)
    alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    # adapt
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    sigma <- min(sigma, pi / sqrt(d))
    adaptive_mu <- adaptive_mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - adaptive_mu)
    
    gradient <- matrix(0, ncol = d, nrow = d)
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * tcrossprod(Theta[, j] - adaptive_mu, Theta[, j] - adaptive_mu)
    }
    gamma <- c / (i ^ kappa)
    
    Q[, 1:m] <- Q[, 1:m] + gamma * crossprod(gradient, Q[, 1:m])
    if (m == 1) {
      Q[, 1] <- Q[, 1] / sqrt(sum(Q[, 1] ^ 2))
    } else {
      Q[, 1:m] <- t((sqrt(colSums(Q[, 1:m] * Q[, 1:m])) ^ (-1)) * t(Q[, 1:m]))
    }
    if (m > 1) {
      # Orthonormalise the first 1 to m columns
      Q[, 1:m] <- gramSchmidt(Q[, 1:m])$Q
    }
    # Orthonormalise fully
    Q <- Q_m(Q[, 1:m])
    
    Theta_tilde <- crossprod(Q, Theta)
    mu_tilde <- crossprod(Q, adaptive_mu)
    gradient <- rep(0, d)
    
    for (j in 1:k) {
      gradient <- gradient + (1 / k) * (Theta_tilde[, j] - mu_tilde) ^ 2
    }
    D <- as.vector(D + (1 / (i + 1) ^ kappa) * (gradient - D))
    for (n in 1:d) {D[n] <- min(D[n], 1)}
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

diag_plus_LR_multiply <- function(D, V, M) {
  # output (D + VV^T)M
  # D is a d x d matrix, V is a d x m matrix
  return(diag(D) * M + V %*% crossprod(V, M))
}

mala_XY_diag_plus_LR <- function(Theta, sigma, J, beta, nits, kappa, D, V) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # D + VV ^ T is an estimate of the target covariance
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  L <- t(chol(D + V %*% t(V))); LLT_inv <- solve(D + V %*% t(V))
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * (diag(D) * grad_log_pi_Theta + V %*% crossprod(V, grad_log_pi_Theta))
    Lxi <- L %*% matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- diag(D) * grad_log_pi_Theta_prop + V %*% crossprod(V, grad_log_pi_Theta_prop)
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    # proposal_ratios <- mala_proposal_ratio_diag_plus_LR(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), D, V)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), LLT_inv)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

mala_XY_diag_plus_LR_chol <- function(Theta, sigma, J, beta, nits, kappa, D, V) {
  # Theta is a n x k matrix representing the states of the k chains
  # sigma is a step-size
  # J is a n x x matrix of couplings
  # beta is an inverse temperature
  # nits is the number of iterations
  # kappa governs the size of the learning rate for sigma
  # D + VV ^ T is an estimate of the cholesky factor
  # of the target covariance
  d <- nrow(Theta); k <- ncol(Theta);
  logpi_currs <- -beta * XY_potential(Theta, J)
  grad_log_pi_Theta <- -beta * XY_gradient(Theta, J)
  
  chains <- array(dim = c(d, k, nits + 1))
  potentials <- matrix(nrow = nits + 1, ncol = k)
  sigmas <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  potentials[1, ] <- -logpi_currs
  sigmas[1] <- sigma
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * diag_plus_LR_multiply(D, V, diag_plus_LR_multiply(D, V, grad_log_pi_Theta))
    Lxi <- diag_plus_LR_multiply(D, V, matrix(rnorm(d * k), nrow = d))
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -beta * XY_potential(Theta_prop, J)
    grad_log_pi_Theta_prop <- -beta * XY_gradient(Theta_prop, J)
    LLTgrad_log_pi_Theta_prop <- diag_plus_LR_multiply(D, V, diag_plus_LR_multiply(D, V, grad_log_pi_Theta_prop))
    
    # Accept/Reject
    target_ratios <- exp(logpi_props - logpi_currs)
    # proposal_ratios <- mala_proposal_ratio_diag_plus_LR(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), D, V)
    proposal_ratios <- mala_proposal_ratio_diag_plus_LR_chol(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), D, V)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    
    # Storage
    chains[, , i + 1] <- Theta
    potentials[i + 1, ] <- -logpi_currs
    sigmas[i + 1] <- sigma
  }
  chains <- chains %% 2 * pi
  # Get the estimate
  estimate <- get_estimate(chains, nits, k, d)
  return(list(chains = chains, sigmas = sigmas, potentials = potentials, estimate = estimate))
}

reverse_KL_gradient_descent <- function(batch_size, mu, D, V, J, d, nits, mu_learn, delta_learn, V_learn, beta) {
  KLs <- vector(length = nits);
  Lambda <- diag(D); delta <- sqrt(Lambda)
  for (i in 1:nits) {
    L_inv <- diag_plus_LR_inverse(D, V)
    standard_batch <- matrix(rnorm(batch_size * d), ncol = batch_size)
    batch <- t(as.vector(mu) + D %*% standard_batch + V %*% (t(V) %*% standard_batch))
    
    L_grad <- reverse_KL_L_grad(batch, J, L_inv, beta)
    #L_grad <- reverse_KL_L_grad_true(Sigma_pi_inv, L_inv, D, V)
    mu <- mu - mu_learn * reverse_KL_mu_grad(batch, J, beta)
    delta <- delta - delta_learn * (delta * diag(L_grad))
    Lambda <- delta ^ 2
    V <- V - V_learn * (L_grad + t(L_grad)) %*% V
    D <- diag(Lambda)
    
    # KLs[i] <- reverse_KL(batch, mu, D, V, J, beta)
  }
  return(list(KLs = KLs, mu = mu, D = D, V = V))
}

reverse_KL_L_grad <- function(batch, J, L_inv, beta) {
  batch_size <- nrow(batch); d <- ncol(batch)
  grad <- matrix(0, ncol = d, nrow = d)
  # for (b in 1:batch_size) {
  #   grad <- grad - outer(as.vector(grad_log_pi_normal(batch[b, ], mu_pi, Sigma_pi_inv)), as.vector(batch[b, ]))
  # }
  for (b in 1:batch_size) {
    grad <- grad - (1 / batch_size) * outer(as.vector(-beta * XY_gradient(batch[b, ], J)), as.vector(batch[b, ]))
  }
  grad <- grad - L_inv
  return(grad)
}

reverse_KL_mu_grad <- function(batch, J, beta) {
  batch_size <- nrow(batch); d <- ncol(batch)
  grad <- rep(0, d)
  # for (b in 1:batch_size) {
  #   grad <- grad - (1 / batch_size) * grad_log_pi_normal(batch[b, ], mu_pi, Sigma_pi_inv)
  # }
  for (b in 1:batch_size) {
    grad <- grad + (1 / batch_size) * beta * XY_gradient(batch[b, ], J)
  }
  return(grad)
}

reverse_KL <- function(batch, mu, D, V, J, beta) {
  LLT <- D ^ 2 + V %*% (t(V) %*% D) + (D %*% V) %*% t(V) + V %*% (t(V) %*% V) %*% t(V)
  # estimate the reverse KL
  #log_ratios <- dmvnorm(batch, mean = mu, sigma = LLT, log = TRUE) - dmvnorm(batch, mean = mu_pi, sigma = Sigma_pi, log = TRUE)
  logistic_negative_log_densities <- beta * XY_potential(t(batch), J)
  log_ratios <- dmvnorm(batch, mean = mu, sigma = LLT, log = TRUE) + logistic_negative_log_densities
  return(mean(log_ratios))
}

diag_plus_LR_inverse <- function(D, V) {
  # Use the Woodbury Identity
  D_inv <- solve(D); m <- ncol(V);
  inner_inverse <- solve(diag(m) + t(V) %*% D_inv %*% V)
  return(D_inv - D_inv %*% V %*% inner_inverse %*% t(V) %*% D_inv)
}

diag_plus_LR_inverse_multiply <- function(D, V, M) {
  # outputs ((D + VV^T) ^ {-1}) M
  D_inv <- solve(D); m <- ncol(V)
  inner_inverse <- solve(diag(m) + t(V) %*% (diag(D_inv) * V))
  return(diag(D_inv) * M - diag(D_inv) * (V %*% (inner_inverse %*% crossprod(V, diag(D_inv) * M))))
}
# At low temp we can initialise at Theta <- matrix(pi / 4, nrow = n, ncol = k)
# At high temp we can initialise with angles from U[-pi, pi]
d <- 150; k <- 2; Theta <- matrix(pi, nrow = d, ncol = k)
nits_coeff <- 1000; nits <- nits_coeff * d ^ 0.5; kappa <- 0.7; sigma <- 0.5 / (d ^ (1 / 4));
beta <- 100 * (1 / d)

# mean field:
J <- matrix(1, nrow = d, ncol = d);

# Erdos-Renyi:
J <- matrix(0, nrow = d, ncol = d); p <- 0.1
for (i in 1:(d - 1)) {
  for (j in (i + 1):d) {
    U <- runif(1)
    if (U <= p) {
      J[i, j] <- 1; J[j, i] <- 1
    }
  }
}
J <- J + diag(d)

# No adaptation
start_time <- Sys.time()
out <- mala_XY_uniform(Theta, sigma, J, beta, nits, kappa)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# 2d scatter plot
df <- data.frame(theta_1 = chains[1, 1, 1:(nits + 1)] %% (2 * pi),
                 theta_2 = chains[2, 1, 1:(nits + 1)] %% (2 * pi))

p <- ggplot(df, aes(x = theta_1, y = theta_2)) +
  geom_point() +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  xlim(c(0, 2 * pi)) +
  ylim(c(0, 2 * pi)) +
  ggtitle('MALA Chain on 300 dimensional Mean Field Classical XY Target')
p

save_plot('2_dimensional_scatter_plot_300d.svg', fig = p, width = 14, height = 7)

# Diagonal adaptation
D <- rep(1, d)
start_time <- Sys.time()
out <- mala_XY_diagonal(Theta, sigma, J, beta, nits, kappa, D)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# Dense adaptation
L <- diag(d)
start_time <- Sys.time()
out <- mala_XY_dense_uniform(Theta, sigma, J, beta, nits, kappa, L)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# eigen adaptation
D <- rep(1, d); c <- 1; Q <- diag(d); m <- 1
start_time <- Sys.time()
out <- mala_XY_eigen(Theta, sigma, J, beta, nits, kappa, Q, D, c, m)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# pBaM
mu <- rep(pi / 4, d); Psi <- diag(d); m <- 3; lambda_0 <- 0.0001
Lambda <- 0.1 * matrix(rnorm(m * d), ncol = m)
Sigma <- Psi + Lambda %*% t(Lambda);
bigT <- 400; B <- 32;

start_time <- Sys.time()
BPaM_out <- BPaM_optimised(bigT, B = 32, mu, Sigma, J, beta, Lambda, Psi, lambda_0)
plot(1:bigT, BPaM_out$KLs)

out <- mala_XY_diag_plus_LR(Theta, sigma, J, beta, nits, kappa, BPaM_out$Psi, BPaM_out$Lambda)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# Gradient descent on the reverse KL
m <- 3; D <- diag(d); V <- matrix(0.1, nrow = d, ncol = m); batch_size <- 10; mu <- Theta[, 1];
KL_nits <- 2000; mu_learn <- 0.01; delta_learn <- 0.0005; V_learn <- 0.0001

start_time <- Sys.time()
descent_out <- reverse_KL_gradient_descent(batch_size, mu, D, V, J, d, KL_nits, mu_learn, delta_learn, V_learn, beta)

plot(x = 1:KL_nits, y = descent_out$KLs)
descent_LLT <- (descent_out$D + descent_out$V %*% t(descent_out$V)) %*% t(descent_out$D + descent_out$V %*% t(descent_out$V))
eigen(descent_LLT)$values

D <- descent_out$D; V <- descent_out$V
out <- mala_XY_diag_plus_LR_chol(Theta, sigma, J, beta, nits, kappa, D, V)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$sigmas)
plot(chains[1, 1, 1:(nits + 1)] %% (2 * pi), chains[2, 1, 1:(nits + 1)] %% (2 * pi))
plot(1:(nits + 1), out$potentials[, 1])
ESSs <- ESS_k_chains(chains); median(ESSs); median(ESSs / time_taken)
print(out$estimate)

# Large Experiment:
ds <- c(10, 20, 30, 40, 50); replications <- 15;
types <- c('none', 'dense', 'diagonal', 'eigen', 'pBaM', 'diagonal+LR')

column_names <- c('minESS', 'medESS', 'time', 'minESSperSec', 'medESSperSec', 'type', 'dimension', 'estimate')
df <- data.frame(matrix(ncol = length(column_names), nrow = 0))
colnames(df) <- column_names

v <- 0
for (d in ds) {
  for (replication in 1:replications) {
    k <- 2; Theta <- matrix(pi / 4, nrow = d, ncol = k)
    nits_coeff <- 1000; nits <- nits_coeff * d ^ 0.5; kappa <- 0.7; sigma <- 0.5 / (d ^ (1 / 4));
    J <- matrix(1, nrow = d, ncol = d); beta <- 100 * (1 / d)
    for (type in types) {
      if (type == 'none') {
        start_time <- Sys.time()
        out <- mala_XY(Theta, sigma, J, beta, nits, kappa)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      } else if (type == 'diagonal') {
        D <- rep(1, d)
        start_time <- Sys.time()
        out <- mala_XY_diagonal(Theta, sigma, J, beta, nits, kappa, D)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      } else if (type == 'dense') {
        L <- diag(d)
        start_time <- Sys.time()
        out <- mala_XY_dense(Theta, sigma, J, beta, nits, kappa, L)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      } else if (type == 'eigen') {
        D <- rep(1, d); c <- 1; Q <- diag(d); m <- 1
        start_time <- Sys.time()
        out <- mala_XY_eigen(Theta, sigma, J, beta, nits, kappa, Q, D, c, m)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      } else if (type == "pBaM") {
        if (d <= 50) {
          lambda_0 <- 1
        } else if (d == 100 || d == 150) {
          lambda_0 <- 0.1
        } else if (d == 200) {
          lambda_0 <- 0.0001
        } else if (d == 250) {
          lambda_0 <- 0.00001
        } else if (d == 300) {
          lambda_0 <- 0.00001
        }
        mu <- rep(pi / 4, d); Psi <- diag(d); m <- 3;
        Lambda <- 0.1 * matrix(rnorm(m * d), ncol = m)
        Sigma <- Psi + Lambda %*% t(Lambda);
        bigT <- 400; B <- 32;
        
        start_time <- Sys.time()
        BPaM_out <- BPaM_optimised(bigT, B = 32, mu, Sigma, J, beta, Lambda, Psi, lambda_0)
        plot(1:bigT, BPaM_out$KLs)
        
        out <- mala_XY_diag_plus_LR(Theta, sigma, J, beta, nits, kappa, BPaM_out$Psi, BPaM_out$Lambda)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      } else if (type == 'diagonal+LR') {
        m <- 3; D <- diag(d); V <- matrix(0.1, nrow = d, ncol = m); batch_size <- 10; mu <- Theta[, 1];
        KL_nits <- 2000; mu_learn <- 0.01; delta_learn <- 0.0005; V_learn <- 0.0001
        
        start_time <- Sys.time()
        descent_out <- reverse_KL_gradient_descent(batch_size, mu, D, V, J, d, KL_nits, mu_learn, delta_learn, V_learn, beta)
        
        descent_LLT <- (descent_out$D + descent_out$V %*% t(descent_out$V)) %*% t(descent_out$D + descent_out$V %*% t(descent_out$V))
        
        D <- descent_out$D; V <- descent_out$V
        out <- mala_XY_diag_plus_LR_chol(Theta, sigma, J, beta, nits, kappa, D, V)
        end_time <- Sys.time()
        time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
        
        chains <- out$chains;
        ESSs <- ESS_k_chains(chains)
        
        df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, d, out$estimate)
      }
      print(v)
      v <- v + 1
    }
  }
}

save(df, file = 'mean_field_XY_diagonal_plus_LR.RData')

df$minESS <- as.numeric(df$minESS); df$medESS <- as.numeric(df$medESS)
df$time <- as.numeric(df$time); df$minESSperSec <- as.numeric(df$minESSperSec)
df$medESSperSec <- as.numeric(df$medESSperSec); df$dimension <- as.numeric(df$dimension)
df$estimate <- as.numeric(df$estimate)

cbPalette <- c("#999999", "#E69F00", "#56B4E9", "#009E73", "#000000", "#0072B2", "#D55E00", "#CC79A7")

p <- ggplot(df, aes(x = as.factor(dimension), y = log10(minESS), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("Mean-field XY, log10(minESS), 1 significant e.vec")
p

save_plot('minESS_mean_field.svg', fig = p, width = 16, height = 10)

p <- ggplot(df, aes(x = as.factor(dimension), y = log10(medESS), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("Mean-field XY, log10(medESS), 1 significant e.vec")
p

save_plot('medESS_mean_field.svg', fig = p, width = 16, height = 9)

p <- ggplot(df, aes(x = as.factor(dimension), y = log10(minESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("Mean-field XY, log10(minESS / s), 1 significant e.vec")
p

save_plot('minESSperSec_mean_field.svg', fig = p, width = 16, height = 10)

p <- ggplot(df, aes(x = as.factor(dimension), y = log10(medESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("Mean-field XY, log10(medESS / s), 1 significant e.vec")
p

save_plot('medESSperSec_mean_field.svg', fig = p, width = 16, height = 9)

p <- ggplot(df, aes(x = as.factor(dimension), y = estimate, color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  scale_color_manual(values = cbPalette) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("Mean-field XY, estimates") +
  geom_hline(yintercept = pi)
p

save_plot('medESSperSec_mean_field.svg', fig = p, width = 16, height = 9)









