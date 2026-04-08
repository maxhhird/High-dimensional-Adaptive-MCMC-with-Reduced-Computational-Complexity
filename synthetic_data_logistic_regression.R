require(mvtnorm)
require(pracma)
require(expm)
require(coda)
require(profvis)
require(mgcv)

Haar_sample <- function(d) {
  M <- matrix(rnorm(d ^ 2), nrow = d)
  QR_object <- qr(M)
  Q <- qr.Q(QR_object); R <- qr.R(QR_object)
  L <- sign(diag(diag(R)))
  return(Q %*% L)
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

Q_m_vector_multiply <- function(vs, u) {
  vs <- as.matrix(vs)
  d <- nrow(vs); m <- ncol(vs)
  if (m == 1) {
    v_1 <- vs[, 1]; diff <- diag(d)[, 1] - v_1
    squared_diff <- sum(diff ^ 2)
    if (squared_diff < 1e-9) {
      return(u)
    } else {
      return(u - (2 / squared_diff) * sum(diff * u) * diff)
    }
  } else if (m > 1) {
    ret <- Q_m_vector_multiply(vs[, 1:(m - 1)], u)
    new_col <- Q_m_vector_multiply(vs[, 1:(m - 1)], diag(d)[, m])
    diff <- new_col - vs[, m]; squared_diff <- sum(diff ^ 2)
    if (squared_diff < 1e-9) {
      return(ret)
    } else {
      return(ret - (2 / squared_diff) * sum(diff * ret) * diff)
    }
  }
}

diff_storage <- function(vs) {
  vs <- as.matrix(vs); d <- nrow(vs); m <- ncol(vs)
  Q_product_storage <- matrix(nrow = d, ncol = m - 1)
  for (k in 1:m) {
    if (k == 1) {
      # Calculate Q_1 e_2 and store the difference
      diff <- -vs[, 1]; diff[1] <- diff[1] + 1
      squared_diff <- sum(diff ^ 2); e_2 <- rep(0, d); e_2[2] <- 1
      if (squared_diff >= 1e-9) {
        Q_product_storage[, 1] <- e_2 - (2 / squared_diff) * diff[2] * diff
      }
    } else {
      # Calculate and store Q_k e_{k + 1}
      if (k < m) {
        # Initialise at e_{k + 1}
        Q_k_e_k_plus_1 <- rep(0, d); Q_k_e_k_plus_1[k + 1] <- 1
        for (s in 1:k) {
          if (s == 1) {
            # Calculate Q_1 e_{k + 1}
            diff <- -vs[, 1]; diff[1] <- diff[1] + 1
            squared_diff <- sum(diff ^ 2)
            if (squared_diff >= 1e-9) {
              Q_k_e_k_plus_1 <- Q_k_e_k_plus_1 - (2 / squared_diff) * diff[k + 1] * diff
            }
          } else {
            # Calculate Q_s e_{k + 1}
            Q_s_minus_1_e_s <- Q_product_storage[, s - 1]
            diff <- Q_s_minus_1_e_s - vs[, s]
            squared_diff <- sum(diff ^ 2)
            if (squared_diff >= 1e-9) {
              Q_k_e_k_plus_1 <- Q_k_e_k_plus_1 - (2 / squared_diff) * sum(diff * Q_k_e_k_plus_1) * diff
            }
          }
        }
        Q_product_storage[, k] <- Q_k_e_k_plus_1
      }
    }
  }
  # Append e_1 onto the storage matrix:
  diff <- c(1, rep(0, d - 1))
  Q_product_storage <- cbind(diff, Q_product_storage)
  # Get the differences
  Q_product_storage <- Q_product_storage - vs
  return(Q_product_storage)
}

Q_m_vector_multiply_storage <- function(storage, u) {
  storage <- as.matrix(storage); d <- nrow(storage); m <- ncol(storage)
  ret <- u
  for (j in 1:m) {
    diff <- storage[, j]; diff_squared <- sum(diff ^ 2)
    if (diff_squared >= 1e-9) {
      ret <- ret - (2 / diff_squared) * sum(diff * ret) * diff
    }
  }
  return(ret)
}

Q_m_vector_multiply_iterative <- function(vs, u) {
  vs <- as.matrix(vs); d <- nrow(vs); m <- ncol(vs)
  Q_product_storage <- matrix(nrow = d, ncol = m - 1)
  ret <- u
  for (k in 1:m) {
    if (k == 1) {
      # Calculate Q_1 u
      diff <- -vs[, 1]; diff[1] <- diff[1] + 1
      squared_diff <- sum(diff ^ 2)
      if (squared_diff >= 1e-9) {
        ret <- ret - (2 / squared_diff) * sum(diff * ret) * diff
      }
      # Calculate Q_1 e_2 and store it
      diff <- -vs[, 1]; diff[1] <- diff[1] + 1
      squared_diff <- sum(diff ^ 2); e_2 <- rep(0, d); e_2[2] <- 1
      if (squared_diff >= 1e-9) {
        Q_product_storage[, 1] <- e_2 - (2 / squared_diff) * diff[2] * diff
      }
    } else {
      # Calculate Q_{k + 1} u
      diff <- Q_product_storage[, k - 1] - vs[, k]
      squared_diff <- sum(diff ^ 2)
      if (squared_diff >= 1e-9) {
        ret <- ret - (2 / squared_diff) * sum(diff * ret) * diff
      }
      # Calculate and store Q_k e_{k + 1}
      if (k < m) {
        # Initialise at e_{k + 1}
        Q_k_e_k_plus_1 <- rep(0, d); Q_k_e_k_plus_1[k + 1] <- 1
        for (s in 1:k) {
          if (s == 1) {
            # Calculate Q_1 e_{k + 1}
            diff <- -vs[, 1]; diff[1] <- diff[1] + 1
            squared_diff <- sum(diff ^ 2)
            if (squared_diff >= 1e-9) {
              Q_k_e_k_plus_1 <- Q_k_e_k_plus_1 - (2 / squared_diff) * diff[k + 1] * diff
            }
          } else {
            # Calculate Q_s e_{k + 1}
            Q_s_minus_1_e_s <- Q_product_storage[, s - 1]
            diff <- Q_s_minus_1_e_s - vs[, s]
            squared_diff <- sum(diff ^ 2)
            if (squared_diff >= 1e-9) {
              Q_k_e_k_plus_1 <- Q_k_e_k_plus_1 - (2 / squared_diff) * sum(diff * Q_k_e_k_plus_1) * diff
            }
          }
        }
        Q_product_storage[, k] <- Q_k_e_k_plus_1
      }
    }
  }
  return(ret)
}

Q_m_matrix_multiply <- function(vs, U) {
  K <- ncol(U); d <- nrow(U); ret <- matrix(ncol = K, nrow = d)
  for (j in 1:K) {
    ret[, j] <- Q_m_vector_multiply(vs, U[, j])
  }
  return(ret)
}

Q_m_transpose_vector_multiply <- function(vs, u) {
  vs <- as.matrix(vs)
  d <- nrow(vs); m <- ncol(vs)
  if (m == 1) {
    v_1 <- vs[, 1]; diff <- diag(d)[, 1] - v_1
    squared_diff <- sum(diff ^ 2)
    if (squared_diff < 1e-9) {
      return(u)
    } else {
      return(u - (2 / squared_diff) * sum(diff * u) * diff)
    }
  } else {
    new_col <- Q_m_vector_multiply(vs[, 1:(m - 1)], diag(d)[, m])
    diff <- new_col - vs[, m]; squared_diff <- sum(diff ^ 2)
    if (squared_diff > 1e-9) {
      ret <- u - (2 / squared_diff) * sum(diff * u) * diff
    } else {
      ret <- u
    }
    return(Q_m_transpose_vector_multiply(vs[, 1:(m - 1)], ret))
  }
}

Q_m_transpose_matrix_multiply <- function(vs, U) {
  K <- ncol(U); d <- nrow(U); ret <- matrix(ncol = K, nrow = d)
  for (j in 1:K) {
    ret[, j] <- Q_m_transpose_vector_multiply(vs, U[, j])
  }
  return(ret)
}

logistic_potential <- function(Y, X, x, Sigma_X, lambda) {
  n <- length(Y)
  first_likelihood_contribution <- sum(Y * (X %*% x))
  second_likelihood_contribution <- 0
  for (i in 1:n) {
    second_likelihood_contribution <- second_likelihood_contribution + log(1 + exp(-sum(x * X[i, ])))
  }
  prior_contribution <- (lambda / 2) * sum(x * (Sigma_X %*% x))
  return(first_likelihood_contribution + second_likelihood_contribution + prior_contribution)
}

logistic_gradient <- function(Y, X, x, Sigma_X, lambda) {
  n <- length(Y)
  d <- length(x)
  first_likelihood_contribution <- t(X) %*% Y
  second_likelihood_contribution <- rep(0, d)
  for (i in 1:n) {
    second_likelihood_contribution <- second_likelihood_contribution - ((1 + exp(sum(x * X[i, ]))) ^ -1) * X[i, ]
  }
  prior_contribution <- lambda * Sigma_X %*% x
  return(first_likelihood_contribution + second_likelihood_contribution + prior_contribution)
}

mala_logistic_k_chains <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, kappa) {
  # Theta is a d x k matrix representing the states of the k chains
  # Y is an n x 1 response vector
  # X is an n x d design matrix
  # lambda encodes the strength of the prior
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  
  chains <- array(dim = c(d, k, nits + 1))
  chains[, , 1] <- Theta
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * grad_log_pi_Theta
    xi <- matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * xi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
    
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
  }
  return(list(chains = chains))
}

mala_logistic_diagonal_k_chains <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, D, kappa, burn) {
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  mu <- rowMeans(Theta)
  
  chains <- array(dim = c(d, k, nits + 1))
  chains[, , 1] <- Theta
  
  for (i in 1:nits) {
    # Propose
    drift <- ((sigma ^ 2) / 2) * D * grad_log_pi_Theta
    Lxi <- (D ^ 0.5) * matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
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
    
    if (i < burn) {
      # Adapt
      mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - mu)
      gradient <- rep(0, d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * (Theta[, j] - mu) ^ 2
      }
      D <- D + (1 / (i + 1) ^ kappa) * (gradient - D)
      sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
    }
    # Storage
    chains[, , i + 1] <- Theta
  }
  return(list(chains = chains))
}

mala_logistic_dense_k_chains <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, L, kappa, burn, c) {
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  mu <- rowMeans(Theta); LLT <- L %*% t(L)
  
  chains <- array(dim = c(d, k, nits + 1))
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  chains[, , 1] <- Theta
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * LLT[1, 1]
  Sigma_ds[1] <- (sigma ^ 2) * LLT[d, d]
  mus[1, ] <- mu
  
  for (i in 1:nits) {
    L_inv <- solve(L); LLT_inv <- t(L_inv) %*% L_inv
    
    # Propose
    drift <- ((sigma ^ 2) / 2) * LLT %*% grad_log_pi_Theta
    Lxi <- L %*% matrix(rnorm(d * k), nrow = d)
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
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
    
    if (i < burn) {
      # Adapt
      learning_rate <- (1 / (i + 1) ^ kappa)
      mu <- mu + learning_rate * (rowMeans(Theta) - mu)
      # gradient <- matrix(0, nrow = d, ncol = d)
      # for (j in 1:k) {
      #   gradient <- gradient + (1 / k) * (Theta[, j] - mu) %*% t(Theta[, j] - mu)
      # }
      # LLT <- LLT + learning_rate * (gradient - LLT)
      # min_eval <- min(eigen(LLT, symmetric = TRUE, only.values = TRUE)$values)
      # if (min_eval < 0) {
      #   LLT <- LLT + (abs(min_eval) + 0.1) * diag(d)
      # }
      # L <- t(chol(LLT))
      learning_rate <- c * (1 / (i + 1) ^ kappa)
      L <- t(cholup(sqrt(1 - learning_rate) * t(L), sqrt(learning_rate * (1 / k)) * (Theta[, 1] - mu), up = TRUE))
      if (k > 1) {
        for (j in 2:k) {
          L <- t(cholup(t(L), sqrt(learning_rate * (1 / k)) * (Theta[, j] - mu), up = TRUE))
        }
      }
      LLT <- tcrossprod(L, L)
      learning_rate <- (1 / (i + 1) ^ kappa)
      sigma <- exp(log(sigma) + learning_rate * (mean(alphas, na.rm = T) - 0.574))
    }
    # Storage
    chains[, , i + 1] <- Theta
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * LLT[1, 1]
    Sigma_ds[i + 1] <- (sigma ^ 2) * LLT[d, d]
    mus[i + 1, ] <- mu
  }
  return(list(chains = chains, sigmas = sigmas, Sigma_ones = Sigma_ones, mus = mus, Sigma_ds = Sigma_ds))
}

mala_logistic_hybrid_k_chains_m_evecs <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, Q, D, kappa, c, p, m, I, burn) {
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  mu <- rowMeans(Theta); tilde_Q <- Q; tilde_D <- D
  Sigma_hat <- matrix(0, nrow = d, ncol = d)
  
  chains <- array(dim = c(d, k, nits + 1))
  Ds <- matrix(nrow = nits + 1, ncol = d)
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  Sigma_offs1 <- vector(length = nits + 1)
  Sigma_offs2 <- vector(length = nits + 1)
  Sigma_offs3 <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  v1s <- matrix(nrow = nits + 1, ncol = d)
  chains[, , 1] <- Theta
  Ds[1, ] <- D
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
  Sigma_ds[1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
  Sigma_offs1[1] <- (sigma ^ 2) * sum(Q[10, ] * D * Q[20, ])
  Sigma_offs2[1] <- (sigma ^ 2) * sum(Q[46, ] * D * Q[19, ])
  Sigma_offs3[1] <- (sigma ^ 2) * sum(Q[25, ] * D * Q[28, ])
  mus[1, ] <- mu
  v1s[1, ] <- Q[, 1]
  
  for (i in 1:nits) {
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_Theta))
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    Theta_prop <- Theta + drift + sigma * Lxi
    # Theta_prop <- Theta + sigma * Lxi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
    LLTgrad_log_pi_Theta_prop <- Q %*% (D * crossprod(Q, grad_log_pi_Theta_prop))
    
    # Accept/reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv_no_LLTinv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), Q, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    if (i < burn) {
      # Adapt
      # SG
      mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - mu)
      gradient <- matrix(0, ncol = d, nrow = d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * tcrossprod(Theta[, j] - mu, Theta[, j] - mu)
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
      
      # Make the first m columns point in one direction:
      for (j in 1:m) {
        if (tilde_Q[1, j] < 0) {tilde_Q[, j] <- -tilde_Q[, j]}
      }
      
      # Scale and diagonal
      sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))
      
      Theta_tilde <- crossprod(tilde_Q, Theta)
      mu_tilde <- crossprod(tilde_Q, mu)
      gradient <- rep(0, d)
      # 
      # # Q_inv <- solve(Q)
      # # Theta_tilde <- Q_inv %*% Theta
      # # mu_tilde <- Q_inv %*% mu
      # # gradient <- rep(0, d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * (Theta_tilde[, j] - mu_tilde) ^ 2
      }
      tilde_D <- as.vector(tilde_D + (1 / (i + 1) ^ kappa) * (gradient - tilde_D))
      if (i %% I == 0) {
        D <- tilde_D; Q <- tilde_Q
      }
    }
    # Storage
    chains[, , i + 1] <- Theta
    Ds[i + 1, ] <- D
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
    Sigma_ds[i + 1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
    Sigma_offs1[i + 1] <- (sigma ^ 2) * sum(Q[10, ] * D * Q[20, ])
    Sigma_offs2[i + 1] <- (sigma ^ 2) * sum(Q[46, ] * D * Q[19, ])
    Sigma_offs3[i + 1] <- (sigma ^ 2) * sum(Q[25, ] * D * Q[28, ])
    mus[i + 1, ] <- mu
    v1s[i + 1, ] <- Q[, 1]
    if (i > floor(nits / 2)) {
      Sigma_hat <- Sigma_hat <- Sigma_hat + (1 / floor(nits / 2)) * Q %*% diag(D) %*% t(Q)
    }
  }
  return(list(chains = chains, Ds = Ds, sigmas = sigmas, Sigma_ones = Sigma_ones, Sigma_ds = Sigma_ds, Sigma_offs1 = Sigma_offs1, mus = mus, v1s = v1s, Sigma_hat = Sigma_hat, Sigma_offs2 = Sigma_offs2, Sigma_offs3 = Sigma_offs3))
}

mala_logistic_hybrid_adam <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, Q, D, kappa, c, p, m, I, burn, m_v, m_D, s_v, s_D, b_1_v, b_2_v, b_1_D, b_2_D, epsilon_v, epsilon_D, bias_correct, fixed_learn, eta, m_mu, s_mu, b_1_mu, b_2_mu, epsilon_mu, adam_start, fixed_learn_mu, mu_kappa, fixed_learn_v, kappa_v) {
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  mu <- rowMeans(Theta); tilde_Q <- Q; tilde_D <- D
  Sigma_hat <- matrix(0, nrow = d, ncol = d)
  
  chains <- array(dim = c(d, k, nits + 1))
  Ds <- matrix(nrow = nits + 1, ncol = d)
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  Sigma_ds <- vector(length = nits + 1)
  Sigma_offs <- vector(length = nits + 1)
  mus <- matrix(nrow = nits + 1, ncol = d)
  v1s <- matrix(nrow = nits + 1, ncol = d)
  chains[, , 1] <- Theta
  Ds[1, ] <- D
  sigmas[1] <- sigma
  Sigma_ones[1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
  Sigma_ds[1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
  Sigma_offs[1] <- (sigma ^ 2) * sum(Q[2, ] * D * Q[3, ])
  mus[1, ] <- mu
  v1s[1, ] <- Q[, 1]
  
  for (i in 1:nits) {
    drift <- ((sigma ^ 2) / 2) * Q %*% (D * crossprod(Q, grad_log_pi_Theta))
    Lxi <- Q %*% (sqrt(D) * matrix(rnorm(d * k), nrow = d))
    Theta_prop <- Theta + drift + sigma * Lxi
    # Theta_prop <- Theta + sigma * Lxi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
    LLTgrad_log_pi_Theta_prop <- Q %*% (D * crossprod(Q, grad_log_pi_Theta_prop))
    
    # Accept/reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_preconditioned_mv_no_LLTinv(t(Theta), t(Theta_prop), sigma, t(Lxi), t(LLTgrad_log_pi_Theta_prop), Q, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    if (i < burn) {
      # Adapt
      # SG
      gradient <- (rowMeans(Theta) - mu)
      if (fixed_learn_mu) {
        gamma <- eta
      } else {
        gamma <- c / (i ^ mu_kappa)
      }
      m_mu <- b_1_mu * m_mu + (1 - b_1_mu) * gradient
      s_mu <- b_2_mu * s_mu + (1 - b_2_mu) * (gradient ^ 2)
      
      if (bias_correct) {
        m_mu <- ((1 - (b_1_mu ^ i)) ^ (-1)) * m_mu
        if (b_2_mu != 1) {
          s_mu <- ((1 - (b_2_mu ^ i)) ^ (-1)) * s_mu
        }
      }
      if (i < adam_start) {
        mu <- mu + gamma * gradient
      } else {
        mu <- mu + gamma * (1 / (sqrt(s_mu) + epsilon_mu)) * m_mu
      }
      
      gradient <- matrix(0, ncol = d, nrow = d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * tcrossprod(Theta[, j] - mu, Theta[, j] - mu)
      }
      gradient <- crossprod(gradient, tilde_Q[, 1:m])
      
      if (fixed_learn_v) {
        gamma <- eta
      } else {
        gamma <- c / ((i + 1) ^ kappa_v)
      }
      m_v <- b_1_v * m_v + (1 - b_1_v) * gradient
      s_v <- b_2_v * s_v + (1 - b_2_v) * (gradient ^ 2)
      
      if (bias_correct) {
        m_v <- ((1 - (b_1_v ^ i)) ^ (-1)) * m_v
        if (b_2_v != 1) {
          s_v <- ((1 - (b_2_v ^ i)) ^ (-1)) * s_v
        }
      }
      
      if (i < adam_start) {
        tilde_Q[, 1:m] <- tilde_Q[, 1:m] + gamma * gradient
      } else {
        tilde_Q[, 1:m] <- tilde_Q[, 1:m] + gamma * (1 / (sqrt(s_v) + epsilon_v)) * m_v
      }
      
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
      
      Theta_tilde <- crossprod(tilde_Q, Theta)
      mu_tilde <- crossprod(tilde_Q, mu)
      gradient <- rep(0, d)
      # 
      # # Q_inv <- solve(Q)
      # # Theta_tilde <- Q_inv %*% Theta
      # # mu_tilde <- Q_inv %*% mu
      # # gradient <- rep(0, d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * (Theta_tilde[, j] - mu_tilde) ^ 2
      }
      gradient <- gradient - tilde_D
      
      if (fixed_learn) {
        gamma <- eta
      } else {
        gamma <- c / (i ^ kappa)
      }
      m_D <- b_1_D * m_D + (1 - b_1_D) * gradient
      s_D <- b_2_D * s_D + (1 - b_2_D) * (gradient ^ 2)
      
      if (bias_correct) {
        m_D <- ((1 - (b_1_D ^ i)) ^ (-1)) * m_D
        if (b_2_D != 1) {
          s_D <- ((1 - (b_2_D ^ i)) ^ (-1)) * s_D
        }
      }
      
      if (i < adam_start) {
        tilde_D <- as.vector(tilde_D + gamma * gradient)
      } else {
        tilde_D <- as.vector(tilde_D + gamma * (1 / (sqrt(s_D) + epsilon_D)) * m_D)
      }
      
      if (i %% I == 0) {
        D <- tilde_D; Q <- tilde_Q
      }
    }
    # Storage
    chains[, , i + 1] <- Theta
    Ds[i + 1, ] <- D
    sigmas[i + 1] <- sigma
    Sigma_ones[i + 1] <- (sigma ^ 2) * sum(Q[1, ] * D * Q[1, ])
    Sigma_ds[i + 1] <- (sigma ^ 2) * sum(Q[d, ] * D * Q[d, ])
    Sigma_offs[i + 1] <- (sigma ^ 2) * sum(Q[2, ] * D * Q[3, ])
    mus[i + 1, ] <- mu
    v1s[i + 1, ] <- Q[, 1]
    if (i > floor(nits / 2)) {
      Sigma_hat <- Sigma_hat + (1 / floor(nits / 2)) * Q %*% diag(D) %*% t(Q)
    }
  }
  return(list(chains = chains, Ds = Ds, sigmas = sigmas, Sigma_ones = Sigma_ones, Sigma_ds = Sigma_ds, Sigma_offs = Sigma_offs, mus = mus, v1s = v1s, Sigma_hat = Sigma_hat))
}

mala_logistic_eigen_linear <- function(Theta, sigma, Y, X, Sigma_X, lambda, nits, vs, D, kappa, c, p, m, I, burn) {
  d <- nrow(Theta); k <- ncol(Theta); n <- length(Y);
  logpi_currs <- -logistic_potential_mv(Y, X, Theta, Sigma_X, lambda)
  grad_log_pi_Theta <- -logistic_gradient_mv(Y, X, Theta, Sigma_X, lambda)
  mu <- rowMeans(Theta); tilde_vs <- vs; tilde_D <- D
  
  chains <- array(dim = c(d, k, nits + 1))
  Ds <- matrix(nrow = nits + 1, ncol = d)
  sigmas <- vector(length = nits + 1)
  Sigma_ones <- vector(length = nits + 1)
  chains[, , 1] <- Theta
  Ds[1, ] <- D
  sigmas[1] <- sigma
  Q_m_first_row <- Q_m_transpose_vector_multiply(vs, diag(d)[, 1])
  Sigma_ones[1] <- (sigma ^ 2) * sum(Q_m_first_row * D * Q_m_first_row)
  
  for (i in 1:nits) {
    drift <- ((sigma ^ 2) / 2) * Q_m_matrix_multiply(vs, D * Q_m_transpose_matrix_multiply(vs, grad_log_pi_Theta))
    Lxi <- Q_m_matrix_multiply(vs, sqrt(D) * matrix(rnorm(d * k), nrow = d))
    Theta_prop <- Theta + drift + sigma * Lxi
    logpi_props <- -logistic_potential_mv(Y, X, Theta_prop, Sigma_X, lambda)
    grad_log_pi_Theta_prop <- -logistic_gradient_mv(Y, X, Theta_prop, Sigma_X, lambda)
    LLTgrad_log_pi_Theta_prop <- Q_m_matrix_multiply(vs, D * Q_m_transpose_matrix_multiply(vs, grad_log_pi_Theta_prop))
    
    # Accept/reject
    target_ratios <- exp(logpi_props - logpi_currs)
    proposal_ratios <- mala_proposal_ratio_linear(Theta, Theta_prop, sigma, Lxi, LLTgrad_log_pi_Theta_prop, vs, D)
    alphas <- pmin(rep(1, k), target_ratios * proposal_ratios)
    # alphas <- pmin(rep(1, k), target_ratios)
    # replace alphas whose current density = 0 with 1
    alphas[is.na(alphas)] <- 1
    Us <- runif(k); mask <- Us < alphas
    
    Theta[, mask] <- Theta_prop[, mask]; logpi_currs[mask] <- logpi_props[mask]
    grad_log_pi_Theta[, mask] <- grad_log_pi_Theta_prop[, mask]
    
    if (i < burn) {
      # Adapt
      # SG
      mu <- mu + (1 / (i + 1) ^ kappa) * (rowMeans(Theta) - mu)
      gradient <- matrix(0, ncol = d, nrow = d)
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * tcrossprod(Theta[, j] - mu, Theta[, j] - mu)
      }
      gamma <- c / (i ^ kappa)
      
      tilde_vs <- tilde_vs + gamma * crossprod(gradient, tilde_vs)
      if (m == 1) {
        tilde_vs <- tilde_vs / sqrt(sum(tilde_vs ^ 2))
      } else {
        tilde_vs <- t((sqrt(colSums(tilde_vs * tilde_vs)) ^ (-1)) * t(tilde_vs))
      }
      if (m > 1 & i %% p == 0) {
        # Orthonormalise the first 1 to m columns
        tilde_vs <- gramSchmidt(tilde_vs)$Q
      }
      
      # Scale and diagonal
      sigma <- exp(log(sigma) + (1 / (i + 1) ^ kappa) * (mean(alphas, na.rm = T) - 0.574))

      Theta_tilde <- Q_m_transpose_matrix_multiply(tilde_vs, Theta)
      mu_tilde <- Q_m_transpose_vector_multiply(tilde_vs, mu)
      gradient <- rep(0, d)
      
      for (j in 1:k) {
        gradient <- gradient + (1 / k) * (Theta_tilde[, j] - mu_tilde) ^ 2
      }
      tilde_D <- as.vector(tilde_D + (1 / (i + 1) ^ kappa) * (gradient - tilde_D))
      if (i %% I == 0) {
        D <- tilde_D; vs <- tilde_vs
      }
    }
    # Storage
    chains[, , i + 1] <- Theta
    Ds[i + 1, ] <- D
    sigmas[i + 1] <- sigma
    Q_m_first_row <- Q_m_transpose_vector_multiply(vs, diag(d)[, 1])
    Sigma_ones[i + 1] <- (sigma ^ 2) * sum(Q_m_first_row * D * Q_m_first_row)
  }
  return(list(chains = chains, Ds = Ds, sigmas = sigmas, Sigma_ones = Sigma_ones))
}

logistic_potential_mv <- function(Y, X, Theta, Sigma_X, lambda) {
  n <- length(Y); k <- ncol(Theta);
  first_likelihood_contribution <- (t(Y) %*% X) %*% Theta
  second_likelihood_contribution <- rep(0, k)
  for (i in 1:n) {
    second_likelihood_contribution <- second_likelihood_contribution + log(1 + exp(-X[i, ] %*% Theta))
  }
  prior_contribution <- (lambda / 2) * diag((t(Theta) %*% Sigma_X) %*% Theta)
  return(first_likelihood_contribution + second_likelihood_contribution + prior_contribution)
}

logistic_gradient_mv <- function(Y, X, Theta, Sigma_X, lambda) {
  n <- length(Y); d <- nrow(Theta); k <- ncol(Theta);
  # matrix with k columns where each column is Y
  Ys <- matrix(rep(Y, k), ncol = k)
  first_likelihood_contribution <- t(X) %*% Ys
  # second_likelihood_contribution <- matrix(0, nrow = n, ncol = k)
  # for (i in 1:n) {
  #   # Xs <- matrix(rep(X[i, ], k), ncol = k)
  #   # second_likelihood_contribution <- second_likelihood_contribution - Xs %*% diag(as.vector((1 + exp(X[i, ] %*% Theta)) ^ -1))
  #   # second_likelihood_contribution <- second_likelihood_contribution - t(as.vector((1 + exp(X[i, ] %*% Theta)) ^ -1) * t(Xs))
  #   second_likelihood_contribution[i, ] <- (1 + exp(X[i, ] %*% Theta)) ^ -1
  # }
  second_likelihood_contribution <- -(1 + exp(X %*% Theta)) ^ -1
  second_likelihood_contribution <- t(X) %*% second_likelihood_contribution
  prior_contribution <- lambda * Sigma_X %*% Theta
  return(first_likelihood_contribution + second_likelihood_contribution + prior_contribution)
}

mala_proposal_ratio_preconditioned_mv <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, LLT_inv) {
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  I_1 <- diag(D_1 %*% LLT_inv %*% t(D_1))
  I_2 <- diag(D_2 %*% LLT_inv %*% t(D_2))
  
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

mala_proposal_ratio_linear <- function(X, X_prop, sigma, Lxi, LLTgrad_log_pi_X_prop, vs, D) {
  # O(k ^ 3 d)
  d <- nrow(X); k <- ncol(X)
  D_1 <- X - X_prop - ((sigma ^ 2) / 2) * LLTgrad_log_pi_X_prop
  D_2 <- sigma * Lxi
  
  ret <- vector(length = k)
  for (j in 1:k) {
    i_1 <- sum(D_1[, j] * Q_m_vector_multiply(vs, (D ^ (-1)) * Q_m_transpose_vector_multiply(vs, D_1[, j])))
    i_2 <- sum(D_2[, j] * Q_m_vector_multiply(vs, (D ^ (-1)) * Q_m_transpose_vector_multiply(vs, D_2[, j])))
    
    ret[j] <- exp(-((1 / (2 * (sigma ^ 2))) * (i_1 - i_2)))
  }
  return(ret)
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

n <- 150; d <- 150;
no_significant_evals <- 3; significant_eval <- 1
significant_evals <- significant_eval + (significant_eval / (10 ^ 3)) * rnorm(no_significant_evals)
X_spectrum <- c(significant_evals, rep(sqrt(1000), min(n, d) - no_significant_evals))
X <- Haar_sample(n) %*% diag(X_spectrum, nrow = n, ncol = d) %*% Haar_sample(d)

XTX <- t(X) %*% X
beta <- rnorm(n = d); Y <- ifelse(runif(n) <= (1 + exp(-X %*% beta)) ^ -1, 1, 0)
Sigma_X <- (1 / n) * XTX
Sigma_X_inv <- solve(Sigma_X)
Sigma_X_inv_sqrt <- sqrtm(Sigma_X_inv)
lambda <- 0.01

evals <- eigen(Sigma_X, only.values = T)$values
inverse_evals <- rev(1 / evals)
plot(1:length(evals), inverse_evals)
conditions <- inverse_evals / min(inverse_evals)
plot(1:length(evals), conditions)

x <- rep(0, d); kappa <- 0.8
potential_curr <- logistic_potential(Y, X, x, Sigma_X, lambda)
i <- 1
while (T) {
  eta <- 2 / (max(evals) + min(evals)) * (i ^ (-kappa))
  x <- x - eta * Sigma_X_inv_sqrt %*% logistic_gradient(Y, X, x, Sigma_X, lambda)
  potential_new <- logistic_potential(Y, X, x, Sigma_X, lambda)
  potential_difference <- abs(potential_curr - potential_new)
  if (potential_difference < .Machine$double.eps || i > 10000) {
    break
  } else {
    potential_curr <- potential_new
    i <- i + 1
  }
}
logistic_mode <- x

nits_coeff <- 15000; nits <- nits_coeff * d ^ 0.5; k <- 2; kappa <- 0.9
sigma <- 0.5 / (d ^ (1 / 4)); Theta <- matrix(rep(logistic_mode, k), ncol = k)
burn <- nits

start_time <- Sys.time()
out <- mala_logistic_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

D <- rep(1, d)
start_time <- Sys.time()
out <- mala_logistic_diagonal_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits, D, kappa, burn)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

L <- Sigma_X_inv_sqrt; c <- 1; kappa <- 0.9
start_time <- Sys.time()
out <- mala_logistic_dense_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits, L, kappa, burn, c)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains;
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)], main = 'Traceplot, dense, MALA')
plot(1:(nits + 1), out$sigmas[1:(nits + 1)], main = 'Sigmas, dense, MALA')
plot(1:(nits + 1), out$Sigma_ones[1:(nits + 1)], main = 'First Diagonal, dense, MALA')
plot(1:(nits + 1), out$Sigma_ds, main = 'Last Diagonal, dense, MALA')
plot(1:(nits + 1), out$mus[, 1], main = 'First mean, dense, MALA')
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

D <- rep(1, d); c <- 1; p <- 1; m <- 3; I <- 1; kappa <- 0.9
vs <- eigen(Sigma_X_inv, symmetric = TRUE)$vectors[, 1:m]; Q <- Q_m(vs)
start_time <- Sys.time()
out <- mala_logistic_hybrid_k_chains_m_evecs(Theta, sigma, Y, X, Sigma_X, lambda, nits, Q, D, kappa, c, p, m, I, burn)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)], main = 'Traceplot, eigen, MALA')
plot(1:(nits + 1), out$Ds[1:(nits + 1), 1], main = 'First leading e.val, eigen, MALA')
plot(1:(nits + 1), out$sigmas[1:(nits + 1)], main = 'Sigmas, eigen, MALA')
plot(1:(nits + 1), out$Sigma_ones, main = 'First Diagonal, eigen, MALA')
plot(floor((nits + 1) / 2):(nits + 1), out$Sigma_ones[floor((nits + 1) / 2):(nits + 1)], main = 'First Diagonal, eigen, MALA, last half')
plot(1:(nits + 1), out$Sigma_ds, main = 'Last Diagonal, eigen, MALA')
plot(1:(nits + 1), out$Sigma_offs1, main = 'Off Diagonal, eigen, MALA')
plot(1:(nits + 1), out$Sigma_offs2, main = 'Off Diagonal')
plot(1:(nits + 1), out$Sigma_offs3, main = 'Off Diagonal')
plot(1:(nits + 1), out$v1s[, 1], main = 'First leading e.vec, eigen, MALA')
plot(1:(nits + 1), out$mus[, 1], main = 'First mean, eigen MALA')
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

D <- rep(1, d); c <- 1; p <- 1; m <- 3; I <- 1; kappa <- 0.7
vs <- eigen(Sigma_X_inv, symmetric = TRUE)$vectors[, 1:m];
start_time <- Sys.time()
out <- mala_logistic_eigen_linear(Theta, sigma, Y, X, Sigma_X, lambda, nits, vs, D, kappa, c, p, m, I, burn)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$Ds[1:(nits + 1)])
plot(1:(nits + 1), out$sigmas[1:(nits + 1)])
plot(1:(nits + 1), out$Sigma_ones[1:(nits + 1)])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

D <- rep(1, d); c <- 0.1; p <- 1; m <- 3; I <- 1; kappa <- 0.9
vs <- eigen(Sigma_X_inv, symmetric = TRUE)$vectors[, 1:m]; Q <- Q_m(vs)
m_v <- matrix(0, nrow = d, ncol = m); m_D <- rep(0, d); s_v <- matrix(0, nrow = d, ncol = m)
s_D <- rep(0, d); b_1_v <- 0.9; b_2_v <- 0.999; b_1_D <- 0.9; b_2_D <- 0.999
epsilon_v <- 10 ^ (-6); epsilon_D <- 10 ^ (-6); bias_correct <- F;
fixed_learn <- T; eta <- 0.0005; m_mu <- rep(0, d); b_1_mu <- 0.9; b_2_mu <- 0.999
epsilon_mu <- 10 ^ (-6); s_mu <- rep(0, d); adam_start <- 0; fixed_learn_mu <- F
mu_kappa <- 0.9; fixed_learn_v <- T; kappa_v <- 0.7
start_time <- Sys.time()
out <- mala_logistic_hybrid_adam(Theta, sigma, Y, X, Sigma_X, lambda, nits, Q, D, kappa, c, p, m, I, burn, m_v, m_D, s_v, s_D, b_1_v, b_2_v, b_1_D, b_2_D, epsilon_v, epsilon_D, bias_correct, fixed_learn, eta, m_mu, s_mu, b_1_mu, b_2_mu, epsilon_mu, adam_start, fixed_learn_mu, mu_kappa, fixed_learn_v, kappa_v)
end_time <- Sys.time()
time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))

chains <- out$chains
plot(1:(nits + 1), chains[1, 1, 1:(nits + 1)])
plot(1:(nits + 1), out$Ds[1:(nits + 1), 1])
plot(1:(nits + 1), out$sigmas[1:(nits + 1)])
plot(1:(nits + 1), out$Sigma_ones[1:(nits + 1)])
plot(1:(nits + 1), out$Sigma_ds[1:(nits + 1)])
plot(1:(nits + 1), out$Sigma_offs[1:(nits + 1)])
plot(1:(nits + 1), out$v1s[, 1])
hist(out$v1s)
plot(1:(nits + 1), out$mus[, 1])
plot(chains[1, 1, 1:(nits + 1)], chains[2, 1, 1:(nits + 1)])
ESSs <- ESS_k_chains(chains); ESSs
ESSs / time_taken

ds <- c(50, 100, 150); ms <- c(1, 2, 3, 4, 5, 6)
replications <- 15; types <- c('none', 'diagonal', 'dense', 'eigen', 'eigen linear')
burn_ins <- c("no burn", "burn")

column_names <- c('minESS', 'medESS', 'time', 'minESSperSec', 'medESSperSec', 'type', 'no_evecs', 'dimension', "burn_in")
df <- data.frame(matrix(ncol = length(column_names), nrow = 0))
colnames(df) <- column_names

v <- 0
for (burn_in in burn_ins) {
  for (d in ds) {
    for (replication in 1:replications) {
      # set up target
      n <- d
      no_significant_evals <- 3; significant_eval <- 1
      significant_evals <- significant_eval + (significant_eval / (10 ^ 3)) * rnorm(no_significant_evals)
      X_spectrum <- c(significant_evals, rep(sqrt(1000), min(n, d) - no_significant_evals))
      X <- Haar_sample(n) %*% diag(X_spectrum, nrow = n, ncol = d) %*% Haar_sample(d)
      
      XTX <- t(X) %*% X
      beta <- rnorm(n = d); Y <- ifelse(runif(n) <= (1 + exp(-X %*% beta)) ^ -1, 1, 0)
      Sigma_X <- (1 / n) * XTX
      Sigma_X_inv <- solve(Sigma_X)
      Sigma_X_inv_sqrt <- sqrtm(Sigma_X_inv)
      lambda <- 0.01
      
      evals <- eigen(Sigma_X, only.values = T)$values
      
      # Initialise the Markov chain
      x <- rep(0, d); kappa <- 0.9
      potential_curr <- logistic_potential(Y, X, x, Sigma_X, lambda)
      i <- 1
      while (T) {
        eta <- 2 / (max(evals) + min(evals)) * (i ^ (-kappa))
        x <- x - eta * Sigma_X_inv_sqrt %*% logistic_gradient(Y, X, x, Sigma_X, lambda)
        potential_new <- logistic_potential(Y, X, x, Sigma_X, lambda)
        potential_difference <- abs(potential_curr - potential_new)
        if (potential_difference < .Machine$double.eps || i > 10000) {
          break
        } else {
          potential_curr <- potential_new
          i <- i + 1
        }
      }
      logistic_mode <- x
      
      nits_coeff <- 15000; nits <- nits_coeff * d ^ 0.5; k <- 2; kappa <- 0.9
      sigma <- 0.5 / (d ^ (1 / 4)); Theta <- matrix(rep(logistic_mode, k), ncol = k)
      if (burn_in == "burn") {
        burn <- floor(nits / 2)
      } else {
        burn <- nits
      }
      
      for (type in types) {
        if (type == 'none') {
          start_time <- Sys.time()
          out <- mala_logistic_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d, burn_in)
          
        } else if (type == 'diagonal') {
          D <- rep(1, d); kappa <- 0.9
          start_time <- Sys.time()
          out <- mala_logistic_diagonal_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits, D, kappa, burn)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d, burn_in)
          
        } else if (type == 'dense') {
          L <- Sigma_X_inv_sqrt; c <- 1; kappa <- 1
          start_time <- Sys.time()
          out <- mala_logistic_dense_k_chains(Theta, sigma, Y, X, Sigma_X, lambda, nits, L, kappa, burn, c)
          end_time <- Sys.time()
          time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
          
          chains <- out$chains;
          ESSs <- ESS_k_chains(chains)
          
          df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, 0, d, burn_in)
          
        } else if (type == 'eigen') {
          for (m in ms) {
            D <- rep(1, d); c <- 0.00001; p <- 1; I <- 1; kappa <- 0.9
            vs <- eigen(Sigma_X_inv, symmetric = TRUE)$vectors[, 1:m]; Q <- Q_m(vs)
            start_time <- Sys.time()
            out <- mala_logistic_hybrid_k_chains_m_evecs(Theta, sigma, Y, X, Sigma_X, lambda, nits, Q, D, kappa, c, p, m, I, burn)
            end_time <- Sys.time()
            time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
            
            chains <- out$chains;
            ESSs <- ESS_k_chains(chains)
            
            df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, m, d, burn_in)
            
          }
        } else if (type == 'eigen linear') {
          for (m in 1:2) {
            D <- rep(1, d); c <- 0.00001; p <- 1; I <- 1; kappa <- 0.9
            vs <- eigen(Sigma_X_inv, symmetric = TRUE)$vectors[, 1:m];
            start_time <- Sys.time()
            out <- mala_logistic_eigen_linear(Theta, sigma, Y, X, Sigma_X, lambda, nits, vs, D, kappa, c, p, m, I, burn)
            end_time <- Sys.time()
            time_taken <- as.numeric(difftime(end_time, start_time, unit = 'secs'))
            
            chains <- out$chains;
            ESSs <- ESS_k_chains(chains)
            
            df[nrow(df) + 1,] <- c(min(ESSs), median(ESSs), time_taken, min(ESSs) / time_taken, median(ESSs) / time_taken, type, m, d, burn_in)
            
          }
        }
      }
    }
    print(v)
    v <- v + 1
  }
}

df$minESS <- as.numeric(df$minESS); df$medESS <- as.numeric(df$medESS)
df$time <- as.numeric(df$time); df$minESSperSec <- as.numeric(df$minESSperSec)
df$medESSperSec <- as.numeric(df$medESSperSec)
df$no_evecs <- as.numeric(df$no_evecs); df$dimension <- as.numeric(df$dimension)

save(df, file = 'synthetic_data_logistic_regression_many_evecs_burn_ins.RData')

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen") | df$type == "none", ], aes(x = as.factor(dimension), y = minESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESS, various m's, k = 2, 3 significant e.vecs, eigen") +
  facet_wrap(vars(burn_in))
p

save_plot('minESS_various_ms_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen") | df$type == "none", ], aes(x = as.factor(dimension), y = medESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESS, various m's, k = 2, 3 significant e.vecs, eigen") +
  facet_wrap(vars(burn_in)) +
  ylim(0, 175)
p

save_plot('medESS_various_ms_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen") | df$type == "none", ], aes(x = as.factor(dimension), y = log(minESSperSec), color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESSperSec, various m's, k = 2, 3 significant e.vecs, eigen") +
  facet_wrap(vars(burn_in))
p

save_plot('minESSperSec_various_ms_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen") | df$type == "none", ], aes(x = as.factor(dimension), y = log(medESSperSec), color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESSperSec, various m's, k = 2, 3 significant e.vecs, eigen") +
  facet_wrap(vars(burn_in))
p

save_plot('medESSperSec_various_ms_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen linear") | df$type == "none", ], aes(x = as.factor(dimension), y = minESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESS, various m's, k = 2, 3 significant e.vecs, linear") +
  facet_wrap(vars(burn_in))
p

save_plot('minESS_various_ms_burn_in_linear.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen linear") | df$type == "none", ], aes(x = as.factor(dimension), y = medESS, color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESS, various m's, k = 2, 3 significant e.vecs, linear") +
  facet_wrap(vars(burn_in)) +
  ylim(0, 175)
p

save_plot('medESS_various_ms_burn_in_linear.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen linear") | df$type == "none", ], aes(x = as.factor(dimension), y = log(minESSperSec), color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESSperSec, various m's, k = 2, 3 significant e.vecs, linear") +
  facet_wrap(vars(burn_in))
p

save_plot('minESSperSec_various_ms_burn_in_linear.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs > 0 & df$type == "eigen linear") | df$type == "none", ], aes(x = as.factor(dimension), y = log(medESSperSec), color = as.factor(no_evecs))) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension', color = 'm') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESSperSec, various m's, k = 2, 3 significant e.vecs, linear") +
  facet_wrap(vars(burn_in))
p

save_plot('medESSperSec_various_ms_burn_in_linear.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 3 | df$no_evecs == 0) & df$type != "eigen linear", ], aes(x = as.factor(dimension), y = minESS, color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("minESS, k = 2, 3 significant e.vecs") +
  facet_wrap(vars(burn_in))
p

save_plot('minESS_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 3 | df$no_evecs == 0) & df$type != "eigen linear", ], aes(x = as.factor(dimension), y = medESS, color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("medESS, k = 2, 3 significant e.vecs") +
  facet_wrap(vars(burn_in)) +
  ylim(0, 250)
p

save_plot('medESS_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 3 | df$no_evecs == 0) & df$type != "eigen linear", ], aes(x = as.factor(dimension), y = log(minESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log(minESSperSec), k = 2, 3 significant e.vecs") +
  facet_wrap(vars(burn_in))
p

save_plot('log_minESSperSec_burn_in.svg', fig = p, width = 16, height = 13)

p <- ggplot(df[(df$no_evecs == 3 | df$no_evecs == 0) & df$type != "eigen linear", ], aes(x = as.factor(dimension), y = log(medESSperSec), color = type)) +
  geom_boxplot(linewidth = 0.3, outlier.size = 0.5) +
  labs(x = 'dimension') +
  theme_gray(base_size = 10) +
  theme(legend.margin=margin(c(0.1,0.1,0.1,0.1))) +
  ggtitle("log(medESSperSec), k = 2, 3 significant e.vecs") +
  facet_wrap(vars(burn_in))
p

save_plot('log_medESSperSec_burn_in.svg', fig = p, width = 16, height = 13)








