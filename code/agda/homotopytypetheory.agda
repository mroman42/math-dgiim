{-# OPTIONS --without-K #-}

module homotopytypetheory where

  -- Equalities between natural numbers
  module Chapter-2-13 where
    data _==_ {l} {A : Set l} : A → A → Set l where
      refl : (x : A) → x == x

    ap : {A B : Set} → {a b : A} → (f : A → B) → a == b → f a == f b
    ap f (refl x) = refl (f x)

    transport : {A : Set} → {P : A → Set} → {x y : A} → (x == y) → P x → P y
    transport (refl x) u = u

    _·_ : {A : Set} → {x y z : A} → (p : x == y) → (q : y == z) → x == z
    (refl x) · (refl .x) = refl x

    data ℕ : Set where
      O : ℕ
      S : ℕ → ℕ

    data ⊥ : Set where

    record ⊤ : Set where
      constructor ✦
  
    -- 2.13. Natural numbers equalities
    code : ℕ → ℕ → Set
    code O     O     = ⊤
    code O     (S m) = ⊥
    code (S n) O     = ⊥
    code (S n) (S m) = code n m

    r : (n : ℕ) → code n n
    r O     = ✦
    r (S n) = r n

    -- 2.13.1. Encoding and decoding of natural numbers
    encode : (m n : ℕ) → (m == n) → code m n
    encode m .m (refl .m) = r m

    decode : (m n : ℕ) → code m n → m == n
    decode O     O     c = refl O
    decode O     (S n) ()
    decode (S m) O     ()
    decode (S m) (S n) c = ap S (decode m n c)


    inverse-l : {m n : ℕ} → (p : m == n) → decode m n (encode m n p) == p
    inverse-l (refl x) = decode-diag
      where
        decode-diag : {n : ℕ} → decode n n (r n) == refl n
        decode-diag {O}   = refl (refl O)
        decode-diag {S n} = ap (ap S) decode-diag

    inverse-r : {m n : ℕ} → (c : code m n) → encode m n (decode m n c) == c
    inverse-r {O}   {O}   ✦  = refl ✦
    inverse-r {O}   {S n} ()
    inverse-r {S m} {O}   ()
    inverse-r {S m} {S n} c with (decode m n c)
    inverse-r {S m} {S .m} c | refl .m = encode-diag (S m) · (codes-are-diag {S m} c)
      where
        encode-diag : (n : ℕ) → encode n n (refl n) == r n
        encode-diag n = refl (r n)

        codes-are-diag : {n : ℕ} → (c : code n n) → r n == c
        codes-are-diag {O}   ✦ = refl ✦
        codes-are-diag {S n} c = codes-are-diag {n} c
        

    -- 2.13.2. Zero is not a successor
    zero-is-not-succ : {m : ℕ} → (S m == O) → ⊥
    zero-is-not-succ {m} = encode (S m) O

    -- 2.13.3. Injectivity of successor
    succ-is-injective : {m n : ℕ} → S m == S n → m == n
    succ-is-injective {m} {n} p = decode m n (encode (S m) (S n) p)

    -- wtf? why does this work?
    succ-is-injective' : {m n : ℕ} → S m == S n → m == n
    succ-is-injective' {m} {n} (refl .(S m)) = refl m
