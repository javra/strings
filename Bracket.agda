{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Diags
open import Arity
open import Sliding
open import Identities

/nsuc : ∀{n} → /n {suc n} ~* ∣ ⊗ /n · / ⊗ ∣ ^⊗ n
/nsuc {zero} = ·∣∣ ■ ι ε⊗ ■ - (ι ⊗ε) ■ - ∣∣·
/nsuc {suc n} = ·~* (~⊗* (/nsuc {n}) ■ - ⊗∣·⊗∣ ■ ·~* (-⊗⊗ ■ ⊗~* (- ∣^⊗suc)) ■ ~·* -⊗⊗)
                ■ ι ·· ■ ~·* (~·* -⊗⊗ ■ ∣⊗·∣⊗)

/n+ : ∀{m n} → /n {m + n} ~* ∣ ^⊗ m ⊗ /n {n} · /n {m} ⊗ ∣ ^⊗ n
/n+ {m} {zero} = - (~·* (- ∣^⊗suc) ■ ι ∣n· ■ ι ⊗ε)
/n+ {m} {suc n} = ·~* (~⊗* (/n+ {m} {n}) ■ - ⊗∣·⊗∣ ■ ·~* (-⊗⊗ ■ ⊗~* (- ∣^⊗suc))) ■ ι ··
                  ■ ~·* (~·* (~⊗* ∣^⊗+ ■ -⊗⊗) ■ ·~* -⊗⊗ ■ ∣n⊗·∣n⊗)

/n·∣⊗ : ∀{m n}{d : D m n} → /n · ∣ ⊗ d ~* d ⊗ ∣ · /n
/n·∣⊗ {d = ε}     = ·~* (ι ⊗ε) ■ - (~·* (ι ε⊗))
/n·∣⊗ {d = ∣}     = ·∣∣ ■ - ∣∣·
/n·∣⊗ {d = d · e} = ·~* (- ∣⊗·∣⊗) ■ ι ·· ■ ~·* /n·∣⊗ ■ -·· ■ ·~* /n·∣⊗
                    ■ ι ·· ■ ~·* ⊗∣·⊗∣
/n·∣⊗ {d = _⊗_ {m} {n} {k} {l} d e}
                  = ~·* (/n+ {m}{k})
                    ■ -·· ■ ·~* (·~* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ~⊗* /n·∣⊗ ■ ι ·⊗·)
                    ■ ι ·· ■ ~·* (·~* -⊗⊗ ■ ∣n⊗·⊗∣m) ■ ·~* (- ∣n⊗·⊗∣m) ■ ι ··
                    ■ ~·* (·~* (~⊗* ∣^⊗suc ■ -⊗⊗)
                           ■ - (ι ·⊗·) ■ ⊗~* /n·∣⊗ ■ ι ·⊗· ■ ~·* (ι ⊗⊗))
                    ■ -·· ■ ·~* (- (/n+ {n} {l}))
/n·∣⊗ {d = ∩}     = ∣· ■ - (ι ∩∣∣//∣) ■ -··
                    ■ ·~* (~·* (~⊗* (- (ι ⊗ε))) ■ ·~* (~⊗* (- (·∣∣ ■ ι ε⊗))))
/n·∣⊗ {d = ∪}     = ~·* (~·* (~⊗* (ι ⊗ε)) ■ ·~* (~⊗* (·∣∣ ■ ι ε⊗)))
                    ■ ι ∣//∣∣∪ ■ - ·∣
/n·∣⊗ {d = /}     = ~·* (~·* (~⊗* (ι ⊗ε)) ■ ·~* (~⊗* (·∣∣ ■ ι ε⊗))) ■ - (ι ///)
                    ■ -·· ■ ·~* (~·* (~⊗* (- (ι ⊗ε))) ■ ·~* (- (~⊗* (·∣∣ ■ ι ε⊗))))
/n·∣⊗ {d = R}     = ι /nR
/n·∣⊗ {d = M}     = ι /nM

/-nsuc : ∀{n} → /-n {suc n} ~* /-n ⊗ ∣ · ∣ ^⊗ _ ⊗ /
/-nsuc {zero}  = ~·* (ι ⊗ε) ■ ·∣∣ ■ - ∣∣· ■ ·~* (- (ι ε⊗))
/-nsuc {suc n} = ·~* (⊗~* (/-nsuc {n}) ■ - ∣⊗·∣⊗ ■ ·~* (ι ⊗⊗)) ■ ι ··
                 ■ ~·* (~·* (⊗~* ∣^⊗suc ■ ι ⊗⊗) ■ ·~* (ι ⊗⊗) ■ ⊗∣·⊗∣)

/-n+ : ∀{m n} → /-n {m + n} ~* /-n {m} ⊗ ∣ ^⊗ n · ∣ ^⊗ m ⊗ /-n {n}
/-n+ {zero}  {n} = - (ι ∣n· ■ ι ε⊗)
/-n+ {suc m} {n} = ·~* (⊗~* (/-n+ {m} {n}) ■ - ∣⊗·∣⊗ ■ ·~* (ι ⊗⊗)) ■ ι ··
                   ■ ~·* (~·* (⊗~* (∣^⊗+ {m}{n}) ■ ι ⊗⊗) ■ ·~* (ι ⊗⊗) ■ ⊗∣n·⊗∣n)

/-n·⊗∣ : ∀{m n}{d : D m n} → /-n · d ⊗ ∣ ~* ∣ ⊗ d · /-n
/-n·⊗∣ {d = ε}     = ∣· ■ ι ε⊗ ■ - (ι ⊗ε) ■ - ·∣
/-n·⊗∣ {d = ∣}     = ·∣∣ ■ - ∣∣·
/-n·⊗∣ {d = d · e} = ·~* (- ⊗∣·⊗∣) ■ ι ·· ■ ~·* /-n·⊗∣ ■ -·· ■ ·~* /-n·⊗∣
                     ■ ι ·· ■ ~·* ∣⊗·∣⊗
/-n·⊗∣ {d = _⊗_ {m}{n}{k}{l} d e} = ~·* (/-n+ {m}{k})
                     ■ -·· ■ ·~* (·~* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* /-n·⊗∣ ■ ι ·⊗·)
                     ■ ι ·· ■ ~·* (·~* (ι ⊗⊗ ■ ~⊗* (- ∣^⊗suc)) ■ ⊗∣n·∣m⊗)
                     ■ ·~* (- ⊗∣n·∣m⊗) ■ ι ·· ■ ~·* (·~* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ~⊗* /-n·⊗∣)
                     ■ ~·* (ι ·⊗· ■ ~·* -⊗⊗) ■ -·· ■ ·~* (- (/-n+ {n} {l}))
/-n·⊗∣ {d = ∩}     = - (ι ·· ■ ·~* (⊗~* (·∣∣ ■ ι ⊗ε)) ■ ~·* (·~* (⊗~* (ι ⊗ε))) ■ ι ∣∩/∣∣/ ■ - ∣·)
/-n·⊗∣ {d = ∪}     = ~·* (~·* (⊗~* (ι ⊗ε)) ■ ·~* (⊗~* (·∣∣ ■ ι ⊗ε))) ■ ι /∣∣/∪∣ ■ - ·∣
/-n·⊗∣ {d = /}     = ~·* (~·* (⊗~* (ι ⊗ε)) ■ ·~* (⊗~* (·∣∣ ■ ι ⊗ε))) ■ ι ///
                     ■ - (·~* (~·* (⊗~* (ι ⊗ε)) ■ ·~* (⊗~* (·∣∣ ■ ι ⊗ε))) ■ ι ··)
/-n·⊗∣ {d = R}     = ι /-nR
/-n·⊗∣ {d = M}     = ι /-nM

∩∣n/n∪∣n : ∀{n} → ∩ ⊗ ∣ ^⊗ (suc n) · ∣ ⊗ /n {suc n} · ∪ ⊗ ∣ ^⊗ (suc n) ~* /n {n}
∩∣n/n∪∣n {n} = ~·* (·~* (⊗~* (/nsuc {n}) ■ - ∣⊗·∣⊗) ■ ι ··
                    ■ ~·* (·~* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ~⊗* ·∣∣ ■ ⊗~* (ι ∣n·)) ■ ·~* (ι ⊗⊗))
               ■ ∩⊗·∣/⊗·∪⊗ ■ ι ·∣n ■ ι ·∣n

∣n∩/-n∣n∪ : ∀{n} → ∣ ^⊗ (suc n) ⊗ ∩ · /-n {suc n} ⊗ ∣ · ∣ ^⊗ (suc n) ⊗ ∪ ~* /-n {n}
∣n∩/-n∣n∪ = ~·* (·~* (~⊗* /-nsuc ■ - ⊗∣·⊗∣ ■ ~·* -⊗⊗) ■ ι ·· ■ ~·* (- (ι ·⊗·) ■ ⊗~* ·∣∣))
            ■ ⊗∩·⊗/∣·⊗∪ ■ ι ·∣n ■ ·~* (- ∣^⊗suc) ■ ι ·∣n ■ ι ∣n·

∩n : ∀{n} → D n (n + 2)
∩n {n} = ∣ ^⊗ n ⊗ ∩ · /n ⊗ ∣

∩n·∣⊗∣ : ∀{m n}{d : D m n} → ∩n · ∣ ⊗ d ⊗ ∣ ~* d · ∩n
∩n·∣⊗∣ = -·· ■ ·~* (- (ι ·⊗·) ■ ~⊗* /n·∣⊗ ■ ι ·⊗·)
         ■ ι ·· ■ ~·* (·~* -⊗⊗ ■ - (ι ·⊗·) ■ ~⊗* (ι ∣n·) ■ ⊗~* ·∣∣)
         ■ ~·* (~⊗* (- (ι ·∣n)) ■ - ·⊗∩) ■ -··

∪n : ∀{n} → D (n + 2) n
∪n {n} = ∣ ⊗ /n · ∪ ⊗ ∣ ^⊗ n

∣⊗∣·∪n : ∀{m n}{d : D m n} → ∣ ⊗ d ⊗ ∣ · ∪n ~* ∪n · d
∣⊗∣·∪n = ι ·· ■ ~·* (~·* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* (- /n·∣⊗) ■ ι ·⊗·) ■ -··
         ■ ·~* (~·* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ⊗~* (ι ·∣n) ■ ~⊗* ∣∣· ■ ⊗~* (- (ι ∣n·)) ■ - ∪⊗·) ■ ι ··

∩-n : ∀{n} → D n (n + 2)
∩-n {n} = ∩ ⊗ ∣ ^⊗ n · ∣ ⊗ /-n

∩-n·∣⊗∣ : ∀{m n}{d : D m n} → ∩-n · ∣ ⊗ d ⊗ ∣ ~* d · ∩-n
∩-n·∣⊗∣ = -·· ■ ·~* (·~* -⊗⊗ ■ - (ι ·⊗·) ■ ⊗~* /-n·⊗∣ ■ ι ·⊗·) ■ ι ·· ■ ~·* (·~* (ι ⊗⊗) ■ ⊗∣n·∣∣⊗)
          ■ ~·* (- ·⊗∣n) ■ -··

∪-n : ∀{n} → D (n + 2) n
∪-n {n} = /-n ⊗ ∣ · ∣ ^⊗ n ⊗ ∪

∣⊗∣·∪-n : ∀{m n}{d : D m n} → ∣ ⊗ d ⊗ ∣ · ∪-n ~* ∪-n · d
∣⊗∣·∪-n = ι ·· ■ ~·* (- (ι ·⊗·) ■ ~⊗* (- /-n·⊗∣) ■ ι ·⊗·) ■ -··
          ■ ·~* (⊗∣∣·∣n⊗ ■ - ∣n⊗·) ■ ι ··

∩∣n∩·∪n : ∀{n} → ∩ ⊗ ∣ ^⊗ n ⊗ ∩ · ∪n ~* ∩n
∩∣n∩·∪n {n} = ι ·· ■ ~·* (·~* (- ∣⊗·∣⊗) ■ ι ·· ■ ~·* (·~* (ι ⊗⊗) ■ - (ι ·⊗·) ■ ⊗~* (ι ∩/)
                                                      ■ ~⊗* (ι ·∣n ■ - (ι ∣n·)) ■ ⊗~* (- ·∣∣) ■ ι ·⊗·))
              ■ -·· ■ -··
              ■ ·~* (~·* (ι ⊗⊗) ■ ·~* (~·* (⊗~* (- ⊗∣·⊗∣) ■ - ∣⊗·∣⊗ ■ ~·* (ι ⊗⊗) ■ ·~* (ι ⊗⊗)) ■ ·~* (ι ⊗⊗ ■ ⊗~* ∣^⊗suc ■ ι ⊗⊗))
                     ■ ·~* (~·* ⊗∣·⊗∣ ■ ⊗∣·⊗∣) ■ ⊗∣·⊗∣
                     ■ ~⊗* (ι ·· ■ ~·* (~·* (-⊗⊗ ■ ⊗~* (- ∣^⊗suc)) ■ ·~* ∣⊗·∣⊗) ■ ·~* -⊗⊗ ■ ∩∣n/n∪∣n))

∩n·∪∣n∪ : ∀{n} → ∩n · ∪ ⊗ ∣ ^⊗ n ⊗ ∪ ~* ∪n
∩n·∪∣n∪ = {!!}

∩∣n∩·∪-n : ∀{n} → ∩ ⊗ ∣ ^⊗ n ⊗ ∩ · ∪-n ~* ∩-n
∩∣n∩·∪-n = ι ·· ■ ~·* (·~* (- ⊗∣·⊗∣) ■ ι ·· ■ ~·* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ - (ι ·⊗·) ■ ~⊗* (ι ∩/)
                                                  ■ ⊗~* (·~* (-⊗⊗ ■ ⊗~* (- ∣^⊗suc)) ■ ι ·∣n ■ - (ι ∣n·)) ■ ~⊗* (- ·∣∣) ■ ι ·⊗·))
           ■ -·· ■ -··
           ■ ·~* (·~* (~·* (~⊗* (- ∣⊗·∣⊗) ■ - ⊗∣·⊗∣)) ■ ι ·· ■ ·~* -⊗⊗
           ■ ~·* (~·* (-⊗⊗ ■ ⊗~* (ι ⊗⊗)) ■ ·~* (~·* -⊗⊗ ■ ·~* -⊗⊗ ■ ∣⊗·∣⊗))
           ■ ~·* (·~* (⊗~* ⊗∣·⊗∣) ■ ∣⊗·∣⊗) ■ ∣⊗·∣⊗ ■ ⊗~* ∣n∩/-n∣n∪)

∩-n·∪∣n∪ : ∀{n} → ∩-n · ∪ ⊗ ∣ ^⊗ n ⊗ ∪ ~* ∪-n
∩-n·∪∣n∪ = {!!}

∪n~∪-n : ∀{m}{d : D m 0} → ∪n · d ~* ∪-n · d
∪n~∪-n = - ∣⊗∣·∪n ■ ·~* (·~* (ι ⊗ε ■ - (ι ε⊗))) ■ ∣⊗∣·∪-n

∩n~∩-n : ∀{m}{d : D 0 m} → d · ∩n ~* d · ∩-n
∩n~∩-n = - ∩n·∣⊗∣ ■ ~·* (~·* (ι ε⊗ ■ - (ι ⊗ε))) ■ ∩-n·∣⊗∣

∩n~∩-n' : ∀{m}{d : D (m + 2) 0} → ∩n · d ~* ∩-n · d
∩n~∩-n' = ~·* (- ∩∣n∩·∪n) ■ -·· ■ ·~* ∪n~∪-n ■ ι ·· ■ ~·* ∩∣n∩·∪-n

∪n~∪-n' : ∀{m}{d : D 0 (m + 2)} → d · ∪n ~* d · ∪-n
∪n~∪-n' = ·~* (- ∩n·∪∣n∪) ■ ι ·· ■ ~·* ∩n~∩-n ■ -·· ■ ·~* ∩-n·∪∣n∪

