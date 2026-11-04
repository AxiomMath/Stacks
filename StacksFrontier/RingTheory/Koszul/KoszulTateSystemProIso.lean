module

public import StacksFrontier.RingTheory.Koszul.KoszulTateSystem
public import StacksFrontier.RingTheory.Koszul.LiftedSheafAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSystemHom

/-!
# The pro-isomorphisms of the proof of Proposition 0GZK

The proof of Proposition 0GZK, which Remark 0H1E carries over to a weakly proregular sequence,
connects the Koszul system `ℬ = (K_n)` and the quotient system `𝒜' = (R / (f₁ ^ n, …, f_r ^ n))` by
a zigzag: `(K_n)` is pro-isomorphic to its subsystem `(K_{nᵢ})` over the exponents
`1 = n₀ < n₁ < ⋯` of the Koszul–Tate ladder, which is pro-isomorphic to the Tate system `(Eᵢ)`
(Remark 0GZ5), which maps by stagewise quasi-isomorphisms to `(R / (f₁ ^ {nᵢ}, …))`, which is
pro-isomorphic to `(R / (f₁ ^ n, …))`. This file records the three pro-isomorphisms, over `ℕ` and
over the site `Stacks.LiftedNat`, and the Tate system as a sheaf of differential graded algebras.

## Main definitions

* `Koszul.powAlgebraSeqProIso`, `Koszul.powQuotientSeqProIso`: a Koszul system, resp. a quotient
  system, is pro-isomorphic to its subsystem along a cofinal monotone sequence of exponents.
* `DividedPowers.TateResolution.koszulTateProIso`: **the Koszul system over the exponents of
  the ladder is pro-isomorphic to the Tate system** (Remark 0GZ5, read on differential graded
  algebras).
* `DividedPowers.TateResolution.liftedKoszulTateSheafAlgebra`: the Tate system as a sheaf of
  differential graded algebras on the chaotic site `Stacks.LiftedNat.{u}`.

## References

* [Stacks Project, Tag 0GZ5](https://stacks.math.columbia.edu/tag/0GZ5)
* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite DifferentialGradedAlgebra

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **A Koszul system is pro-isomorphic to its subsystem along cofinal exponents.** For a
monotone `e` with `e i ≥ i + 1`, the representatives are the transition homomorphisms
`K_{e i + 1} → K_{e i}` and `K_{e i} → K_{i + 1}`. -/
def powAlgebraSeqProIso (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) (h1 : ∀ i, 1 ≤ e i)
    (hcof : ∀ i, i + 1 ≤ e i) :
    SystemProIso (powAlgebraDiagram f) (powAlgebraSeq f e he h1) where
  F₁ := he.functor
  F₂ := 𝟭 ℕ
  hom :=
    { app := fun i => powTransition f (h1 i.unop) (Nat.le_succ _)
      naturality := fun _ j g => hom_eq_of_toAlgebraHom_eq
        ((powTransition_comp f (h1 j.unop) (Nat.le_succ _)
          (Nat.succ_le_succ (he (leOfHom g.unop)))).trans
          (powTransition_comp f (h1 j.unop) (he (leOfHom g.unop)) (Nat.le_succ _)).symm) }
  inv :=
    { app := fun i => powTransition f (Nat.succ_pos _) (hcof i.unop)
      naturality := fun i j g => hom_eq_of_toAlgebraHom_eq
        ((powTransition_comp f (Nat.succ_pos j.unop) (hcof j.unop)
          (he (leOfHom g.unop))).trans
          (powTransition_comp f (Nat.succ_pos j.unop) (Nat.succ_le_succ (leOfHom g.unop))
            (hcof i.unop)).symm) }
  le₁ := fun i => (Nat.le_succ i).trans (hcof i)
  le₂ := fun i => (Nat.le_succ i).trans (hcof i)
  hom_inv := fun i => hom_eq_of_toAlgebraHom_eq
    (powTransition_comp f (Nat.succ_pos i) (hcof i) (Nat.le_succ _))
  inv_hom := fun i => hom_eq_of_toAlgebraHom_eq
    (powTransition_comp f (h1 i) (Nat.le_succ _) (hcof (e i)))

/-- **A quotient system is pro-isomorphic to its subsystem along cofinal exponents.** All maps are
the canonical surjections. -/
def powQuotientSeqProIso (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e)
    (hcof : ∀ i, i + 1 ≤ e i) :
    SystemProIso (powQuotientAlgebraDiagram f) (powQuotientSeq f e he) where
  F₁ := he.functor
  F₂ := 𝟭 ℕ
  hom :=
    { app := fun _ => degreeZeroHom (Ideal.Quotient.factorₐ R (powIdeal_le f (Nat.le_succ _)))
      naturality := fun _ _ _ => degreeZero_quotient_hom_ext _ _ }
  inv :=
    { app := fun i => degreeZeroHom (Ideal.Quotient.factorₐ R (powIdeal_le f (hcof i.unop)))
      naturality := fun _ _ _ => degreeZero_quotient_hom_ext _ _ }
  le₁ := fun i => (Nat.le_succ i).trans (hcof i)
  le₂ := fun i => (Nat.le_succ i).trans (hcof i)
  hom_inv := fun _ => degreeZero_quotient_hom_ext _ _
  inv_hom := fun _ => degreeZero_quotient_hom_ext _ _

end Koszul

namespace DividedPowers.TateResolution

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (proregular : Koszul.IsWeaklyProregular f)

/-- **The Koszul system over the exponents of the Koszul–Tate ladder is pro-isomorphic to the
Tate system.** The representatives are `K_{nᵢ₊₁} → Eᵢ` and `Eᵢ₊₁ → K_{nᵢ₊₁}`, and the two
composites are the transition maps: Remark 0GZ5 read on differential graded algebras. -/
def koszulTateProIso :
    SystemProIso (koszulTateKoszulSystem f proregular) (koszulTateDGASystem f proregular) where
  F₁ := 𝟭 ℕ
  F₂ := Monotone.functor (f := fun i : ℕ => i + 1) fun _ _ h => Nat.succ_le_succ h
  hom := koszulTateUp f proregular
  inv := koszulTateDown f proregular
  le₁ := fun i => i.le_add_right 1
  le₂ := fun i => i.le_add_right 1
  hom_inv := koszulTateUp_app_koszulTateDown_app f proregular
  inv_hom := koszulTateDown_app_koszulTateUp_app f proregular

/-- The exponents `nᵢ₊₁` of the Koszul–Tate ladder dominate `i + 1`. -/
theorem succ_le_koszulTateFactorizationPower_succ (i : ℕ) :
    i + 1 ≤ koszulTateFactorizationPower f proregular (i + 1) :=
  le_koszulTateFactorizationPower f proregular (i + 1)

/-- The full Koszul system `(K_{n+1})` is pro-isomorphic to the Koszul system over the exponents
of the Koszul–Tate ladder. -/
def koszulTateKoszulSeqProIso :
    SystemProIso (Koszul.powAlgebraDiagram f) (koszulTateKoszulSystem f proregular) :=
  Koszul.powAlgebraSeqProIso f _ _ _ (succ_le_koszulTateFactorizationPower_succ f proregular)

/-- The full quotient system `(R / (f₁ ^ (n+1), …))` is pro-isomorphic to the quotient system over
the exponents of the Koszul–Tate ladder. -/
def koszulTateQuotientSeqProIso :
    SystemProIso (Koszul.powQuotientAlgebraDiagram f) (koszulTateQuotientSystem f proregular) :=
  Koszul.powQuotientSeqProIso f _ _ (succ_le_koszulTateFactorizationPower_succ f proregular)

/-- **The sheaf `ℰ` of the proof of Proposition 0GZK**: the Tate system of a weakly proregular
sequence, on the chaotic site `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateSheafAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := Stacks.LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (Stacks.LiftedNat.liftDiagram (koszulTateDGASystem f proregular))

end DividedPowers.TateResolution

namespace DividedPowers.TateResolution

open Stacks

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (proregular : Koszul.IsWeaklyProregular f)

/-- The sheaf `ℬₑ` of the Koszul algebras over the exponents of the Koszul–Tate ladder, on the
chaotic site `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateKoszulSheafAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (LiftedNat.liftDiagram (koszulTateKoszulSystem f proregular))

/-- The sheaf `𝒜'ₑ` of the quotients over the exponents of the Koszul–Tate ladder, on the chaotic
site `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateQuotientSheafAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (LiftedNat.liftDiagram (koszulTateQuotientSystem f proregular))

/-- `koszulTateProIso`, over `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateProIso :
    SystemProIso (LiftedNat.liftDiagram.{u} (koszulTateKoszulSystem f proregular))
      (LiftedNat.liftDiagram.{u} (koszulTateDGASystem f proregular)) :=
  (koszulTateProIso f proregular).lift

/-- `koszulTateKoszulSeqProIso`, over `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateKoszulSeqProIso :
    SystemProIso (LiftedNat.liftDiagram.{u} (Koszul.powAlgebraDiagram f))
      (LiftedNat.liftDiagram.{u} (koszulTateKoszulSystem f proregular)) :=
  (koszulTateKoszulSeqProIso f proregular).lift

/-- `koszulTateQuotientSeqProIso`, over `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateQuotientSeqProIso :
    SystemProIso (LiftedNat.liftDiagram.{u} (Koszul.powQuotientAlgebraDiagram f))
      (LiftedNat.liftDiagram.{u} (koszulTateQuotientSystem f proregular)) :=
  (koszulTateQuotientSeqProIso f proregular).lift

/-- The augmentation of the Tate system, over `Stacks.LiftedNat.{u}`: a morphism of inverse
systems which is a quasi-isomorphism at every stage. -/
def liftedKoszulTateAug :
    LiftedNat.liftDiagram.{u} (koszulTateDGASystem f proregular) ⟶
      LiftedNat.liftDiagram.{u} (koszulTateQuotientSystem f proregular) :=
  Functor.whiskerLeft LiftedNat.toNat.op (koszulTateAug f proregular)

/-- Every component of the lifted augmentation of the Tate system is a quasi-isomorphism. -/
theorem quasiIso_liftedKoszulTateAug_app (i : LiftedNat.{u}ᵒᵖ) :
    QuasiIso ((liftedKoszulTateAug f proregular).app i).toCochainMap :=
  quasiIso_koszulTateAug_app f proregular (op i.unop.down)

/-- **The augmentation `ℰ → 𝒜'ₑ` of the Tate sheaf**, a homomorphism of sheaves of differential
graded algebras on the chaotic site `Stacks.LiftedNat.{u}`. -/
def liftedKoszulTateAugHom :
    liftedKoszulTateSheafAlgebra f proregular ⟶ liftedKoszulTateQuotientSheafAlgebra f proregular :=
  Stacks.ChaoticSite.systemAlgebraHom (liftedKoszulTateAug f proregular)

/-- The augmentation of the Tate sheaf preserves the unit. -/
theorem liftedKoszulTateAugHom_preservesOne : (liftedKoszulTateAugHom f proregular).PreservesOne :=
  Stacks.ChaoticSite.systemAlgebraHom_preservesOne _

/-- **The augmentation of the Tate sheaf is a quasi-isomorphism**: the hypothesis of Tags 0FTZ
and 0GZF for step (2) of the proof of Proposition 0GZK. -/
theorem isQuasiIso_liftedKoszulTateAugHom
    [HasSheafify (⊥ : GrothendieckTopology LiftedNat.{u}) AddCommGrpCat.{u}] :
    (liftedKoszulTateAugHom f proregular).IsQuasiIso :=
  Stacks.ChaoticSite.isQuasiIso_systemAlgebraHom _ (quasiIso_liftedKoszulTateAug_app f proregular)

end DividedPowers.TateResolution
