module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedLimit
public import StacksFrontier.Homology.DerivedComplete

/-!
# Derived global sections over the Koszul tower are derived complete

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `I = (f₁, …, f_r)` and let `ℬ` be the sheaf of
differential graded algebras on `ℕ` with the chaotic topology given by the inverse system
`n ↦ K_{n+1}` of Koszul algebras on `f₁ ^ (n + 1), …, f_r ^ (n + 1)`. For every object `M` of
`D(ℬ, d)` the derived global sections `RΓ(M)` are derived complete with respect to `I`.

## Main definitions

* `Stacks.ChaoticSite.sectionsComplex`: the complex of `R`-modules of sections over `U` of a
  complex of sheaves of modules over the constant sheaf of rings.
* `Stacks.ChaoticSite.rightMulCochain`: right multiplication by a section `ξ` of degree `-1`
  of `ℬ`, with the sign `(-1) ^ p` in degree `p`, as a cochain of degree `-1`.

## Main results

* `Stacks.ChaoticSite.homotopyRightMul`: if `dξ = c · 1`, right multiplication by `ξ` is a
  null-homotopy of multiplication by `c` on the complex of sections of a differential graded
  `ℬ`-module.
* `Koszul.isDerivedComplete_derivedGlobalSections`: **the derived global sections of an object
  of `D(ℬ, d)` are derived complete with respect to `(f₁, …, f_r)`.**

## Implementation notes

The argument is the one in the proof of Proposition 0GZK. Represent `M` by a graded injective
K-injective module `I`; then `RΓ(M)` is the derived limit of the tower of complexes of sections
`I(n)` (`Stacks.ChaoticSite.exists_isDerivedLimit_derivedGlobalSections`). Each `I(n)` is a
differential graded module over `K_{n+1}`, and the generator `ξᵢ` of `K_{n+1}` satisfies
`dξᵢ = fᵢ ^ (n + 1)`, so by the Leibniz rule `fᵢ ^ (n + 1)` is null-homotopic on `I(n)`. Hence
every element of `I` acts nilpotently on `I(n)` in `D(R)`, and Lemma 091W applies.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Lemma 15.91.10 (Tag 091W)](https://stacks.math.columbia.edu/tag/091W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Stacks.PresheafOfModules CochainComplex.HomComplex

universe u

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] (R : Type u) [CommRing R]

/-- The complex of `R`-modules of sections over `U` of a complex of sheaves of modules over the
constant sheaf of rings with value `R`. -/
abbrev sectionsComplex
    (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := C) R)) ℤ) (U : Cᵒᵖ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (((sectionsFunctor R).mapHomologicalComplex _).obj K).asFunctor.obj U

variable {R}
variable {ℬ : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R)}

/-- Right multiplication by a section `ξ` of degree `-1` of `ℬ` over `U`, with the sign
`(-1) ^ p` in degree `p`, as a cochain of degree `-1` on the complex of sections over `U` of a
differential graded `ℬ`-module. -/
def rightMulCochain (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ) (U : Cᵒᵖ)
    (ξ : (ℬ.complex.X (-1)).val.obj U) :
    Cochain (sectionsComplex R N.complex U) (sectionsComplex R N.complex U) (-1) :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom
    { toFun := fun x => (p.negOnePow : ℤ) •
        _root_.SheafOfModules.gradedCast (fun k => ((N.complex.X k).val.obj U : Type u)) hpq
          ((N.mul p (-1)).app U x ξ)
      map_add' := fun x y => by
        rw [map_add, AddMonoidHom.add_apply, _root_.SheafOfModules.gradedCast_add, smul_add]
      map_smul' := fun r x => by
        subst hpq
        exact (congrArg (fun y => (p.negOnePow : ℤ) • y)
          ((N.mul p (-1)).map_smul_left U r x ξ)).trans (smul_comm _ _ _) }

/-- The components of `rightMulCochain` are `x ↦ (-1) ^ p x ξ`. -/
theorem rightMulCochain_v_apply (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ)
    (U : Cᵒᵖ) (ξ : (ℬ.complex.X (-1)).val.obj U) (p q : ℤ) (hpq : p + -1 = q)
    (x : (N.complex.X p).val.obj U) :
    ((rightMulCochain N U ξ).v p q hpq).hom x = (p.negOnePow : ℤ) •
      _root_.SheafOfModules.gradedCast (fun k => ((N.complex.X k).val.obj U : Type u)) hpq
        ((N.mul p (-1)).app U x ξ) := rfl

/-- The differential of a complex of sheaves of modules commutes with transport along equalities
of degrees. -/
theorem d_gradedCast (K : CochainComplex (_root_.SheafOfModules.{u} (constRingSheaf (C := C) R)) ℤ)
    (U : Cᵒᵖ) {a a' b b' : ℤ} (ha : a = a') (hb : b = b') (y : (K.X a).val.obj U) :
    (K.d a' b').val.app U (_root_.SheafOfModules.gradedCast (fun k => ((K.X k).val.obj U : Type u))
        ha y) =
      _root_.SheafOfModules.gradedCast (fun k => ((K.X k).val.obj U : Type u)) hb
        ((K.d a b).val.app U y) := by
  subst ha hb
  rfl

/-- A transported term heterogeneously equal to `x` is `x`. -/
theorem gradedCast_eq_of_heq {T : ℤ → Type u} {i j : ℤ} (h : i = j) (y : T i) {x : T j}
    (hyx : HEq y x) : _root_.SheafOfModules.gradedCast T h y = x :=
  eq_of_heq ((_root_.SheafOfModules.gradedCast_heq T h y).trans hyx)

/-- **The Leibniz rule makes right multiplication by `ξ` a null-homotopy of `c`**: if
`dξ = c · 1`, then `d(h x) + h(dx) = c x` for `h x = (-1) ^ p x ξ` on sections of degree `p`. -/
theorem d_rightMul_add_rightMul_d (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ)
    (U : Cᵒᵖ) (ξ : (ℬ.complex.X (-1)).val.obj U) (c : R)
    (hξ : (ℬ.complex.d (-1) 0).val.app U ξ = c • ℬ.one.eval U) (p : ℤ)
    (x : (N.complex.X p).val.obj U) :
    (N.complex.d (p - 1) p).val.app U ((p.negOnePow : ℤ) •
        _root_.SheafOfModules.gradedCast (fun k => ((N.complex.X k).val.obj U : Type u))
          (show p + -1 = p - 1 by omega) ((N.mul p (-1)).app U x ξ)) +
      ((p + 1).negOnePow : ℤ) •
        _root_.SheafOfModules.gradedCast (fun k => ((N.complex.X k).val.obj U : Type u))
          (show p + 1 + -1 = p by omega)
          ((N.mul (p + 1) (-1)).app U ((N.complex.d p (p + 1)).val.app U x) ξ) = c • x := by
  have hξ' : (ℬ.complex.d (-1) (-1 + 1)).val.app U ξ = c • ℬ.one.eval U := hξ
  rw [map_zsmul, d_gradedCast N.complex U (show p + -1 = p - 1 by omega)
    (show p + -1 + 1 = p by omega), N.leibniz p (-1) U x ξ, hξ']
  have hm : (N.mul p (-1 + 1)).app U x (c • ℬ.one.eval U) =
      c • (N.mul p (-1 + 1)).app U x (ℬ.one.eval U) :=
    (N.mul p (-1 + 1)).map_smul_right U c x _
  have h1 : HEq ((N.mul p (-1 + 1)).app U x (ℬ.one.eval U)) x := N.mul_one p U x
  rw [hm]
  simp only [_root_.SheafOfModules.gradedCast_add, _root_.SheafOfModules.gradedCast_smul,
    _root_.SheafOfModules.gradedCast_trans]
  rw [gradedCast_eq_of_heq (T := fun k ↦ ((N.complex.X k).val.obj U : Type u))
    (show p + (-1 + 1) = p by omega) _ h1]
  generalize _root_.SheafOfModules.gradedCast (fun k ↦ ((N.complex.X k).val.obj U : Type u)) _
    ((N.mul (p + 1) (-1)).app U ((N.complex.d p (p + 1)).val.app U x) ξ) = A
  rw [smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
    Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

/-- **Right multiplication by `ξ` is a null-homotopy of `c`** on the complex of sections over `U`
of a differential graded `ℬ`-module, whenever `ξ` is a section of degree `-1` of `ℬ` with
`dξ = c · 1`. -/
def homotopyRightMul (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} ℬ)
    (U : Cᵒᵖ) (ξ : (ℬ.complex.X (-1)).val.obj U) (c : R)
    (hξ : (ℬ.complex.d (-1) 0).val.app U ξ = c • ℬ.one.eval U) :
    Homotopy (c • 𝟙 (sectionsComplex R N.complex U)) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨rightMulCochain N U ξ, by
    ext p x
    rw [Cochain.add_v, Cochain.ofHom_v, Cochain.ofHom_v,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) (by omega) rfl]
    simp only [Int.negOnePow_zero, one_smul, HomologicalComplex.zero_f, add_zero]
    exact (d_rightMul_add_rightMul_d N U ξ c hξ p x).symm⟩

end Stacks.ChaoticSite

section Nilpotent

variable {A : Type*} [CommRing A] {D : Type*} [Category D] [Preadditive D] [Linear A D]

/-- The scalars acting nilpotently on an object of an `A`-linear category form an ideal: if every
element of `s` acts nilpotently on `X`, so does every element of the ideal generated by `s`. -/
theorem isNilpotent_smul_one_of_mem_span (X : D) {s : Set A}
    (hs : ∀ a ∈ s, IsNilpotent (a • (1 : End X))) {a : A} (ha : a ∈ Ideal.span s) :
    IsNilpotent (a • (1 : End X)) := by
  induction ha using Submodule.span_induction with
  | mem a ha => exact hs a ha
  | zero => rw [zero_smul]; exact IsNilpotent.zero
  | add a b _ _ hna hnb =>
      rw [add_smul]
      exact Commute.isNilpotent_add (((Commute.refl (1 : End X)).smul_left a).smul_right b)
        hna hnb
  | smul b a _ hna =>
      rw [smul_eq_mul, mul_smul]
      exact hna.smul b

end Nilpotent

namespace Koszul

open Stacks Stacks.ChaoticSite

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The generator `ξᵢ` of the Koszul algebra `K_{n+1}`, as a section of degree `-1` of the sheaf
`ℬ = (K_{m+1})_m` over the stage `n`. -/
def liftedPowGenerator (f : Fin r → R) (n : ℕ) (i : Fin r) :
    ((liftedPowSheafAlgebra f).complex.X (-1)).val.obj (op (LiftedNat.up.{u} n)) :=
  (⟨ExteriorAlgebra.ι R (Pi.single i 1), ι_mem_powAlgebra_grading f (n + 1) _⟩ :
    (powAlgebra f (n + 1)).grading (-1))

/-- The differential of `ℬ` sends the generator `ξᵢ` over the stage `n` to `fᵢ ^ (n + 1)`. -/
theorem d_liftedPowGenerator (f : Fin r → R) (n : ℕ) (i : Fin r) :
    ((liftedPowSheafAlgebra f).complex.d (-1) 0).val.app (op (LiftedNat.up.{u} n))
        (liftedPowGenerator f n i) =
      f i ^ (n + 1) • (liftedPowSheafAlgebra f).one.eval (op (LiftedNat.up.{u} n)) := by
  apply Subtype.ext
  have hd := systemComplex_d_val_app (LiftedNat.liftDiagram.{u} (powAlgebraDiagram f)) (-1)
    (op (LiftedNat.up.{u} n))
  rw [show (liftedPowSheafAlgebra f).complex.d (-1) 0 =
    (systemComplex (LiftedNat.liftDiagram.{u} (powAlgebraDiagram f))).d (-1) (-1 + 1) from rfl, hd]
  exact (powAlgebra_d_ι f (n + 1) i).trans
    (Algebra.algebraMap_eq_smul_one (A := ExteriorAlgebra R (Fin r → R)) _)

attribute [local instance] HasDerivedCategory.standard

/-- Over the stage `n`, multiplication by `fᵢ ^ (n + 1)` is zero on the complex of sections of a
differential graded `ℬ`-module in `D(R)`: it is null-homotopic, by right multiplication with
`ξᵢ`. -/
theorem smul_id_sectionsTower_eq_zero (f : Fin r → R)
    (N : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra f)) (n : ℕ)
    (i : Fin r) :
    f i ^ (n + 1) • 𝟙 ((sectionsTower R N.complex ⋙ DerivedCategory.Q).obj (op n)) = 0 := by
  have h := DerivedCategory.Q_map_eq_of_homotopy (h :=
    homotopyRightMul N _ (liftedPowGenerator f n i) _ (d_liftedPowGenerator f n i))
  rw [Functor.map_zero, Functor.Linear.map_smul, CategoryTheory.Functor.map_id] at h
  exact h

/-- Every element of `(f₁, …, f_r)` acts nilpotently, in `D(R)`, on the complex of sections over
any stage of a differential graded `ℬ`-module. -/
theorem isNilpotent_smul_one_sectionsTower (f : Fin r → R)
    (N : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra f)) (n : ℕ)
    {a : R} (ha : a ∈ Ideal.span (Set.range f)) :
    IsNilpotent (a • (1 : End ((sectionsTower R N.complex ⋙ DerivedCategory.Q).obj (op n)))) := by
  refine isNilpotent_smul_one_of_mem_span _ ?_ ha
  rintro _ ⟨i, rfl⟩
  exact ⟨n + 1, by rw [smul_id_pow]; exact smul_id_sectionsTower_eq_zero f N n i⟩

/-- **Stacks 0GZK, derived completeness of the derived global sections.** Let `ℬ` be the sheaf of
differential graded algebras on `ℕ` given by the Koszul algebras `K_{n+1}` on
`f₁ ^ (n + 1), …, f_r ^ (n + 1)`. For every object `M` of `D(ℬ, d)` the derived global sections
`RΓ(M)` are derived complete with respect to `(f₁, …, f_r)`. -/
theorem isDerivedComplete_derivedGlobalSections (f : Fin r → R)
    (M : SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (liftedPowSheafAlgebra f)) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedComplete (Ideal.span (Set.range f))
      ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨I, -, -, p, δ, hT⟩ := exists_isDerivedLimit_derivedGlobalSections R
    (liftedPowSheafAlgebra f) M
  intro a ha
  have hprod := isDerivedCompleteAt_pi fun n =>
    isDerivedCompleteAt_of_isNilpotent (isNilpotent_smul_one_sectionsTower f I n ha)
  exact isDerivedCompleteAt_of_distTriang hT hprod hprod

end Koszul
