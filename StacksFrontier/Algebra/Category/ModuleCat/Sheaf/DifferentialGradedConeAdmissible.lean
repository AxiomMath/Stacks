module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc

/-!
# The cone of a morphism of differential graded modules is an admissible short exact sequence

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules. The cone of `f` sits in
`0 ⟶ L ⟶ C(f) ⟶ K[1] ⟶ 0`,
the two maps being the canonical inclusion and the canonical projection of the cone. Degreewise
the cone is the direct sum `K^{n+1} ⊕ L^n` and its right action is the direct-sum action, so after
forgetting the differentials the pair splits. That is exactly what makes it an *admissible* short
exact sequence in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAdmissible.lean`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ShiftPackage.xIso` identifies the degree-`n` piece of a
  chosen shift of `K` with `K^{n+1}`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.gradedSplitting` is the graded splitting of
  the cone: the retraction of the inclusion is the second projection of the degreewise splitting
  and the section of the projection is the first inclusion.

## Main results

* `SheafOfModules.DifferentialGradedModule.ConePackage.inclusion_f` and
  `SheafOfModules.DifferentialGradedModule.ConePackage.projection_f`: the two canonical maps of a
  cone package, read through the degreewise splitting, are `biprod.inr` and `biprod.fst`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.isAdmissibleShortExact`: the inclusion and
  the projection of any cone package are an admissible short exact sequence.
* `SheafOfModules.DifferentialGradedModule.isAdmissibleShortExact_conePackage`: the same for the
  chosen cone package `SheafOfModules.DifferentialGradedModule.conePackage`.

## Implementation notes

A `SheafOfModules.DifferentialGradedModule.ConePackage` pins its cone down only through the data
it records: the underlying complex is Mathlib's mapping cone, the degreewise splitting is
Mathlib's `HomologicalComplex.homotopyCofiber.XIsoBiprod`, and the two canonical maps are
Mathlib's — the last three recorded as `HEq`s. So `inclusion_f` and `projection_f` destructure the
package, substitute the equality of complexes and then turn those `HEq`s into equalities, exactly
as `SheafOfModules.DifferentialGradedModule.conePackage_coneDesc_f` does in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeComparison.lean`. For the
projection one more step is needed: its target is the *chosen* shift `shift K` rather than the
shifted complex, so its `HEq` is converted with `CategoryTheory.comp_eqToHom_heq`, which is how
the package was built in the first place. For the same reason the projection is characterized
after composing with `ShiftPackage.xIso`, which keeps every intermediate composite spelled in one
way: the two spellings `(shift K).complex.X n` and `K.complex.X (n + 1)` are definitionally but
not syntactically equal, and a composite mixing them is not type-correct at the transparency `rw`
uses to build a motive.

The splitting is not obtained from
`SheafOfModules.DifferentialGradedModule.GradedSplitting.ofBiprod` by transport: the cone is a
direct sum degreewise but *not* a biproduct of differential graded modules — its differential is
the twisted one — so there is no isomorphism `C(f) ≅ K[1] ⊞ L` of differential graded modules to
transport along. What the biproduct contributes is the three identities `biprod.inr_snd`,
`biprod.inl_fst` and `biprod.total`, which is what the proofs below use.

That the section commutes with the right action is the one place where both action equations of
the cone are needed: in the first coordinate the action on the image of `K[1]` is the action of
`K[1]` (`ConePackage.action_first` together with `ShiftPackage.shifted_action`), and in the second
it vanishes, by `ConePackage.action_second` and additivity of the action. The two coordinates then
determine the section, by `SheafOfModules.biprodSections_ext`.

The degrees `(n + i) + 1` and `(n + 1) + i` are propositionally but not definitionally equal, so
the first-coordinate comparison runs through `SheafOfModules.castHom`, as the module laws
themselves do.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, m} A}

/-! ### Evaluation of morphisms of sheaves of modules on sections -/

theorem congr_val_app {X Y : SheafOfModules.{m} R} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Cᵒᵖ)
    (z : X.val.obj U) : φ.val.app U z = ψ.val.app U z := by rw [h]

/-! ### Transports along equalities of degrees -/

theorem eq_castHom_of_heq {X : ℤ → SheafOfModules.{m} R} {d d' : ℤ} (h : d' = d)
    (U : Cᵒᵖ) {z : (X d).val.obj U} {w : (X d').val.obj U} (hzw : HEq z w) :
    z = castHom X h U w :=
  eq_of_heq (hzw.trans (heq_castHom X h U w).symm)

/-! ### The degreewise identification of a chosen shift -/

namespace ShiftPackage

/-- The degree-`n` piece of a chosen shift of `K`, identified with `K^{n+1}`. -/
noncomputable def xIso (S : ShiftPackage K) (n : ℤ) :
    S.shifted.complex.X n ≅ K.complex.X (n + 1) where
  hom := (eqToHom S.shifted_complex).f n
  inv := (eqToHom S.shifted_complex.symm).f n
  hom_inv_id :=
    calc (eqToHom S.shifted_complex).f n ≫ (eqToHom S.shifted_complex.symm).f n
        = (eqToHom S.shifted_complex ≫ eqToHom S.shifted_complex.symm).f n := rfl
      _ = 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl, HomologicalComplex.id_f]
  inv_hom_id :=
    calc (eqToHom S.shifted_complex.symm).f n ≫ (eqToHom S.shifted_complex).f n
        = (eqToHom S.shifted_complex.symm ≫ eqToHom S.shifted_complex).f n := rfl
      _ = 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl, HomologicalComplex.id_f]

private theorem shifted_mul_eq (S : ShiftPackage K) (n i : ℤ) (U : Cᵒᵖ) :
    ∀ (x : (S.shifted.complex.X n).val.obj U) (a : (A.complex.X i).val.obj U),
      ((eqToHom S.shifted_complex).f (n + i)).val.app U ((S.shifted.mul n i).app U x a) =
        castHom K.complex.X (add_right_comm n 1 i) U
          ((K.mul (n + 1) i).app U (((eqToHom S.shifted_complex).f n).val.app U x) a) := by
  obtain ⟨⟨c, μ, hassoc, hone, hleib⟩, hc, ha⟩ := S
  dsimp only at hc ha ⊢
  subst hc
  intro x a
  simp only [eqToHom_refl, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  refine eq_castHom_of_heq (X := K.complex.X) (add_right_comm n 1 i) U ?_
  exact heq_dependent_apply
    (fun (d : ℤ) (φ : (K.complex.X (n + 1)).val.obj U →+
      (A.complex.X i).val.obj U →+ (K.complex.X d).val.obj U) => φ x a)
    (show n + i + 1 = n + 1 + i by omega) (ha n i U)

/-- **The right action of a chosen shift of `K` is the action of `K` with its degree raised by
one**, read through the identification of the pieces. -/
theorem xIso_mul (S : ShiftPackage K) (n i : ℤ) (U : Cᵒᵖ)
    (x : (S.shifted.complex.X n).val.obj U) (a : (A.complex.X i).val.obj U) :
    ((S.xIso (n + i)).hom).val.app U ((S.shifted.mul n i).app U x a) =
      castHom K.complex.X (add_right_comm n 1 i) U
        ((K.mul (n + 1) i).app U (((S.xIso n).hom).val.app U x) a) :=
  S.shifted_mul_eq n i U x a

end ShiftPackage

namespace ConePackage

variable {f : K ⟶ L}

/-! ### The two canonical maps of a cone package, read through the degreewise splitting -/

private theorem rawProjection_f (φ : K.complex ⟶ L.complex) (n : ℤ) :
    (CochainComplex.HomComplex.Cocycle.homOf
        ((CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1))).f n =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) (by simp)).hom ≫
        biprod.fst := by
  rw [CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe,
    CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ (n + 1) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX]
  show (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).hom ≫ biprod.fst = _
  rfl

/-- **The inclusion of a cone package is `biprod.inr` read through the degreewise splitting.** -/
theorem inclusion_f (P : ConePackage f) (n : ℤ) :
    P.inclusion.toHomologicalComplex.f n = biprod.inr ≫ (P.componentIso n).inv := by
  obtain ⟨⟨cplx, mul, hassoc, hone, hleib⟩, incl, proj, hc, iso, hiso, af, as, hi, hp⟩ := P
  dsimp only at hc hiso hi ⊢
  subst hc
  rw [show incl.toHomologicalComplex =
      CochainComplex.mappingCone.inr f.toHomologicalComplex from eq_of_heq hi,
    show iso n = HomologicalComplex.homotopyCofiber.XIsoBiprod
      f.toHomologicalComplex n (n + 1) (by simp) from eq_of_heq (hiso n)]
  exact (HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv f.toHomologicalComplex
    (n + 1) n (by simp)).symm

/-- **The projection of a cone package is `biprod.fst` read through the degreewise splitting**,
once the chosen shift is identified with the shifted complex by `ShiftPackage.xIso`. -/
theorem projection_f (P : ConePackage f) (n : ℤ) :
    P.projection.toHomologicalComplex.f n ≫ ((shiftPackage K).xIso n).hom =
      (P.componentIso n).hom ≫ biprod.fst := by
  have hsh := (shiftPackage K).shifted_complex
  obtain ⟨⟨cplx, mul, hassoc, hone, hleib⟩, incl, proj, hc, iso, hiso, af, as, hi, hp⟩ := P
  dsimp only at hc hiso hp ⊢
  subst hc
  have key : proj.toHomologicalComplex ≫ eqToHom hsh =
      CochainComplex.HomComplex.Cocycle.homOf
        ((CochainComplex.mappingCone.fst f.toHomologicalComplex).rightShift 1 0 (zero_add 1)) :=
    eq_of_heq ((comp_eqToHom_heq _ hsh).trans hp)
  rw [show iso n = HomologicalComplex.homotopyCofiber.XIsoBiprod
      f.toHomologicalComplex n (n + 1) (by simp) from eq_of_heq (hiso n),
    show proj.toHomologicalComplex.f n ≫ ((shiftPackage K).xIso n).hom =
      (CochainComplex.HomComplex.Cocycle.homOf
        ((CochainComplex.mappingCone.fst f.toHomologicalComplex).rightShift 1 0
          (zero_add 1))).f n from congrArg (fun φ => HomologicalComplex.Hom.f φ n) key]
  exact rawProjection_f f.toHomologicalComplex n

/-! ### The two coordinate maps of the splitting -/

/-- The retraction of the cone's inclusion: the second projection of the degreewise splitting. -/
noncomputable def coneRetractionX (P : ConePackage f) (n : ℤ) :
    P.cone.complex.X n ⟶ L.complex.X n :=
  (P.componentIso n).hom ≫ biprod.snd

/-- The section of the cone's projection: the first inclusion of the degreewise splitting. -/
noncomputable def coneSectionX (P : ConePackage f) (n : ℤ) :
    (shift K).complex.X n ⟶ P.cone.complex.X n :=
  ((shiftPackage K).xIso n).hom ≫ biprod.inl ≫ (P.componentIso n).inv

/-- The first coordinate of the section `coneSectionX` is the identification
`(shiftPackage K).xIso n` of the chosen shift with the shifted complex. -/
theorem coneSectionX_fst (P : ConePackage f) (n : ℤ) :
    P.coneSectionX n ≫ (P.componentIso n).hom ≫ biprod.fst =
      ((shiftPackage K).xIso n).hom := by
  simp only [coneSectionX, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst, Category.comp_id]

/-- The second coordinate of the section `coneSectionX` vanishes. -/
theorem coneSectionX_snd (P : ConePackage f) (n : ℤ) :
    P.coneSectionX n ≫ (P.componentIso n).hom ≫ biprod.snd = 0 := by
  simp only [coneSectionX, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_snd, comp_zero]

/-- Sections of a piece of the cone are determined by their two coordinates. -/
theorem sections_ext (P : ConePackage f) (n : ℤ) (U : Cᵒᵖ)
    {x y : (P.cone.complex.X n).val.obj U}
    (h₁ : ((P.componentIso n).hom ≫ biprod.fst).val.app U x =
      ((P.componentIso n).hom ≫ biprod.fst).val.app U y)
    (h₂ : ((P.componentIso n).hom ≫ biprod.snd).val.app U x =
      ((P.componentIso n).hom ≫ biprod.snd).val.app U y) : x = y := by
  have h : ((P.componentIso n).hom).val.app U x = ((P.componentIso n).hom).val.app U y :=
    biprodSections_ext _ _ U h₁ h₂
  calc x = ((P.componentIso n).hom ≫ (P.componentIso n).inv).val.app U x := by
          rw [Iso.hom_inv_id]; rfl
    _ = ((P.componentIso n).inv).val.app U (((P.componentIso n).hom).val.app U x) := rfl
    _ = ((P.componentIso n).inv).val.app U (((P.componentIso n).hom).val.app U y) := by rw [h]
    _ = ((P.componentIso n).hom ≫ (P.componentIso n).inv).val.app U y := rfl
    _ = y := by rw [Iso.hom_inv_id]; rfl

/-- In the first coordinate the section of the cone's projection commutes with the right action:
there the cone acts as the shift of `K` does. -/
theorem coneSectionX_action_fst (P : ConePackage f) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((shift K).complex.X n).val.obj U) (a : (A.complex.X i).val.obj U) :
    ((P.componentIso (n + i)).hom ≫ biprod.fst).val.app U
        ((P.coneSectionX (n + i)).val.app U (((shift K).mul n i).app U x a)) =
      ((P.componentIso (n + i)).hom ≫ biprod.fst).val.app U
        ((P.cone.mul n i).app U ((P.coneSectionX n).val.app U x) a) := by
  have h1 : ∀ (k : ℤ) (z : ((shift K).complex.X k).val.obj U),
      ((P.componentIso k).hom ≫ biprod.fst).val.app U ((P.coneSectionX k).val.app U z) =
        (((shiftPackage K).xIso k).hom).val.app U z := fun k z =>
    (comp_val_app (P.coneSectionX k) ((P.componentIso k).hom ≫ biprod.fst) U z).symm.trans
      (congr_val_app (P.coneSectionX_fst k) U z)
  rw [h1, (shiftPackage K).xIso_mul n i U x a, ← h1 n x]
  exact (eq_castHom_of_heq (X := K.complex.X) (add_right_comm n 1 i) U
    (P.action_first n i U ((P.coneSectionX n).val.app U x) a)).symm

/-- In the second coordinate the section of the cone's projection commutes with the right action:
both sides vanish, the section landing in the first summand. -/
theorem coneSectionX_action_snd (P : ConePackage f) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((shift K).complex.X n).val.obj U) (a : (A.complex.X i).val.obj U) :
    ((P.componentIso (n + i)).hom ≫ biprod.snd).val.app U
        ((P.coneSectionX (n + i)).val.app U (((shift K).mul n i).app U x a)) =
      ((P.componentIso (n + i)).hom ≫ biprod.snd).val.app U
        ((P.cone.mul n i).app U ((P.coneSectionX n).val.app U x) a) := by
  have h2 : ∀ (k : ℤ) (z : ((shift K).complex.X k).val.obj U),
      ((P.componentIso k).hom ≫ biprod.snd).val.app U ((P.coneSectionX k).val.app U z) = 0 :=
    fun k z =>
      (comp_val_app (P.coneSectionX k) ((P.componentIso k).hom ≫ biprod.snd) U z).symm.trans
        (congr_val_app (P.coneSectionX_snd k) U z)
  rw [h2, P.action_second n i U ((P.coneSectionX n).val.app U x) a, h2 n x,
    map_zero ((L.mul n i).app U), AddMonoidHom.zero_apply]

/-! ### The graded splitting -/

/-- **The graded splitting of the cone.** The inclusion `L ⟶ C(f)` and the projection
`C(f) ⟶ K[1]` of a cone package split after forgetting the differentials: degreewise the cone is
the direct sum `K^{n+1} ⊕ L^n` with the direct-sum action, so the second projection retracts the
inclusion, the first inclusion sections the projection, and the two decompose the identity. -/
noncomputable def gradedSplitting (P : ConePackage f) :
    GradedSplitting P.inclusion P.projection where
  r :=
    { app := fun n => P.coneRetractionX n
      map_smul := fun n i U x a => P.action_second n i U x a }
  s :=
    { app := fun n => P.coneSectionX n
      map_smul := fun n i U x a =>
        P.sections_ext (n + i) U (P.coneSectionX_action_fst n i U x a)
          (P.coneSectionX_action_snd n i U x a) }
  f_r := GradedModule.Hom.ext fun n => by
    have h : P.inclusion.toHomologicalComplex.f n ≫
        ((P.componentIso n).hom ≫ biprod.snd) = 𝟙 _ := by
      rw [P.inclusion_f n]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd]
    exact h
  s_g := GradedModule.Hom.ext fun n => by
    have h : (((shiftPackage K).xIso n).hom ≫ biprod.inl ≫ (P.componentIso n).inv) ≫
        P.projection.toHomologicalComplex.f n = 𝟙 _ := by
      rw [← Iso.cancel_iso_hom_right _ _ ((shiftPackage K).xIso n), Category.assoc,
        P.projection_f n]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst, Category.comp_id,
        Category.id_comp]
    exact h
  id := GradedModule.Hom.ext fun n => by
    have h₁ : ((P.componentIso n).hom ≫ biprod.snd) ≫
        P.inclusion.toHomologicalComplex.f n =
        (P.componentIso n).hom ≫ (biprod.snd ≫ biprod.inr) ≫ (P.componentIso n).inv := by
      rw [P.inclusion_f n]
      simp only [Category.assoc]
    have h₂ : P.projection.toHomologicalComplex.f n ≫
        (((shiftPackage K).xIso n).hom ≫ biprod.inl ≫ (P.componentIso n).inv) =
        (P.componentIso n).hom ≫ (biprod.fst ≫ biprod.inl) ≫ (P.componentIso n).inv := by
      rw [← Category.assoc, P.projection_f n]
      simp only [Category.assoc]
    have h : ((P.componentIso n).hom ≫ biprod.snd) ≫ P.inclusion.toHomologicalComplex.f n +
        P.projection.toHomologicalComplex.f n ≫
          (((shiftPackage K).xIso n).hom ≫ biprod.inl ≫ (P.componentIso n).inv) = 𝟙 _ := by
      rw [h₁, h₂, ← Preadditive.comp_add, ← Preadditive.add_comp,
        add_comm (biprod.snd ≫ biprod.inr), biprod.total, Category.id_comp, Iso.hom_inv_id]
    exact h

/-- **The inclusion and the projection of a cone package are an admissible short exact
sequence.** -/
theorem isAdmissibleShortExact (P : ConePackage f) :
    IsAdmissibleShortExact P.inclusion P.projection :=
  ⟨P.gradedSplitting⟩

end ConePackage

/-- **The inclusion and the projection of the cone are an admissible short exact sequence**:
`0 ⟶ L ⟶ C(f) ⟶ K[1] ⟶ 0` is split after forgetting the differentials. -/
theorem isAdmissibleShortExact_conePackage (f : K ⟶ L) :
    IsAdmissibleShortExact (conePackage f).inclusion (conePackage f).projection :=
  (conePackage f).isAdmissibleShortExact

end SheafOfModules.DifferentialGradedModule

end
