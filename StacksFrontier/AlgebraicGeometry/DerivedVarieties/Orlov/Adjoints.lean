module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.Regular
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterizationFiniteExt
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverField
public import StacksFrontier.CategoryTheory.Triangulated.LinearYonedaHomological
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exact functors between perfect derived categories of proper schemes have adjoints

Let `k` be a field and let `X`, `Y` be proper schemes over `k` with `X` regular. Every `k`-linear
exact functor `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` has an exact right adjoint and an exact left adjoint:
this is [Stacks, Tag 0FYN].

The proof is the source's. For `M` perfect on `Y` the contravariant functor
`K ↦ Hom_Y(F(K), M)` on `D_perf(𝒪_X)` is `k`-linear and cohomological, and it has finite total
dimension `∑_n dim_k Ext^n_Y(F(K), M) < ∞` by [Stacks, Tag 0FYC] (the implication (1) ⇒ (2) of
[Stacks, Tag 0FYD], `M` being in `D^b_Coh(𝒪_Y)`); so by the representability theorem
[Stacks, Tag 0FYH] it is `Hom_X(-, K')` for some `K'` in `D^b_Coh(𝒪_X)`, which is perfect because
`X` is regular. That is the right adjoint, objectwise. For the left adjoint the covariant functor
`K ↦ Hom_Y(M, F(K))` is represented by [Stacks, Tag 0H4A]. An adjoint of an exact functor is
exact ([Stacks, Tag 0A8D]).

## The two models

Representability is a statement about functors to `Mod_k` with values in `Type u`, so it lives at
the locally small model `perfectDerived X` of `D_perf(𝒪_X)`, whose morphisms are in `Type u`.
[Stacks, Tag 0FYN] is stated at the standard model `PerfectDerivedCategory X`. The two are
identified by `perfectModelEquivalence`, the restriction of the triangulated `k`-linear comparison
`Stacks.AlgebraicGeometry.DerivedVarieties.Representability.modelEquivalence` to the perfect
objects; existence of adjoints is transported along it.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.perfectModelEquivalence`: the comparison of
  the two models of `D_perf(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.cardinalSum_rank_hom_shift_lt_aleph0`: finite
  total dimension of `Ext` between perfect objects on a proper scheme, at the locally small model.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isLeftAdjoint_and_isRightAdjoint`: every
  `k`-linear exact `F` is a left and a right adjoint, at the standard model.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.exists_exact_rightAdjoint_and_leftAdjoint`:
  **[Stacks, Tag 0FYN]**, the adjoints being exact.

## References

* [Stacks Project, Tag 0FYN](https://stacks.math.columbia.edu/tag/0FYN)
* [Stacks Project, Tag 0FYH](https://stacks.math.columbia.edu/tag/0FYH)
* [Stacks Project, Tag 0H4A](https://stacks.math.columbia.edu/tag/0H4A)
* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes
open Stacks.AlgebraicGeometry.DerivedVarieties.Representability
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe v u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance] AlgebraicGeometry.isTriangulated_isPerfect_locallySmall
attribute [local instance] AlgebraicGeometry.modulesLinear

/-! ### Elementary linear algebra of shifted morphisms -/

section Linear

variable (k : Type*) [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- `Hom(A[n], B) ≃ Hom(A, B[-n])`, `k`-linearly, in a `k`-linear category with a linear
shift. -/
def homShiftNegLinearEquiv (A B : C) (n : ℤ) : (A⟦n⟧ ⟶ B) ≃ₗ[k] (A ⟶ B⟦-n⟧) :=
  { toEquiv := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C (-n))).homEquiv
    map_add' := fun _ _ => (shiftFunctor C (-n)).map_add
    map_smul' := fun r f => (shiftFunctor C (-n)).map_smul r f } ≪≫ₗ
    Linear.homCongr k ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).app A) (Iso.refl _)

end Linear

/-- Morphisms of a full subcategory are the morphisms of the ambient category, `k`-linearly. -/
def fullSubcategoryHomLinearEquiv (k : Type*) [Semiring k] {C : Type*} [Category* C]
    [Preadditive C] [Linear k C] (P : ObjectProperty C) (A B : P.FullSubcategory) :
    (A ⟶ B) ≃ₗ[k] (A.obj ⟶ B.obj) :=
  { toEquiv := P.fullyFaithfulι.homEquiv
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- A cardinal sum indexed by `ℤ` is finite as soon as it is, summand by summand and up to
universe lifts, a reindexing of a finite one. -/
theorem cardinalSum_lt_aleph0_of_lift_eq_comp {f : ℤ → Cardinal.{u}} {g : ℤ → Cardinal.{v}}
    (σ : ℤ ≃ ℤ) (h : ∀ n, Cardinal.lift.{v} (f n) = Cardinal.lift.{u} (g (σ n)))
    (hg : Cardinal.sum g < Cardinal.aleph0) :
    Cardinal.sum f < Cardinal.aleph0 := by
  obtain ⟨h1, h2⟩ := CoherentCharacterization.lt_aleph0_cardinalSum_iff.1 hg
  refine CoherentCharacterization.lt_aleph0_cardinalSum_iff.2 ⟨fun n => ?_, ?_⟩
  · exact Cardinal.lift_lt_aleph0.1 ((h n).trans_lt (Cardinal.lift_lt_aleph0.2 (h1 (σ n))))
  · refine (h2.preimage σ.injective.injOn).subset fun n hn h0 => hn ?_
    exact Cardinal.lift_eq_zero.1
      ((h n).trans (by rw [show g (σ n) = 0 from h0, Cardinal.lift_zero]))

/-! ### Finite total `Ext` between perfect objects at the locally small model -/

variable {k : Type u} [Field k]

section FiniteExt

variable (Y : Over (Spec (CommRingCat.of k))) [IsProper Y.hom]

section Standard

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Finite total `Ext` between perfect objects on a proper scheme, at the standard model**:
[Stacks, Tag 0FYC], from the implication (1) ⇒ (2) of [Stacks, Tag 0FYD], a perfect object on a
Noetherian scheme being in `D^b_Coh`. -/
theorem cardinalSum_rank_hom_shift_lt_aleph0_standard {A B : DerivedCategory Y.left.Modules}
    (hA : IsPerfect (X := Y.left.toRingedSpace) A) (hB : IsPerfect (X := Y.left.toRingedSpace) B) :
    Cardinal.sum (fun n : ℤ => Module.rank k (A ⟶ B⟦n⟧)) < Cardinal.aleph0 := by
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  exact CoherentCharacterization.cardinalSum_rank_ext_lt_aleph0_of_derivedCategoryBBounded' Y B
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect Y.left B hB) A hA

end Standard

/-- **Finite total `Ext` between perfect objects on a proper scheme, at the locally small model**:
`∑_n dim_k Hom(A, B[n]) < ∞`. This is `cardinalSum_rank_hom_shift_lt_aleph0_standard` carried
across the comparison of models, which is fully faithful, `k`-linear and commutes with shifts. -/
theorem cardinalSum_rank_hom_shift_lt_aleph0 {A B : DerivedCategory Y.left.Modules}
    (hA : IsPerfect.{u, u, u} (X := Y.left.toRingedSpace) A)
    (hB : IsPerfect.{u, u, u} (X := Y.left.toRingedSpace) B) :
    Cardinal.sum (fun n : ℤ => Module.rank k (A ⟶ B⟦n⟧)) < Cardinal.aleph0 := by
  let e := modelEquivalence Y.left
  have hA' := (isPerfect_modelEquivalence_inverse_obj_iff Y.left A).2 hA
  have hB' := (isPerfect_modelEquivalence_inverse_obj_iff Y.left B).2 hB
  refine cardinalSum_lt_aleph0_of_lift_eq_comp (Equiv.refl ℤ) (fun n => ?_)
    (cardinalSum_rank_hom_shift_lt_aleph0_standard Y hA' hB')
  exact (({ toEquiv := e.fullyFaithfulInverse.homEquiv
            map_add' := fun _ _ => e.inverse.map_add
            map_smul' := fun r f => e.inverse.map_smul r f } :
          (A ⟶ B⟦n⟧) ≃ₗ[k] (e.inverse.obj A ⟶ e.inverse.obj (B⟦n⟧))) ≪≫ₗ
      Linear.homCongr k (Iso.refl _) ((e.inverse.commShiftIso n).app B)).lift_rank_eq

end FiniteExt

/-! ### Adjoints at the locally small model -/

section LocallySmall

open Pretriangulated.Opposite

variable (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [IsProper Y.hom]
  (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated]
  [F.Linear k]

/-- `Hom(F(E[n]), M) ≃ Hom(F(E), M[-n])` in the ambient derived category, `k`-linearly. -/
def homShiftObjLinearEquiv (E : perfectDerived X.left) (M : perfectDerived Y.left) (n : ℤ) :
    (F.obj (E⟦n⟧) ⟶ M) ≃ₗ[k] ((F.obj E).obj ⟶ M.obj⟦-n⟧) :=
  Linear.homCongr k ((F.commShiftIso n).app E) (Iso.refl M) ≪≫ₗ
    fullSubcategoryHomLinearEquiv k _ _ _ ≪≫ₗ
    Linear.homCongr k (((ObjectProperty.ι _).commShiftIso n).app (F.obj E)) (Iso.refl _) ≪≫ₗ
    homShiftNegLinearEquiv k _ _ n

/-- `Hom(M, F(E[n])) ≃ Hom(M, F(E)[n])` in the ambient derived category, `k`-linearly. -/
def homObjShiftLinearEquiv (E : perfectDerived X.left) (M : perfectDerived Y.left) (n : ℤ) :
    (M ⟶ F.obj (E⟦n⟧)) ≃ₗ[k] (M.obj ⟶ (F.obj E).obj⟦n⟧) :=
  Linear.homCongr k (Iso.refl M) ((F.commShiftIso n).app E) ≪≫ₗ
    fullSubcategoryHomLinearEquiv k _ _ _ ≪≫ₗ
    Linear.homCongr k (Iso.refl _) (((ObjectProperty.ι _).commShiftIso n).app (F.obj E))

variable {X Y}

include Y in
/-- **The right adjoint exists objectwise**: for `M` perfect on `Y` the functor
`K ↦ Hom_Y(F(K), M)` is representable, by [Stacks, Tag 0FYH]. -/
theorem rightAdjointObjIsDefined_of_isRegular (hX : IsRegular X.left) (M : perfectDerived Y.left) :
    F.rightAdjointObjIsDefined M := by
  let H : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k :=
    F.op ⋙ (linearYoneda k (perfectDerived Y.left)).obj M
  have hH : ∀ {E E' : (perfectDerived X.left)ᵒᵖ} (f : E ⟶ E') (r : k),
      H.map ((r • f.unop).op) = r • H.map f := by
    intro E E' f r
    ext g
    change F.map (r • f.unop) ≫ g = r • (F.map f.unop ≫ g)
    rw [Functor.map_smul]
    exact Linear.smul_comp _ _ _ _ _ _
  have hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (H.obj (op (E⟦n⟧)))) < Cardinal.aleph0 :=
    fun E => cardinalSum_lt_aleph0_of_lift_eq_comp (Equiv.neg ℤ)
      (g := fun n : ℤ => Module.rank k ((F.obj E).obj ⟶ M.obj⟦n⟧))
      (fun n => (homShiftObjLinearEquiv X Y F E M n).lift_rank_eq)
      (cardinalSum_rank_hom_shift_lt_aleph0 Y (F.obj E).property M.property)
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    Representability.exists_iso_linearYoneda_of_isHomological_of_isProper X H hH hfin
  let KP : perfectDerived X.left :=
    ⟨K, Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular
      hX K hK⟩
  exact (show (F.op ⋙ yoneda.obj M).RepresentableBy KP from
    { homEquiv := fun {E} => (ObjectProperty.fullyFaithfulι _).homEquiv.trans
        (e.app (op E)).toLinearEquiv.symm.toEquiv
      homEquiv_comp := fun f g =>
        (congrArg (fun φ => φ.hom ((ObjectProperty.ι _).map g)) (e.inv.naturality f.op) :) }
    ).isRepresentable

include Y in
/-- **The left adjoint exists objectwise**: for `M` perfect on `Y` the functor
`K ↦ Hom_Y(M, F(K))` is corepresentable, by [Stacks, Tag 0H4A]. -/
theorem leftAdjointObjIsDefined_of_isRegular (hX : IsRegular X.left) (M : perfectDerived Y.left) :
    F.leftAdjointObjIsDefined M := by
  let G : perfectDerived X.left ⥤ ModuleCat.{u} k :=
    F ⋙ (linearCoyoneda k (perfectDerived Y.left)).obj (op M)
  have hG : ∀ {E E' : perfectDerived X.left} (f : E ⟶ E') (r : k), G.map (r • f) = r • G.map f := by
    intro E E' f r
    ext g
    change g ≫ F.map (r • f) = r • (g ≫ F.map f)
    rw [Functor.map_smul]
    exact Linear.comp_smul _ _ _ _ _ _
  have hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (G.obj (E⟦n⟧))) < Cardinal.aleph0 :=
    fun E => cardinalSum_lt_aleph0_of_lift_eq_comp (Equiv.refl ℤ)
      (g := fun n : ℤ => Module.rank k (M.obj ⟶ (F.obj E).obj⟦n⟧))
      (fun n => (homObjShiftLinearEquiv X Y F E M n).lift_rank_eq)
      (cardinalSum_rank_hom_shift_lt_aleph0 Y M.property (F.obj E).property)
  obtain ⟨K, ⟨e⟩⟩ :=
    Representability.exists_iso_linearCoyoneda_of_isHomological_of_isRegular X hX G hG hfin
  exact (show (F ⋙ coyoneda.obj (op M)).CorepresentableBy K from
    { homEquiv := fun {E} => (e.app E).toLinearEquiv.symm.toEquiv
      homEquiv_comp := fun f g => (congrArg (fun φ => φ.hom g) (e.inv.naturality f) :) }
    ).isCorepresentable

include Y in
/-- **Every `k`-linear exact functor is a left and a right adjoint, at the locally small
model.** -/
theorem isLeftAdjoint_and_isRightAdjoint_locallySmall (hX : IsRegular X.left) :
    F.IsLeftAdjoint ∧ F.IsRightAdjoint :=
  ⟨Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (by
      ext M
      simpa using rightAdjointObjIsDefined_of_isRegular F hX M),
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (by
      ext M
      simpa using leftAdjointObjIsDefined_of_isRegular F hX M)⟩

end LocallySmall

/-! ### The comparison of the two models of `D_perf(𝒪_X)` -/

section Models

variable (X : Scheme.{u})

/-- **The comparison of the standard and the locally small model of `D_perf(𝒪_X)`**: the
restriction of `Stacks.AlgebraicGeometry.DerivedVarieties.Representability.modelEquivalence` to
the perfect objects, which it preserves and reflects. -/
def perfectModelEquivalence : PerfectDerivedCategory X ≌ perfectDerived X :=
  haveI : ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory X.Modules => IsPerfect.{u, u, u} (X := X.toRingedSpace) K) :=
    ⟨fun e h => isPerfect_of_iso X e h⟩
  (modelEquivalence X).congrFullSubcategory
    (funext fun K => propext (isPerfect_modelEquivalence_functor_obj_iff X K))

/-- The functor of `perfectModelEquivalence X` commutes with the shift. -/
instance perfectModelEquivalence_functor_commShift :
    (perfectModelEquivalence X).functor.CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (modelEquivalence X).functor) _).CommShift ℤ)

/-- The functor of `perfectModelEquivalence X` is triangulated. -/
instance perfectModelEquivalence_functor_isTriangulated :
    (perfectModelEquivalence X).functor.IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (modelEquivalence X).functor) _).IsTriangulated

/-- The inverse of `perfectModelEquivalence X` commutes with the shift. -/
instance perfectModelEquivalence_inverse_commShift :
    (perfectModelEquivalence X).inverse.CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (modelEquivalence X).inverse) _).CommShift ℤ)

/-- The inverse of `perfectModelEquivalence X` is triangulated. -/
instance perfectModelEquivalence_inverse_isTriangulated :
    (perfectModelEquivalence X).inverse.IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (modelEquivalence X).inverse) _).IsTriangulated

end Models

section ModelsLinear

variable (X : Over (Spec (CommRingCat.of k)))

/-- The functor of `perfectModelEquivalence X.left` is `k`-linear. -/
instance perfectModelEquivalence_functor_linear :
    (perfectModelEquivalence X.left).functor.Linear k where
  map_smul f r := (ObjectProperty.fullyFaithfulι _).map_injective
    ((modelEquivalence X.left).functor.map_smul r f.hom)

/-- The inverse of `perfectModelEquivalence X.left` is `k`-linear. -/
instance perfectModelEquivalence_inverse_linear :
    (perfectModelEquivalence X.left).inverse.Linear k where
  map_smul f r := (ObjectProperty.fullyFaithfulι _).map_injective
    ((modelEquivalence X.left).inverse.map_smul r f.hom)

end ModelsLinear

/-! ### Adjoints at the standard model -/

section Standard

variable (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [IsProper Y.hom]

/-- For `X`, `Y` proper over a field `k` with `X` regular, every `k`-linear exact functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is both a left and a right adjoint. -/
theorem isLeftAdjoint_and_isRightAdjoint (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear k] :
    F.IsLeftAdjoint ∧ F.IsRightAdjoint := by
  let eX := perfectModelEquivalence X.left
  let eY := perfectModelEquivalence Y.left
  let F' : perfectDerived X.left ⥤ perfectDerived Y.left := eX.inverse ⋙ F ⋙ eY.functor
  obtain ⟨hl, hr⟩ := isLeftAdjoint_and_isRightAdjoint_locallySmall (Y := Y) F' hX
  let iso : eX.functor ⋙ F' ⋙ eY.inverse ≅ F :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eX.unitIso.symm _ ≪≫ Functor.leftUnitor _) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F eY.unitIso.symm ≪≫ Functor.rightUnitor F
  exact ⟨Functor.isLeftAdjoint_of_iso iso, Functor.isRightAdjoint_of_iso iso⟩

/-- **The right adjoint of [Stacks, Tag 0FYN]**: a `k`-linear exact functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` has an exact right adjoint. -/
theorem exists_exact_rightAdjoint (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear k] :
    ∃ G : PerfectDerivedCategory Y.left ⥤ PerfectDerivedCategory X.left,
      Nonempty (F ⊣ G) ∧ ∃ hG : G.CommShift ℤ, letI := hG; G.IsTriangulated := by
  have := (isLeftAdjoint_and_isRightAdjoint X Y hX F).1
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  let hG : F.rightAdjoint.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨F.rightAdjoint, ⟨adj⟩, hG, adj.isTriangulated_rightAdjoint⟩

/-- **The left adjoint of [Stacks, Tag 0FYN]**: a `k`-linear exact functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` has an exact left adjoint. -/
theorem exists_exact_leftAdjoint (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear k] :
    ∃ G : PerfectDerivedCategory Y.left ⥤ PerfectDerivedCategory X.left,
      Nonempty (G ⊣ F) ∧ ∃ hG : G.CommShift ℤ, letI := hG; G.IsTriangulated := by
  have := (isLeftAdjoint_and_isRightAdjoint X Y hX F).2
  let adj : F.leftAdjoint ⊣ F := Adjunction.ofIsRightAdjoint F
  let hG : F.leftAdjoint.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  exact ⟨F.leftAdjoint, ⟨adj⟩, hG, adj.isTriangulated_leftAdjoint⟩

/-- **[Stacks, Tag 0FYN].** Let `k` be a field and let `X`, `Y` be proper schemes over `k`. If `X`
is regular, then any `k`-linear exact functor `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` has an exact right
adjoint and an exact left adjoint.

Here `D_perf` is `PerfectDerivedCategory`, "exact" is a triangulated functor (a commutation with
the shift making it `CategoryTheory.Functor.IsTriangulated`), and `k`-linearity is for the
structure induced by the structure morphisms (`AlgebraicGeometry.modulesLinear`). -/
@[stacks 0FYN]
theorem exists_exact_rightAdjoint_and_leftAdjoint (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear k] :
    (∃ G : PerfectDerivedCategory Y.left ⥤ PerfectDerivedCategory X.left,
      Nonempty (F ⊣ G) ∧ ∃ hG : G.CommShift ℤ, letI := hG; G.IsTriangulated) ∧
    (∃ G : PerfectDerivedCategory Y.left ⥤ PerfectDerivedCategory X.left,
      Nonempty (G ⊣ F) ∧ ∃ hG : G.CommShift ℤ, letI := hG; G.IsTriangulated) :=
  ⟨exists_exact_rightAdjoint X Y hX F, exists_exact_leftAdjoint X Y hX F⟩

end Standard

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
