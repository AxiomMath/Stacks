module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Localization.LocallySmall
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Saturation

@[expose] public section

/-!
# Intrinsic characterizations of the perfect objects of `D(R)`

Let `R` be a ring, not assumed commutative, and let `D(R)` be the derived category of `R`-modules.
The perfect
objects of `D(R)`, in the sense of `StacksDraft.Perfect.IsPerfect`, were defined by exhibiting a
representative: a bounded complex of finite projective modules. This module removes the
representative from the description twice over. First, the perfect objects are exactly the objects
of the triangulated envelope of the regular module `R` placed in degree zero, so that `R[0]` is a
classical generator of the perfect derived category. Second, the perfect objects are exactly the
compact objects of `D(R)`, a condition referring to nothing but the morphisms of `D(R)` and the
coproducts in it.

## Main results

* `StacksDraft.Perfect.isPerfect_eq_triangEnvelope_singleton_regularModule` ([stacks 0ATI]): the
  perfect objects form the smallest strictly full, saturated, triangulated subcategory of `D(R)`
  containing `R[0]`.
* `StacksDraft.Perfect.isPerfect_iff_isCompactObject` ([stacks 07LT]): an object of `D(R)` is
  perfect if and only if it is a compact object.

## Implementation notes

The full subcategory of perfect objects is represented by its object property on `D(R)`. Being the
smallest strictly full, saturated, triangulated subcategory containing `R[0]`, equivalently the
assertion that `R[0]` is a classical generator of it, is expressed by equality with
`CategoryTheory.ObjectProperty.triangEnvelope`.

The instances witnessing that perfectness is closed under isomorphism, contains zero, is a
triangulated subcategory and is stable under retracts are all `private` and installed only as local
instances: they are the hypotheses the envelope calculation consumes, and making them global would
put them on the instance graph of every importing module. Saturation is the one of the four that
does not follow from the two-out-of-three property of perfectness in a triangle; it is
`StacksDraft.Perfect.isPerfect_of_retract`, proved over an arbitrary ring in
`StacksFrontier/Homology/Perfect/Saturation.lean`.

Ring and modules share the universe `u`, so the module category contains the regular module and the
finite free modules used in the proof; this is the universe convention of the source. Compactness
is correspondingly tested against coproducts indexed in `Type u`.

Compactness of `R[0]` is a statement about the *small* derived category, whose homomorphism types
live in the same universe as the objects of `ModuleCat.{u} R`; the derived category used throughout
the rest of the development is Mathlib's standard localization of cochain complexes, whose
homomorphism types are a priori larger. The two are identified by the uniqueness of localizations,
and the identification is upgraded to a triangulated equivalence commuting with the shift; the
existence of the small localization comes from local smallness of the standard one, which in turn
follows from the existence of K-injective resolutions.

## References

* [Stacks Project, Tag 0ATI](https://stacks.math.columbia.edu/tag/0ATI)
* [Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT)
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

open scoped DirectSum

universe u v w z

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

section Envelope

/-! ### Perfectness as a triangulated subcategory

The envelope calculation needs the perfect objects to form a strictly full, saturated,
triangulated subcategory. Each of the four closure properties is recorded here as a `private`
local instance. -/

/-- Perfectness is closed under isomorphism in `D(R)`. -/
private theorem isPerfect_isClosedUnderIsomorphisms {R : Type u} [Ring R] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) where
  of_iso e := by
    rintro ⟨P, a, b, hPa, hPb, hPfinite, hPprojective, ⟨i⟩⟩
    exact ⟨P, a, b, hPa, hPb, hPfinite, hPprojective, ⟨e.symm ≪≫ i⟩⟩

attribute [local instance] isPerfect_isClosedUnderIsomorphisms

/-- The zero object of `D(R)` is perfect: the zero complex is a bounded complex of finite
projective modules representing it. -/
private lemma zero_isPerfect {R : Type u} [Ring R] :
    IsPerfect (0 : DerivedCategory (ModuleCat.{u} R)) := by
  let P : CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.zero
  have hP : IsZero P := HomologicalComplex.isZero_zero
  have hPge : P.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ => Functor.map_isZero (HomologicalComplex.eval _ _ i) hP
  have hPle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ => Functor.map_isZero (HomologicalComplex.eval _ _ i) hP
  have hsub (i : ℤ) : Subsingleton (P.X i) :=
    ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero (HomologicalComplex.eval _ _ i) hP)
  refine ⟨P, 0, 0, hPge, hPle, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · have := hsub i
    infer_instance
  · have := hsub i
    infer_instance
  · exact ⟨(isZero_zero _).iso (Functor.map_isZero DerivedCategory.Q hP)⟩

/-- Perfectness contains a zero object. -/
private theorem isPerfect_containsZero {R : Type u} [Ring R] :
    ObjectProperty.ContainsZero
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) where
  exists_zero := ⟨0, isZero_zero _, zero_isPerfect⟩

attribute [local instance] isPerfect_containsZero

/-- Perfectness is closed under extensions, by the two-out-of-three property [stacks 066R]. -/
private theorem isPerfect_isTriangulatedClosed₂ {R : Type u} [Ring R] :
    ObjectProperty.IsTriangulatedClosed₂
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) :=
  ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ ↦
    (isPerfect_of_distinguished T hT).2.1 h₁ h₃

attribute [local instance] isPerfect_isTriangulatedClosed₂

/-- The positive shift of a perfect object is perfect: rotate the contractible triangle on `K`. -/
private lemma isPerfect_shift_one {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) :
    IsPerfect (K⟦(1 : ℤ)⟧) := by
  let T := (Pretriangulated.contractibleTriangle K).rotate
  have h : IsPerfect T.obj₃ :=
    (isPerfect_of_distinguished T
      (Pretriangulated.rot_of_distTriang _
        (Pretriangulated.contractible_distinguished K))).1 hK zero_isPerfect
  simpa [T] using h

/-- The negative shift of a perfect object is perfect: shift the rotated contractible triangle. -/
private lemma isPerfect_shift_neg_one {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) :
    IsPerfect (K⟦(-1 : ℤ)⟧) := by
  let T := (CategoryTheory.shiftFunctor
    (Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} R))) (-1)).obj
    (Pretriangulated.contractibleTriangle K).rotate
  have hT : T ∈ Pretriangulated.distinguishedTriangles :=
    Pretriangulated.Triangle.shift_distinguished _
      (Pretriangulated.rot_of_distTriang _ (Pretriangulated.contractible_distinguished K)) (-1)
  have hzero : IsPerfect T.obj₂ :=
    ObjectProperty.prop_of_isZero _ (Functor.map_isZero _ (isZero_zero _))
  have hK' : IsPerfect
        ((CategoryTheory.shiftFunctor _ (1 : ℤ) ⋙
          CategoryTheory.shiftFunctor _ (-1 : ℤ)).obj K) := by
      let e : ((CategoryTheory.shiftFunctor _ (1 : ℤ) ⋙
          CategoryTheory.shiftFunctor _ (-1 : ℤ)).obj K) ≅ K :=
        (CategoryTheory.shiftFunctorAdd' _ (1 : ℤ) (-1 : ℤ) 0 (by omega)).symm.app K ≪≫
          (CategoryTheory.shiftFunctorZero _ ℤ).app K
      exact ObjectProperty.prop_of_iso _ e.symm hK
  have hthird : IsPerfect T.obj₃ := by simpa [T] using hK'
  have hfirst := (isPerfect_of_distinguished T hT).2.2 hzero hthird
  simpa [T] using hfirst

/-- Perfectness is stable under the shifts by nonnegative integers. -/
private lemma isPerfect_shift_nat {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) (n : ℕ) :
    IsPerfect (K⟦(n : ℤ)⟧) := by
  induction n with
  | zero =>
      exact ObjectProperty.prop_of_iso _
        ((CategoryTheory.shiftFunctorZero _ ℤ).symm.app K) hK
  | succ n ih =>
      have h := isPerfect_shift_one (K⟦(n : ℤ)⟧) ih
      exact ObjectProperty.prop_of_iso _
        ((CategoryTheory.shiftFunctorAdd' _ (n : ℤ) 1 (n + 1 : ℕ)
          (by omega)).symm.app K) h

/-- Perfectness is stable under the shifts by negative integers. -/
private lemma isPerfect_shift_negSucc {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) (n : ℕ) :
    IsPerfect (K⟦Int.negSucc n⟧) := by
  induction n with
  | zero => simpa using isPerfect_shift_neg_one K hK
  | succ n ih =>
      have h := isPerfect_shift_neg_one (K⟦Int.negSucc n⟧) ih
      exact ObjectProperty.prop_of_iso _
        ((CategoryTheory.shiftFunctorAdd' _ (Int.negSucc n) (-1) (Int.negSucc (n + 1))
          (by omega)).symm.app K) h

/-- Perfectness is stable under all shifts. -/
private theorem isPerfect_isStableUnderShift {R : Type u} [Ring R] :
    ObjectProperty.IsStableUnderShift
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) ℤ where
  isStableUnderShiftBy n := ⟨by
    intro K hK
    cases n with
    | ofNat n => exact isPerfect_shift_nat K hK n
    | negSucc n => exact isPerfect_shift_negSucc K hK n⟩

attribute [local instance] isPerfect_isStableUnderShift

/-- Perfectness is a triangulated subcategory of `D(R)`. -/
private theorem isPerfect_isTriangulated {R : Type u} [Ring R] :
    ObjectProperty.IsTriangulated
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) where

attribute [local instance] isPerfect_isTriangulated

/-- Perfectness is saturated: a retract of a perfect object is perfect, by
`StacksDraft.Perfect.isPerfect_of_retract`. -/
private theorem isPerfect_isStableUnderRetracts {R : Type u} [Ring R] :
    ObjectProperty.IsStableUnderRetracts
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) where
  of_retract ret hY := isPerfect_of_retract.{u, u} ret.i ret.r ret.retract hY

attribute [local instance] isPerfect_isStableUnderRetracts

/-! ### Finite projective modules are summands of finite free modules -/

/-- The regular module is a finite product of copies of itself. -/
private lemma regularModule_mem_binaryProductsClosure {R : Type u} [Ring R] :
    (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure (ModuleCat.of R R) :=
  ObjectProperty.le_limitsClosure _ (fun _ : Unit ↦ Discrete WalkingPair) _
    (ObjectProperty.ofObj_apply _ ())

/-- A free module on a nonempty finite basis is a finite product of copies of the regular
module. -/
private lemma positiveFiniteFree_mem_binaryProductsClosure {R : Type u} [Ring R] (n : ℕ) :
    (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure
      (ModuleCat.of R (Fin (n + 1) → R)) := by
  induction n with
  | zero =>
      apply ObjectProperty.prop_of_iso _
        (LinearEquiv.funUnique (Fin 1) R R).symm.toModuleIso
      exact regularModule_mem_binaryProductsClosure
  | succ n ih =>
      apply ObjectProperty.prop_of_iso _
        ((LinearEquiv.piCongrLeft R (fun _ : Option (Fin (n + 1)) ↦ R) (finSuccEquiv (n + 1)) ≪≫ₗ
          LinearEquiv.piOptionEquivProd R).toModuleIso.symm)
      exact ObjectProperty.prop_of_iso
        (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure
        ((IsLimit.conePointUniqueUpToIso
          (limit.isLimit (pair (ModuleCat.of R R) (ModuleCat.of R (Fin (n + 1) → R))))
          (BinaryBiproduct.isLimit (ModuleCat.of R R)
            (ModuleCat.of R (Fin (n + 1) → R)))) ≪≫
          ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (Fin (n + 1) → R)))
        (ObjectProperty.prop_prod
          (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure
          (ModuleCat.of R R) (ModuleCat.of R (Fin (n + 1) → R))
          regularModule_mem_binaryProductsClosure ih)

/-- Every finite free module, the zero module included, is a direct summand of a finite product of
copies of the regular module. -/
private lemma finiteFree_mem_retractClosure {R : Type u} [Ring R] (n : ℕ) :
    (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure.retractClosure
      (ModuleCat.of R (Fin n → R)) := by
  cases n with
  | zero =>
      exact ObjectProperty.prop_retractClosure
        regularModule_mem_binaryProductsClosure
        ((ModuleCat.isZero_iff_subsingleton.mpr inferInstance).retract _)
  | succ n =>
      apply ObjectProperty.le_retractClosure
      exact positiveFiniteFree_mem_binaryProductsClosure n

/-- A finite projective module is a direct summand of a finite free module, hence of a finite
product of copies of the regular module. -/
private lemma finiteProjective_mem_retractClosure {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    (hM : Module.Finite R M ∧ Module.Projective R M) :
    (ObjectProperty.singleton (ModuleCat.of R R)).binaryProductsClosure.retractClosure M := by
  let : Module.Finite R M := hM.1
  let : Module.Projective R M := hM.2
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ObjectProperty.prop_of_retract _
    { i := ModuleCat.ofHom g
      r := ModuleCat.ofHom f
      retract := by simpa [← ModuleCat.hom_comp] using congrArg ModuleCat.ofHom hfg }
    (finiteFree_mem_retractClosure n)

/-- The regular module placed in degree zero is perfect. -/
private lemma regularModule_isPerfect {R : Type u} [Ring R] :
    IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  have hX (i : ℤ) : Nonempty (R ≃ₗ[R] P.X i) ∨ Subsingleton (P.X i) := by
    by_cases hi : i = 0
    · subst i
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).symm
      exact Or.inl ⟨LinearEquiv.ofBijective e.hom.hom
        (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom)⟩
    · exact Or.inr (ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) i hi))
  refine ⟨P, 0, 0, inferInstance, inferInstance, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · rcases hX i with ⟨⟨e⟩⟩ | _
    · exact Module.Finite.equiv e
    · infer_instance
  · rcases hX i with ⟨⟨e⟩⟩ | _
    · exact Module.Projective.of_equiv e
    · infer_instance
  · exact ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
      (ModuleCat.of R R)⟩

/-- **Stacks 0ATI.** The perfect objects of `D(R)` form the smallest strictly full, saturated,
triangulated subcategory containing the regular module `R` in degree zero. Equivalently, `R[0]`
is a classical generator of the perfect derived category. -/
@[stacks 0ATI]
theorem isPerfect_eq_triangEnvelope_singleton_regularModule {R : Type u} [Ring R] :
    (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) =
      (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).triangEnvelope := by
  let E : ObjectProperty (ModuleCat.{u} R) :=
    ObjectProperty.singleton (ModuleCat.of R R)
  let S : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
    ObjectProperty.singleton
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  show (IsPerfect : ObjectProperty _) = S.triangEnvelope
  let : S.Nonempty := ⟨⟨
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R),
    ObjectProperty.ofObj_apply _ ()⟩⟩
  apply le_antisymm
  · intro K hK
    obtain ⟨P, a, b, hPge, hPle, hPfinite, hPprojective, ⟨e⟩⟩ := hK
    let a' := min a b
    let b' := max a b
    let : P.IsStrictlyGE a' := P.isStrictlyGE_of_ge a' a (min_le_left _ _)
    let : P.IsStrictlyLE b' := P.isStrictlyLE_of_le b b' (le_max_right _ _)
    have hterms : ∀ i ∈ Set.Icc a' b', E.binaryProductsClosure.retractClosure (P.X i) := by
      intro i _
      exact finiteProjective_mem_retractClosure (P.X i) ⟨hPfinite i, hPprojective i⟩
    have hQP :=
      (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
        E min_le_max).2 P hterms
    have hbase :
        (⨆ i ∈ Set.Icc a' b',
          E.map (DerivedCategory.singleFunctor (ModuleCat.{u} R) i)) ≤
          S.triangEnvelope := by
      refine iSup₂_le fun i hi ↦ ?_
      rintro X ⟨Y, hY, ⟨f⟩⟩
      have hYeq : ModuleCat.of R R = Y := by simpa [E] using hY
      subst Y
      apply S.triangEnvelope.prop_of_iso f
      let q : ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))⟦-i⟧ ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj (ModuleCat.of R R) :=
        ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso (-i) i 0
          (by omega)).app _
      exact S.triangEnvelope.prop_of_iso q
        (ObjectProperty.le_shift S.triangEnvelope (-i) _
          (S.le_triangEnvelope _ (by simp [S])))
    have htower :
        (ObjectProperty.extensionProductIter
          (⨆ i ∈ Set.Icc a' b',
            E.map (DerivedCategory.singleFunctor (ModuleCat.{u} R) i)).binaryProductsClosure
          (b' - a').toNat).retractClosure ≤
            S.triangEnvelope := by
      rw [ObjectProperty.retractClosure_le_iff]
      apply ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂
      rwa [ObjectProperty.binaryProductsClosure_le_iff]
    exact ObjectProperty.prop_of_iso _ e.symm (htower _ hQP)
  · rw [ObjectProperty.triangEnvelope_le_iff]
    simpa [S] using regularModule_isPerfect (R := R)

end Envelope

section Compactness

-- The localization comparisons below rewrite through `let`-bound functors and instances, so
-- unification has to unfold those definitions.
set_option backward.isDefEq.respectTransparency false

/-! ### Local smallness of the derived category

A K-injective resolution turns the homomorphisms out of an arbitrary object into homomorphisms of
cochain complexes, of which there are only `Type v` many. -/

/-- Homomorphisms between complexes are all realized by maps of complexes as soon as the
localization functor to the homotopy category is bijective on the corresponding homomorphisms. -/
private theorem map_surjective_of_bijective_Qh_map
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ)
    (h : Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj L) →
        _)) :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  obtain ⟨g, hg⟩ := h.surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K)).1
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- Homomorphisms into a K-injective complex are all realized by maps of complexes. -/
theorem map_surjective_of_isKInjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ I) → _) :=
  map_surjective_of_bijective_Qh_map _ _ (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) I)

/-- The derived category of an abelian category with enough injectives and countable exact products
is locally small: replace the target by a K-injective resolution and the homomorphisms become a
quotient of a set of maps of complexes. -/
theorem locallySmall_derivedCategory
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C] :
    LocallySmall.{v} (DerivedCategory C) := by
  constructor
  intro X Y
  obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage Y)
  let e : Y ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫ asIso (DerivedCategory.Q.map f)
  let eX := DerivedCategory.Q.objObjPreimageIso X
  have : Small.{v} (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X) ⟶
      DerivedCategory.Q.obj I) :=
    small_of_surjective (map_surjective_of_isKInjective (DerivedCategory.Q.objPreimage X) I)
  exact small_of_injective (Iso.homCongr eX.symm e).injective

/-! ### The regular module generates the derived category -/

/-- A map of complexes which becomes zero in the derived category induces zero on cohomology. -/
theorem homologyMap_eq_zero_of_Q_map_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (hf : DerivedCategory.Q.map f = 0) (n : ℤ) :
    HomologicalComplex.homologyMap f n = 0 := by
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors C n).hom.app K)).1
  rw [← DerivedCategory.homologyFunctorFactors_hom_naturality, hf]
  simp only [Functor.map_zero, zero_comp]
  exact (comp_zero).symm

/-- An object of the derived category with vanishing cohomology is a zero object. -/
theorem isZero_of_homology_isZero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DerivedCategory C) (hK : ∀ n, IsZero ((DerivedCategory.homologyFunctor C n).obj K)) :
    IsZero K := by
  have : IsIso (0 : K ⟶ K) := (DerivedCategory.isIso_iff C _).2 fun n =>
    (hK n).isIso (hK n) _
  apply (IsZero.iff_id_eq_zero K).2
  apply (cancel_mono (0 : K ⟶ K)).1
  simp

/-- A projective separator of an abelian category, placed in degree zero, is a weak generator of
the derived category: an object receiving only zero maps from all its shifts has no nonzero map
out of the separator into any cohomology module, hence vanishing cohomology. -/
theorem isWeakTriangulatedGenerator_single_of_projective_separator
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (hP : IsSeparator P) :
    (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor C 0).obj P)).IsWeakTriangulatedGenerator := by
  intro K hK
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  apply isZero_of_homology_isZero K
  intro n
  have hL : IsZero (L.homology n) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply hP
    intro G hG g
    simp only [ObjectProperty.singleton_iff] at hG
    subst G
    let a := Projective.factorThru g (L.homologyπ n)
    let φ : (CochainComplex.singleFunctor C n).obj P ⟶ L :=
      HomologicalComplex.mkHomFromSingle (a ≫ L.iCycles n) (fun j _ => by simp)
    have hφ : DerivedCategory.Q.map φ = 0 := by
      apply (cancel_mono e.hom).1
      rw [zero_comp]
      apply hK
      refine ⟨(DerivedCategory.singleFunctor C 0).obj P, -n, ?_, by simp⟩
      exact (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by omega)).app P).symm
    have hc : HomologicalComplex.cyclesMap φ n =
        (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n P).hom ≫ a := by
      apply (cancel_mono (L.iCycles n)).1
      simp [φ, HomologicalComplex.cyclesMap_i,
        HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
      rfl
    have hg : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n P).hom ≫ g = 0 := by
      rw [← Projective.factorThru_comp g (L.homologyπ n), ← Category.assoc,
        ← hc, ← HomologicalComplex.homologyπ_naturality,
        homologyMap_eq_zero_of_Q_map_eq_zero φ hφ n, comp_zero]
    have : g = 0 := (cancel_epi
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n P).hom).1 (by simpa using hg)
    simp [this]
  exact hL.of_iso ((DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors C n).app L)

/-! ### Termwise coproducts of cochain complexes

A coproduct of cochain complexes is computed degreewise, and a family of homotopies out of the
summands assembles into a homotopy out of the coproduct. Hence the localization functor to the
homotopy category preserves coproducts. -/

section TermwiseCoproduct

variable (A : Type u) [Category.{v} A] [Abelian A]

open HomologicalComplex

/-- The degree-`n` part of a coproduct of cochain complexes is the coproduct of the degree-`n`
parts. -/
private noncomputable def degreewiseIsColimit {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ) (n : ℤ) :
    IsColimit ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K))) :=
  isColimitOfPreserves _ (coproductIsCoproduct K)

/-- The inclusions of the degreewise colimit cofan are the degree-`n` components of the inclusions
of the coproduct. -/
private lemma degreewiseIsColimit_inj {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ)
    (n : ℤ) (j : J) :
    ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ = (Sigma.ι K j).f n := by
  simp [HomologicalComplex.eval, Cofan.mk]

/-- The component of the homotopy assembled from a family of homotopies out of the summands. -/
private noncomputable def descHomotopyComponent {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (H : ∀ j, (i k : ℤ) → (K j).X i ⟶ Y.X k) (n m : ℤ) :
    (∐ K).X n ⟶ Y.X m :=
  (degreewiseIsColimit A K n).desc { pt := Y.X m, ι := Discrete.natTrans (fun ⟨j⟩ => H j n m) }

/-- The assembled homotopy component restricts to the given one on each summand. -/
private lemma descHomotopyComponent_fac {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (H : ∀ j, (i k : ℤ) → (K j).X i ⟶ Y.X k)
    (n m : ℤ) (j : J) :
    (Sigma.ι K j).f n ≫ descHomotopyComponent A K Y H n m = H j n m := by
  have := (degreewiseIsColimit A K n).fac
    { pt := Y.X m, ι := Discrete.natTrans (fun ⟨j⟩ => H j n m) } ⟨j⟩
  simp only [HomologicalComplex.eval, Functor.mapCocone, Cofan.mk,
    Functor.const_obj_obj, Discrete.natTrans_app] at this
  rw [descHomotopyComponent]; exact this

/-- Two maps out of a coproduct of cochain complexes that are homotopic on each summand are
homotopic. -/
private noncomputable def coproductHomotopy {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (f g : (∐ K) ⟶ Y)
    (H : ∀ j, Homotopy (Sigma.ι K j ≫ f) (Sigma.ι K j ≫ g)) :
    Homotopy f g where
  hom n m := descHomotopyComponent A K Y (fun j => (H j).hom) n m
  zero n m hnm := by
    apply (degreewiseIsColimit A K n).hom_ext
    rintro ⟨j⟩
    have e1 : ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
        (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ ≫
          descHomotopyComponent A K Y (fun j => (H j).hom) n m
        = (H j).hom n m := by
      rw [degreewiseIsColimit_inj]
      exact descHomotopyComponent_fac A K Y _ n m j
    rw [e1, show ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
        (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ ≫
          (0 : (∐K).X n ⟶ Y.X m) = 0 from comp_zero]
    exact (H j).zero n m hnm
  comm n := by
    apply (degreewiseIsColimit A K n).hom_ext
    rintro ⟨j⟩
    have hd : (Sigma.ι K j).f n ≫ (dNext n)
        (fun a b => descHomotopyComponent A K Y (fun j => (H j).hom) a b)
        = (dNext n) (H j).hom := by
      rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n+1)),
          dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n+1)),
          ← Category.assoc, (Sigma.ι K j).comm n (n+1), Category.assoc,
          descHomotopyComponent_fac]
    have hp : (Sigma.ι K j).f n ≫ (prevD n)
        (fun a b => descHomotopyComponent A K Y (fun j => (H j).hom) a b)
        = (prevD n) (H j).hom := by
      rw [prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n-1) n),
          prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n-1) n),
          ← Category.assoc, descHomotopyComponent_fac]
    have key := (H j).comm n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at key
    change (Sigma.ι K j).f n ≫ _ = (Sigma.ι K j).f n ≫ _
    rw [Preadditive.comp_add, Preadditive.comp_add, hd, hp, key]

/-- The map out of the image of a coproduct of complexes in the homotopy category determined by a
family of maps out of the summands. -/
private noncomputable def homotopyCoproductDesc {J : Type*}
    (K : J → CochainComplex A ℤ) [HasCoproduct K]
    (P : HomotopyCategory A (ComplexShape.up ℤ))
    (inj : ∀ j, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j) ⟶ P) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (∐ K) ⟶ P :=
  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    (Sigma.desc (fun j => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage
      (inj j : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j)
        ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.as)))

/-- The descended map restricts to the given map on each summand. -/
private lemma homotopyCoproductDesc_fac {J : Type*}
    (K : J → CochainComplex A ℤ) [HasCoproduct K]
    (P : HomotopyCategory A (ComplexShape.up ℤ))
    (inj : ∀ j, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j) ⟶ P) (j : J) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j) ≫
      homotopyCoproductDesc A K P inj
      = inj j := by
  rw [homotopyCoproductDesc]; rw [← Functor.map_comp]; rw [Sigma.ι_desc]
  exact Functor.map_preimage _ _

/-- The image of a termwise coproduct of cochain complexes is a coproduct in the homotopy
category. -/
private noncomputable def homotopyCoproductIsColimit {J : Type*} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (∐ K))
      (fun j => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j))) := by
  refine Cofan.IsColimit.mk _ (fun s => homotopyCoproductDesc A K s.pt (fun j => s.inj j))
    (fun s j => homotopyCoproductDesc_fac A K s.pt _ j) (fun s m hm => ?_)
  obtain ⟨mc, rfl⟩ : ∃ mc, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map mc = m :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage m,
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_preimage m⟩
  refine HomotopyCategory.eq_of_homotopy _ _ (coproductHomotopy A K _ _ _ (fun j => ?_))
  refine HomotopyCategory.homotopyOfEq _ _ ?_
  rw [Functor.map_comp]
  have hmj : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j)
      ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map mc = s.inj j := hm j
  rw [hmj, ← homotopyCoproductDesc_fac A K s.pt (fun j => s.inj j) j, homotopyCoproductDesc]
  rw [← Functor.map_comp]

end TermwiseCoproduct

/-! ### The localization functor preserves coproducts -/

/-- The localization functor `Q : C(A) ⥤ D(A)` preserves coproducts of any shape available in
`A`. -/
private theorem preservesColimitsOfShape_discrete_Q
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    (J : Type*) [HasCoproductsOfShape J C] :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := C)) := by
  have hK (K : J → CochainComplex C ℤ) :
      PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := C)) := by
    let q := HomotopyCategory.quotient C (.up ℤ)
    have hc := (isColimit_mapCofan_of_exists_map_bijective DerivedCategory.Qh
      (exists_map_bijective_Qh C) (fun j => q.map (Sigma.ι K j))
      (homotopyCoproductIsColimit C K)).some
    have : PreservesColimit (Discrete.functor K) (q ⋙ DerivedCategory.Qh) :=
      preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
        ((isColimitMapCoconeCofanMkEquiv (q ⋙ DerivedCategory.Qh) K (Sigma.ι K)).symm hc)
    exact preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso C)
  constructor
  intro F
  have := hK (fun j => F.obj ⟨j⟩)
  exact preservesColimit_of_iso_diagram
    (K₁ := Discrete.functor (fun j => F.obj ⟨j⟩)) DerivedCategory.Q
    (Discrete.natIso (fun ⟨j⟩ => Iso.refl _))

/-- The derived category inherits the coproducts of the underlying abelian category. -/
theorem hasCoproductsOfShape_derivedCategory
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    (J : Type*) [HasCoproductsOfShape J C] :
    HasCoproductsOfShape J (DerivedCategory C) := by
  have := preservesColimitsOfShape_discrete_Q (C := C) J
  constructor
  intro F
  let K : Discrete J ⥤ CochainComplex C ℤ :=
    Discrete.functor (fun j => DerivedCategory.Q.objPreimage (F.obj ⟨j⟩))
  have : HasColimit (K ⋙ DerivedCategory.Q) :=
    inferInstance
  exact hasColimit_of_iso (F := K ⋙ DerivedCategory.Q)
    (Discrete.natIso (fun j => (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm))

/-! ### Compactness of the regular module and of its image in the derived category -/

/-- The compactness map out of a direct sum of homomorphism groups is always injective: a summand
is recovered by composing with the projection onto it. -/
public theorem injective_directSumToHom
    {C : Type*} [Category C] [Preadditive C] (P : C)
    {J : Type*} [DecidableEq J] (E : J → C) [HasCoproduct E] :
    Function.Injective (DirectSum.toAddMonoid
      (fun j => Preadditive.rightComp P (Sigma.ι E j))) := by
  classical
  have hp (j : J) (x : ⨁ i, (P ⟶ E i)) :
      DirectSum.toAddMonoid (fun i => Preadditive.rightComp P (Sigma.ι E i)) x ≫
        Sigma.desc (Pi.single j (𝟙 (E j))) = x j := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp [Preadditive.add_comp, hx, hy]
    | of i f =>
      by_cases h : i = j
      · subst i
        simp [DirectSum.toAddMonoid_of, Preadditive.rightComp]
      · simp [DirectSum.toAddMonoid_of, Preadditive.rightComp, h, Ne.symm h,
          DirectSum.of_eq_of_ne]
  intro x y h
  apply DFinsupp.ext
  intro j
  rw [← hp j x, ← hp j y, h]

/-- The regular module is a compact object of the category of `R`-modules: a homomorphism out of
`R` is determined by the image of `1`, which lies in a finite subsum. -/
public theorem isCompactObject_regularModule {R : Type u} [Ring R] :
    IsCompactObject.{u} (ModuleCat.of R R) := by
  classical
  constructor
  intro J _ E _
  refine ⟨injective_directSumToHom _ E, ?_⟩
  intro f
  let e := ModuleCat.coprodIsoDirectSum E
  let x := (f ≫ e.hom) 1
  let a (j : J) : ModuleCat.of R R ⟶ E j :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R (E j) (x j))
  refine ⟨∑ j ∈ x.support, DirectSum.of _ j (a j), ?_⟩
  apply (cancel_mono e.hom).1
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Preadditive.sum_comp, Category.assoc]
  simp only [e, ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [a, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply,
    one_smul, DirectSum.lof]
  show ∑ j ∈ x.support, DFinsupp.single j (x j) = x
  exact DFinsupp.sum_single

/-- The regular module is a separator of the category of `R`-modules. -/
theorem isSeparator_regularModule {R : Type u} [Ring R] :
    IsSeparator (ModuleCat.of R R) := by
  intro X Y f g h
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, ModuleCat.hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)) 1

/-- The regular module in degree zero is a weak generator of `D(R)`. -/
public theorem isWeakTriangulatedGenerator_regularModule
    {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_single_of_projective_separator _ isSeparator_regularModule

/-- A projective object placed in a single degree gives a K-projective complex. -/
theorem isKProjective_single
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) [Projective P] (n : ℤ) :
    ((CochainComplex.singleFunctor C n).obj P).IsKProjective := by
  have (i : ℤ) : Projective (((CochainComplex.singleFunctor C n).obj P).X i) := by
    by_cases hi : i = n
    · subst i
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n P i hi).projective
  exact CochainComplex.isKProjective_of_projective _ n

/-- Homomorphisms out of a K-projective complex are all realized by maps of complexes. -/
theorem map_surjective_of_isKProjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P K : CochainComplex C ℤ) [P.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ K) → _) :=
  map_surjective_of_bijective_Qh_map _ _ (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient C (.up ℤ)).obj K))

/-- Local smallness provides a derived category whose homomorphism types live in the universe of
the morphisms of the underlying abelian category. -/
theorem nonempty_smallDerivedCategory
    {C : Type u} [Category.{v} C] [Abelian C]
    [EnoughInjectives C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C] :
    Nonempty (HasDerivedCategory.{v} C) := by
  have := locallySmall_derivedCategory (C := C)
  exact ⟨MorphismProperty.hasLocalizationOfLocallySmall'
    (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory.Q (C := C))⟩

/-- A morphism out of a compact object into an arbitrary colimit cofan factors through a finite
subsum. -/
public theorem exists_sum_cofan_of_isCompactObject
    {C : Type*} [Category C] [Preadditive C] (P : C) [IsCompactObject.{w} P]
    {J : Type w} {E : J → C} {S : C} (ι : ∀ j, E j ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (f : P ⟶ S) :
    ∃ (s : Finset J) (a : ∀ j, P ⟶ E j), ∑ j ∈ s, a j ≫ ι j = f := by
  classical
  have : HasCoproduct E := ⟨⟨_, hc⟩⟩
  let e := (coproductIsCoproduct E).coconePointUniqueUpToIso hc
  obtain ⟨x, hx⟩ := (IsCompactObject.bijective_toAddMonoid_rightComp_sigmaι E).surjective
    (f ≫ e.inv)
  refine ⟨x.support, fun j => x j, ?_⟩
  have hx' : ∑ j ∈ x.support, x j ≫ Sigma.ι E j = f ≫ e.inv := by
    have hs : (∑ j ∈ x.support, DirectSum.of _ j (x j)) = x := DFinsupp.sum_single
    have h := congrArg (DirectSum.toAddMonoid
      (fun j => Preadditive.rightComp P (Sigma.ι E j))) hs
    simpa only [map_sum, DirectSum.toAddMonoid_of,
      Preadditive.rightComp, AddMonoidHom.mk'_apply] using h.trans hx
  have he (j : J) : Sigma.ι E j ≫ e.hom = ι j :=
    (coproductIsCoproduct E).comp_coconePointUniqueUpToIso_hom hc ⟨j⟩
  simpa only [Preadditive.sum_comp, Category.assoc, he, Iso.inv_hom_id,
    Category.comp_id] using congrArg (fun g => g ≫ e.hom) hx'

/-- Compactness descends along a coproduct-preserving additive functor that is faithful on the
object in question. -/
theorem isCompactObject_of_map_injective
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (P : C) (hF : ∀ Y, Function.Injective (F.map : (P ⟶ Y) → _))
    [IsCompactObject.{w} (F.obj P)] : IsCompactObject.{w} P := by
  classical
  constructor
  intro J _ E _
  refine ⟨injective_directSumToHom _ _, ?_⟩
  intro f
  let ι (j : J) := F.map (Sigma.ι E j)
  have hc : IsColimit (Cofan.mk (F.obj (∐ E)) ι) :=
    (isColimitMapCoconeCofanMkEquiv F E (Sigma.ι E))
      (isColimitOfPreserves F (coproductIsCoproduct E))
  obtain ⟨s, a, ha⟩ := exists_sum_cofan_of_isCompactObject (F.obj P) ι hc (F.map f)
  let p (j : J) : (∐ E) ⟶ E j := Sigma.desc (Pi.single j (𝟙 (E j)))
  have hproj (j : J) (hj : j ∈ s) : F.map f ≫ F.map (p j) = a j := by
    rw [← ha, Preadditive.sum_comp]
    have hterm (i : J) : (a i ≫ ι i) ≫ F.map (p j) =
        if h : i = j then a j else 0 := by
      dsimp [ι, p]
      rw [Category.assoc, ← F.map_comp, Sigma.ι_desc]
      split_ifs with h
      · subst i; simp
      · rw [Pi.single_eq_of_ne h, F.map_zero, comp_zero]
    simp only [hterm]
    simp [hj]
  refine ⟨∑ j ∈ s, DirectSum.of _ j (f ≫ p j), ?_⟩
  apply hF _
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Functor.map_sum, Functor.map_comp, Category.assoc]
  calc
    ∑ j ∈ s, F.map f ≫ F.map (p j) ≫ F.map (Sigma.ι E j) =
        ∑ j ∈ s, a j ≫ ι j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Category.assoc, hproj j hj]
    _ = F.map f := ha

/-- Compactness is invariant under isomorphism, for an arbitrary PREADDITIVE category. Named
apart from `CategoryTheory.isCompactObject_of_iso`, which is the triangulated-category form and
takes the compactness of the source explicitly: both are in scope in files that open this
namespace, so a shared bare name would make their call sites ambiguous. -/
theorem isCompactObject_of_iso_of_preadditive
    {C : Type*} [Category C] [Preadditive C] {P Q : C}
    [IsCompactObject.{w} P] (e : P ≅ Q) : IsCompactObject.{w} Q := by
  classical
  constructor
  intro J _ E _
  refine ⟨injective_directSumToHom _ _, ?_⟩
  intro f
  obtain ⟨s, a, ha⟩ := exists_sum_cofan_of_isCompactObject P (Sigma.ι E)
    (coproductIsCoproduct E) (e.hom ≫ f)
  refine ⟨∑ j ∈ s, DirectSum.of _ j (e.inv ≫ a j), ?_⟩
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Category.assoc, ← Preadditive.comp_sum, ha,
    Iso.inv_hom_id_assoc]

/-- A compact object placed in a single degree gives a compact cochain complex: the evaluation
functor in that degree is faithful on maps out of it. -/
theorem isCompactObject_cochain_single
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasCoproducts.{w} C] (P : C) [IsCompactObject.{w} P] (n : ℤ) :
    IsCompactObject.{w} ((CochainComplex.singleFunctor C n).obj P) := by
  have : IsCompactObject.{w} (((CochainComplex.singleFunctor C n).obj P).X n) :=
    isCompactObject_of_iso_of_preadditive
      (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm
  have : IsCompactObject.{w} ((HomologicalComplex.eval C (.up ℤ) n).obj
      ((CochainComplex.singleFunctor C n).obj P)) := this
  exact isCompactObject_of_map_injective (HomologicalComplex.eval C (.up ℤ) n) _
    fun _ _ _ hfg => HomologicalComplex.from_single_hom_ext hfg

/-- Compactness is carried along a coproduct-preserving essentially surjective additive functor
that is full on the object in question. -/
theorem isCompactObject_map_of_map_surjective
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{w} C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.EssSurj]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (P : C) (hF : ∀ Y, Function.Surjective (F.map : (P ⟶ Y) → _))
    [IsCompactObject.{w} P] : IsCompactObject.{w} (F.obj P) := by
  classical
  constructor
  intro J _ E _
  refine ⟨injective_directSumToHom _ _, ?_⟩
  intro f
  let K (j : J) := F.objPreimage (E j)
  let e (j : J) : F.obj (K j) ≅ E j := F.objObjPreimageIso (E j)
  have hc : IsColimit (Cofan.mk (F.obj (∐ K)) (fun j => F.map (Sigma.ι K j))) :=
    (isColimitMapCoconeCofanMkEquiv F K (Sigma.ι K))
      (isColimitOfPreserves F (coproductIsCoproduct K))
  let ec : Cofan (fun j => F.obj (K j)) :=
    Cofan.mk (∐ E) (fun j => (e j).hom ≫ Sigma.ι E j)
  have hec : IsColimit ec :=
    (IsColimit.precomposeHomEquiv (Discrete.natIso
        (F := Discrete.functor (fun j => F.obj (K j)))
        (G := Discrete.functor E) (fun j => e j.as)) _).2
      (coproductIsCoproduct E)
  let t := hc.coconePointUniqueUpToIso hec
  have ht (j : J) : F.map (Sigma.ι K j) ≫ t.hom = (e j).hom ≫ Sigma.ι E j :=
    hc.comp_coconePointUniqueUpToIso_hom hec ⟨j⟩
  obtain ⟨g, hg⟩ := hF _ (f ≫ t.inv)
  obtain ⟨s, a, ha⟩ := exists_sum_cofan_of_isCompactObject P (Sigma.ι K)
    (coproductIsCoproduct K) g
  refine ⟨∑ j ∈ s, DirectSum.of _ j (F.map (a j) ≫ (e j).hom), ?_⟩
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Category.assoc]
  calc
    ∑ j ∈ s, F.map (a j) ≫ (e j).hom ≫ Sigma.ι E j =
        F.map (∑ j ∈ s, a j ≫ Sigma.ι K j) ≫ t.hom := by
      simp only [Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
        Category.assoc, ht]
    _ = f := by rw [ha, hg]; simp

/-- A projective compact object placed in a single degree is a compact object of the derived
category. -/
public theorem isCompactObject_derived_single
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [EnoughInjectives C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C] [HasCoproducts.{v} C]
    (P : C) [Projective P] [IsCompactObject.{v} P] (n : ℤ) :
    IsCompactObject.{v} ((DerivedCategory.singleFunctor C n).obj P) := by
  have := isKProjective_single P n
  have := isCompactObject_cochain_single P n
  have := fun J : Type v => preservesColimitsOfShape_discrete_Q (C := C) J
  exact isCompactObject_map_of_map_surjective DerivedCategory.Q _
    (fun Y => map_surjective_of_isKProjective _ Y)

/-! ### Transport of the triangulated envelope along a triangulated equivalence -/

/-- A triangulated functor carries the triangulated envelope of a single object into the
triangulated envelope of its image. -/
theorem triangEnvelope_map
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (P X : C)
    (h : (ObjectProperty.singleton P).triangEnvelope X) :
    (ObjectProperty.singleton (F.obj P)).triangEnvelope (F.obj X) := by
  let Q := (ObjectProperty.singleton (F.obj P)).triangEnvelope
  have : (Q.inverseImage F).IsStableUnderRetracts :=
    ⟨fun r h => Q.prop_of_retract (r.map F) h⟩
  have hle : (ObjectProperty.singleton P).triangEnvelope ≤ Q.inverseImage F :=
    (ObjectProperty.triangEnvelope_le_iff _).2 (ObjectProperty.singleton_le_iff.2
      (ObjectProperty.le_triangEnvelope _ _ (by simp)))
  exact hle X h

/-- Membership in the triangulated envelope of a single object is detected by a triangulated
equivalence. -/
theorem triangEnvelope_map_iff
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
    [e.inverse.CommShift ℤ] [e.inverse.IsTriangulated] (P X : C) :
    (ObjectProperty.singleton (e.functor.obj P)).triangEnvelope (e.functor.obj X) ↔
      (ObjectProperty.singleton P).triangEnvelope X := by
  refine ⟨fun h => ?_, triangEnvelope_map e.functor P X⟩
  have h' := triangEnvelope_map e.inverse _ _ h
  have hle : (ObjectProperty.singleton (e.inverse.obj (e.functor.obj P))).triangEnvelope ≤
      (ObjectProperty.singleton P).triangEnvelope :=
    (ObjectProperty.triangEnvelope_le_iff _).2 (ObjectProperty.singleton_le_iff.2
      (((ObjectProperty.singleton P).triangEnvelope).prop_of_iso (e.unitIso.app P)
        (ObjectProperty.le_triangEnvelope _ _ (by simp))))
  exact ((ObjectProperty.singleton P).triangEnvelope).prop_of_iso
    (e.unitIso.app X).symm (hle _ h')

/-- Isomorphic objects have the same triangulated envelope. -/
theorem triangEnvelope_singleton_eq_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {P Q : C} (e : P ≅ Q) :
    (ObjectProperty.singleton P).triangEnvelope =
      (ObjectProperty.singleton Q).triangEnvelope := by
  have h {P Q : C} (e : P ≅ Q) : (ObjectProperty.singleton P).triangEnvelope ≤
      (ObjectProperty.singleton Q).triangEnvelope :=
    (ObjectProperty.triangEnvelope_le_iff _).2 (ObjectProperty.singleton_le_iff.2
      (((ObjectProperty.singleton Q).triangEnvelope).prop_of_iso e.symm
        (ObjectProperty.le_triangEnvelope _ _ (by simp))))
  exact le_antisymm (h e) (h e.symm)

open ObjectProperty in
/-- If a compact weak generator of `D` corresponds under a triangulated equivalence `C ≌ D` to an
object `P` of `C`, then the triangulated envelope of `P` is the property of being compact. -/
theorem triangEnvelope_eq_isCompactObject_of_equivalence
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C]
    {D : Type*} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{v} D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
    [e.inverse.CommShift ℤ] [e.inverse.IsTriangulated]
    (P : C) (Q : D) (i : e.functor.obj P ≅ Q) [IsCompactObject.{v} Q]
    (hQ : (ObjectProperty.singleton Q).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton P).triangEnvelope = IsCompactObject.{v} := by
  have hD :=
    (isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      Q
      |>.mp hQ).1
  ext X
  rw [← triangEnvelope_map_iff e P X, triangEnvelope_singleton_eq_of_iso i, hD]
  constructor
  · intro h
    exact isCompactObject_of_map_injective e.functor X (fun _ => e.functor.map_injective)
  · intro h
    exact isCompactObject_map_of_map_surjective e.functor X
      (fun _ => e.functor.map_surjective)

/-! ### Comparing two localizations of the homotopy category

The compactness statement is about the small derived category, while the perfectness statement is
about Mathlib's standard one. The two are compared by the uniqueness of localizations, upgraded to
a triangulated equivalence commuting with the shift. -/

section ChangeLocalization

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

/-- The comparison equivalence between two derived categories of `C`, from the uniqueness of the
localization of the homotopy category at the acyclic objects. -/
public noncomputable abbrev derivedEquivalence :=
  Localization.uniq (@DerivedCategory.Qh C _ _ h₁) (@DerivedCategory.Qh C _ _ h₂)
    (HomotopyCategory.subcategoryAcyclic C).trW

/-- The comparison equivalence commutes with the shift. -/
@[instance_reducible]
public noncomputable def derivedEquivalenceCommShift :
    (derivedEquivalence h₁ h₂).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization (@DerivedCategory.Qh C _ _ h₁)
    (HomotopyCategory.subcategoryAcyclic C).trW ℤ (@DerivedCategory.Qh C _ _ h₂)
    (derivedEquivalence h₁ h₂).functor

attribute [local instance] derivedEquivalenceCommShift

/-- The comparison equivalence is triangulated, since it is a lift of a triangulated functor along
the localization. -/
public theorem derivedEquivalence_isTriangulated :
    letI : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₁) n).Additive :=
      by let := h₁; infer_instance
    letI : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₂) n).Additive :=
      by let := h₂; infer_instance
    (derivedEquivalence h₁ h₂).functor.IsTriangulated := by
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₁) n).Additive := by
    let := h₁
    infer_instance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory C _ _ h₂) n).Additive := by
    let := h₂
    infer_instance
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso (@DerivedCategory.Qh C _ _ h₁)
      (HomotopyCategory.subcategoryAcyclic C).trW (@DerivedCategory.Qh C _ _ h₂)
      (derivedEquivalence h₁ h₂).functor)

/-- The comparison equivalence identifies the two localization functors out of the category of
cochain complexes. -/
noncomputable def derivedEquivalenceCompQIso :
    @DerivedCategory.Q C _ _ h₁ ⋙ (derivedEquivalence h₁ h₂).functor ≅
      @DerivedCategory.Q C _ _ h₂ :=
  Functor.isoWhiskerRight (@DerivedCategory.quotientCompQhIso C _ _ h₁).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _) ≪≫
    @DerivedCategory.quotientCompQhIso C _ _ h₂

end ChangeLocalization

/-- The triangulated envelope of the regular module in degree zero is the property of being a
compact object: transport the statement for the small derived category, where `R[0]` is compact
and a weak generator, along the comparison equivalence. -/
theorem triangEnvelope_eq_isCompactObject_regularModule
    {R : Type u} [Ring R] :
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).triangEnvelope = IsCompactObject.{u} := by
  let h₁ := HasDerivedCategory.standard (ModuleCat.{u} R)
  let h₂ := (nonempty_smallDerivedCategory (C := ModuleCat.{u} R)).some
  let := h₂
  let e := derivedEquivalence h₁ h₂
  let P := (@DerivedCategory.singleFunctor (ModuleCat.{u} R) _ _ h₁ 0).obj (ModuleCat.of R R)
  let Q := (@DerivedCategory.singleFunctor (ModuleCat.{u} R) _ _ h₂ 0).obj (ModuleCat.of R R)
  have : ∀ n : ℤ,
      (shiftFunctor (@DerivedCategory (ModuleCat.{u} R) _ _ h₁) n).Additive := by
    let := h₁
    infer_instance
  have : ∀ n : ℤ,
      (shiftFunctor (@DerivedCategory (ModuleCat.{u} R) _ _ h₂) n).Additive := by
    infer_instance
  have : HasCoproducts.{u} (@DerivedCategory (ModuleCat.{u} R) _ _ h₁) := by
    let := h₁
    exact fun J => hasCoproductsOfShape_derivedCategory J
  have : HasCoproducts.{u} (@DerivedCategory (ModuleCat.{u} R) _ _ h₂) :=
    fun J => hasCoproductsOfShape_derivedCategory J
  let : e.functor.CommShift ℤ := derivedEquivalenceCommShift h₁ h₂
  have : e.functor.IsTriangulated := derivedEquivalence_isTriangulated h₁ h₂
  let := e.commShiftInverse ℤ
  have : e.CommShift ℤ := e.commShift_of_functor ℤ
  have : e.IsTriangulated := Equivalence.IsTriangulated.mk' e inferInstance
  have : IsCompactObject.{u} (ModuleCat.of R R) := isCompactObject_regularModule
  have : IsCompactObject.{u} Q := isCompactObject_derived_single _ 0
  have i : e.functor.obj P ≅ Q :=
    (derivedEquivalenceCompQIso h₁ h₂).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  exact triangEnvelope_eq_isCompactObject_of_equivalence e P Q i
    isWeakTriangulatedGenerator_regularModule

/-- **Stacks 07LT.** An object of the derived category of modules over a ring is perfect if and
only if it is compact. Perfectness is thus intrinsic to the triangulated category `D(R)` with its
coproducts, referring neither to a representing complex nor to the ring. -/
@[stacks 07LT]
theorem isPerfect_iff_isCompactObject
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{u} R)) :
    IsPerfect K ↔ IsCompactObject.{u} K := by
  rw [show (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) =
    IsCompactObject.{u} from isPerfect_eq_triangEnvelope_singleton_regularModule.trans
      triangEnvelope_eq_isCompactObject_regularModule]

end Compactness

end StacksDraft.Perfect
