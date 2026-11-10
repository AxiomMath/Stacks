module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleRelativeBoxMapIso
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.Devissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.IsoOfHighTriangles
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexPushforwardLocal
public import
    StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FiniteTorDimensionOfAPerfectObject
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Nondegeneracy.DeRhamNotIsZero
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence

/-!
# The relative box map for a bounded and a bounded below complex

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes and let
`𝓕^•`, `𝓖^•` be complexes of quasi-coherent modules with differentials differential operators of
finite order on `X/S` and on `Y/S`. This file proves that the relative map
`Ra_*𝓕^• ⊗^𝐋 Rb_*𝓖^• ⟶ Rf_*Tot(𝓕^• ⊠ 𝓖^•)` of
`Stacks.Cohomology.BoxKunnethFlat.relativeBoxMap` is an isomorphism when `𝓕^•` is bounded, `𝓖^•`
is bounded below, all terms are flat over `S` and `S` is quasi-compact, following the proof of
[Stacks, Tag 0FLT].

The bounded case is the dévissage of
`Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_of_finite`
from the single complexes of `Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_single`. For
`𝓖^•` bounded below the brutal truncation `σ_{≥N}𝓖^• ⟶ 𝓖^• ⟶ σ_{≤N-1}𝓖^•` is a distinguished
triangle of the homotopy category, the map is invertible at the bounded `σ_{≤N-1}𝓖^•`, and both
sides at `σ_{≥N}𝓖^•` vanish in low degrees: the target because `Rf_*` keeps lower bounds, the
source because `Ra_*𝓕^•` has finite Tor dimension by [Stacks, Tag 0FML] (3) on the quasi-compact
`S`. `Stacks.DerivedCategoryTruncation.isIso_app_of_triangles_isGE` concludes.

The file also records the quasi-coherence of the cohomology of `Ra_*𝓕^•` and `Rb_*𝓖^•` that the
global cup product on an affine base needs: [Stacks, Tag 0FML] (2) for the bounded `𝓕^•`, and for
the bounded below `𝓖^•` the same with a truncation, since `Rb_*` of `σ_{≥N}𝓖^•` vanishes below `N`.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_of_finite_of_isFlatOver`: the bounded
  case.
* `Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_of_isStrictlyGE`: the bounded below case.
* `Stacks.Cohomology.BoxKunnethFlat.isQuasicoherent_homology_leftComplex` and
  `Stacks.Cohomology.BoxKunnethFlat.isQuasicoherent_homology_rightComplex`: quasi-coherence.

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.BoxKunneth
open scoped CategoryTheory.Prod

universe u w₁ w₂

namespace Stacks.Cohomology.BoxKunnethFlat

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### Terms of a brutal truncation -/

/-- A property of the terms of a complex which holds at every zero object holds at every term of
a brutal truncation of it: such a term is a term of the complex or a zero object. -/
theorem prop_stupidTrunc_X {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] (P : ι' → C → Prop)
    (hz : ∀ i' M, IsZero M → P i' M) (h : ∀ n, P n (K.X n)) (i' : ι') :
    P i' ((K.stupidTrunc e).X i') := by
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi
    have hX : (K.stupidTrunc e).X (e.f i) = K.X (e.f i) := by
      change HomologicalComplex.extend.X (K.restriction e) (e.r (e.f i)) = _
      rw [e.r_f]
      rfl
    rw [hX]
    exact h _
  · exact hz _ _ (K.isZero_stupidTrunc_X e i' fun i hi' => hi ⟨i, hi'⟩)

/-- The brutal truncation `σ_{≤N}` of a complex vanishing below `n₀` has finitely many nonzero
terms. -/
theorem finite_support_stupidTruncLE {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (L : CochainComplex C ℤ) (n₀ N : ℤ) [L.IsStrictlyGE n₀] :
    {j : ℤ | ¬ IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE N)).X j)}.Finite := by
  refine (Set.finite_Icc n₀ N).subset fun j hj => ⟨?_, ?_⟩
  · by_contra h
    exact hj (prop_stupidTrunc_X L (ComplexShape.embeddingUpIntLE N)
      (fun j M => j < n₀ → IsZero M) (fun _ _ hM _ => hM)
      (fun k hk => L.isZero_of_isStrictlyGE n₀ k hk) j (by omega))
  · by_contra h
    exact hj (CochainComplex.isZero_of_isStrictlyLE
      (L.stupidTrunc (ComplexShape.embeddingUpIntLE N)) N j (by omega))

/-- The total complex of a bifunctor at two complexes vanishing below `m` and below `n` vanishes
below `m + n`. -/
theorem isStrictlyGE_mapBifunctor_of_isStrictlyGE {C₁ C₂ D : Type*} [Category C₁] [Category C₂]
    [Category D] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [HasZeroObject C₁]
    [HasZeroObject C₂] [HasZeroObject D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] (m n : ℤ)
    [K₁.IsStrictlyGE m] [K₂.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE
      (HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)) (m + n) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero ((F.obj (K₁.X p)).obj (K₂.X q)) := by
    by_cases hp : p < m
    · exact (F.map_isZero (K₁.isZero_of_isStrictlyGE m p hp)).obj _
    · exact (F.obj (K₁.X p)).map_isZero
        (K₂.isZero_of_isStrictlyGE n q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- An additive functor keeps a lower bound on the terms of a complex. -/
theorem isStrictlyGE_mapHomologicalComplex {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- The derived direct image along a morphism of ringed spaces keeps a lower bound. -/
theorem isGE_derivedPushforward_ringedSpace {Z W : RingedSpace.{u, u}} (g : Z ⟶ W)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing Z))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing W))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) (c : ℤ) (hE : E.IsGE c) :
    ((derivedPushforward g).obj E).IsGE c :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward g) (derivedPushforward g)
    (derivedPushforwardUnit g) (isIso_derivedPushforwardUnit_app_of_isKInjective g) E c hE

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The derived direct image `Rb_*` of a complex vanishing below `N` vanishes below `N`. -/
theorem isGE_derivedPushforward_rightComplex
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (N : ℤ)
    [L.IsStrictlyGE N] :
    ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
      (DerivedCategory.Q.obj (rightComplex b L))).IsGE N := by
  have := isStrictlyGE_mapHomologicalComplex (toInverseImageModules b) L N
  have h : (DerivedCategory.Q.obj (rightComplex b L)).IsGE N := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact isGE_derivedPushforward_ringedSpace (inverseImageBaseProjection b) _ N h

/-! ### The bounded case -/

/-- **The relative map at two bounded complexes**, the terms of the second flat over `S`. -/
theorem isIso_relativeBoxMap_of_finite_of_isFlatOver [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b]
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (hL : {j : ℤ | ¬ IsZero (L.X j)}.Finite)
    (hLflat : ∀ n, IsFlatOver b.toLRSHom.toShHom (L.X n).module) :
    IsIso (relativeBoxMap a b K L) :=
  isIso_relativeBoxMap_of_finite a b (fun _ => True)
    (fun G => IsFlatOver b.toLRSHom.toShHom G.module)
    (fun i j F G _ hG => isIso_relativeBoxMap_single a b F G i j hG) K (fun _ => trivial) hK
    L hLflat hL

/-! ### Lower bounds -/

/-- A bounded complex of differential operators, read as a complex of `a⁻¹𝒪_S`-modules, is
locally bounded. -/
theorem isLocallyBounded_leftComplex
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) :
    Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K) := by
  intro _
  refine ⟨⊤, trivial, hK.toFinset, fun i hi => ?_⟩
  have h : IsZero (K.X i) := by simpa using hi
  exact Functor.map_isZero _ ((toInverseImageModules a).map_isZero h)

/-- **`Ra_*𝓕^•` has Tor amplitude bounded below**, for `𝓕^•` bounded with terms flat over a
quasi-compact `S`: [Stacks, Tag 0FML] (3) and the quasi-compactness of `S`. -/
theorem exists_hasTorAmplitudeGE_leftComplex [QuasiCompact a] [QuasiSeparated a]
    [CompactSpace S]
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hKflat : ∀ n, IsFlatOver a.toLRSHom.toShHom (K.X n).module) :
    ∃ c : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE S.toRingedSpace
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K))) c := by
  have h3 :=
      RelativeComplexPushforward.locallyHasFiniteTorDimension_derivedPushforward_relativeComplex
    a (leftComplex a K) (isLocallyBounded_leftComplex a K hK)
    (fun i => Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver a (K.X i).module (hKflat i))
    (fun i => (K.X i).module) (fun i => inferInstance) (fun i => Iso.refl _)
  have : CompactSpace S.toRingedSpace.carrier := inferInstanceAs (CompactSpace S)
  obtain ⟨c, d, h⟩ :=
    Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_locallyHasFiniteTorDimension
      S.toRingedSpace _ h3
  exact ⟨c, Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude
    S.toRingedSpace _ c d h⟩

/-- The underlying module of a zero object of differential operators is a zero module. -/
theorem isZero_module_of_isZero {Z : Scheme.{u}} {g : Z ⟶ S}
    {G : FiniteOrderDifferentialOperatorCategory g} (hG : IsZero G) : IsZero G.module := by
  by_contra h
  exact FiniteOrderDifferentialOperatorCategory.not_isZero_of_not_isZero_module h hG

/-- Every term of a brutal truncation of a complex with terms flat over `S` is flat over `S`. -/
theorem isFlatOver_stupidTrunc_X {Z : Scheme.{u}} {g : Z ⟶ S}
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory g) ℤ)
    (hL : ∀ n, IsFlatOver g.toLRSHom.toShHom (L.X n).module) {ι : Type*} {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] (n : ℤ) :
    IsFlatOver g.toLRSHom.toShHom ((L.stupidTrunc e).X n).module :=
  prop_stupidTrunc_X L e (fun _ M => IsFlatOver g.toLRSHom.toShHom M.module)
    (fun _ M hM => isFlatOver_of_isZero g M.module (isZero_module_of_isZero hM)) hL n

/-! ### The bounded below case -/

/-- A lower bound transfers along an isomorphism and weakens to any smaller bound. -/
private theorem isGE_of_iso_of_isGE_of_le {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {E E' : DerivedCategory C} (e : E ≅ E') {p q : ℤ}
    (h : DerivedCategory.TStructure.t.IsGE E' p) (hpq : q ≤ p) :
    DerivedCategory.TStructure.t.IsGE E q :=
  have := DerivedCategory.TStructure.t.isGE_of_ge E' q p hpq
  DerivedCategory.TStructure.t.isGE_of_iso e.symm q

/-- **The relative map for a bounded and a bounded below complex** with terms flat over a
quasi-compact `S`: the brutal truncation `σ_{≥N}𝓖^• ⟶ 𝓖^• ⟶ σ_{≤N-1}𝓖^•`, the bounded case at
`σ_{≤N-1}𝓖^•`, and lower bounds at `σ_{≥N}𝓖^•` from the Tor amplitude of `Ra_*𝓕^•` and the
lower bound of `𝓕^•`. -/
theorem isIso_relativeBoxMap_of_isStrictlyGE [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b] [CompactSpace S]
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (m : ℤ) [K.IsStrictlyGE m]
    (hKflat : ∀ n, IsFlatOver a.toLRSHom.toShHom (K.X n).module)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (n₀ : ℤ)
    [L.IsStrictlyGE n₀] (hLflat : ∀ n, IsFlatOver b.toLRSHom.toShHom (L.X n).module) :
    IsIso (relativeBoxMap a b K L) := by
  obtain ⟨c, hc⟩ := exists_hasTorAmplitudeGE_leftComplex a K hK hKflat
  let := sourceRightCommShift a b K
  let := targetRightCommShift a b K
  have := sourceRight_isTriangulated a b K
  have := targetRight_isTriangulated a b K
  rw [← isIso_relativeBoxMapRight_app_iff]
  refine Stacks.DerivedCategoryTruncation.isIso_app_of_triangles_isGE (sourceRight a b K)
    (targetRight a b K) (relativeBoxMapRight a b K) _ (fun n => ?_)
  obtain ⟨N, hNc, hNm⟩ : ∃ N : ℤ, n + 2 ≤ c + N ∧ n + 2 ≤ m + N :=
    ⟨max (n + 2 - c) (n + 2 - m), by omega, by omega⟩
  let S' := StacksDraft.StupidTruncation.stupidTruncGELEShortComplex L N
  let σ := StacksDraft.StupidTruncation.stupidTruncGELESplitting L N
  let Y' := L.stupidTrunc (ComplexShape.embeddingUpIntGE N)
  let Z' := L.stupidTrunc (ComplexShape.embeddingUpIntLE (N - 1))
  refine ⟨(HomotopyCategory.quotient _ _).obj Y', (HomotopyCategory.quotient _ _).obj Z',
    (HomotopyCategory.quotient _ _).map S'.f, (HomotopyCategory.quotient _ _).map S'.g,
    (CochainComplex.trianglehOfDegreewiseSplit S' σ).mor₃,
    CochainComplex.trianglehOfDegreewiseSplit_distinguished S' σ, ?_, ?_, ?_⟩
  · exact (isIso_relativeBoxMapRight_app_iff a b K Z').2
      (isIso_relativeBoxMap_of_finite_of_isFlatOver a b K hK Z'
        (finite_support_stupidTruncLE L n₀ (N - 1)) (isFlatOver_stupidTrunc_X L hLflat _))
  · have h₂ := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE
      (Stacks.Cohomology.TorAmplitude.derTensorSite S.toRingedSpace) _ _ c N hc
      (isGE_derivedPushforward_rightComplex b Y' N)
    exact isGE_of_iso_of_isGE_of_le ((sourceRightIso a b K).app Y') h₂ hNc
  · have h₁ : (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K Y'
        (boxProductRelativeCurried a b) (ComplexShape.up ℤ))).IsGE (m + N) := by
      have := isStrictlyGE_mapBifunctor_of_isStrictlyGE (boxProductRelativeCurried a b) K Y' m N
      rw [DerivedCategory.isGE_Q_obj_iff]
      infer_instance
    exact isGE_of_iso_of_isGE_of_le ((targetRightIso a b K).app Y')
      (isGE_derivedPushforward_ringedSpace
        (inverseImageBaseProjection (pullback.fst a b ≫ a)) _ (m + N) h₁) hNm

/-! ### Quasi-coherence of the two direct images -/

/-- **The cohomology sheaves of `Ra_*𝓕^•` are quasi-coherent** for a bounded `𝓕^•`:
[Stacks, Tag 0FML] (2). The same statement read at `b` is the one for `Rb_*𝓖^•`. -/
theorem isQuasicoherent_homology_leftComplex [QuasiCompact a] [QuasiSeparated a]
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).IsQuasicoherent :=
  Stacks.RelativeComplexPushforward.derivedCategoryB_derivedPushforward_relativeComplex a
    (leftComplex a K) (isLocallyBounded_leftComplex a K hK) (fun i => (K.X i).module)
    (fun _ => inferInstance) (fun _ => Iso.refl _) j

/-- The direct image `Rb_*` of complexes of differential operators, as a functor on the homotopy
category. -/
abbrev rightPushforward :
    HomotopyCategory (FiniteOrderDifferentialOperatorCategory b) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (toInverseImageModules b).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)

/-- `rightPushforward` at the class of a complex. -/
def rightPushforwardQuotientIso
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    (rightPushforward b).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) ≅
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L)) :=
  (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).mapIso
    (DerivedCategory.Qh.mapIso
      (((toInverseImageModules b).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app L) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _)

/-- **The cohomology sheaves of `Rb_*𝓖^•` are quasi-coherent** for a bounded below `𝓖^•`: in a
degree `j` they are those of `Rb_*σ_{≤j+1}𝓖^•`, because `Rb_*σ_{≥j+2}𝓖^•` vanishes below `j + 2`,
and [Stacks, Tag 0FML] (2) applies to the bounded `σ_{≤j+1}𝓖^•`. -/
theorem isQuasicoherent_homology_rightComplex_of_isStrictlyGE [QuasiCompact b] [QuasiSeparated b]
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (n₀ : ℤ)
    [L.IsStrictlyGE n₀] (j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L)))).IsQuasicoherent := by
  let : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection b)).rightAdjointCommShift ℤ
  let : (derivedAdjunction (inverseImageBaseProjection b)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection b)).commShift_of_leftAdjoint ℤ
  have : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).IsTriangulated :=
    (derivedAdjunction (inverseImageBaseProjection b)).isTriangulated_rightAdjoint
  let : (DerivedCategory.Qh ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let : (rightPushforward b).CommShift ℤ := Functor.CommShift.comp _ _
  have : (rightPushforward b).IsTriangulated := inferInstance
  let N := j + 2
  let S' := StacksDraft.StupidTruncation.stupidTruncGELEShortComplex L N
  let σ := StacksDraft.StupidTruncation.stupidTruncGELESplitting L N
  let Y' := L.stupidTrunc (ComplexShape.embeddingUpIntGE N)
  let Z' := L.stupidTrunc (ComplexShape.embeddingUpIntLE (N - 1))
  have hT := (rightPushforward b).map_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished S' σ)
  have hY : ((rightPushforward b).obj ((HomotopyCategory.quotient _ _).obj Y')).IsGE N := by
    have := isGE_derivedPushforward_rightComplex b Y' N
    exact DerivedCategory.TStructure.t.isGE_of_iso (rightPushforwardQuotientIso b Y').symm N
  have hiso := Stacks.DerivedCategoryTruncation.isIso_homologyMap_mor₂_of_isZero _ hT j
    ((DerivedCategory.isGE_iff _ _).1 hY j (by omega))
    ((DerivedCategory.isGE_iff _ _).1 hY (j + 1) (by omega))
  have hZ := isQuasicoherent_homology_leftComplex b Z'
    (finite_support_stupidTruncLE L n₀ (N - 1)) j
  exact (_root_.SheafOfModules.isQuasicoherent _).prop_of_iso
    ((DerivedCategory.homologyFunctor _ j).mapIso (rightPushforwardQuotientIso b L).symm ≪≫
      @asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ j).map
        ((rightPushforward b).mapTriangle.obj
          (CochainComplex.trianglehOfDegreewiseSplit S' σ)).mor₂) hiso ≪≫
      (DerivedCategory.homologyFunctor _ j).mapIso (rightPushforwardQuotientIso b Z')).symm hZ

end Stacks.Cohomology.BoxKunnethFlat

end
