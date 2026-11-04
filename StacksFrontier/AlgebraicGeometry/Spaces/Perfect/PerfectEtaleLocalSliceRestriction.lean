module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartCoversTop
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongACocontinuousFunctor

/-!
# Perfectness on an algebraic space is local for the étale topology, through slice restriction

Let `S` be a scheme and `X` an algebraic space over `S`.  Perfect objects of `D(𝒪_X)`, in the
sense of Stacks 08G5 on the small étale ringed site, behave as the source uses them throughout
Derived Categories of Spaces:

* the restriction of a perfect object along an étale morphism `f : U ⟶ X` is perfect;
* an object whose restrictions to the members of an étale covering `{U_i ⟶ X}` are perfect is
  perfect; in particular perfectness may be checked on the two members of an elementary
  distinguished square, which is the form in which Stacks 08HK, 09IV and 08HB use it.

The source treats both as evident ("being perfect is local on `X_étale`").  The library's
statement of the local nature of perfectness, `AlgebraicGeometry.RingedSite.isPerfect_of_locally`,
is stated for a `RingedSite.{u, u, 0}` and does not reach the small étale ringed site of an
algebraic space, which is a `RingedSite.{u + 1, u, u}`; the general-universe forms used here are
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_isCocontinuous_of_sliceFunctors` and
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_isPerfect_mapDerivedCategory`.

The comparison between a slice of the small étale site of `U` at a chart `V` and the slice of
the small étale site of `X` at the composite chart is the slice form of Stacks 04M0,
`AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence`.  Restriction of modules
along it matches the structure sheaves and commutes with restriction to slices on the nose, so
the squares the transfer principles ask for are identities.

## Main results

* `AlgebraicGeometry.Space.etaleSliceRestrictionEquivalence`: restriction of modules along the
  slice form of Stacks 04M0 is an equivalence (restriction along an étale morphism preserving
  perfectness is `AlgebraicGeometry.Space.isPerfect_etaleModulePullback_standard`).
* `AlgebraicGeometry.Space.isPerfect_of_isEtaleCovering`: perfectness descends along an étale
  covering.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_eds`: perfectness may be checked on the two
  members of an elementary distinguished square.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Slice

variable {X Y : AlgebraicSpaces B S hS}

/-- Restriction of modules from the slice of the small étale site of `Y` at the composite chart
`f ∘ V` to the slice of the small étale site of `X` at the chart `V`, along the slice form of
Stacks 04M0.  The structure sheaves agree on the nose, so no change of scalars occurs. -/
abbrev etaleSliceRestriction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over V) :=
  SheafOfModules.pushforward
    (F := (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor) (𝟙 _)

/-- The restriction of modules along the slice form of Stacks 04M0 is an equivalence: it is the
reindexing of modules along an equivalence of sites. -/
def etaleSliceRestrictionEquivalence (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) ≌
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over V) :=
  Stacks.SheafOfModules.reindexEquivalence (J' := (smallEtaleRingedSite B S hS X.1 X.2).J.over V)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))

/-- The functor of `AlgebraicGeometry.Space.etaleSliceRestrictionEquivalence` is
`AlgebraicGeometry.Space.etaleSliceRestriction`. -/
theorem etaleSliceRestrictionEquivalence_functor (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleSliceRestrictionEquivalence B S hS f hf V).functor =
      etaleSliceRestriction B S hS f hf V := rfl

/-- The slice restriction `AlgebraicGeometry.Space.etaleSliceRestriction` is additive. -/
instance etaleSliceRestriction_additive (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleSliceRestriction B S hS f hf V).Additive :=
  inferInstanceAs (SheafOfModules.pushforward
    (F := (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor) (𝟙 _)).Additive

/-- The slice restriction `AlgebraicGeometry.Space.etaleSliceRestriction` is an equivalence. -/
instance etaleSliceRestriction_isEquivalence (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleSliceRestriction B S hS f hf V).IsEquivalence :=
  inferInstanceAs (etaleSliceRestrictionEquivalence B S hS f hf V).functor.IsEquivalence

/-- The slice restriction `AlgebraicGeometry.Space.etaleSliceRestriction` preserves finite
limits. -/
instance etaleSliceRestriction_preservesFiniteLimits (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteLimits (etaleSliceRestriction B S hS f hf V) :=
  inferInstance

/-- The slice restriction `AlgebraicGeometry.Space.etaleSliceRestriction` preserves finite
colimits. -/
instance etaleSliceRestriction_preservesFiniteColimits (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteColimits (etaleSliceRestriction B S hS f hf V) :=
  inferInstance

/-- The inverse of the slice restriction. -/
abbrev etaleSliceExtension (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :=
  (etaleSliceRestrictionEquivalence B S hS f hf V).inverse

/-- The inverse `AlgebraicGeometry.Space.etaleSliceExtension` of the slice restriction is
additive. -/
instance etaleSliceExtension_additive (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleSliceExtension B S hS f hf V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restricting an `𝒪_Y`-module to the slice at `f ∘ V` and then along the slice comparison is
restricting its étale pullback to the slice at `V`; the two are equal. -/
def etaleSliceRestrictionSquare (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V) ⋙
      etaleSliceRestriction B S hS f hf V ≅
      etaleModulePullback.{u, u} B S hS f hf ⋙
        SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V :=
  Iso.refl _

/-- The slice restriction carries the unit to the unit, on the nose. -/
def etaleSliceRestrictionUnitIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleSliceRestriction B S hS f hf V).obj (SheafOfModules.unit _) ≅
      SheafOfModules.unit _ :=
  Iso.refl _

end Slice

/-! ### Restriction along an étale morphism -/

/-- Postcomposition with an étale morphism is cocontinuous for the topologies of the small étale
ringed sites. -/
instance smallEtaleRingedSitePostcomp_isCocontinuous {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtaleRingedSitePostcomp B S hS f hf).IsCocontinuous
      (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallEtalePostcomp_isCocontinuous B S hS f hf

/-! ### Descent along an étale covering -/

section Descent

variable {I : Type} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- **Perfectness descends along an étale covering.**  Let `{f_i : U_i ⟶ X}` be an étale covering
of an algebraic space `X` and `E` an object of `D(𝒪_X)`.  If every restriction `E|_{U_i}` is
perfect, then `E` is perfect. -/
theorem isPerfect_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (f i) (hcov.etale i)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  have : ∀ i, (smallEtaleRingedSitePostcomp B S hS (f i) (hcov.etale i)).IsContinuous
      (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).J (smallEtaleRingedSite B S hS X.1 X.2).J :=
    fun i => smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS (f i) (hcov.etale i)
  refine RingedSite.isPerfect_of_forall_isPerfect_mapDerivedCategory
    (Y := fun i => smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2)
    (fun i => smallEtaleRingedSitePostcomp B S hS (f i) (hcov.etale i))
    (fun i => etaleModulePullback.{u, u} B S hS (f i) (hcov.etale i))
    (fun i W => etaleSliceExtension B S hS (f i) (hcov.etale i) W)
    (coversTop_of_isEtaleCovering B S hS Yi f hcov)
    (fun i W => (etaleSliceExtension B S hS (f i) (hcov.etale i) W).mapIso
        (etaleSliceRestrictionUnitIso B S hS (f i) (hcov.etale i) W).symm ≪≫
      ((etaleSliceRestrictionEquivalence B S hS (f i) (hcov.etale i) W).unitIso.app _).symm)
    (fun i W => (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (etaleSliceRestrictionSquare B S hS (f i) (hcov.etale i) W).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (etaleSliceRestrictionEquivalence B S hS (f i) (hcov.etale i) W).unitIso.symm ≪≫
      Functor.rightUnitor _)
    E hE

end Descent

/-! ### The two members of an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The two members of an elementary distinguished square, the open subspace and the étale
algebraic space, indexed by `Bool`. -/
abbrev edsCoveringMember : Bool → AlgebraicSpaces B S hS
  | false => edsOpen B S hS hsq
  | true => edsEtale B S hS hsq

/-- The morphisms of the two members of an elementary distinguished square to its target. -/
abbrev edsCoveringMemberHom : ∀ b : Bool, edsCoveringMember B S hS hsq b ⟶ W
  | false => edsOpenHom B S hS hsq
  | true => edsEtaleHom B S hS hsq

/-- **The open subspace and the étale space of an elementary distinguished square form an étale
covering of the target**: every point lies on the open subspace or, lying on its reduced closed
complement over which the étale morphism is an isomorphism, lifts along the étale morphism. -/
theorem isEtaleCovering_edsCoveringMember :
    IsEtaleCovering B S hS (fun b => (edsCoveringMember B S hS hsq b).1)
      (fun b => (edsCoveringMemberHom B S hS hsq b).hom) := by
  classical
  refine ⟨W.2, fun b => (edsCoveringMember B S hS hsq b).2, ?_, ?_⟩
  · intro b
    cases b
    · exact isEtale_edsOpenHom B S hS hsq
    · exact isEtale_edsEtaleHom B S hS hsq
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    by_cases hx : x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
    · obtain ⟨z, hz⟩ := hx
      exact Set.mem_iUnion.mpr ⟨false, ⟨z, hz⟩⟩
    · let D := reducedClosedSubspace B S hS W.1 W.2
        (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ hsq.isClosedComplement
      have hxD : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) := by
        rw [range_pointsMap_ι_reducedClosedSubspace]
        exact hx
      have hy : ∃ y : points B S hS V, pointsMap B S hS V fV y = x := by
        obtain ⟨z, rfl⟩ := hxD
        have : IsIso (D.fromPreimage fV) := hsq.isIsoOverComplement
        obtain ⟨p, hp⟩ := pointsMap_surjective_of_isIso B S hS (D.fromPreimage fV) z
        refine ⟨pointsMap B S hS (D.preimage fV).toFunctor (D.preimage fV).ι p, ?_⟩
        rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hp]
      exact Set.mem_iUnion.mpr ⟨true, hy⟩

/-- **Perfectness may be checked on the two members of an elementary distinguished square.**
If `(U ⊆ X, j : V ⟶ X)` is an elementary distinguished square and `E` is an object of `D(𝒪_X)`
with `E|_U` and `E|_V` perfect, then `E` is perfect. -/
theorem isPerfect_of_isPerfect_eds (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))
    (hV : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect E :=
  isPerfect_of_isEtaleCovering B S hS (edsCoveringMember B S hS hsq)
    (edsCoveringMemberHom B S hS hsq)
    (isEtaleCovering_edsCoveringMember B S hS hsq) E fun b => by
      cases b
      · exact hU
      · exact hV

end Square

end AlgebraicGeometry.Space

end
