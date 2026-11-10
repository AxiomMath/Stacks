module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MonoToZeroDimensionalLocalSpectra
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Reduced algebraic spaces with one point

An algebraic space over a scheme `S` is reduced with exactly one point exactly when it admits
a surjective flat morphism from the spectrum of a field, and such a cover may always be chosen
locally of finite type.  Adding local Noetherianity on one side matches local finite
presentation of the cover on the other, and a reduced locally Noetherian singleton space is
regular.

Reducedness, local Noetherianity and regularity of an algebraic space are the étale-local
scheme properties of Stacks 03E6, and "exactly one point" says that the point set of
Stacks 03BU is nonempty and a subsingleton.

Such a space, monomorphically over an algebraic space `X` and carried by a single point `x` of
`|X|`, is a *residual space* of `X` at `x`. For a locally Noetherian `X` the point `x` is
closed in `|X|` exactly when a residual space at `x` is a closed subspace of `X`, and then it
is the reduced closed subspace of `X` on `{x}`.

A space carrying a flat, surjective, locally finitely presented cover by a field spectrum
admits no proper nonempty subobjects: a monomorphism into it is either empty or an
isomorphism. The same dichotomy for a monomorphism into a field spectrum itself is the input
for that statement.

## Main definitions

* `AlgebraicGeometry.Space.HasFlatFieldCover`: there is a surjective flat morphism to the space
  from an object of the site whose underlying scheme is the spectrum of a field.
* `AlgebraicGeometry.Space.HasLocallyOfFiniteTypeFlatFieldCover`: such a cover which is
  moreover locally of finite type.
* `AlgebraicGeometry.Space.HasLocallyOfFinitePresentationFlatFieldCover`: such a cover which is
  moreover locally of finite presentation.
* `AlgebraicGeometry.Space.IsResidualSpaceAt`: a monomorphism exhibiting its source as a
  residual space of an algebraic space at a point of its point set, Stacks 06R0.

## Main results

* `AlgebraicGeometry.Space.isReduced_and_singleton_points_iff_hasFlatFieldCover` and
  `AlgebraicGeometry.Space.hasFlatFieldCover_iff_hasLocallyOfFiniteTypeFlatFieldCover` are the
  three equivalent conditions of Stacks 06QW.
* `AlgebraicGeometry.Space.isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover`
  is Stacks 06QX.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_isReduced_of_isLocallyNoetherian`
  is Stacks 06R1: a reduced locally Noetherian singleton algebraic space is regular.
* `AlgebraicGeometry.Space.isEmpty_points_or_isIso_of_mono_to_fieldSpectrum` is Stacks 06MG: a
  monomorphism of algebraic spaces into the spectrum of a field is either empty or an
  isomorphism.
* `AlgebraicGeometry.Space.isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover` is
  Stacks 06QY: a monomorphism into an algebraic space with a flat, surjective, locally finitely
  presented cover by a field spectrum is either empty or an isomorphism.
* `AlgebraicGeometry.Space.isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt` is
  Stacks 0H1U: a point of a locally Noetherian algebraic space is closed exactly when its
  residual space is a closed subspace.
  `AlgebraicGeometry.Space.isClosed_singleton_iff_exists_isResidualSpaceAt_isClosedImmersion`
  is the same equivalence phrased through the existence of such a residual space, and
  `AlgebraicGeometry.Space.isResidualSpaceAt_ι_reducedClosedSubspace` identifies the residual
  space at a closed point with the reduced closed subspace on that point.

## Implementation notes

A field spectrum over the base is presented as an object of the chosen big fppf site whose
underlying scheme is isomorphic to the spectrum of a field, rather than as that spectrum
itself; the site is only prescribed up to its size cutoff, so the two differ.

A residual space is described by a predicate on a monomorphism `f : Z ⟶ X` rather than by a
subobject of `X`, matching the formulation of Stacks 06QZ; the point `x` it sits over is
recorded by asking that every point of `|Z|` map to `x`, which together with nonemptiness and
subsingletonness of `|Z|` says that the image of `|Z| → |X|` is `{x}`.

Stacks 06QZ — that a residual space at a point exists and is unique up to isomorphism over
`X` — is not available here. Existence at a *closed* point is proved along the way, as the
reduced closed subspace on that point. Uniqueness is not, and the implication of Stacks 0H1U
that produces a closed immersion out of a closed point consumes it: it is what identifies an
arbitrary residual space at `x` with that reduced closed subspace. It is therefore carried as
the hypothesis `huniq` of
`AlgebraicGeometry.Space.isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt`, and
avoided altogether in
`AlgebraicGeometry.Space.isClosed_singleton_iff_exists_isResidualSpaceAt_isClosedImmersion`.

Emptiness of an algebraic space is expressed as emptiness of its point set of Stacks 03BU, and
the conclusion "`Z' = Z`" of Stacks 06QY as the given monomorphism `Z' ⟶ Z` being an
isomorphism, which is the statement that survives without choosing a subobject of `Z`.

## References

* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 06QW](https://stacks.math.columbia.edu/tag/06QW)
* [Stacks Project, Tag 06QX](https://stacks.math.columbia.edu/tag/06QX)
* [Stacks Project, Tag 06QY](https://stacks.math.columbia.edu/tag/06QY)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 06R1](https://stacks.math.columbia.edu/tag/06R1)
* [Stacks Project, Tag 0H1U](https://stacks.math.columbia.edu/tag/0H1U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Shortcut instance: instance search for products of presheaves on the big fppf site times
out in Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_reducedSingleton
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-! ### Flat field covers -/

/-- There is a surjective flat morphism to `F` from an object of the site whose underlying
scheme is the spectrum of a field. -/
abbrev HasFlatFieldCover (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (T : BigFppfOver B S hS) (k : Type u) (hk : Field k),
    letI : Field k := hk
    Nonempty (((BigFppfOver.toScheme B S hS).obj T) ≅ Spec (.of k)) ∧
      ∃ f : yoneda.obj T ⟶ F, IsSurjective B S hS f ∧ IsFlat B S hS f

/-- A surjective flat field-spectrum cover which is locally of finite type. -/
abbrev HasLocallyOfFiniteTypeFlatFieldCover (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (T : BigFppfOver B S hS) (k : Type u) (hk : Field k),
    letI : Field k := hk
    Nonempty (((BigFppfOver.toScheme B S hS).obj T) ≅ Spec (.of k)) ∧
      ∃ f : yoneda.obj T ⟶ F, IsLocallyOfFiniteType B S hS f ∧
        IsSurjective B S hS f ∧ IsFlat B S hS f

/-- A surjective flat field-spectrum cover which is locally of finite presentation. -/
abbrev HasLocallyOfFinitePresentationFlatFieldCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (T : BigFppfOver B S hS) (k : Type u) (hk : Field k),
    letI : Field k := hk
    Nonempty (((BigFppfOver.toScheme B S hS).obj T) ≅ Spec (.of k)) ∧
      ∃ f : yoneda.obj T ⟶ F, IsLocallyOfFinitePresentation B S hS f ∧
        IsSurjective B S hS f ∧ IsFlat B S hS f

/-! ### Auxiliary scheme-level facts -/

private theorem flat_fromSpecResidueField_of_isField_stalk
    {X : Scheme.{u}} (x : X) (hx : IsField (X.presheaf.stalk x)) :
    Flat (X.fromSpecResidueField x) := by
  rw [Flat.iff_flat_stalkMap]
  intro y
  have hy : (X.fromSpecResidueField x) y = x :=
    Scheme.fromSpecResidueField_apply x y
  exact RingHom.Flat.of_isField (hy.symm ▸ hx) _

private theorem residueFieldMap_locallyOfFiniteType_of_isClosed_singleton
    {X Y : Scheme.{u}} (f : Y ⟶ X) [_root_.AlgebraicGeometry.IsOpenImmersion f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    LocallyOfFiniteType (X.fromSpecResidueField (f y)) := by
  let ρ := Spec.map (f.residueFieldMap y)
  have : IsIso ρ := by dsimp [ρ]; infer_instance
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Y.fromSpecResidueField y) :=
    (isClosed_singleton_iff_isClosedImmersion).mp hy
  have hcomp : LocallyOfFiniteType (ρ ≫ X.fromSpecResidueField (f y)) := by
    rw [f.SpecMap_residueFieldMap_fromSpecResidueField y]
    infer_instance
  simpa using (inferInstance : LocallyOfFiniteType (inv ρ ≫ ρ ≫ X.fromSpecResidueField (f y)))

private theorem isReduced_of_etale_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : Etale f) :
    IsReduced X := by
  obtain ⟨I, K, hK, _hAlg, _hFinite, _hSeparable, e, _he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp hf
  let : ∀ i, Field (K i) := hK
  have hsum : IsReduced (∐ fun i : I => Spec (.of (K i))) := by
    let 𝒰 := sigmaOpenCover (fun i : I => Spec (.of (K i)))
    have hcomp : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
      intro i
      let : Field (K i) := hK i
      change IsReduced (Spec (.of (K i)))
      infer_instance
    exact IsReduced.of_openCover _ 𝒰
  have : IsReduced (∐ fun i : I => Spec (.of (K i))) := hsum
  exact isReduced_of_isOpenImmersion e.hom

/-! ### Transferring properties between the site and its presheaves -/

/-- An identity morphism of a represented presheaf has every relative morphism property coming
from a scheme property that holds for isomorphisms. -/
private theorem presheaf_inverseImage_id (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso f → P f)
    (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro a b g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact hP _ (Functor.map_isIso (BigFppfOver.toScheme B S hS) snd)

/-- A morphism of the site whose underlying morphism of schemes has an étale-local
multiplicative property has that property on every étale chart. -/
private theorem holdsOnEveryEtaleChart_yonedaMap (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] (hP : IsEtaleLocalOnSourceAndTarget P)
    (hiso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso f → P f)
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : P ((BigFppfOver.toScheme B S hS).map f)) :
    HoldsOnEveryEtaleChart B S hS P (yoneda.map f) := by
  rw [holdsOnEveryEtaleChart_iff_representable B S hS P hP]
  let l := yoneda.preimage (yoneda.obj U).reprW.hom
  let r := yoneda.preimage (yoneda.obj V).reprW.inv
  have hcomp : yoneda.preimage ((yoneda.obj U).reprW.hom ≫ yoneda.map f ≫
      (yoneda.obj V).reprW.inv) = l ≫ f ≫ r := by
    apply yoneda.map_injective
    simp [l, r]
  have : IsIso l := by
    have : IsIso (yoneda.map l) := by
      simpa [l] using (inferInstance : IsIso ((yoneda.obj U).reprW.hom))
    exact Yoneda.fullyFaithful.isIso_of_isIso_map _
  have : IsIso r := by
    have : IsIso (yoneda.map r) := by
      simpa [r] using (inferInstance : IsIso ((yoneda.obj V).reprW.inv))
    exact Yoneda.fullyFaithful.isIso_of_isIso_map _
  rw [hcomp]
  simpa only [Functor.map_comp, Category.assoc] using
    P.comp_mem _ _ (P.comp_mem _ _ (hiso _ inferInstance) hf) (hiso _ inferInstance)

private theorem isFlat_yonedaMap {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : Flat ((BigFppfOver.toScheme B S hS).map f)) :
    IsFlat B S hS (yoneda.map f) :=
  holdsOnEveryEtaleChart_yonedaMap B S hS @Flat Flat.isEtaleLocalOnSourceAndTarget
    (fun _ hf => have := hf; inferInstance) f hf

private theorem isLocallyOfFiniteType_yonedaMap {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f)) :
    IsLocallyOfFiniteType B S hS (yoneda.map f) :=
  holdsOnEveryEtaleChart_yonedaMap B S hS @LocallyOfFiniteType
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (fun _ hf => have := hf; inferInstance) f hf

/-! ### The equivalent conditions -/

/-- A morphism of the site whose underlying morphism of schemes is étale is étale on every
étale chart, as a morphism of presheaves. -/
private theorem presheaf_etale_yonedaMap {U V : BigFppfOver B S hS} (s : U ⟶ V)
    (hs : Etale ((BigFppfOver.toScheme B S hS).map s)) :
    (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map s) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)) :=
    ⟨fun hpb hf =>
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
        (hpb.map (BigFppfOver.toScheme B S hS)) hf⟩
  exact MorphismProperty.relative_map hs

/-- A morphism from an object of the site to an algebraic space which is surjective on étale
charts is surjective on points. -/
private theorem pointsMap_surjective_of_isSurjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F}
    (ha : (MorphismProperty.inverseImage (@Surjective.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      a) :
    Function.Surjective (pointsMap B S hS (yoneda.obj U) a) := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact (surjective_iff_pointsMap_surjective B S hS (isAlgebraicSpace_yoneda B S hS U) hF a
    (hF.diagonal_representable.of_diag a)).mp ha

/-- If an algebraic space has at most one point, then a morphism to it from an object of the site
is surjective as soon as the source carries a field-valued point. -/
private theorem isSurjective_of_subsingleton_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hsub : Subsingleton (points B S hS F))
    {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ F)
    (pt : FieldValuedPoint B S hS (yoneda.obj T)) : IsSurjective B S hS g := fun _ =>
  ⟨pt.class B S hS (yoneda.obj T), hsub.elim _ _⟩

/-- **Stacks 06QW**, conditions (1) and (2).  A reduced algebraic space over `S` has exactly
one point if and only if it admits a surjective flat morphism from the spectrum of a field. -/
@[stacks 06QW "conditions (1) and (2)"]
theorem isReduced_and_singleton_points_iff_hasFlatFieldCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X) ∧
      Nonempty (points B S hS F) ∧ Subsingleton (points B S hS F)) ↔
        HasFlatFieldCover B S hS F := by
  constructor
  · rintro ⟨hred, hnonempty, hsub⟩
    obtain ⟨U, a, haSurj, haEtale⟩ := hF.exists_atlas
    let W := (BigFppfOver.toScheme B S hS).obj U
    have hredW : IsReduced W :=
      (exists_atlas_iff_forall_etale B S hS F (fun X : Scheme.{u} => IsReduced X) hF).mp
        hred U a haEtale
    obtain ⟨z⟩ := hnonempty
    obtain ⟨q, -⟩ := pointsMap_surjective_of_isSurjective B S hS hF haSurj z
    obtain ⟨qrep⟩ := Quot.exists_rep q
    let x₀ : W :=
      (BigFppfOver.toScheme B S hS).map qrep.value (IsLocalRing.closedPoint qrep.carrier)
    let c : {s : Set W // s ∈ irreducibleComponents W} :=
      ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
    let x : W := genericPoints.ofComponent c
    have hxcomp : closure ({x} : Set W) ∈ irreducibleComponents W := by
      rw [(genericPoints.isGenericPoint_ofComponent c).def]
      exact c.property
    have : IsReduced W := hredW
    have hxfield : IsField (W.presheaf.stalk x) :=
      isField_stalk_of_closure_mem_irreducibleComponents W x hxcomp
    let hk : B.Contains (Spec (W.residueField x)) :=
      B.residueField_spec_contains U.left.property x
    let i : B.obj hk ⟶ U.left :=
      B.inclusion.preimage (X := B.obj hk) (Y := U.left) (W.fromSpecResidueField x)
    let T : BigFppfOver B S hS := Over.mk (i ≫ U.hom)
    let α : T ⟶ U := Over.homMk i
    let g : yoneda.obj T ⟶ F := yoneda.map α ≫ a
    have hαflatScheme : Flat ((BigFppfOver.toScheme B S hS).map α) := by
      change Flat (B.inclusion.map i)
      rw [B.inclusion.map_preimage]
      exact flat_fromSpecResidueField_of_isField_stalk x hxfield
    have haflat : IsFlat B S hS a :=
      isFlat_of_isEtale B S hS (isEtale_of_presheafEtale B S hS a haEtale)
    have hgflat : IsFlat B S hS g :=
      isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS T)
        (isAlgebraicSpace_yoneda B S hS U) hF (yoneda.map α) a
        (isFlat_yonedaMap B S hS α hαflatScheme) haflat
    let pt : FieldValuedPoint B S hS (yoneda.obj T) :=
      { carrier := W.residueField x
        field := inferInstance
        contained := hk
        toBase := B.inclusion.map (i ≫ U.hom)
        value := 𝟙 T }
    exact ⟨T, W.residueField x, inferInstance, ⟨Iso.refl _⟩, g,
      isSurjective_of_subsingleton_points B S hS hsub g pt, hgflat⟩
  · rintro ⟨T, k, hk, ⟨e⟩, f, hsurj, hflat⟩
    let : Field k := hk
    let q := BigFppfOver.toScheme B S hS
    have : HasBinaryProducts (BigFppfOver B S hS) :=
      hasBinaryProducts_of_hasTerminal_and_pullbacks _
    let hrep : yoneda.relativelyRepresentable f := hF.diagonal_representable.of_diag f
    have hsurjRel : (MorphismProperty.inverseImage (@Surjective.{u}) q).presheaf f :=
      (surjective_iff_pointsMap_surjective B S hS (isAlgebraicSpace_yoneda B S hS T) hF f
        hrep).mpr hsurj
    have hred : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X) := by
      refine (exists_atlas_iff_forall_etale B S hS F
        (fun X : Scheme.{u} => IsReduced X) hF).mpr ?_
      intro V g hg
      let W := hrep.pullback g
      let i : W ⟶ T := hrep.fst' g
      let j : W ⟶ V := hrep.snd g
      have hpb : IsPullback (yoneda.map i) (yoneda.map j) f g := hrep.isPullback' g
      have hiEtale : Etale (q.map i) := hg.property f (yoneda.map j) i hpb.flip
      have hiEtalePresheaf := presheaf_etale_yonedaMap B S hS i hiEtale
      have : IsReduced (q.obj W) := by
        refine isReduced_of_etale_over_field (q.map i ≫ e.hom) ?_
        have : Etale (q.map i) := hiEtale
        infer_instance
      have : Flat (q.map j) := hflat W V (yoneda.map i) g j hiEtalePresheaf hg hpb.w.symm
      have : Surjective (q.map j) := hsurjRel.property g (yoneda.map i) j hpb
      exact _root_.AlgebraicGeometry.isReduced_of_flat_of_surjective (q.map j)
    have : Subsingleton (Spec (.of k)) := inferInstance
    have hTsub : Subsingleton (q.obj T) := ⟨fun x y => by
      simpa using congrArg e.inv (Subsingleton.elim (e.hom x) (e.hom y))⟩
    refine ⟨hred, ⟨pointsMap B S hS (yoneda.obj T) f
      ((schemePointRepresentative B S hS T (e.inv (IsLocalRing.closedPoint k))).class B S hS
        (yoneda.obj T))⟩, ?_⟩
    have := (pointsEquivScheme B S hS T).subsingleton
    exact hsurj.subsingleton

/-- **Stacks 06QW**, conditions (2) and (3).  A surjective flat morphism to an algebraic space
over `S` from the spectrum of a field may be replaced by one that is in addition locally of
finite type. -/
@[stacks 06QW "conditions (2) and (3)"]
theorem hasFlatFieldCover_iff_hasLocallyOfFiniteTypeFlatFieldCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasFlatFieldCover B S hS F ↔ HasLocallyOfFiniteTypeFlatFieldCover B S hS F := by
  constructor
  · intro hcover
    have hpointsSub : Subsingleton (points B S hS F) :=
      ((isReduced_and_singleton_points_iff_hasFlatFieldCover B S hS F hF).2 hcover).2.2
    rcases hcover with ⟨T₀, k₀, hk₀, ⟨e₀⟩, f₀, hsurj₀, hflat₀⟩
    let : Field k₀ := hk₀
    have hk₀' : B.Contains (Spec (.of k₀)) := by
      change (Spec (.of k₀)).size < B.cutoff
      rw [← Scheme.size_congr e₀]
      exact T₀.left.property
    obtain ⟨U, a, haSurj, haEtale⟩ := hF.exists_atlas
    obtain ⟨qpoint, -⟩ := pointsMap_surjective_of_isSurjective B S hS hF haSurj
      (pointsMap B S hS (yoneda.obj T₀) f₀
        ((schemePointRepresentative B S hS T₀ (e₀.inv (IsLocalRing.closedPoint k₀))).class B S hS
          (yoneda.obj T₀)))
    obtain ⟨p, -⟩ := Quot.exists_rep qpoint
    let X := (BigFppfOver.toScheme B S hS).obj U
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (schemePoint B S hS U p)) isOpen_univ
    let W := X.restrict V.isOpenEmbedding
    have : IsAffine W := by
      change IsAffine (V : X.Opens)
      exact hVaff
    let R := Γ(W, ⊤)
    have : Nontrivial R :=
      PrimeSpectrum.nontrivial (W.isoSpec.hom ⟨schemePoint B S hS U p, hxV⟩)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    let y : Spec R := ⟨m, hm.isPrime⟩
    have hy : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hm
    let fX : Spec R ⟶ X := W.isoSpec.inv ≫ X.ofRestrict V.isOpenEmbedding
    have : _root_.AlgebraicGeometry.IsOpenImmersion fX := inferInstance
    let k := X.residueField (fX y)
    let hk : B.Contains (Spec (X.residueField (fX y))) :=
      B.residueField_spec_contains U.left.property (fX y)
    let i : B.obj hk ⟶ U.left :=
      B.inclusion.preimage (X := B.obj hk) (Y := U.left) (X.fromSpecResidueField (fX y))
    let T : BigFppfOver B S hS := Over.mk (i ≫ U.hom)
    let α : T ⟶ U := Over.homMk i
    let g : yoneda.obj T ⟶ F := yoneda.map α ≫ a
    have hαlftScheme : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) := by
      change LocallyOfFiniteType (B.inclusion.map i)
      rw [B.inclusion.map_preimage]
      exact residueFieldMap_locallyOfFiniteType_of_isClosed_singleton fX y hy
    have haEtale' := isEtale_of_presheafEtale B S hS a haEtale
    have hgLft : IsLocallyOfFiniteType B S hS g :=
      isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS T)
        (isAlgebraicSpace_yoneda B S hS U) hF (yoneda.map α) a
        (isLocallyOfFiniteType_yonedaMap B S hS α hαlftScheme)
        (isLocallyOfFiniteType_of_isEtale B S hS hF haEtale')
    let i₀ : B.obj hk₀' ⟶ T₀.left :=
      B.inclusion.preimage (X := B.obj hk₀') (Y := T₀.left) e₀.inv
    let T₀' : BigFppfOver B S hS := Over.mk (i₀ ≫ T₀.hom)
    let α₀ : T₀' ⟶ T₀ := Over.homMk i₀
    let f₀' : yoneda.obj T₀' ⟶ F := yoneda.map α₀ ≫ f₀
    let b₀ : Spec (.of k₀) ⟶ S := B.inclusion.map (i₀ ≫ T₀.hom)
    let b : Spec (.of k) ⟶ S := B.inclusion.map (i ≫ U.hom)
    have hα₀flatScheme : Flat ((BigFppfOver.toScheme B S hS).map α₀) := by
      change Flat (B.inclusion.map i₀)
      rw [B.inclusion.map_preimage]
      infer_instance
    have hf₀'flat : IsFlat B S hS f₀' :=
      isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS T₀')
        (isAlgebraicSpace_yoneda B S hS T₀) hF (yoneda.map α₀) f₀
        (isFlat_yonedaMap B S hS α₀ hα₀flatScheme) hflat₀
    let pt₀ : FieldValuedPoint B S hS (yoneda.obj T₀') :=
      { carrier := k₀, field := inferInstance, contained := hk₀', toBase := b₀,
        value := 𝟙 T₀' }
    let pt : FieldValuedPoint B S hS (yoneda.obj T) :=
      { carrier := k, field := inferInstance, contained := hk, toBase := b, value := 𝟙 T }
    have hf₀'surj := isSurjective_of_subsingleton_points B S hS hpointsSub f₀' pt₀
    have hgsurj := isSurjective_of_subsingleton_points B S hS hpointsSub g pt
    exact ⟨T, k, inferInstance, ⟨Iso.refl _⟩, g, hgLft, hgsurj,
      isFlat_of_fieldCover B S hS F hF k₀ hk₀' b₀ f₀' hf₀'surj hf₀'flat k hk b g⟩
  · rintro ⟨T, k, hk, hT, f, -, hsurj, hflat⟩
    exact ⟨T, k, hk, hT, f, hsurj, hflat⟩

/-- Local Noetherianity of an algebraic space over `S` follows from a flat, surjective,
locally finitely presented cover by a locally Noetherian object of the site. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_of_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : BigFppfOver B S hS)
    (hT : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
    (f : yoneda.obj T ⟶ F) (hflat : IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X) := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine (exists_atlas_iff_forall_etale B S hS F
    (fun X : Scheme.{u} => IsLocallyNoetherian X) hF).mpr ?_
  intro V g hg
  have hgr : yoneda.relativelyRepresentable g := hF.diagonal_representable.of_diag g
  let W := hgr.pullback f
  let p := hgr.fst f
  let s : W ⟶ T := hgr.snd f
  have hpull := hgr.isPullback f
  let r : W ⟶ V := yoneda.preimage p
  have hr : yoneda.map r = p := yoneda.map_preimage p
  have hsquare : yoneda.map r ≫ g = yoneda.map s ≫ f := by simpa [hr] using hpull.w
  have hsEtale : Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hg.property f p s (by simpa [hr] using hpull)
  have hW : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) := by
    have : Etale ((BigFppfOver.toScheme B S hS).map s) := hsEtale
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) := hT
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map s)
  have hsEtaleChart := presheaf_etale_yonedaMap B S hS s hsEtale
  have hrflat : Flat ((BigFppfOver.toScheme B S hS).map r) :=
    hflat W V (yoneda.map s) g r hsEtaleChart hg hsquare
  have hrlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map r) :=
    hlfp W V (yoneda.map s) g r hsEtaleChart hg hsquare
  have hrsurj : Surjective ((BigFppfOver.toScheme B S hS).map r) :=
    ((surjective_iff_surjective_pointsMap B S hS F hF T f).mpr hsurj).property g
      (yoneda.map s) r (by simpa [hr] using hpull.flip)
  have hcover : Presieve.ofArrows (fun _ : Unit => (BigFppfOver.toScheme B S hS).obj W)
      (fun _ => (BigFppfOver.toScheme B S hS).map r) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun _ => ⟨hrflat, hrlfp⟩⟩
    have : Surjective ((BigFppfOver.toScheme B S hS).map r) := hrsurj
    exact ⟨(), ((BigFppfOver.toScheme B S hS).map r).surjective x⟩
  refine ObjectProperty.of_presieve (P := fun X : Scheme.{u} => IsLocallyNoetherian X)
    hcover ?_
  rintro Y f ⟨i⟩
  cases i
  simpa using hW

/-- **Stacks 06QX.** A reduced, locally Noetherian algebraic space over `S` has exactly one
point if and only if it admits a flat, surjective, locally finitely presented morphism from the
spectrum of a field. -/
@[stacks 06QX]
theorem isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X) ∧
      HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X) ∧
      Nonempty (points B S hS F) ∧ Subsingleton (points B S hS F)) ↔
    HasLocallyOfFinitePresentationFlatFieldCover B S hS F := by
  constructor
  · rintro ⟨hred, hnoeth, hnonempty, hsub⟩
    obtain ⟨T, k, hk, e, f, hft, hsurj, hflat⟩ :=
      (hasFlatFieldCover_iff_hasLocallyOfFiniteTypeFlatFieldCover B S hS F hF).mp
        ((isReduced_and_singleton_points_iff_hasFlatFieldCover B S hS F hF).mp
          ⟨hred, hnonempty, hsub⟩)
    let : Field k := hk
    exact ⟨T, k, hk, e, f, isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS
      (isAlgebraicSpace_yoneda B S hS T) hF f hnoeth hft, hsurj, hflat⟩
  · rintro ⟨T, k, hk, e, f, hlfp, hsurj, hflat⟩
    let : Field k := hk
    have hredsingle := (isReduced_and_singleton_points_iff_hasFlatFieldCover B S hS F hF).mpr
      ⟨T, k, hk, e, f, hsurj, hflat⟩
    have hT : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) := by
      obtain ⟨e⟩ := e
      exact ObjectProperty.prop_of_iso (fun X : Scheme.{u} => IsLocallyNoetherian X) e.symm
        (by infer_instance)
    exact ⟨hredsingle.1, hasEtaleLocalProperty_isLocallyNoetherian_of_cover B S hS F hF T hT f
      hflat hsurj hlfp, hredsingle.2.1, hredsingle.2.2⟩

/-- **Stacks 06R1.** A reduced, locally Noetherian algebraic space over `S` with exactly one
point is regular. -/
@[stacks 06R1]
theorem hasEtaleLocalProperty_isRegular_of_isReduced_of_isLocallyNoetherian
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X))
    (hnoeth : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X))
    (hnonempty : Nonempty (points B S hS F)) (hsub : Subsingleton (points B S hS F)) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsRegular X) := by
  obtain ⟨T, k, hk, ⟨e⟩, f, hlfp, hsurj, hflat⟩ :=
    (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B S hS F hF).mp
      ⟨hred, hnoeth, hnonempty, hsub⟩
  let : Field k := hk
  refine hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    B S hS (isAlgebraicSpace_yoneda B S hS T) hF f hlfp hflat hsurj ?_
  refine ⟨T, 𝟙 _, presheaf_inverseImage_id B S hS @Surjective
    (fun _ hf => have := hf; inferInstance) T,
    presheaf_inverseImage_id B S hS @Etale (fun _ hf => have := hf; inferInstance) T, ?_⟩
  exact ObjectProperty.prop_of_iso (fun X : Scheme.{u} => IsRegular X) e.symm
    (fun _ => ⟨⟨⊤, isAffineOpen_top _⟩, by trivial, IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv⟩)

/-! ### Monomorphisms into a space covered by a field -/

/-- **Stacks 06MG.** A monomorphism of algebraic spaces over `S` whose target is the spectrum
of a field is either empty or an isomorphism. -/
theorem isEmpty_points_or_isIso_of_mono_to_fieldSpectrum
    {k : Type u} [Field k] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj T) [Mono f] :
    IsEmpty (points B S hS F) ∨ IsIso f := by
  classical
  have hrepF : F.IsRepresentable :=
    isRepresentable_of_mono_to_coproduct_spec_zeroDimensional B S hS hF f T (Iso.refl _)
      PUnit (fun _ => CommRingCat.of k) (fun _ => inferInstance)
      (fun _ => ringKrullDim_eq_zero_of_field k)
      (e.trans (coproductUniqueIso (fun _ : PUnit => Spec (CommRingCat.of k))).symm)
  obtain ⟨V, hV⟩ := hrepF.has_representation
  let ε : yoneda.obj V ≅ F := Functor.representableByEquiv (Classical.choice hV)
  let g : V ⟶ T := yoneda.preimage (ε.hom ≫ f)
  have hg : yoneda.map g = ε.hom ≫ f := yoneda.map_preimage _
  have : Mono ε.hom := IsIso.mono_of_iso _
  have hεf : Mono (ε.hom ≫ f) := mono_comp _ _
  have : Mono (yoneda.map g) := by rw [hg]; exact hεf
  have : Mono g := yoneda.mono_of_mono_map inferInstance
  have : Mono ((BigFppfOver.toScheme B S hS).map g) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) g
  rcases isEmpty_or_nonempty ((BigFppfOver.toScheme B S hS).obj V) with hV₀ | hV₁
  · have : IsEmpty (points B S hS (yoneda.obj V)) := (pointsEquivScheme B S hS V).isEmpty
    exact Or.inl (Function.isEmpty (pointsMap B S hS F ε.inv))
  · right
    have : Nonempty ((BigFppfOver.toScheme B S hS).obj V) := hV₁
    have : IsIso ((BigFppfOver.toScheme B S hS).map g ≫ e.hom) :=
      AlgebraicGeometry.isIso_of_mono_to_spec_field ((BigFppfOver.toScheme B S hS).map g ≫ e.hom)
    have : IsIso ((BigFppfOver.toScheme B S hS).map g) := IsIso.of_isIso_comp_right _ e.hom
    have : (BigFppfOver.toScheme B S hS).ReflectsIsomorphisms := inferInstance
    have : IsIso g := isIso_of_reflects_iso g (BigFppfOver.toScheme B S hS)
    have : IsIso (yoneda.map g) := Functor.map_isIso yoneda g
    have : IsIso (ε.hom ≫ f) := by rw [← hg]; infer_instance
    exact IsIso.of_isIso_comp_left ε.hom f

/-- A surjective, flat, locally finitely presented morphism to an algebraic space over `S` from
an object of the site is locally surjective for the fppf topology. -/
private theorem isLocallySurjective_of_fppfFieldCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (T : BigFppfOver B S hS) (p : yoneda.obj T ⟶ F)
    (hsurj : IsSurjective B S hS p) (hflat : IsFlat B S hS p)
    (hlfp : IsLocallyOfFinitePresentation B S hS p) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p := by
  have hrep : yoneda.relativelyRepresentable p := hF.diagonal_representable.of_diag p
  have hs' := (presheafSurjective_iff_isSurjective B S hS
    (isAlgebraicSpace_yoneda B S hS T) hF p hrep).mpr hsurj
  have hf' := (isFlat_iff_presheaf B S hS (isAlgebraicSpace_yoneda B S hS T) hF hrep).mp hflat
  have hl' := (isLocallyOfFinitePresentation_iff_presheaf B S hS
    (isAlgebraicSpace_yoneda B S hS T) hF hrep).mp hlfp
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (F := ⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩)
    (G := ⟨F, hF.isSheaf⟩) (ObjectProperty.homMk p)
    ⟨hrep, fun _ _ h fst snd hsq =>
      ⟨hf'.2 h fst snd hsq, hl'.2 h fst snd hsq, hs'.2 h fst snd hsq⟩⟩

/-- **Stacks 06QY.** Let `f : Z' ⟶ Z` be a monomorphism of algebraic spaces over `S`, and
suppose `Z` admits a surjective, flat, locally finitely presented morphism from the spectrum of
a field. Then either `Z'` is empty or `f` is an isomorphism. -/
@[stacks 06QY]
theorem isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover
    {Z' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : IsAlgebraicSpace B S hS Z') (hZ : IsAlgebraicSpace B S hS Z) (f : Z' ⟶ Z) [Mono f]
    (hcover : HasLocallyOfFinitePresentationFlatFieldCover B S hS Z) :
    IsEmpty (points B S hS Z') ∨ IsIso f := by
  classical
  obtain ⟨T, k, hk, ⟨e⟩, p, hlfp, hsurj, hflat⟩ := hcover
  let _ : Field k := hk
  rcases isEmpty_or_nonempty (points B S hS Z') with h₀ | h₁
  · exact Or.inl h₀
  right
  obtain ⟨z'⟩ := h₁
  have hW : IsAlgebraicSpace B S hS (Limits.pullback f p) :=
    isAlgebraicSpace_pullback B S hS f p hZ' (isAlgebraicSpace_yoneda B S hS T) hZ
  have hsq : IsPullback (Limits.pullback.fst f p) (Limits.pullback.snd f p) f p :=
    IsPullback.of_hasPullback f p
  obtain ⟨t, ht⟩ := hsurj (pointsMap B S hS Z' f z')
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS hsq z' t ht.symm
  have : IsIso (Limits.pullback.snd f p) := by
    rcases isEmpty_points_or_isIso_of_mono_to_fieldSpectrum B S hS T e hW
      (Limits.pullback.snd f p) with hempty | hiso
    · exact (hempty.false w).elim
    · exact hiso
  have hfac : (inv (Limits.pullback.snd f p) ≫ Limits.pullback.fst f p) ≫ f = p := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p :=
    isLocallySurjective_of_fppfFieldCover B S hS hZ T p hsurj hflat hlfp
  have hfsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  have hfinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) f :=
    Presheaf.isLocallyInjective_of_injective _ f fun U =>
      (mono_iff_injective (f.app U)).mp ((NatTrans.mono_iff_mono_app f).mp inferInstance U)
  let fSh : (⟨Z', hZ'.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      (⟨Z, hZ.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    ObjectProperty.homMk f
  have : IsIso fSh := (Sheaf.isLocallyBijective_iff_isIso fSh).mp ⟨hfinj, hfsurj⟩
  exact Functor.map_isIso (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) fSh

/-! ### Residual spaces -/

attribute [local instance] pointTopology

/-- **Stacks 06R0.** A monomorphism `f : Z ⟶ X` of algebraic spaces over `S` exhibits `Z` as
a *residual space* of `X` at a point `x` of `|X|` when `Z` is reduced and locally Noetherian,
`|Z|` consists of exactly one point, and that point maps to `x`. Reducedness and local
Noetherianity are the étale-local scheme properties of Stacks 03E6. -/
@[stacks 06R0]
def IsResidualSpaceAt (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (x : points B S hS X)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Z ⟶ X) : Prop :=
  IsAlgebraicSpace B S hS Z ∧ Mono f ∧
    HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsReduced T) ∧
    HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
    Nonempty (points B S hS Z) ∧ Subsingleton (points B S hS Z) ∧
    ∀ z : points B S hS Z, pointsMap B S hS Z f z = x

variable {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image on points of a residual space of `X` at `x` is the singleton `{x}`. -/
theorem range_pointsMap_of_isResidualSpaceAt {x : points B S hS X} (f : Z ⟶ X)
    (hf : IsResidualSpaceAt B S hS X x f) :
    Set.range (pointsMap B S hS Z f) = {x} := by
  obtain ⟨-, -, -, -, ⟨z₀⟩, -, hsupp⟩ := hf
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ hsupp z, fun hy => ⟨z₀, (hsupp z₀).trans hy.symm⟩⟩

/-- **Stacks 0H1U**, the implication that needs no local Noetherianity: if a residual space of
`X` at `x` is a closed subspace of `X`, then `x` is a closed point of `|X|`. -/
theorem isClosed_singleton_of_isClosedImmersion_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) (f : Z ⟶ X)
    (hf : IsResidualSpaceAt B S hS X x f) (hcl : IsClosedImmersion B S hS f) :
    _root_.IsClosed ({x} : Set (points B S hS X)) := by
  rw [← range_pointsMap_of_isResidualSpaceAt B S hS f hf]
  exact isClosed_range_pointsMap_of_isClosedImmersion B S hS hX f hcl

/-- **The residual space at a closed point of a locally Noetherian algebraic space exists**,
and is the reduced closed subspace of Stacks 03IQ on that point. -/
theorem isResidualSpaceAt_ι_reducedClosedSubspace (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hx : _root_.IsClosed ({x} : Set (points B S hS X))) :
    IsResidualSpaceAt B S hS X x (reducedClosedSubspace B S hS X hX {x} hx).ι := by
  set W := reducedClosedSubspace B S hS X hX {x} hx
  have halg : IsAlgebraicSpace B S hS W.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X hX {x} hx
  have himm : IsImmersion B S hS W.ι :=
    isImmersion_of_isClosedImmersion B S hS
      (isClosedImmersion_ι_reducedClosedSubspace B S hS hX {x} hx)
  have hrange : Set.range (pointsMap B S hS W.toFunctor W.ι) = {x} :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX {x} hx
  have hsupp : ∀ z : points B S hS W.toFunctor, pointsMap B S hS W.toFunctor W.ι z = x := by
    intro z
    have hz : pointsMap B S hS W.toFunctor W.ι z ∈
        Set.range (pointsMap B S hS W.toFunctor W.ι) := ⟨z, rfl⟩
    rw [hrange] at hz
    simpa using hz
  refine ⟨halg, inferInstance,
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX {x} hx,
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS halg hX W.ι
      (isLocallyOfFiniteType_of_isImmersion B S hS W.ι himm) hN, ?_, ?_, hsupp⟩
  · have hmem : x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by rw [hrange]; rfl
    obtain ⟨z₀, -⟩ := hmem
    exact ⟨z₀⟩
  · exact ⟨fun a b => (isEmbedding_pointsMap_of_isImmersion B S hS hX W.ι himm).injective
      ((hsupp a).trans (hsupp b).symm)⟩

/-- **Stacks Project, Tag 0H1U.** Let `S` be a scheme, let `X` be an algebraic space over `S`
which is locally Noetherian, let `x` be a point of `|X|`, and let `f : Z ⟶ X` be a residual
space of `X` at `x`. Then `x` is a closed point of `|X|` if and only if `f` is a closed
immersion. The hypothesis `huniq` is the uniqueness part of Stacks 06QZ: every residual space
of `X` at `x` is isomorphic to `f` over `X`. -/
@[stacks 0H1U]
theorem isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (f : Z ⟶ X) (hf : IsResidualSpaceAt B S hS X x f)
    (huniq : ∀ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : W ⟶ X),
      IsResidualSpaceAt B S hS X x g → ∃ e : W ≅ Z, e.hom ≫ f = g) :
    _root_.IsClosed ({x} : Set (points B S hS X)) ↔ IsClosedImmersion B S hS f := by
  refine ⟨fun hx => ?_, isClosed_singleton_of_isClosedImmersion_of_isResidualSpaceAt
    B S hS hX x f hf⟩
  obtain ⟨e, he⟩ := huniq _ (reducedClosedSubspace B S hS X hX {x} hx).ι
    (isResidualSpaceAt_ι_reducedClosedSubspace B S hS hX hN x hx)
  have hfeq : f = e.inv ≫ (reducedClosedSubspace B S hS X hX {x} hx).ι := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hfeq]
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.inv _
    (isClosedImmersion_ι_reducedClosedSubspace B S hS hX {x} hx)

/-- **Stacks Project, Tag 0H1U**, phrased so as not to refer to the uniqueness of the residual
space: a point `x` of the point set of a locally Noetherian algebraic space `X` over `S` is
closed exactly when some residual space of `X` at `x` is a closed subspace of `X`. -/
@[stacks 0H1U "the equivalence through the existence of a residual space"]
theorem isClosed_singleton_iff_exists_isResidualSpaceAt_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) :
    _root_.IsClosed ({x} : Set (points B S hS X)) ↔
      ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : Y ⟶ X),
        IsResidualSpaceAt B S hS X x f ∧ IsClosedImmersion B S hS f := by
  refine ⟨fun hx => ⟨_, (reducedClosedSubspace B S hS X hX {x} hx).ι,
    isResidualSpaceAt_ι_reducedClosedSubspace B S hS hX hN x hx,
    isClosedImmersion_ι_reducedClosedSubspace B S hS hX {x} hx⟩, ?_⟩
  rintro ⟨Y, f, hf, hcl⟩
  exact isClosed_singleton_of_isClosedImmersion_of_isResidualSpaceAt B S hS hX x f hf hcl

end AlgebraicGeometry.Space

end
