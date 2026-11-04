module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Precomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The largest open subspace of the target over which a morphism has a local property

Let `S` be a scheme contained in a big fppf site `B`, let `τ` be one of the fppf, syntomic,
smooth and étale topologies of **Stacks 03YH**, and let `P` be a property of morphisms of
algebraic spaces over `S` which is local on the target for `τ`. Every morphism
`f : X ⟶ Y` of algebraic spaces over `S` then has a largest open subspace `W(f) ⊆ Y` over
which its restriction has `P`, and that open subspace is compatible with the base changes `τ`
admits: a morphism `g : Y' ⟶ Y` which `τ` admits as a member of a covering family and over
which `f` has `P` factors through `W(f)`; for any member `g`, `W` of the base change of `f`
along `g` is the inverse image of `W(f)`; and in particular this holds for every member of a
`τ`-covering of `Y`.

The construction is the source's. The union, inside the space of points `|Y|` of
**Stacks 03BU**, of the images of all `g : Y' ⟶ Y` which `τ` admits and over which `f` has `P`
is open, because such a `g` is universally open by **Stacks 042S**, hence open. By the
correspondence of **Stacks 03BZ** that open set is the point set of a unique open subspace `W`,
and the chosen morphisms factor through `W` by **Stacks 03IE** and form a `τ`-covering of it,
so the restriction of `f` over `W` has `P` by locality on the target. Maximality is immediate,
an open subspace over which `f` has `P` being one of the morphisms in the union. Compatibility
with a base change along a member `g` follows in one direction from the factorization and in
the other from stability of `P` under such base changes.

## Main definitions

* `AlgebraicGeometry.Space.openObject` and `AlgebraicGeometry.Space.openInclusion`: an open
  subspace of **Stacks 02YU** read as an algebraic space over `S` together with its inclusion.
* `AlgebraicGeometry.Space.HasPropertyOnOpen`: the restriction of a morphism over an open
  subspace of its target has a given property.
* `AlgebraicGeometry.Space.largestOpenSubspace`: the largest open subspace of the target over
  which the restriction has `P`, with its defining property. This is the existence and
  maximality assertion of **Stacks 06R2**.

## Main results

* `AlgebraicGeometry.Space.factorsThrough_largestOpenSubspace`: **Stacks 06R2**, part (1).
* `AlgebraicGeometry.Space.largestOpenSubspace_baseChange`: **Stacks 06R2**, part (2).
* `AlgebraicGeometry.Space.largestOpenSubspace_covering`: **Stacks 06R2**, part (3).

## Implementation notes

The morphisms `τ` admits as members of a covering family are
`AlgebraicGeometry.Space.Topology.IsMember`; the fpqc topology is excluded throughout by the
hypothesis `τ ≠ Topology.fpqc`, exactly as the source excludes it, because a flat morphism need
not be open. This file records the permanence properties of that condition which the
construction uses — composition, base change, and the fact that an étale morphism, in
particular an isomorphism or the inclusion of an open subspace, is a member.

The family of all admissible morphisms over which `f` has `P` is indexed by a type in
`Type (u + 1)`, since the objects of the category of algebraic spaces over `S` are presheaves
of types in `Type u`. Locality of `P` on the target is therefore required at the index universe
`u + 1` for the three main results, while the auxiliary statements keep an index universe `v`
together with a smallness hypothesis on that family. The covering family in part (3) retains
its own index universe `v`.

Equality of two open subspaces after base change is equality of subfunctors of the new target,
the inverse image being `CategoryTheory.Subfunctor.preimage` of **Stacks 083Q**.

## References

* [Stacks Project, Tag 06R2](https://stacks.math.columbia.edu/tag/06R2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

attribute [local instance] pointTopology

/-! ### Permanence of the member condition of a topology -/

/-- A composite of two morphisms of algebraic spaces over `S` which `τ` admits as members of a
covering family is again such a morphism. -/
private theorem isMember_comp (τ : Topology) {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) {f : F ⟶ G} {g : G ⟶ H}
    (hf : τ.IsMember B S hS f) (hg : τ.IsMember B S hS g) :
    τ.IsMember B S hS (f ≫ g) := by
  cases τ with
  | fpqc => exact isFlat_comp B S hS hF hG hH f g hf hg
  | fppf =>
      exact ⟨isFlat_comp B S hS hF hG hH f g hf.1 hg.1,
        isLocallyOfFinitePresentation_comp B S hS hF hG hH f g hf.2 hg.2⟩
  | syntomic => exact isSyntomic_comp B S hS hF hG hH f g hf hg
  | smooth => exact isSmooth_comp B S hS hF hG hH f g hf hg
  | etale => exact isEtale_comp B S hS hf hg

/-- A base change of a morphism of algebraic spaces over `S` which `τ` admits as a member of a
covering family is again such a morphism. -/
private theorem isMember_of_isPullback (τ : Topology)
    {X' X Z Y : AlgebraicSpaces B S hS} (p : X' ⟶ X) (f' : X' ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (sq : IsPullback p f' f g) (hf : τ.IsMember B S hS f.hom) :
    τ.IsMember B S hS f'.hom := by
  cases τ with
  | fpqc => exact (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hf
  | fppf =>
      exact ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hf.1,
        (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hf.2⟩
  | syntomic => exact (isSyntomic_isStableUnderBaseChange B S hS).of_isPullback sq hf
  | smooth => exact (isSmooth_isStableUnderBaseChange B S hS).of_isPullback sq hf
  | etale => exact isEtale_of_isPullback B S hS p f' f g sq hf

/-- An étale morphism of algebraic spaces over `S` is a member of a covering family for every
one of the five topologies: it is flat, locally of finite presentation, syntomic and smooth. -/
private theorem isMember_of_isEtale (τ : Topology) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G} (hf : IsEtale B S hS f) :
    τ.IsMember B S hS f := by
  cases τ with
  | fpqc => exact isFlat_of_isEtale B S hS hf
  | fppf =>
      exact ⟨isFlat_of_isEtale B S hS hf,
        isLocallyOfFinitePresentation_of_isEtale B S hS hf⟩
  | syntomic => exact isSyntomic_of_isSmooth B S hS f (isSmooth_of_isEtale B S hS hG hf)
  | smooth => exact isSmooth_of_isEtale B S hS hG hf
  | etale => exact hf

/-- A morphism of algebraic spaces over `S` which `τ` admits as a member of a covering family
is universally open, provided `τ` is not the fpqc topology: it is flat and locally of finite
presentation, so **Stacks 042S** applies. -/
private theorem universallyOpen_of_isMember (τ : Topology) (hτ : τ ≠ .fpqc)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G} (hf : τ.IsMember B S hS f) :
    UniversallyOpen B S hS f := by
  have h042S := universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hF hG f
  cases τ with
  | fpqc => exact absurd rfl hτ
  | fppf => exact h042S hf.1 hf.2
  | syntomic =>
      exact h042S (isFlat_of_isSyntomic B S hS hf)
        (isLocallyOfFinitePresentation_of_isSyntomic B S hS hf)
  | smooth =>
      exact h042S (isFlat_of_isSmooth B S hS f hf)
        (isLocallyOfFinitePresentation_of_isSmooth B S hS hf)
  | etale =>
      exact h042S (isFlat_of_isEtale B S hS hf)
        (isLocallyOfFinitePresentation_of_isEtale B S hS hf)

/-- A morphism of algebraic spaces over `S` which `τ` admits as a member of a covering family
is open, provided `τ` is not the fpqc topology. -/
private theorem isOpenMorphism_of_isMember (τ : Topology) (hτ : τ ≠ .fpqc)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G} (hf : τ.IsMember B S hS f) :
    IsOpenMorphism B S hS f :=
  isOpen_of_universallyOpen B S hS hG f (universallyOpen_of_isMember B S hS τ hτ hF hG hf)

/-- A family of morphisms of algebraic spaces over `S` which `τ` admits as members of a
covering family and which is jointly surjective on points is a `τ`-covering family, provided
`τ` is not the fpqc topology. -/
private theorem isCovering_of_isMember (τ : Topology) (hτ : τ ≠ .fpqc) {I : Type v}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (g : ∀ i, Yi i ⟶ Y) (hY : IsAlgebraicSpace B S hS Y)
    (hYi : ∀ i, IsAlgebraicSpace B S hS (Yi i)) (hg : ∀ i, τ.IsMember B S hS (g i))
    (hsurj : (⋃ i, Set.range (pointsMap B S hS (Yi i) (g i))) = Set.univ) :
    τ.IsCovering B S hS Yi g := by
  refine ⟨hY, hYi, ?_⟩
  cases τ with
  | fpqc => exact absurd rfl hτ
  | fppf => exact ⟨hY, hYi, fun i ↦ (hg i).1, fun i ↦ (hg i).2, hsurj⟩
  | syntomic => exact ⟨hY, hYi, hg, hsurj⟩
  | smooth => exact ⟨hY, hYi, hg, hsurj⟩
  | etale => exact ⟨hY, hYi, hg, hsurj⟩

/-! ### Open subspaces as algebraic spaces -/

/-- The algebraic space over `S` underlying an open subspace of **Stacks 02YU** of an algebraic
space over `S`. -/
def openObject {Y : AlgebraicSpaces B S hS}
    (W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W}) : AlgebraicSpaces B S hS :=
  ⟨W.1.toFunctor, W.2.1⟩

/-- The inclusion of an open subspace of **Stacks 02YU** into its ambient algebraic space, as a
morphism of algebraic spaces over `S`. -/
def openInclusion {Y : AlgebraicSpaces B S hS}
    (W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W}) : openObject B S hS W ⟶ Y :=
  ObjectProperty.homMk W.1.ι

/-- The inclusion of an open subspace is étale: an open immersion of algebraic spaces over `S`
is étale after every representable base change. -/
private theorem isEtale_openInclusion {Y : AlgebraicSpaces B S hS}
    (W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W}) :
    IsEtale B S hS (openInclusion B S hS W).hom :=
  isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS W.2.2)

/-- The restriction of `f : X ⟶ Y` over an open subspace `W` of `Y`, that is the base change of
`f` along the inclusion of `W`, has the property `P`. -/
def HasPropertyOnOpen (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W}) : Prop :=
  P (pullback.snd f (openInclusion B S hS W))

/-- Restricting a base change of `f : X ⟶ Y` along `g : U ⟶ Y` further along `h : V ⟶ U` is
restricting `f` along the composite, up to the pasting isomorphism of fibre products. -/
private theorem pullback_snd_comp_iff {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) [P.RespectsIso] {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ Y)
    (h : V ⟶ U) :
    P (pullback.snd (pullback.snd f g) h) ↔ P (pullback.snd f (h ≫ g)) := by
  have he : (pullbackLeftPullbackSndIso f g h).hom ≫ pullback.snd f (h ≫ g) =
      pullback.snd (pullback.snd f g) h :=
    pullbackLeftPullbackSndIso_hom_snd f g h
  rw [← he, P.cancel_left_of_respectsIso]

/-- A property of the restriction of `f` along a morphism depends on that morphism only
through the morphism itself, so it transports along an equality of base morphisms. The rewrite
cannot be done in place, the fibre product's existence instance depending on the morphism. -/
private theorem pullback_snd_of_eq {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) {X Y U : C} (f : X ⟶ Y) {g g' : U ⟶ Y} (h : g = g')
    (hp : P (pullback.snd f g')) : P (pullback.snd f g) := by
  subst h; exact hp

/-- A subfunctor of the source of `f` which maps into a subfunctor of its target is contained in
the inverse image of the latter. -/
private theorem subfunctor_le_preimage_of_factor
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor Y} {V : Subfunctor X}
    (f : Y ⟶ X)
    (h : U.toFunctor ⟶ V.toFunctor) (hh : h ≫ V.ι = U.ι ≫ f) : U ≤ V.preimage f := by
  intro T x hx
  show f.app T (U.ι.app T ⟨x, hx⟩) ∈ V.obj T
  have hval : V.ι.app T (h.app T ⟨x, hx⟩) = f.app T (U.ι.app T ⟨x, hx⟩) := by
    have hval' := congrArg (fun α ↦ α ⟨x, hx⟩) (congrArg (fun α ↦ α.app T) hh)
    change (V.ι.app T ∘ h.app T) ⟨x, hx⟩ = (f.app T ∘ U.ι.app T) ⟨x, hx⟩ at hval'
    convert hval' using 1 <;> rfl
  rw [← hval]
  exact (h.app T ⟨x, hx⟩).property

/-- A containment of open subspaces is the same as a containment of their point sets. -/
private theorem range_pointsMap_subset_iff {Y : AlgebraicSpaces B S hS}
    {U V : {U : Subfunctor Y.obj // IsOpenSubspace B S hS U}} :
    Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) ⊆
      Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) ↔ U.1 ≤ V.1 := by
  rw [← openSubspacesOrderIso_apply B S hS Y.obj Y.property U,
    ← openSubspacesOrderIso_apply B S hS Y.obj Y.property V]
  exact (openSubspacesOrderIso B S hS Y.obj Y.property).le_iff_le

/-! ### The admissible morphisms over which the property holds -/

/-- A morphism into the target of `f` which `τ` admits as a member of a covering family and
along which the base change of `f` has `P`. -/
private abbrev GoodArrow (τ : Topology) (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  {q : Σ Z : AlgebraicSpaces B S hS, Z ⟶ Y //
    τ.IsMember B S hS q.2.hom ∧ P (pullback.snd f q.2)}

/-- The set of points of the target hit by one such morphism. -/
private def goodArrowPointSet (τ : Topology) (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) : Set (points B S hS Y.obj) :=
  Set.range (pointsMap B S hS q.1.1.obj q.1.2.hom)

/-- The union of the point sets of all such morphisms is open, each of them being open. -/
private theorem isOpen_iUnion_goodArrowPointSet (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsOpen (⋃ q : GoodArrow B S hS τ P f, goodArrowPointSet B S hS τ P f q) :=
  isOpen_iUnion fun q ↦
    (isOpenMorphism_of_isMember B S hS τ hτ q.1.1.property Y.property q.2.1).isOpen_range

/-- The union of the point sets of all morphisms `τ` admits along which the base change of `f`
has `P`, as an open subset of the space of points of the target. -/
private def goodArrowUnionOpen (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    TopologicalSpace.Opens (points B S hS Y.obj) :=
  ⟨⋃ q : GoodArrow B S hS τ P f, goodArrowPointSet B S hS τ P f q,
    isOpen_iUnion_goodArrowPointSet B S hS τ hτ P f⟩

/-- The open subspace of the target whose points are hit by the morphisms `τ` admits along
which the base change of `f` has `P`. -/
private noncomputable def goodArrowOpenSubspace (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    {W : Subfunctor Y.obj // IsOpenSubspace B S hS W} :=
  (openSubspacesOrderIso B S hS Y.obj Y.property).symm (goodArrowUnionOpen B S hS τ hτ P f)

private theorem goodArrowOpenSubspace_points (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (goodArrowOpenSubspace B S hS τ hτ P f).1.toFunctor
      (goodArrowOpenSubspace B S hS τ hτ P f).1.ι) =
      ⋃ q : GoodArrow B S hS τ P f, goodArrowPointSet B S hS τ P f q := by
  simpa [goodArrowOpenSubspace, goodArrowUnionOpen] using
    (openSubspacesOrderIso_apply B S hS Y.obj Y.property
      (goodArrowOpenSubspace B S hS τ hτ P f)).symm

private theorem goodArrow_range_subset (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) :
    Set.range (pointsMap B S hS q.1.1.obj q.1.2.hom) ⊆
      Set.range (pointsMap B S hS (goodArrowOpenSubspace B S hS τ hτ P f).1.toFunctor
        (goodArrowOpenSubspace B S hS τ hτ P f).1.ι) := by
  rw [goodArrowOpenSubspace_points B S hS τ hτ P f]
  rintro x ⟨z, rfl⟩
  exact Set.mem_iUnion.mpr ⟨q, ⟨z, rfl⟩⟩

/-- By **Stacks 03IE** each of the morphisms factors through that open subspace. -/
private theorem goodArrow_factorsThrough (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) :
    ∃ h : q.1.1.obj ⟶ (goodArrowOpenSubspace B S hS τ hτ P f).1.toFunctor,
      h ≫ (goodArrowOpenSubspace B S hS τ hτ P f).1.ι = q.1.2.hom :=
  (factorsThrough_openSubspace_iff_points B S hS Y.property q.1.1.property
    (goodArrowOpenSubspace B S hS τ hτ P f).1 (goodArrowOpenSubspace B S hS τ hτ P f).2
    q.1.2.hom).2 (goodArrow_range_subset B S hS τ hτ P f q)

/-- The factorization of such a morphism through the open subspace. -/
private noncomputable def goodArrowFactor (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) :
    q.1.1 ⟶ openObject B S hS (goodArrowOpenSubspace B S hS τ hτ P f) :=
  ObjectProperty.homMk (Classical.choose (goodArrow_factorsThrough B S hS τ hτ P f q))

private theorem goodArrowFactor_fac (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) :
    goodArrowFactor B S hS τ hτ P f q ≫
      openInclusion B S hS (goodArrowOpenSubspace B S hS τ hτ P f) = q.1.2 :=
  ObjectProperty.hom_ext _
    (Classical.choose_spec (goodArrow_factorsThrough B S hS τ hτ P f q))

/-- A morphism which `τ` admits and which factors through the inclusion of an open subspace
factors through it by a morphism `τ` admits: the factorization is a base change of the given
morphism along a monomorphism. -/
private theorem isMember_of_factorsThrough_openInclusion (τ : Topology)
    {Y : AlgebraicSpaces B S hS}
    {W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W}} {Z : AlgebraicSpaces B S hS}
    {g : Z ⟶ Y} (hg : τ.IsMember B S hS g.hom) (h : Z ⟶ openObject B S hS W)
    (hh : h ≫ openInclusion B S hS W = g) : τ.IsMember B S hS h.hom := by
  have hmono : Mono (openInclusion B S hS W) := by
    have : Mono W.1.ι := inferInstance
    refine ⟨fun a b hab ↦ ObjectProperty.hom_ext _ ((cancel_mono W.1.ι).1 ?_)⟩
    exact congrArg (fun k ↦ k.hom) hab
  have hpb : IsPullback (𝟙 Z) h g (openInclusion B S hS W) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [hh]⟩
  exact isMember_of_isPullback B S hS τ (𝟙 Z) h g (openInclusion B S hS W) hpb hg

/-- Each factorization through the open subspace is a morphism `τ` admits, being a base change
of a morphism `τ` admits along the monomorphism which is the inclusion. -/
private theorem isMember_goodArrowFactor (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (q : GoodArrow B S hS τ P f) :
    τ.IsMember B S hS (goodArrowFactor B S hS τ hτ P f q).hom :=
  isMember_of_factorsThrough_openInclusion B S hS τ q.2.1 _
    (goodArrowFactor_fac B S hS τ hτ P f q)

/-- The factorizations through the open subspace are jointly surjective on its points: the
inclusion of the open subspace is injective on points by **Stacks 06RV**, and the points of the
open subspace are by construction the union of the images of the chosen morphisms. -/
private theorem isJointlySurjective_goodArrowFactor (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsJointlySurjective B S hS (fun q : GoodArrow B S hS τ P f ↦ q.1.1.obj)
      (fun q ↦ (goodArrowFactor B S hS τ hτ P f q).hom) := by
  set W := goodArrowOpenSubspace B S hS τ hτ P f with hW
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  have hx : pointsMap B S hS W.1.toFunctor W.1.ι x ∈
      ⋃ q : GoodArrow B S hS τ P f, goodArrowPointSet B S hS τ P f q := by
    rw [← goodArrowOpenSubspace_points B S hS τ hτ P f]
    exact ⟨x, rfl⟩
  obtain ⟨q, z, hz⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨q, z, pointsMap_injective_of_mono B S hS W.1.ι ?_⟩
  calc pointsMap B S hS W.1.toFunctor W.1.ι
        (pointsMap B S hS q.1.1.obj (goodArrowFactor B S hS τ hτ P f q).hom z)
      = pointsMap B S hS q.1.1.obj
          ((goodArrowFactor B S hS τ hτ P f q).hom ≫ W.1.ι) z :=
        (pointsMap_comp_apply B S hS _ _ z).symm
    _ = pointsMap B S hS q.1.1.obj q.1.2.hom z :=
      congrArg (fun k ↦ pointsMap B S hS q.1.1.obj k.hom z)
        (goodArrowFactor_fac B S hS τ hτ P f q)
    _ = pointsMap B S hS W.1.toFunctor W.1.ι x := hz

/-- The restriction of `f` over that open subspace has `P`: the factorizations form a
`τ`-covering of it along which the base changes of `f` have `P`. -/
private theorem hasPropertyOnOpen_goodArrowOpenSubspace (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, v} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Small.{v} (GoodArrow B S hS τ P f)] :
    HasPropertyOnOpen B S hS P f (goodArrowOpenSubspace B S hS τ hτ P f) := by
  set W := goodArrowOpenSubspace B S hS τ hτ P f with hW
  set E := (equivShrink.{v} (GoodArrow B S hS τ P f)).symm with hE
  have hR : Presieve.ofArrows (fun j : Shrink.{v} (GoodArrow B S hS τ P f) ↦ (E j).1.1)
      (fun j ↦ goodArrowFactor B S hS τ hτ P f (E j)) ∈
        Topology.precoverage.{u, v} τ B S hS (openObject B S hS W) :=
    ⟨Shrink.{v} (GoodArrow B S hS τ P f), _, _, rfl,
      isCovering_of_isMember B S hS τ hτ _ _ W.2.1 (fun j ↦ (E j).1.1.property)
        (fun j ↦ isMember_goodArrowFactor B S hS τ hτ P f (E j))
        (isJointlySurjective_reindex B S hS
          (isJointlySurjective_goodArrowFactor B S hS τ hτ P f) E.surjective)⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR ?_
  rintro Z k hpb ⟨j⟩
  have hdirect : P (pullback.snd f (goodArrowFactor B S hS τ hτ P f (E j) ≫
      openInclusion B S hS W)) := by
    rw [goodArrowFactor_fac B S hS τ hτ P f (E j)]
    exact (E j).2.2
  exact (pullback_snd_comp_iff P f (openInclusion B S hS W)
    (goodArrowFactor B S hS τ hτ P f (E j))).2 hdirect

/-- That open subspace is the largest one over which the restriction of `f` has `P`. -/
private theorem goodArrowOpenSubspace_isLargest (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, v} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Small.{v} (GoodArrow B S hS τ P f)] :
    ∃ W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W},
      HasPropertyOnOpen B S hS P f W ∧
        ∀ V : {V : Subfunctor Y.obj // IsOpenSubspace B S hS V},
          HasPropertyOnOpen B S hS P f V → V.1 ≤ W.1 := by
  refine ⟨goodArrowOpenSubspace B S hS τ hτ P f,
    hasPropertyOnOpen_goodArrowOpenSubspace.{u, v} B S hS τ hτ P f, fun V hV ↦ ?_⟩
  exact (range_pointsMap_subset_iff B S hS).1 (goodArrow_range_subset B S hS τ hτ P f
    ⟨⟨openObject B S hS V, openInclusion B S hS V⟩,
      isMember_of_isEtale B S hS τ Y.property (isEtale_openInclusion B S hS V), hV⟩)

/-! ### Stacks 06R2 -/

/-- **Stacks 06R2**, existence and maximality. For a property `P` of morphisms of algebraic
spaces over `S` which is local on the target for a topology `τ` other than the fpqc topology,
every morphism `f : X ⟶ Y` has a largest open subspace of `Y` over which its restriction has
`P`. -/
@[stacks 06R2 "existence and maximality"]
noncomputable def largestOpenSubspace (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    {W : {W : Subfunctor Y.obj // IsOpenSubspace B S hS W} //
      HasPropertyOnOpen B S hS P f W ∧
        ∀ V : {V : Subfunctor Y.obj // IsOpenSubspace B S hS V},
          HasPropertyOnOpen B S hS P f V → V.1 ≤ W.1} :=
  Classical.choice (by
    obtain ⟨W, hW⟩ := goodArrowOpenSubspace_isLargest.{u, u + 1} B S hS τ hτ P f
    exact ⟨⟨W, hW⟩⟩)

/-- The restriction of `f` over its largest open locus has `P`, and every open subspace over
which the restriction has `P` is contained in it. -/
private theorem largestOpenSubspace_spec (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    HasPropertyOnOpen B S hS P f (largestOpenSubspace B S hS τ hτ P f).1 ∧
      ∀ V : {V : Subfunctor Y.obj // IsOpenSubspace B S hS V},
        HasPropertyOnOpen B S hS P f V →
          V.1 ≤ (largestOpenSubspace B S hS τ hτ P f).1.1 :=
  (largestOpenSubspace B S hS τ hτ P f).2

/-- **Stacks 06R2**, part (1). A morphism `g : Y' ⟶ Y` which `τ` admits as a member of a
covering family and along which the base change of `f` has `P` factors through the largest open
locus of `f`. -/
@[stacks 06R2 "part (1)"]
theorem factorsThrough_largestOpenSubspace (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} τ B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : τ.IsMember B S hS g.hom) (hP : P (pullback.snd f g)) :
    ∃ h : Y' ⟶ openObject B S hS (largestOpenSubspace B S hS τ hτ P f).1,
      h ≫ openInclusion B S hS (largestOpenSubspace B S hS τ hτ P f).1 = g := by
  have hle := (largestOpenSubspace_spec.{u} B S hS τ hτ P f).2
    (goodArrowOpenSubspace B S hS τ hτ P f)
    (hasPropertyOnOpen_goodArrowOpenSubspace.{u, u + 1} B S hS τ hτ P f)
  obtain ⟨h, hh⟩ := (factorsThrough_openSubspace_iff_points B S hS Y.property Y'.property
    (largestOpenSubspace B S hS τ hτ P f).1.1 (largestOpenSubspace B S hS τ hτ P f).1.2
    g.hom).2 ((goodArrow_range_subset B S hS τ hτ P f ⟨⟨Y', g⟩, hg, hP⟩).trans
      ((range_pointsMap_subset_iff B S hS).2 hle))
  exact ⟨ObjectProperty.homMk h, ObjectProperty.hom_ext _ hh⟩

/-- **Stacks 06R2**, part (2). The largest open locus of a base change of `f` along a morphism
`g` which `τ` admits as a member of a covering family is the inverse image of the largest open
locus of `f`. -/
@[stacks 06R2 "part (2)"]
theorem largestOpenSubspace_baseChange (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} τ B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : τ.IsMember B S hS g.hom) :
    (largestOpenSubspace B S hS τ hτ P (pullback.snd f g)).1.1 =
      ((largestOpenSubspace B S hS τ hτ P f).1.1).preimage g.hom := by
  set L := largestOpenSubspace B S hS τ hτ P f with hL0
  set L' := largestOpenSubspace B S hS τ hτ P (pullback.snd f g) with hL0'
  set V : {V : Subfunctor Y'.obj // IsOpenSubspace B S hS V} :=
    ⟨L.1.1.preimage g.hom,
      isOpenSubspace_preimage B S hS g.hom L.1.1 Y.property Y'.property L.1.2⟩ with hV0
  have hL := largestOpenSubspace_spec.{u} B S hS τ hτ P f
  have hL' := largestOpenSubspace_spec.{u} B S hS τ hτ P (pullback.snd f g)
  -- The largest open locus of the base change is contained in the inverse image, by part (1).
  have hfwd : L'.1.1 ≤ V.1 := by
    have hdirect : P (pullback.snd f (openInclusion B S hS L'.1 ≫ g)) :=
      (pullback_snd_comp_iff P f g (openInclusion B S hS L'.1)).mp hL'.1
    obtain ⟨h, hfac⟩ := factorsThrough_largestOpenSubspace B S hS τ hτ P f
      (openInclusion B S hS L'.1 ≫ g)
      (isMember_comp B S hS τ (openObject B S hS L'.1).property Y'.property Y.property
        (isMember_of_isEtale B S hS τ Y'.property (isEtale_openInclusion B S hS L'.1)) hg)
      hdirect
    exact subfunctor_le_preimage_of_factor B S hS g.hom h.hom
      (congrArg (fun k ↦ k.hom) hfac)
  -- Conversely the restriction of the base change over the inverse image has `P`, because the
  -- inverse image is the base change along `g` of the largest open locus of `f`.
  refine le_antisymm hfwd (hL'.2 V ?_)
  set r : openObject B S hS V ⟶ openObject B S hS L.1 :=
    ObjectProperty.homMk (L.1.1.fromPreimage g.hom) with hr0
  have hpullCat : IsPullback r (openInclusion B S hS V) (openInclusion B S hS L.1) g :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage g.hom L.1.1)
  have hr : τ.IsMember B S hS r.hom :=
    isMember_of_isPullback B S hS τ (openInclusion B S hS V) r g
      (openInclusion B S hS L.1) hpullCat.flip hg
  have hbase : P (pullback.snd (pullback.snd f (openInclusion B S hS L.1)) r) :=
    MorphismProperty.IsLocalAtTarget.pullbackSnd
      (mem_precoverage_idPair.{u, u + 1} τ r hr) (Presieve.ofArrows.mk (ULift.up true)) hL.1
  have hdirect : P (pullback.snd f (openInclusion B S hS V ≫ g)) :=
    pullback_snd_of_eq P f hpullCat.w.symm
      ((pullback_snd_comp_iff P f (openInclusion B S hS L.1) r).mp hbase)
  show P (pullback.snd (pullback.snd f g) (openInclusion B S hS V))
  exact (pullback_snd_comp_iff P f g (openInclusion B S hS V)).mpr hdirect

/-- **Stacks 06R2**, part (3). The largest open locus of the base change of `f` along a member
of a `τ`-covering of its target is the inverse image of the largest open locus of `f`. -/
@[stacks 06R2 "part (3)"]
theorem largestOpenSubspace_covering (τ : Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} τ B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {I : Type v}
    (Yi : I → AlgebraicSpaces B S hS) (g : ∀ i, Yi i ⟶ Y)
    (hg : τ.IsCovering B S hS (fun i ↦ (Yi i).obj) (fun i ↦ (g i).hom)) (i : I) :
    (largestOpenSubspace B S hS τ hτ P (pullback.snd f (g i))).1.1 =
      ((largestOpenSubspace B S hS τ hτ P f).1.1).preimage (g i).hom := by
  refine largestOpenSubspace_baseChange B S hS τ hτ P f (g i) ?_
  obtain ⟨-, -, hc⟩ := hg
  cases τ with
  | fpqc => exact absurd rfl hτ
  | fppf => exact ⟨hc.flat i, hc.locallyOfFinitePresentation i⟩
  | syntomic => exact hc.syntomic i
  | smooth => exact hc.smooth i
  | etale => exact hc.etale i

end

end AlgebraicGeometry.Space

end
