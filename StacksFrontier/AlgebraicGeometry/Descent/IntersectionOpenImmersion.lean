module

public import StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImage
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SubsetLocallyRingedSpaceFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical embedding of an intersection is an open immersion on an open

Let `X` be an ind-quasi-affine scheme, let `E = ⋂ᵢ Uᵢ` be the intersection of a nonempty family
of quasi-compact opens of `X`, and let `W` be an open of `X` contained in `E`. Writing `j` for the
canonical embedding of [Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API), this file
proves that `j` restricted to `W` is an open immersion **of schemes** onto the open subscheme
`j(W)` of `Spec Γ(E, 𝒪_X|_E)`.

Tag 0API itself provides only an isomorphism of *locally ringed spaces* at `E`, and `E` carries no
scheme structure. The content here is that over the open part `W` of `E` both sides are schemes
and the embedding is an open immersion between them.

## Main results

* `AlgebraicGeometry.ofSubsetHom` : the canonical map from the restriction of a locally ringed
  space to a subset, as a morphism of locally ringed spaces.
* `AlgebraicGeometry.isIso_ofSubsetHom_univ` : that map is an isomorphism at the whole space.
* `AlgebraicGeometry.isIso_stalkMap_toΓSpec_subsetLocallyRingedSpace` : the canonical embedding of
  an intersection of quasi-compact opens in an ind-quasi-affine scheme is an isomorphism on
  stalks.
* `AlgebraicGeometry.isIso_stalkMap_subsetLocallyRingedSpaceMap` : the morphism of restrictions
  induced by an open immersion is an isomorphism on stalks.
* `AlgebraicGeometry.injective_toΓSpec_base_subsetLocallyRingedSpace` : that embedding is
  injective on points.
* `AlgebraicGeometry.Γ_map_ofSubsetHom` : the induced map on global sections is the restriction of
  a global function to the subset.
* `AlgebraicGeometry.exists_isOpenImmersion_range_eq_subsetΓSpecImage` : **the canonical embedding
  restricted to an open is an open immersion of schemes onto its image**, compatibly with the
  restriction of global functions to the subset.

## Implementation notes

*Why the embedding is an isomorphism on stalks.* The isomorphism of locally ringed spaces that
Tag 0API produces factors the embedding through the canonical map of the restriction of
`Spec Γ(E, 𝒪_X|_E)` to a subset, and that map is an isomorphism on stalks by
`AlgebraicGeometry.isIso_ofSubset_stalkMap`.

*Where the scheme structure on the source comes from.* The restriction of `W` to the whole of its
own space is `W` itself, by `AlgebraicGeometry.isIso_ofSubsetHom_univ`, and
`AlgebraicGeometry.subsetLocallyRingedSpaceMap` at the open immersion `W ⟶ X` carries it into the
restriction of `X` to `E`. That morphism is an isomorphism on stalks because
`AlgebraicGeometry.stalkMap_subsetPresheafedSpaceMap` identifies its stalk map with the stalk map
of `W ⟶ X`, which is an isomorphism.

*What the open immersion is for.* It is the identification that the last step of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) uses to exhibit an invariant open of
the scheme carrying a descent datum as a base change of the descended scheme.

*Where openness of the image comes from.* Only through Tag 0API's own assertion
`AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen`, applied to each open of `X` contained in `W`;
every open of `W` is of that form, which is what makes the embedding an open map on `W`.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

universe u v

namespace AlgebraicGeometry

/-- **The canonical map of the restriction of a locally ringed space to a subset, as a morphism of
locally ringed spaces.** Its stalk maps are isomorphisms, hence local homomorphisms. -/
@[ega "0 4.1.2" "special case"]
def ofSubsetHom (X : LocallyRingedSpace.{u}) (E : Set X) :
    subsetLocallyRingedSpace X E ⟶ X where
  toHom := ofSubset X E
  prop x := by
    have h := isIso_ofSubset_stalkMap X E x
    exact isLocalHom_of_isIso ((ofSubset X E).stalkMap x)

/-- The underlying map of `AlgebraicGeometry.ofSubsetHom` is the inclusion of the subset. -/
lemma ofSubsetHom_base_apply (X : LocallyRingedSpace.{u}) (E : Set X)
    (x : subsetLocallyRingedSpace X E) : (ofSubsetHom X E).base x = x.1 := rfl

/-- The map on global sections induced by `AlgebraicGeometry.ofSubsetHom` is the restriction of a
global function of a scheme to the subset. -/
lemma Γ_map_ofSubsetHom (X : Scheme.{u}) (E : Set X) :
    LocallyRingedSpace.Γ.map (ofSubsetHom X.toLocallyRingedSpace E).op = X.topToSubset E :=
  (X.topToSubset_eq_unit_app E).symm

/-- **The restriction of a locally ringed space to the whole of its space is itself.** The
canonical map is an isomorphism on stalks and a homeomorphism on spaces. -/
lemma isIso_ofSubsetHom_univ (X : LocallyRingedSpace.{u}) :
    IsIso (ofSubsetHom X (Set.univ : Set X)) := by
  have hstalk : ∀ x, IsIso ((ofSubsetHom X (Set.univ : Set X)).stalkMap x) := fun x =>
    isIso_ofSubset_stalkMap X Set.univ x
  have hemb : IsOpenEmbedding (ofSubsetHom X (Set.univ : Set X)).base.hom :=
    (isOpen_univ (X := X)).isOpenEmbedding_subtypeVal
  have hopen : LocallyRingedSpace.IsOpenImmersion (ofSubsetHom X (Set.univ : Set X)) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ hemb
  have hepi : Epi (ofSubsetHom X (Set.univ : Set X)).base :=
    (TopCat.epi_iff_surjective _).2 fun x => ⟨⟨x, Set.mem_univ x⟩, rfl⟩
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

/-- Equal morphisms of presheafed spaces have the same stalk maps, so one is an isomorphism as
soon as the other is. -/
private lemma isIso_stalkMap_of_eq {P Q : PresheafedSpace CommRingCat.{u}} {α β : P ⟶ Q}
    (h : α = β) (x : P) (hα : IsIso (α.stalkMap x)) : IsIso (β.stalkMap x) := h ▸ hα

/-- **The canonical embedding of an intersection of quasi-compact opens in an ind-quasi-affine
scheme is an isomorphism on every stalk**, where the intersection carries the inverse image of the
structure sheaf. -/
lemma isIso_stalkMap_toΓSpec_subsetLocallyRingedSpace (X : Scheme.{u}) [IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (x : subsetLocallyRingedSpace X.toLocallyRingedSpace E) :
    IsIso ((subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.stalkMap x) := by
  subst hE
  obtain ⟨-, V, -, -, -, -, -, e, he⟩ := exists_iInter_iso_iInter_in_specΓ (X := X) U hU
  have hL : IsIso (e.hom.toHom.stalkMap x) := inferInstance
  have hR := isIso_ofSubset_stalkMap _ _ (e.hom.base x)
  exact isIso_stalkMap_of_eq he x (by
    rw [PresheafedSpace.stalkMap.comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hR hL)

/-- An isomorphism of locally ringed spaces has inverse base map a left inverse of its base map. -/
private lemma inv_base_hom_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (z : X) :
    e.inv.base (e.hom.base z) = z :=
  congrArg (fun t : TopCat.Hom _ _ => t.hom z)
    (congrArg (fun q : LocallyRingedSpace.Hom _ _ => q.base) e.hom_inv_id)

/-- **The canonical embedding of an intersection of quasi-compact opens in an ind-quasi-affine
scheme is injective on points.** -/
lemma injective_toΓSpec_base_subsetLocallyRingedSpace (X : Scheme.{u}) [IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    Function.Injective
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base.hom := by
  subst hE
  obtain ⟨-, V, -, -, -, -, -, e, he⟩ := exists_iInter_iso_iInter_in_specΓ (X := X) U hU
  have hbase0 := congrArg (fun q : PresheafedSpace.Hom _ _ => q.base) he
  have hb : ∀ z, (subsetLocallyRingedSpace X.toLocallyRingedSpace
      (⋂ i, (U i : Set X))).toΓSpec.base z = (e.hom.base z).1 := fun z =>
    (congrArg (fun t : TopCat.Hom _ _ => t.hom z) hbase0).symm
  intro a b hab
  exact ((inv_base_hom_base_apply e a).symm.trans (congrArg (fun z => e.inv.base z)
    (Subtype.ext ((hb a).symm.trans (hab.trans (hb b)))))).trans (inv_base_hom_base_apply e b)

/-- **The morphism of restrictions induced by an open immersion is an isomorphism on stalks.**
Through the isomorphisms `AlgebraicGeometry.isIso_ofSubset_stalkMap` its stalk map is the stalk
map of the open immersion, which is an isomorphism. -/
lemma isIso_stalkMap_subsetLocallyRingedSpaceMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (E : Set Y) (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) (x : E') :
    IsIso ((subsetLocallyRingedSpaceMap g E E' h).stalkMap x) := by
  have h1 := isIso_ofSubset_stalkMap Y.toLocallyRingedSpace E
    ((subsetPresheafedSpaceMap g E E' h).base x)
  have h2 : IsIso (g.toLRSHom.toHom.stalkMap x.1) := inferInstance
  have h3 := isIso_ofSubset_stalkMap X.toLocallyRingedSpace E' x
  have hrhs : IsIso (g.toLRSHom.toHom.stalkMap x.1 ≫
      (ofSubset X.toLocallyRingedSpace E').stalkMap x) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3
  rw [← stalkMap_subsetPresheafedSpaceMap g E E' h x] at hrhs
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 hrhs

/-! ### The canonical embedding as a named morphism -/

/-- **The restriction of a locally ringed space to the whole of its space is the space itself**,
as an isomorphism. -/
def ofSubsetUnivIso (X : LocallyRingedSpace.{u}) :
    subsetLocallyRingedSpace X (Set.univ : Set X) ≅ X :=
  @asIso _ _ _ _ (ofSubsetHom X (Set.univ : Set X)) (isIso_ofSubsetHom_univ X)

/-- A morphism of schemes lands in the whole of its target. -/
lemma univ_subset_preimage_univ {T' T : Scheme.{u}} (a : T' ⟶ T) :
    (Set.univ : Set T') ⊆ a.base ⁻¹' (Set.univ : Set T) := fun _ _ ↦ Set.mem_univ _

/-- A morphism landing in a subset, followed by a morphism carrying that subset into another,
lands in the latter. -/
lemma univ_subset_preimage_comp {T Z Y : Scheme.{u}} (m : T ⟶ Z) (q : Z ⟶ Y) {E : Set Y}
    {E' : Set Z} (h : E' ⊆ q.base ⁻¹' E) (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E') :
    (Set.univ : Set T) ⊆ (m ≫ q).base ⁻¹' E := by
  intro x _
  have hx : (m ≫ q).base x = q.base (m.base x) := by rw [Scheme.Hom.comp_apply]
  rw [Set.mem_preimage, hx]
  exact h (hm (Set.mem_univ x))

/-- **The canonical embedding of [Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) at
the whole of a scheme**: the unit of the `Γ`–`Spec` adjunction at the restriction of the scheme to
its own space, read through the isomorphism of that restriction with the scheme. -/
def univΓSpecMap (T : Scheme.{u}) : T ⟶ Spec (T.sectionsRingOnSubset (Set.univ : Set T)) :=
  ⟨(ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
    (subsetLocallyRingedSpace T.toLocallyRingedSpace (Set.univ : Set T)).toΓSpec⟩

/-- **The canonical embedding of [Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
along a morphism landing in the subset**: for `m : T ⟶ Y` whose image lies in `E ⊆ Y`, the
morphism `T ⟶ Spec Γ(E, 𝒪_Y|_E)` induced by `m` and the embedding of `E`. -/
def subsetΓSpecLift {T Y : Scheme.{u}} (m : T ⟶ Y) (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E) : T ⟶ Spec (Y.sectionsRingOnSubset E) :=
  ⟨(ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
    subsetLocallyRingedSpaceMap m E (Set.univ : Set T) hm ≫
    (subsetLocallyRingedSpace Y.toLocallyRingedSpace E).toΓSpec⟩

/-- The canonical embedding does not depend on the morphism beyond its value, so a provable
equality of morphisms may be substituted even though the containment hypotheses differ. -/
lemma subsetΓSpecLift_congr {T Y : Scheme.{u}} {m m' : T ⟶ Y} (e : m = m') (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E) (hm' : (Set.univ : Set T) ⊆ m'.base ⁻¹' E) :
    subsetΓSpecLift m E hm = subsetΓSpecLift m' E hm' := by
  subst e
  rfl

/-- The canonical embedding along `m` is the embedding at the whole of the source followed by the
spectrum of the induced map on sections. -/
lemma subsetΓSpecLift_eq {T Y : Scheme.{u}} (m : T ⟶ Y) (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E) :
    subsetΓSpecLift m E hm = univΓSpecMap T ≫
      Spec.map (Scheme.sectionsRingOnSubsetMap m E (Set.univ : Set T) hm) := by
  refine Scheme.Hom.ext' ?_
  rw [Scheme.Hom.comp_toLRSHom]
  change (ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
      subsetLocallyRingedSpaceMap m E (Set.univ : Set T) hm ≫
        (subsetLocallyRingedSpace Y.toLocallyRingedSpace E).toΓSpec =
    ((ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
      (subsetLocallyRingedSpace T.toLocallyRingedSpace (Set.univ : Set T)).toΓSpec) ≫
        Spec.locallyRingedSpaceMap (Scheme.sectionsRingOnSubsetMap m E (Set.univ : Set T) hm)
  rw [Category.assoc, subsetLocallyRingedSpaceMap_comp_toΓSpec]
  rfl

/-- The embedding at the whole of a scheme, followed by the spectrum of the restriction of global
functions, is the canonical morphism to the spectrum of the global functions. -/
lemma univΓSpecMap_comp_specMap_topToSubset (T : Scheme.{u}) :
    univΓSpecMap T ≫ Spec.map (T.topToSubset (Set.univ : Set T)) = T.toSpecΓ := by
  refine Scheme.Hom.ext' ?_
  rw [Scheme.Hom.comp_toLRSHom]
  change ((ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
      (subsetLocallyRingedSpace T.toLocallyRingedSpace (Set.univ : Set T)).toΓSpec) ≫
        Spec.locallyRingedSpaceMap (T.topToSubset (Set.univ : Set T)) = T.toSpecΓ.toLRSHom
  have hnat : ofSubsetHom T.toLocallyRingedSpace (Set.univ : Set T) ≫ T.toSpecΓ.toLRSHom =
      (subsetLocallyRingedSpace T.toLocallyRingedSpace (Set.univ : Set T)).toΓSpec ≫
        Spec.locallyRingedSpaceMap (T.topToSubset (Set.univ : Set T)) := by
    rw [← Γ_map_ofSubsetHom T (Set.univ : Set T)]
    exact identityToΓSpec.naturality _
  rw [Category.assoc, ← hnat]
  exact (ofSubsetUnivIso T.toLocallyRingedSpace).inv_hom_id_assoc _

/-- **Naturality of the embedding at the whole of a scheme** in the scheme. -/
lemma comp_univΓSpecMap {T' T : Scheme.{u}} (a : T' ⟶ T) :
    a ≫ univΓSpecMap T = univΓSpecMap T' ≫
      Spec.map (Scheme.sectionsRingOnSubsetMap a (Set.univ : Set T) (Set.univ : Set T')
        (univ_subset_preimage_univ a)) := by
  refine Scheme.Hom.ext' ?_
  rw [Scheme.Hom.comp_toLRSHom, Scheme.Hom.comp_toLRSHom]
  change a.toLRSHom ≫ (ofSubsetUnivIso T.toLocallyRingedSpace).inv ≫
      (subsetLocallyRingedSpace T.toLocallyRingedSpace (Set.univ : Set T)).toΓSpec =
    ((ofSubsetUnivIso T'.toLocallyRingedSpace).inv ≫
      (subsetLocallyRingedSpace T'.toLocallyRingedSpace (Set.univ : Set T')).toΓSpec) ≫
        Spec.locallyRingedSpaceMap (Scheme.sectionsRingOnSubsetMap a (Set.univ : Set T)
          (Set.univ : Set T') (univ_subset_preimage_univ a))
  have hsq : subsetLocallyRingedSpaceMap a (Set.univ : Set T) (Set.univ : Set T')
        (univ_subset_preimage_univ a) ≫ (ofSubsetUnivIso T.toLocallyRingedSpace).hom =
      (ofSubsetUnivIso T'.toLocallyRingedSpace).hom ≫ a.toLRSHom :=
    LocallyRingedSpace.Hom.ext'
      (subsetPresheafedSpaceMap_comp_ofSubset a (Set.univ : Set T) (Set.univ : Set T')
        (univ_subset_preimage_univ a))
  rw [Category.assoc, ← subsetLocallyRingedSpaceMap_comp_toΓSpec a (Set.univ : Set T)
    (Set.univ : Set T') (univ_subset_preimage_univ a), (Iso.eq_comp_inv _).mpr hsq]
  simp only [Category.assoc]
  exact ((ofSubsetUnivIso T'.toLocallyRingedSpace).inv_hom_id_assoc _).symm

/-- **Naturality of the canonical embedding in the subset.** The embedding along `m` followed by
the spectrum of the map on sections induced by `q` is the embedding along `m ≫ q`. -/
@[reassoc]
lemma subsetΓSpecLift_comp_specMap_sectionsRingOnSubsetMap {T Z Y : Scheme.{u}} (m : T ⟶ Z)
    (q : Z ⟶ Y) (E : Set Y) (E' : Set Z) (h : E' ⊆ q.base ⁻¹' E)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E') :
    subsetΓSpecLift m E' hm ≫ Spec.map (Scheme.sectionsRingOnSubsetMap q E E' h) =
      subsetΓSpecLift (m ≫ q) E (univ_subset_preimage_comp m q h hm) := by
  rw [subsetΓSpecLift_eq, subsetΓSpecLift_eq, Category.assoc, ← Spec.map_comp,
    Scheme.sectionsRingOnSubsetMap_comp]

/-- **Naturality of the canonical embedding in the source.** -/
lemma comp_subsetΓSpecLift {T' T Y : Scheme.{u}} (a : T' ⟶ T) (m : T ⟶ Y) (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E) :
    a ≫ subsetΓSpecLift m E hm =
      subsetΓSpecLift (a ≫ m) E
        (univ_subset_preimage_comp a m hm (univ_subset_preimage_univ a)) := by
  rw [subsetΓSpecLift_eq, subsetΓSpecLift_eq, ← Category.assoc, comp_univΓSpecMap,
    Category.assoc, ← Spec.map_comp, Scheme.sectionsRingOnSubsetMap_comp]

/-- **The canonical embedding along a composite** is the first morphism followed by the embedding
along the second, with the containment hypothesis of the composite free. -/
lemma subsetΓSpecLift_comp_left {T' T Y : Scheme.{u}} (a : T' ⟶ T) (m : T ⟶ Y) (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E)
    (hm' : (Set.univ : Set T') ⊆ (a ≫ m).base ⁻¹' E) :
    subsetΓSpecLift (a ≫ m) E hm' = a ≫ subsetΓSpecLift m E hm :=
  (subsetΓSpecLift_congr rfl E hm' _).trans (comp_subsetΓSpecLift a m E hm).symm

/-- The canonical embedding along `m`, followed by the spectrum of the restriction of global
functions to the subset, is `m` followed by the canonical morphism to the spectrum of the global
functions. -/
lemma subsetΓSpecLift_comp_specMap_topToSubset {T Y : Scheme.{u}} (m : T ⟶ Y) (E : Set Y)
    (hm : (Set.univ : Set T) ⊆ m.base ⁻¹' E) :
    subsetΓSpecLift m E hm ≫ Spec.map (Y.topToSubset E) = m ≫ Y.toSpecΓ := by
  rw [subsetΓSpecLift_eq, Category.assoc, ← Spec.map_comp,
    Scheme.topToSubset_comp_sectionsRingOnSubsetMap, Spec.map_comp, ← Category.assoc,
    univΓSpecMap_comp_specMap_topToSubset, Scheme.toSpecΓ_naturality]

/-! ### The embedding of an open contained in the intersection -/

/-- The inclusion of an open contained in a subset lands in that subset. -/
lemma univ_subset_preimage_opensι {X : Scheme.{u}} (E : Set X) (W : X.Opens)
    (hWE : (W : Set X) ⊆ E) : (Set.univ : Set W.toScheme) ⊆ W.ι.base ⁻¹' E :=
  fun x _ ↦ hWE x.2

/-- **The canonical embedding of an open contained in the intersection, on points**: it sends a
point of the open to the image of the corresponding point of the intersection. -/
lemma subsetΓSpecLift_opensι_base {X : Scheme.{u}} (E : Set X) (W : X.Opens)
    (hWE : (W : Set X) ⊆ E) (x : W.toScheme) :
    (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)).base x =
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base ⟨x.1, hWE x.2⟩ := by
  have hcbase : ∀ y, (subsetLocallyRingedSpaceMap W.ι E (Set.univ : Set W.toScheme)
          (univ_subset_preimage_opensι E W hWE) ≫
        (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec).base y =
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base
        ⟨y.1.1, hWE y.1.2⟩ := fun _ ↦ rfl
  have hpt : ((ofSubsetUnivIso W.toScheme.toLocallyRingedSpace).inv.base x).1 = x :=
    inv_base_hom_base_apply (ofSubsetUnivIso W.toScheme.toLocallyRingedSpace).symm x
  have h := hcbase ((ofSubsetUnivIso W.toScheme.toLocallyRingedSpace).inv.base x)
  rwa [hpt] at h

/-- **The canonical embedding of an intersection of quasi-compact opens in an ind-quasi-affine
scheme, restricted to an open contained in the intersection, is an open immersion of schemes.** -/
theorem isOpenImmersion_subsetΓSpecLift_opensι (X : Scheme.{u}) [IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) (W : X.Opens) (hWE : (W : Set X) ⊆ E) :
    IsOpenImmersion (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)) := by
  set hsub := univ_subset_preimage_opensι E W hWE
  set n := subsetLocallyRingedSpaceMap W.ι E (Set.univ : Set W.toScheme) hsub
  set jE := (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec
  have hcbase : ∀ y, (n ≫ jE).base y = jE.base ⟨y.1.1, hWE y.1.2⟩ := fun _ ↦ rfl
  have hcstalk : ∀ y, IsIso ((n ≫ jE).stalkMap y) := by
    intro y
    rw [LocallyRingedSpace.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_stalkMap_toΓSpec_subsetLocallyRingedSpace X U hU E hE (n.base y))
      (isIso_stalkMap_subsetLocallyRingedSpaceMap W.ι E (Set.univ : Set W.toScheme) hsub y)
  have hinjc : Function.Injective (n ≫ jE).base.hom := by
    intro a b hab
    rw [hcbase a, hcbase b] at hab
    have h₁ := congrArg Subtype.val
      (injective_toΓSpec_base_subsetLocallyRingedSpace X U hU E hE hab)
    exact Subtype.ext (Subtype.ext h₁)
  have hopenc : IsOpenMap (n ≫ jE).base.hom := by
    intro A hA
    obtain ⟨B, hB, hAB⟩ := isOpen_induced_iff.mp hA
    obtain ⟨Ω, hΩ, hBΩ⟩ := isOpen_induced_iff.mp hB
    have himg : (n ≫ jE).base.hom '' A = subsetΓSpecImage X E (Ω ∩ (W : Set X)) := by
      ext t
      constructor
      · rintro ⟨y, hyA, rfl⟩
        exact ⟨⟨y.1.1, hWE y.1.2⟩, ⟨(Set.ext_iff.mp hBΩ y.1).mpr ((Set.ext_iff.mp hAB y).mpr hyA),
          y.1.2⟩, (hcbase y).symm⟩
      · rintro ⟨z, ⟨hzΩ, hzW⟩, rfl⟩
        exact ⟨⟨⟨z.1, hzW⟩, Set.mem_univ _⟩,
          (Set.ext_iff.mp hAB _).mp ((Set.ext_iff.mp hBΩ _).mp hzΩ), hcbase _⟩
    rw [himg]
    exact isOpen_image_toΓSpec_of_isOpen X U hU E (Ω ∩ (W : Set X)) hE
      (fun _ hx => hWE hx.2) (hΩ.inter W.2)
  have hoic : LocallyRingedSpace.IsOpenImmersion (n ≫ jE) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
      (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        (n ≫ jE).base.hom.continuous hinjc hopenc)
  exact LocallyRingedSpace.IsOpenImmersion.comp
    ((ofSubsetUnivIso W.toScheme.toLocallyRingedSpace).inv) (n ≫ jE)

/-- **The range of the canonical embedding of an open contained in the intersection is the image
of that open** under the embedding of the intersection. -/
theorem range_subsetΓSpecLift_opensι {X : Scheme.{u}} (E : Set X) (W : X.Opens)
    (hWE : (W : Set X) ⊆ E) :
    Set.range (subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE)).base =
      subsetΓSpecImage X E (W : Set X) := by
  have hpt := subsetΓSpecLift_opensι_base E W hWE
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.1, hWE x.2⟩, x.2, (hpt x).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z.1, hz⟩, hpt _⟩

/-- **The canonical embedding of an intersection of quasi-compact opens restricted to an open is
an open immersion of schemes onto its image**, compatibly with the restriction of global functions
to the intersection. -/
theorem exists_isOpenImmersion_range_eq_subsetΓSpecImage (X : Scheme.{u}) [IsIndQuasiAffine X]
    {I : Type v} [Nonempty I] (U : I → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) (W : X.Opens) (hWE : (W : Set X) ⊆ E) :
    ∃ k : W.toScheme ⟶ Spec (X.sectionsRingOnSubset E),
      IsOpenImmersion k ∧
      (∀ x : W.toScheme, k.base x =
        (subsetLocallyRingedSpace X.toLocallyRingedSpace E).toΓSpec.base ⟨x.1, hWE x.2⟩) ∧
      Set.range k.base = subsetΓSpecImage X E (W : Set X) ∧
      k ≫ Spec.map (X.topToSubset E) = W.ι ≫ X.toSpecΓ :=
  ⟨subsetΓSpecLift W.ι E (univ_subset_preimage_opensι E W hWE),
    isOpenImmersion_subsetΓSpecLift_opensι X U hU E hE W hWE,
    subsetΓSpecLift_opensι_base E W hWE, range_subsetΓSpecLift_opensι E W hWE,
    subsetΓSpecLift_comp_specMap_topToSubset W.ι E (univ_subset_preimage_opensι E W hWE)⟩

end AlgebraicGeometry

end

end
