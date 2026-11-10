module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FlasqueSoftUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Softness of the restriction of an inverse image to the fibres of a base change

Let `f : X ⟶ Y` be a map of spaces whose fibres are quasi-compact and whose points are separated,
let `k : W ⟶ Y` be another map and let

```
X' --g--> X
|         |
f'        f
v         v
W --k---> Y
```

present `X'` as the fibre product `W ×_Y X`. Let `J` be a **flasque** abelian sheaf on `X`. The
topological half of proper base change ([Stacks, Tag 0DCU]) needs the restriction of `g^{-1} J` to
each fibre of `f'` to be **soft**, which is the hypothesis of
`Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` and of
`Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber`.

Neither of the two sufficient conditions already in the library applies on the nose: `g^{-1} J` is
not flasque, and `Stacks.Topology.isSoft_restrictionFunctorUnivLE_of_isFlasque` proves softness
only for a restriction of a flasque sheaf *to a subset of its own space*. What is missing is a
**transport of softness along a homeomorphism**, and that is what this file supplies: `g` carries
the fibre `f'^{-1}(w)` homeomorphically onto the fibre `f^{-1}(k w)`, and the restriction of
`g^{-1} J` to the first fibre is the inverse image, along that homeomorphism, of the restriction
of `J` to the second — which is soft because `J` is flasque.

The transport is assembled from the adjunctions, not from any computation of an inverse image:

* the inverse image is the left adjoint of the direct image
  (`CategoryTheory.Functor.sheafAdjunctionContinuous`), and the direct image along a composite is
  *definitionally* the composite of the direct images, because `TopologicalSpace.Opens.map` turns a
  composite into a composite by `rfl`
  (`TopologicalSpace.Opens.map_comp_eq`). So `inverseImageSquareIso` is
  `CategoryTheory.Adjunction.leftAdjointUniq` applied to two composite adjunctions with the *same*
  right adjoint, the two spellings of that right adjoint being identified by
  `CategoryTheory.Functor.sheafPushforwardContinuousIso`;
* along an isomorphism of spaces the inverse image is the *direct* image along the inverse
  (`inverseImageIsoDirectImageUnivLE`), again by uniqueness of left adjoints — and the direct image
  is concrete: its sections over `U` are the sections of the original over the preimage of `U`. So
  softness transports by hand, with no eqToHom gymnastics.

## Main definitions

All in the namespace `Stacks.Topology`.

* `directImageUnivLE`, `inverseImageUnivLE`: the direct and inverse images of abelian sheaves along
  a continuous map, at a coefficient universe independent of the space. The second is
  `Stacks.Topology.restrictionFunctorUnivLE` for an arbitrary map in place of the inclusion of a
  subset.
* `fiberHomeoOfPullbackPresentation`, `fiberIsoOfPullbackPresentation`: the homeomorphism
  `f'^{-1}(w) ≅ f^{-1}(k w)` induced by `g`, read off a presentation of `X'` as the subspace of
  `W × X` cut out by `k p.1 = f p.2` — the presentation
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_sitePullback_homeo` produces.

## Main results

* `IsSoft.directImage_of_iso`: **softness transports along a homeomorphism**, for the direct image
  along the inverse. This is the one step that needs the definition of softness; everything else is
  formal.
* `inverseImageIsoDirectImageUnivLE`, `inverseImageSquareIso`: the two identifications of inverse
  images described above.
* `isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo`: **the transport.** If `g` carries a
  subset `Z₁ ⊆ X₁` homeomorphically onto `Z₂ ⊆ X₂` and the restriction of `F` to `Z₂` is soft, then
  the restriction of `g^{-1} F` to `Z₁` is soft.
* `isSoft_restrictionFunctorUnivLE_inverseImage_of_isFlasque`: the same for a flasque `F`, the
  softness over `Z₂` being supplied by
  `Stacks.Topology.isSoft_restrictionFunctorUnivLE_of_isFlasque`.
* `isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque`: **the deliverable** — for a base change
  square presented as above and a flasque `J`, the restriction of `g^{-1} J` to every fibre of `f'`
  is soft. This is exactly the fibrewise hypothesis of
  `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber`.

## Implementation notes

`CategoryTheory.Equivalence.toAdjunction` states its type in terms of the equivalence's own
`functor` and `inverse` fields, and instance search for
`CategoryTheory.Functor.IsContinuous` does not see through them, so the adjunction of
`TopologicalSpace.Opens.map` functors attached to an isomorphism of spaces is introduced by the
named `opensMapAdjunctionOfIso`, whose *stated* type is the one instance search needs. A type
ascription at the use site is not enough: the ascribed term keeps its own type, and the
`IsContinuous` argument is then synthesised against `(Opens.mapMapIso φ).symm.functor`.

Softness is transported with no `eqToHom`: given a neighbourhood `V'` of the transported closed set
in the second space, the open `V` of the first space is the preimage of `V'`, whose own preimage
`V''` back in the second space is only *propositionally* `V'`. Rather than identify them, the
established equality of sections over `V'` is restricted further to `V''`, which is `≤ V'`; the
restriction maps of a direct image are the restriction maps of the original sheaf along
`Opens.map`, and `Opens` is a poset, so the resulting statement is the goal on the nose.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the tag
is not complete until all of them are in the library.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe t s

noncomputable section

/-- **The direct image of abelian sheaves along a continuous map, at a coefficient universe
independent of the space.** Its sections over an open `U` of the target are the sections of the
original sheaf over the preimage of `U`. -/
abbrev directImageUnivLE {X Y : TopCat.{s}} (g : X ⟶ Y) :
    X.Sheaf AddCommGrpCat.{t} ⥤ Y.Sheaf AddCommGrpCat.{t} :=
  (Opens.map g).sheafPushforwardContinuous AddCommGrpCat.{t}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The adjunction of `TopologicalSpace.Opens.map` functors attached to an isomorphism of spaces.
It is introduced as a named declaration, rather than by a type ascription on
`CategoryTheory.Equivalence.toAdjunction`, because the ascribed term would keep its own type and
instance search for `CategoryTheory.Functor.IsContinuous` does not see through the `functor` field
of an equivalence. -/
def opensMapAdjunctionOfIso {Z₁ Z₂ : TopCat.{s}} (φ : Z₁ ≅ Z₂) :
    Opens.map φ.inv ⊣ Opens.map φ.hom :=
  (Opens.mapMapIso φ).symm.toAdjunction

/-- **Softness transports along a homeomorphism.** If `H` is a soft abelian sheaf on `Z₂` and
`φ : Z₁ ≅ Z₂` is an isomorphism of spaces, the direct image of `H` along `φ.inv` is a soft sheaf on
`Z₁`: its sections over an open `U` are the sections of `H` over the preimage of `U`, so an
extension of a section is transported by taking preimages in both directions. -/
theorem IsSoft.directImage_of_iso {Z₁ Z₂ : TopCat.{s}} (φ : Z₁ ≅ Z₂)
    {H : Z₂.Sheaf AddCommGrpCat.{t}} (hH : IsSoft H) :
    IsSoft ((directImageUnivLE.{t} φ.inv).obj H) := by
  have hhi : ∀ x : Z₁, (φ.inv.hom : Z₂ → Z₁) ((φ.hom.hom : Z₁ → Z₂) x) = x := fun x ↦
    ConcreteCategory.congr_hom φ.hom_inv_id x
  have hih : ∀ y : Z₂, (φ.hom.hom : Z₁ → Z₂) ((φ.inv.hom : Z₂ → Z₁) y) = y := fun y ↦
    ConcreteCategory.congr_hom φ.inv_hom_id y
  intro K hK U hKU s
  obtain ⟨u, V', hV'U', hK'V', hres⟩ := hH ((φ.inv.hom : Z₂ → Z₁) ⁻¹' K)
    (hK.preimage φ.inv.hom.continuous) ((Opens.map φ.inv).obj U) (fun _ hy ↦ hKU hy) s
  refine ⟨u, (Opens.map φ.hom).obj V', fun x hx ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have h2 : (φ.inv.hom : Z₂ → Z₁) ((φ.hom.hom : Z₁ → Z₂) x) ∈ U := hV'U' hx
    rw [hhi x] at h2
    exact h2
  · change (φ.hom.hom : Z₁ → Z₂) x ∈ V'
    refine hK'V' ?_
    change (φ.inv.hom : Z₂ → Z₁) ((φ.hom.hom : Z₁ → Z₂) x) ∈ K
    rw [hhi x]
    exact hx
  · have hV'' : (Opens.map φ.inv).obj ((Opens.map φ.hom).obj V') ≤ V' := by
      intro y hy
      have h1 : (φ.hom.hom : Z₁ → Z₂) ((φ.inv.hom : Z₂ → Z₁) y) ∈ V' := hy
      rw [hih y] at h1
      exact h1
    change TopCat.Presheaf.restrict (F := H.obj) u _ = _
    refine Eq.trans (TopCat.Presheaf.restrict_restrict (F := H.obj) hV''
      (le_top : V' ≤ ⊤) u).symm ?_
    refine Eq.trans (congrArg
      (fun z ↦ TopCat.Presheaf.restrict (F := H.obj) z (homOfLE hV'')) hres) ?_
    exact TopCat.Presheaf.restrict_restrict (F := H.obj) hV'' hV'U' s

variable [UnivLE.{s, t}]

/-- **The inverse image of abelian sheaves along a continuous map, at a coefficient universe
independent of the space.** This is `Stacks.Topology.restrictionFunctorUnivLE` with the inclusion
of a subset replaced by an arbitrary map. -/
abbrev inverseImageUnivLE {X Y : TopCat.{s}} (g : X ⟶ Y) :
    Y.Sheaf AddCommGrpCat.{t} ⥤ X.Sheaf AddCommGrpCat.{t} :=
  (Opens.map g).sheafPullback AddCommGrpCat.{t}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- **The inverse image is left adjoint to the direct image**, at a coefficient universe
independent of the space. This is `CategoryTheory.Functor.sheafAdjunctionContinuous` for
`TopologicalSpace.Opens.map`. -/
def inverseImageAdjunctionUnivLE {X Y : TopCat.{s}} (g : X ⟶ Y) :
    inverseImageUnivLE.{t} g ⊣ directImageUnivLE.{t} g :=
  Functor.sheafAdjunctionContinuous (Opens.map g) AddCommGrpCat.{t}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- **Along an isomorphism of spaces the inverse image is the direct image along the inverse.**
Both are left adjoint to the direct image along `φ.hom`: the first by
`inverseImageAdjunctionUnivLE`, the second because the two `Opens.map` functors of an isomorphism
are adjoint, so `CategoryTheory.Adjunction.sheafPushforwardContinuous` applies. -/
def inverseImageIsoDirectImageUnivLE {Z₁ Z₂ : TopCat.{s}} (φ : Z₁ ≅ Z₂) :
    inverseImageUnivLE.{t} φ.hom ≅ directImageUnivLE.{t} φ.inv :=
  Adjunction.leftAdjointUniq (inverseImageAdjunctionUnivLE.{t} φ.hom)
    (Adjunction.sheafPushforwardContinuous (E := AddCommGrpCat.{t}) (opensMapAdjunctionOfIso φ)
      (Opens.grothendieckTopology Z₁) (Opens.grothendieckTopology Z₂))

/-- **Softness transports along a homeomorphism, for the inverse image.** This is
`IsSoft.directImage_of_iso` carried across `inverseImageIsoDirectImageUnivLE` by
`Stacks.Topology.IsSoft.of_iso`. -/
theorem IsSoft.inverseImage_of_iso {Z₁ Z₂ : TopCat.{s}} (φ : Z₁ ≅ Z₂)
    {H : Z₂.Sheaf AddCommGrpCat.{t}} (hH : IsSoft H) :
    IsSoft ((inverseImageUnivLE.{t} φ.hom).obj H) :=
  IsSoft.of_iso ((inverseImageIsoDirectImageUnivLE.{t} φ).app H).symm
    (IsSoft.directImage_of_iso.{t} φ hH)

/-- **A commuting square whose vertical maps are isomorphisms of the fibres gives one
identification of inverse images.** Both composites are left adjoint to the direct image along the
diagonal of the square: the direct image of a composite is *definitionally* the composite of the
direct images, because `TopologicalSpace.Opens.map` sends a composite to a composite by `rfl`, and
the two spellings `ι₁ ≫ g` and `φ.hom ≫ ι₂` of that diagonal are identified by
`CategoryTheory.Functor.sheafPushforwardContinuousIso` applied to
`TopologicalSpace.Opens.mapIso`. -/
def inverseImageSquareIso {X₁ X₂ Z₁ Z₂ : TopCat.{s}}
    (ι₁ : Z₁ ⟶ X₁) (g : X₁ ⟶ X₂) (φ : Z₁ ≅ Z₂) (ι₂ : Z₂ ⟶ X₂)
    (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂) :
    inverseImageUnivLE.{t} g ⋙ inverseImageUnivLE.{t} ι₁ ≅
      inverseImageUnivLE.{t} ι₂ ⋙ inverseImageUnivLE.{t} φ.hom :=
  Adjunction.leftAdjointUniq
    (((inverseImageAdjunctionUnivLE.{t} g).comp (inverseImageAdjunctionUnivLE.{t} ι₁) :
      inverseImageUnivLE.{t} g ⋙ inverseImageUnivLE.{t} ι₁ ⊣
        directImageUnivLE.{t} (ι₁ ≫ g)))
    (Adjunction.ofNatIsoRight
      (((inverseImageAdjunctionUnivLE.{t} ι₂).comp (inverseImageAdjunctionUnivLE.{t} φ.hom) :
        inverseImageUnivLE.{t} ι₂ ⋙ inverseImageUnivLE.{t} φ.hom ⊣
          directImageUnivLE.{t} (φ.hom ≫ ι₂)))
      (Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm) AddCommGrpCat.{t}
        (Opens.grothendieckTopology X₂) (Opens.grothendieckTopology Z₁)))

/-- **Softness transports along a homeomorphism of subsets induced by a map of ambient spaces.**
If `g : X₁ ⟶ X₂` carries a subset `Z₁` of `X₁` homeomorphically onto a subset `Z₂` of `X₂` — which
is what `hcomm` says, `φ` being the homeomorphism — and the restriction of `F` to `Z₂` is soft,
then the restriction of `g^{-1} F` to `Z₁` is soft. -/
theorem isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo {X₁ X₂ : TopCat.{s}} (g : X₁ ⟶ X₂)
    (Z₁ : Set X₁) (Z₂ : Set X₂) (φ : TopCat.of Z₁ ≅ TopCat.of Z₂)
    (hcomm : Stacks.subsetInclusion X₁ Z₁ ≫ g = φ.hom ≫ Stacks.subsetInclusion X₂ Z₂)
    {F : X₂.Sheaf AddCommGrpCat.{t}}
    (hsoft : IsSoft ((restrictionFunctorUnivLE.{t} X₂ Z₂).obj F)) :
    IsSoft ((restrictionFunctorUnivLE.{t} X₁ Z₁).obj ((inverseImageUnivLE.{t} g).obj F)) :=
  IsSoft.of_iso ((inverseImageSquareIso.{t} (Stacks.subsetInclusion X₁ Z₁) g φ
      (Stacks.subsetInclusion X₂ Z₂) hcomm).app F).symm
    (IsSoft.inverseImage_of_iso.{t} φ hsoft)

/-- **The restriction of the inverse image of a flasque sheaf to a subset carried
homeomorphically onto a quasi-compact subset with separated points is soft.** The softness over
`Z₂` is `Stacks.Topology.isSoft_restrictionFunctorUnivLE_of_isFlasque`; what is added is the
transport of `isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo`. -/
@[sga "4 Vbis 4.1.5" "more general"]
theorem isSoft_restrictionFunctorUnivLE_inverseImage_of_isFlasque {X₁ X₂ : TopCat.{s}}
    (g : X₁ ⟶ X₂) (Z₁ : Set X₁) (Z₂ : Set X₂) (φ : TopCat.of Z₁ ≅ TopCat.of Z₂)
    (hcomm : Stacks.subsetInclusion X₁ Z₁ ≫ g = φ.hom ≫ Stacks.subsetInclusion X₂ Z₂)
    (F : X₂.Sheaf AddCommGrpCat.{t}) [TopCat.Sheaf.IsFlasque F] (hZ₂ : IsCompact Z₂)
    (hSep : ∀ x ∈ Z₂, ∀ y ∈ Z₂, x ≠ y →
      ∃ A B : Set X₂, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsSoft ((restrictionFunctorUnivLE.{t} X₁ Z₁).obj ((inverseImageUnivLE.{t} g).obj F)) :=
  isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo.{t} g Z₁ Z₂ φ hcomm
    (isSoft_restrictionFunctorUnivLE_of_isFlasque.{t} F Z₂ hZ₂ hSep)

end

section Fibre

variable {X Y W X' : TopCat.{s}} (f : X ⟶ Y) (k : W ⟶ Y) (f' : X' ⟶ W) (g : X' ⟶ X)
  (e : X' ≃ₜ {p : W × X // (k.hom : W → Y) p.1 = (f.hom : X → Y) p.2})
  (he : ∀ q : X', (e q : W × X) = ((f'.hom : X' → W) q, (g.hom : X' → X) q))

include e he in
/-- **A presentation of `X'` as the subspace of `W × X` cut out by `k p.1 = f p.2`, compatible
with the two projections, makes the square commute on points.** The condition defining the
subspace *is* the commutation, read at the pair of coordinates of a point. -/
theorem apply_comp_eq_of_pullbackPresentation (q : X') :
    (f.hom : X → Y) ((g.hom : X' → X) q) = (k.hom : W → Y) ((f'.hom : X' → W) q) := by
  have h := (e q).2
  rw [he q] at h
  exact h.symm

include e he in
/-- The second projection carries the fibre of `f'` over `w` into the fibre of `f` over `k w`. -/
theorem map_mem_fiber_of_pullbackPresentation (w : W)
    (q : ((f'.hom : X' → W) ⁻¹' ({w} : Set W))) :
    (g.hom : X' → X) q.1 ∈ ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y)) := by
  have hq : (f'.hom : X' → W) q.1 = w := q.2
  change (f.hom : X → Y) ((g.hom : X' → X) q.1) = (k.hom : W → Y) w
  rw [apply_comp_eq_of_pullbackPresentation f k f' g e he q.1, hq]

/-- A point of the fibre of `f` over `k w`, paired with `w`, satisfies the condition cutting the
fibre product out of the product. -/
theorem fiberPairCondition (w : W)
    (x : ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y))) :
    (k.hom : W → Y) ((w, x.1) : W × X).1 = (f.hom : X → Y) ((w, x.1) : W × X).2 := by
  have hx : (f.hom : X → Y) x.1 = (k.hom : W → Y) w := x.2
  exact hx.symm

include he in
/-- The point of `X'` with coordinates `w` and a point of the fibre of `f` over `k w` lies in the
fibre of `f'` over `w`. -/
theorem symm_mem_fiber_of_pullbackPresentation (w : W)
    (x : ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y))) :
    e.symm ⟨(w, x.1), fiberPairCondition f k w x⟩ ∈ ((f'.hom : X' → W) ⁻¹' ({w} : Set W)) := by
  have hval := he (e.symm ⟨(w, x.1), fiberPairCondition f k w x⟩)
  rw [Homeomorph.apply_symm_apply] at hval
  exact (congrArg Prod.fst hval).symm

/-- **The fibres of a base change are the fibres of the original map.** Read off a presentation of
`X'` as the subspace of `W × X` cut out by `k p.1 = f p.2`, compatibly with the two projections
`f'` and `g` — the presentation
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_sitePullback_homeo` produces — the
second projection `g` carries `f'^{-1}(w)` homeomorphically onto `f^{-1}(k w)`, with inverse
`x ↦ (w, x)`. -/
def fiberHomeoOfPullbackPresentation (w : W) :
    ((f'.hom : X' → W) ⁻¹' ({w} : Set W)) ≃ₜ
      ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y)) where
  toFun q := ⟨(g.hom : X' → X) q.1, map_mem_fiber_of_pullbackPresentation f k f' g e he w q⟩
  invFun x := ⟨e.symm ⟨(w, x.1), fiberPairCondition f k w x⟩,
    symm_mem_fiber_of_pullbackPresentation f k f' g e he w x⟩
  left_inv q := by
    refine Subtype.ext ?_
    have hq : (f'.hom : X' → W) q.1 = w := q.2
    refine Eq.trans (congrArg e.symm (Subtype.ext ?_)) (e.symm_apply_apply q.1)
    rw [he q.1, hq]
  right_inv x := by
    refine Subtype.ext ?_
    have hval := he (e.symm ⟨(w, x.1), fiberPairCondition f k w x⟩)
    rw [Homeomorph.apply_symm_apply] at hval
    exact (congrArg Prod.snd hval).symm
  continuous_toFun :=
    Continuous.subtype_mk (g.hom.continuous.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (e.symm.continuous.comp
        (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _)) _

/-- The homeomorphism of `fiberHomeoOfPullbackPresentation` as an isomorphism in `TopCat`, which is
the shape `isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo` consumes. -/
def fiberIsoOfPullbackPresentation (w : W) :
    TopCat.of ((f'.hom : X' → W) ⁻¹' ({w} : Set W)) ≅
      TopCat.of ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y)) :=
  TopCat.isoOfHomeo (fiberHomeoOfPullbackPresentation f k f' g e he w)

/-- The fibre isomorphism is induced by `g`: the two ways of mapping the fibre `f'^{-1}(w)` into
`X` agree. This is the hypothesis `hcomm` of
`isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo`. -/
theorem subsetInclusion_comp_fiberIsoOfPullbackPresentation (w : W) :
    Stacks.subsetInclusion X' ((f'.hom : X' → W) ⁻¹' ({w} : Set W)) ≫ g =
      (fiberIsoOfPullbackPresentation f k f' g e he w).hom ≫
        Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(k.hom : W → Y) w} : Set Y)) := by
  refine ConcreteCategory.hom_ext _ _ fun q ↦ ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rfl

variable [UnivLE.{s, t}]

include k e he in
/-- **The restriction of the inverse image of a flasque sheaf to every fibre of a base change is
soft.** This is the second ingredient of clause 8 of [Stacks, Tag 0DCU]: `g` carries the fibre
`f'^{-1}(w)` homeomorphically onto the fibre `f^{-1}(k w)`
(`fiberIsoOfPullbackPresentation`), the restriction of the flasque `J` to that fibre is soft
(`Stacks.Topology.isSoft_restrictionFunctorUnivLE_of_isFlasque`), and softness transports
(`isSoft_restrictionFunctorUnivLE_inverseImage_of_homeo`).

The conclusion is exactly the fibrewise hypothesis of
`Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` and of
`Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber` for the map `f'` and the sheaf
`g^{-1} J`, so those two vanishing theorems apply to `g^{-1} J` once `f'` is known to be closed
with quasi-compact separated fibres. -/
@[sga "4 Vbis 4.1.5" "special case"]
theorem isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque
    (J : X.Sheaf AddCommGrpCat.{t}) [TopCat.Sheaf.IsFlasque J]
    (hcpt : ∀ y : Y, IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
    (hsep : IsSeparatedMap (f.hom : X → Y)) (w : W) :
    IsSoft ((restrictionFunctorUnivLE.{t} X' ((f'.hom : X' → W) ⁻¹' ({w} : Set W))).obj
      ((inverseImageUnivLE.{t} g).obj J)) := by
  refine isSoft_restrictionFunctorUnivLE_inverseImage_of_isFlasque.{t} g _ _
    (fiberIsoOfPullbackPresentation f k f' g e he w)
    (subsetInclusion_comp_fiberIsoOfPullbackPresentation f k f' g e he w) J
    (hcpt ((k.hom : W → Y) w)) ?_
  intro x hx y hy hxy
  refine hsep x y ?_ hxy
  have hx' : (f.hom : X → Y) x = (k.hom : W → Y) w := hx
  have hy' : (f.hom : X → Y) y = (k.hom : W → Y) w := hy
  rw [hx', hy']

end Fibre

end Stacks.Topology

end
