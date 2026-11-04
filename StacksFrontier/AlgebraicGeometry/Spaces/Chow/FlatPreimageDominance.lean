module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A component of a flat inverse image dominates the subspace

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` with `Y` decent, and let
`Z ⊆ Y` be an integral closed subspace. Then every irreducible component `Z'` of `f^{-1}(Z)`
**dominates** `Z`: a generic point of `|Z'|` is carried by `f` to a generic point of `|Z|`.

## Main results

* `AlgebraicGeometry.Space.FlatPreimage.isGenericPoint_map_of_generalizingMap`: the
  topological core. For a continuous map along which generizations lift, a generic point of an
  irreducible component of the inverse image of a set with a generic point is carried to a
  generic point of that set.
* `AlgebraicGeometry.Space.FlatPreimage.generalizingMap_pointsMap_of_isFlat`: generizations
  lift along the map on points of a flat morphism of algebraic spaces over `S` with decent
  target.
* `AlgebraicGeometry.Space.FlatPreimage.isGenericPoint_pointsMap_preimageComponent_of_isFlat`:
  the dominance clause itself, for an integral closed subspace of a decent algebraic space.
* `AlgebraicGeometry.Space.FlatPreimage.isGenericPoint_pointsMap_preimageComponent_of_isGood`:
  the same statement in Situation 0EDT, for good spaces over the base.

## Implementation notes

**Flatness lifts generizations.** Stacks proves the clause from openness of a flat morphism
locally of finite presentation (Tag 042S), which forces a generic point of a component to go to
the generic point because the components of the inverse image are locally finite and so one of
them carries an open set. Lifting generizations is the weaker input and it suffices on its own:
if `ξ` is a generic point of a component of `|f^{-1}(Z)|` then `f ξ` lies in `|Z| = closure {η}`,
so `η` is a generization of `f ξ` and lifts to a generization `ξ'` of `ξ` inside `f^{-1}(Z)`; the
closure of `ξ'` is then an irreducible subset of `|f^{-1}(Z)|` containing the component, hence is
that component, so `ξ'` is also a specialization of `ξ` and `η = f ξ'` is a specialization of
`f ξ`. The two specializations give `closure {f ξ} = closure {η} = |Z|`.

Consequently **neither local finiteness of the components nor the Kolmogorov property of `|Y|`
nor local Noetherianness is used**, in contrast with the étale case
(`AlgebraicGeometry.Space.IntegralClosedSubspace.isGenericPoint_pointsMap_of_isGenericPoint`),
and the relative-dimension hypothesis of Tag 0EP5 is not needed for this clause either: `f` is
only required to be flat. The counterexample recorded with the étale case — the map from
`{0} ∪ {1/n}` to the Sierpiński space — is not a counterexample here, since generizations do
not lift along it.

**Where flatness enters.** Generizations lift along the map on points by reduction to a
commuting square of étale charts: condition (8) of Tag 03MM provides a square
`p ≫ f = h ≫ q` with `p : h_U ⟶ X` surjective étale, `q : h_V ⟶ Y` étale and the morphism of
schemes `h : U ⟶ V` flat. A point of `|X|` is lifted to `|U|` by surjectivity of `p` on points;
a generization of its image in `|Y|` is lifted to `|V|` by Tag 03K2,
`AlgebraicGeometry.Space.generalizingMap_pointsMap_of_isDecentSpace`, which is where decency of
the target is used; that generization is lifted to `|U|` by going down along the flat morphism
of schemes, Mathlib's `AlgebraicGeometry.Flat.generalizingMap`, read through the homeomorphism
of Tag 03BX, clause (1), between the points of a represented presheaf and the points of the
representing scheme; and its image in `|X|` is the required generization, by continuity of `p`
on points and commutativity of the square.

Flatness of the morphism of schemes in the square is obtained from the every-chart condition on
`h` at the square of identity charts, which is admissible because the identity of a represented
presheaf is étale.

## References

* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.FlatPreimage

/-! ### The topological core -/

/-- **A generic point of a component of an inverse image goes to a generic point, for a map
along which generizations lift.** Let `φ : α → β` be continuous with `GeneralizingMap φ`, let
`ξ` be a generic point of a subset `V` of `β`, let `C` be an irreducible component of
`φ ⁻¹' V` and let `x` be a generic point of the image of `C` in `α`. Then `φ x` is a generic
point of `V`. -/
@[ega "IV 2.3.4" "(i) ⇒ (iii)", ega "IV 2.3.5" "partial"]
theorem isGenericPoint_map_of_generalizingMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {φ : α → β} (hcont : Continuous φ) (hgen : GeneralizingMap φ)
    {V : Set β} {ξ : β} (hξ : IsGenericPoint ξ V)
    (C : irreducibleComponents (φ ⁻¹' V)) {x : α}
    (hx : IsGenericPoint x (Subtype.val '' (C : Set (φ ⁻¹' V)))) :
    IsGenericPoint (φ x) V := by
  have hTclosed : IsClosed (φ ⁻¹' V) := hξ.isClosed.preimage hcont
  obtain ⟨c, -, hcx⟩ := hx.mem
  have hxT : x ∈ φ ⁻¹' V := hcx ▸ c.2
  have h1 : ξ ⤳ φ x := hξ.specializes hxT
  obtain ⟨x', hx'x, hx'ξ⟩ := hgen h1
  have hx'T : x' ∈ φ ⁻¹' V := by
    rw [Set.mem_preimage, hx'ξ]
    exact hξ.mem
  set C' : irreducibleComponents (φ ⁻¹' V) :=
    ⟨irreducibleComponent (⟨x', hx'T⟩ : φ ⁻¹' V),
      irreducibleComponent_mem_irreducibleComponents _⟩
  have hC'closed : IsClosed (Subtype.val '' (C' : Set (φ ⁻¹' V))) :=
    hTclosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C'.2)
  have hx'C' : x' ∈ Subtype.val '' (C' : Set (φ ⁻¹' V)) :=
    ⟨⟨x', hx'T⟩, mem_irreducibleComponent, rfl⟩
  have hxC' : x ∈ Subtype.val '' (C' : Set (φ ⁻¹' V)) :=
    closure_minimal (Set.singleton_subset_iff.2 hx'C') hC'closed hx'x.mem_closure
  have hCC' : Subtype.val '' (C : Set (φ ⁻¹' V)) ⊆ Subtype.val '' (C' : Set (φ ⁻¹' V)) := by
    rw [← hx.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hxC') hC'closed
  have hsub : (C : Set (φ ⁻¹' V)) ⊆ (C' : Set (φ ⁻¹' V)) :=
    (Set.image_subset_image_iff Subtype.val_injective).1 hCC'
  have hxx' : x ⤳ x' := by
    refine specializes_iff_mem_closure.2 ?_
    rw [hx.def]
    exact Set.image_mono (C.2.2 C'.2.1 hsub) hx'C'
  have h2 : φ x ⤳ ξ := hx'ξ ▸ hxx'.map hcont
  rw [isGenericPoint_def, ← hξ.def]
  exact inseparable_iff_closure_eq.1 (inseparable_iff_specializes_and.2 ⟨h2, h1⟩)

/-! ### Generizations lift along a flat morphism of algebraic spaces -/

section Flat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Generizations lift along the map on points of a flat morphism.** Let `f : X ⟶ Y` be a
flat morphism of algebraic spaces over `S` with `Y` decent. Then the map `|X| → |Y|` is a
generalizing map: every generization of the image of a point of `|X|` is the image of a
generization of that point. -/
theorem generalizingMap_pointsMap_of_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) {f : X ⟶ Y}
    (hflat : IsFlat B S hS f) :
    GeneralizingMap (pointsMap B S hS X f) := by
  obtain ⟨U, V, p, q, h, hpEt, hqEt, hpSurj, hsq, hhFlat⟩ :=
    ((isFlat_tfae B S hS hX hY f).out 1 8).mp hflat
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  have hschemeFlat : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hhFlat U V (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj V)) h (hmulEtale.id_mem _)
      (hmulEtale.id_mem _) (by simp)
  have hgenScheme : GeneralizingMap (fun z : (BigFppfOver.toScheme B S hS).obj U =>
      ((BigFppfOver.toScheme B S hS).map h) z) :=
    _root_.AlgebraicGeometry.Flat.generalizingMap _
  have hcontV : Continuous (pointsToScheme B S hS V) :=
    (schemePointsHomeomorph B S hS V).continuous
  have hsymmU : ∀ z : (BigFppfOver.toScheme B S hS).obj U,
      pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm z) = z :=
    (schemePointsHomeomorph B S hS U).apply_symm_apply
  have hcomm : ∀ w : points B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj V) q
          (pointsMap B S hS (yoneda.obj U) (yoneda.map h) w) =
        pointsMap B S hS X f (pointsMap B S hS (yoneda.obj U) p w) := by
    intro w
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq]
  intro x y hxy
  obtain ⟨u, hu⟩ := hpSurj x
  have hvy : y ⤳ pointsMap B S hS (yoneda.obj V) q
      (pointsMap B S hS (yoneda.obj U) (yoneda.map h) u) := by
    rw [hcomm u, hu]
    exact hxy
  obtain ⟨v', hv'v, hv'y⟩ := generalizingMap_pointsMap_of_isDecentSpace B S hS Y hY hYdec V q
    ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hqEt) hvy
  have hspecScheme : pointsToScheme B S hS V v' ⤳ pointsToScheme B S hS V
      (pointsMap B S hS (yoneda.obj U) (yoneda.map h) u) := hv'v.map hcontV
  rw [pointsToScheme_pointsMap_yoneda B S hS h u] at hspecScheme
  obtain ⟨w, hwspec, hwimg⟩ := hgenScheme hspecScheme
  have hkey : pointsMap B S hS (yoneda.obj U) (yoneda.map h)
      ((schemePointsHomeomorph B S hS U).symm w) = v' := by
    refine (bijective_pointsToScheme B S hS V).1 ?_
    rw [pointsToScheme_pointsMap_yoneda B S hS h, hsymmU w]
    exact hwimg
  refine ⟨pointsMap B S hS (yoneda.obj U) p ((schemePointsHomeomorph B S hS U).symm w), ?_, ?_⟩
  · rw [← hu]
    refine Specializes.map ?_ (continuous_pointsMap B S hS p)
    have hlift := hwspec.map (schemePointsHomeomorph B S hS U).symm.continuous
    rwa [show (schemePointsHomeomorph B S hS U).symm (pointsToScheme B S hS U u) = u from
      (schemePointsHomeomorph B S hS U).symm_apply_apply u] at hlift
  · rw [← hcomm, hkey, hv'y]

end Flat

/-! ### The dominance clause -/

section Dominance

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The dominance clause of Stacks 0EP5, for a flat morphism of decent algebraic spaces.**
Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` with `X` and `Y` decent, and
let `Z ⊆ Y` be an integral closed subspace. A generic point of an irreducible component of
`f^{-1}(Z)` is carried by `f` to a generic point of `|Z|`; that is, the component dominates
`Z`. -/
theorem isGenericPoint_pointsMap_preimageComponent_of_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) {f : X ⟶ Y} (hflat : IsFlat B S hS f)
    (Z : IntegralClosedSubspace B S hS Y)
    (C : irreducibleComponents (Z.preimagePointSet B S hS f))
    (x : points B S hS X)
    (hx : IsGenericPoint x (subspacePointSet B S hS X
      (Z.preimageComponent B S hS f hX hXdec hY C).subspace)) :
    IsGenericPoint (pointsMap B S hS X f x) (subspacePointSet B S hS Y Z.subspace) := by
  refine isGenericPoint_map_of_generalizingMap (continuous_pointsMap B S hS f)
    (generalizingMap_pointsMap_of_isFlat B S hS hX hY hYdec hflat)
    (isGenericPoint_pointsMap_genericPoint B S hS hY Z) C ?_
  rwa [Z.subspacePointSet_preimageComponent B S hS f hX hXdec hY C] at hx

end Dominance

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

attribute [local instance] pointTopology

/-- **The dominance clause of Stacks 0EP5, in Situation 0EDT.** Let `X/B` and `Y/B` be good, let
`f : X ⟶ Y` be a flat morphism over the base and let `Z ⊆ Y` be an integral closed subspace.
Then every irreducible component of `f^{-1}(Z)` dominates `Z`: a generic point of the component
is carried by `f` to a generic point of `|Z|`. The relative dimension of `f` does not enter the
dominance clause, so it is not a hypothesis; neither is local finiteness of the components of
the inverse image. -/
theorem isGenericPoint_pointsMap_preimageComponent_of_isGood (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hflat : IsFlat D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (x : points D.site D.base D.base_mem X)
    (hx : IsGenericPoint x (subspacePointSet D.site D.base D.base_mem X
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace)) :
    IsGenericPoint (pointsMap D.site D.base D.base_mem X f x)
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace) :=
  isGenericPoint_pointsMap_preimageComponent_of_isFlat D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 (D.isDecentSpace_of_isGood sY hY) hflat Z C x hx

end Situation

end AlgebraicGeometry.Space.FlatPreimage

end
