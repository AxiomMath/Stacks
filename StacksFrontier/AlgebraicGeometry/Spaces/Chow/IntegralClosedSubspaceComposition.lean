module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# Integral closed subspaces of an integral closed subspace

Let `V ⊆ W ⊆ X` be a chain of integral closed subspaces of algebraic spaces over `S`. Working
inside `W` produces data attached to `V` as an integral closed subspace of `W`, while working
inside `X` produces data attached to the image of `V` in `X`. This file identifies the two.

* The image in `X` of the image in `W` of `V` is the image in `X` of `V`
  (`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward_comp`), an equality of integral
  closed subspaces of `X`.
* The subspace `V` is isomorphic over `X` to its image, which carries the reduced closed
  subspace structure of Stacks 03IQ on a set of points of `X`
  (`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`).
* `k`-cycles transport along that isomorphism, and the transport is compatible with pushforward:
  pushing a `k`-cycle on `V` forward to `W` and then to `X` is the same as transporting it to the
  image of `V` and pushing forward from there
  (`AlgebraicGeometry.Space.integralClosedSubspacePushforward_comp_pushforward`).

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`: the identification of an
  integral closed subspace with its image along a closed immersion.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardCycleTransport`: the induced
  homomorphism of cycle groups.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward_comp`: pushing forward along a
  composite of closed immersions is pushing forward twice.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso_hom_comp_ι`: the identification
  is one of spaces over `X`.
* `AlgebraicGeometry.Space.locallyFinite_subspacePointSet_pushforward`: the images of a locally
  finite family of integral closed subspaces form a locally finite family.
* `AlgebraicGeometry.Space.cycleClosedPushforward_comp`: the composition law for the pushforward
  of coefficient families.
* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_comp_pushforward`: the three-level
  compatibility.

## Implementation notes

The isomorphism is built from Stacks 03JJ, which factors a morphism out of an étale-locally
reduced algebraic space through a closed subspace as soon as its image on points is contained in
that of the closed subspace. Applied once it produces a morphism from `V` to its image, and
applied twice — first through the range of the ambient closed immersion, then through `V` itself
— it produces a morphism back; the two composites are the identity because the inclusions are
monomorphisms. Reducedness, decency and irreducibility of the point space are read off from the
integral closed subspaces on either side, not transported along the isomorphism.

The ambient morphism is an arbitrary closed immersion `i : Y ⟶ X` and not the inclusion of a
closed subspace, which is the generality of
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` itself. The factorization goes
through `CategoryTheory.Subfunctor.range i`, a closed subspace of `X` isomorphic to `Y`; the
three-level situation `V ⊆ W ⊆ X` is the case `i = W.subspace.ι`.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Composition of images -/

section Pushforward

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of an integral closed subspace of `Z` along a composite `g ≫ i` of closed
immersions is the image along `i` of its image along `g`. -/
theorem IntegralClosedSubspace.pushforward_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) {g : Z ⟶ Y}
    (hg : IsClosedImmersion B S hS g) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (V : IntegralClosedSubspace B S hS Z) :
    IntegralClosedSubspace.pushforward B S hS hX hZ hXdec
        (isClosedImmersion_comp B S hS g i hg hi) V =
      IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi
        (IntegralClosedSubspace.pushforward B S hS hY hZ hYdec hg V) := by
  refine injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_)
  change subspacePointSet B S hS X (IntegralClosedSubspace.pushforward B S hS hX hZ hXdec
      (isClosedImmersion_comp B S hS g i hg hi) V).subspace =
    subspacePointSet B S hS X (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi
      (IntegralClosedSubspace.pushforward B S hS hY hZ hYdec hg V)).subspace
  rw [IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_pushforward, pointsMap_comp, Set.image_comp]

/-- The images of a locally finite family of integral closed subspaces of `Y` along a closed
immersion `i : Y ⟶ X` form a locally finite family. -/
theorem locallyFinite_subspacePointSet_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) {J : Type v} (V : J → IntegralClosedSubspace B S hS Y)
    (hV : LocallyFinite fun j : J => subspacePointSet B S hS Y (V j).subspace) :
    LocallyFinite fun j : J => subspacePointSet B S hS X
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi (V j)).subspace := by
  refine locallyFinite_of_isClosedEmbedding_extend
    (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi) (e := id)
    (fun w hw ↦ (hw w rfl).elim)
    (fun j ↦ (IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi (V j)).le)
    hV

end Pushforward

/-! ### The identification of an integral closed subspace with its image -/

section PushforwardIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inverse of `CategoryTheory.Subfunctor.toRange` of a monomorphism, followed by that
monomorphism, is the inclusion of its range. -/
theorem inv_toRange_comp_of_mono {i : Y ⟶ X} [Mono i] :
    inv (Subfunctor.toRange i) ≫ i = (Subfunctor.range i).ι :=
  (IsIso.inv_comp_eq (Subfunctor.toRange i)).2 (Subfunctor.toRange_ι i).symm

/-- The composite inclusion of an integral closed subspace `V` of `Y` into `X` factors through
the image of `V` in `X`. -/
theorem IntegralClosedSubspace.exists_hom_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (V : IntegralClosedSubspace B S hS Y) :
    ∃ φ : V.subspace.toFunctor ⟶
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor,
      φ ≫ (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι =
        V.subspace.ι ≫ i :=
  (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX V.isClosedSubspace.1
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace
      V.isIntegralSpace.1 (V.subspace.ι ≫ i)).2
    (le_of_eq ((IntegralClosedSubspace.range_pointsMap_ι_comp B S hS i V).trans
      (IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi V).symm))

/-- The inclusion of the image of `V` in `X` factors through the composite inclusion of `V`
into `X`. -/
theorem IntegralClosedSubspace.exists_hom_pushforward_symm (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (V : IntegralClosedSubspace B S hS Y) :
    ∃ ψ : (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor ⟶
        V.subspace.toFunctor,
      ψ ≫ V.subspace.ι ≫ i =
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι := by
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  have hUpts : subspacePointSet B S hS X
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace =
      pointsMap B S hS Y i '' subspacePointSet B S hS Y V.subspace :=
    IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi V
  have hsub₀ : Set.range (pointsMap B S hS
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι) ⊆
      Set.range (pointsMap B S hS (Subfunctor.range i).toFunctor
        (Subfunctor.range i).ι) := by
    rw [range_pointsMap_ι_range B S hS i]
    intro x hx
    obtain ⟨w, -, hweq⟩ : x ∈ pointsMap B S hS Y i '' subspacePointSet B S hS Y V.subspace :=
      hUpts ▸ hx
    exact ⟨w, hweq⟩
  obtain ⟨ψ₀, hψ₀⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace.1
      (Subfunctor.range i) (isClosedSubspace_range_of_isClosedImmersion B S hS i hY hi)
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isIntegralSpace.1
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι).2 hsub₀
  have hψ₁ : (ψ₀ ≫ inv (Subfunctor.toRange i)) ≫ i =
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι := by
    rw [Category.assoc, inv_toRange_comp_of_mono B S hS (i := i), hψ₀]
  have hsub₁ : Set.range (pointsMap B S hS
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor
        (ψ₀ ≫ inv (Subfunctor.toRange i))) ⊆
      Set.range (pointsMap B S hS V.subspace.toFunctor V.subspace.ι) := by
    rintro _ ⟨p, rfl⟩
    have hmem : pointsMap B S hS Y i
        (pointsMap B S hS
          (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor
          (ψ₀ ≫ inv (Subfunctor.toRange i)) p) ∈
        subspacePointSet B S hS X
          (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace := by
      rw [← Function.comp_apply (f := pointsMap B S hS Y i), ← pointsMap_comp, hψ₁]
      exact ⟨p, rfl⟩
    rw [hUpts] at hmem
    obtain ⟨w, hwV, hweq⟩ := hmem
    exact Set.mem_of_eq_of_mem
      (((isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi).injective hweq).symm)
      hwV
  obtain ⟨ψ, hψ⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isClosedSubspace.1
      V.subspace V.isClosedSubspace
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).isIntegralSpace.1
      (ψ₀ ≫ inv (Subfunctor.toRange i))).2 hsub₁
  exact ⟨ψ, by rw [← Category.assoc, hψ, hψ₁]⟩

/-- **An integral closed subspace is its image.** The identification of an integral closed
subspace `V` of `Y` with its image in `X` along a closed immersion `i : Y ⟶ X`, as an
isomorphism of presheaves over `X`.

The two morphisms are those of
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_hom_pushforward` and
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_hom_pushforward_symm`. -/
def IntegralClosedSubspace.pushforwardIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (V : IntegralClosedSubspace B S hS Y) :
    V.subspace.toFunctor ≅
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.toFunctor where
  hom := (IntegralClosedSubspace.exists_hom_pushforward B S hS hX hY hXdec hi V).choose
  inv := (IntegralClosedSubspace.exists_hom_pushforward_symm B S hS hX hY hXdec hi V).choose
  hom_inv_id := by
    have : Mono i := mono_of_isClosedImmersion B S hS i hi
    have : Mono (V.subspace.ι ≫ i) := mono_comp _ _
    rw [← cancel_mono (V.subspace.ι ≫ i), Category.assoc,
      (IntegralClosedSubspace.exists_hom_pushforward_symm B S hS hX hY hXdec hi V).choose_spec,
      (IntegralClosedSubspace.exists_hom_pushforward B S hS hX hY hXdec hi V).choose_spec,
      Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι,
      Category.assoc,
      (IntegralClosedSubspace.exists_hom_pushforward B S hS hX hY hXdec hi V).choose_spec,
      (IntegralClosedSubspace.exists_hom_pushforward_symm B S hS hX hY hXdec hi V).choose_spec,
      Category.id_comp]

/-- The identification of an integral closed subspace with its image is one of presheaves over
`X`: it carries the inclusion of the image to the composite inclusion. -/
@[simp]
theorem IntegralClosedSubspace.pushforwardIso_hom_comp_ι (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (V : IntegralClosedSubspace B S hS Y) :
    (IntegralClosedSubspace.pushforwardIso B S hS hX hY hXdec hi V).hom ≫
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι =
      V.subspace.ι ≫ i :=
  (IntegralClosedSubspace.exists_hom_pushforward B S hS hX hY hXdec hi V).choose_spec

/-- The inverse of the identification carries the composite inclusion of `V` to the inclusion of
the image. -/
@[simp]
theorem IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (V : IntegralClosedSubspace B S hS Y) :
    (IntegralClosedSubspace.pushforwardIso B S hS hX hY hXdec hi V).inv ≫ V.subspace.ι ≫ i =
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi V).subspace.ι :=
  (IntegralClosedSubspace.exists_hom_pushforward_symm B S hS hX hY hXdec hi V).choose_spec

end PushforwardIso

/-! ### Composition of the pushforward of cycles -/

section CyclePushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The pushforward of a coefficient family along a closed immersion depends only on the
morphism, not on the proof that it is a closed immersion. -/
theorem cycleClosedPushforward_congr (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i i' : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (hi' : IsClosedImmersion D.site D.base D.base_mem i') (h : i = i')
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) :
    cycleClosedPushforward D hX hY hXdec hi β = cycleClosedPushforward D hX hY hXdec hi' β := by
  subst h
  rfl

/-- Pushing a coefficient family forward along a composite `g ≫ i` of closed immersions is
pushing it forward along `g` and then along `i`. -/
theorem cycleClosedPushforward_comp (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hZ : IsAlgebraicSpace D.site D.base D.base_mem Z)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y) {g : Z ⟶ Y}
    (hg : IsClosedImmersion D.site D.base D.base_mem g) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (β : IntegralClosedSubspace D.site D.base D.base_mem Z → ℤ) :
    cycleClosedPushforward D hX hZ hXdec
        (isClosedImmersion_comp D.site D.base D.base_mem g i hg hi) β =
      cycleClosedPushforward D hX hY hXdec hi
        (cycleClosedPushforward D hY hZ hYdec hg β) := by
  funext W
  have hcomp := IntegralClosedSubspace.pushforward_comp D.site D.base D.base_mem hX hY hZ hXdec
    hYdec hg hi
  by_cases hiW : ∃ U, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec
      hi U = W
  · obtain ⟨U, rfl⟩ := hiW
    rw [cycleClosedPushforward_apply_pushforward]
    by_cases hgU : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY hZ hYdec
        hg V = U
    · obtain ⟨V, rfl⟩ := hgU
      rw [cycleClosedPushforward_apply_pushforward, ← hcomp V,
        cycleClosedPushforward_apply_pushforward]
    · rw [cycleClosedPushforward_apply_of_forall_ne D hY hZ hYdec hg β U
        fun V hV ↦ hgU ⟨V, hV⟩]
      exact cycleClosedPushforward_apply_of_forall_ne D hX hZ hXdec _ β _ fun V hV ↦ hgU ⟨V,
        IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX hY hXdec hi
          ((hcomp V).symm.trans hV)⟩
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi _ W
      fun U hU ↦ hiW ⟨U, hU⟩]
    exact cycleClosedPushforward_apply_of_forall_ne D hX hZ hXdec _ β W fun V hV ↦
      hiW ⟨IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY hZ hYdec hg V,
        (hcomp V).symm.trans hV⟩

end CyclePushforward

/-! ### Carrying a cycle on `V ⊆ W` out to `X` -/

section CycleTransport

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Transport of `k`-cycles along the identification of an integral closed subspace with its
image.** Pushforward of `k`-cycles along
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`, which is an isomorphism and in
particular a closed immersion; both sides are viewed over the base through the ambient closed
immersion `i : Y ⟶ X`. -/
def IntegralClosedSubspace.pushforwardCycleTransport (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y) (k : ℤ) :
    CycleGroup D (V.subspace.ι ≫ i ≫ sX) k →+
      CycleGroup D ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
        (D.isDecentSpace_of_isGood sX hX) hi V).subspace.ι ≫ sX) k :=
  cycleGroupClosedPushforward D
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
      (D.isDecentSpace_of_isGood sX hX) hi V).isClosedSubspace.1 V.isClosedSubspace.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
      (D.isDecentSpace_of_isGood sX hX) hi V).isIntegralSpace.isDecentSpace
    (isClosedImmersion_of_isIso D.site D.base D.base_mem
      (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY
        (D.isDecentSpace_of_isGood sX hX) hi V).hom)
    _ (isGood_integralClosedSubspace D sX hX
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
        (D.isDecentSpace_of_isGood sX hX) hi V)).2.2
    _ (by rw [← Category.assoc, IntegralClosedSubspace.pushforwardIso_hom_comp_ι,
      Category.assoc]) k

/-- **Carrying a cycle on `V ⊆ W` out to `X`.** In the situation of Stacks 0EDT let `X/B` be
good, let `W ⊆ X` be an integral closed subspace and let `V ⊆ W` be an integral closed subspace
of `W`. Pushing a `k`-cycle on `V` forward to `W` and then to `X` is the same as transporting it
along the identification of `V` with its image in `X` and pushing forward from that image. -/
theorem integralClosedSubspacePushforward_comp_pushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) (k : ℤ)
    (c : CycleGroup D (V.subspace.ι ≫ W.subspace.ι ≫ sX) k) :
    integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) V k c) =
      integralClosedSubspacePushforward D sX hX
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
            W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V) k
        (IntegralClosedSubspace.pushforwardCycleTransport D sX hX W.isClosedSubspace.1
          W.isClosedSubspace.2 V k c) := by
  refine Subtype.ext ?_
  refine Eq.trans (cycleClosedPushforward_comp D hX.1 W.isClosedSubspace.1
    V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
    W.isIntegralSpace.isDecentSpace V.isClosedSubspace.2 W.isClosedSubspace.2 c.1).symm ?_
  refine Eq.trans ?_ (cycleClosedPushforward_comp D hX.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).isClosedSubspace.1
    V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).isIntegralSpace.isDecentSpace
    (isClosedImmersion_of_isIso D.site D.base D.base_mem
      (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).hom)
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).isClosedSubspace.2 c.1)
  exact cycleClosedPushforward_congr D hX.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) _ _
    (IntegralClosedSubspace.pushforwardIso_hom_comp_ι D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).symm c.1

end CycleTransport

end AlgebraicGeometry.Space

end
