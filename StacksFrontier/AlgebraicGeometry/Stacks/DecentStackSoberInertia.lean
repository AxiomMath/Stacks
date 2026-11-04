module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentRepresentedSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackKolmogorov
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# Sobriety of decent algebraic stacks with quasi-compact inertia (Stacks 0GW9)

Let `𝒳` be a decent algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact.
**Stacks 0GW9** asserts that the space of points `|𝒳|` (**Stacks 04XL**) is sober.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasiSober_points_of_isDecent_of_isGerbe`: the space
  of points of a decent gerbe over an algebraic space is quasi-sober.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedEmbedding_pointsMap_of_isClosedSubstack`: the
  points of a closed substack form a closed subspace of the points of the ambient stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDecent_of_isClosedSubstack` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_inertia_of_fullyFaithful`: a
  closed substack of a decent stack with quasi-compact inertia is again such.
* `AlgebraicGeometry.Stack.AlgebraicStacks.stacksSober_points_of_isDecent`: **Stacks 0GW9**.

## Implementation notes

The proof is the source's. Kolmogorov is **Stacks 0GW7**. For an irreducible closed `T ⊆ |𝒳|`,
the reduced closed substack `𝒵` on `T` (**Stacks 0509**) is decent (**Stacks 0GW3**) with
quasi-compact inertia (the inertia of `𝒵` is the base change of that of `𝒳`, **Stacks 06R5**, and
quasi-compactness base changes, **Stacks 050V**), it is reduced, and `|𝒵| ≅ T` is irreducible. By
**Stacks 06RC** it has a dense open substack `𝒰` which is a gerbe over an algebraic space `U`; `𝒰`
is decent, so `U` is decent (**Stacks 0GW5**) and `|U|` is sober (**Stacks 03K6**), and
`|𝒰| ≅ |U|` (**Stacks 06R9**). A generic point of `|𝒰|` is then a generic point of `T`.

## References

* [Stacks Project, Tag 0GW9](https://stacks.math.columbia.edu/tag/0GW9)
* [Stacks Project, Tag 0GW7](https://stacks.math.columbia.edu/tag/0GW7)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 06R9](https://stacks.math.columbia.edu/tag/06R9)
* [Stacks Project, Tag 0GW5](https://stacks.math.columbia.edu/tag/0GW5)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The space of points of a decent gerbe over an algebraic space is quasi-sober.** If `𝒢` is
decent and a gerbe over an algebraic stack `𝒴` represented by an algebraic space `F`, then `𝒴`
is decent (**Stacks 0GW5**), hence `F` is decent, hence `|F|` is sober (**Stacks 03K6**); and
`|𝒢| ≅ |𝒴| ≅ |F|` (**Stacks 06R9**). -/
theorem quasiSober_points_of_isDecent_of_isGerbe (𝒢 : AlgebraicStacks.{u, w} B S hS)
    (hd : IsDecent B S hS 𝒢.val) (hg : IsGerbe B S hS 𝒢) :
    @QuasiSober (AlgebraicStacks.points B S hS 𝒢) (pointTopology B S hS 𝒢.val) := by
  obtain ⟨𝒴, ⟨F, hF, ⟨e⟩⟩, f, hf⟩ := hg
  have hFd := isDecentSpace_of_isDecent_representing B S hS 𝒴.val
    (isDecent_of_isGerbeOver B S hS f hf hd) F hF e
  let := Space.pointTopology B S hS F
  let := pointTopology B S hS 𝒴.val
  let := pointTopology B S hS 𝒢.val
  let : QuasiSober (Space.points B S hS F) :=
    (stacksSober_iff_t0_and_quasiSober.mp
      (Space.stacksSober_points_of_isDecentSpace B S hS hF hFd)).2
  let : QuasiSober (AlgebraicStacks.points B S hS 𝒴) :=
    ((isHomeomorph_spacePointMap_representing B S hS F hF 𝒴.val e).homeomorph _).symm
      |>.isClosedEmbedding.quasiSober
  exact ((isHomeomorph_pointsMap_of_isGerbeOver B S hS f hf).homeomorph _)
    |>.isClosedEmbedding.quasiSober

variable {B S hS}

/-- **The points of a closed substack form a closed subspace.** The inclusion of a closed
substack of `𝒳` is continuous and closed on points (**Stacks 0H20**) and injective, being fully
faithful. -/
theorem isClosedEmbedding_pointsMap_of_isClosedSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    @Topology.IsClosedEmbedding _ _
      (pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA).val)
      (pointTopology B S hS 𝒳.val)
      (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hA)) := by
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA).val
  let := pointTopology B S hS 𝒳.val
  have hi : AlgebraicStacks.IsClosedImmersion B S hS (fullSubcategoryInclusion 𝒳 P hA) :=
    hP.2.choose_spec
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_pointsMap B S hS _ 𝒳.val _)
    (pointsMap_injective_of_fullyFaithful B S hS _)
    (isClosedMap_pointsMap_of_isClosedImmersion B S hS _ hi)

/-- A stack with an immersion into a decent algebraic stack is decent. -/
private theorem isDecent_of_isImmersion {𝒬 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒬 ⟶ 𝒳)
    (hd : IsDecent B S hS 𝒳.val) (hf : AlgebraicStacks.IsImmersion B S hS f) :
    IsDecent B S hS 𝒬.val :=
  isDecent_of_representable_or_quasiSeparated B S hS f hd
    (Or.inr ⟨hf.1, isQuasiSeparated_of_isMonomorphism B S hS _
      (isMonomorphism_of_isImmersion B S hS _ hf)⟩)

/-- **A closed substack of a decent algebraic stack is decent** (**Stacks 0GW3**): its inclusion
is representable by algebraic spaces and, being a monomorphism, quasi-separated. -/
theorem isDecent_of_isClosedSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (hd : IsDecent B S hS 𝒳.val) {P : ObjectProperty 𝒳.val.val.obj} (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    IsDecent B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA).val := by
  have hi : AlgebraicStacks.IsClosedImmersion B S hS (fullSubcategoryInclusion 𝒳 P hA) :=
    hP.2.choose_spec
  exact isDecent_of_isImmersion _ hd (isImmersion_of_isClosedImmersion B S hS _ hi)

/-- **The inertia of a fully faithful source is quasi-compact when that of the target is.** For
a 1-morphism `f : 𝒬 ⟶ 𝒳` of algebraic stacks with fully faithful underlying functor, the inertia
projection of `𝒬` is a base change of that of `𝒳` (**Stacks 06R5**), and quasi-compactness is
stable under base change (**Stacks 050V**). -/
theorem isQuasiCompactMorphism_inertia_of_fullyFaithful {𝒬 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒬 ⟶ 𝒳) (hf : (CatFiberedInGroupoids.homFunctor f.hom).FullyFaithful)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒬) :=
  isQuasiCompactMorphism_baseChange B S hS _ f _ (Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_inertiaFullyFaithfulSquareAlgebraicStacks B S hS f hf)) hqc

/-- **Stacks 0GW9.** Let `𝒳` be a decent algebraic stack over `S` such that the inertia projection
`I_𝒳 ⟶ 𝒳` is quasi-compact. Then the space of points `|𝒳|` is sober. -/
@[stacks 0GW9]
theorem stacksSober_points_of_isDecent (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hd : IsDecent B S hS 𝒳.val)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    @StacksSober (AlgebraicStacks.points B S hS 𝒳) (pointTopology B S hS 𝒳.val) := by
  let := pointTopology B S hS 𝒳.val
  refine stacksSober_iff_t0_and_quasiSober.mpr
    ⟨t0Space_points_of_isDecent B S hS 𝒳.val 𝒳.property hd, ⟨fun {T} hT hclosed => ?_⟩⟩
  obtain ⟨P, hP, hPT⟩ := exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳 T hclosed
  obtain ⟨hA, -⟩ := hP.2
  obtain ⟨hrange, hred⟩ := hPT hA
  let 𝒵 := fullSubcategoryAlgebraicStack 𝒳 P hA
  let i := fullSubcategoryInclusion 𝒳 P hA
  let := pointTopology B S hS 𝒵.val
  have hφ := isClosedEmbedding_pointsMap_of_isClosedSubstack hP hA
  have hZd := isDecent_of_isClosedSubstack hd hP hA
  have hZqc := isQuasiCompactMorphism_inertia_of_fullyFaithful i
    (Functor.FullyFaithful.ofFullyFaithful _) hqc
  have hZirr : IrreducibleSpace (AlgebraicStacks.points B S hS 𝒵) :=
    hφ.toHomeomorph.irreducibleSpace_iff.2 (by
      rw [hrange]
      exact isIrreducible_iff_irreducibleSpace.mp hT)
  obtain ⟨W, hWdense, hWgerbe⟩ := exists_openSubstack_dense_isGerbe B S hS 𝒵 hred hZqc
  let 𝒰 := fullSubcategoryAlgebraicStack 𝒵 W.property W.isAlgebraic
  let j := W.inclusion
  let := pointTopology B S hS 𝒰.val
  have hUd : IsDecent B S hS 𝒰.val :=
    isDecent_of_isImmersion j hZd ⟨W.isOpenImmersion.1, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (W.isOpenImmersion.2 U y hy F hF he)⟩
  let : QuasiSober (AlgebraicStacks.points B S hS 𝒰) :=
    quasiSober_points_of_isDecent_of_isGerbe B S hS 𝒰 hUd hWgerbe
  let ψ := AlgebraicStacks.pointsMap B S hS j
  have := full_fullSubcategoryInclusion 𝒵 W.property W.isAlgebraic
  have := faithful_fullSubcategoryInclusion 𝒵 W.property W.isAlgebraic
  have hψ : Topology.IsOpenEmbedding ψ :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_pointsMap B S hS _ 𝒵.val _)
      (pointsMap_injective_of_fullyFaithful B S hS
        (fullSubcategoryInclusion 𝒵 W.property W.isAlgebraic))
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ W.isOpenImmersion)
  obtain ⟨_, z₀, -⟩ : (Set.range ψ).Nonempty := hWdense.nonempty
  have : Nonempty (AlgebraicStacks.points B S hS 𝒰) := ⟨z₀⟩
  have : IrreducibleSpace (AlgebraicStacks.points B S hS 𝒰) := hψ.irreducibleSpace
  obtain ⟨η, hη⟩ := QuasiSober.sober (IrreducibleSpace.isIrreducible_univ
    (AlgebraicStacks.points B S hS 𝒰)) isClosed_univ
  refine ⟨AlgebraicStacks.pointsMap B S hS i (ψ η), ?_⟩
  have h1 := hη.image hψ.continuous
  rw [Set.image_univ, show closure (Set.range ψ) = Set.univ from hWdense.closure_eq] at h1
  show closure {AlgebraicStacks.pointsMap B S hS i (ψ η)} = T
  rw [← hrange, ← Set.image_singleton, hφ.closure_image_eq, h1.def, Set.image_univ]

end AlgebraicGeometry.Stack.AlgebraicStacks

end
