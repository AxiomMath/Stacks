module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SingleCoverAlgebraicity
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EssentiallySurjective
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic

/-!
# Representability of the diagonal passes to a target that is locally in the image

Let `G : 𝒵 ⟶ 𝒴` be a fully faithful 1-morphism of categories fibred in groupoids over the big fppf
site of `S`, with a common morphism universe, such that

* the presheaves `Mor(x, y)` of `𝒴` are fppf sheaves,
* every object of `𝒴` lies, fppf locally, in the essential image of `G`,
* `𝒵` has effective descent for the étale topology, and
* the isomorphism presheaves of `𝒵` are algebraic spaces (condition (2) of Stacks 045G).

Then the isomorphism presheaves of `𝒴` are algebraic spaces. The typical instance is the
stackification of a category fibred in groupoids with representable diagonal and `Mor`-sheaves
which is already an étale stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_locally_essImage`: the statement above.

## Implementation notes

For two objects `x`, `y` of `𝒴` over `T`, the covering sieves on which they come from `𝒵` are
intersected and refined to a single morphism `f : V ⟶ T` out of a disjoint union of members
(`AlgebraicGeometry.Stack.exists_single_cover_of_mem_topology`). The summand inclusions of `V`
form an étale covering, so the étale descent of `𝒵` glues the local preimages into preimages
`a`, `b` of the restrictions of `x`, `y` to `V`
(`CategoryTheory.Functor.exists_iso_of_locally_essImage`). Over `V` the isomorphism presheaf of
`x`, `y` is then that of `G a`, `G b`, which full faithfulness of `G` identifies with that of `a`,
`b` (Stacks 04WQ, as `CategoryTheory.Comma.isIso_morPresheafMap_of_fullyFaithful`), an algebraic
space by hypothesis; `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_of_single_cover` descends it
along `f`.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w₁ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of morphisms of the big fppf site of `S` which are étale and jointly surjective on
underlying schemes generates a covering sieve of the étale topology the site's category carries. -/
theorem ofArrows_mem_etaleOver_of_etale {V : BigFppfOver B S hS} {I : Type*}
    (Wi : I → BigFppfOver B S hS) (j : ∀ i, Wi i ⟶ V)
    (het : ∀ i, Etale (B.inclusion.map (j i).left))
    (hjs : ∀ x : B.inclusion.obj V.left, ∃ i, x ∈ Set.range (B.inclusion.map (j i).left)) :
    Sieve.ofArrows Wi j ∈ (etaleTopology B).over (B.obj hS) V := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [etalePrecoverage_eq_comap B, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hjs, het⟩

/-- **Representability of the diagonal passes to a target locally in the image of a fully
faithful 1-morphism.** Let `G : 𝒵 ⟶ 𝒴` be a fully faithful 1-morphism of categories fibred in
groupoids over the big fppf site of `S`, with one morphism universe. If the presheaves `Mor(x, y)`
of `𝒴` are fppf sheaves, every object of `𝒴` lies fppf locally in the essential image of `G`, `𝒵`
has effective descent for the étale topology, and the isomorphism presheaves of `𝒵` are
algebraic spaces, then so are those of `𝒴`. -/
theorem isAlgebraicSpaceIsomPresheaf_of_locally_essImage
    {𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w₂} (BigFppfOver B S hS)}
    (G : 𝒵.val.obj ⥤ 𝒴.val.obj) [G.Full] [G.Faithful]
    (hG : 𝒵.val.p.IsFibredOneMorphism 𝒴.val.p G)
    (hmor : haveI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
      ∀ (T : BigFppfOver B S hS) (x y : 𝒴.val.p.Fiber T),
        𝒴.val.p.IsMorSheaf (BigFppfOver.topology B S hS) T x y)
    (hdesc : haveI : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
      𝒵.val.p.HasEffectiveDescent ((etaleTopology B).over (B.obj hS)))
    (hloc : haveI : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
      haveI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
      ∀ (T : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber T),
        ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ T),
          R.arrows f → ∃ z : 𝒵.val.p.Fiber V,
            Nonempty ((Fiber.mapOfComp 𝒵.val.p 𝒴.val.p G hG.comp_eq V).obj z ≅
              pullbackFiber 𝒴.val.p y f))
    (hdiag : IsAlgebraicSpaceIsomPresheaf B S hS 𝒵) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒴 := by
  classical
  let : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  intro T x y
  let J := BigFppfOver.topology B S hS
  let J' := (etaleTopology B).over (B.obj hS)
  have hJ' : J' ≤ J := fun _ _ h => etaleTopology_le_topology B _ h
  obtain ⟨Rx, hRx, hx⟩ := hloc T x
  obtain ⟨Ry, hRy, hy⟩ := hloc T y
  obtain ⟨I, Wi, fi, V, j, f, hfi, hfac, -, -, -, het, hjs, hflat, hlfp, hsurj⟩ :=
    exists_single_cover_of_mem_topology B S hS (J.intersection_covering hRx hRy)
  have hjet : Sieve.ofArrows Wi j ∈ J' V := ofArrows_mem_etaleOver_of_etale B S hS Wi j het hjs
  have hmor' : ∀ (a b : 𝒴.val.p.Fiber V), 𝒴.val.p.IsMorSheaf J' V a b := fun a b =>
    Presheaf.IsSheaf.of_le (fun _ _ h => hJ' _ h) (hmor V a b)
  -- the local preimages glue over the étale covering of `V` by the summands
  have hglue : ∀ (z : 𝒴.val.p.Fiber T) (Rz : Sieve T), (∀ i, Rz.arrows (fi i)) →
      (∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ T), Rz.arrows g → ∃ c : 𝒵.val.p.Fiber W,
        Nonempty ((Fiber.mapOfComp 𝒵.val.p 𝒴.val.p G hG.comp_eq W).obj c ≅
          pullbackFiber 𝒴.val.p z g)) →
      ∃ a : 𝒵.val.p.Fiber V,
        Nonempty ((Fiber.mapOfComp 𝒵.val.p 𝒴.val.p G hG.comp_eq V).obj a ≅
          pullbackFiber 𝒴.val.p z f) := by
    intro z Rz hRz hz
    refine exists_iso_of_locally_essImage hG hdesc hmor' (pullbackFiber 𝒴.val.p z f) hjet ?_
    intro Y k hk
    obtain ⟨Y', g, _, ⟨i⟩, rfl⟩ := hk
    obtain ⟨c, ⟨ec⟩⟩ := hz (fi i) (hRz i)
    refine ⟨pullbackFiber 𝒵.val.p c g, ⟨?_⟩⟩
    exact (mapPullbackFiberIso' hG c g).symm ≪≫ pullbackFiberIso ec g ≪≫
      pullbackFiberCompIso' z (fi i) g (g ≫ fi i) rfl ≪≫
      (pullbackFiberCompIso' z f (g ≫ j i) (g ≫ fi i) (by rw [Category.assoc, hfac])).symm
  obtain ⟨a, ⟨ea⟩⟩ := hglue x Rx (fun i => (hfi i).1) hx
  obtain ⟨b, ⟨eb⟩⟩ := hglue y Ry (fun i => (hfi i).2) hy
  obtain ⟨F₀, hF₀, ⟨i₀⟩⟩ := hdiag V a b
  have := Comma.isIso_morPresheafMap_of_fullyFaithful hG a b
  let φ : 𝒵.val.p.isomPresheaf a b ≅ (Over.map f).op ⋙ 𝒴.val.p.isomPresheaf x y :=
    isomPresheafIsoMorPresheaf _ 𝒵.isFiberedInGroupoids a b ≪≫
      asIso (hG.morPresheafMap a b) ≪≫
      (isomPresheafIsoMorPresheaf _ 𝒴.isFiberedInGroupoids _ _).symm ≪≫
      isomPresheafIsoOfIso 𝒴.val.p ea eb ≪≫ isomPresheafPullbackCompIso 𝒴.val.p x y f
  refine exists_isAlgebraicSpace_of_single_cover B S hS (𝒴.val.p.isomPresheaf x y)
    ((Presheaf.isSheaf_of_iso_iff (isomPresheafIsoMorPresheaf _ 𝒴.isFiberedInGroupoids x y)).2
      (hmor T x y)) f hflat hlfp hsurj F₀ hF₀
    (i₀ ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op φ) uliftFunctor.{u, v})

end AlgebraicGeometry.Stack

end
