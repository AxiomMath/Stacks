module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandModule
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse

/-!
# Quasi-coherence of the band module is local on the charts carrying a frame

This file reduces the quasi-coherence of the band module of Stacks 0CKG (2)
(`AlgebraicGeometry.Stack.EtaleSmoothLift.bandModule`) to its restrictions to the étale charts
`V` of `W` over which the gerbe has an object, the source's appeal to Properties of Spaces,
Lemma 03M0 ("it suffices to check a module is quasi-coherent after going to an étale covering").

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite_over`: a sheaf of
  modules whose restrictions to the members of a family covering the final object are
  quasi-coherent is quasi-coherent (Stacks 03DN), with the module universe free.
* `CategoryTheory.Functor.mem_of_locallyNonempty_of_isDenseSubsite`: for a dense subsite
  `G : C ⥤ D` and a locally nonempty prefibred category over `D`, the objects of `C` whose image
  carries an object of the fibre cover every object of `C`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isQuasicoherentOnSite_bandModule_of_frames`: the
  reduction.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.SheafOfModules

universe u v r m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Stacks 03DN, quasi-coherence, read on slices.**  A sheaf of modules whose restriction to
each member of a family of objects covering the final object is quasi-coherent is
quasi-coherent; the universe of the module sections is independent of that of the rings. -/
theorem isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite_over
    (M : SheafOfModules.{m} R) {I : Type u} {V : I → C} (hV : J.CoversTop V)
    (h : ∀ i, (M.over (V i)).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation M
    (W := fun a : {Z : C // (M.over Z).HasGlobalPresentation} => a.1) (fun U => ?_)
    (fun a => a.2)
  refine J.transitive (hV U) _ fun Z f hf => ?_
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff V f).mp hf
  obtain ⟨K, T, t, hcov, hpres⟩ := (h i).locally_hasGlobalPresentation (Over.mk g)
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hcov
  refine J.superset_covering (fun Y y hy => ?_) hcov
  obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hy
  exact (Sieve.mem_ofObjects_iff _ _).mpr
    ⟨⟨(T k).left, hasGlobalPresentation_iteratedSlice' M (V i) (T k) (hpres k)⟩, ⟨a⟩⟩

end Stacks.SheafOfModules

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

/-- The sieve of the morphisms `Z ⟶ Y` of `C` such that the fibre over `G Z` is nonempty. -/
def nonemptyFiberSieve (G : C ⥤ D) (p : 𝒮 ⥤ D) [p.IsPreFibered] (Y : C) : Sieve Y where
  arrows Z _ := Nonempty (p.Fiber (G.obj Z))
  downward_closed {_ _} _ h g := ⟨pullbackFiber p h.some (G.map g)⟩

/-- **The objects of a dense subsite whose image carries an object of a locally nonempty
fibred category cover.** -/
theorem mem_of_locallyNonempty_of_isDenseSubsite (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [G.IsDenseSubsite J K] [G.Full] (p : 𝒮 ⥤ D) [p.IsPreFibered]
    (hne : p.LocallyNonempty K) (Y : C) : nonemptyFiberSieve G p Y ∈ J Y := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  rw [← G.functorPushforward_mem_iff (J := J) (K := K)]
  obtain ⟨T₀, hT₀, hfib⟩ := hne (G.obj Y)
  refine K.transitive hT₀ _ fun T f hf => K.superset_covering ?_
    (Functor.IsCoverDense.is_cover (G := G) (K := K) T)
  rintro T' g ⟨⟨Z, lift, map, fac⟩⟩
  refine ⟨Z, G.preimage (map ≫ f), lift, ⟨pullbackFiber p (hfib f hf).some map⟩, ?_⟩
  rw [G.map_preimage, ← Category.assoc, fac]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local instance] isFibered_proj

/-- **Quasi-coherence of the band module reduces to the charts carrying a frame** (Stacks 03M0
as used in the proof of Stacks 0CKG): if the restriction of the band module to every étale chart
`V` of `W` over which the gerbe has an object is quasi-coherent, the band module is. -/
theorem isQuasicoherentOnSite_bandModule_of_frames
    (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
    (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
      (Space.SpacesEtale.topology B S hS W))
    (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
      (Space.SpacesEtale.topology B S hS W))
    (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
    (θ : ∀ (U : Space.SpacesEtale B S hS W)
      (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
      (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
        (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
          uliftFunctor.{u + 1, u + 1})
    (h₁ h₂ h₃) -- the clauses of Stacks 0CJY, as in `bandModule`
    (hloc : ∀ (V : Space.SmallEtale B S hS W.1)
      (_ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
        ((Space.comparisonFunctor B S hS W).obj V)),
      ((bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).over V).IsQuasicoherentOnSite) :
    (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).IsQuasicoherentOnSite := by
  have := Space.comparisonFunctor_full B S hS W
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite_over _
    (V := fun a : {V : Space.SmallEtale B S hS W.1 // Nonempty
      ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
        ((Space.comparisonFunctor B S hS W).obj V))} => a.1) (fun Y => ?_)
    (fun a => hloc a.1 a.2.some)
  refine (Space.SmallEtale.topology B S hS W.1).superset_covering (fun Z f hf => ?_)
    (Functor.mem_of_locallyNonempty_of_isDenseSubsite (Space.comparisonFunctor B S hS W) _
      (Space.SpacesEtale.topology B S hS W) proj hne Y)
  exact (Sieve.mem_ofObjects_iff _ _).mpr ⟨⟨Z, hf⟩, ⟨𝟙 Z⟩⟩

end AlgebraicGeometry.Stack.EtaleSmoothLift
