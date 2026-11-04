module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementUniqueness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.Depth.FlatFibreAssociatedPrime
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Pullback of an improvement along a Cohen–Macaulay morphism

Let `F → F''` be an improvement of a coherent `𝒪_X`-module `F` along a closed subset `Z` of a
Noetherian scheme `X` (`AlgebraicGeometry.IsImprovement`) and let `f : Y → X` be a Cohen–Macaulay
morphism with `Y` Noetherian. Then `f^*F → f^*F''` is an improvement of `f^*F` along
`f^{-1}(Z)`.

The three conditions along the inverse images of the nested pair `Z ∖ {reached points} ⊆ Z` are
already available (`AlgebraicGeometry.isNestedImprovement_pullback`), so what is left is to
identify the set of points of `f^{-1}(Z)` reached from outside `f^{-1}(Z)` for `f^*F` with the
inverse image of the set of points of `Z` reached from outside `Z` for `F`. One inclusion is the
upper bound on the depth at a reached point, the other is a construction of a reaching point
upstairs out of one downstairs; both go through the exact formula for the depth of the stalk of a
pullback along a flat morphism, which is where the Cohen–Macaulay hypothesis is used in full.

## Main results

* `AlgebraicGeometry.depth_stalk_pullback_eq`: the depth of the stalk of a flat pullback of a
  coherent module is the depth of the stalk downstairs plus the depth of the fibre of the local
  ring.
* `AlgebraicGeometry.reachedFromOutside_base_of_reachedFromOutside_pullback`: a point of
  `f^{-1}(Z)` reached from outside `f^{-1}(Z)` for `f^*F` lies over a point of `Z` reached from
  outside `Z` for `F`.
* `AlgebraicGeometry.two_le_depth_stalk_pullback_of_notReachedFromOutside`: at a point of
  `f^{-1}(Z)` which is *not* reached from outside `f^{-1}(Z)` for `f^*F`, the stalk of `f^*F''`
  has depth at least two.
* `AlgebraicGeometry.isImprovement_pullback`: the pullback of an improvement along a
  Cohen–Macaulay morphism of Noetherian schemes is an improvement along the inverse image of the
  closed subset.
* `AlgebraicGeometry.epi_stalk_pullback_of_isImprovement` and
  `AlgebraicGeometry.depth_stalk_pullback_eq_one_of_isImprovement`: the two halves of the second
  condition upstairs, stated separately.

## Implementation notes

The depth formula is `Module.depth_tensorProduct_of_flat` ([Stacks, Tag 0338]) transported along
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, which identifies the stalk of
a pullback with the base change of the stalk. It is the equality of which
`AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat` keeps only the first summand; both
summands are needed here, in opposite directions.

For the comparison of the reached points, the direction from upstairs to downstairs uses only the
upper bound `AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside`, applied to the pullback
map: the depth upstairs is at most one, hence so is the depth downstairs by the formula, which
rules out the lower bound of two that the third condition would give at a point not reached
downstairs.

The other direction is the one place where the Cohen–Macaulayness of the fibres enters. If the
depth of the fibre `𝒪_{Y,y}/𝔪_{X,f y}𝒪_{Y,y}` were zero, then Cohen–Macaulayness of the local
ring of the fibre (`AlgebraicGeometry.quotientStalkEquivFiberStalk` together with
`Stacks.Depth.ringKrullDim_quotient_eq_depth_of_cohenMacaulay`) would make that fibre
zero-dimensional; a prime of `𝒪_{X,f y}` cut out by a point reaching `f y`
(`AlgebraicGeometry.exists_associatedPrime_stalk_of_isImmediateSpecialization`) then has a prime
of `𝒪_{Y,y}` above it associated to the stalk of `f^*F`
(`Stacks.Depth.exists_isAssociatedPrimeStacks_over_of_flat`) whose quotient is again at most
one-dimensional (`Stacks.Depth.ringKrullDim_quotient_map_le_one_of_closedFibre_dimension_zero`),
so that it leaves no room below the maximal ideal
(`Stacks.Depth.covBy_maximalIdeal_of_ringKrullDim_quotient_le_one`) and cuts out a point reaching
`y` and lying over the point reaching `f y`, contradicting the hypothesis.

The source's coherence of `F` is used only for its quasi-coherence, which is what the
associated-point machinery needs; it is assumed as coherence because that is the hypothesis of
the source and of the rest of this file.

The module structure on a stalk is spelled out wherever a depth appears, as in
`AlgebraicGeometry.IsImprovement` and `AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat`, so
the statements fit the existing depth results without transport. That structure is
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`;
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` is the same instance by definition.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The depth of a stalk of a flat pullback.** For a flat morphism `f : Y ⟶ X` of Noetherian
schemes and a coherent `𝒪_X`-module `G`, the depth of the stalk of `f^*G` at `y` is the depth of
the stalk of `G` at `f y` plus the depth of the fibre `𝒪_{Y,y}/𝔪_{X,f y}𝒪_{Y,y}`.

The stalk of `f^*G` at `y` is `𝒪_{Y,y} ⊗_{𝒪_{X,f y}} G_{f y}`, so this is the depth formula for a
flat base change, [Stacks, Tag 0338]. Dropping the second summand gives
`AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat`. -/
public theorem depth_stalk_pullback_eq {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (G : X.Modules) [G.IsCoherent] (y : Y) :
    letI : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
      (f.stalkMap y).hom.toAlgebra
    letI : Module (X.presheaf.stalk (f.base y))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val (f.base y)
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) =
      Module.depth (X.presheaf.stalk (f.base y))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y)))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)) +
        Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y ⧸
            ((IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y))).map
                (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) •
              (⊤ : Submodule (Y.presheaf.stalk y) (Y.presheaf.stalk y)))) := by
  dsimp only
  let R := X.presheaf.stalk (f.base y)
  let S := Y.presheaf.stalk y
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback f).obj G).val.presheaf y
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) G.val (f.base y)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
  let : Algebra R S := (f.stalkMap y).hom.toAlgebra
  have : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : Module.Finite R M := SheafOfModules.finite_stalk X.sheaf G (f.base y)
  have : IsLocalHom (algebraMap R S) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat R S := Flat.stalkMap f y
  obtain ⟨E, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom G y
  have hdepthEq : Module.depth S (IsLocalRing.maximalIdeal S) N =
      Module.depth S (IsLocalRing.maximalIdeal S) (TensorProduct R S M) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) E
  exact hdepthEq.trans (Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := M) (N := S))

/-- The pullback of an improvement along a Cohen–Macaulay morphism is a nested improvement along
the inverse images of the nested pair. -/
private theorem isNestedImprovement_pullback_of_isImprovement {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] {Z : Set X} {F G : X.Modules} (φ : F ⟶ G) (hφ : IsImprovement Z φ)
    (f : Y ⟶ X) (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x))
    (hcm : f.IsCohenMacaulay hfib) :
    IsNestedImprovement (f.base ⁻¹' Z) (f.base ⁻¹' NotReachedFromOutside Z F)
      ((Scheme.Modules.pullback f).map φ) :=
  isNestedImprovement_pullback φ (isNestedImprovement_of_isImprovement hφ) f hfib hcm

/-- **The reaching point descends.** Let `F → F''` be an improvement of `F` along `Z` and let
`f : Y ⟶ X` be a Cohen–Macaulay morphism of Noetherian schemes. If a point `y` of `f^{-1}(Z)` is
reached from outside `f^{-1}(Z)` for `f^*F`, then `f y` is reached from outside `Z` for `F`.

Upstairs the pullback is an improvement along the inverse images of the nested pair, so
`AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside` bounds the depth of the stalk of
`f^*F''` at `y` by one; by `AlgebraicGeometry.depth_stalk_pullback_eq` the depth of the stalk of
`F''` at `f y` is then at most one, which contradicts the bound of two that the third condition of
an improvement gives at a point of `Z` not reached from outside `Z`. -/
public theorem reachedFromOutside_base_of_reachedFromOutside_pullback {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {Z : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy : y ∈ f.base ⁻¹' Z)
    (hr : ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y) :
    ReachedFromOutside Z F (f.base y) := by
  by_contra hnr
  have : Flat f := Flat.of_stalkMap f fun z => (hcm z).1
  have : G.IsCoherent := hφ.1
  have hn := isNestedImprovement_pullback_of_isImprovement φ hφ f hfib hcm
  have : ((Scheme.Modules.pullback f).obj G).IsCoherent := hn.1
  have hup := depth_stalk_le_one_of_reachedFromOutside
    ((Scheme.Modules.pullback f).map φ) hn.2.1 y hr
  have hformula := depth_stalk_pullback_eq f G y
  dsimp only at hup hformula
  exact absurd ((hφ.2.2.2 (f.base y) hy hnr).trans (le_self_add.trans (hformula.symm.trans_le hup)))
    (by norm_num)

/-- **A zero-dimensional fibre carries the reaching point upwards.** Let `f : Y ⟶ X` be a
Cohen–Macaulay morphism of Noetherian schemes, let `F` be a quasi-coherent `𝒪_X`-module and let
`y : Y` be a point at which the fibre `𝒪_{Y,y}/𝔪_{X,f y}𝒪_{Y,y}` has depth zero. If `f y` is
reached from outside `Z` for `F`, then `y` is reached from outside `f^{-1}(Z)` for `f^*F`.

The fibre is Cohen–Macaulay, so a fibre of depth zero is zero-dimensional. A point reaching `f y`
cuts out a prime `p` of `𝒪_{X,f y}` which is associated to the stalk of `F`, strictly below the
maximal ideal, and has at most one-dimensional quotient. A prime of `𝒪_{Y,y}` over `p` associated
to the stalk of `f^*F` and strictly below the maximal ideal then has at most one-dimensional
quotient as well, because the fibre is zero-dimensional, so nothing lies strictly between it and
the maximal ideal: it cuts out an associated point of `f^*F` specializing immediately to `y`, and
that point lies over the point reaching `f y`, hence outside `f^{-1}(Z)`. -/
private lemma reachedFromOutside_pullback_of_depth_fibre_eq_zero {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [Flat f]
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    {Z : Set X} (F : X.Modules) [F.IsQuasicoherent] (y : Y)
    (hdepth : Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      ((Y.presheaf.stalk y) ⧸ Ideal.map (f.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y)))) = 0)
    (hr : ReachedFromOutside Z F (f.base y)) :
    ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y := by
  have : IsLocallyNoetherian (f.fiber (f.base y)) := hfib (f.base y)
  let : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := Flat.stalkMap f y
  -- the fibre is zero-dimensional
  have hfibdim : ringKrullDim ((Y.presheaf.stalk y) ⧸
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y))).map
        (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y))) = 0 := by
    rw [RingHom.algebraMap_toAlgebra,
      Stacks.Depth.ringKrullDim_quotient_eq_depth_of_cohenMacaulay _
        (quotientStalkEquivFiberStalk f y) (hcm y).2, hdepth]
    rfl
  -- the prime cut out by a point reaching `f y`
  obtain ⟨x', hx'Z, hassx, himm⟩ := hr
  let : Module (X.presheaf.stalk (f.base y)) (F.presheaf.stalk (f.base y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (f.base y)
  obtain ⟨p, hp, hplt, hpdim, hpx⟩ :=
    exists_associatedPrime_stalk_of_isImmediateSpecialization F x' (f.base y) hassx himm
  -- a prime of the local ring upstairs above it, associated to the stalk of `f^*F`
  obtain ⟨q, hq, hqp, hqm⟩ := Stacks.Depth.exists_isAssociatedPrimeStacks_over_of_flat
    (S := Y.presheaf.stalk y) p.asIdeal hp hplt
  have : q.IsPrime := hq.1
  have himmUp := isImmediateSpecialization_fromSpecStalk y ⟨q, hq.1⟩ hqm
    (Stacks.Depth.covBy_maximalIdeal_of_ringKrullDim_quotient_le_one _ q
      (Ideal.map_le_iff_le_comap.mpr hqp.ge) hqm
      (Stacks.Depth.ringKrullDim_quotient_map_le_one_of_closedFibre_dimension_zero
        (S := Y.presheaf.stalk y) p.asIdeal hpdim hfibdim))
  have : ((Scheme.Modules.pullback f).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom F
      ‹F.IsQuasicoherent›
  obtain ⟨E, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom F y
  have hassUp := isAssociatedPoint_fromSpecStalk_of_isAssociatedPrimeStacks
    ((Scheme.Modules.pullback f).obj F) y ⟨q, hq.1⟩
    (isAssociatedPrimeStacks_of_injective E.symm.toLinearMap E.symm.injective q hq)
  -- that prime cuts out a point over `x'`
  have hfx : f.base (Y.fromSpecStalk y ⟨q, hq.1⟩) = x' := by
    rw [← hpx, ← show PrimeSpectrum.comap (f.stalkMap y).hom ⟨q, hq.1⟩ = p from
      PrimeSpectrum.ext hqp]
    exact (congrArg (fun k : Spec (Y.presheaf.stalk y) ⟶ X => k.base ⟨q, hq.1⟩)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := f) (x := y))).symm
  exact ⟨Y.fromSpecStalk y ⟨q, hq.1⟩, by rwa [Set.mem_preimage, hfx], hassUp, himmUp⟩

/-- **The depth bound at a point not reached upstairs.** Let `F → F''` be an improvement of a
coherent `𝒪_X`-module `F` along `Z` and let `f : Y ⟶ X` be a Cohen–Macaulay morphism of Noetherian
schemes. At a point `y` of `f^{-1}(Z)` which is not reached from outside `f^{-1}(Z)` for `f^*F`,
the stalk of `f^*F''` has depth at least two.

By `AlgebraicGeometry.depth_stalk_pullback_eq` the depth upstairs is the depth of the stalk of
`F''` at `f y` plus the depth of the fibre of the local ring. If `f y` is not reached from outside
`Z` the first summand is already at least two. If it is reached, the first summand is exactly one,
so it suffices that the fibre have positive depth; a fibre of depth zero would carry the point
reaching `f y` up to a point reaching `y`, which is excluded by hypothesis. -/
@[stacks 0DX5 "condition (3) for the pullback along a Cohen-Macaulay morphism: depth at least \
two at a point of the inverse image of Z which is not itself reached from outside that inverse \
image"]
public theorem two_le_depth_stalk_pullback_of_notReachedFromOutside {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {Z : Set X} {F G : X.Modules} [F.IsCoherent] (φ : F ⟶ G)
    (hφ : IsImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy : y ∈ f.base ⁻¹' Z)
    (hnr : ¬ ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) := by
  have : Flat f := Flat.of_stalkMap f fun z => (hcm z).1
  have : G.IsCoherent := hφ.1
  have hformula := depth_stalk_pullback_eq f G y
  dsimp only at hformula
  rw [hformula]
  by_cases hbase : ReachedFromOutside Z F (f.base y)
  · rw [(hφ.2.2.1 (f.base y) hy hbase).2]
    refine le_trans (by norm_num : (2 : ℕ∞) ≤ 1 + 1) (add_le_add le_rfl ?_)
    refine Order.one_le_iff_ne_zero.mpr fun hd0 => ?_
    rw [RingHom.algebraMap_toAlgebra] at hd0
    rw [show Ideal.map (f.stalkMap y).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y))) •
            (⊤ : Submodule (Y.presheaf.stalk y) (Y.presheaf.stalk y)) =
        Ideal.map (f.stalkMap y).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y))) from
      Ideal.mul_top _] at hd0
    have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    exact hnr (reachedFromOutside_pullback_of_depth_fibre_eq_zero f hfib hcm F y hd0 hbase)
  · exact (hφ.2.2.2 (f.base y) hy hbase).trans le_self_add

/-- **Stacks Project, Tag 0DX5, the assertion about the pullback.** The pullback of an improvement
of a coherent module along a Cohen–Macaulay morphism of Noetherian schemes is an improvement along
the inverse image of the closed subset: it satisfies conditions (1), (2) and (3) with respect to
`f^{-1}(Z) ⊆ Y`.

An improvement along `Z` is an improvement along the nested pair `Z ∖ {reached points} ⊆ Z`
(`AlgebraicGeometry.isNestedImprovement_of_isImprovement`), whose pullback is an improvement along
the inverse images of that pair (`AlgebraicGeometry.isNestedImprovement_pullback`). Those inverse
images are the pair belonging to `f^*F` and `f^{-1}(Z)`, because the points of `f^{-1}(Z)` reached
from outside `f^{-1}(Z)` for `f^*F` are exactly the points lying over points of `Z` reached from
outside `Z` for `F`; that is the content of
`AlgebraicGeometry.reachedFromOutside_base_of_reachedFromOutside_pullback` and
`AlgebraicGeometry.two_le_depth_stalk_pullback_of_notReachedFromOutside`. -/
@[stacks 0DX5 "the final assertion: the pullback of the map along a Cohen-Macaulay morphism \
with Noetherian source satisfies conditions (1), (2) and (3) with respect to the inverse image \
of the closed subscheme"]
public theorem isImprovement_pullback {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {Z : Set X} {F G : X.Modules} [F.IsCoherent] (φ : F ⟶ G) (hφ : IsImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib) :
    IsImprovement (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).map φ) := by
  have hn := isNestedImprovement_pullback_of_isImprovement φ hφ f hfib hcm
  refine isImprovement_of_isNestedImprovement ⟨hn.1, hn.2.1, ?_, ?_⟩
  · intro y hy hy'
    exact hn.2.2.1 y hy fun hc => hc.2
      (reachedFromOutside_base_of_reachedFromOutside_pullback φ hφ f hfib hcm y hy
        (reachedFromOutside_of_notMem_notReachedFromOutside hy hy'))
  · intro y hy'
    exact two_le_depth_stalk_pullback_of_notReachedFromOutside φ hφ f hfib hcm y hy'.1 hy'.2

/-- The pullback of an improvement along a Cohen–Macaulay morphism of Noetherian schemes is
surjective on the stalk at every point of the inverse image of the closed subset which is reached
from outside that inverse image: the surjectivity half of condition (2) upstairs. -/
@[stacks 0DX5 "the surjectivity in condition (2) for the pullback along a Cohen-Macaulay \
morphism"]
public theorem epi_stalk_pullback_of_isImprovement {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] {Z : Set X} {F G : X.Modules} [F.IsCoherent] (φ : F ⟶ G)
    (hφ : IsImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy : y ∈ f.base ⁻¹' Z)
    (hr : ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y) :
    Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((Scheme.Modules.pullback f).map φ).mapPresheaf) :=
  ((isImprovement_pullback φ hφ f hfib hcm).2.2.1 y hy hr).1

/-- The target of the pullback of an improvement along a Cohen–Macaulay morphism of Noetherian
schemes has stalk of depth exactly one at every point of the inverse image of the closed subset
which is reached from outside that inverse image: the depth half of condition (2) upstairs. -/
@[stacks 0DX5 "the depth equality in condition (2) for the pullback along a Cohen-Macaulay \
morphism: the depth is exactly one, not merely at least one"]
public theorem depth_stalk_pullback_eq_one_of_isImprovement {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] {Z : Set X} {F G : X.Modules} [F.IsCoherent] (φ : F ⟶ G)
    (hφ : IsImprovement Z φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy : y ∈ f.base ⁻¹' Z)
    (hr : ReachedFromOutside (f.base ⁻¹' Z) ((Scheme.Modules.pullback f).obj F) y) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) = (1 : ℕ∞) :=
  ((isImprovement_pullback φ hφ f hfib hcm).2.2.1 y hy hr).2

end AlgebraicGeometry

end
