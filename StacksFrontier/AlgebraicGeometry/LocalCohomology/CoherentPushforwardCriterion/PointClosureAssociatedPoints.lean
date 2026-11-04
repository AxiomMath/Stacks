module

public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCoherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated points of the direct image of the structure sheaf of a point closure

Let `U` be a locally Noetherian scheme, `x ∈ U`, and `i_x : W_x → U` the integral closed
subscheme with generic point `x`. This file computes

`Ass(i_{x,*} 𝒪_{W_x}) = {x}`.

## Main results

* `isAssociatedPrimeStacks_comap_iff_of_surjective`: for a surjective ring map `R → S` and an
  `S`-module, a prime of `S` is associated over `S` exactly when its preimage is associated over
  `R`.
* `AlgebraicGeometry.isAssociatedPoint_pushforward_iff_of_isClosedImmersion`: for a closed
  immersion `i` and a quasi-coherent `M`, `i w ∈ Ass(i_* M) ↔ w ∈ Ass(M)`.
* `AlgebraicGeometry.schemeAssociatedPoints_eq_singleton_genericPoint`: the associated points
  of an integral locally Noetherian scheme are its generic point alone.
* `AlgebraicGeometry.associatedPoints_pointClosureStructureSheaf`: the identity above, and
  `AlgebraicGeometry.associatedPoints_pointClosureStructureSheaf_subset` the inclusion `⊆ {x}`.
* `AlgebraicGeometry.isCoherent_pushforward_pointClosure_of_injective_stalk_at`: the
  pushforward of `i_{x,*} 𝒪_{W_x}` along an open immersion into a locally Noetherian scheme is
  coherent as soon as it maps, injectively on the stalk at `x`, to a quasi-coherent module whose
  pushforward is coherent.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.CodimensionOneObstruction

universe u

/-- A module with one element has no associated primes. -/
theorem not_isAssociatedPrimeStacks_of_subsingleton {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Subsingleton M] (p : Ideal R) : ¬ IsAssociatedPrimeStacks R M p := by
  rintro ⟨hp, m, rfl⟩
  refine hp.ne_top (eq_top_iff.2 fun r _ ↦ ?_)
  rw [Submodule.mem_colon_span_singleton]
  exact Subsingleton.elim _ _

/-- Let `φ : R →+* S` be surjective and `N`
an `S`-module, regarded as an `R`-module by restriction of scalars. A prime `q` of `S` is
associated to `N` over `S` exactly when `q.comap φ` is associated to `N` over `R`.

The annihilator over `R` of an element is the `φ`-preimage of its annihilator over `S`, and for
a surjective `φ` the map `Ideal.comap φ` is injective and reflects primality; the two statements
therefore say the same thing about the same element. -/
@[ega "IV 3.1.10.1" "Surjective homomorphisms"]
theorem isAssociatedPrimeStacks_comap_iff_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) {N : Type*} [AddCommGroup N] [Module S N]
    (q : Ideal S) :
    letI : Module R N := Module.compHom N φ
    IsAssociatedPrimeStacks R N (q.comap φ) ↔ IsAssociatedPrimeStacks S N q := by
  let _ : Module R N := Module.compHom N φ
  have hsmul : ∀ (r : R) (n : N), r • n = φ r • n := fun _ _ ↦ rfl
  have hann : ∀ n : N, (⊥ : Submodule R N).colon (Submodule.span R {n})
      = ((⊥ : Submodule S N).colon (Submodule.span S {n})).comap φ := fun n ↦ by
    ext r
    simp only [Ideal.mem_comap, Submodule.mem_colon_span_singleton, Submodule.mem_bot, hsmul]
  have hprime : (q.comap φ).IsPrime ↔ q.IsPrime := by
    refine ⟨fun h ↦ ⟨fun hq ↦ h.ne_top (by simp [hq]), fun {a b} hab ↦ ?_⟩,
      fun h ↦ h.comap φ⟩
    obtain ⟨y, rfl⟩ := hφ a
    obtain ⟨z, rfl⟩ := hφ b
    exact h.mem_or_mem (show y * z ∈ q.comap φ by simpa using hab)
  constructor
  · rintro ⟨hp, n, hn⟩
    exact ⟨hprime.mp hp, n, Ideal.comap_injective_of_surjective φ hφ (by rw [← hann n, hn])⟩
  · rintro ⟨hp, n, hn⟩
    exact ⟨hprime.mpr hp, n, by rw [hann n, hn]⟩

namespace AlgebraicGeometry

/-- For a closed immersion `i : W ⟶ U` and a quasi-coherent `𝒪_W`-module `M`, the point `i w`
is associated to `i_* M` exactly when `w` is associated to `M`. -/
theorem isAssociatedPoint_pushforward_iff_of_isClosedImmersion {W U : Scheme.{u}} (i : W ⟶ U)
    [IsClosedImmersion i] (M : W.Modules) [M.IsQuasicoherent] (w : W) :
    Stacks.Divisors.IsAssociatedPoint ((Scheme.Modules.pushforward i).obj M) (i w) ↔
      Stacks.Divisors.IsAssociatedPoint M w := by
  have hfib : i ⁻¹' ({i w} : Set U) = {w} :=
    Set.eq_singleton_iff_unique_mem.2
      ⟨rfl, fun z hz ↦ (IsClosedImmersion.isClosedEmbedding i).injective hz⟩
  obtain ⟨e⟩ := stalk_isomorphic_pushforward_of_finite_singleton_fiber i w hfib M
  let φ := ConcreteCategory.hom (i.stalkMap w)
  let _ : Module (U.presheaf.stalk (i w))
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf w) := Module.compHom _ φ
  let el := e.toLinearEquiv
  have hback := isAssociatedPrimeStacks_iff_of_semilinear
    (RingEquiv.refl (U.presheaf.stalk (i w))) el.toAddEquiv (fun r m ↦ el.map_smul r m)
    (p := IsLocalRing.maximalIdeal (U.presheaf.stalk (i w)))
  have hmap : Ideal.map (RingEquiv.refl (U.presheaf.stalk (i w))).toRingHom
      (IsLocalRing.maximalIdeal (U.presheaf.stalk (i w)))
      = IsLocalRing.maximalIdeal (U.presheaf.stalk (i w)) := Ideal.map_id _
  rw [hmap] at hback
  refine hback.symm.trans ?_
  rw [← IsLocalRing.maximalIdeal_comap φ]
  exact isAssociatedPrimeStacks_comap_iff_of_surjective φ (i.stalkMap_surjective w) _

/-- **The associated points of an integral locally Noetherian scheme.** `Ass(W)` is the single
generic point of `W`.

Associated and weakly associated points agree on a locally Noetherian scheme
([Stacks, Tag 05AR]); on a reduced scheme the weakly associated points are the generic points
of the irreducible components ([Stacks, Tag 0EME]); and an irreducible sober `T0` space has
exactly one of those. -/
@[ega "IV 3.2.1" "special case"]
theorem schemeAssociatedPoints_eq_singleton_genericPoint (W : Scheme.{u}) [IsIntegral W]
    [IsLocallyNoetherian W] :
    Stacks.Divisors.schemeAssociatedPoints W = {genericPoint W} :=
  calc Stacks.Divisors.schemeAssociatedPoints W
      = Stacks.Divisors.schemeWeaklyAssociatedPoints W :=
        associatedPoints_eq_weaklyAssociatedPoints W _
    _ = genericPoints W := weaklyAssociatedPointsOfScheme_eq_genericPoints W
    _ = {genericPoint W} := genericPoints_eq_singleton

/-- If `W` is integral and locally Noetherian and `i : W ⟶ U` is a closed immersion, the only
point of `U` associated to `i_* 𝒪_W` is the image of the generic point of `W`. -/
theorem associatedPoints_pushforward_unit_eq_singleton {W U : Scheme.{u}} (i : W ⟶ U)
    [IsClosedImmersion i] [IsIntegral W] [IsLocallyNoetherian W] :
    Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))
      = {i (genericPoint W)} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun y hy ↦ ?_⟩
  · exact (isAssociatedPoint_pushforward_iff_of_isClosedImmersion i _ _).mpr
      ((schemeAssociatedPoints_eq_singleton_genericPoint W).ge rfl)
  · by_cases hr : y ∈ Set.range (ConcreteCategory.hom i.base)
    · obtain ⟨w, rfl⟩ := hr
      exact congrArg _ ((schemeAssociatedPoints_eq_singleton_genericPoint W).le
        ((isAssociatedPoint_pushforward_iff_of_isClosedImmersion i _ w).mp hy))
    · have := subsingleton_stalk_pushforward_of_notMemRange' i
        (SheafOfModules.unit W.ringCatSheaf) y hr
      exact absurd hy (not_isAssociatedPrimeStacks_of_subsingleton _)

/-- For `x` a point of a locally Noetherian scheme `U` and
`i_x : W_x → U` the integral closed subscheme with generic point `x`, the only point of `U`
associated to `i_{x,*} 𝒪_{W_x}` is `x` itself. -/
theorem associatedPoints_pointClosureStructureSheaf {U : Scheme.{u}} [IsLocallyNoetherian U]
    (x : U) : Stacks.Divisors.associatedPoints (pointClosureStructureSheaf x) = {x} := by
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have h := associatedPoints_pushforward_unit_eq_singleton
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U))).subschemeι
  rwa [Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x] at h

/-- The inclusion `Ass(i_{x,*} 𝒪_{W_x}) ⊆ {x}`. -/
theorem associatedPoints_pointClosureStructureSheaf_subset {U : Scheme.{u}}
    [IsLocallyNoetherian U] (x : U) :
    Stacks.Divisors.associatedPoints (pointClosureStructureSheaf x) ⊆ {x} :=
  (associatedPoints_pointClosureStructureSheaf x).le

/-- Let `j : U ⟶ X` be an open immersion into a locally Noetherian scheme, `x ∈ U`, and
`φ : i_{x,*} 𝒪_{W_x} ⟶ F` a morphism to a quasi-coherent module whose pushforward along `j` is
coherent. If `φ` is injective on the stalk at `x`, then the pushforward of `i_{x,*} 𝒪_{W_x}`
along `j` is coherent. -/
theorem isCoherent_pushforward_pointClosure_of_injective_stalk_at
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    {F : U.Modules} [F.IsQuasicoherent]
    (φ : pointClosureStructureSheaf x ⟶ F)
    (hφ : Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf U.ringCatSheaf.obj).map φ.val)).hom)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  refine isCoherent_pushforward_pointClosure_of_injective_on_associatedPoints j x φ (fun y ↦ ?_) hF
  rcases eq_or_ne y x with rfl | hy
  · exact Or.inl hφ
  · exact Or.inr fun hmem ↦ hy (associatedPoints_pointClosureStructureSheaf_subset x hmem)

end AlgebraicGeometry

end
