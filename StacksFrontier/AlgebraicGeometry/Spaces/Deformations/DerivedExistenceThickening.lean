module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Nakayama's lemma along the thickenings `Xₙ ⊂ Xₙ₊₁` of Situation 0DIK

The transitions `Aₙ₊₁ → Aₙ` of Situation 0DIK are surjective with locally nilpotent kernels, so
`Spec Aₙ → Spec Aₙ₊₁` is surjective, and so is its base change `iₙ : Xₙ ⟶ Xₙ₊₁` on points. A
quasi-coherent module of finite type whose pullback along a morphism surjective on points vanishes
is zero: the support of the pullback is the inverse image of the support (Stacks 07TZ).

## Main results

* `AlgebraicGeometry.surjective_spec_map_of_locallyNilpotent_ker`: `Spec` of a surjective ring
  map with locally nilpotent kernel is surjective.
* `AlgebraicGeometry.Space.isZero_of_isZero_modulePullback`: Nakayama's lemma along a morphism of
  algebraic spaces surjective on points, for quasi-coherent modules of finite type.
* `AlgebraicGeometry.Space.surjective_pointsMap_transitionSpace`: `iₙ : Xₙ ⟶ Xₙ₊₁` is surjective
  on points.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry

/-- **`Spec` of a surjective ring map with locally nilpotent kernel is surjective**: every prime
contains the kernel, so it is the preimage of its image. -/
theorem surjective_spec_map_of_locallyNilpotent_ker {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hs : Function.Surjective f.hom) (hn : (RingHom.ker f.hom).LocallyNilpotent) :
    Surjective (Spec.map f) := by
  refine ⟨fun q ↦ ?_⟩
  let q' : PrimeSpectrum R := q
  have := q'.isPrime
  have hker : RingHom.ker f.hom ≤ q'.asIdeal := fun x hx ↦ by
    obtain ⟨k, hk⟩ := hn x hx
    exact q'.isPrime.mem_of_pow_mem k (hk ▸ q'.asIdeal.zero_mem)
  have := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨q'.asIdeal.map f.hom, inferInstance⟩ : PrimeSpectrum S), ?_⟩
  refine PrimeSpectrum.ext ?_
  change Ideal.comap f.hom (Ideal.map f.hom q'.asIdeal) = q'.asIdeal
  rw [Ideal.comap_map_of_surjective' f.hom hs, sup_eq_left.2 hker]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Nakayama's lemma along a morphism surjective on points.** A quasi-coherent module of
finite type whose pullback along a morphism of algebraic spaces surjective on points vanishes is
zero: the support of the pullback is the inverse image of the support (Stacks 07TZ, part (3)). -/
theorem isZero_of_isZero_modulePullback {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (hg : Function.Surjective (pointsMap B S hS X'.1 g.hom))
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (h : IsZero ((modulePullback B S hS g).obj F)) : IsZero F := by
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS X F).1 ?_
  have h' := (supportOfSheaf_eq_empty_iff_isZero B S hS X' _).2 h
  rw [supportOfSheaf_modulePullback_eq B S hS g F hqc hft] at h'
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := hg x
  exact (Set.eq_empty_iff_forall_notMem.1 h') y hx

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B' : BigFppfSite.{u})
    (hS' : B'.Contains (limitBase F)) (hSn : ∀ n : ℕ, B'.Contains (baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B' hS')))

/-- **The thickening `iₙ : Xₙ ⟶ Xₙ₊₁` is surjective on points** when the transition `Aₙ₊₁ → Aₙ`
is surjective with locally nilpotent kernel: it is the base change of `Spec Aₙ → Spec Aₙ₊₁`. -/
theorem surjective_pointsMap_transitionSpace (n : ℕ)
    (hs : Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (hn : (RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent) :
    Function.Surjective (pointsMap B' (limitBase F) hS' (spaceAt F B' hS' hSn X n).1
      (transitionSpace F B' hS' hSn X n).hom) := by
  have hbase : Function.Surjective (pointsMap B' (limitBase F) hS'
      (schemeSpace (baseObjectAt F B' hS' hSn n)).1 (baseSpaceTransition F B' hS' hSn n).hom) :=
    (surjective_iff_surjective_pointsMap B' (limitBase F) hS' _
      (isAlgebraicSpace_yoneda B' (limitBase F) hS' _) _ _).1
      ((presheaf_yoneda_map_iff B' (limitBase F) hS' inferInstance
        (baseObjectTransition F B' hS' hSn n)).2
        (surjective_spec_map_of_locallyNilpotent_ker _ hs hn))
  exact surjective_pointsMap_of_isPullback B' (limitBase F) hS'
    (AlgebraicSpaces.isPullback_hom B' (limitBase F) hS'
      (isPullback_transitionSpace F B' hS' hSn X n)) hbase

end Space

end AlgebraicGeometry

end
