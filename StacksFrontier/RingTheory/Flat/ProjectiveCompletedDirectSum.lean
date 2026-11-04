module

public import Mathlib.Algebra.DirectSum.Finsupp
public import StacksFrontier.Algebra.MittagLeffler.Pi
public import StacksFrontier.Algebra.MittagLeffler.ShortExact
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# The completion of a direct sum over a complete Noetherian ring

Let `R` be a Noetherian ring which is complete with respect to an ideal `I`, and let `A` be a
set. This file proves Stacks 05DJ: the `I`-adic completion of `⊕_{α ∈ A} R` is a flat
Mittag-Leffler `R`-module.

The flatness half needs neither completeness nor the direct sum: it is
`AdicCompletion.flat_directSum`, Stacks 06LE, already in the library, and this file only records
the tag 05DJ on it. The Mittag-Leffler half is the source's argument. The comparison map
`AdicCompletion.directSumToPi` from the completed direct sum to the product `∏_{α ∈ A} R` is
universally injective (Stacks 05BC), the product is flat and Mittag-Leffler (Stacks 05D0), and
the Mittag-Leffler property passes from the target of a universally injective map to its source
(Stacks 059N), applied to the universally exact sequence with that map as its first term.

## Main results

* `AdicCompletion.isMittagLeffler_finsupp`: for a Noetherian `I`-adically complete ring `R` and
  a set `A`, the `I`-adic completion of `A →₀ R` is a Mittag-Leffler `R`-module.

## Implementation notes

Stacks 05D0 is available in the library as `Module.flat_and_mittagLeffler_pi`, but only with the
ring, the index set and all test data in a single universe. The argument for 05DJ needs the index
set and the test data of the Mittag-Leffler condition in a universe potentially larger than that
of `R`, so the two halves of 05D0 are reproved here in that generality, as the private lemmas
`flat_pi_of_isNoetherianRing` and `isMittagLeffler_pi_of_isNoetherianRing`; their proofs are the
proofs of 05D0, with `R` replaced by a `Small` copy where the Mathlib API demands it.

Stacks 059N and Stacks 0AS5 are both stated for modules in one universe, while the statement of
05DJ quantifies the Mittag-Leffler test data independently of the index set. Everything in sight
is therefore lifted into the single universe `max uR uA uP uN` before those two lemmas are
applied, and the resulting witness is shrunk back down to `max uR uP`; being a finite module over
`R`, it is small in that universe.

The direct sum `⊕_{α ∈ A} R` is spelled `A →₀ R` in the Mittag-Leffler statement, matching the
shape in which Stacks 05DK consumes it, and `DirectSum A (fun _ => R)` in the flatness statement,
matching `AdicCompletion.flat_directSum`; the two are identified by `finsuppLEquivDirectSum`.

## References

* [Stacks Project, Tag 05DJ](https://stacks.math.columbia.edu/tag/05DJ)
-/

@[expose] public section

open scoped TensorProduct

universe uR uA uP uN

add_to_stacks 05DJ "flatness; neither `IsAdicComplete` nor the shape of the direct sum is needed,
so the library statement is the more general Tag 06LE" AdicCompletion.flat_directSum

namespace AdicCompletion

/-- Stacks 05D0, flatness half, with the index set in an arbitrary universe: for a Noetherian
ring `R` and a set `A`, the `R`-module `A → R` is flat. -/
private theorem flat_pi_of_isNoetherianRing (R : Type uR) [CommRing R] [IsNoetherianRing R]
    (A : Type uA) : Module.Flat R (A → R) := by
  classical
  let R' := ULift.{max uR uA} R
  let e : R' ≃+* R := ULift.ringEquiv
  have : IsNoetherianRing R' :=
    isNoetherianRing_of_surjective R R' e.symm.toRingHom e.symm.surjective
  have hchase : IsCoherentRing R' ↔ ∀ B : Type (max uR uA), Module.Flat R' (B → R') :=
    (IsCoherentRing.tfae_flat_pi R').out 1 3
  have hflat : Module.Flat R' (Shrink.{max uR uA} A → R') :=
    hchase.mp (isCoherentRing_of_isNoetherianRing R') _
  let eR : R' ≃ₗ[R'] R :=
    { toFun := ULift.down, invFun := ULift.up, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let eA : (Shrink.{max uR uA} A → R') ≃ₗ[R'] (A → R) :=
    (LinearEquiv.piCongrRight fun _ => eR).trans
      (LinearEquiv.funCongrLeft R' R (equivShrink A))
  exact Module.Flat.ulift_left_iff.mp (Module.Flat.of_linearEquiv (R := R') eA.symm)

/-- The span of the coordinates of `x ∈ F ⊗[R] (A → R)` is the smallest submodule `N ⊆ F` with
`x` in the image of `N ⊗[R] (A → R)`. This is the key step of Stacks 05D0, in the generality
needed for Stacks 05DJ. -/
private theorem isLeast_span_range_piScalarRightHom {R : Type uR} [CommRing R]
    [IsNoetherianRing R] [Small.{max uR uA} R] (A : Type (max uR uA))
    (F : Type (max uR uA)) [AddCommGroup F] [Module R F] [Module.Finite R F]
    (x : F ⊗[R] (A → R)) :
    IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor (A → R))}
      (Submodule.span R (Set.range (TensorProduct.piScalarRightHom R R F A x))) := by
  have hbij : ∀ (G : Type (max uR uA)) [AddCommGroup G] [Module R G] [Module.Finite R G],
      Function.Bijective (TensorProduct.piScalarRightHom R R G A) := fun G _ _ _ => by
    have hfp : Module.FinitePresentation R G := Module.finitePresentation_of_finite R G
    have h : Module.FinitePresentation R G ↔
        ∀ B : Type (max uR uA), Function.Bijective (TensorProduct.piScalarRightHom R R G B) :=
      (Module.FinitePresentation.tfae_piRightHom_bijective R G).out 1 4
    exact h.mp hfp A
  set F' := Submodule.span R (Set.range (TensorProduct.piScalarRightHom R R F A x)) with hF'
  have hmem : ∀ a, TensorProduct.piScalarRightHom R R F A x a ∈ F' :=
    fun a => Submodule.subset_span ⟨a, rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := (hbij F').surjective fun a => (⟨_, hmem a⟩ : F')
    refine ⟨y, (hbij F).injective (funext fun a => ?_)⟩
    rw [TensorProduct.piScalarRightHom_rTensor_apply, hy]
    rfl
  · rintro N ⟨y, hy⟩
    rw [hF', Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← hy, TensorProduct.piScalarRightHom_rTensor_apply]
    exact (TensorProduct.piScalarRightHom R R (↥N) A y a).2

/-- Stacks 05D0, Mittag-Leffler half, with the index set and the test data in an arbitrary
universe above that of `R`. -/
private theorem isMittagLeffler_pi_of_isNoetherianRing {R : Type uR} [CommRing R]
    [IsNoetherianRing R] [Small.{max uR uA} R] (A : Type (max uR uA)) :
    IsMittagLeffler.{uR, max uR uA, max uR uA, max uR uA, max uR uA} R (A → R) := by
  have : Module.Flat R (A → R) := flat_pi_of_isNoetherianRing R A
  rw [isMittagLeffler_def_iff]
  exact (Module.mittagLeffler_iff_exists_isLeast_mem_range_rTensor_subtype R (A → R)).2
    fun F _ _ _ _ x => ⟨_, isLeast_span_range_piScalarRightHom A F x⟩

/-- A linear equivalence carries `I • ⊤` to `I • ⊤`. -/
private theorem map_smul_top_of_linearEquiv {R : Type uR} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (I : Ideal R) :
    (I • (⊤ : Submodule R M)).map e.toLinearMap = I • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'', Submodule.map_top, e.range]

/-- Transporting the injectivity of `Submodule.mapQ` along linear equivalences of the source and
the target. -/
private theorem injective_mapQ_congr {R : Type uR} [CommRing R] {M N M' N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] {p : Submodule R M} {q : Submodule R N} {p' : Submodule R M'}
    {q' : Submodule R N'} (f : M →ₗ[R] N) (eM : M' ≃ₗ[R] M) (eN : N ≃ₗ[R] N')
    (hp : p'.map eM.toLinearMap = p) (hq : q.map eN.toLinearMap = q') (h₀ : p ≤ q.comap f)
    (hf : Function.Injective (p.mapQ q f h₀)) :
    Function.Injective (p'.mapQ q' (eN.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap)
      (fun x hx => by
        have hxp : eM x ∈ p := hp ▸ ⟨x, hx, rfl⟩
        exact hq ▸ ⟨f (eM x), h₀ hxp, rfl⟩)) := by
  refine (Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff _ _).2 fun x hx => ?_
  have hx' : f (eM x) ∈ q := by
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp (show eN (f (eM x)) ∈ q.map eN.toLinearMap by
      simpa [hq] using hx)
    exact eN.injective heq ▸ hy
  obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp
    (hp ▸ (Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff f h₀).mp hf hx' :
    eM x ∈ p'.map eM.toLinearMap)
  exact eM.injective heq ▸ hy

/-- An inclusion of kernels transports along additive equivalences commuting with the two maps. -/
private theorem ker_le_ker_of_comm {R X Y Z X' Y' Z' : Type*} [Semiring R] [AddCommMonoid X]
    [Module R X] [AddCommMonoid Y] [Module R Y] [AddCommMonoid Z] [Module R Z] [AddCommMonoid X']
    [Module R X'] [AddCommMonoid Y'] [Module R Y'] [AddCommMonoid Z'] [Module R Z']
    {f : X →ₗ[R] Y} {g : X →ₗ[R] Z} {f' : X' →ₗ[R] Y'} {g' : X' →ₗ[R] Z'} (eX : X ≃+ X')
    (eY : Y ≃+ Y') (eZ : Z ≃+ Z') (hf : ∀ x, f' (eX x) = eY (f x))
    (hg : ∀ x, g' (eX x) = eZ (g x)) (h : LinearMap.ker f ≤ LinearMap.ker g) :
    LinearMap.ker f' ≤ LinearMap.ker g' := by
  intro x hx
  obtain ⟨y, rfl⟩ := eX.surjective x
  simp only [LinearMap.mem_ker, hf, hg, AddEquivClass.map_eq_zero_iff] at hx ⊢
  exact h hx

/-- Applying `map v id` after the equivalence `rTensor eA` then `lTensor eT` agrees with applying
the equivalence for `eB` after `map u id`, when `v ∘ eA = eB ∘ u`. -/
private theorem map_id_rTensor_lTensor_comm {R : Type uR} [CommRing R] {A A' B B' T T' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A'] [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] [AddCommGroup T] [Module R T] [AddCommGroup T'] [Module R T']
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eT : T' ≃ₗ[R] T) (u : A' →ₗ[R] B') (v : A →ₗ[R] B)
    (h : ∀ x, v (eA x) = eB (u x)) (x : A' ⊗[R] T') :
    TensorProduct.map v (LinearMap.id : T →ₗ[R] T)
        (((LinearEquiv.rTensor T' eA).trans (LinearEquiv.lTensor A eT)) x) =
      ((LinearEquiv.rTensor T' eB).trans (LinearEquiv.lTensor B eT))
        (TensorProduct.map u (LinearMap.id : T' →ₗ[R] T') x) := by
  refine TensorProduct.induction_on x (by simp) (fun p t => by simp [h]) ?_
  intro x y hx hy
  simp only [map_add, hx, hy]

/-- **Stacks Project, Tag 05DJ.** If `R` is Noetherian and `I`-adically complete, then the
`I`-adic completion of the direct sum of an `A`-indexed family of copies of `R` is a
Mittag-Leffler `R`-module. -/
@[stacks 05DJ "the Mittag-Leffler property; the direct sum `⊕_{α ∈ A} R` is spelled `A →₀ R`.
Mittag-Leffler is `IsMittagLeffler`, condition (1) of 059E, as in 059N and 059X."]
theorem isMittagLeffler_finsupp {R : Type uR} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete I R] (A : Type uA) :
    IsMittagLeffler.{uR, uP, max uR uA, max uR uP, uN} R (AdicCompletion I (A →₀ R)) := by
  classical
  -- The single universe into which everything is lifted.
  let A₂ : Type (max uR uA uP uN) := ULift.{max uR uA uP uN} A
  let eA : A₂ ≃ A := Equiv.ulift
  let eN : (A → R) ≃ₗ[R] (A₂ → R) := LinearEquiv.funCongrLeft R R eA
  let M := AdicCompletion I (A →₀ R)
  let eC : M ≃ₗ[R] AdicCompletion I (DirectSum A fun _ : A => R) :=
    (AdicCompletion.congr I (finsuppLEquivDirectSum R R A)).restrictScalars R
  let f₀ : M →ₗ[R] (A → R) := (AdicCompletion.directSumToPi R I A) ∘ₗ eC.toLinearMap
  let M' := ULift.{max uR uA uP uN} M
  let eM : M' ≃ₗ[R] M := ULift.moduleEquiv
  let f' : M' →ₗ[R] (A₂ → R) := eN.toLinearMap ∘ₗ f₀ ∘ₗ eM.toLinearMap
  have hUI : UniversallyInjective f₀ := fun T _ _ => by
    rw [LinearMap.rTensor_comp]
    exact (AdicCompletion.universallyInjective_directSumToPi R I A T).comp
      (eC.rTensor T).injective
  have : Module.Flat R (A → R) := flat_pi_of_isNoetherianRing R A
  have hUI' : UniversallyInjective f' := by
    have : Module.Flat R (A₂ → R) := flat_pi_of_isNoetherianRing R A₂
    refine (Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top f').mpr fun J hJ => ?_
    exact injective_mapQ_congr f₀ eM eN (map_smul_top_of_linearEquiv eM J)
      (map_smul_top_of_linearEquiv eN J) (Submodule.smul_top_le_comap_smul_top J f₀)
      ((Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top f₀).mp hUI hJ)
  -- `A₂ → R` is Mittag-Leffler, and universal injectivity of `f'` passes this to `M'`.
  have hMLM' : IsMittagLeffler.{uR, max uR uA uP uN, max uR uA uP uN, max uR uA uP uN,
      max uR uA uP uN} R M' := by
    rw [isMittagLeffler_def_iff]
    refine (Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
      (M₃ := (A₂ → R) ⧸ LinearMap.range f') (LinearMap.exact_map_mkQ_range f')
      (Submodule.mkQ_surjective _) hUI').1 ?_
    exact (isMittagLeffler_def_iff R (A₂ → R)).mp (isMittagLeffler_pi_of_isNoetherianRing A₂)
  -- Descend the conclusion from `M'` back to `M`.
  intro P _ _ hP g
  let P' : Type (max uR uA uP uN) := ULift.{max uR uA uP uN} P
  let eP : P' ≃ₗ[R] P := ULift.moduleEquiv
  have : Module.FinitePresentation R P' := (LinearEquiv.finitePresentation_iff eP).mpr hP
  obtain ⟨Q, hQadd, hQmod, hQfp, k, hdom⟩ := hMLM' P' (eM.symm.toLinearMap ∘ₗ g ∘ₗ eP.toLinearMap)
  have : Module.FinitePresentation R Q := hQfp
  have : Small.{max uR uP} Q := Module.Finite.small R Q
  let eQ : Shrink.{max uR uP} Q ≃ₗ[R] Q := Shrink.linearEquiv R Q
  have : Module.FinitePresentation R (Shrink.{max uR uP} Q) :=
    (LinearEquiv.finitePresentation_iff eQ).mpr hQfp
  refine ⟨Shrink.{max uR uP} Q, inferInstance, inferInstance, inferInstance,
    eQ.symm.toLinearMap ∘ₗ k ∘ₗ eP.symm.toLinearMap, ?_, ?_⟩
  all_goals
    intro T _ _
    let T' : Type (max uR uA uP uN) := ULift.{max uR uA uP uN} T
    let eT : T' ≃ₗ[R] T := ULift.moduleEquiv
    let dX : (P' ⊗[R] T') ≃ₗ[R] (P ⊗[R] T) :=
      (LinearEquiv.rTensor T' eP).trans (LinearEquiv.lTensor P eT)
    let dY : (M' ⊗[R] T') ≃ₗ[R] (M ⊗[R] T) :=
      (LinearEquiv.rTensor T' eM).trans (LinearEquiv.lTensor M eT)
    let dZ : (Q ⊗[R] T') ≃ₗ[R] (Shrink.{max uR uP} Q ⊗[R] T) :=
      (LinearEquiv.rTensor T' eQ.symm).trans (LinearEquiv.lTensor (Shrink.{max uR uP} Q) eT)
    have hf := map_id_rTensor_lTensor_comm eP eM eT (eM.symm.toLinearMap ∘ₗ g ∘ₗ eP.toLinearMap) g
      fun x => by simp
    have hg := map_id_rTensor_lTensor_comm eP eQ.symm eT k
      (eQ.symm.toLinearMap ∘ₗ k ∘ₗ eP.symm.toLinearMap) fun x => by simp
    first
    | exact ker_le_ker_of_comm dX.toAddEquiv dY.toAddEquiv dZ.toAddEquiv hf hg (hdom.1 T')
    | exact ker_le_ker_of_comm dX.toAddEquiv dZ.toAddEquiv dY.toAddEquiv hg hf (hdom.2 T')

end AdicCompletion

end
