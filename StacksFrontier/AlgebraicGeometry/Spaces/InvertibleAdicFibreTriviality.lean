module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFormalFunctionsDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreIdealPower
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitting

/-!
# Invertible modules trivial on every adic fibre

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `X` be a proper algebraic
space over `Spec A` and write `Xₙ = X ×_{Spec A} Spec(A/Iⁿ⁺¹)` for its adic fibres. An invertible
`𝒪_X`-module `L` whose restriction to every `Xₙ` is trivial is trivial. No compatibility between
the trivializations on the different `Xₙ` is required.

This is the step "the map `Pic(Y) → Pic(X)` is injective … by Grothendieck's existence theorem"
of the argument of the Stacks project preceding Tag 0D1R, in the form that argument uses once the
deformations of `𝒪_X` to the thickenings are known to be trivial.

## The argument

By the theorem on formal functions in degree zero, clause (3) of Stacks 08AY, there is a `k ≥ 1`
such that the image of `H⁰(X, L/IᵏL) → H⁰(X, L/IL)` is the image of `H⁰(X, L) → H⁰(X, L/IL)`.
A trivialization `𝒪_{X_{k-1}} ≅ L|_{X_{k-1}}` gives, through `L/IᵏL ≅ (ι_{k-1})_* ι_{k-1}^* L`
(Stacks 04CJ), an epimorphism `𝒪_X → L/IᵏL`; its image in `H⁰(X, L/IL)` lifts to a section
`s : 𝒪_X → L`, and `s` is surjective modulo `I`, hence on the fibre `X₀`. The support of the
cokernel of `s` is closed and its image in `Spec A` is closed because `X` is proper; it misses
`V(I)`, which meets every nonempty closed subset of `Spec A` as `I` lies in the Jacobson radical.
So `s` is surjective, hence an isomorphism of invertible modules.

## Main results

* `AlgebraicGeometry.Space.exists_pointsMap_adicThickeningMap_mem_of_isClosed`: over an
  `I`-adically complete ring, every nonempty closed subset of `Spec A` meets `Spec(A/Iⁿ⁺¹)`.
* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_adicFibreInclusion`: a map of
  quasi-coherent modules on `X`, with target of finite type, which is surjective on an adic fibre
  is surjective.
* `AlgebraicGeometry.Space.exists_unit_hom_comp_idealQuotientπ_eq`: sections of `K / IᵏK`, for
  `k` large, lift to `K` modulo `Iⁿ` (Stacks 08AY, clause (3), in degree zero).
* `AlgebraicGeometry.Space.nonempty_iso_unit_of_forall_adicFibre_iso_unit`: **an invertible
  module trivial on every adic fibre is trivial.**
* `AlgebraicGeometry.Space.eq_zero_of_forall_picardPullback_adicFibreInclusion_eq_zero` and
  `AlgebraicGeometry.Space.injective_picardPullback_adicFibreInclusion`: **`Pic(X) → ∏ₙ Pic(Xₙ)`
  is injective.**
* `AlgebraicGeometry.Space.nonempty_iso_of_forall_adicFibre_iso`:
  two invertible modules isomorphic on every adic fibre are isomorphic.
* `AlgebraicGeometry.Space.nonempty_iso_of_adicFibreRestriction_iso`: coherent modules with
  isomorphic systems of restrictions to the adic fibres are isomorphic (Stacks 08BF).

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology hasCokernels_modules

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **Over an `I`-adically complete ring, every nonempty closed subset of `Spec A` meets
`Spec(A/Iⁿ⁺¹)`**, on the points of the algebraic spaces they represent: a nonempty closed set
contains a closed point, a maximal ideal, which contains `I` because `I` lies in the Jacobson
radical. -/
theorem exists_pointsMap_adicThickeningMap_mem_of_isClosed [IsAdicComplete I A] (n : ℕ)
    (W : Set (points B (Spec (.of A)) hA (schemeSpace (baseObject A B hA)).1)) (hW : IsClosed W)
    (hne : W.Nonempty) :
    ∃ y₀, pointsMap B (Spec (.of A)) hA
      (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)).1
      (schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)).hom y₀ ∈
        W := by
  refine exists_pointsMap_yoneda_mem_of_isClosed _ (fun W hW ⟨w, hw⟩ => ?_) W hW hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (w : PrimeSpectrum A).asIdeal
    (w : PrimeSpectrum A).isPrime.ne_top
  have hjac : (⊥ : Ideal A).jacobson ≤ m := sInf_le ⟨bot_le, hm⟩
  have hIm : I ^ (n + 1) ≤ m :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans ((IsAdicComplete.le_jacobson_bot I).trans hjac)
  have hker : RingHom.ker (Ideal.Quotient.mk (I ^ (n + 1))) ≤ m := by
    rw [Ideal.mk_ker]
    exact hIm
  let v : PrimeSpectrum (A ⧸ I ^ (n + 1)) :=
    ⟨Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) m,
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
  have hv : PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1))) v = ⟨m, hm.isPrime⟩ := by
    ext1
    exact (Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective m).trans
      (sup_eq_left.2 hker)
  refine ⟨v, ?_⟩
  change (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1))) v : PrimeSpectrum A) ∈ W
  rw [hv]
  exact (((PrimeSpectrum.le_iff_specializes (w : PrimeSpectrum A) ⟨m, hm.isPrime⟩).1 hle).mem_closed
    hW hw)

/-- **A map of quasi-coherent modules on a proper algebraic space over an `I`-adically complete
ring which is surjective on an adic fibre is surjective**, for a target of finite type. -/
theorem epi_of_epi_modulePullback_adicFibreInclusion [IsAdicComplete I A]
    (hf : IsProper B (Spec (.of A)) hA f.hom) (n : ℕ)
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (hNft : SheafOfModules.IsFiniteTypeOnSite N) (u : M ⟶ N)
    (hu : Epi ((modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).map u)) :
    Epi u :=
  epi_of_epi_modulePullback_of_isPullback f hf.2.2 _ (adicFibreProjection A I B hA X f n)
    (adicFibreInclusion A I B hA X f n) (IsPullback.of_hasPullback _ _)
    (exists_pointsMap_adicThickeningMap_mem_of_isClosed I n) hM hN hNft u hu

/-! ### Lifting sections modulo `I` -/

section Lifting

attribute [local instance] hasInjectiveResolutions_modules

variable [IsNoetherianRing A]
  (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
  (K : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 K]

include hX in
/-- **Sections modulo `Iⁿ` that lift far enough lift to `X`**: for a coherent module `K` on a
proper algebraic space over a Noetherian ring `A` and every `n`, there is a `k ≥ n` such that the
image in `K / IⁿK` of every section of `K / IᵏK` is the image of a section of `K`.  This is
clause (3) of the theorem on formal functions (Stacks 08AY) in degree zero, read on morphisms out
of `𝒪_X`. -/
theorem exists_unit_hom_comp_idealQuotientπ_eq (n : ℕ) :
    ∃ k, ∃ h : n ≤ k, ∀ a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶
        idealQuotient (baseRingHom A B hA X.1 X.2) K (I ^ k),
      ∃ s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶ K,
        s ≫ idealQuotientπ (baseRingHom A B hA X.1 X.2) K (I ^ n) =
          a ≫ idealQuotientMap (baseRingHom A B hA X.1 X.2) K (Ideal.pow_le_pow_right h) := by
  obtain ⟨c, -, hc⟩ := exists_adicCohomology_bounds X hX K I 0
  obtain ⟨k, hnk, hk⟩ := hc n
  refine ⟨k, hnk, fun a => ?_⟩
  let φ := baseRingHom A B hA X.1 X.2
  let Q := idealQuotient φ K (I ^ k)
  let Qn := idealQuotient φ K (I ^ n)
  let x : adicCohomology φ K I 0 k := (cohomologyResZeroIso X Q).inv (Q.unitHomEquiv a)
  obtain ⟨y, hy⟩ : adicCohomologyMap φ K I 0 n k hnk x ∈
      LinearMap.range (adicCohomologyProj φ K I 0 n) := by
    rw [← hk k hnk le_rfl]
    exact LinearMap.mem_range_self _ x
  refine ⟨K.unitHomEquiv.symm ((cohomologyResZeroIso X K).hom y), Qn.unitHomEquiv.injective ?_⟩
  have h1 := cohomologyResZeroIso_naturality X (idealQuotientπ φ K (I ^ n)) y
  have h2 := cohomologyResZeroIso_naturality X
    (idealQuotientMap φ K (Ideal.pow_le_pow_right hnk)) x
  have hx : (cohomologyResZeroIso X Q).hom x = Q.unitHomEquiv a :=
    Iso.inv_hom_id_apply (cohomologyResZeroIso X Q) _
  rw [SheafOfModules.unitHomEquiv_comp_apply, SheafOfModules.unitHomEquiv_comp_apply, ← hx]
  exact (congrArg (SheafOfModules.sectionsMap (idealQuotientπ φ K (I ^ n)))
    (K.unitHomEquiv.apply_symm_apply _)).trans
      (h1.symm.trans ((congrArg (cohomologyResZeroIso X Qn).hom hy).trans h2))

end Lifting

/-! ### Triviality on the adic fibres -/

section Triviality

variable [IsNoetherianRing A] [IsAdicComplete I A]

omit [IsNoetherianRing A] in
/-- **A section of an invertible module which is surjective modulo `I` trivializes it**: for `X`
proper over an `I`-adically complete ring, a map `s : 𝒪_X ⟶ L` to an invertible module
whose composite with `L ⟶ L / I L` is an epimorphism is an isomorphism.  The projection
`L ⟶ L / I L ≅ (ι₀)_* ι₀^* L` is an isomorphism after pullback to `X₀`, so `s` is surjective on
`X₀`; then it is surjective (`epi_of_epi_modulePullback_adicFibreInclusion`), hence an isomorphism
of invertible modules. -/
theorem isIso_of_epi_comp_idealQuotientπ (hf : IsProper B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶ L)
    (hsπ : Epi (s ≫ idealQuotientπ (baseRingHom A B hA X.1 X.2) L (I ^ (0 + 1)))) :
    IsIso s := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  let := fun n => SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
      (adicFibreSpaceOf A I B hA X f n).1 (adicFibreSpaceOf A I B hA X f n).2).O)
  let φ := baseRingHom A B hA X.1 X.2
  let O := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
  let ι := adicFibreInclusion A I B hA X f
  let adj := fun n => modulePullbackAdjunction B (Spec (.of A)) hA (ι n)
  have hLq : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X L hL
  have hO : IsInvertibleModule X O := Stacks.SheafOfModules.isInvertible_unit _ _
  have hOq : O.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X O hO
  have hι : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (ι n).hom :=
    isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom
  have hker : ∀ n (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      kerIdealSmul B (Spec (.of A)) hA (ι n) M =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) M :=
    fun n M => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA X.2 f.hom n M
  -- The projection `L ⟶ L / I L` is an isomorphism on `X₀`.
  obtain ⟨e₀, he₀⟩ := exists_idealPowerQuotient_iso_comp_eq_unit_comp B (Spec (.of A)) hA ι hι
    hker 0 L _ (Iso.refl _)
  have hπη : idealQuotientπ φ L (I ^ (0 + 1)) ≫
      ((idealQuotientIsoIdealPowerQuotient X I L hLq (0 + 1)).hom ≫ e₀.hom) =
        (adj 0).unit.app L := by
    rw [← Category.assoc]
    change (idealQuotientπ φ L (I ^ (0 + 1)) ≫ idealQuotientToIdealPowerQuotient X I L (0 + 1)) ≫
      e₀.hom = _
    rw [idealQuotientπ_comp_idealQuotientToIdealPowerQuotient, he₀, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.comp_id]
  let F := modulePullback B (Spec (.of A)) hA (ι 0)
  have hε : IsIso ((adj 0).counit.app (F.obj L)) := by
    have hff := fullyFaithfulModulePushforward B (Spec (.of A)) hA (ι 0) (hι 0)
    have := hff.full
    have := hff.faithful
    infer_instance
  have hFη : IsIso (F.map ((adj 0).unit.app L)) := by
    have h : F.map ((adj 0).unit.app L) = inv ((adj 0).counit.app (F.obj L)) := by
      exact IsIso.eq_inv_of_inv_hom_id ((adj 0).left_triangle_components L)
    rw [h]
    infer_instance
  have hFπ : IsIso (F.map (idealQuotientπ φ L (I ^ (0 + 1)))) := by
    have : IsIso (F.map (idealQuotientπ φ L (I ^ (0 + 1))) ≫
        F.map ((idealQuotientIsoIdealPowerQuotient X I L hLq (0 + 1)).hom ≫ e₀.hom)) := by
      rw [← F.map_comp, hπη]
      exact hFη
    exact IsIso.of_isIso_comp_right _ (F.map ((idealQuotientIsoIdealPowerQuotient X I L hLq
      (0 + 1)).hom ≫ e₀.hom))
  -- Hence `s` is surjective on `X₀`, so surjective, so an isomorphism.
  have := (adj 0).isLeftAdjoint
  have hFs : Epi (F.map s) := by
    have : F.map s = F.map (s ≫ idealQuotientπ φ L (I ^ (0 + 1))) ≫
        inv (F.map (idealQuotientπ φ L (I ^ (0 + 1)))) := by
      rw [F.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    exact epi_comp _ _
  have hLfp : L.IsFinitePresentationOnSite := isFinitePresentationOnSite_of_isInvertibleModule L hL
  have hsepi : Epi s :=
    epi_of_epi_modulePullback_adicFibreInclusion I X f hf 0 hOq hLq inferInstance s hFs
  exact isIso_of_epi_of_isInvertibleModule hO hL s

/-- **An invertible module trivial on every adic fibre is trivial.**  Let `A` be a Noetherian
ring complete with respect to an ideal `I` and `X` a proper algebraic space over `Spec A`.  If an
invertible `𝒪_X`-module `L` restricts to a trivial module on every adic fibre
`Xₙ = X ×_{Spec A} Spec(A/Iⁿ⁺¹)`, then `L ≅ 𝒪_X`.  The trivializations on the different `Xₙ` are
not assumed compatible.

This is the injectivity of `Pic(Y) → Pic(X)` in the argument of the Stacks project preceding
Tag 0D1R, once every deformation of `𝒪_X` to the thickenings is known to be trivial. -/
theorem nonempty_iso_unit_of_forall_adicFibre_iso_unit
    (hf : IsProper B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (h : ∀ n, Nonempty ((modulePullback B (Spec (.of A)) hA
      (adicFibreInclusion A I B hA X f n)).obj L ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1
            (adicFibreSpaceOf A I B hA X f n).2).O)))) :
    Nonempty (L ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))) := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  let := fun n => SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
      (adicFibreSpaceOf A I B hA X f n).1 (adicFibreSpaceOf A I B hA X f n).2).O)
  let φ := baseRingHom A B hA X.1 X.2
  let O := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
  let ι := adicFibreInclusion A I B hA X f
  let adj := fun n => modulePullbackAdjunction B (Spec (.of A)) hA (ι n)
  have hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1) := by
    rw [(isTerminal_yoneda_obj_base B _ hA).hom_ext ((isTerminal_yoneda_obj_base B _ hA).from X.1)
      f.hom]
    exact hf
  have := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.2.1.1
  have hLc : IsCoherent B (Spec (.of A)) hA X.1 X.2 L := isCoherent_of_isInvertible L hL
  have hLq : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X L hL
  have hO : IsInvertibleModule X O := Stacks.SheafOfModules.isInvertible_unit _ _
  have hOq : O.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X O hO
  have hι : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (ι n).hom :=
    isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom
  have hker : ∀ n (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      kerIdealSmul B (Spec (.of A)) hA (ι n) M =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) M :=
    fun n M => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA X.2 f.hom n M
  -- A level `k = m + 1` from which sections modulo `I` lift.
  obtain ⟨k, h1k, hk⟩ := exists_unit_hom_comp_idealQuotientπ_eq I X hX L (0 + 1)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨e⟩ := h m
  let e₂ := e ≪≫ (modulePullbackUnitIso B (Spec (.of A)) hA (ι m)).symm
  obtain ⟨e', -⟩ := exists_idealPowerQuotient_iso_comp_eq_unit_comp B (Spec (.of A)) hA ι hι hker
    m L _ e₂
  -- The trivialization on `Xₘ` gives an epimorphism `𝒪_X ⟶ L / Iᵐ⁺¹ L`.
  have hηO : Epi ((adj m).unit.app O) := by
    have hq := isUnitQuotient_idealPowerQuotient B (Spec (.of A)) hA ι hι hker O
    rw [← hq.comp_hom m]
    exact @epi_comp' _ _ _ _ _ _ _ (hq.epi m) (IsIso.epi_of_iso _)
  let a : O ⟶ idealQuotient φ L (I ^ (m + 1)) :=
    (adj m).unit.app O ≫ e'.inv ≫ (idealQuotientIsoIdealPowerQuotient X I L hLq (m + 1)).inv
  have ha : Epi a := epi_comp' hηO (epi_comp' (IsIso.epi_of_iso _) (IsIso.epi_of_iso _))
  obtain ⟨s, hs⟩ := hk a
  have hle : I ^ (m + 1) ≤ I ^ (0 + 1) := Ideal.pow_le_pow_right h1k
  have hmap : Epi (idealQuotientMap φ L hle) :=
    @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_idealQuotientπ φ L (I ^ (0 + 1)))
      (idealQuotientπ_idealQuotientMap φ L hle)
  have hsπ : Epi (s ≫ idealQuotientπ φ L (I ^ (0 + 1))) := by
    rw [hs]
    exact epi_comp' ha hmap
  have hsiso : IsIso s := isIso_of_epi_comp_idealQuotientπ I X f hf L hL s hsπ
  exact ⟨(asIso s).symm⟩

/-- **A Picard class of `X` which vanishes on every adic fibre vanishes**: the kernel of
`Pic(X) → ∏ₙ Pic(Xₙ)` is trivial, for `X` proper over a Noetherian `I`-adically complete ring. -/
theorem eq_zero_of_forall_picardPullback_adicFibreInclusion_eq_zero
    (hf : IsProper B (Spec (.of A)) hA f.hom) (x : picardGroup X)
    (h : ∀ n, picardPullback (adicFibreInclusion A I B hA X f n) x = 0) : x = 0 := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass X x
  obtain ⟨e⟩ := nonempty_iso_unit_of_forall_adicFibre_iso_unit I X
    f hf L hL fun n => by
      have hn := h n
      rw [picardPullback_picardClass] at hn
      exact (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).1 hn
  exact (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).2 ⟨e⟩

/-- **`Pic(X) → ∏ₙ Pic(Xₙ)` is injective** for an algebraic space `X` proper over a Noetherian
ring `A` complete with respect to `I`, where `Xₙ = X ×_{Spec A} Spec(A/Iⁿ⁺¹)`. -/
theorem injective_picardPullback_adicFibreInclusion (hf : IsProper B (Spec (.of A)) hA f.hom) :
    Function.Injective fun (x : picardGroup X) (n : ℕ) =>
      picardPullback (adicFibreInclusion A I B hA X f n) x := by
  intro x y hxy
  refine sub_eq_zero.1 (eq_zero_of_forall_picardPullback_adicFibreInclusion_eq_zero I X f hf _
    fun n => ?_)
  have hn := congrFun hxy n
  rw [← picardPullbackHom_apply, map_sub, picardPullbackHom_apply, picardPullbackHom_apply]
  exact sub_eq_zero.2 hn

/-- **Two invertible modules isomorphic on every adic fibre are isomorphic**, for an algebraic
space `X` proper over a Noetherian `I`-adically complete ring.  The isomorphisms on the
different fibres are not assumed compatible. -/
theorem nonempty_iso_of_forall_adicFibre_iso
    (hf : IsProper B (Spec (.of A)) hA f.hom) (L M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hL : IsInvertibleModule X L) (hM : IsInvertibleModule X M)
    (h : ∀ n, Nonempty ((modulePullback B (Spec (.of A)) hA
      (adicFibreInclusion A I B hA X f n)).obj L ≅
        (modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj M)) :
    Nonempty (L ≅ M) := by
  refine (picardClass_eq_picardClass_iff X L M hL hM).1
    (injective_picardPullback_adicFibreInclusion I X f hf (funext fun n => ?_))
  dsimp only
  rw [picardPullback_picardClass, picardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 (h n)

/-- **Grothendieck's existence theorem determines coherent modules from their adic fibres**: two
coherent modules on an algebraic space proper over a Noetherian `I`-adically complete ring
whose systems of restrictions to the adic fibres are isomorphic, compatibly with the transition
isomorphisms, are isomorphic.  This is the full faithfulness half of Stacks 08BF. -/
theorem nonempty_iso_of_adicFibreRestriction_iso (hf : IsProper B (Spec (.of A)) hA f.hom)
    (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (e : (adicFibreRestrictionOf I X f hf.2.1.1).obj M ≅
      (adicFibreRestrictionOf I X f hf.2.1.1).obj N) :
    Nonempty (M ≅ N) := by
  have := isEquivalence_adicFibreRestriction_of_isProper I X f hf
  exact ⟨(adicFibreRestrictionOf I X f hf.2.1.1).preimageIso e⟩

end Triviality

end AlgebraicGeometry.Space

end
