module

public import StacksFrontier.RingTheory.LocalCohomology.BoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutKernel
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero

/-!
# Stable images of local cohomology with specialization-closed support

Let `A` be a Noetherian ring of finite dimension, let `T ⊆ Spec(A)` be stable under
specialization and let `{M_n}` be an inverse system of `A`-modules. Suppose that for every `m`
there is `m'(m) ≥ m` such that, at every prime `𝔭 ∈ T` and for every `k ≥ m'(m)`, the transition
map vanishes on `Hⁱ⁻¹_{𝔭A_𝔭}`, the image of the transition map on `Hⁱ_{𝔭A_𝔭}` does not depend on
`k`, and that image injects into `Hⁱ_{𝔭A_𝔭}(M_{0,𝔭})`. Then the images of the transition maps of
`{Hⁱ_T(M_n)}` are eventually injective: there is `m₀` such that for `m ≥ m₀` the image of
`Hⁱ_T(M_k) → Hⁱ_T(M_m)` injects into `Hⁱ_T(M_{m₀})` for all large `k`.

## Main results

All in the namespace `Stacks.LocalCohomology`:

* `eventually_injective_image_localCohomologyWithSupportIn` — the eventual injectivity of the
  images.
* `eventually_injective_image_localCohomologyWithSupportIn_of_image_injective`: the same,
  without asking the localized transition images to be independent of `k`.
* `inverseSystem_transition_comp_apply` — transition maps of a tower of modules compose,
  evaluated at an element.

## Implementation notes

The induction is on the dimension of `T`, passing from `T` to its nonminimal primes `T'`. At
each step the four-term exact sequence of the minimal-prime filtration is used in the form of
two statements about `Hⁱ_{T'} → Hⁱ_T`: its kernel is pro-zero, because a class in it comes from
a closed support cut by a principal equation and so is killed once the transition map kills
`Hⁱ⁻¹` of that closed support; and a class of `Hⁱ_T` dying at the base level is in its image,
because it localizes to zero at each prime minimal in `T`, where local cohomology with support
in `T` is local cohomology of the local ring. Injectivity for `T'` is the inductive hypothesis,
and the whole is assembled by a diagram chase on inverse systems.

## References

* [Stacks Project, Tag 0EFA](https://stacks.math.columbia.edu/tag/0EFA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PrimeSpectrum

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Inverse systems of modules -/

/-- Transition maps of an inverse system indexed by the natural numbers compose. -/
private theorem inverseSystem_map_comp_apply
    {R : Type u} [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{max u v} R)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : F.obj (op c)) :
    (F.map (homOfLE hab).op).hom ((F.map (homOfLE hbc).op).hom x) =
      (F.map (homOfLE (hab.trans hbc)).op).hom x := by
  have h := F.map_comp (homOfLE hbc).op (homOfLE hab).op
  have hcomp : (homOfLE hbc).op ≫ (homOfLE hab).op = (homOfLE (hab.trans hbc)).op :=
    Subsingleton.elim _ _
  rw [hcomp] at h
  exact congrArg (fun g => g.hom x) h.symm

/-- Transition maps of an inverse system of modules indexed by the natural numbers compose,
evaluated at an element. -/
alias inverseSystem_transition_comp_apply := inverseSystem_map_comp_apply

/-- A morphism of inverse systems commutes with the transition maps. -/
private theorem inverseSystem_natTrans_apply
    {R : Type u} [CommRing R] {F G : ℕᵒᵖ ⥤ ModuleCat.{max u v} R}
    (η : F ⟶ G) {a b : ℕ} (hab : a ≤ b) (x : F.obj (op b)) :
    (η.app (op a)).hom ((F.map (homOfLE hab).op).hom x) =
      (G.map (homOfLE hab).op).hom ((η.app (op b)).hom x) := by
  exact congrArg (fun g => ModuleCat.Hom.hom g x) (η.naturality (homOfLE hab).op)

/-- Injectivity of the image of a transition map is invariant under an isomorphism of inverse
systems. -/
private theorem inverseSystem_iso_image_eq_zero
    {R : Type u} [CommRing R] {F G : ℕᵒᵖ ⥤ ModuleCat.{max u v} R}
    (e : F ≅ G) {r m k : ℕ} (hrm : r ≤ m) (hmk : m ≤ k)
    (hinj : ∀ y : G.obj (op k),
      (G.map (homOfLE hmk).op).hom y ∈ LinearMap.ker (G.map (homOfLE hrm).op).hom →
      (G.map (homOfLE hmk).op).hom y = 0)
    (x : F.obj (op k))
    (hx : (F.map (homOfLE hmk).op).hom x ∈ LinearMap.ker (F.map (homOfLE hrm).op).hom) :
    (F.map (homOfLE hmk).op).hom x = 0 := by
  have hy := hinj ((e.hom.app (op k)).hom x) (by
    rw [LinearMap.mem_ker, ← inverseSystem_natTrans_apply e.hom hmk,
      ← inverseSystem_natTrans_apply e.hom hrm, LinearMap.mem_ker.mp hx, map_zero])
  have hinjective : Function.Injective (e.hom.app (op m)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinjective
  rw [map_zero, inverseSystem_natTrans_apply e.hom hmk]
  exact hy

/-- **The diagram chase.** Let `G ⟶ H` be a morphism of inverse systems whose kernel at some
level `base` is killed by a transition map, whose source has eventually injective images over
`base`, and for which a class of `H` dying at `base` lifts to `G`. Then the images of the
transition maps of `H` are eventually injective. -/
private theorem eventualImageInjectivity_of_kernel
    {R : Type u} [CommRing R] (G H : ℕᵒᵖ ⥤ ModuleCat.{max u v} R)
    (inclusion : G ⟶ H) (base : ℕ)
    (hkernel : ∃ cutoff, ∃ hbase : base ≤ cutoff,
      ∀ x : G.obj (op cutoff), (inclusion.app (op cutoff)).hom x = 0 →
        (G.map (homOfLE hbase).op).hom x = 0)
    (hG : ∀ (index : ℕ) (hbase : base ≤ index), ∃ cutoff, ∃ hindex : index ≤ cutoff,
      ∀ (source : ℕ) (hcutoff : cutoff ≤ source) (x : G.obj (op source)),
        (G.map (homOfLE (hindex.trans hcutoff)).op).hom x ∈
          LinearMap.ker (G.map (homOfLE hbase).op).hom →
        (G.map (homOfLE (hindex.trans hcutoff)).op).hom x = 0)
    (hlift : ∀ (index : ℕ) (hbase : base ≤ index), ∃ cutoff, ∃ hindex : index ≤ cutoff,
      ∀ (source : ℕ) (hcutoff : cutoff ≤ source) (x : H.obj (op source)),
        (H.map (homOfLE (hbase.trans (hindex.trans hcutoff))).op).hom x = 0 →
        ∃ y : G.obj (op index), (inclusion.app (op index)).hom y =
          (H.map (homOfLE (hindex.trans hcutoff)).op).hom x) :
    ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : H.obj (op source),
          (H.map (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker (H.map (homOfLE hcutoff).op).hom →
          (H.map (homOfLE (hindex.trans hbound)).op).hom x = 0 := by
  obtain ⟨cutoff, hbaseCutoff, hkernelCutoff⟩ := hkernel
  refine ⟨cutoff, ?_⟩
  intro index hcutoff
  obtain ⟨middle, hindexMiddle, hGprop⟩ := hG index (hbaseCutoff.trans hcutoff)
  obtain ⟨sourceBound, hmiddleSource, hliftProp⟩ :=
    hlift middle (hbaseCutoff.trans (hcutoff.trans hindexMiddle))
  refine ⟨sourceBound, hindexMiddle.trans hmiddleSource, ?_⟩
  intro source hbound x hx
  have hmiddle : middle ≤ source := hmiddleSource.trans hbound
  have hcutoffSource : (H.map (homOfLE (hcutoff.trans
      (hindexMiddle.trans hmiddle))).op).hom x = 0 := by
    rw [← inverseSystem_map_comp_apply H hcutoff (hindexMiddle.trans hmiddle)]
    exact LinearMap.mem_ker.mp hx
  have hbaseSource : (H.map (homOfLE (hbaseCutoff.trans
      (hcutoff.trans (hindexMiddle.trans hmiddle)))).op).hom x = 0 := by
    rw [← inverseSystem_map_comp_apply H hbaseCutoff
      (hcutoff.trans (hindexMiddle.trans hmiddle)), hcutoffSource, map_zero]
  obtain ⟨y, hy⟩ := hliftProp source hbound x hbaseSource
  have hcutoffKernel : (inclusion.app (op cutoff)).hom
      ((G.map (homOfLE (hcutoff.trans hindexMiddle)).op).hom y) = 0 := by
    rw [inverseSystem_natTrans_apply inclusion (hcutoff.trans hindexMiddle), hy,
      inverseSystem_map_comp_apply H]
    exact hcutoffSource
  have hbaseZero := hkernelCutoff _ hcutoffKernel
  have hGkernel : (G.map (homOfLE hindexMiddle).op).hom y ∈
      LinearMap.ker (G.map (homOfLE (hbaseCutoff.trans hcutoff)).op).hom := by
    rw [LinearMap.mem_ker, inverseSystem_map_comp_apply G]
    rw [inverseSystem_map_comp_apply G] at hbaseZero
    exact hbaseZero
  have hyzero := hGprop middle le_rfl y hGkernel
  rw [← inverseSystem_map_comp_apply H hindexMiddle hmiddle,
    ← hy, ← inverseSystem_natTrans_apply inclusion hindexMiddle, hyzero, map_zero]

/-! ### The dimension bound -/

/-- Every subset of the spectrum of a Noetherian ring of finite dimension has dimension at most
the dimension of the ring. -/
private theorem nonminimalDim_le_ringKrullDim {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (S : Set (PrimeSpectrum A)) :
    nonminimalDim S ≤ ((ringKrullDim A).unbotD 0).toNat := by
  by_cases hS : S.Nonempty
  · have hDne : Order.krullDim (OrderDual (↥S)) ≠ ⊥ :=
      (Order.krullDim_ne_bot_iff).2 ⟨⟨hS.choose, hS.choose_spec⟩⟩
    have hDE : Order.krullDim (OrderDual (↥S)) ≤ ringKrullDim A := by
      calc
        Order.krullDim (OrderDual (↥S)) ≤ topologicalKrullDim (↥S) :=
          krullDim_orderDual_le_topologicalKrullDim S
        _ ≤ topologicalKrullDim (PrimeSpectrum A) := topologicalKrullDim_subspace_le _ S
        _ = ringKrullDim A := topologicalKrullDim_eq_ringKrullDim A
    refine ENat.toNat_le_toNat (WithBot.unbotD_mono (a := (0 : ℕ∞)) hDne hDE) ?_
    intro h
    exact (ne_of_lt hdim) ((WithBot.unbotD_eq_iff).mp h |>.resolve_right (by simp))
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    subst hS
    have hempty : IsEmpty (↥(∅ : Set (PrimeSpectrum A))) := by simp
    have hbot : Order.krullDim (OrderDual (↥(∅ : Set (PrimeSpectrum A)))) = ⊥ := by
      have : IsEmpty (OrderDual (↥(∅ : Set (PrimeSpectrum A)))) := hempty
      exact Order.krullDim_eq_bot
    simp [nonminimalDim, hbot]

/-! ### The kernel of the inclusion of the nonminimal primes -/

/-- The map on local cohomology of modules induced by an inclusion of supports. -/
private def supportInclusionModuleNatTrans (A : Type u) [CommRing A]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) (i : ℤ) :
    localCohomologyWithSupportInModuleFunctor.{u, v} A S i ⟶
      localCohomologyWithSupportInModuleFunctor.{u, v} A T i :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0)
    (Functor.whiskerRight (derivedSectionsWithSupportInInclusion.{u, v} A h)
      (DerivedCategory.homologyFunctor _ i))

/-- Uniform vanishing of the transition maps on `Hⁱ⁻¹` at every prime of `T` makes the
transition maps vanish on `Hⁱ⁻¹_{V(I)}` for every closed `V(I) ⊆ T` simultaneously. -/
private theorem closedSupport_previousDegree_maps_zero_uniform
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (T : Set (PrimeSpectrum A)) (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ T, ∀ (k : ℕ) (hck : c ≤ k),
      (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) ((i : ℤ) - 1)).map
          (homOfLE (hmc.trans hck)).op = 0) :
    ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k), ∀ I : Ideal A,
      zeroLocus (I : Set A) ⊆ T →
      (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
        (zeroLocus (I : Set A)) ((i : ℤ) - 1)).map (homOfLE (hmc.trans hck)).op = 0 := by
  classical
  cases i with
  | zero =>
    intro m
    refine ⟨m, le_rfl, ?_⟩
    intro k hmk I hI
    have hz := isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A
      (zeroLocus (I : Set A)) (M.obj (op m)) (((0 : ℕ) : ℤ) - 1) (by norm_num)
    exact hz.eq_of_tgt _ _
  | succ j =>
    have hdeg : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by push_cast; ring
    intro m
    let c : ℕ → ℕ := fun l => Classical.choose (hloc l)
    have hc : ∀ l, l ≤ c l := fun l => Classical.choose (Classical.choose_spec (hloc l))
    have hlocal : ∀ (l k : ℕ) (hbound : c l ≤ k), ∀ p : PrimeSpectrum A, p ∈ T →
        ((ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (j : ℤ)).map
          (M.map (homOfLE ((hc l).trans hbound)).op) = 0) := by
      intro l k hbound p hp
      have hz := Classical.choose_spec (Classical.choose_spec (hloc l)) p hp k hbound
      rw [← hdeg]
      exact hz
    refine ⟨c^[2 ^ ((ringKrullDim A).unbotD 0).toNat] m,
      Function.id_le_iterate_of_id_le hc _ m, ?_⟩
    intro k hck I hI
    rw [hdeg]
    exact localCohomologyWithSupportIn_map_eq_zero_of_local_of_dimension_le.{u, v} A hdim M j c hc
      _ (zeroLocus (I : Set A)) (isClosed_zeroLocus _).stableUnderSpecialization
      (nonminimalDim_le_ringKrullDim hdim _)
      (fun l k' hbound p hp => hlocal l k' hbound p (hI hp)) m k hck

/-- **The kernel of the inclusion of the nonminimal primes is pro-zero.** A class in
`Hⁱ_{T'}(M_c)` dying in `Hⁱ_T(M_c)` has zero image in `Hⁱ_{T'}(M_m)`, once the transition from
`c` to `m` kills `Hⁱ⁻¹` of every closed subset of `T`. -/
private theorem supportInclusion_kernel_eventually_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℤ)
    (hprevious : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k), ∀ I : Ideal A,
      zeroLocus (I : Set A) ⊆ T →
      (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
        (zeroLocus (I : Set A)) (i - 1)).map (homOfLE (hmc.trans hck)).op = 0)
    (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c,
      ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
          (nonminimalPrimes T) i).obj (op c),
        ((supportInclusionModuleNatTrans.{u, v} A (nonminimalPrimes_subset T) i).app
          (M.obj (op c))).hom x = 0 →
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
          (nonminimalPrimes T) i).map (homOfLE hmc).op).hom x = 0 := by
  obtain ⟨c, hmc, hzero⟩ := hprevious m
  refine ⟨c, hmc, ?_⟩
  intro x hx
  obtain ⟨I, f, hIT, hadm, y, hyx, hy0⟩ :=
    (kernel_changeOfSupport_eq_closedSupportImages.{u, v} A T hT
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (M.obj (op c))) i x).mp hx
  have hprev : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (i - 1)).map
      ((derivedSectionsWithSupportIn.{u, v} A (zeroLocus (I : Set A))).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map
          (M.map (homOfLE hmc).op))) = 0 := hzero c le_rfl I hIT
  have hytrans := principalCut_map_eq_zero_of_previousDegree_of_support_eq.{u, v} A I f
    (zeroLocus (I : Set A) ∩ zeroLocus ({f} : Set A)) rfl Set.inter_subset_left
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map (M.map (homOfLE hmc).op))
    i hprev y hy0
  have hytrans' : ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
      (zeroLocus (I : Set A) ∩ zeroLocus ({f} : Set A)) i).map (homOfLE hmc).op).hom y = 0 :=
    hytrans
  have hnat := inverseSystem_natTrans_apply
    (Functor.whiskerLeft M (supportInclusionModuleNatTrans.{u, v} A hadm i)) hmc y
  rw [← hyx]
  refine hnat.symm.trans ?_
  rw [hytrans', map_zero]

/-! ### Localizing at a prime minimal in the support -/

/-- A class of `Hⁱ_T(M_k)` whose image in `Hⁱ_T(M_m)` dies in `Hⁱ_T(M_r)` localizes to zero at
every prime minimal in `T`, provided the images of the transition maps of local cohomology at
that prime inject into level `r`. -/
private theorem minimalPrime_localization_image_eq_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℤ)
    (p : PrimeSpectrum A) (hp : p ∈ T \ nonminimalPrimes T)
    (r m k : ℕ) (hrm : r ≤ m) (hmk : m ≤ k)
    (hinj : ∀ y : (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).obj (op k),
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).map
          (homOfLE hmk).op).hom y ∈
        LinearMap.ker ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).map
            (homOfLE hrm).op).hom →
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).map
          (homOfLE hmk).op).hom y = 0)
    (x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op k))
    (hx : (ModuleCat.localizedModuleMkLinearMap
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op r))
        p.asIdeal.primeCompl)
      (((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        (homOfLE (hrm.trans hmk)).op).hom x) = 0) :
    (ModuleCat.localizedModuleMkLinearMap
      ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op m))
      p.asIdeal.primeCompl)
      (((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        (homOfLE hmk).op).hom x) = 0 := by
  classical
  -- The kernel condition transported to the restriction of scalars, which changes nothing.
  have hinj' : ∀ y : (M ⋙ (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) ⋙
          restrictScalarsAtPrime.{u, v} A p).obj (op k),
      ((M ⋙ (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) ⋙
          restrictScalarsAtPrime.{u, v} A p).map (homOfLE hmk).op).hom y ∈
        LinearMap.ker ((M ⋙ (ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) i) ⋙
              restrictScalarsAtPrime.{u, v} A p).map (homOfLE hrm).op).hom →
      ((M ⋙ (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) ⋙
          restrictScalarsAtPrime.{u, v} A p).map (homOfLE hmk).op).hom y = 0 := hinj
  have hiso : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i ⋙
        CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max u v}
          p.asIdeal.primeCompl) ≅
      M ⋙ (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) ⋙
          restrictScalarsAtPrime.{u, v} A p :=
    Functor.isoWhiskerLeft M (minimalPrimeLocalCohomologyIso.{u, v} A hdim T hT p hp i)
  -- The transition maps of the localized system are the localizations of the transition maps.
  have hmapsys : ∀ {a b : ℕ} (hab : a ≤ b)
      (z : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj (op b)),
      ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i ⋙
          CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max u v}
            p.asIdeal.primeCompl).map (homOfLE hab).op).hom
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _ z) =
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl _
        (((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
          (homOfLE hab).op).hom z) := by
    intro a b hab z
    exact IsLocalizedModule.map_apply p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)
      ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map (homOfLE hab).op).hom z
  -- The canonical map to the localized module factors through the literal localized module.
  have hmkeq : ∀ (N : ModuleCat.{max u v} A) (z : N),
      (ModuleCat.localizedModuleMkLinearMap N p.asIdeal.primeCompl) z = 0 ↔
        LocalizedModule.mkLinearMap p.asIdeal.primeCompl N z = 0 := by
    intro N z
    rw [show (ModuleCat.localizedModuleMkLinearMap N p.asIdeal.primeCompl) z =
        (Shrink.linearEquiv A (LocalizedModule p.asIdeal.primeCompl N)).symm
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N z) from rfl]
    exact map_eq_zero_iff _ (Shrink.linearEquiv A
      (LocalizedModule p.asIdeal.primeCompl N)).symm.injective
  have hx' := (hmkeq _ _).mp hx
  refine (hmkeq _ _).mpr ?_
  rw [← hmapsys hmk x]
  refine inverseSystem_iso_image_eq_zero hiso hrm hmk hinj' _ ?_
  rw [LinearMap.mem_ker]
  exact (inverseSystem_map_comp_apply
    (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i ⋙
      CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max u v} p.asIdeal.primeCompl)
    hrm hmk _).trans ((hmapsys (hrm.trans hmk) x).trans hx')

/-! ### The inductive step and the theorem -/

/-- Local cohomology with empty support vanishes, so the images of its transition maps are
trivially injective. -/
private theorem eventualImageInjectivity_empty
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℤ) :
    ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (∅ : Set (PrimeSpectrum A)) i).obj (op source),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (∅ : Set (PrimeSpectrum A)) i).map (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (∅ : Set (PrimeSpectrum A)) i).map (homOfLE hcutoff).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (∅ : Set (PrimeSpectrum A)) i).map (homOfLE (hindex.trans hbound)).op).hom x = 0 := by
  refine ⟨0, fun index hcutoff => ⟨index, le_rfl, fun source hbound x _ => ?_⟩⟩
  have hz := isZero_localCohomologyWithSupportIn_empty.{u, v} A
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (M.obj (op index))) i
  have : Subsingleton ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
      (∅ : Set (PrimeSpectrum A)) i).obj (op index)) :=
    ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

/-- **The inductive step.** If the images of the transition maps of local cohomology with
support in the nonminimal primes of `S` are eventually injective, then so are those of local
cohomology with support in `S`. -/
private theorem inductiveStep_of_image_injective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (S : Set (PrimeSpectrum A)) (hS : StableUnderSpecialization S)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ S, ∀ (k : ℕ) (hck : c ≤ k),
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl)
          ((i : ℤ) - 1)).map (homOfLE (hmc.trans hck)).op = 0) ∧
      (∀ x : (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0))
    (hG : ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (nonminimalPrimes S) (i : ℤ)).obj (op source),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (nonminimalPrimes S) (i : ℤ)).map (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (nonminimalPrimes S) (i : ℤ)).map (homOfLE hcutoff).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (nonminimalPrimes S) (i : ℤ)).map (homOfLE (hindex.trans hbound)).op).hom x = 0) :
    ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).obj (op source),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S
              (i : ℤ)).map (homOfLE hcutoff).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hindex.trans hbound)).op).hom x = 0 := by
  classical
  obtain ⟨base, hGprop⟩ := hG
  refine eventualImageInjectivity_of_kernel
    (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A (nonminimalPrimes S) (i : ℤ))
    (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ))
    (Functor.whiskerLeft M (supportInclusionModuleNatTrans.{u, v} A
      (nonminimalPrimes_subset S) (i : ℤ))) base ?_ hGprop ?_
  · refine supportInclusion_kernel_eventually_zero.{u, v} A S hS M (i : ℤ) ?_ base
    refine closedSupport_previousDegree_maps_zero_uniform.{u, v} A hdim S M i (fun m => ?_)
    obtain ⟨c, hmc, hprop⟩ := hloc m
    exact ⟨c, hmc, fun p hp k hck => (hprop p hp k hck).1⟩
  · intro index hbase
    obtain ⟨c, hmc, hprop⟩ := hloc index
    refine ⟨c, hmc, ?_⟩
    intro source hcutoff x hzeroAtBase
    refine (range_changeOfSupport_eq_localizationKernel.{u, v} A S hS
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (M.obj (op index)))
      (i : ℤ) _).mpr ?_
    intro p hp
    refine minimalPrime_localization_image_eq_zero.{u, v} A hdim S hS M (i : ℤ) p hp
      base index source hbase (hmc.trans hcutoff) (fun y hy => ?_) x ?_
    · refine (hprop p hp.1 source hcutoff).2 y ?_
      rw [LinearMap.mem_ker,
        ← inverseSystem_map_comp_apply _ (Nat.zero_le base) hbase,
        LinearMap.mem_ker.mp hy, map_zero]
    · rw [hzeroAtBase, map_zero]

/-- **The inductive step**, with the stability of the localized transition images among the
per-prime hypotheses, as in the source; that stability is not used, see
`inductiveStep_of_image_injective`. -/
private theorem inductiveStep
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (S : Set (PrimeSpectrum A)) (hS : StableUnderSpecialization S)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ S, ∀ (k : ℕ) (hck : c ≤ k),
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl)
          ((i : ℤ) - 1)).map (homOfLE (hmc.trans hck)).op = 0) ∧
      (LinearMap.range ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE (hmc.trans hck)).op).hom =
        LinearMap.range ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE hmc).op).hom) ∧
      (∀ x : (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0))
    (hG : ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (nonminimalPrimes S) (i : ℤ)).obj (op source),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (nonminimalPrimes S) (i : ℤ)).map (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
              (nonminimalPrimes S) (i : ℤ)).map (homOfLE hcutoff).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A
            (nonminimalPrimes S) (i : ℤ)).map (homOfLE (hindex.trans hbound)).op).hom x = 0) :
    ∃ cutoff, ∀ (index : ℕ) (hcutoff : cutoff ≤ index), ∃ sourceBound,
      ∃ hindex : index ≤ sourceBound, ∀ (source : ℕ) (hbound : sourceBound ≤ source),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).obj (op source),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hindex.trans hbound)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S
              (i : ℤ)).map (homOfLE hcutoff).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hindex.trans hbound)).op).hom x = 0 :=
  inductiveStep_of_image_injective.{u, v} A hdim S hS M i
    (fun m => by
      obtain ⟨c, hmc, h⟩ := hloc m
      exact ⟨c, hmc, fun p hp k hck => ⟨(h p hp k hck).1, (h p hp k hck).2.2⟩⟩) hG

/-- **Stacks 0EFA, without the stable-image hypothesis.** Let `A` be a Noetherian ring of finite
dimension, let `T ⊆ Spec(A)` be stable under specialization and let `{M_n}` be an inverse system
of `A`-modules. If for every `m` there is `c ≥ m` such that at every prime `𝔭 ∈ T` and for every
`k ≥ c` the transition map vanishes on `Hⁱ⁻¹_{𝔭A_𝔭}` and its image on `Hⁱ_{𝔭A_𝔭}` injects into
`Hⁱ_{𝔭A_𝔭}(M_{0,𝔭})`, then there is `m₀` such that for every `m ≥ m₀` the image of
`Hⁱ_T(M_k) → Hⁱ_T(M_m)` injects into `Hⁱ_T(M_{m₀})` for all large `k`. The source also asks
that the image on `Hⁱ_{𝔭A_𝔭}` be independent of `k`; the argument does not use it. -/
theorem eventually_injective_image_localCohomologyWithSupportIn_of_image_injective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ T, ∀ (k : ℕ) (hck : c ≤ k),
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl)
          ((i : ℤ) - 1)).map (homOfLE (hmc.trans hck)).op = 0) ∧
      (∀ x : (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0)) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).obj (op k),
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T
            (i : ℤ)).map (homOfLE hm₀m).op).hom →
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (homOfLE (hmc.trans hck)).op).hom x = 0 := by
  classical
  suffices h : ∀ (n : ℕ) (S : Set (PrimeSpectrum A)), StableUnderSpecialization S → S ⊆ T →
      nonminimalDim S ≤ n →
      ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
        ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).obj (op k),
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
            LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S
              (i : ℤ)).map (homOfLE hm₀m).op).hom →
          ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A S (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 by
    exact h (nonminimalDim T) T hT Set.Subset.rfl le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hST hSdim
    refine inductiveStep_of_image_injective.{u, v} A hdim S hS M i (fun l => ?_) ?_
    · obtain ⟨c, hmc, hprop⟩ := hloc l
      exact ⟨c, hmc, fun p hp k hck => hprop p (hST hp) k hck⟩
    by_cases hne : (nonminimalPrimes S).Nonempty
    · have hlt := nonminimalDim_nonminimalPrimes_lt S (hne.mono (nonminimalPrimes_subset S)) hne
        hdim
      exact ih _ (by omega) (nonminimalPrimes S) (stableUnderSpecialization_nonminimalPrimes hS)
        ((nonminimalPrimes_subset S).trans hST) le_rfl
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact eventualImageInjectivity_empty.{u, v} A M (i : ℤ)

/-- **Stacks 0EFA.** Let `A` be a Noetherian ring of finite dimension, let `T ⊆ Spec(A)` be
stable under specialization and let `{M_n}` be an inverse system of `A`-modules. If for every `m`
there is `c ≥ m` such that at every prime `𝔭 ∈ T` and for every `k ≥ c` the transition map
vanishes on `Hⁱ⁻¹_{𝔭A_𝔭}`, its image on `Hⁱ_{𝔭A_𝔭}` is independent of `k` and that image injects
into `Hⁱ_{𝔭A_𝔭}(M_{0,𝔭})`, then there is `m₀` such that for every `m ≥ m₀` the image of
`Hⁱ_T(M_k) → Hⁱ_T(M_m)` injects into `Hⁱ_T(M_{m₀})` for all large `k`.

The independence of the image from `k` is not needed for the conclusion; see
`eventually_injective_image_localCohomologyWithSupportIn_of_image_injective`. -/
@[stacks 0EFA]
theorem eventually_injective_image_localCohomologyWithSupportIn
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A < ⊤)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (hloc : ∀ m : ℕ, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ p ∈ T, ∀ (k : ℕ) (hck : c ≤ k),
      ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl)
          ((i : ℤ) - 1)).map (homOfLE (hmc.trans hck)).op = 0) ∧
      (LinearMap.range ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE (hmc.trans hck)).op).hom =
        LinearMap.range ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
          p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
            (Localization p.asIdeal.primeCompl) (i : ℤ)).map (homOfLE hmc).op).hom) ∧
      (∀ x : (M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).obj (op k),
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v}
            p.asIdeal.primeCompl ⋙ localCohomologyModuleFunctor
              (Localization p.asIdeal.primeCompl) (i : ℤ)).map
                (homOfLE (Nat.zero_le m)).op).hom →
        ((M ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0)) :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).obj (op k),
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T
            (i : ℤ)).map (homOfLE hm₀m).op).hom →
        ((M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (homOfLE (hmc.trans hck)).op).hom x = 0 :=
  eventually_injective_image_localCohomologyWithSupportIn_of_image_injective.{u, v} A hdim T hT M i
    (fun m => by
      obtain ⟨c, hmc, h⟩ := hloc m
      exact ⟨c, hmc, fun p hp k hck => ⟨(h p hp k hck).1, (h p hp k hck).2.2⟩⟩)

end Stacks.LocalCohomology

end
