module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.ChartModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.Reduction
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FiberwiseFreeReducedBase

/-!
# Charts of the descent locus

For a flat proper morphism `f : X ⟶ S` locally of finite presentation with `𝒪_T ≅ p_*𝒪_{X_T}`
after every base change, a finite locally free `E` on `X`, a Noetherian stage of the problem over
an affine open `V` of `S` and a prime `p` of the stage, this file produces a chart at `p` in the
sense of `AlgebraicGeometry.DescentLocus.HasChart`: it is the chart of a kernel model of the stage
at `p` (`AlgebraicGeometry.DescentLocus.KernelModelData.chart`). This is the local step of the proof
of [Stacks, Tag 0BDP].

## Main results

* `AlgebraicGeometry.DescentLocus.hasChart`: every prime of every stage has a chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentLocus

/-- A ring map whose spectrum lands in `D(g)` inverts `g`. -/
theorem isUnit_of_range_specMap_subset {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (g : A) (h : Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))) : IsUnit (φ g) := by
  by_contra hu
  obtain ⟨Q, hQ, hgQ⟩ := exists_max_ideal_of_mem_nonunits hu
  have := h ⟨⟨Q, hQ.isPrime⟩, rfl⟩
  exact this hgQ

/-- The image of the closed point of `Spec K` under `Spec φ` is the kernel of `φ`. -/
theorem specMap_closedPoint_asIdeal {A K : Type u} [CommRing A] [Field K] (φ : A →+* K) :
    (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker φ := by
  change (PrimeSpectrum.comap φ (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker φ
  ext a
  simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]

/-- A morphism into `Spec A` from the spectrum of a ring is the spectrum of a ring map. -/
theorem exists_specMap_eq {A B : Type u} [CommRing A] [CommRing B]
    (t : Spec (.of B) ⟶ Spec (.of A)) : ∃ φ : A →+* B, Spec.map (CommRingCat.ofHom φ) = t := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  exact ⟨φ.hom, by simp⟩

section Chart

open RingedSpaceModuleAdjunction

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
  (E : X.Modules) {V : S.Opens} (hV : IsAffineOpen V) (St : NoetherianStage f E hV)

include hO in
/-- `𝒪 ≅ p_*𝒪` holds for every base change of `f`, not only the chosen ones. -/
theorem isIso_c_of_isPullback' {X' T : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ T} {c : T ⟶ S}
    (sq : IsPullback a b f c) : IsIso b.toLRSHom.toHom.c :=
  Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_of_isPullback sq
    (isIso_c_of_isIso_structureSheafHom _ (hO c))

/-- The dimension of the sections of `E` over the base change of `f` to a field point is the
dimension of the kernel of the model matrix there. -/
theorem finrank_sections_fieldPoint (M : KernelModelData St.f₀ St.E₀) {K : Type u} [Field K]
    (k : Spec (.of K) ⟶ Spec Γ(S, V)) (ψ : St.A₀ →+* K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) = k ≫ Spec.map (CommRingCat.ofHom St.φ))
    (hg : IsUnit (ψ M.g)) :
    @Module.finrank K Γ((Scheme.Modules.pullback (pullback.fst f (k ≫ hV.fromSpec))).obj E, ⊤) _ _
        (Stacks.Cech.sectionsModule (pullback.snd f (k ≫ hV.fromSpec))
          ((Scheme.Modules.pullback (pullback.fst f (k ≫ hV.fromSpec))).obj E) ⊤) =
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin (M.D.map ψ))) := by
  have sq := St.isPullback_stageMap k
  rw [← hψ] at sq
  let := Stacks.Cech.sectionsModule (pullback.snd f (k ≫ hV.fromSpec))
    ((Scheme.Modules.pullback (pullback.fst f (k ≫ hV.fromSpec))).obj E) ⊤
  let := Stacks.Cech.sectionsModule (pullback.snd f (k ≫ hV.fromSpec))
    ((Scheme.Modules.pullback (St.stageMap k)).obj St.E₀) ⊤
  exact (baseSectionsEquivOfIso (pullback.snd f (k ≫ hV.fromSpec)) (St.stageIso k)).finrank_eq.trans
    (M.finrank_sections_eq ψ hg sq)

/-- A residue field point of `S` inside `V`, as a point of `Spec Γ(S, V)`. -/
theorem exists_residueFieldPoint (x : Spec Γ(S, V)) :
    ∃ k : Spec (.of (S.residueField (hV.fromSpec x))) ⟶ Spec Γ(S, V),
      k ≫ hV.fromSpec = S.fromSpecResidueField (hV.fromSpec x) ∧
        k (IsLocalRing.closedPoint _) = x := by
  have hr : Set.range (S.fromSpecResidueField (hV.fromSpec x)) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x, by rw [Scheme.fromSpecResidueField_apply]⟩
  refine ⟨IsOpenImmersion.lift hV.fromSpec _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  apply hV.fromSpec.isOpenEmbedding.injective
  change (IsOpenImmersion.lift hV.fromSpec _ hr ≫ hV.fromSpec) (IsLocalRing.closedPoint _) = _
  rw [IsOpenImmersion.lift_fac]
  exact Scheme.fromSpecResidueField_apply _ _


/-- The dimension of the sections of `E` over the base change of `f` along a field point. -/
def finrankSections {K : Type u} [Field K] (g : Spec (.of K) ⟶ S) : ℕ :=
  @Module.finrank K Γ((Scheme.Modules.pullback (pullback.fst f g)).obj E, ⊤) _ _
    (Stacks.Cech.sectionsModule (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E) ⊤)


/-- The base change of `f` along a map from an affine scheme has the ring of global sections of
the base. -/
private theorem bijective_globalRingHom_snd
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    {B : Type u} [CommRing B] (g : Spec (.of B) ⟶ S) :
    Function.Bijective (Stacks.Cech.globalRingHom (pullback.snd f g)).hom :=
  bijective_globalRingHom_of_isIso (pullback.snd f g)
    (isIso_c_of_isPullback' f hO (IsPullback.of_hasPullback f g))

include hO in
/-- **A base along which `E` descends, mapping into `D(g)` and the rank `r` locus, factors
through the chart** (the case of the spectrum of a ring with `E` free on the base change). -/
theorem exists_lift_chart_of_iso_free [Flat f] [IsProper f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [St.E₀.IsFiniteType]
    (M : KernelModelData St.f₀ St.E₀) {B : Type u} [CommRing B] (h : Spec (.of B) ⟶ Spec Γ(S, V))
    (hD : Set.range (h ≫ Spec.map (CommRingCat.ofHom St.φ)) ⊆
      (PrimeSpectrum.basicOpen M.g : Set (PrimeSpectrum St.A₀)))
    (hR : Set.range (h ≫ hV.fromSpec) ⊆ (Scheme.Modules.rankBaseOpen f E M.r : Set S)) {m : ℕ}
    (e : (Scheme.Modules.pullback (pullback.fst f (h ≫ hV.fromSpec))).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin m))) :
    ∃ l : Spec (.of B) ⟶ M.chart.left, l ≫ M.chart.hom = h ≫ Spec.map (CommRingCat.ofHom St.φ) := by
  obtain ⟨ψ, hψ⟩ := exists_specMap_eq (h ≫ Spec.map (CommRingCat.ofHom St.φ))
  by_cases hne : IsEmpty (Spec (.of B))
  · exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _⟩
  rw [not_isEmpty_iff] at hne
  obtain ⟨t⟩ := hne
  have hsurj : Surjective f := surjective_of_isIso_structureSheafHom f (hO (𝟙 S))
  obtain ⟨x₀, hx₀⟩ := hsurj.surj ((h ≫ hV.fromSpec) t)
  obtain ⟨x, hx, -⟩ := Scheme.Pullback.exists_preimage_pullback x₀ t hx₀
  have hm : m = M.r := by
    have h1 := Scheme.Modules.mem_rankStratum_of_pullback_iso_free E _ e x
    have h2 := Scheme.Modules.range_fst_subset_rankStratum f E _ hR ⟨x, rfl⟩
    have h2' : (pullback.fst f (h ≫ hV.fromSpec)) x ∈ Scheme.Modules.rankStratum E M.r := h2
    rw [Scheme.Modules.mem_rankStratum] at h1 h2'
    exact h1.symm.trans h2'
  subst hm
  have sq := St.isPullback_stageMap h
  rw [← hψ] at sq
  have hg : IsUnit (ψ M.g) := isUnit_of_range_specMap_subset ψ M.g (by rw [hψ]; exact hD)
  have hp : ∀ {B' : Type u} [CommRing B'] (ψ' : B →+* B'),
      Function.Bijective (Stacks.Cech.globalRingHom (pullback.snd (pullback.snd f (h ≫ hV.fromSpec))
        (Spec.map (CommRingCat.ofHom ψ')))).hom := fun ψ' ↦
    bijective_globalRingHom_of_isIso _ (isIso_c_of_isPullback' f hO
      ((IsPullback.of_hasPullback (pullback.snd f (h ≫ hV.fromSpec))
        (Spec.map (CommRingCat.ofHom ψ'))).paste_horiz
          (IsPullback.of_hasPullback f (h ≫ hV.fromSpec))))
  obtain ⟨l, hl⟩ := M.exists_lift_of_iso_free ψ hg sq (bijective_globalRingHom_snd f hO _) hp
    ((St.stageIso h).symm ≪≫ e)
  exact ⟨l, hl.trans hψ⟩

/-- **A base factoring through the chart, inside the rank `r` locus, satisfies the descent
condition.** -/
theorem descendsFromBase_of_exists_lift_chart
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [UniversallyClosed f]
    [St.E₀.IsFiniteType] (M : KernelModelData St.f₀ St.E₀) {T : Scheme.{u}}
    (h : T ⟶ Spec Γ(S, V))
    (hR : Set.range (h ≫ hV.fromSpec) ⊆ (Scheme.Modules.rankBaseOpen f E M.r : Set S))
    (hl : ∃ l : T ⟶ M.chart.left, l ≫ M.chart.hom = h ≫ Spec.map (CommRingCat.ofHom St.φ)) :
    DescendsFromBase f E (h ≫ hV.fromSpec) := by
  have sq := St.isPullback_stageMap h
  have hr := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (St.stageIso h)
    (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_fst f E (h ≫ hV.fromSpec) hR)
  obtain ⟨e⟩ := M.nonempty_iso_free_of_exists_lift sq hr hl
  exact AlgebraicGeometry.descendsFromBase_of_nonempty_iso_free f E (h ≫ hV.fromSpec) M.r
    ⟨St.stageIso h ≪≫ e⟩

include hO in
/-- **Every prime of every Noetherian stage has a chart.** -/
theorem hasChart [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (p : PrimeSpectrum St.A₀) : HasChart f E St p := by
  have : St.E₀.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent St.E₀).2
  obtain ⟨M, hgp, hDp⟩ := exists_kernelModelData St.f₀ St.E₀ St.isFlatOver p.asIdeal
  -- field points over `D(g)`
  have hfield : ∀ (K : Type u) [Field K] (k : Spec (.of K) ⟶ Spec Γ(S, V)) (y : Spec Γ(S, V)),
      k (IsLocalRing.closedPoint K) = y →
      Spec.map (CommRingCat.ofHom St.φ) y ∈ PrimeSpectrum.basicOpen M.g →
      finrankSections f E (k ≫ hV.fromSpec) ≤ M.r ∧
      (Spec.map (CommRingCat.ofHom St.φ) y = p →
        finrankSections f E (k ≫ hV.fromSpec) = M.r) := by
    intro K _ k y hy hk
    obtain ⟨ψ, hψ⟩ := exists_specMap_eq (k ≫ Spec.map (CommRingCat.ofHom St.φ))
    have hψpt : Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K) =
        Spec.map (CommRingCat.ofHom St.φ) y := by
      rw [hψ, ← hy]; rfl
    have hg : IsUnit (ψ M.g) := by
      refine isUnit_of_range_specMap_subset ψ M.g ?_
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rw [hz, hψpt]
      exact hk
    unfold finrankSections
    rw [finrank_sections_fieldPoint f E hV St M k ψ hψ hg]
    refine ⟨(Submodule.finrank_le _).trans (by simp), fun hp ↦ ?_⟩
    have hker : ∀ i j, ψ (M.D i j) = 0 := by
      intro i j
      have h1 : (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K)).asIdeal =
          p.asIdeal := by rw [hψpt, hp]
      rw [specMap_closedPoint_asIdeal] at h1
      rw [← RingHom.mem_ker, h1]
      exact hDp i j
    have : LinearMap.ker (Matrix.mulVecLin (M.D.map ψ)) = ⊤ :=
      eq_top_iff.2 fun v _ ↦ M.mem_ker_of_map_eq_zero ψ hker v
    rw [this, finrank_top]
    simp
  -- residue field points over `D(g)`
  have hres : ∀ x : Spec Γ(S, V),
      Spec.map (CommRingCat.ofHom St.φ) x ∈ PrimeSpectrum.basicOpen M.g →
      fibreH0 f E (hV.fromSpec x) ≤ M.r ∧
        (Spec.map (CommRingCat.ofHom St.φ) x = p → fibreH0 f E (hV.fromSpec x) = M.r) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := exists_residueFieldPoint hV x
    have e1 : fibreH0 f E (hV.fromSpec x) =
      finrankSections f E (S.fromSpecResidueField (hV.fromSpec x)) := rfl
    rw [e1, ← hk]
    exact hfield _ k x hkx hx
  refine ⟨M.g, hgp, M.r, M.chart, inferInstance, M.finitePresentation_chart, ?_, ?_, ?_, ?_⟩
  · -- clause (b)
    exact fun x hx ↦ (hres x hx).1
  · -- clause (c)
    exact fun x hx ↦ (hres x (by rw [hx]; exact hgp)).2 hx
  · -- clause (d)
    intro K _ k m hk ⟨e⟩
    have h := (hfield K k _ rfl (by
      change (k ≫ Spec.map (CommRingCat.ofHom St.φ)) (IsLocalRing.closedPoint K) ∈ _
      rw [hk]; exact hgp)).2 hk
    unfold finrankSections at h
    rw [finrank_sections_of_iso_free _ (bijective_globalRingHom_snd f hO _) e] at h
    exact h
  · -- the universal property
    intro T h hD hR
    refine ⟨descendsFromBase_of_exists_lift_chart f E hV St M h hR, fun hdesc ↦ ?_⟩
    obtain ⟨κ, W, hW, hWaff⟩ := hdesc.exists_affine_cover_iso_free
    refine exists_lift_of_iSup_eq_top M.chart.hom _ W hW fun k ↦ ?_
    obtain ⟨haff, m, ⟨e⟩⟩ := hWaff k
    have : IsAffine (W k) := haff
    let i := (W k : Scheme.{u}).isoSpec
    let h' : Spec (.of Γ(W k, ⊤)) ⟶ Spec Γ(S, V) := i.inv ≫ (W k).ι ≫ h
    obtain ⟨e'⟩ := nonempty_pullback_fst_iso_free_of_comp f E i.inv
      (g₂ := h' ≫ hV.fromSpec) (by simp [h']) e
    have hD' : Set.range (h' ≫ Spec.map (CommRingCat.ofHom St.φ)) ⊆
        (PrimeSpectrum.basicOpen M.g : Set (PrimeSpectrum St.A₀)) := by
      rintro _ ⟨y, rfl⟩
      exact hD ⟨_, rfl⟩
    have hR' : Set.range (h' ≫ hV.fromSpec) ⊆ (Scheme.Modules.rankBaseOpen f E M.r : Set S) := by
      rintro _ ⟨y, rfl⟩
      exact hR ⟨_, rfl⟩
    obtain ⟨l', hl'⟩ := exists_lift_chart_of_iso_free f hO E hV St M h' hD' hR' e'
    refine ⟨i.hom ≫ l', ?_⟩
    rw [Category.assoc, hl']
    simp [h']

end Chart

end AlgebraicGeometry.DescentLocus
