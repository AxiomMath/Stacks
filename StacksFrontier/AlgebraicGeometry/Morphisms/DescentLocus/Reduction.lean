module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.ChartDefs
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus0BDP
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionGlue
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSectionsBaseChange

/-!
# The descent locus from local charts

Let `f : X ⟶ S` be flat, proper and locally of finite presentation with `𝒪_T = p_* 𝒪` for every
base change `p : X ×_S T ⟶ T`, and let `E` be finite locally free on `X`.
[Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) asserts that the descent condition
`AlgebraicGeometry.DescendsFromBase f E` is represented by an immersion of finite presentation
`Z ⟶ S`. This file reduces that statement to the existence of local charts
(`AlgebraicGeometry.DescentLocus.HasChart`) at the primes of Noetherian stages over the affine
opens of `S`.

## Main results

* `AlgebraicGeometry.DescentLocus.exists_rank_of_descendsFromBase`: a point over which `E`
  descends lies in the base open of some rank `m`, and `m` is the dimension of the sections of
  `E` on the fibre over it.
* `AlgebraicGeometry.DescentLocus.exists_glueChart`: on each glue open the descent condition is
  represented by an immersion of finite presentation.
* `AlgebraicGeometry.DescentLocus.hasDescentLocus_of_hasChart`: the descent condition is
  representable once every prime of every Noetherian stage has a local chart.

## Implementation notes

The charts are glued with `AlgebraicGeometry.exists_isImmersion_represents_of_local_of_le` over
the open `G` covered by the glue opens `glueOpen`: the image in an affine open `V` of a basic
open `D(g)` of a stage, intersected with the base open of a rank `ρ` at least the chart rank `r`.
For `ρ = r` the chart is the base change of the given immersion; for `ρ > r` it is empty, since a
point over which `E` descends has fibre dimension equal to its rank, while over `D(g)` the fibre
dimension is at most `r`. Every point over which `E` descends lies in `G`, by the same equality
of rank and fibre dimension. `G ⟶ S` is quasi-compact because, over an affine open `W`, `G ∩ W`
is the finite union, over the ranks `ρ` of `E` above `W`, of the image of a quasi-compact open of
the Noetherian stage intersected with the closed set `rankBaseOpen f E ρ`; this set is closed
because `f` is open (Tag 01UA).

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.DescentLocus

section Basic

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism whose base change along the identity has `𝒪 = p_* 𝒪` and is universally closed is
surjective. -/
theorem surjective_of_isIso_structureSheafHom [UniversallyClosed f]
    (hO : IsIso (structureSheafHom (pullback.snd f (𝟙 S)).toLRSHom.toShHom)) : Surjective f := by
  have := VectorBundleCodimensionOne.surjective_of_isIso_cMap (pullback.snd f (𝟙 S))
    (isIso_c_of_isIso_structureSheafHom _ hO)
  refine ⟨fun s ↦ ?_⟩
  obtain ⟨z, hz⟩ := (pullback.snd f (𝟙 S)).surjective s
  refine ⟨pullback.fst f (𝟙 S) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Category.comp_id, hz]

variable (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- For a universally closed and universally open morphism, the base open of rank `ρ` is
closed. -/
theorem isClosed_rankBaseOpen [UniversallyClosed f] [UniversallyOpen f] (ρ : ℕ) :
    IsClosed (Scheme.Modules.rankBaseOpen f E ρ : Set S) := by
  rw [← isOpen_compl_iff]
  change IsOpen (f '' (Scheme.Modules.rankStratum E ρ : Set X)ᶜ)ᶜᶜ
  rw [compl_compl]
  exact f.isOpenMap _ (Scheme.Modules.isClopen_rankStratum E ρ).isClosed.isOpen_compl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
/-- If the pullback of `E` along the first projection of `X ×_S Y₁` is free and `Y₂ ⟶ S`
factors through `Y₁ ⟶ S`, the pullback of `E` to `X ×_S Y₂` is free of the same rank. -/
theorem nonempty_pullback_fst_iso_free_of_comp {Y₁ Y₂ : Scheme.{u}} {g₁ : Y₁ ⟶ S} {g₂ : Y₂ ⟶ S}
    (a : Y₂ ⟶ Y₁) (ha : a ≫ g₁ = g₂) {I : Type u}
    (e : (Scheme.Modules.pullback (pullback.fst f g₁)).obj E ≅ SheafOfModules.free I) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst f g₂)).obj E ≅ SheafOfModules.free I) := by
  let φ : pullback f g₂ ⟶ pullback f g₁ :=
    pullback.lift (pullback.fst f g₂) (pullback.snd f g₂ ≫ a)
      (by rw [Category.assoc, ha, pullback.condition])
  exact ⟨(Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _ : φ ≫ _ = _).symm).app E ≪≫
    ((Scheme.Modules.pullbackComp φ (pullback.fst f g₁)).app E).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso e ≪≫ schemeModulesPullbackObjFreeIso φ I⟩

end Basic

/-- A morphism whose range lies in the range of an open immersion factors through it. -/
private theorem exists_comp_eq_of_range_subset {Y Z T : Scheme.{u}} (i : Y ⟶ Z)
    [IsOpenImmersion i] (a : T ⟶ Z) (h : Set.range a ⊆ Set.range i) :
    ∃ l : T ⟶ Y, l ≫ i = a :=
  ⟨IsOpenImmersion.lift i a h, IsOpenImmersion.lift_fac _ _ _⟩

/-- Every point of `S` is the image of a point of `Spec Γ(S, V)` for some affine open `V`. -/
private theorem exists_isAffineOpen_fromSpec_eq {S : Scheme.{u}} (s : S) :
    ∃ (V : S.Opens) (hV : IsAffineOpen V) (x : Spec Γ(S, V)), hV.fromSpec x = s := by
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  exact ⟨V, hV, by rwa [← Set.mem_range, hV.range_fromSpec]⟩

section PPoints

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [UniversallyClosed f]

/-- **Points satisfying the descent condition.** If `E` descends along `g : T ⟶ S`, every point
`g t` lies in the base open of some rank `m`, and `m` is the dimension of the global sections of
`E` on the fibre over `g t`. -/
theorem exists_rank_of_descendsFromBase
    (hchart : ∀ {V : S.Opens} (hV : IsAffineOpen V) (St : NoetherianStage f E hV)
      (p : PrimeSpectrum St.A₀), HasChart f E St p)
    (hSt : ∀ {V : S.Opens} (hV : IsAffineOpen V), Nonempty (NoetherianStage f E hV))
    {T : Scheme.{u}} {g : T ⟶ S} (hg : DescendsFromBase f E g) (t : T) :
    ∃ m : ℕ, g t ∈ Scheme.Modules.rankBaseOpen f E m ∧ fibreH0 f E (g t) = m := by
  obtain ⟨κ, W, hW, hfree⟩ := hg.exists_affine_cover_iso_free
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show t ∈ ⨆ k, W k by rw [hW]; trivial)
  obtain ⟨m, ⟨e⟩⟩ := (hfree k).2
  have e' : (Scheme.Modules.pullback (pullback.fst f ((W k).ι ≫ g))).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin m)) := e
  have hRB := Scheme.Modules.mem_rankBaseOpen_of_pullback_iso_free f E g t (W k) hk e'
  obtain ⟨V, hV, x₀, hx₀⟩ := exists_isAffineOpen_fromSpec_eq (g t)
  let St := (hSt hV).some
  have hrange : Set.range (T.fromSpecResidueField t ≫ g) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact ⟨x₀, hx₀⟩
  obtain ⟨kk, hkk⟩ := exists_comp_eq_of_range_subset hV.fromSpec _ hrange
  let pt : Spec (T.residueField t) := IsLocalRing.closedPoint (T.residueField t)
  let x : Spec Γ(S, V) := kk pt
  have hx : hV.fromSpec x = g t := by
    rw [← Scheme.Hom.comp_apply, hkk, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  obtain ⟨g', -, r, Z, -, -, -, hb, hc, -⟩ :=
    hchart hV St (Spec.map (CommRingCat.ofHom St.φ) x)
  have hrW : Set.range (T.fromSpecResidueField t) ⊆ Set.range (W k).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.fromSpecResidueField_apply]
    exact hk
  obtain ⟨a, ha'⟩ := exists_comp_eq_of_range_subset (W k).ι _ hrW
  have ha : a ≫ (W k).ι ≫ g = kk ≫ hV.fromSpec := by
    rw [hkk, ← Category.assoc, ha']
  exact ⟨m, hRB, by
    rw [← hx, hb x rfl, hc _ kk m rfl (nonempty_pullback_fst_iso_free_of_comp f E a ha e')]⟩

end PPoints

section Charts

/-- Factoring through the base change of `Z₀ ⟶ Y` along `b : U ⟶ Y` is factoring the composite
with `b` through `Z₀`. -/
theorem exists_lift_pullback_snd_iff {Y U T : Scheme.{u}} (Z₀ : Over Y) (b : U ⟶ Y)
    (a : T ⟶ U) :
    (∃ l : T ⟶ pullback Z₀.hom b, l ≫ pullback.snd Z₀.hom b = a) ↔
      ∃ l : T ⟶ Z₀.left, l ≫ Z₀.hom = a ≫ b := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, Category.assoc]⟩
  · rintro ⟨l, hl⟩
    exact ⟨pullback.lift l a hl, pullback.lift_snd _ _ _⟩

/-- The base change of an immersion of finite presentation is an immersion of finite
presentation. -/
theorem isImmersion_finitePresentation_pullback_snd {Y U : Scheme.{u}} (Z₀ : Over Y)
    (hi : IsImmersion Z₀.hom) (hfp : FinitePresentation Z₀.hom) (b : U ⟶ Y) :
    IsImmersion (pullback.snd Z₀.hom b) ∧ FinitePresentation (pullback.snd Z₀.hom b) := by
  obtain ⟨h₁, h₂, h₃⟩ := hfp
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The empty open subscheme is an immersion of finite presentation. -/
theorem isImmersion_finitePresentation_bot {U : Scheme.{u}} :
    IsImmersion (⊥ : U.Opens).ι ∧ FinitePresentation (⊥ : U.Opens).ι := by
  have : IsEmpty (⊥ : U.Opens).toScheme := ⟨fun x ↦ x.2⟩
  refine ⟨inferInstance, inferInstance, ⟨fun V _ _ ↦ ?_⟩, inferInstance⟩
  rw [Set.eq_empty_of_isEmpty ((⊥ : U.Opens).ι ⁻¹' V)]
  exact isCompact_empty

/-- A morphism factors through the empty open subscheme exactly when its source is empty. -/
theorem exists_lift_bot_iff {U T : Scheme.{u}} (a : T ⟶ U) :
    (∃ l : T ⟶ (⊥ : U.Opens).toScheme, l ≫ (⊥ : U.Opens).ι = a) ↔ IsEmpty T := by
  refine ⟨fun ⟨l, _⟩ ↦ ⟨fun y ↦ (l y).2⟩, fun h ↦ ?_⟩
  refine exists_comp_eq_of_range_subset _ a ?_
  rintro _ ⟨y, rfl⟩
  exact h.elim y

end Charts

section Empty

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
  (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

include hO in
/-- The descent condition holds along any morphism out of the empty scheme: it is local on the
source, and the empty family covers the empty scheme. -/
theorem descendsFromBase_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (g : T ⟶ S) :
    DescendsFromBase f E g :=
  @descendsFromBase_of_iSup_eq_top _ _ f _ _ hO E (by assumption) _ g PEmpty PEmpty.elim
    (eq_top_iff.2 fun y ↦ isEmptyElim y) fun k ↦ k.elim

end Empty

section Glue

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The open of `S` on which a chart over the affine open `V` is used: the image in `V` of the
preimage of the basic open `D(g)` of the stage, intersected with the base open of rank `ρ`. -/
def glueOpen [UniversallyClosed f] {V : S.Opens} (hV : IsAffineOpen V) {A₀ : Type u}
    [CommRing A₀] (φ : A₀ →+* Γ(S, V)) (g : A₀) (ρ : ℕ) : S.Opens :=
  hV.fromSpec ''ᵁ (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen g) ⊓
    Scheme.Modules.rankBaseOpen f E ρ

/-- Membership in a glue open. -/
theorem mem_glueOpen [UniversallyClosed f] {V : S.Opens} (hV : IsAffineOpen V) {A₀ : Type u}
    [CommRing A₀] (φ : A₀ →+* Γ(S, V)) (g : A₀) (ρ : ℕ) {s : S} :
    s ∈ glueOpen f E hV φ g ρ ↔
      (∃ x : Spec Γ(S, V), Spec.map (CommRingCat.ofHom φ) x ∈ PrimeSpectrum.basicOpen g ∧
        hV.fromSpec x = s) ∧ s ∈ Scheme.Modules.rankBaseOpen f E ρ :=
  Iff.rfl

/-- **A chart on a glue open.** On the glue open of a chart of rank `r` and a rank `ρ ≥ r`, the
descent condition is represented by an immersion of finite presentation: the base change of the
chart when `ρ = r`, and the empty subscheme when `ρ > r`, since then no point of the glue open
satisfies the descent condition. -/
theorem exists_glueChart [Flat f] [IsProper f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (hchart : ∀ {V : S.Opens} (hV : IsAffineOpen V) (St : NoetherianStage f E hV)
      (p : PrimeSpectrum St.A₀), HasChart f E St p)
    (hSt : ∀ {V : S.Opens} (hV : IsAffineOpen V), Nonempty (NoetherianStage f E hV))
    [Surjective f] {V : S.Opens} (hV : IsAffineOpen V) (St : NoetherianStage f E hV)
    (g : St.A₀) (r : ℕ) (Z : Over (Spec (.of St.A₀))) (hi : IsImmersion Z.hom)
    (hfp : FinitePresentation Z.hom)
    (hb : ∀ x : Spec Γ(S, V), Spec.map (CommRingCat.ofHom St.φ) x ∈ PrimeSpectrum.basicOpen g →
      fibreH0 f E (hV.fromSpec x) ≤ r)
    (he : ∀ {T : Scheme.{u}} (h : T ⟶ Spec Γ(S, V)),
      Set.range (h ≫ Spec.map (CommRingCat.ofHom St.φ)) ⊆
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum St.A₀)) →
      Set.range (h ≫ hV.fromSpec) ⊆ Scheme.Modules.rankBaseOpen f E r →
      ((∃ l : T ⟶ Z.left, l ≫ Z.hom = h ≫ Spec.map (CommRingCat.ofHom St.φ)) ↔
        DescendsFromBase f E (h ≫ hV.fromSpec)))
    (ρ : ℕ) (hρ : r ≤ ρ) :
    ∃ Z' : Over (glueOpen f E hV St.φ g ρ : Scheme.{u}), IsImmersion Z'.hom ∧
      FinitePresentation Z'.hom ∧
      ∀ {T : Scheme.{u}} (a : T ⟶ (glueOpen f E hV St.φ g ρ : Scheme.{u})),
        (∃ l : T ⟶ Z'.left, l ≫ Z'.hom = a) ↔
          DescendsFromBase f E (a ≫ (glueOpen f E hV St.φ g ρ).ι) := by
  set U := glueOpen f E hV St.φ g ρ
  rcases hρ.eq_or_lt with rfl | hlt
  · have hUV : Set.range U.ι ⊆ Set.range hV.fromSpec := by
      rw [Scheme.Opens.range_ι]
      rintro s ⟨⟨x, -, rfl⟩, -⟩
      exact ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := exists_comp_eq_of_range_subset hV.fromSpec U.ι hUV
    obtain ⟨hi', hfp'⟩ := isImmersion_finitePresentation_pullback_snd Z hi hfp
      (c ≫ Spec.map (CommRingCat.ofHom St.φ))
    refine ⟨Over.mk (pullback.snd Z.hom (c ≫ Spec.map (CommRingCat.ofHom St.φ))), hi', hfp',
      fun {T} a ↦ ?_⟩
    refine (exists_lift_pullback_snd_iff Z (c ≫ Spec.map (CommRingCat.ofHom St.φ)) a).trans ?_
    have h1 : ∀ u : (U : Scheme.{u}),
        Spec.map (CommRingCat.ofHom St.φ) (c u) ∈ PrimeSpectrum.basicOpen g := by
      intro u
      obtain ⟨⟨x, hx, hxu⟩, -⟩ := u.2
      have hxu' : hV.fromSpec x = u.1 := hxu
      have hcu : c u = x := by
        apply hV.fromSpec.isOpenEmbedding.injective
        rw [hxu', ← Scheme.Hom.comp_apply, hc]
        rfl
      rwa [hcu]
    have key := he (a ≫ c) (by
        rintro _ ⟨t, rfl⟩
        rw [Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact h1 (a t)) (by
        rintro _ ⟨t, rfl⟩
        rw [Category.assoc, hc, Scheme.Hom.comp_apply]
        exact (a t).2.2)
    simpa only [Category.assoc, hc] using key
  · refine ⟨Over.mk (⊥ : (U : Scheme.{u}).Opens).ι, isImmersion_finitePresentation_bot.1,
      isImmersion_finitePresentation_bot.2, fun {T} a ↦ ?_⟩
    refine (exists_lift_bot_iff a).trans ⟨fun _ ↦ descendsFromBase_of_isEmpty f hO E _,
      fun hP ↦ ?_⟩
    rcases isEmpty_or_nonempty T with hT | hT
    · exact hT
    exfalso
    obtain ⟨t⟩ := hT
    obtain ⟨m, hm, hfib⟩ := exists_rank_of_descendsFromBase f E hchart hSt hP t
    obtain ⟨⟨x, hx, hxs⟩, hRB⟩ := (a t).2
    have hat : (a ≫ U.ι) t = (a t).1 := rfl
    rw [hat] at hm hfib
    have hmρ : m = ρ := Scheme.Modules.eq_of_mem_rankBaseOpen f E hm hRB (f.surjective _)
    have hxs' : hV.fromSpec x = (a t).1 := hxs
    have hle := hb x hx
    rw [hxs', hfib] at hle
    omega

/-- The union of the glue opens of a family of charts over the affine opens of `S` is
quasi-compact over `S`. -/
private theorem quasiCompact_iSup_glueOpen [IsProper f] [UniversallyOpen f] [Surjective f]
    (St : ∀ V : {V : S.Opens // IsAffineOpen V}, NoetherianStage f E V.2)
    (cg : ∀ V : {V : S.Opens // IsAffineOpen V}, PrimeSpectrum (St V).A₀ → (St V).A₀)
    (hcg : ∀ V p, p ∈ PrimeSpectrum.basicOpen (cg V p))
    (cr : ∀ V : {V : S.Opens // IsAffineOpen V}, PrimeSpectrum (St V).A₀ → ℕ)
    (hle : ∀ V p (x : Spec Γ(S, V.1)),
      Spec.map (CommRingCat.ofHom (St V).φ) x ∈ PrimeSpectrum.basicOpen (cg V p) →
        fibreH0 f E (V.2.fromSpec x) ≤ cr V p)
    (heq : ∀ V p (x : Spec Γ(S, V.1)), Spec.map (CommRingCat.ofHom (St V).φ) x = p →
      fibreH0 f E (V.2.fromSpec x) = cr V p) :
    QuasiCompact (⨆ i : Σ V : {V : S.Opens // IsAffineOpen V}, Σ p : PrimeSpectrum (St V).A₀,
      {ρ : ℕ // cr V p ≤ ρ}, glueOpen f E i.1.2 (St i.1).φ (cg i.1 i.2.1) i.2.2.1).ι := by
  set G : S.Opens := ⨆ i : Σ V : {V : S.Opens // IsAffineOpen V},
    Σ p : PrimeSpectrum (St V).A₀, {ρ : ℕ // cr V p ≤ ρ},
      glueOpen f E i.1.2 (St i.1).φ (cg i.1 i.2.1) i.2.2.1
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro W hW
  rw [G.ι.isOpenEmbedding.isInducing.isCompact_iff]
  change IsCompact (G.ι '' (G.ι ⁻¹' (W : Set S)))
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  let W' : {V : S.Opens // IsAffineOpen V} := ⟨W, hW⟩
  let πW := Spec.map (CommRingCat.ofHom (St W').φ)
  let O : ℕ → (Spec (.of (St W').A₀)).Opens := fun ρ ↦
    ⨆ (p : PrimeSpectrum (St W').A₀) (_ : cr W' p ≤ ρ), PrimeSpectrum.basicOpen (cg W' p)
  let R : Set ℕ := Scheme.Modules.finiteLocallyFreeRank E '' (f ⁻¹' (W : Set S))
  have hR : R.Finite :=
    ((f.isCompact_preimage hW.isCompact).image
      (Scheme.Modules.finiteLocallyFreeRank E).continuous).finite_of_discrete
  have hdecomp : (W : Set S) ∩ G = ⋃ ρ ∈ R,
      (hW.fromSpec '' (πW ⁻¹ᵁ O ρ : Set _)) ∩ Scheme.Modules.rankBaseOpen f E ρ := by
    ext s
    constructor
    · rintro ⟨hsW, hsG⟩
      obtain ⟨⟨V', p', ρ, hρ⟩, ⟨x', hx', hx's⟩, hRB⟩ := Opens.mem_iSup.1 hsG
      obtain ⟨y, hy⟩ := f.surjective s
      have hyρ := (Scheme.Modules.mem_rankBaseOpen_iff f E).1 hRB y hy
      obtain ⟨x₀, hx₀⟩ : s ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
      refine Set.mem_biUnion (x := ρ) ⟨y, by rwa [Set.mem_preimage, hy],
        (Scheme.Modules.mem_rankStratum E).1 hyρ⟩ ⟨⟨x₀, ?_, hx₀⟩, hRB⟩
      have hq : cr W' (πW x₀) ≤ ρ := by
        have h1 := heq W' (πW x₀) x₀ rfl
        have h2 := hle V' p' x' hx'
        have hx's' : V'.2.fromSpec x' = s := hx's
        rw [hx₀] at h1
        rw [hx's'] at h2
        omega
      exact Opens.mem_iSup.2 ⟨πW x₀, Opens.mem_iSup.2 ⟨hq, hcg W' (πW x₀)⟩⟩
    · intro hs
      obtain ⟨ρ, -, ⟨x₀, hx₀O, rfl⟩, hRB⟩ := Set.mem_iUnion₂.1 hs
      obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hx₀O
      obtain ⟨hpρ, hpg⟩ := Opens.mem_iSup.1 hp
      exact ⟨hW.range_fromSpec ▸ Set.mem_range_self x₀,
        Opens.mem_iSup.2 ⟨⟨W', p, ρ, hpρ⟩, ⟨x₀, hpg, rfl⟩, hRB⟩⟩
  rw [hdecomp]
  refine hR.isCompact_biUnion fun ρ _ ↦ ?_
  refine (IsCompact.image ?_ hW.fromSpec.continuous).inter_right
    (isClosed_rankBaseOpen f E ρ)
  exact πW.isCompact_preimage
    (TopologicalSpace.NoetherianSpace.isCompact (α := PrimeSpectrum (St W').A₀) _)

/-- **Stacks Tag 0BDP from local charts.** Let `f : X ⟶ S` be flat, proper and locally of finite
presentation with `𝒪_T = (X ×_S T ⟶ T)_* 𝒪` for every base change, and `E` finite locally free
on `X`. If every prime of every Noetherian stage of `f` and `E` has a local chart, the descent
condition for `E` is represented by an immersion of finite presentation into `S`. -/
theorem hasDescentLocus_of_hasChart {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hchart : ∀ {V : S.Opens} (hV : IsAffineOpen V) (St : NoetherianStage f E hV)
      (p : PrimeSpectrum St.A₀), HasChart f E St p) :
    HasDescentLocus f E := by
  have : Surjective f := surjective_of_isIso_structureSheafHom f (hO (𝟙 S))
  have : UniversallyOpen f := universallyOpen_of_flat_of_locallyOfFinitePresentation f
  have hSt : ∀ {V : S.Opens} (hV : IsAffineOpen V), Nonempty (NoetherianStage f E hV) :=
    fun hV ↦ nonempty_noetherianStage f E hV
  have St : ∀ V : {V : S.Opens // IsAffineOpen V}, NoetherianStage f E V.2 :=
    fun V ↦ (hSt V.2).some
  choose cg hcg cr cZ hZi hZfp hle heq _ hrep using
    fun (V : {V : S.Opens // IsAffineOpen V}) (p : PrimeSpectrum (St V).A₀) ↦
      hchart V.2 (St V) p
  let ι := Σ V : {V : S.Opens // IsAffineOpen V}, Σ p : PrimeSpectrum (St V).A₀,
    {ρ : ℕ // cr V p ≤ ρ}
  let U : ι → S.Opens := fun i ↦ glueOpen f E i.1.2 (St i.1).φ (cg i.1 i.2.1) i.2.2.1
  have hchartU : ∀ i : ι, ∃ Z' : Over (U i : Scheme.{u}), IsImmersion Z'.hom ∧
      FinitePresentation Z'.hom ∧ ∀ {T : Scheme.{u}} (a : T ⟶ (U i : Scheme.{u})),
        (∃ l : T ⟶ Z'.left, l ≫ Z'.hom = a) ↔ DescendsFromBase f E (a ≫ (U i).ι) :=
    fun i ↦ exists_glueChart f E hO hchart hSt i.1.2 (St i.1) (cg i.1 i.2.1) (cr i.1 i.2.1)
      (cZ i.1 i.2.1) (hZi _ _) (hZfp _ _) (hle _ _) (hrep _ _) i.2.2.1 i.2.2.2
  choose Z hZimm hZfp' hZ using hchartU
  let G : S.Opens := ⨆ i, U i
  have hPG : ∀ {T : Scheme.{u}} (g : T ⟶ S), DescendsFromBase f E g → Set.range g ⊆ G := by
    rintro T g hg _ ⟨t, rfl⟩
    obtain ⟨m, hm, hfib⟩ := exists_rank_of_descendsFromBase f E hchart hSt hg t
    obtain ⟨V, hV, x, hx⟩ := exists_isAffineOpen_fromSpec_eq (g t)
    let V' : {V : S.Opens // IsAffineOpen V} := ⟨V, hV⟩
    let p := Spec.map (CommRingCat.ofHom (St V').φ) x
    have hr : cr V' p = m := by
      rw [← hfib, ← hx]
      exact (heq V' p x rfl).symm
    exact Opens.mem_iSup.2 ⟨⟨V', p, m, hr.le⟩, ⟨x, hcg V' p, hx⟩, hm⟩
  have hG : QuasiCompact G.ι := quasiCompact_iSup_glueOpen f E St cg hcg cr hle heq
  obtain ⟨Z₀, h₁, h₂, h₃⟩ := exists_isImmersion_represents_of_local_of_le
    (fun g ↦ DescendsFromBase f E g) (fun h _ hg ↦ hg.precomp h)
    (fun g _ V hV h ↦
      @descendsFromBase_of_iSup_eq_top _ _ f _ _ hO E (by assumption) _ g _ V hV h)
    G hG hPG U (fun i ↦ le_iSup U i) Z hZimm hZfp' hZ rfl
  exact ⟨Z₀, h₁, h₂, fun g ↦ h₃ g⟩

end Glue

end AlgebraicGeometry.DescentLocus

end
