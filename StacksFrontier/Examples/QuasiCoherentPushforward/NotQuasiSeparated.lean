module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Quasi-separatedness is necessary for quasi-coherent pushforward

Let `A = ∏_{n ≥ 0} ℤ/2ⁿ⁺¹ℤ`, let `t = 2`, and let `eₙ` be the coordinate idempotents. Put
`V = ⋃ₙ D(eₙ) ⊆ Spec A` and let `X` be the scheme obtained by gluing two copies of `Spec A`
along `V`. The structure morphism `f : X ⟶ Spec A` is quasi-compact, because `X` is covered by
two compact opens, but it is not quasi-separated, and `f_* 𝒪_X` is not quasi-coherent.

The obstruction is that `V ∩ D(t)` is empty while `D(t)` is not: over `D(t)` the two charts of
`X` are disjoint, so there is a section of `f_* 𝒪_X` over `D(t)` restricting to `1` on one
chart and to `0` on the other. A global section of `𝒪_X`, on the other hand, has the same
value on both charts, because `V` meets every `D(eₙ)` and the coordinates of `A` are detected
there. So no power of `t` multiplies that section into the image of the global sections, and
quasi-coherence fails. Failure of quasi-separatedness then follows from the theorem that a
quasi-compact quasi-separated morphism does push quasi-coherent modules forward.

## Main results

* `exists_quasiCompact_not_quasiSeparated_pushforward_not_isQuasicoherent`, in the namespace
  `Stacks.Examples.QcohPushforward`: a quasi-compact morphism which is not quasi-separated and
  whose pushforward of the quasi-coherent structure sheaf is not quasi-coherent.

## Implementation notes

The structure sheaf as a module over itself is `SheafOfModules.unit`, and its pushforward is
`AlgebraicGeometry.Scheme.Modules.pushforward`; the four properties are attached to a single
morphism in one existential statement. The glued scheme is the pushout of the open immersion
`V ⟶ Spec A` along itself, whose charts are the two pushout inclusions. The index type of the
product is `ULift ℕ` so that `A` lies in the universe `Spec` requires.

## References

* [Stacks Project, Tag 078D](https://stacks.math.columbia.edu/tag/078D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Examples.QcohPushforward

universe u

/-- The ring `∏_{n ≥ 0} ℤ/2ⁿ⁺¹ℤ`. -/
private abbrev doubledRing : Type u :=
  ∀ i : ULift.{u} ℕ, ZMod (2 ^ (i.down + 1))

/-- The element `t = 2` of `∏_{n ≥ 0} ℤ/2ⁿ⁺¹ℤ`, all of whose powers are nonzero while each
coordinate is nilpotent. -/
private def doubledT : doubledRing.{u} := fun _ ↦ 2

/-- The `i`-th coordinate idempotent of `∏_{n ≥ 0} ℤ/2ⁿ⁺¹ℤ`. -/
private def doubledIdem (i : ULift.{u} ℕ) : doubledRing.{u} :=
  fun j ↦ if j = i then 1 else 0

/-- The spectrum of `∏_{n ≥ 0} ℤ/2ⁿ⁺¹ℤ`. -/
private noncomputable abbrev doubledSpec : Scheme.{u} :=
  Spec (CommRingCat.of doubledRing.{u})

/-- The open subset `V = ⋃ₙ D(eₙ)` along which the two copies of the spectrum are glued. -/
private noncomputable def doubledOverlap : doubledSpec.{u}.Opens :=
  ⨆ i : ULift.{u} ℕ, PrimeSpectrum.basicOpen (doubledIdem i)

/-- The open immersion of the gluing locus into the spectrum. -/
private noncomputable def doubledOverlapInclusion :
    doubledOverlap.{u}.toScheme ⟶ doubledSpec.{u} :=
  Scheme.Opens.ι _

/-- The inclusion of the gluing locus is an open immersion. -/
private instance isOpenImmersion_doubledOverlapInclusion :
    IsOpenImmersion doubledOverlapInclusion.{u} := by
  dsimp [doubledOverlapInclusion]
  infer_instance

/-- The scheme obtained by gluing two copies of `Spec A` along `V`. -/
private noncomputable abbrev doubledScheme : Scheme.{u} :=
  pushout doubledOverlapInclusion.{u} doubledOverlapInclusion.{u}

/-- The structure morphism of the glued scheme, which is the identity on each chart. -/
private noncomputable def doubledMap : doubledScheme.{u} ⟶ doubledSpec.{u} :=
  pushout.desc (𝟙 _) (𝟙 _) (by simp)

/-- The first chart followed by the structure morphism is the identity. -/
private lemma doubledMap_inl :
    pushout.inl doubledOverlapInclusion doubledOverlapInclusion ≫
      doubledMap = 𝟙 doubledSpec :=
  pushout.inl_desc _ _ _

/-- The second chart followed by the structure morphism is the identity. -/
private lemma doubledMap_inr :
    pushout.inr doubledOverlapInclusion doubledOverlapInclusion ≫
      doubledMap = 𝟙 doubledSpec :=
  pushout.inr_desc _ _ _

/-- Every point of the glued scheme lies on one of the two charts. -/
private theorem doubledScheme_charts_cover (x : doubledScheme.{u}) :
    (∃ y, pushout.inl doubledOverlapInclusion doubledOverlapInclusion y = x) ∨
      ∃ y, pushout.inr doubledOverlapInclusion doubledOverlapInclusion y = x := by
  obtain ⟨k, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span doubledOverlapInclusion doubledOverlapInclusion) x
  cases k with
  | none =>
      refine Or.inl ⟨doubledOverlapInclusion y, ?_⟩
      have hchart : colimit.ι
          (span doubledOverlapInclusion doubledOverlapInclusion) none =
          doubledOverlapInclusion ≫
            pushout.inl doubledOverlapInclusion doubledOverlapInclusion := by
        change colimit.ι
          (span doubledOverlapInclusion doubledOverlapInclusion) none =
          doubledOverlapInclusion ≫ colimit.ι
            (span doubledOverlapInclusion doubledOverlapInclusion) WalkingSpan.left
        simpa only [span_map_fst] using
          (colimit.w (span doubledOverlapInclusion doubledOverlapInclusion)
            WalkingSpan.Hom.fst).symm
      rw [hchart] at hy
      simpa using hy
  | some j =>
      cases j with
      | left => exact Or.inl ⟨y, by simpa [pushout.inl] using hy⟩
      | right => exact Or.inr ⟨y, by simpa [pushout.inr] using hy⟩

/-- The glued scheme is compact, being covered by the two charts. -/
private theorem doubledScheme_compactSpace :
    CompactSpace doubledScheme.{u} := by
  let f : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inl doubledOverlapInclusion doubledOverlapInclusion
  let g : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inr doubledOverlapInclusion doubledOverlapInclusion
  have hcover : Set.range f.base ∪ Set.range g.base = Set.univ := by
    ext x
    simpa only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true] using
      doubledScheme_charts_cover x
  have hcompact := (isCompact_range f.continuous).union (isCompact_range g.continuous)
  rw [hcover] at hcompact
  change IsCompact (Set.univ : Set doubledScheme.{u}) at hcompact
  exact isCompact_univ_iff.mp hcompact

/-- The gluing locus maps to the intersection of the two charts. -/
private noncomputable def doubledOverlapToIntersection :
    doubledOverlap.toScheme ⟶
      pullback (pushout.inl doubledOverlapInclusion doubledOverlapInclusion)
        (pushout.inr doubledOverlapInclusion doubledOverlapInclusion) :=
  pullback.lift doubledOverlapInclusion doubledOverlapInclusion
    (pushout.condition (f := doubledOverlapInclusion) (g := doubledOverlapInclusion))

/-- The map from the gluing locus to the intersection of the charts is compatible with the
first projection. -/
private theorem doubledOverlapToIntersection_fst_apply (y : doubledOverlap.{u}.toScheme) :
    (pullback.fst (pushout.inl doubledOverlapInclusion doubledOverlapInclusion)
        (pushout.inr doubledOverlapInclusion doubledOverlapInclusion))
      (doubledOverlapToIntersection y) = doubledOverlapInclusion y := by
  rw [← Scheme.Hom.comp_apply, doubledOverlapToIntersection, pullback.lift_fst]

/-- The gluing locus surjects onto the intersection of the two charts. -/
private theorem doubledOverlapToIntersection_surjective :
    Function.Surjective doubledOverlapToIntersection.{u}.base := by
  intro z
  let f : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inl doubledOverlapInclusion doubledOverlapInclusion
  let g : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inr doubledOverlapInclusion doubledOverlapInclusion
  let F := span doubledOverlapInclusion doubledOverlapInclusion
  have he : f.base ((pullback.fst f g).base z) = g.base ((pullback.snd f g).base z) :=
    ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.base) (pullback.condition (f := f) (g := g))) z
  have he' : colimit.ι F WalkingSpan.left ((pullback.fst f g).base z) =
      colimit.ι F WalkingSpan.right ((pullback.snd f g).base z) := by
    simpa [f, g, pushout.inl, pushout.inr] using he
  obtain ⟨k, α, β, y, hy₁, hy₂⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := F)).mp he'
  cases k with
  | none =>
      refine ⟨y, ?_⟩
      apply (Scheme.Hom.isOpenEmbedding (pullback.fst f g)).injective
      rw [doubledOverlapToIntersection_fst_apply]
      cases α
      simpa [F, span_map_fst] using hy₁
  | some j =>
      cases j with
      | left => cases β
      | right => cases α

/-- The element `t` is nilpotent on each coordinate: `tⁿ⁺¹ eₙ = 0`. -/
private theorem doubledT_pow_mul_idem (i : ULift.{u} ℕ) :
    doubledT ^ (i.down + 1) * doubledIdem i = 0 := by
  ext j
  by_cases h : j = i
  · subst j
    simp only [Pi.mul_apply, Pi.pow_apply, doubledT, doubledIdem,
      ite_true, mul_one, Pi.zero_apply]
    change (Nat.cast (2 : ℕ) : ZMod (2 ^ (i.down + 1))) ^ (i.down + 1) = 0
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  · simp [doubledIdem, h]

/-- No power of `t` vanishes, since the `n`-th coordinate of `tⁿ` is nonzero. -/
private theorem doubledT_pow_ne_zero (n : ℕ) : doubledT.{u} ^ n ≠ 0 := by
  intro h
  have hcoord := congrFun h (ULift.up n)
  change (2 : ZMod (2 ^ (n + 1))) ^ n = 0 at hcoord
  have heq : ((2 ^ n : ℕ) : ZMod (2 ^ (n + 1))) = 0 := by
    convert hcoord using 1
    norm_cast
  have hdvd : 2 ^ (n + 1) ∣ 2 ^ n := (ZMod.natCast_eq_zero_iff _ _).mp heq
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  omega

/-- The standard open `D(t) ⊆ Spec A`. -/
private noncomputable abbrev doubledTBasicOpen : doubledSpec.{u}.Opens :=
  PrimeSpectrum.basicOpen doubledT.{u}

/-- The gluing locus is disjoint from `D(t)`: a prime containing no `eₙ` contains `t`,
because `tⁿ⁺¹ eₙ = 0`. -/
private theorem doubledOverlap_disjoint_t :
    doubledOverlap.{u} ⊓ doubledTBasicOpen.{u} = ⊥ := by
  ext x
  constructor
  · rintro ⟨hxV, hxt⟩
    have hxV' : x ∈ (⨆ i : ULift.{u} ℕ, PrimeSpectrum.basicOpen (doubledIdem i) :
        TopologicalSpace.Opens (PrimeSpectrum doubledRing.{u})) := hxV
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV'
    have hprod : doubledT.{u} ^ (i.down + 1) * doubledIdem.{u} i ∈ x.asIdeal := by
      rw [doubledT_pow_mul_idem]
      exact Ideal.zero_mem _
    rcases x.isPrime.mem_or_mem hprod with ht | hi
    · exact hxt ((x.isPrime.pow_mem_iff_mem _ (by omega)).mp ht)
    · exact hxi hi
  · simp

/-- The image of the gluing locus in the glued scheme is exactly the intersection of the two
charts. -/
private theorem doubledOverlap_image_eq_chart_intersection :
    Set.range (doubledOverlapInclusion.{u} ≫
        pushout.inl doubledOverlapInclusion.{u} doubledOverlapInclusion.{u}).base =
      Set.range (pushout.inl doubledOverlapInclusion.{u}
        doubledOverlapInclusion.{u}).base ∩
        Set.range (pushout.inr doubledOverlapInclusion.{u}
          doubledOverlapInclusion.{u}).base := by
  let f := pushout.inl doubledOverlapInclusion.{u} doubledOverlapInclusion.{u}
  let g := pushout.inr doubledOverlapInclusion.{u} doubledOverlapInclusion.{u}
  let j : pullback f g ⟶ doubledScheme.{u} := pullback.fst f g ≫ f
  have hrange : Set.range j.base = Set.range f.base ∩ Set.range g.base := by
    change Set.range (fun x => f.base ((pullback.fst f g).base x)) = _
    exact IsOpenImmersion.range_pullback_to_base_of_left (f := f) (g := g)
  have hcompBase : (fun x => j.base (doubledOverlapToIntersection.base x)) =
      (doubledOverlapInclusion ≫ f).base :=
    funext fun x ↦ congrArg f.base (doubledOverlapToIntersection_fst_apply x)
  rw [← hcompBase]
  exact (doubledOverlapToIntersection_surjective.range_comp _).trans hrange

/-- A global section of the glued scheme has the same coordinates on both charts: each
coordinate of `A` is detected on `D(eₙ)`, which lies in the gluing locus. -/
private theorem doubledGlobalSection_chart_coordinates
    (s : Γ(doubledScheme.{u}, ⊤)) :
    ∀ i : ULift.{u} ℕ,
      (((Scheme.ΓSpecIso (CommRingCat.of doubledRing.{u})).hom
        ((pushout.inl doubledOverlapInclusion doubledOverlapInclusion).appTop s)) i) =
      (((Scheme.ΓSpecIso (CommRingCat.of doubledRing.{u})).hom
        ((pushout.inr doubledOverlapInclusion doubledOverlapInclusion).appTop s)) i) := by
  intro i
  let Zi := ZMod (2 ^ (i.down + 1))
  let Zi' : Type u := ULift.{u} Zi
  let lift : Zi →+* Zi' :=
    { toFun := ULift.up
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let π' : CommRingCat.of doubledRing.{u} ⟶ CommRingCat.of Zi' := CommRingCat.ofHom
    (lift.comp (Pi.evalRingHom (fun j : ULift.{u} ℕ => ZMod (2 ^ (j.down + 1))) i))
  let p := Spec.map π'
  let Ui : doubledSpec.{u}.Opens := PrimeSpectrum.basicOpen (doubledIdem i)
  have hpre : p ⁻¹ᵁ Ui = ⊤ := by
    have heval : π'.hom (doubledIdem i) = 1 := by
      change ULift.up (if i = i then (1 : Zi) else 0) = (1 : Zi')
      simp only [ite_true]
      rfl
    change PrimeSpectrum.basicOpen (π'.hom (doubledIdem i)) = ⊤
    rw [heval, PrimeSpectrum.basicOpen_one]
  have hUi : Ui ≤ doubledOverlap.{u} :=
    le_iSup (fun j : ULift.{u} ℕ => PrimeSpectrum.basicOpen (doubledIdem j)) i
  have hpV : Set.range p ⊆ Set.range doubledOverlapInclusion := by
    rintro _ ⟨x, rfl⟩
    have hx : p x ∈ Ui := by
      change x ∈ p ⁻¹ᵁ Ui
      rw [hpre]
      trivial
    exact ⟨⟨p x, hUi hx⟩, rfl⟩
  let q := IsOpenImmersion.lift doubledOverlapInclusion p hpV
  have hq : q ≫ doubledOverlapInclusion = p := IsOpenImmersion.lift_fac _ _ _
  have he : p ≫ pushout.inl doubledOverlapInclusion doubledOverlapInclusion =
      p ≫ pushout.inr doubledOverlapInclusion doubledOverlapInclusion := by
    rw [← hq, Category.assoc, Category.assoc, pushout.condition]
  have hcoord := congrArg (fun h : Spec (CommRingCat.of Zi') ⟶ doubledScheme =>
    h.appTop s) he
  change p.appTop ((pushout.inl doubledOverlapInclusion
    doubledOverlapInclusion).appTop s) =
      p.appTop ((pushout.inr doubledOverlapInclusion
        doubledOverlapInclusion).appTop s) at hcoord
  have hcoord' := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of Zi')).hom z) hcoord
  have hn (a : Γ(doubledSpec, ⊤)) :
      (Scheme.ΓSpecIso (CommRingCat.of Zi')).hom (p.appTop a) =
        π' ((Scheme.ΓSpecIso (CommRingCat.of doubledRing)).hom a) :=
    congrArg (fun h : Γ(doubledSpec, ⊤) ⟶ CommRingCat.of Zi' => h a)
      (Scheme.ΓSpecIso_naturality π')
  rw [hn, hn] at hcoord'
  exact congrArg ULift.down hcoord'

open TopologicalSpace Opposite

/-- On a union of two disjoint opens there is a section of the structure sheaf equal to `1` on
one of them and to `0` on the other. -/
private lemma exists_section_of_disjoint {X : Scheme.{u}} (U V : X.Opens)
    (hUV : U ⊓ V = ⊥) (W : X.Opens) (hU : U ≤ W) (hV : V ≤ W)
    (hcover : W ≤ U ⊔ V) :
    ∃ s : Γ(X, W), X.presheaf.map (homOfLE hU).op s = 1 ∧
      X.presheaf.map (homOfLE hV).op s = 0 := by
  let C : Bool → X.Opens := fun b ↦ if b then V else U
  let t : ∀ b, Γ(X, C b) := fun b ↦ if b then 0 else 1
  have hC (b : Bool) : C b ≤ W := by cases b <;> assumption
  have hcov : W ≤ ⨆ b, C b := hcover.trans (sup_le
    (le_iSup C false) (le_iSup C true))
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf C t := by
    intro i j
    cases i <;> cases j
    · simp [t]
    · have he : C false ⊓ C true = ⊥ := hUV
      have : Subsingleton Γ(X, C false ⊓ C true) := he.symm ▸ inferInstance
      exact Subsingleton.elim _ _
    · have he : C true ⊓ C false = ⊥ := by simpa [C, inf_comm] using hUV
      have : Subsingleton Γ(X, C true ⊓ C false) := he.symm ▸ inferInstance
      exact Subsingleton.elim _ _
    · simp [t]
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' C W
    (fun b ↦ homOfLE (hC b)) hcov t hcompat
  exact ⟨s, hs false, hs true⟩

/-- Pulling a section back along an open immersion agrees with restricting it to the image of
the open subset. -/
private lemma appLE_of_restriction_eq {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] (P : X.Opens) (W : Y.Opens) (h : i ''ᵁ W ≤ P)
    (s : Γ(X, P)) (a : Γ(X, i ''ᵁ W))
    (hs : X.presheaf.map (homOfLE h).op s = a) :
    i.appLE P W (by intro x hx; exact h ⟨x, hx, rfl⟩) s = (i.appIso W).hom a := by
  rw [← hs, ← CommRingCat.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- The two charts of the glued scheme agree on global sections. -/
private lemma doubledGlobalSection_charts_eq (s : Γ(doubledScheme.{u}, ⊤)) :
    (pushout.inl doubledOverlapInclusion doubledOverlapInclusion).appTop s =
      (pushout.inr doubledOverlapInclusion doubledOverlapInclusion).appTop s :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of doubledRing)).hom).injective <|
    funext (doubledGlobalSection_chart_coordinates s)

/-- Over `D(t)` the two charts of the glued scheme are disjoint and cover the preimage, so
there is a section of the structure sheaf equal to `1` on one chart and `0` on the other. -/
private lemma doubled_exists_separating_section :
    let W := doubledTBasicOpen.{u}
    let P := doubledMap.{u} ⁻¹ᵁ W
    let l : doubledSpec.{u} ⟶ doubledScheme.{u} :=
      pushout.inl doubledOverlapInclusion doubledOverlapInclusion
    let r : doubledSpec.{u} ⟶ doubledScheme.{u} :=
      pushout.inr doubledOverlapInclusion doubledOverlapInclusion
    ∃ (hl : W ≤ l ⁻¹ᵁ P) (hr : W ≤ r ⁻¹ᵁ P) (s : Γ(doubledScheme, P)),
      l.appLE P W hl s = 1 ∧ r.appLE P W hr s = 0 := by
  intro W P l r
  have hl (x : doubledSpec) : doubledMap (l x) = x :=
    congrArg (fun f : doubledSpec ⟶ doubledSpec => f x) doubledMap_inl
  have hr (x : doubledSpec) : doubledMap (r x) = x :=
    congrArg (fun f : doubledSpec ⟶ doubledSpec => f x) doubledMap_inr
  have hU : l ''ᵁ W ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    change doubledMap (l x) ∈ W
    rwa [hl]
  have hV : r ''ᵁ W ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    change doubledMap (r x) ∈ W
    rwa [hr]
  have hcover : P ≤ (l ''ᵁ W) ⊔ (r ''ᵁ W) := by
    intro x hx
    rcases doubledScheme_charts_cover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · change doubledMap (l y) ∈ W at hx
      exact Or.inl ⟨y, by rwa [hl] at hx, rfl⟩
    · change doubledMap (r y) ∈ W at hx
      exact Or.inr ⟨y, by rwa [hr] at hx, rfl⟩
  have hdisj : (l ''ᵁ W) ⊓ (r ''ᵁ W) = ⊥ := by
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    have hxrange : x ∈ Set.range l.base ∩ Set.range r.base :=
      ⟨Set.image_subset_range _ _ hx.1, Set.image_subset_range _ _ hx.2⟩
    rw [← doubledOverlap_image_eq_chart_intersection] at hxrange
    obtain ⟨y, rfl⟩ := hxrange
    have hP := hU hx.1
    change doubledMap (l (doubledOverlapInclusion y)) ∈ W at hP
    rw [hl] at hP
    have hmem : doubledOverlapInclusion y ∈
        doubledOverlap ⊓ doubledTBasicOpen := ⟨y.property, hP⟩
    rwa [doubledOverlap_disjoint_t] at hmem
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_disjoint (l ''ᵁ W) (r ''ᵁ W)
    hdisj P hU hV hcover
  exact ⟨fun x hx ↦ hU ⟨x, hx, rfl⟩, fun x hx ↦ hV ⟨x, hx, rfl⟩, s,
    (appLE_of_restriction_eq l P W hU s 1 hs₁).trans (map_one _),
    (appLE_of_restriction_eq r P W hV s 0 hs₂).trans (map_zero _)⟩

/-- If the pushforward of the structure sheaf is quasi-coherent, then every section over the
preimage of a standard open `D(t)` is a global section divided by a power of `t`. -/
private lemma exists_power_mul_eq_restrict {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R)
    [((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent]
    (t : R) (s : Γ(X, f ⁻¹ᵁ PrimeSpectrum.basicOpen t)) :
    ∃ (n : ℕ) (a : Γ(X, ⊤)),
      f.app (PrimeSpectrum.basicOpen t)
        ((Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv (t ^ n))) * s =
      X.presheaf.map (homOfLE le_top).op a := by
  let M := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let F := modulesSpecToSheaf.obj M
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen t
  let s' : F.obj.obj (op U) := s
  have : IsLocalizedModule (.powers t)
      (F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance t
  obtain ⟨⟨a, m⟩, h⟩ := IsLocalizedModule.surj (.powers t)
    (F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s'
  obtain ⟨n, hn⟩ := m.property
  refine ⟨n, a, ?_⟩
  change f.app (PrimeSpectrum.basicOpen t)
    ((Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv m.val)) * s =
      X.presheaf.map (homOfLE le_top).op a at h
  rwa [← hn] at h

/-- Restricting a global section to an open and then pulling back along a morphism is the
same as pulling back and then restricting. -/
private lemma appLE_restriction {X Y : Scheme.{u}} (i : Y ⟶ X)
    (P : X.Opens) (W : Y.Opens) (h : W ≤ i ⁻¹ᵁ P) (a : Γ(X, ⊤)) :
    i.appLE P W h (X.presheaf.map (homOfLE le_top).op a) =
      Y.presheaf.map (homOfLE le_top).op (i.appTop a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  change (i.appLE ⊤ W _) a = _
  rfl

/-- A section of a morphism recovers the sections it pulled back. -/
private lemma appLE_app_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ X)
    (hi : i ≫ f = 𝟙 Y) (W : Y.Opens) (h : W ≤ i ⁻¹ᵁ (f ⁻¹ᵁ W))
    (a : Γ(Y, W)) : i.appLE (f ⁻¹ᵁ W) W h (f.app W a) = a := by
  have hid (g : Y ⟶ Y) (hg : g = 𝟙 Y) (hW : W ≤ g ⁻¹ᵁ W) :
      g.appLE W W hW = 𝟙 _ := by
    subst g
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (congrArg (fun k : op W ⟶ op W ↦ Y.presheaf.map k)
      (Subsingleton.elim (homOfLE hW).op (𝟙 (op W)))).trans (Y.presheaf.map_id _)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appLE i f W W h, hid _ hi h]
  rfl

/-- The pushforward of the structure sheaf of the glued scheme is not quasi-coherent: the
section separating the two charts over `D(t)` would force a unit of `Γ(Spec A, D(t))` to
vanish. -/
private lemma doubled_pushforward_not_isQuasicoherent :
    ¬ ((Scheme.Modules.pushforward doubledMap.{u}).obj
      (SheafOfModules.unit doubledScheme.ringCatSheaf)).IsQuasicoherent := by
  intro hqc
  let W := doubledTBasicOpen.{u}
  let P := doubledMap.{u} ⁻¹ᵁ W
  let l : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inl doubledOverlapInclusion doubledOverlapInclusion
  let r : doubledSpec.{u} ⟶ doubledScheme.{u} :=
    pushout.inr doubledOverlapInclusion doubledOverlapInclusion
  obtain ⟨hl, hr, s, hs₁, hs₂⟩ := doubled_exists_separating_section.{u}
  obtain ⟨n, a, ha⟩ := exists_power_mul_eq_restrict doubledMap doubledT s
  let b : Γ(doubledSpec, W) := doubledSpec.presheaf.map
    (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of doubledRing)).inv
      (doubledT ^ n))
  have hleft : b = doubledSpec.presheaf.map (homOfLE le_top).op (l.appTop a) := by
    have h := congrArg (fun z ↦ l.appLE P W hl z) ha
    rwa [map_mul, appLE_app_of_section doubledMap l doubledMap_inl W hl b,
      hs₁, mul_one, appLE_restriction] at h
  have hright : (0 : Γ(doubledSpec, W)) =
      doubledSpec.presheaf.map (homOfLE le_top).op (r.appTop a) := by
    have h := congrArg (fun z ↦ r.appLE P W hr z) ha
    rwa [map_mul, hs₂, mul_zero, appLE_restriction] at h
  have hb : b = 0 := hleft.trans ((congrArg
    (fun z ↦ doubledSpec.presheaf.map (homOfLE le_top).op z)
    (doubledGlobalSection_charts_eq a)).trans hright.symm)
  have hne : W ≠ ⊥ := by
    intro he
    obtain ⟨m, hm⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff doubledT).mp he
    exact doubledT_pow_ne_zero m hm
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty W).mp hne
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  have hunit : IsUnit b := by
    let t : Γ(doubledSpec, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of doubledRing)).inv doubledT
    have hW : W ≤ doubledSpec.basicOpen t := by
      dsimp only [W, t, doubledTBasicOpen, doubledSpec]
      rw [basicOpen_eq_of_affine]
      exact le_refl _
    have hu := (doubledSpec.toRingedSpace.isUnit_res_basicOpen t).map
      (doubledSpec.presheaf.map (homOfLE hW).op).hom
    change IsUnit ((doubledSpec.presheaf.map (homOfLE hW).op)
      (doubledSpec.presheaf.map (homOfLE (doubledSpec.basicOpen_le t)).op t)) at hu
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at hu
    dsimp [b]
    rw [map_pow, map_pow]
    exact hu.pow n
  exact hunit.ne_zero hb

/-- **Stacks Project, Tag 078D (non-quasi-separated case).** A quasi-compact morphism need not
be quasi-separated, and may send its quasi-coherent structure sheaf to a module which is not
quasi-coherent. -/
@[stacks 078D "non_quasi_separated"]
theorem exists_quasiCompact_not_quasiSeparated_pushforward_not_isQuasicoherent :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      QuasiCompact f ∧
      ¬ QuasiSeparated f ∧
      (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent ∧
      ¬ ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
  have hqc : QuasiCompact doubledMap.{u} :=
    (quasiCompact_iff_compactSpace doubledMap).2 doubledScheme_compactSpace
  have hunit :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit doubledScheme.{u}
  refine ⟨doubledScheme.{u}, doubledSpec.{u}, doubledMap.{u}, hqc,
    fun _ ↦ doubled_pushforward_not_isQuasicoherent
      (AlgebraicGeometry.pushforward_isQuasicoherent doubledMap _),
    hunit, doubled_pushforward_not_isQuasicoherent⟩

end Stacks.Examples.QcohPushforward
