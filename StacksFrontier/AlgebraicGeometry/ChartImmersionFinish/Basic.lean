module

public import StacksFrontier.AlgebraicGeometry.AmpleChartsOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.ChartDegreeEqualisation.Basic
public import StacksFrontier.AlgebraicGeometry.ChartDictionary.Basic

/-!
# Steps 2 and 4 of Stacks Tag 01VS: `ChartImmersion` is a theorem

`Stacks.AmpleImmersionReduction.ChartImmersion f L` says that for an ample `L` on a scheme locally
of finite type over `S` some positive power of `L` carries a generating family of global sections
whose pinned morphism to projective space over `S` is an immersion. It is steps 2 and 4 of the
proof of [Stacks, Tag 01VS], and it was one of the named inputs of that tag. This file proves it:
`Stacks.ChartImmersionFinish.chartImmersion`.

## The three pieces that were missing, and where they come from

Everything geometric is available in the library; what this file adds is the join:

1. **The algebra generators.** [Stacks, Tag 01T2] is formalized as
   `Stacks.AmpleChartsOverBase.exists_generating_family_finiteType_of_isAmple`, whose per-chart
   datum is `RingHom.FiniteType (f.appLE V (nvCover s i) e).hom` — finite-type-ness of the ring
   map, not a generating set. `RingHom.FiniteType` is by definition `Algebra.FiniteType` for
   `RingHom.toAlgebra`, which is by definition `Subalgebra.FG ⊤`, which is by definition the
   existence of a `Finset` whose `Algebra.adjoin` is `⊤`, so this is destructuring:
   `Stacks.ChartImmersionFinish.exists_finset_adjoin_eq_top`. Composed with
   `Stacks.ChartDictionary.mem_closure_of_adjoin_eq_top` it becomes the `Subring.closure` statement
   the chart condition is phrased in, `exists_finset_forall_mem_closure`.

2. **The index type.** `Stacks.ChartDegreeEqualisation.exists_family_ratio_eq` returns the
   equalised family indexed by `ι ⊕ (Σ i, κ i)` — the covering sections on the left, the
   numerators of the generators on the right — while a morphism to `ℙⁿ_S` is pinned by a
   `Fin (n + 1)`-indexed family. Re-indexing along an equivalence and padding with the zero section
   is the pattern of `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple`. The only
   property of the padded family that is needed is that it agrees with the original one along the
   embedding `q ↦ (eqv q).castSucc`, and `Stacks.ChartImmersionFinish.ratio_reindex` says what that
   does to the coordinate ratios: they are the restrictions of the original ones, along an
   inclusion of opens that is in fact an equality.

3. **The sub-family of charts.** `Stacks.ChartDictionary.isImmersion_of_closure` asks for an
   affine chart, an affine open of the base over it and the generation statement at *every* index.
   The equalised family cannot supply that: the nonvanishing open of a numerator is an arbitrary
   open of `X`, neither affine nor over an affine open of `S`, and no generation statement about it
   is available. But step 4 is a Zariski-local argument on the target that only ever uses the
   chartwise hypothesis at an index whose chart contains the given point, so the hypotheses are
   only needed on a sub-family whose charts already cover `X` — which the `inl` part does.
   `Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover` and
   `isImmersion_of_closure_subcover` are that generalisation, with the covering sub-family given
   as an indexing map `ψ : J → Fin (n + 1)` rather than as a subset, so that the affine opens of
   the base are indexed by `J` and no choice is needed to recover them.

The three are entangled and cannot be done in sequence: the generation hypothesis is a property of
*which* family is chosen, and the family that has it is the equalised one, so the re-indexing has
to happen before the family defines the morphism.

## The transport

The generators of 01T2 live on the chart `X_{s₀ i}` of the covering family; the generation
hypothesis is about the chart of the *equalised* family. The two opens are equal, but the rings of
sections over them are not the same term, and the ratios of the equalised family cannot be
rewritten along the equality because the open occurs in their type.
`Stacks.ChartImmersionFinish.forall_mem_closure_chart` does the move once and for all, at the level
of `Subring.closure` rather than of `Algebra.adjoin`, where it is the image of a surjection:
restriction along an equality of opens is surjective, and
`AlgebraicGeometry.Scheme.Hom.appLE_map` says the structure map of the smaller chart is the
restriction of the structure map of the larger.

## Main results

* `Stacks.ChartImmersionFinish.exists_finset_adjoin_eq_top`,
  `exists_finset_forall_mem_closure`: **`RingHom.FiniteType` as a generating set.**
* `Stacks.ChartImmersionFinish.ratio_reindex`: **the coordinate ratios of a re-indexed family.**
* `Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover`,
  `isImmersion_of_closure_subcover`: **step 4 and the chart route on a covering sub-family.**
* `Stacks.ChartImmersionFinish.forall_mem_closure_chart`: **the generation hypothesis transported
  between two equal charts.**
* `Stacks.ChartImmersionFinish.chartImmersion`: **`Stacks.AmpleImmersionReduction.ChartImmersion`,
  with no hypothesis beyond the two it carries itself.**

## No Stacks attribute is attached

`ChartImmersion` is **not** a statement of the Stacks Project: it says nothing about `𝒪(1)` and
nothing about any degree beyond the single one it produces, as the docstring of the condition
records. [Stacks, Tag 01VS] additionally needs
`Stacks.AmpleImmersionReduction.TwistPassage`, which no declaration in this repository proves; see
`StacksFrontier/AlgebraicGeometry/ChartImmersionFinish/Consequences.lean` for exactly what the
present theorem does and does not make unconditional.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.ChartImmersionFinish

/-! ### Finite type as a generating set -/

/-- **`RingHom.FiniteType` is a finite algebra generating set.** -/
theorem exists_finset_adjoin_eq_top {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (h : φ.FiniteType) :
    ∃ t : Finset A, @Algebra.adjoin R A _ _ φ.toAlgebra (↑t : Set A) = ⊤ :=
  let _ := φ.toAlgebra; h.out

/-- **`RingHom.FiniteType` gives a finite set whose subring closure with the image is everything.**
-/
theorem exists_finset_forall_mem_closure {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (h : φ.FiniteType) :
    ∃ t : Finset A, ∀ y : A, y ∈ Subring.closure (Set.range φ ∪ (↑t : Set A)) := by
  let _ := φ.toAlgebra
  obtain ⟨t, ht⟩ := exists_finset_adjoin_eq_top φ h
  refine ⟨t, fun y => ?_⟩
  have := Stacks.ChartDictionary.mem_closure_of_adjoin_eq_top (R := R) (A := A)
    (subset_refl (↑t : Set A)) ht y
  rwa [RingHom.algebraMap_toAlgebra] at this

/-- **The generating statement pushes forward along a surjection.** -/
theorem forall_mem_closure_map {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (φ : R →+* A) (θ : A →+* B) (hθ : Function.Surjective θ) {t : Set A}
    (h : ∀ y : A, y ∈ Subring.closure (Set.range φ ∪ t)) (z : B) :
    z ∈ Subring.closure (Set.range (θ.comp φ) ∪ θ '' t) := by
  obtain ⟨y, rfl⟩ := hθ z
  have hle : Subring.closure (Set.range φ ∪ t) ≤
      (Subring.closure (Set.range (θ.comp φ) ∪ θ '' t)).comap θ := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨r, rfl⟩ | hx)
    · exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)
  exact hle (h y)

/-! ### Restriction along an equality of opens -/

section Restriction

variable {X : Scheme.{u}}

/-- Restricting twice is restricting once. -/
theorem resO_resO {W₁ W₂ W₃ : X.Opens} (h₁₂ : W₂ ≤ W₁) (h₂₃ : W₃ ≤ W₂) (a : Γ(X, W₁)) :
    resO h₂₃ (resO h₁₂ a) = resO (h₂₃.trans h₁₂) a := by
  change (X.presheaf.map (homOfLE h₂₃).op).hom ((X.presheaf.map (homOfLE h₁₂).op).hom a) = _
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  exact congrArg (fun q => (X.presheaf.map q).hom a) (Subsingleton.elim _ _)

/-- Restriction along `le_rfl` is the identity. -/
theorem resO_self {W : X.Opens} (h : W ≤ W) (a : Γ(X, W)) : resO h a = a := by
  change (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 (op W) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

/-- **Restriction along an equality of opens is surjective.** -/
theorem surjective_resO_of_eq {W W' : X.Opens} (h : W = W') (h' : W ≤ W') :
    Function.Surjective fun a : Γ(X, W') => resO h' a := by
  subst h
  exact fun a => ⟨a, resO_self h' a⟩

/-- **Restriction along an inclusion of opens, as a ring homomorphism.** -/
def resOHom {W W' : X.Opens} (h : W' ≤ W) : Γ(X, W) →+* Γ(X, W') :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The ring homomorphism `resOHom h` sends a section `a` to its restriction `resO h a`. -/
@[simp] theorem resOHom_apply {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X, W)) :
    resOHom h a = resO h a := rfl

end Restriction

/-! ### Re-indexing the coordinate ratios -/

section Reindex

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The coordinate ratios of a re-indexed family are the restrictions of the original ones.**
If `s' ∘ φ = s` then the `φ i`-th chart of `s'` is contained in the `i`-th chart of `s` — in fact
equal to it — and the ratio `s'_{φ k} / s'_{φ i}` is the restriction of `s_k / s_i`.

This is what makes the padding of a family along an injection usable: the chart conditions and the
generation hypothesis are stated about the ratios, and the ratios of the padded family at the
padded indices are those of the original family. -/
theorem ratio_reindex {ι ι' : Type*} (s : ι → Γ(L, ⊤)) (s' : ι' → Γ(L, ⊤)) (φ : ι → ι')
    (hφ : ∀ i, s' (φ i) = s i) (i k : ι) :
    ratio s' (φ i) (φ k) = resO (le_of_eq (congrArg (nvOpen L) (hφ i))) (ratio s i k) := by
  have hle := le_of_eq (congrArg (nvOpen L) (hφ i))
  refine (eq_div (s' (φ i)) le_rfl ?_).symm
  have h := resO_ratio_smul s hle k
  have e₁ : resT (nvCover s' (φ i)) (s' (φ i)) = resT (nvCover s' (φ i)) (s i) :=
    congrArg _ (hφ i)
  have e₂ : resT (nvCover s' (φ i)) (s' (φ k)) = resT (nvCover s' (φ i)) (s k) :=
    congrArg _ (hφ k)
  exact (congrArg (fun z => resO hle (ratio s i k) • z) e₁).trans (h.trans e₂.symm)

/-- The chart of a re-indexed family is the chart of the original. -/
theorem nvCover_reindex {ι ι' : Type*} (s : ι → Γ(L, ⊤)) (s' : ι' → Γ(L, ⊤)) (φ : ι → ι')
    (hφ : ∀ i, s' (φ i) = s i) (i : ι) : nvCover s' (φ i) = nvCover s i :=
  congrArg (nvOpen L) (hφ i)

end Reindex

/-! ### Step 4 on a sub-family of charts -/

section Subcover

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

open Stacks.SectionsToProjectiveSpace in
/-- **Step 4 of the proof of [Stacks, Tag 01VS], on a sub-family of the charts.** This is
`Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart` with the chartwise
hypothesis asked for only at the indices of a subset `J` whose charts already cover `X`.

The generalisation is needed and not cosmetic. The family that the degree equalisation produces
carries, besides the covering sections, the *numerators* of the algebra generators, and nothing
says that the nonvanishing open of a numerator is affine or maps into an affine open of the base.
The proof of the ungeneralised statement only ever uses the chartwise hypothesis at an index whose
chart contains the given point, so the restriction costs nothing: being an immersion is Zariski
local on the target and the charts indexed by `J` already cover. -/
theorem isImmersion_of_isImmersion_standardChart_subcover {S : Scheme.{u}}
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    {J : Type*} (ψ : J → Fin (n + 1)) (hJ : ∀ x : X, ∃ j, x ∈ nvCover s (ψ j))
    (hcl : ∀ j : J, ∃ g : (nvCover s (ψ j)).toScheme ⟶
        (projectiveSpaceOver.standardChart n S (ψ j)).toScheme,
      IsImmersion g ∧
        g ≫ (projectiveSpaceOver.standardChart n S (ψ j)).ι = (nvCover s (ψ j)).ι ≫ p) :
    IsImmersion p := by
  have hop : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun q i _ hqi => MorphismProperty.HasOfPostcompProperty.of_postcomp
      (W := @IsImmersion) (W' := (⊤ : MorphismProperty Scheme)) q i trivial hqi⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) p
  intro x
  obtain ⟨j, hi⟩ := hJ x
  have hpre : p ⁻¹ᵁ projectiveSpaceOver.standardChart n S (ψ j) = nvCover s (ψ j) :=
    Stacks.AmpleImmersionReduction.preimage_standardChart s hs p hchart (ψ j)
  refine ⟨projectiveSpaceOver.standardChart n S (ψ j), ?_, ?_⟩
  · exact show x ∈ p ⁻¹ᵁ projectiveSpaceOver.standardChart n S (ψ j) from hpre ▸ hi
  · rw [hpre]
    obtain ⟨g, hgcl, hgfac⟩ := hcl j
    rw [← hgfac]
    have := hgcl
    infer_instance

open Stacks.SectionsToProjectiveSpace in
/-- **The chart route of [Stacks, Tag 01VS] through step 4, on a sub-family of the charts.** This
is `Stacks.ChartDictionary.isImmersion_of_closure` with affineness of the chart, the affine open of
the base and the generation hypothesis demanded only at the indices of a covering subset `J`. -/
theorem isImmersion_of_closure_subcover (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    {S : Scheme.{u}} {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (hchart : ∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    {J : Type*} (ψ : J → Fin (n + 1)) (hJ : ∀ x : X, ∃ j, x ∈ nvCover s (ψ j))
    (haff : ∀ j : J, IsAffineOpen (nvCover s (ψ j)))
    (V : J → S.Opens) (hV : ∀ j : J, IsAffineOpen (V j))
    (hle : ∀ j : J, nvCover s (ψ j) ≤ f ⁻¹ᵁ V j)
    (hgen : ∀ (j : J) (y : Γ(X, nvCover s (ψ j))), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE (V j) (nvCover s (ψ j)) (hle j)).hom r) ∪
        Set.range (ratio s (ψ j)))) :
    IsImmersion p :=
  isImmersion_of_isImmersion_standardChart_subcover s hs p hchart ψ hJ
    fun j => Stacks.ChartDictionary.exists_isImmersion_standardChart s p hpf (ψ j) (hchart (ψ j))
      (hV j) (hle j) (haff j) (hgen j)

end Subcover

/-! ### The generation hypothesis on the chart of the equalised family -/

section Transport

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- **The generation hypothesis transports along an equality of charts.** The algebra generators
of [Stacks, Tag 01T2] are produced on the chart `X_{a i}` of the *covering* family, while the
generation hypothesis that step 4 consumes is about the chart of the *equalised* family. The two
opens are equal, and this moves the statement from one to the other, enlarging the generating set
to any set containing the restrictions — which is how the generators become coordinate ratios. -/
theorem forall_mem_closure_chart {U W : X.Opens} (hWU : W = U) {V : S.Opens}
    (hleU : U ≤ f ⁻¹ᵁ V) (hleW : W ≤ f ⁻¹ᵁ V) {t : Set Γ(X, U)}
    (ht : ∀ y : Γ(X, U), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE V U hleU).hom r) ∪ t))
    {T : Set Γ(X, W)} (hT : resO hWU.le '' t ⊆ T) (y : Γ(X, W)) :
    y ∈ Subring.closure (Set.range (fun r => (f.appLE V W hleW).hom r) ∪ T) := by
  have hcomp : (resOHom hWU.le).comp (f.appLE V U hleU).hom = (f.appLE V W hleW).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_map f hleU (homOfLE hWU.le).op)
  have h := forall_mem_closure_map (f.appLE V U hleU).hom (resOHom hWU.le)
    (surjective_resO_of_eq hWU hWU.le) ht y
  rw [hcomp] at h
  exact Subring.closure_mono (Set.union_subset_union_right _ hT) h

end Transport

/-! ### Steps 2 and 4 of Stacks Tag 01VS -/

section Main

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X S : Scheme.{u}}

/-- **Steps 2 and 4 of the proof of [Stacks, Tag 01VS]**, i.e.
`Stacks.AmpleImmersionReduction.ChartImmersion f L`, with no hypothesis beyond the ampleness and
finite type that the condition carries itself. For an ample `L` on a scheme locally of finite type
over `S`, some positive power of `L` has a generating family of global sections whose pinned
morphism to projective space over `S` is an immersion.

The family is the equalised one of `Stacks.ChartDegreeEqualisation.exists_family_ratio_eq`, run on
the cover of `Stacks.AmpleChartsOverBase.exists_generating_family_finiteType_of_isAmple` and on the
algebra generators that cover's `RingHom.FiniteType` clause supplies — so each generator is a
coordinate ratio of the family — and then re-indexed to `Fin (M + 1)` and padded with the zero
section. On each chart of the covering part of that family the ratios together with the sections
of `𝒪_S(Vᵢ)` therefore generate the sections of the chart, which is exactly the hypothesis
`Stacks.ChartDictionary.isImmersion_of_closure` consumes; the numerator part of the family carries
no such hypothesis and none is needed, which is what
`Stacks.ChartImmersionFinish.isImmersion_of_closure_subcover` is for.

**This is not [Stacks, Tag 01VS]** and no attribute is attached: it says nothing about `𝒪(1)` and
nothing about any degree beyond the single one it produces. -/
theorem chartImmersion (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.AmpleImmersionReduction.ChartImmersion f L := by
  classical
  intro hL hft
  obtain ⟨N₀, m, s₀, hN₀, hgen₀, haff₀, hover⟩ :=
    Stacks.AmpleChartsOverBase.exists_generating_family_finiteType_of_isAmple L hL f
  choose V hVaff hle₀ hFT using hover
  choose t ht using fun i => exists_finset_forall_mem_closure _ (hFT i)
  choose a ha using fun i =>
    Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L N₀ (s₀ i)
  have hcov₀ : ∀ {U : Fin (m + 1) → X.Opens}, (∀ i, U i = nvCover s₀ i) → ∀ x : X, ∃ i, x ∈ U i :=
    fun hU x => (exists_mem_nvCover_of_generatesStalks s₀ hgen₀ x).imp fun i hi => (hU i).ge hi
  have hUa : ∀ i, Stacks.AmpleFiniteAvoidance.nvOpen L (a i) = nvCover s₀ i := by
    intro i
    refine TopologicalSpace.Opens.ext ?_
    rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen, ha i,
      Stacks.NonvanishingOpen.coe_nonvanishingOpen]
  obtain ⟨N₁, s₁, hnv, hN₁, hgen₁, hr⟩ :=
    Stacks.ChartDegreeEqualisation.exists_family_ratio_eq L hL hN₀ a
      (hcov₀ hUa)
      (fun i (j : {x : Γ(X, nvCover s₀ i) // x ∈ t i}) => resO (hUa i).le (j : Γ(X, nvCover s₀ i)))
  obtain ⟨M, ⟨eqv⟩⟩ : ∃ M : ℕ,
      Nonempty ((Fin (m + 1) ⊕ (Σ i, {x : Γ(X, nvCover s₀ i) // x ∈ t i})) ≃ Fin M) :=
    ⟨_, ⟨Finite.equivFin _⟩⟩
  obtain ⟨s₂, hφ⟩ : ∃ s₂ : Fin (M + 1) → Γ(tensorPowModule X L (N₁ : ℤ), ⊤),
      ∀ q, s₂ (eqv q).castSucc = s₁ q :=
    ⟨Fin.lastCases 0 fun k => s₁ (eqv.symm k), fun q => by
      simp only [Fin.lastCases_castSucc, Equiv.symm_apply_apply]⟩
  have hW : ∀ i, nvCover s₂ (eqv (Sum.inl i)).castSucc = nvCover s₀ i := fun i =>
    (nvCover_reindex s₁ s₂ (fun q => (eqv q).castSucc) hφ (Sum.inl i)).trans
      ((hnv i).trans (hUa i))
  have hcov₂ := hcov₀ hW
  have hle₂ : ∀ i, nvCover s₂ (eqv (Sum.inl i)).castSucc ≤ f ⁻¹ᵁ V i := fun i =>
    (hW i).le.trans (hle₀ i)
  have hgen₂ : GeneratesStalks s₂ :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem s₂ fun x =>
      (hcov₂ x).elim fun i hi => ⟨_, hi⟩
  refine ⟨(N₁ : ℤ), M, s₂, by exact_mod_cast hN₁, hgen₂, fun p hpf hchart => ?_⟩
  refine isImmersion_of_closure_subcover s₂ hgen₂ p hpf hchart
    (fun i => (eqv (Sum.inl i)).castSucc) hcov₂ (fun i => by rw [hW i]; exact haff₀ i) V hVaff
    hle₂ ?_
  intro i y
  refine forall_mem_closure_chart (hW i) (hle₀ i) (hle₂ i) (ht i) ?_ y
  rintro z ⟨w, hw, rfl⟩
  refine ⟨(eqv (Sum.inr (Sigma.mk i ⟨w, hw⟩))).castSucc, ?_⟩
  rw [ratio_reindex s₁ s₂ (fun q => (eqv q).castSucc) hφ (Sum.inl i)
    (Sum.inr (Sigma.mk i ⟨w, hw⟩)), hr i ⟨w, hw⟩]
  simp only [resO_resO]

end Main

end Stacks.ChartImmersionFinish

end
