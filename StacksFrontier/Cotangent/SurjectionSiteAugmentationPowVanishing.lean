module

public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationGraded

/-!
# The footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`

Let `A → B` be a ring map, let `κ` be a cardinal and let `S = C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the polynomial site. Write

`H_i(C_{B/A}, ℱ) = (L_i colim)(ℱ)`

for the homology of the site with coefficients in a presheaf `ℱ` of `B`-modules [Stacks, Tag
08PF], and let `𝒦ⁿ = CommAlgCat.smallPolynomialAugmentationIdealPow A B κ n` be the `n`-th power
of the augmentation ideal of `Ō = 𝒪 ⊗_A B̲`, from
`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration`.

This file proves the footnote of [Stacks, Tag 08RF]:

`H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`,

from the two halves of the source's argument. The dévissage half is proved here; the
pro-nilpotence half is an explicit hypothesis of the declarations below, named `hpro`.

## The shape of the argument

The vanishing is **not** a formal consequence of the vanishing of the graded pieces: a filtered
complex all of whose graded pieces are acyclic can have nonzero cohomology (the counterexample
is recorded in the module docstring of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration`). The source splits the proof in
two.

* **Dévissage.** For `i < m` the inclusion `𝒦^{m+1} ⊆ 𝒦^m` induces a *surjection*
  `H_i(C_{B/A}, 𝒦^{m+1}) → H_i(C_{B/A}, 𝒦^m)`. This is the long exact sequence of
  `0 → 𝒦^{m+1} → 𝒦^m → 𝒦^m/𝒦^{m+1} → 0` together with the vanishing of the graded piece,
  `H_i(C_{B/A}, 𝒦^m/𝒦^{m+1}) = 0` for `i < m`. Composing, `H_i(C_{B/A}, 𝒦^{n+c}) →
  H_i(C_{B/A}, 𝒦ⁿ)` is surjective for every `c`, as soon as `i < n`. This is
  `CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap`.

  The source instead states the dévissage as `H_i(C_{B/A}, 𝒦ⁿ/𝒦^{n+c}) = 0` for `i < n` and
  reads the conclusion off the long exact sequence of `0 → 𝒦^{n+c} → 𝒦ⁿ → 𝒦ⁿ/𝒦^{n+c} → 0`.
  The surjectivity statement above is the same induction with the quotient presheaves
  eliminated: the one long exact sequence it uses is the one the quotient presheaves are built
  out of, and no presheaf `𝒦ⁿ/𝒦ᵐ` has to be constructed.

* **Pro-nilpotence.** For every `k` there is a `c` such that for every `n` the map
  `H_i(C_{B/A}, 𝒦^{n+c}) → H_i(C_{B/A}, 𝒦ⁿ)` is *zero* for every `i < k`. This is the hypothesis
  `hpro` below. The source proves it from [Stacks, Tag 08RE] through the change of rings
  spectral sequence of [Stacks, Tag 068F] and the truncation argument of [Stacks, Tag 08Q2],
  after moving to the derived tensor product `𝒦ⁿ ⊗^L_𝒪 B̲` by [Stacks, Tag 08QJ], with
  `c = k²`.

The dévissage's own input, the vanishing `H_i(C_{B/A}, 𝒦ᵏ/𝒦ᵏ⁺¹) = 0` for `i < k` of the graded
pieces, is carried here as the hypothesis `hgr` because this file is below the symmetric powers
in the import order.  It is **not** an open obligation: for a surjective `A → B` it is proved,
from the identification of the graded pieces with the symmetric powers and the vanishing clause
of [Stacks, Tag 08RF], as
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationGraded_of_surjective` in
`StacksFrontier.Cotangent.SurjectionSiteFootnoteVanishing`, where the footnote vanishing is
restated on `hpro` alone.

Combining the two is immediate: for `i < n`, taking `k = n` in the pro-nilpotence hypothesis
gives a `c` for which `H_i(C_{B/A}, 𝒦^{n+c}) → H_i(C_{B/A}, 𝒦ⁿ)` is both an epimorphism, by the
dévissage, and zero. An epimorphism which is zero has a zero target. That is
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow`.

## Main definitions

* `CommAlgCat.smallPolynomialAugmentationIdealPowMap`: the inclusion `𝒦ᵐ ⊆ 𝒦ⁿ` for `n ≤ m`, as
  a morphism of presheaves of `B`-modules.
* `CommAlgCat.smallPolynomialAugmentationGradedShortComplex`: the sequence
  `0 → 𝒦^{n+1} → 𝒦ⁿ → 𝒦ⁿ/𝒦^{n+1} → 0` of presheaves of `B`-modules.

## Main results

* `CommAlgCat.shortExact_smallPolynomialAugmentationGradedShortComplex`: that sequence is short
  exact.
* `CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowIncl` and
  `CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap`: the dévissage.
* `CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow`: the footnote
  vanishing, from the dévissage and the pro-nilpotence hypothesis.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks

/-! ### Short exactness in a category of diagrams is objectwise -/

section Evaluation

variable {J : Type*} [Category J] {D : Type*} [Category D] [Abelian D]

/-- A short complex of diagrams is short exact as soon as all its evaluations are: the homology
of a short complex of diagrams is computed objectwise and a diagram is zero as soon as all its
values are, while a natural transformation is a monomorphism, respectively an epimorphism, as
soon as all its components are. -/
private theorem shortExact_of_evaluation' (S : ShortComplex (J ⥤ D))
    (h : ∀ j : J, (S.map ((evaluation J D).obj j)).ShortExact) : S.ShortExact where
  exact := by
    rw [S.exact_iff_isZero_homology]
    refine Functor.isZero _ fun j => ?_
    exact ((S.map ((evaluation J D).obj j)).exact_iff_isZero_homology.mp (h j).exact).of_iso
      (S.mapHomologyIso ((evaluation J D).obj j)).symm
  mono_f := have : ∀ j, Mono (S.f.app j) := fun j => (h j).mono_f; NatTrans.mono_of_mono_app S.f
  epi_g := have : ∀ j, Epi (S.g.app j) := fun j => (h j).epi_g; NatTrans.epi_of_epi_app S.g

end Evaluation

end Stacks

namespace CommAlgCat

section Vanishing

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` -/

/-- **The inclusion `𝒦ᵐ ⊆ 𝒦ⁿ`** for `n ≤ m`, as a morphism of presheaves of `B`-modules on the
small model of the polynomial site. -/
def smallPolynomialAugmentationIdealPowMap {n m : ℕ} (h : n ≤ m) :
    smallPolynomialAugmentationIdealPow A B κ m ⟶ smallPolynomialAugmentationIdealPow A B κ n :=
  Stacks.submoduleFunctorIncl _ _ _ _ _
    (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ h)

/-- The inclusion of `𝒦ⁿ` into itself is the identity. -/
@[simp]
lemma smallPolynomialAugmentationIdealPowMap_self (n : ℕ) (h : n ≤ n) :
    smallPolynomialAugmentationIdealPowMap A B κ h = 𝟙 _ :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

/-- The inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` compose. -/
@[simp]
lemma smallPolynomialAugmentationIdealPowMap_comp {n m p : ℕ} (h : n ≤ m) (h' : m ≤ p) :
    smallPolynomialAugmentationIdealPowMap A B κ h' ≫
        smallPolynomialAugmentationIdealPowMap A B κ h =
      smallPolynomialAugmentationIdealPowMap A B κ (h.trans h') :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

/-- The inclusion `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ` of the filtration is the case `m = n + 1`. -/
lemma smallPolynomialAugmentationIdealPowMap_succ (n : ℕ) :
    smallPolynomialAugmentationIdealPowMap A B κ (Nat.le_succ n) =
      smallPolynomialAugmentationIdealPowIncl A B κ n :=
  rfl

/-! ### The short exact sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0` -/

/-- The composite `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹` vanishes: a section of `𝒦ⁿ⁺¹` is by definition killed
in the quotient. -/
lemma smallPolynomialAugmentationIdealPowIncl_comp_gradedπ (n : ℕ) :
    smallPolynomialAugmentationIdealPowIncl A B κ n ≫
      smallPolynomialAugmentationGradedπ A B κ n = 0 := by
  refine NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change Submodule.Quotient.mk (Submodule.inclusion
    (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ (Nat.le_succ n) X) x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact x.2

/-- **The sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0`** of presheaves of `B`-modules on the small
model of the polynomial site, as a short complex. It is short exact by
`CommAlgCat.shortExact_smallPolynomialAugmentationGradedShortComplex`. -/
def smallPolynomialAugmentationGradedShortComplex (n : ℕ) :
    ShortComplex ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) :=
  ShortComplex.mk (smallPolynomialAugmentationIdealPowIncl A B κ n)
    (smallPolynomialAugmentationGradedπ A B κ n)
    (smallPolynomialAugmentationIdealPowIncl_comp_gradedπ A B κ n)

/-- **The sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0` is short exact over every object of the
site**: the inclusion of submodules is injective with image the submodule the quotient is taken
by, and the projection onto a quotient is surjective with that submodule as its kernel. -/
theorem shortExact_smallPolynomialAugmentationGradedShortComplex_map_evaluation (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ((smallPolynomialAugmentationGradedShortComplex A B κ n).map
      ((evaluation ((smallBoundedPolynomialSite A B κ)ᵒᵖ)
        (ModuleCat.{u} (B : Type u))).obj X)).ShortExact :=
  have hle := smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ (Nat.le_succ n) X
  { mono_f := (ModuleCat.mono_iff_injective _).2 (Submodule.inclusion_injective hle)
    epi_g := (ModuleCat.epi_iff_surjective _).2
      (surjective_smallPolynomialAugmentationGradedπ A B κ n X)
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      change LinearMap.range ((smallPolynomialAugmentationIdealPowIncl A B κ n).app X).hom =
        LinearMap.ker ((smallPolynomialAugmentationGradedπ A B κ n).app X).hom
      rw [ker_smallPolynomialAugmentationGradedπ A B κ n X]
      exact Submodule.range_inclusion _ _ hle }

/-- **The sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0` is short exact.** Short exactness of a
sequence of presheaves of modules is objectwise, and over each object of the site it is
`CommAlgCat.shortExact_smallPolynomialAugmentationGradedShortComplex_map_evaluation`. -/
theorem shortExact_smallPolynomialAugmentationGradedShortComplex (n : ℕ) :
    (smallPolynomialAugmentationGradedShortComplex A B κ n).ShortExact :=
  Stacks.shortExact_of_evaluation' _
    (shortExact_smallPolynomialAugmentationGradedShortComplex_map_evaluation A B κ n)

/-! ### The dévissage: the transition maps are surjective on homology -/

/-- **One step of the dévissage.** If the graded piece `𝒦ⁿ/𝒦ⁿ⁺¹` has vanishing `H_i`, then the
inclusion `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ` induces a surjection on `H_i(C_{B/A}, -)`: the long exact sequence of
`0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → 𝒦ⁿ/𝒦ⁿ⁺¹ → 0` is exact at `H_i(C_{B/A}, 𝒦ⁿ)`, and the term after it
vanishes. -/
theorem epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowIncl (n i : ℕ)
    (hgr : IsZero (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationGraded A B κ n))) :
    Epi (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived i).map
      (smallPolynomialAugmentationIdealPowIncl A B κ n)) :=
  ((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
      ModuleCat.{u} (B : Type u)).leftDerived_exact
    (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ n) i).epi_f
      (hgr.eq_zero_of_tgt _)

/-- **The dévissage.** Suppose the graded pieces vanish in low degree: `H_i(C_{B/A},
𝒦ᵏ/𝒦ᵏ⁺¹) = 0` for `i < k`. Then for `i < n ≤ m` the inclusion `𝒦ᵐ ⊆ 𝒦ⁿ` induces a surjection
`H_i(C_{B/A}, 𝒦ᵐ) → H_i(C_{B/A}, 𝒦ⁿ)`.

This is the source's dévissage step of [Stacks, Tag 08RF], with the quotient presheaves
`𝒦ⁿ/𝒦ᵐ` eliminated: it is an induction on `m` along the one long exact sequence those
presheaves are assembled from, each step being
`CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowIncl` applied with
`i < n ≤ m`. -/
theorem epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap
    (hgr : ∀ k i : ℕ, i < k → IsZero (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationGraded A B κ k)))
    (i n m : ℕ) (hi : i < n) (h : n ≤ m) :
    Epi (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived i).map
      (smallPolynomialAugmentationIdealPowMap A B κ h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [smallPolynomialAugmentationIdealPowMap_self, CategoryTheory.Functor.map_id]
    infer_instance
  | succ m hnm ih =>
    rw [← smallPolynomialAugmentationIdealPowMap_comp A B κ hnm (Nat.le_succ m),
      CategoryTheory.Functor.map_comp, smallPolynomialAugmentationIdealPowMap_succ]
    exact epi_comp' (epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowIncl A B κ m i
      (hgr m i (hi.trans_le hnm))) ih

/-! ### The pro-nilpotence of the filtration on homology -/

/-- **The pro-nilpotence of the augmentation filtration on homology**: for every `k` there is a
`c` such that for every `n` the inclusion `𝒦^{n+c} ⊆ 𝒦ⁿ` induces the zero map on
`H_i(C_{B/A}, -)` for every `i < k`.

This is the first claim in the proof of [Stacks, Tag 08RF] — "given `k ≥ 0` set `c = k²`; we
claim that `H_i(C_{B/A}, 𝒦^{n+c}) → H_i(C_{B/A}, 𝒦ⁿ)` is zero for `i < k` and all `n ≥ 0`" —
and it is the one step of the proof of the footnote vanishing that this file does not carry
out.

### The route, as far as it has been checked

Write `𝒪` for the structure presheaf, `Ō = 𝒪 ⊗_A B̲` and `B̲` for the constant presheaf, so
that `𝒦ⁿ` is a presheaf of `Ō`-modules and the coefficients run `𝒪 → Ō → B̲`.  Four of the
five inputs are proved, in the shape in which each is used:

* [Stacks, Tag 08QJ] at `𝒦ⁿ` is
  `CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow`
  (`StacksFrontier.Cotangent.SurjectionSiteAugmentationStructureModule`), with nothing assumed.
  Composed with `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_iff` and
  `Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff`, it says: for a
  K-projective resolution `𝒬_•` of `𝒦ⁿ` over `𝒪`, `Lπ_!` of the *degreewise* unit
  `𝒬_• ⟶ 𝒬_• ⊗_𝒪 B̲` is invertible.  So `Lπ_!(𝒦ⁿ)` may be computed from the honest complex
  `𝒬_• ⊗_𝒪 B̲`.
* [Stacks, Tag 08Q2] is `main_covariant`, and it applies verbatim in
  `PresheafOfModules 𝒪` and in `PresheafOfModules Ō` under
  `attribute [local instance] HasDerivedCategory.standard`.
* [Stacks, Tag 08RE] is `MvPolynomial.tor_map_augmentationIdeal_pow_succ_eq_zero`, which is
  the translated form at a general augmentation, so it applies to `𝒦ⁿ(U) ⊆ Ō(U)` on the nose.
  Note it kills the map on `Tor_b^{Ō(U)}(B, -)` in **every** degree `b`, not only `b < k`; so
  `k` single steps suffice in `main_covariant` and `c = k` works, the source's `c = k²` being
  a non-optimal bound.
* the objectwise input is `PresheafOfModules.projective_obj`
  (`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ProjectiveObjectwise`): a
  projective presheaf of modules has projective, hence flat, modules of sections, so the
  sections of `𝒬_•` form a flat resolution and the homology of `(𝒬_• ⊗_𝒪 B̲)(U)` is
  `Tor_*^{𝒪(U)}(𝒦ⁿ(U), B)`;
* the passage from the abelian reading of the homology of the site, which is the one Tag 08QJ
  is stated in, to the `B`-module reading used here is
  `Stacks.ChaoticSite.leftDerivedColim_map_eq_zero_of_forget`.

What is **not** available is the change of rings itself.  [Stacks, Tag 068F],
`exists_tor_change_of_rings_spectral_sequence`, cannot supply it, for two independent reasons.
Its spectral sequence is produced inside an existential whose abutment is a `Prop` with the
filtration quantified away, so no map of spectral sequences and no map of abutments is
available, and a statement that a map "is zero on `E₂`" cannot even be formed.  And its `E₂`
is `Tor_n^{Ō}(Tor_m^{𝒪}(B, Ō), 𝒦ⁿ)`, which groups the two changes of rings the other way
round from the source: Tag 08RE needs its first `Tor` argument to be killed by the
augmentation ideal (see the docstring of
`MvPolynomial.tor_zero_map_variableIdeal_pow_succ_eq_zero_of_smul_eq_zero`), and
`Tor_0^{𝒪}(B, Ō) = B ⊗_A B` is not, since `X_e - g_e` acts on it as `1 ⊗ g_e - g_e ⊗ 1`.  The
source's grouping, `Tor_a^{𝒪}(Ō, Tor_b^{Ō}(B, 𝒦ⁿ))`, is the one where Tag 08RE applies.

So the remaining obligation is the functorial base change for the tower `𝒪 → Ō → B̲`: an
identification of `𝒦ⁿ ⊗^L_𝒪 B̲` with `Λ_• ⊗^L_B (𝒦ⁿ ⊗^L_Ō B̲)`, where
`Λ_• = B̲ ⊗^L_𝒪 Ō`, compatible with the inclusions `𝒦^{n+1} ⊆ 𝒦ⁿ`.  Granting it, the proof
is: resolve `𝒦ⁿ` over `Ō`, apply `main_covariant` to `k` single steps of
`𝒦^{n+k} → ⋯ → 𝒦ⁿ` with Tag 08RE discharging every `H^{-j}`, push the resulting
factorisation through `τ^{≤ -k}` along `Λ_• ⊗_B -` and `Lπ_!`, both of which carry complexes
concentrated in degrees `≤ -k` to complexes concentrated in degrees `≤ -k`, and transport back
along Tag 08QJ.  The obstruction to writing that down is not the spectral sequence but the two
`Ō`-module structures on `Ō ⊗^L_𝒪 Ō`, which [Stacks, Tag 08YT] records as genuinely different;
the comparison has to keep them apart, and the intermediate bicomplexes of the usual proof
carry only the `𝒪`-structure.

### That obligation is not the source's, and the source's is cheaper

The paragraph above, and the counterexample of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationBaseChange`, are both about an identification
of **presheaves** on the site.  The source states no such identification.  Its second claim is
local, and it says so: *"Proof of the second claim.  The statement is local, hence we may work
over an object `U = (P → B)` as above.  We have to show the maps
`Tor_i^P(B, K^{n+k}) → Tor_i^P(B, K^n)` are zero for `i < k`."*  What is being proved there is
that a map induces zero on **cohomology sheaves**, and a map of presheaves is zero exactly when
it is zero over every object; so everything after that sentence happens over honest commutative
rings, where the two `Ō`-module structures on `Ō ⊗^L_𝒪 Ō` and the whole `(★)` question do not
arise.  Consistently with this, the counterexample refuting `(★)` is at `A = k → B = k[S]`,
which is **not surjective**, at the object whose structure map is the identity; under the
remark's own surjectivity hypothesis the source puts every object in the normal form
`P = A[E]` with every variable mapping to `0`, and that object is then unavailable.

So the obligation is the source's local claim.  Over an object in that normal form,
`𝒪(U) = A[E]`, `Ō(U) = B[E]`, `B̲(U) = B` and `𝒦ⁿ(U) = 𝔪ⁿ ⊗_A B` with
`𝔪 = (X_e; e ∈ E) ⊆ A[E]`, and the following route needs no change of rings at all.  Note that
the normal form is reached by an isomorphism of *objects of the site*: for a surjective `A → B`
every point `g : E → B` lifts to a point `ã : E → A`, and translating the variables by `ã` is
an `A`-algebra automorphism of `A[E]` carrying `(A[E], g)` to `(A[E], 0)`; this is the one place
surjectivity is used in the second claim.  The following route needs no change of rings at all:

* [Stacks, Tag 08RE] is already proved in a form that applies **over `A[E]`**, not over `B[E]`:
  `MvPolynomial.tor_map_augmentationIdeal_pow_succ_eq_zero` takes the base ring, the point and
  the module as parameters, so at base ring `A`, point `0` and module `B` — which `𝔪`
  annihilates, since `A[E] → B` kills every variable — it reads
  `Tor_i^{A[E]}(B, 𝔪^{n+1}) → Tor_i^{A[E]}(B, 𝔪ⁿ) = 0` for **every** `i`.
* Fix a projective `A[E]`-resolution `Q_•` of `B` and set `W_n = Q_• ⊗_{A[E]} 𝔪ⁿ`.  Then
  `Q_• ⊗_{A[E]} 𝒦ⁿ(U) = W_n ⊗_A B`, and each `W_n` is a complex of free `A`-modules because
  `𝔪ⁿ` is one (`MvPolynomial.free_variableIdeal_pow`).
* `main_covariant` in `D(ModuleCat A)` then makes the `k`-fold composite `W_{n+k} → W_n` factor
  through `τ^{≤ -k}W_n`, and `(-) ⊗^L_A B` carries degrees `≤ -k` to degrees `≤ -k`.  Hence
  `Tor_i^{𝒪(U)}(B, 𝒦^{n+k}(U)) → Tor_i^{𝒪(U)}(B, 𝒦ⁿ(U))` is zero for `i < k`, which is the
  source's second claim with `c = k`.

The source's first step then runs as it stands — Tag 08QJ at `𝒦ⁿ`, `main_covariant` again in
the presheaves, and `Lπ_!` applied to a complex in degrees `≤ -k` — and yields `hpro` with
`c = k²`.

### What of that route is proved

The two `t`-exactness statements the route runs on are proved, in a generality that makes them
usable on both of its two applications of `main_covariant`:

* the right `t`-exactness of `(-) ⊗^L_A B` is `Stacks.homologyMap_map_chainComp_eq_zero`
  (`StacksFrontier.Algebra.Homology.DerivedCategory.ChainCompFactorisation`).  No derived tensor
  functor is involved: Tag 08Q2's factorisation is upgraded there to a *homotopy* between
  morphisms of complexes, which it is as soon as the source of the chain is K-projective, and
  an additive functor applied degreewise carries a homotopy to a homotopy.  So the statement
  proved is that for **any** additive functor `F` the composite of the chain induces the zero
  map on `H^i(F(-))` for `i > -k`, which covers `(-) ⊗_A B` on the complexes of frees `W_•`
  and `colim` on complexes of projective presheaves alike;
* the right `t`-exactness of `Lπ_!` is `Stacks.CategoryHomology.isLE_totalDerivedColimit_obj`
  (`StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedRightTExact`), a specialisation of
  `Stacks.CategoryHomology.isLE_leftDerived_obj`: *every* total left derived functor of an
  additive functor out of a category with enough projectives is right `t`-exact, because an
  object of `D^{≤ a}` is resolved by projectives still concentrated in degrees `≤ a`
  ([Stacks, Tag 0646](3)) and there the derived functor is the underived one applied
  degreewise.

So is the **normal form** the second claim is read in, in both its halves
(`StacksFrontier.Cotangent.SurjectionSiteNormalForm`):

* `CommAlgCat.zeroPointIso` is the normal form in the site — for a surjective `A → B` every
  object `(S, g)` is isomorphic to `(S, 0)`, by translating the variables by a lift
  `ã : S → A` of `g`, which `MvPolynomial.translateEquiv` provides as an `A`-algebra
  automorphism of `A[S]`.  `CommAlgCat.zeroPointSiteIso` reads it in the category presheaves are
  taken on, where, with `Stacks.SheafOfModules.app_eq_zero_of_iso`, it reduces an objectwise
  vanishing statement about a morphism of presheaves to the objects with point `0`.  **This is
  the one place surjectivity is used in the second claim.**
* `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm` is the normal form on sections,
  `𝒦ⁿ(U) ≅ B ⊗_A 𝔪ⁿ` over an object whose point is `0`, pinned down in coordinates by
  `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul` and compatible with the
  inclusions `𝒦ᵐ ⊆ 𝒦ⁿ`.

And so are the two restatements that put Tag 08RE and Tag 08QJ in the
shapes the two claims consume:

* `MvPolynomial.tor'_map_augmentationIdeal_pow_eq_zero_of_lt`
  (`StacksFrontier.RingTheory.AugmentationIdealPowTorFirstVariable`) is Tag 08RE with the **first**
  variable resolved.  The library's Tag 08RE is stated for `CategoryTheory.Tor`, which derives the
  second variable, hence resolves the ideal; the local complexes `W_m = Q_• ⊗_{A[E]} 𝔪ᵐ` resolve
  the first, so their homology is `CategoryTheory.Tor'`.  The bridge is the balancing
  `Tor_iso_Tor'` of [Stacks, Tag 00M1], whose naturality in the second variable carries the
  vanishing of a map across.
* `Stacks.ChaoticSite.AbelianValued.homologyTotalDerivedColimitSingleNatIso`
  (`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.AbelianDerivedColimitHomology`) is
  `H^{-i}(Lπ_!(ℱ[0])) ≅ H_i(C_{B/A}, ℱ)` at abelian coefficients, as an isomorphism of
  *functors*, with `Stacks.ChaoticSite.AbelianValued.leftDerivedColim_map_eq_zero` the vanishing
  implication read off its naturality.  The first claim needs it because it computes the homology
  of the site through `Lπ_!`, where Tag 08QJ — the only route from `𝒦ⁿ` to `𝒦ⁿ ⊗^L_𝒪 B̲` — is
  stated, and at abelian coefficients, which
  `Stacks.ChaoticSite.leftDerivedColim_map_eq_zero_of_forget` is what brings the `B`-module
  reading of `hpro` down to.

Finally the **interchange** `(Q_• ⊗_{A[E]} 𝔪ⁿ) ⊗_A B ≅ Q_• ⊗_{A[E]} (𝔪ⁿ ⊗_A B)` is
`ModuleCat.tensorRightAssoc` (`StacksFrontier.RingTheory.TensorInterchange`), a natural isomorphism
of functors `ModuleCat A[E] ⥤ ModuleCat A` — hence pushable along
`Functor.mapHomologicalComplex`, which is
`ModuleCat.tensorRightAssocMapHomologicalComplex` — together with its compatibility with the
inclusions `𝔪ᵐ ⊆ 𝔪ⁿ`,
`ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc_mapHomologicalComplex`.  At one
module it is `TensorProduct.AlgebraTensorModule.assoc` at `R := A`, `A := A[E]`.

### What is left

* the local claim itself: `W_m` is a complex of `A`-projectives, hence K-projective
  (`MvPolynomial.free_variableIdeal_pow`, `CochainComplex.isKProjective_of_projective`); its
  transition maps are zero on homology in every degree by the `Tor'` form of Tag 08RE, read
  through `CategoryTheory.ProjectiveResolution.leftDerived_app_eq`, which identifies the homology
  map of `(NatTrans.mapHomologicalComplex α _).app Q_•` with a component of
  `NatTrans.leftDerived α`; `Stacks.homologyMap_map_chainComp_eq_zero` at `F = (-) ⊗_A B` then
  gives the claim, the interchange identifying `F(W_m)` with `Q_• ⊗_{A[E]} 𝒦ᵐ(U)`.

  One seam to be aware of in that last identification.  The interchange's second functor is
  `N ↦ N ⊗_{A[E]} (𝔪ᵐ ⊗_A B)`, where `𝔪ᵐ ⊗_A B` carries the `A[E]`-action of its **left**
  factor — which is the action `𝒦ᵐ(U)` has, so that orientation is the one the identification
  needs.  `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm` is stated in the other
  orientation, `𝒦ᵐ(U) ≅ B ⊗_A 𝔪ᵐ`, because there the `B`-action is the one of the left factor
  and the statement can be a `B`-linear equivalence, which `𝔪ᵐ ⊗_A B` cannot be without a
  `Module B (𝔪ᵐ ⊗_A B)` that Mathlib does not provide.  The bridge is `TensorProduct.comm`, and
  what makes it a short step is that the normal form is pinned in coordinates by
  `CommAlgCat.smallPolynomialAugmentationIdealPowNormalForm_symm_tmul`: both orientations send
  the generator to `b · p` inside `Ō(U) = B[E]`, so the `A[E]`-equivariance of the composite is
  multiplicativity of `MvPolynomial.map`.
* the global claim: Tag 08QJ at `𝒦ⁿ`
  (`CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow`),
  the naturality of `Stacks.ChaoticSite.derivedColimitTensorComparison` in the inclusions, and
  the computation of `derivedExtendScalars` at a K-projective resolution
  (`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`), replace the chain
  `𝒦^{n+k²} ⊆ ⋯ ⊆ 𝒦ⁿ` by a chain of complexes of abelian presheaves whose cohomology presheaves
  are the local `Tor'`s; `main_covariant` there, with the local claim as `h2`, and
  `Stacks.CategoryHomology.isZero_homology_totalDerivedColimit_obj` for the right `t`-exactness
  of `Lπ_!`, give `hpro` with `c = k²`.

`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow` derives the footnote
vanishing from this together with the vanishing of the graded pieces. -/
def SmallPolynomialAugmentationProNilpotent : Prop :=
  ∀ k : ℕ, ∃ c : ℕ, ∀ n i : ℕ, i < k →
    ((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived i).map
      (smallPolynomialAugmentationIdealPowMap A B κ (Nat.le_add_right n c)) = 0

/-! ### The footnote vanishing -/

/-- **The footnote vanishing of [Stacks, Tag 08RF], from its two halves.** Suppose

* `hgr`: the graded pieces vanish in low degree, `H_i(C_{B/A}, 𝒦ᵏ/𝒦ᵏ⁺¹) = 0` for `i < k`; and
* `hpro`: the filtration is pro-nilpotent on homology — for every `k` there is a `c` such that
  for every `n` the inclusion `𝒦^{n+c} ⊆ 𝒦ⁿ` induces the zero map on `H_i(C_{B/A}, -)` for
  every `i < k`.

Then `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`.

The proof is the source's combination of its two claims. Take `k = n` in `hpro` and let `c` be
the resulting integer. The map `H_i(C_{B/A}, 𝒦^{n+c}) → H_i(C_{B/A}, 𝒦ⁿ)` is zero by `hpro`,
and is an epimorphism by the dévissage
`CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap`, which applies
because `i < n ≤ n + c`. An epimorphism which is the zero morphism has a zero target. -/
theorem isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow
    (hgr : ∀ k i : ℕ, i < k → IsZero (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationGraded A B κ k)))
    (hpro : SmallPolynomialAugmentationProNilpotent A B κ)
    (i n : ℕ) (hi : i < n) :
    IsZero (((colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationIdealPow A B κ n)) := by
  obtain ⟨c, hc⟩ := hpro n
  have hepi := epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap A B κ hgr i n
    (n + c) hi (Nat.le_add_right n c)
  exact IsZero.of_epi_eq_zero _ (hc n i hi)


end Vanishing

end CommAlgCat

end
