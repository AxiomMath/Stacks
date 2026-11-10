module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of a coherent module with zero-dimensional support

Let `k` be a field, let `f : X ⟶ Spec k` be proper and let `ℱ` be a coherent module on `X` whose
support has dimension at most zero. Then

* `H⁰(X, ℱ) = ⨁_{x ∈ Supp ℱ} ℱ_x`,
* `Hⁱ(X, ℱ) = 0` for every `i > 0`, and
* `χ(X, ℱ) = dim_k H⁰(X, ℱ)`.

These are clauses (2), (3) and (4) of [Stacks, Tag 0AYT]. The argument for (3) is the source's
own: `ℱ` is the direct
image of a coherent module `𝒢` along the inclusion `ι : Z ⟶ X` of its scheme-theoretic support,
the scheme `Z` is affine because it is proper over `k` and zero-dimensional, so the higher
cohomology of `𝒢` vanishes by Serre's affine vanishing, and cohomology is unchanged by pushing
forward along a closed immersion. Clause (4) is then the source's own "we have (4) by definition
of the Euler characteristic `χ(X, ℱ)` and (3)": the alternating sum that defines
`AlgebraicGeometry.eulerCharacteristic` collapses to its degree-zero term.

## Main results

* `AlgebraicGeometry.isAffine_subscheme_annihilatorIdeal_of_topologicalKrullDim_supp_le_zero`:
  the scheme-theoretic support of such a module is an affine scheme.
* `AlgebraicGeometry.suppStalkDirectSumAddEquiv`:
  **clause (2) of [Stacks, Tag 0AYT]**, the decomposition `Γ(X, ℱ) ≅ ⨁_{x ∈ Supp ℱ} ℱ_x` of the
  global sections as the direct sum of the stalks along the support, the isomorphism being the
  one that assembles the germ maps.
* `AlgebraicGeometry.cohomologyOverFieldZeroEquivDirectSumSuppStalk`:
  the same clause read at `H⁰(X, ℱ)` rather than at `Γ(X, ℱ)`.
* `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero`:
  **clause (3) of [Stacks, Tag 0AYT]**, the vanishing `Hⁱ(X, ℱ) = 0` for `i > 0`.
* `AlgebraicGeometry.eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero`:
  **clause (4) of [Stacks, Tag 0AYT]**, the identity `χ(X, ℱ) = dim_k H⁰(X, ℱ)`.

## Implementation notes

**Clause (2) is proved on `X` itself, not on the scheme-theoretic support.** The source descends
`ℱ` to `Z`, decomposes `Z` as a finite disjoint union of spectra of local Artinian rings
([Stacks, Tag 06LH]), reads `H⁰(Z, 𝒢) = ⨁_z 𝒢_z` off that decomposition, and transports the
answer back along `𝒢_z = (ι_* 𝒢)_x = ℱ_x`. The route taken here keeps the whole argument on `X`
and uses `Z` only to see that `Supp ℱ` is a finite set of points, each isolated in `Supp ℱ`: the
subscheme `Z` is locally Artinian because it is locally Noetherian of dimension zero
(`AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`, which is the content of
[Stacks, Tag 06LH] needed here), hence discrete, and compact because it is proper over `k`;
`ι` is a closed embedding, so `Supp ℱ = range ι` inherits both. Given that, the germ map
`Γ(X, ℱ) ⟶ ∏_{x ∈ Supp ℱ} ℱ_x` is an isomorphism by pure sheaf theory: sections are determined
by their germs and the stalks off `Supp ℱ` vanish, which gives injectivity; and a family of
germs glues over the cover of `X` by `X ∖ Supp ℱ` together with one isolating open per point of
the support, every overlap of two distinct members of that cover missing `Supp ℱ` and therefore
carrying no nonzero section. So neither the module–sheaf correspondence on an affine scheme nor
the stalk comparison along `ι` is needed, and no decomposition of a module over an Artinian ring
is needed.

**The direct sum and the product.** `Supp ℱ` is finite, so the product of the stalks and their
direct sum agree; `AlgebraicGeometry.suppStalkDirectSumAddEquiv` is stated with the source's
direct sum and factors through the product form
`AlgebraicGeometry.suppStalkPiAddEquiv`, which is the one the germ maps assemble into directly.

**Why the scheme-theoretic support is affine.** The source says only "`Z` is affine since it has
dimension zero". The route taken here is through finiteness over the base: the inclusion
`ι : Z ⟶ X` of the closed subscheme cut out by the annihilator of `ℱ` is a closed immersion,
hence proper, so `ι ≫ f` is proper; the underlying space of `Z` is the support of `ℱ`
(`AlgebraicGeometry.supp_eq_support_annihilatorIdeal` together with
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`), so `Z` is zero-dimensional; a proper
morphism out of a zero-dimensional scheme is finite by Zariski's main theorem
(`AlgebraicGeometry.isFinite_of_isProper_of_topologicalKrullDim_le_zero`); and a scheme finite —
in particular affine — over an affine scheme is affine.

**Locally Noetherian is not a hypothesis.** The descent of `ℱ` to its scheme-theoretic support
needs `X` locally Noetherian, but a proper morphism is locally of finite type and the spectrum of
a field is Noetherian, so `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` supplies it
from the properness already assumed.

**The passage between the two spellings of cohomology.** Serre vanishing is stated for `Hgroup`,
the cohomology of the abelian sheaf of sections, while the conclusion is about
`AlgebraicGeometry.cohomologyOverField`. The two vanish together by
`AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`, so no comparison of the
cohomology theories beyond that equivalence is needed.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped DirectSum
open Stacks.AlgebraicGeometry.CoherentTFAE

namespace AlgebraicGeometry

universe u

/-- **The scheme-theoretic support of a coherent module with zero-dimensional support on a proper
scheme over a field is affine.** Its underlying space is the support of the module, so it is
zero-dimensional, and it is proper over `k`; a proper morphism out of a zero-dimensional scheme is
finite, hence affine, and so the source is affine. -/
theorem isAffine_subscheme_annihilatorIdeal_of_topologicalKrullDim_supp_le_zero (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) :
    IsAffine (annihilatorIdeal F).subscheme := by
  have hrange : Set.range (annihilatorIdeal F).subschemeι.base ⊆
      _root_.SheafOfModules.supp F := by
    rw [supp_eq_support_annihilatorIdeal F, ← (annihilatorIdeal F).range_subschemeι]
  have hdim : topologicalKrullDim ((annihilatorIdeal F).subscheme : Type u) ≤ 0 :=
    (topologicalKrullDim_le_of_range_subset _ _ hrange).trans hF
  have : IsFinite ((annihilatorIdeal F).subschemeι ≫ f) :=
    isFinite_of_isProper_of_topologicalKrullDim_le_zero _ hdim
  exact isAffine_of_isAffineHom ((annihilatorIdeal F).subschemeι ≫ f)

/-! ### Clause (2): the global sections are the direct sum of the stalks along the support -/

/-- The underlying sheaf of abelian groups of an `𝒪_X`-module, packaged as a sheaf. -/
private noncomputable def abSheaf {X : Scheme.{u}} (F : X.Modules) : TopCat.Sheaf Ab.{u} X :=
  ⟨Scheme.Modules.presheaf F, F.isSheaf⟩

/-- **Away from the support the stalk is trivial.** -/
theorem subsingleton_stalk_of_notMem_supp {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hx : x ∉ _root_.SheafOfModules.supp F) :
    Subsingleton ((Scheme.Modules.presheaf F).stalk x) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ c : (Scheme.Modules.presheaf F).stalk x, c = 0 := fun c => by
    by_contra hc
    exact hx ⟨c, hc⟩
  rw [h a, h b]

/-- **A section over an open that misses the support vanishes.** Every one of its germs is zero
because the stalks there are, and a section of a sheaf is determined by its germs. -/
theorem eq_zero_of_inter_supp_eq_empty {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (hU : (U : Set X) ∩ _root_.SheafOfModules.supp F = ∅) (s : Γ(F, U)) : s = 0 :=
  TopCat.Presheaf.section_ext (abSheaf F) U s 0 fun x hx =>
    (subsingleton_stalk_of_notMem_supp F
      (fun h => Set.eq_empty_iff_forall_notMem.mp hU x ⟨hx, h⟩)).elim _ _

/-- **The germ maps at the points of the support, assembled into one homomorphism** from the
global sections of `ℱ` to the product of the stalks of `ℱ` along `Supp ℱ`. -/
noncomputable def suppGermHom {X : Scheme.{u}} (F : X.Modules) :
    Γ(F, ⊤) →+ ∀ x : ↥(_root_.SheafOfModules.supp F), (Scheme.Modules.presheaf F).stalk x.1 :=
  AddMonoidHom.pi fun x => ConcreteCategory.hom ((Scheme.Modules.presheaf F).Γgerm x.1)

/-- **`AlgebraicGeometry.suppGermHom` is injective, for every module.** A section all of whose
germs along the support vanish has all its germs zero, the stalks off the support being trivial,
and so is zero. -/
theorem injective_suppGermHom {X : Scheme.{u}} (F : X.Modules) :
    Function.Injective (suppGermHom F) := by
  intro s t h
  refine TopCat.Presheaf.section_ext (abSheaf F) ⊤ s t fun x _ => ?_
  by_cases hx : x ∈ _root_.SheafOfModules.supp F
  · exact congrFun h ⟨x, hx⟩
  · exact (subsingleton_stalk_of_notMem_supp F hx).elim _ _

/-- **`AlgebraicGeometry.suppGermHom` is surjective** as soon as the support is closed and each
of its points is isolated in it.

Given a family of germs, pick a representing section at each point of the support and shrink its
domain inside the isolating open. Those domains together with the complement of the support
cover `X`, and the overlap of two distinct members of that cover misses the support, hence
carries no nonzero section: the family — extended by zero on the complement — is therefore
compatible, and its gluing is a global section with the prescribed germs. -/
theorem surjective_suppGermHom {X : Scheme.{u}} (F : X.Modules)
    (hclosed : IsClosed (_root_.SheafOfModules.supp F))
    (hisol : ∀ x ∈ _root_.SheafOfModules.supp F, ∃ U : X.Opens, x ∈ U ∧
      (U : Set X) ∩ _root_.SheafOfModules.supp F = {x}) :
    Function.Surjective (suppGermHom F) := by
  classical
  intro t
  choose U hxU hUS using hisol
  choose V hV sV hsV using fun x : ↥(_root_.SheafOfModules.supp F) =>
    (Scheme.Modules.presheaf F).exists_germ_eq (t x)
  let O : Option ↥(_root_.SheafOfModules.supp F) → X.Opens := fun i => i.elim
    ⟨(_root_.SheafOfModules.supp F)ᶜ, hclosed.isOpen_compl⟩
    (fun x => U x.1 x.2 ⊓ V x)
  have hmemO : ∀ x : ↥(_root_.SheafOfModules.supp F), x.1 ∈ O (some x) :=
    fun x => ⟨hxU x.1 x.2, hV x⟩
  have hempty : ∀ i j, i ≠ j →
      ((O i ⊓ O j : X.Opens) : Set X) ∩ _root_.SheafOfModules.supp F = ∅ := by
    intro i j hij
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    obtain ⟨⟨hyi, hyj⟩, hyS⟩ := hy
    match i, j with
    | none, none => exact hij rfl
    | none, some x => exact hyi hyS
    | some x, none => exact hyj hyS
    | some x, some x' =>
      have hx : y = x.1 := by
        have hmem : y ∈ (U x.1 x.2 : Set X) ∩ _root_.SheafOfModules.supp F := ⟨hyi.1, hyS⟩
        rwa [hUS x.1 x.2, Set.mem_singleton_iff] at hmem
      have hx' : y = x'.1 := by
        have hmem : y ∈ (U x'.1 x'.2 : Set X) ∩ _root_.SheafOfModules.supp F := ⟨hyj.1, hyS⟩
        rwa [hUS x'.1 x'.2, Set.mem_singleton_iff] at hmem
      exact hij (congrArg some (Subtype.ext (hx ▸ hx')))
  let sf : ∀ i, Γ(F, O i) := fun i => match i with
    | none => 0
    | some x => (Scheme.Modules.presheaf F).map (Opens.infLERight (U x.1 x.2) (V x)).op (sV x)
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.Modules.presheaf F) O sf := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · have hzero := eq_zero_of_inter_supp_eq_empty F (O i ⊓ O j) (hempty i j hij)
      exact (hzero _).trans (hzero _).symm
  have hcover : (⊤ : X.Opens) ≤ iSup O := by
    intro y _
    rw [Opens.mem_iSup]
    by_cases hy : y ∈ _root_.SheafOfModules.supp F
    · exact ⟨some ⟨y, hy⟩, hmemO ⟨y, hy⟩⟩
    · exact ⟨none, hy⟩
  obtain ⟨s, hs, -⟩ := (abSheaf F).existsUnique_gluing' O ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  refine ⟨s, funext fun x => ?_⟩
  have hx : x.1 ∈ O (some x) := hmemO x
  have h₁ : (Scheme.Modules.presheaf F).map (homOfLE (le_top (a := O (some x)))).op s =
      (Scheme.Modules.presheaf F).map (Opens.infLERight (U x.1 x.2) (V x)).op (sV x) :=
    hs (some x)
  have h₂ : (Scheme.Modules.presheaf F).germ (O (some x)) x.1 hx
      ((Scheme.Modules.presheaf F).map (homOfLE (le_top (a := O (some x)))).op s) =
      (Scheme.Modules.presheaf F).Γgerm x.1 s :=
    (Scheme.Modules.presheaf F).Γgerm_res_apply x.1 hx s
  have h₃ : (Scheme.Modules.presheaf F).germ (O (some x)) x.1 hx
      ((Scheme.Modules.presheaf F).map (Opens.infLERight (U x.1 x.2) (V x)).op (sV x)) =
      (Scheme.Modules.presheaf F).germ (V x) x.1 (hV x) (sV x) :=
    TopCat.Presheaf.germ_res_apply (Scheme.Modules.presheaf F)
      (Opens.infLERight (U x.1 x.2) (V x)) x.1 hx (sV x)
  change (Scheme.Modules.presheaf F).Γgerm x.1 s = t x
  rw [← h₂, h₁, h₃]
  exact hsV x

/-- **The support of a coherent module is the image of its scheme-theoretic support.** -/
theorem supp_eq_range_subschemeι {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] :
    _root_.SheafOfModules.supp F = Set.range (annihilatorIdeal F).subschemeι.base := by
  rw [supp_eq_support_annihilatorIdeal F, ← (annihilatorIdeal F).range_subschemeι]

section ZeroDimensional

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (F : X.Modules) [F.IsCoherent]
  (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0)

include f hF

/-- **The scheme-theoretic support of a coherent module with zero-dimensional support on a
proper scheme over a field is a finite discrete space.** It is locally Noetherian of dimension
zero, hence locally Artinian — which is the content of [Stacks, Tag 06LH] used here — hence
discrete; and it is proper over `k`, hence compact. -/
theorem discreteTopology_and_finite_subscheme_annihilatorIdeal_of_supp_le_zero
    [IsLocallyNoetherian X] :
    DiscreteTopology ((annihilatorIdeal F).subscheme : Type u) ∧
      Finite ((annihilatorIdeal F).subscheme : Type u) := by
  have hrange : Set.range (annihilatorIdeal F).subschemeι.base ⊆
      _root_.SheafOfModules.supp F := by
    rw [supp_eq_range_subschemeι F]
  have hdim : topologicalKrullDim ((annihilatorIdeal F).subscheme : Type u) ≤ 0 :=
    (topologicalKrullDim_le_of_range_subset _ _ hrange).trans hF
  have : IsLocallyNoetherian ((annihilatorIdeal F).subscheme) :=
    LocallyOfFiniteType.isLocallyNoetherian ((annihilatorIdeal F).subschemeι ≫ f)
  have : IsLocallyArtinian ((annihilatorIdeal F).subscheme) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : CompactSpace ((annihilatorIdeal F).subscheme : Type u) :=
    (quasiCompact_iff_compactSpace ((annihilatorIdeal F).subschemeι ≫ f)).mp inferInstance
  exact ⟨inferInstance, finite_of_compact_of_discrete⟩

/-- **Every point of a zero-dimensional support is isolated in it:** some open of `X` meets the
support in that point alone. The scheme-theoretic support is discrete and its inclusion is a
closed embedding, so a singleton open of it is cut out by an open of `X`. -/
theorem exists_isolating_open_of_supp_le_zero :
    ∀ x ∈ _root_.SheafOfModules.supp F, ∃ U : X.Opens, x ∈ U ∧
      (U : Set X) ∩ _root_.SheafOfModules.supp F = {x} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : DiscreteTopology ((annihilatorIdeal F).subscheme : Type u) :=
    (discreteTopology_and_finite_subscheme_annihilatorIdeal_of_supp_le_zero k f F hF).1
  intro x hx
  rw [supp_eq_range_subschemeι F] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, ht, hpre⟩ :=
    (IsClosedImmersion.isClosedEmbedding
      (annihilatorIdeal F).subschemeι).isInducing.isOpen_iff.mp (isOpen_discrete {z})
  have hzt : z ∈ (annihilatorIdeal F).subschemeι.base ⁻¹' t := by rw [hpre]; rfl
  refine ⟨⟨t, ht⟩, hzt, ?_⟩
  rw [supp_eq_range_subschemeι F]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hzt, ⟨z, rfl⟩⟩, ?_⟩
  rintro y ⟨hyt, z', rfl⟩
  have hz' : z' ∈ (annihilatorIdeal F).subschemeι.base ⁻¹' t := hyt
  rw [hpre, Set.mem_singleton_iff] at hz'
  rw [hz']

/-- **A zero-dimensional support is a finite set of points.** -/
theorem finite_supp_of_supp_le_zero : (_root_.SheafOfModules.supp F).Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Finite ((annihilatorIdeal F).subscheme : Type u) :=
    (discreteTopology_and_finite_subscheme_annihilatorIdeal_of_supp_le_zero k f F hF).2
  rw [supp_eq_range_subschemeι F]
  exact Set.finite_range _

/-- **The germ map onto the stalks along a zero-dimensional support is bijective.** -/
theorem bijective_suppGermHom_of_supp_le_zero : Function.Bijective (suppGermHom F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsFiniteType := (isQuasicoherent_isFiniteType_of_isCoherent F).2
  refine ⟨injective_suppGermHom F, surjective_suppGermHom F ?_
    (exists_isolating_open_of_supp_le_zero k f F hF)⟩
  exact _root_.SheafOfModules.isClosed_supp F

/-- **[Stacks, Tag 0AYT] (2) at the product of the stalks.** For `f : X ⟶ Spec k` proper and `ℱ`
coherent on `X` with `dim (supp ℱ) ≤ 0`, the germ maps assemble into an isomorphism

  `Γ(X, ℱ) ≅ ∏_{x ∈ Supp ℱ} ℱ_x`

of abelian groups. The support is finite
(`AlgebraicGeometry.finite_supp_of_supp_le_zero`), so this product is the source's direct sum;
that reading is `AlgebraicGeometry.suppStalkDirectSumAddEquiv`. -/
noncomputable def suppStalkPiAddEquiv :
    Γ(F, ⊤) ≃+ ∀ x : ↥(_root_.SheafOfModules.supp F), (Scheme.Modules.presheaf F).stalk x.1 :=
  AddEquiv.ofBijective (suppGermHom F) (bijective_suppGermHom_of_supp_le_zero k f F hF)

/-- **[Stacks, Tag 0AYT] (2): `H⁰(X, ℱ)` is the direct sum of the stalks of `ℱ` along its
support.** For `f : X ⟶ Spec k` proper and `ℱ` coherent on `X` with `dim (supp ℱ) ≤ 0`,

  `Γ(X, ℱ) ≅ ⨁_{x ∈ Supp ℱ} ℱ_x`

as abelian groups, the isomorphism being the one assembled from the germ maps
(`AlgebraicGeometry.suppGermHom`) followed by the identification of the product of a finite
family with its direct sum. -/
@[stacks 0AYT "(2), at the `Γ(ℱ, ⊤)` spelling of `H⁰(X, ℱ)`; the `H⁰` spelling is \
`AlgebraicGeometry.cohomologyOverFieldZeroEquivDirectSumSuppStalk`"]
noncomputable def suppStalkDirectSumAddEquiv :
    Γ(F, ⊤) ≃+ ⨁ x : ↥(_root_.SheafOfModules.supp F), (Scheme.Modules.presheaf F).stalk x.1 :=
  letI : Fintype ↥(_root_.SheafOfModules.supp F) :=
    (finite_supp_of_supp_le_zero k f F hF).fintype
  (suppStalkPiAddEquiv k f F hF).trans
    (DirectSum.linearEquivFunOnFintype ℤ _
      (fun x : ↥(_root_.SheafOfModules.supp F) =>
        (Scheme.Modules.presheaf F).stalk x.1)).toAddEquiv.symm

/-- **[Stacks, Tag 0AYT] (2), read at `H⁰(X, ℱ)`.** Composing
`AlgebraicGeometry.suppStalkDirectSumAddEquiv` with the identification of degree-zero cohomology
with global sections gives

  `H⁰(X, ℱ) = ⨁_{x ∈ Supp ℱ} ℱ_x`.

It is an `Equiv` rather than an additive equivalence because
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`, the only identification of
`H⁰(X, ℱ)` with `Γ(ℱ, ⊤)` this library has, is one: `Γ(ℱ, ⊤)` carries no `Module k` instance
and the comparison is stated at the level of types. The additive structure of the decomposition
is in `AlgebraicGeometry.suppStalkDirectSumAddEquiv`. -/
@[stacks 0AYT "(2), at the `H⁰(X, ℱ)` spelling; the additive structure of the same \
decomposition is on `AlgebraicGeometry.suppStalkDirectSumAddEquiv`"]
noncomputable def cohomologyOverFieldZeroEquivDirectSumSuppStalk :
    (cohomologyOverField k f F 0 : Type u) ≃
      ⨁ x : ↥(_root_.SheafOfModules.supp F), (Scheme.Modules.presheaf F).stalk x.1 :=
  (cohomologyOverFieldZeroEquivSections k f F).trans
    (suppStalkDirectSumAddEquiv k f F hF).toEquiv

end ZeroDimensional

/-- **[Stacks, Tag 0AYT] (3): the higher cohomology of a coherent module whose support has
dimension at most zero vanishes.** For `f : X ⟶ Spec k` proper and `ℱ` coherent on `X` with
`dim (supp ℱ) ≤ 0`, the `k`-vector space `Hⁱ(X, ℱ)` is zero for every `i > 0`.

The module is the direct image of a coherent module on its scheme-theoretic support
([Stacks, Tag 02OM]), that support is affine, Serre vanishing ([Stacks, Tag 01XB]) kills the
higher cohomology there, and a closed immersion does not change cohomology. -/
@[stacks 0AYT "(3)"]
theorem isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) (i : ℕ) (hi : 0 < i) :
    IsZero (cohomologyOverField k f F i) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal F
  have _ : G.IsCoherent := hG
  have _ : G.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent G).1
  have _ : IsAffine (annihilatorIdeal F).subscheme :=
    isAffine_subscheme_annihilatorIdeal_of_topologicalKrullDim_supp_le_zero k f F hF
  have hvan : IsZero (cohomologyOverField k ((annihilatorIdeal F).subschemeι ≫ f) G i) :=
    (isZero_cohomologyOverField_iff_isZero_hgroup k _ G i).mpr
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ G ⊤
        (isAffineOpen_top _) i hi)
  exact hvan.of_iso
    ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k _ f G i).trans
      (cohomologyOverFieldIso k f e i)).symm

/-- **[Stacks, Tag 0AYT] (4): the Euler characteristic of a coherent module whose support has
dimension at most zero is the dimension of its space of global sections.** For
`f : X ⟶ Spec k` proper and `ℱ` coherent on `X` with `dim (supp ℱ) ≤ 0`,

  `χ(X, ℱ) = dim_k H⁰(X, ℱ)`.

This is the source's "we have (4) by definition of the Euler characteristic `χ(X, ℱ)` and (3)":
`AlgebraicGeometry.eulerCharacteristic` is by definition the alternating sum
`∑ⁿ (-1)ⁿ dim_k Hⁿ(X, ℱ)`, clause (3) kills every term with `n > 0`, and a sum supported on `{0}`
is its value there. -/
@[stacks 0AYT "(4)"]
theorem eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsCoherent] (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) :
    eulerCharacteristic k f F = (Module.finrank k (cohomologyOverField k f F 0) : ℤ) := by
  rw [eulerCharacteristic_eq_finsum]
  exact finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k f F fun i hi =>
    isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f F hF i hi

end AlgebraicGeometry

end
