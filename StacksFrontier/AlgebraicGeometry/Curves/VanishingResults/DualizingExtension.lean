module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions of the dualizing sheaf on a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω` be the dualizing sheaf of `X` and consider an exact sequence
`ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` of coherent `𝒪_X`-modules. [Stacks, Tag 0B5E] asserts that if
`H¹(X, 𝒬) = 0` then either `H¹(X, ℱ) = 0` or `ℱ ≅ ω ⊕ 𝒬`.

## Main definitions

* `AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` is the
  representability of the functor `ℱ ↦ Hom_k(H¹(X, ℱ), k)` by the dualizing sheaf, together
  with its naturality: clause (5) of [Stacks, Tag 0BS2].
* `AlgebraicGeometry.CohenMacaulayCurveSituation.SecondCohomologyVanishing` is the vanishing of
  `H²(X, -)`, which holds on a one-dimensional scheme by [Stacks, Tag 02UZ].

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`: **[Stacks, Tag 02UZ]**
  for the modules on a scheme proper over a field — `Hⁱ(X, ℱ) = 0` above the dimension of `X`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.secondCohomologyVanishing`: that vanishing in
  degree two, which is what Situation [Stacks, Tag 0B5D] consumes.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_f_of_isZero`
  and `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_g_of_isZero`
  are the two surjectivity steps of the long exact sequence of a short exact sequence.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_one_of_exact`:
  for an exact sequence `ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` with `H¹(X, 𝒬) = 0`, the map `H¹(X, ω) ⟶ H¹(X, ℱ)` is
  surjective.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.exists_retraction_of_bijective`: if
  `H¹(X, ω) ⟶ H¹(X, ℱ)` is bijective then `ω ⟶ ℱ` has a retraction.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.isZero_firstCohomology_or_iso_biprod`:
  the splitting of [Stacks, Tag 0B5E] for any `ω` with the three properties above; the tag
  itself, at the dualizing sheaf, is in `Curves/VanishingResults/DualizingSheafExtension.lean`.

## Implementation notes

Cohomology over the base field is `AlgebraicGeometry.cohomologyOverField`, and its
functoriality in the module is `AlgebraicGeometry.cohomologyOverFieldMap`; the exact sequence
`ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` is recorded as exactness of the short complex `ω ⟶ ℱ ⟶ 𝒬` together with
`Epi` for the second arrow, and the splitting alternative as an isomorphism `ℱ ≅ ω ⊞ 𝒬`
identifying the two arrows with `biprod.inl` and `biprod.snd`.

*Vanishing of `H²`.* The source's "`H¹(X, 𝒬) = 0` makes `H¹(X, ω) ⟶ H¹(X, ℱ)` an isomorphism"
also uses that `H²` vanishes on `X`, because `ω ⟶ ℱ` need not be injective: the surjection
factors through the image of `ω`, and only `H²` of the kernel being zero makes the first factor
surjective. That vanishing is [Stacks, Tag 02UZ], and it is **proved here**, as
`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`: Grothendieck's
vanishing theorem is available for abelian sheaves on a Noetherian space
(`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`), and the
three comparisons needed to read it in the `AlgebraicGeometry.cohomologyOverField` spelling are
available too; see the implementation note on the proof.

**Two hypotheses are carried.**

*Duality.* `FirstCohomologyDuality ω` is clause (5) of [Stacks, Tag 0BS2]: for every
quasi-coherent `ℱ` the group `Hom(ℱ, ω)` is the `k`-linear dual of `H¹(X, ℱ)`, naturally in
`ℱ`. It is a hypothesis **here** because `ω` is an arbitrary module at this point in the chapter:
the statement is about whichever `ω` the consumer supplies, and nothing constrains it. It is not
a hypothesis in the development as a whole — at the canonical dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` it is discharged by
`AlgebraicGeometry.CohenMacaulayCurveSituation.firstCohomologyDuality_dualizingSheafOverField` of
`Curves/VanishingResults/DualizingSheafClauseFive.lean`, which is clause (5) of
[Stacks, Tag 0BS2] proved with nothing carried. [Stacks, Tag 0AWP], the form the source cites, is
proved over a field in `Curves/VanishingResults/DualizingModuleRepresentability.lean` and has
that clause as its `d = 1` case. The naturality clause is what the source's "the composition
`ω ⟶ ℱ ⟶ ω` is the identity by the universal property" consumes, and the pointwise bijection
alone does not prove the tag.

*One-dimensionality of `H¹(X, ω)`.* The source gets `dim_k H¹(X, ω) = 1` from the duality of
`H⁰(X, 𝒪_X) = k` with `H¹(X, ω)` of Section [Stacks, Tag 0B5B], which is not in this
development either; it is the hypothesis `hone`. That duality is clause (4) of
[Stacks, Tag 0BS2] at `K = 𝒪_X` and `i = 0`, read in the Cohen--Macaulay case `ω^• = ω[1]` of
[Stacks, Tag 0BS3] — a *different* clause from the `FirstCohomologyDuality` above, and not a
consequence of it: at `ℱ = ω` clause (5) says only that `H¹(X, ω)^∨` is `End(ω)`, and
`End(ω) = k[t]/(t²)` with `H¹(X, ω)` its dual is a model of clause (5), with its naturality, in
which `dim_k H¹(X, ω) = 2`. Given the clause-(4) pairing,
`AlgebraicGeometry.CohenMacaulayCurveSituation.finrank_cohomologyOverField_one_eq_one_of_unitDual`
of `Curves/VanishingResults/DualizingRiemannRoch.lean` discharges `hone` from the
`H⁰(X, 𝒪_X) = k` of Situation [Stacks, Tag 0B5D].

**How [Stacks, Tag 02UZ] is read in the `cohomologyOverField` spelling.** Grothendieck's
vanishing theorem is available for an abelian sheaf on a Noetherian topological space, in the
`CategoryTheory.Sheaf.H` spelling. Three existing comparisons carry it over, in this order:
`AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup` ([Stacks, Tag 01F1] (1)) to the
abelian-group-valued cohomology of the underlying sheaf;
`Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`
([Stacks, Tag 03FD]) to the value at `⊤` of Mathlib's cohomology presheaf; and
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top` from that value to
`CategoryTheory.Sheaf.H`, the whole space being the terminal open. The Noetherian space is
produced from properness alone: a proper morphism is locally of finite type, so `X` is locally
Noetherian over the spectrum of a field, and it is quasi-compact, so `X` is a Noetherian scheme.

## References

* [Stacks Project, Tag 0B5E](https://stacks.math.columbia.edu/tag/0B5E)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleComparison
  (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf)
open Stacks.Cohomology.TerminalCohomology (subsingleton_H_iff_subsingleton_H'_top)
open Stacks.CohomologyVanishing (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le)

universe u

namespace AlgebraicGeometry

/-! ### Grothendieck vanishing above the dimension -/

/-- **Stacks Project, Tag 02UZ.** For `f : X ⟶ Spec k` proper and `X` of topological Krull
dimension at most `d`, the cohomology `Hⁱ(X, ℱ)` of every `𝒪_X`-module vanishes for `i > d`.

Properness makes `X` a Noetherian scheme, hence a Noetherian space, where Grothendieck's theorem
is `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`; the
three comparisons listed in the module documentation read that vanishing in the
`AlgebraicGeometry.cohomologyOverField` spelling. -/
@[stacks 02UZ "the vanishing Hⁱ(X, ℱ) = 0 for i above the dimension, for the modules on a \
scheme proper over a field, read through the comparison of Tag 01F1 (1) with the cohomology of \
the underlying abelian sheaf"]
public theorem isZero_cohomologyOverField_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) {d i : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (cohomologyOverField k f F i) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hnoeth : IsNoetherian X := { }
  refine (isZero_cohomologyOverField_iff_isZero_hgroup k f F i).mpr ?_
  refine (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (J := Opens.grothendieckTopology (X : Type u)) (R := X.ringCatSheaf)
    (U := (⊤ : Opens (X : Type u))) (n := i) (F := F)).mpr ?_
  have hsub := (subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i).mp
    (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le (d := d) hdim hi _)
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

/-! ### Linear algebra: a surjection out of a line -/

/-- **A surjective linear map out of a one-dimensional space onto a nonzero space is
bijective.** The kernel is a proper subspace of a line, hence zero. -/
public theorem bijective_of_surjective_of_finrank_eq_one {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (φ : V →ₗ[k] W)
    (hsurj : Function.Surjective φ) (hV : Module.finrank k V = 1) (hW : ¬ Subsingleton W) :
    Function.Bijective φ := by
  have : FiniteDimensional k V := FiniteDimensional.of_finrank_pos (by omega)
  have : FiniteDimensional k W := Module.Finite.of_surjective φ hsurj
  have : Nontrivial W := not_subsingleton_iff_nontrivial.mp hW
  refine ⟨?_, hsurj⟩
  have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hr, hV, finrank_top] at h
  have hWpos : 0 < Module.finrank k W := Module.finrank_pos_iff.mpr inferInstance
  have hker : Module.finrank k (LinearMap.ker φ : Submodule k V) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-! ### The cited input, and the vanishing that is proved -/

/-- **Clause (5) of [Stacks, Tag 0BS2]: the dualizing sheaf `ω` represents the functor
`ℱ ↦ Hom_k(H¹(X, ℱ), k)` on quasi-coherent modules.**

The first field is the bijection and the second is its naturality, which is the form the
universal property is used in: a map `ℱ ⟶ ω` is determined by, and can be prescribed through,
the `k`-linear functional it induces on `H¹(X, ℱ)`.

`ω` is an unconstrained module here, so its representability has to be assumed; at the canonical
dualizing sheaf it is proved, by
`AlgebraicGeometry.CohenMacaulayCurveSituation.firstCohomologyDuality_dualizingSheafOverField` of
`Curves/VanishingResults/DualizingSheafClauseFive.lean`. -/
public structure FirstCohomologyDuality (ω : S.X.Modules) where
  /-- Maps to `ω` are the `k`-linear functionals on first cohomology. -/
  dual : ∀ F : S.X.Modules, F.IsQuasicoherent →
    (F ⟶ ω) ≃+ (cohomologyOverField S.k S.f F 1 →ₗ[S.k] S.k)
  /-- The bijection is natural in the module: precomposing a map to `ω` with `u` corresponds to
  precomposing the functional with `H¹(X, u)`. -/
  dual_comp : ∀ (F G : S.X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
    (u : F ⟶ G) (φ : G ⟶ ω),
      dual F hF (u ≫ φ) = (dual G hG φ).comp (cohomologyOverFieldMap S.k S.f u 1).hom

/-- **Vanishing of the second cohomology of every module on `X`.** On a one-dimensional
Noetherian scheme this is [Stacks, Tag 02UZ]; it holds in Situation [Stacks, Tag 0B5D] by
`AlgebraicGeometry.CohenMacaulayCurveSituation.secondCohomologyVanishing`. -/
public def SecondCohomologyVanishing : Prop :=
  ∀ M : S.X.Modules, IsZero (cohomologyOverField S.k S.f M 2)

/-- **`H²(X, -)` vanishes in Situation [Stacks, Tag 0B5D].** This is [Stacks, Tag 02UZ] on the
one-dimensional proper scheme `X`. -/
@[stacks 02UZ "degree two on a one-dimensional proper scheme over a field, which is what \
Situation 0B5D consumes"]
public theorem secondCohomologyVanishing : S.SecondCohomologyVanishing := fun M =>
  isZero_cohomologyOverField_of_topologicalKrullDim_le S.k S.f M
    (d := 1) (le_of_eq S.dimension_one) (by omega)

/-! ### Surjectivity along the long exact sequence -/

variable {S}

/-- **`Hⁿ(X, ℱ₁) ⟶ Hⁿ(X, ℱ₂)` is onto when `Hⁿ(X, ℱ₃) = 0`**, for a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `X`. -/
public theorem surjective_cohomologyOverFieldMap_f_of_isZero {T : ShortComplex S.X.Modules}
    (hT : T.ShortExact) (n : ℕ) (h : IsZero (cohomologyOverField S.k S.f T.X₃ n)) :
    Function.Surjective (cohomologyOverFieldMap S.k S.f T.f n) := by
  obtain ⟨-, -, hfg, -, -⟩ := exists_cohomologyOverField_longExactSequence S.k S.f hT
  have := ModuleCat.subsingleton_of_isZero h
  exact fun b => (hfg n b).mp (Subsingleton.elim _ _)

/-- **`Hⁿ(X, ℱ₂) ⟶ Hⁿ(X, ℱ₃)` is onto when `Hⁿ⁺¹(X, ℱ₁) = 0`**, for a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `X`. -/
public theorem surjective_cohomologyOverFieldMap_g_of_isZero {T : ShortComplex S.X.Modules}
    (hT : T.ShortExact) (n : ℕ) (h : IsZero (cohomologyOverField S.k S.f T.X₁ (n + 1))) :
    Function.Surjective (cohomologyOverFieldMap S.k S.f T.g n) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence S.k S.f hT
  have := ModuleCat.subsingleton_of_isZero h
  exact fun b => (hgd n b).mp (Subsingleton.elim _ _)

/-- **`H⁰(X, ℱ₃)` embeds into `H¹(X, ℱ₁)` when `H⁰(X, ℱ₂) ⟶ H⁰(X, ℱ₃)` is the zero map**, for a
short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `X`: the connecting map has zero
kernel, because its kernel is the image of the zero map. -/
public theorem finrank_zeroth_le_finrank_first {T : ShortComplex S.X.Modules}
    (hT : T.ShortExact) (hfin : FiniteDimensional S.k (cohomologyOverField S.k S.f T.X₁ 1))
    (hzero : ∀ a, cohomologyOverFieldMap S.k S.f T.g 0 a = 0) :
    Module.finrank S.k (cohomologyOverField S.k S.f T.X₃ 0) ≤
      Module.finrank S.k (cohomologyOverField S.k S.f T.X₁ 1) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence S.k S.f hT
  have := hfin
  refine LinearMap.finrank_le_finrank_of_injective (f := (d 0).hom) ?_
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun b hb => ?_)
  obtain ⟨a, ha⟩ := (hgd 0 b).mp hb
  exact ha.symm.trans (hzero a)

/-! ### Stacks Tag 0B5E -/

/-- **The first cohomology of the dualizing sheaf surjects onto that of an extension of it with
quotient of vanishing first cohomology.** For an exact sequence `ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` of modules on
`X` with `H¹(X, 𝒬) = 0`, the map `H¹(X, ω) ⟶ H¹(X, ℱ)` is onto.

The sequence is split at the kernel `𝒦` of `ℱ ⟶ 𝒬` into `0 ⟶ 𝒦 ⟶ ℱ ⟶ 𝒬 ⟶ 0`, where
`H¹(X, 𝒬) = 0` makes `H¹(X, 𝒦) ⟶ H¹(X, ℱ)` onto, and `0 ⟶ ker ⟶ ω ⟶ 𝒦 ⟶ 0`, where the
vanishing of `H²` makes `H¹(X, ω) ⟶ H¹(X, 𝒦)` onto. -/
public theorem surjective_cohomologyOverFieldMap_one_of_exact
    (hH2 : S.SecondCohomologyVanishing) {ω F Q : S.X.Modules} (α : ω ⟶ F) (β : F ⟶ Q)
    (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β]
    (hQ : IsZero (cohomologyOverField S.k S.f Q 1)) :
    Function.Surjective (cohomologyOverFieldMap S.k S.f α 1) := by
  have h₁ : Function.Surjective (cohomologyOverFieldMap S.k S.f (kernel.ι β) 1) :=
    surjective_cohomologyOverFieldMap_f_of_isZero
      (ShortComplex.shortExact_mk_kernel_ι β) 1 hQ
  have hρ : Epi (kernel.lift β α hαβ) := hex.epi_kernelLift
  have h₂ : Function.Surjective
      (cohomologyOverFieldMap S.k S.f (kernel.lift β α hαβ) 1) :=
    surjective_cohomologyOverFieldMap_g_of_isZero
      (ShortComplex.shortExact_mk_kernel_ι (kernel.lift β α hαβ)) 1
      (hH2 (kernel (kernel.lift β α hαβ)))
  have hfac : α = kernel.lift β α hαβ ≫ kernel.ι β := (kernel.lift_ι β α hαβ).symm
  rw [hfac, cohomologyOverFieldMap_comp]
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp] using h₁.comp h₂

/-- **A nonzero first cohomology makes `H¹(X, ω) ⟶ H¹(X, ℱ)` an isomorphism.** A surjection out
of the one-dimensional space `H¹(X, ω)` onto a nonzero space is bijective. -/
public theorem bijective_cohomologyOverFieldMap_one_of_exact
    (hH2 : S.SecondCohomologyVanishing) {ω F Q : S.X.Modules} (α : ω ⟶ F) (β : F ⟶ Q)
    (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β]
    (hQ : IsZero (cohomologyOverField S.k S.f Q 1))
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (hF : ¬ IsZero (cohomologyOverField S.k S.f F 1)) :
    Function.Bijective (cohomologyOverFieldMap S.k S.f α 1).hom :=
  bijective_of_surjective_of_finrank_eq_one _
    (surjective_cohomologyOverFieldMap_one_of_exact hH2 α β hαβ hex hQ) hone
    fun h => hF (@ModuleCat.isZero_of_subsingleton _ _
      (cohomologyOverField S.k S.f F 1) h)

/-- **The universal property of the dualizing sheaf produces a retraction of `ω ⟶ ℱ`.** If
`H¹(X, ω) ⟶ H¹(X, ℱ)` is bijective then the `k`-linear functional on `H¹(X, ℱ)` obtained by
transporting the one that corresponds to `𝟙 ω` corresponds to a map `ℱ ⟶ ω` whose composite
with `ω ⟶ ℱ` induces the identity on `H¹(X, ω)`, hence is the identity. -/
public theorem exists_retraction_of_bijective {ω F : S.X.Modules} (hωq : ω.IsQuasicoherent)
    (hFq : F.IsQuasicoherent) (hdual : S.FirstCohomologyDuality ω) (α : ω ⟶ F)
    (hbij : Function.Bijective (cohomologyOverFieldMap S.k S.f α 1).hom) :
    ∃ φ : F ⟶ ω, α ≫ φ = 𝟙 ω := by
  set e := LinearEquiv.ofBijective (cohomologyOverFieldMap S.k S.f α 1).hom hbij with he
  refine ⟨(hdual.dual F hFq).symm ((hdual.dual ω hωq (𝟙 ω)).comp e.symm.toLinearMap), ?_⟩
  refine (hdual.dual ω hωq).injective ?_
  rw [hdual.dual_comp ω F hωq hFq α _, AddEquiv.apply_symm_apply]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show (cohomologyOverFieldMap S.k S.f α 1).hom x = e x from rfl, e.symm_apply_apply]

/-- **The splitting of [Stacks, Tag 0B5E] for any `ω` with the three properties it uses.** In
Situation [Stacks, Tag 0B5D], let `ω` be a quasi-coherent module and let `ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` be
an exact sequence of `𝒪_X`-modules with `H¹(X, 𝒬) = 0`. Then either `H¹(X, ℱ) = 0`, or the
sequence splits and `ℱ ≅ ω ⊕ 𝒬` compatibly with both of its arrows.

If `H¹(X, ℱ) ≠ 0` then `H¹(X, ω) ⟶ H¹(X, ℱ)` is surjective, hence bijective because
`dim_k H¹(X, ω) = 1`; the universal property of `ω` turns the inverse into a retraction of
`ω ⟶ ℱ`; and a retraction splits the sequence.

Clause (5) of [Stacks, Tag 0BS2], the representability of `ω`, is the carried hypothesis
`hdual`; `dim_k H¹(X, ω) = 1`, which the source reads off the duality of Section
[Stacks, Tag 0B5B], is the carried hypothesis `hone`; and the vanishing of `H²(X, -)` of
[Stacks, Tag 02UZ] is the carried hypothesis `hH2`. All three hold for the dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`, and [Stacks, Tag 0B5E] itself is
`isZero_firstCohomology_or_iso_biprod_dualizingSheafOverField` in
`Curves/VanishingResults/DualizingSheafExtension.lean`. -/
public theorem isZero_firstCohomology_or_iso_biprod {ω F Q : S.X.Modules}
    (hωq : ω.IsQuasicoherent) (hFq : F.IsQuasicoherent)
    (hdual : S.FirstCohomologyDuality ω) (hH2 : S.SecondCohomologyVanishing)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1) (α : ω ⟶ F) (β : F ⟶ Q)
    (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β]
    (hQ : IsZero (cohomologyOverField S.k S.f Q 1)) :
    IsZero (cohomologyOverField S.k S.f F 1) ∨
      ∃ e : F ≅ ω ⊞ Q, α ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = β := by
  by_cases hF : IsZero (cohomologyOverField S.k S.f F 1)
  · exact Or.inl hF
  obtain ⟨φ, hφ⟩ := exists_retraction_of_bijective hωq hFq hdual α
    (bijective_cohomologyOverFieldMap_one_of_exact hH2 α β hαβ hex hQ hone hF)
  set sp := ShortComplex.Splitting.ofExactOfRetraction
    (ShortComplex.mk α β hαβ) hex φ hφ ‹Epi β› with hsp
  refine Or.inr ⟨sp.isoBinaryBiproduct, ?_, ?_⟩
  · refine biprod.hom_ext _ _ ?_ ?_
    · simpa using sp.f_r
    · simpa using hαβ
  · simp

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
