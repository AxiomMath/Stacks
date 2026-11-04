module

public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Consumers

/-!
# Section extension off a nonvanishing locus: Stacks Tag 01PW and clause (3) of Tag 01Q3

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `s` a global section of a tensor power of
`L`, and `X_s` its nonvanishing locus. Stacks Tag 01PW compares the degree-zero part of the
localisation of the graded section ring `Γ_*(X, L)` at `s` with the functions on `X_s`:

* for `X` quasi-compact the comparison map is injective, and
* for `X` quasi-compact and quasi-separated it is an isomorphism.

The half every consumer in this repository is waiting for is the **surjectivity**: a function on
`X_s` becomes, after multiplication by a power of `s`, the restriction of a global section of a
power of `L`. This file states that half, as
`Stacks.SectionExtension.IsSectionRatio`, and spends it: the premises
`Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` and
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing` of the ample cluster are proved from it here, and
with them clauses (3) and (4) of Stacks Tag 01Q3 and the equivalence of both with ampleness.

## Main definitions

* `Stacks.SectionExtension.IsSectionRatio`: **the surjectivity half of Stacks Tag 01PW**, in the
  shape the consumers use. Every function on an `X_s` is the ratio `t / σ` of two global sections
  of one and the same tensor power of `L`, with `σ` nowhere vanishing on `X_s`. **No affineness of
  `X_s` is assumed**, matching the source lemma, whose hypotheses are on `X` alone.

## Main results

* `Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen`: **unconditional, and the geometric
  step the reduction turns on.** If a global section `t` of an invertible module restricts on an
  open `U` to `g • σ|_U`, for `σ` a global section of the same module nowhere vanishing on `U`,
  then `X_t ⊓ U` is the basic open of `g`. This is the statement that turns a ratio of global
  sections into a basic open and back.
* `Stacks.SectionExtension.exists_powNonvanishingOpen_eq_basicOpen`: **every basic open of an
  `X_s` is an `X_t`**, on the premise, with no affineness hypothesis on `X_s`. This is
  `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` stated without importing that file, and it
  implies `Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, which is the same statement restricted
  to an affine `X_s`; both identifications are made in `Consumers.lean`.
* `Stacks.SectionExtension.isBasisNonvanishing_of_isSectionRatio`: **clause (1) implies clause
  (3) of Stacks Tag 01Q3** on the premise, and
  `Stacks.SectionExtension.isBasisAffineNonvanishing_of_isSectionRatio` clause (4), Stacks Tag
  01PX being unconditional in this repository.
* `Stacks.SectionExtension.isAmple_iff_isBasisNonvanishing`,
  `Stacks.SectionExtension.isAmple_iff_isBasisAffineNonvanishing`: the three-way equivalence
  (1) ⟺ (3) ⟺ (4) of Stacks Tag 01Q3 for an arbitrary invertible module, on the premise and
  nothing else.
* `Stacks.SectionExtension.exists_tensorPow_section_nonvanishingLocus_eq`: the vocabulary bridge
  from a homogeneous element of the section ring back to an honest global section of
  `Stacks.Ample.tensorPowModule`. `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq` is
  the other direction; both are needed, since the premise and its consumers are stated over the
  tensor powers while `X_{st} = X_s ⊓ X_t` is stated over the section ring.

## Why the premise is stated as a ratio rather than as a power of `s`

Stacks Tag 01PW produces, for `g` a function on `X_s` with `s` of degree `d`, an integer `m ≥ 1`
and a global section `t` of `L ^⊗ (m d)` with `t|_{X_s} = g • s^m|_{X_s}`. The denominator `s^m`
plays no part in anything downstream beyond being a global section of the **same** power as `t`
which does not vanish on `X_s`; so `IsSectionRatio` asks for a denominator `σ` with those two
properties and nothing more. Tag 01PW implies it, with `σ = s^m`, because `X_{s^m} = X_s`
(`Stacks.AmpleFiniteAvoidance.nvLocus_mul` by induction). Stating it this way keeps the power
operation on homogeneous sections — which this repository does not have as a definition, only as
the existence statements of `Stacks.AmpleAffineAvoidance.Powers` — out of the premise and out of
the reduction.

The weakening is not a vacuity. Taking `p = 0` and `σ` a nowhere-vanishing section of `𝒪_X`
would ask `g` to be the restriction of a *global function*, which is strictly stronger than Tag
01PW; the content of the premise is exactly that `g` lies in the image of
`Γ_*(X, L)_{(σ)} → Γ(X_s, 𝒪_X)` for some admissible denominator.

## What is not done

**`Stacks.SectionExtension.IsSectionRatio` is not proved in the generality in which it is
stated.** It is the surjectivity half of Stacks Tag 01PW; no Stacks attribute is attached anywhere
in this file, because the only label whose content is at stake here is 01PW and 01PW is assumed,
not proved. `StacksFrontier/AlgebraicGeometry/SectionExtension/Ample.lean` proves it for an
**ample** `L` (`Stacks.SectionExtension.isSectionRatio_of_isAmple`), which is what every consumer
of the ample cluster needs except part (2) of Stacks Tag 0892, where the module the premise is
applied to is a pullback whose ampleness is the conclusion. The case of an arbitrary invertible
module on a quasi-compact quasi-separated scheme — 01PW's own hypothesis — is open. The source's
proof is a gluing argument over a finite affine cover and its four steps are these, in the
vocabulary this repository has:

1. *The cover.* For `L` ample, `X` is covered by finitely many **affine** `X_{a_i}`
   (`Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen` with `CompactSpace X`), and the
   degrees can be made equal by `Stacks.AmpleAffineAvoidance.exists_common_degree`. Taking the
   cover to consist of nonvanishing loci is what makes the rest work: on `X_{a_i}` the section
   `a_i` and **each of its powers** is a basis of the corresponding tensor power, by
   `Stacks.NonvanishingSpelling.bijective_smul`, so no trivialisation of a tensor power over a
   local open is needed anywhere — that absence, recorded as the wall in two other files, is not
   on the critical path.
2. *The local extension.* On `V := X_{a_i}`, writing `s|_V = f_i • a_i|_V`, one has
   `V ⊓ X_s = X.basicOpen f_i` by `nonvanishingOpen_inf_eq_basicOpen` below, and `V` is affine, so
   `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` gives `e_i` and `c_i : Γ(X, V)` with
   `c_i|_{X.basicOpen f_i} = f_i^{e_i} * g|`. Finitely many `i`, so `k := max e_i + 1` is
   available.
3. *The powers.* One then needs `(s^k)|_V = f_i^k • (a_i^k)|_V`. **This step is done**, in
   `Powers.lean`: `Stacks.SectionExtension.powSec` is the power operation on homogeneous sections
   that `Stacks.GradedSections` lacks, and
   `Stacks.SectionExtension.resTop_globalSection_powSec` is the identity.
4. *Gluing.* The local sections agree on `X_{a_i} ⊓ X_{a_j}`, which is **affine** by Stacks Tag
   01PV (`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nvOpen`), after multiplication by
   a further power of `s`; the exponent comes from
   `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`, which is the
   injectivity half of Tag 01PW in the only case the argument needs. They then glue by
   `TopCat.Sheaf.existsUnique_gluing'` applied to `⟨M.presheaf, M.isSheaf⟩`.

Steps 1 to 4 are carried out in `Ample.lean`, for `L` ample. Step 3 is done there with
`Stacks.TensorPowerTrivialize.sectionPow` rather than with `Stacks.SectionExtension.powSec` of
`Powers.lean`: the two are the same power operation indexed differently, and the former's indexing
keeps `Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow` free of hypotheses.
`GloballyTrivial.lean` proves the premise outright in the case where every tensor power of `L` has
a nowhere-vanishing global basis, which is the quasi-affine case.

**Quasi-separatedness of `X` is not discharged anywhere, and the ample case does not need it.**
The source needs it for part (2) of Tag 01PW and this repository cannot produce it from ampleness:
that is Properties 28.27.8, which is absent, and the route through
`QuasiSeparatedSpace.of_isTopologicalBasis` would need clause (4) of Tag 01Q3, which is what is
being proved. `GloballyTrivial.lean` therefore carries it as an explicit hypothesis. `Ample.lean`
avoids it altogether: its overlaps `X_{a i} ⊓ X_{a j}` are affine by Stacks Tag 01PV, so the
affine form of the annihilator lemma suffices where the source uses the Qcqs form.

**The injectivity half of Tag 01PW is not stated.** It is needed only through step 4, where
Mathlib's statement about an affine open suffices.

**No module-valued form is stated.** Stacks Tag 01PW is about an arbitrary quasi-coherent
`𝓕`, and what is here is the case `𝓕 = 𝒪_X`: the conclusion is an equation between *scalar*
multiples, `t|_U = g • σ|_U`. The general form asserts `s'|_{X_σ} = s ⊗ σ^e` in
`Γ(𝓕 ⊗ N^⊗e, X_σ)`, and this repository has no tensor product of *sections* — only the
sheafified tensor product of modules, with `Stacks.SectionProduct`'s own record that the
sectionwise multiplication clause of Tag 01CV is unproved for exactly that reason. The machinery
used here, `Stacks.GradedSections.mulMap` and `Stacks.SectionExtension.powSec`, exists only for
the tensor powers of one invertible module, so the module-valued form is not a restatement of
this but a separate development.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [EGA I, Section 6.8]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance

universe u

namespace Stacks.SectionExtension

/-! ### The nonvanishing locus of a known ratio -/

section Ratio

variable {X : Scheme.{u}} {M : X.Modules}

/-- Restriction of a global section of an `𝒪_X`-module to an open. -/
noncomputable abbrev resTop (U : X.Opens) (t : Γ(M, ⊤)) : Γ(M, U) :=
  M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t

variable [IsInvertibleModule X M]

/-- **A section does not vanish where its ratio by a nonvanishing section is a unit.** For `σ`
a global section of an invertible `𝒪_X`-module not vanishing anywhere on `U`, and `t` a global
section of the same module whose restriction to `U` is `g • σ|_U`, the locus `X_t` meets `U`
exactly where `g` generates.

This is the pointwise form of `nonvanishingOpen_inf_eq_basicOpen`; the proof is the one
`Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit` runs for the basis section of a
sectionwise trivialisation, with that basis section replaced by `σ`, which is legitimate because
the only property of it used is that it does not lie in `𝔪_y · M_y`. -/
theorem mem_nonvanishingLocus_iff_isUnit_of_res_eq (σ t : Γ(M, ⊤)) {U : X.Opens}
    (hU : U ≤ nonvanishingOpen X M σ) {g : Γ(X, U)} (h : resTop U t = g • resTop U σ) {y : X}
    (hy : y ∈ U) :
    y ∈ nonvanishingLocus M t ↔ IsUnit ((X.presheaf.germ U y hy).hom g) := by
  have hg : (M.presheaf.Γgerm y).hom t =
      (X.presheaf.germ U y hy).hom g • (M.presheaf.Γgerm y).hom σ := by
    rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : U ≤ ⊤)) M.presheaf y hy t,
      show M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t = g • resTop U σ from h, germ_smul,
      TopCat.Presheaf.Γgerm_res_apply]
  rw [mem_nonvanishingLocus_iff, hg, smul_mem_maximalSmul_iff, not_or, not_not]
  exact and_iff_left (hU hy)

/-- **A ratio of global sections of one invertible module is a basic open.** If `σ` does not
vanish on `U` and `t|_U = g • σ|_U`, then `X_t ⊓ U = X.basicOpen g`.

This is the geometric content of Stacks Tag 01PW read backwards, and it is what makes the
surjectivity half of that lemma produce a nonvanishing locus: the containment
`X.basicOpen g ≤ U` is automatic, so no intersection survives on the right. No affineness and no
quasi-compactness are used. -/
theorem nonvanishingOpen_inf_eq_basicOpen (σ t : Γ(M, ⊤)) {U : X.Opens}
    (hU : U ≤ nonvanishingOpen X M σ) (g : Γ(X, U)) (h : resTop U t = g • resTop U σ) :
    nonvanishingOpen X M t ⊓ U = X.basicOpen g := by
  have key (y) (hyU : y ∈ U) : y ∈ nonvanishingLocus M t ↔ y ∈ X.basicOpen g :=
    (mem_nonvanishingLocus_iff_isUnit_of_res_eq σ t hU h hyU).trans (X.mem_basicOpen g y hyU).symm
  exact Opens.ext (Set.ext fun y =>
    (and_congr_left (key y)).trans (and_iff_left_of_imp (X.basicOpen_le g ·)))

end Ratio

/-! ### The vocabulary bridge, from the section ring to the tensor powers -/

section Bridge

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The vocabulary bridge, the direction `Stacks.AmpleFiniteAvoidance` does not state.** A
homogeneous element of the section ring of degree `n` is an honest global section of the `n`-th
integer tensor power of `L`, with the same nonvanishing locus. The two modules are *equal* by
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`, so the comparison is an `eqToIso` and
`Stacks.Ample.nonvanishingLocus_congr` transports the locus. -/
theorem exists_tensorPow_section_nonvanishingLocus_eq (n : ℕ)
    (a : Stacks.GradedSections.powSections L n) :
    ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      nonvanishingLocus (tensorPowModule X L (n : ℤ)) s = nvLocus L a := by
  have heq : (Stacks.TensorPowers.natTensorPow L n : X.Modules) = tensorPowModule X L (n : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n
  let e : (Stacks.TensorPowers.natTensorPow L n : X.Modules) ≅ tensorPowModule X L (n : ℤ) :=
    eqToIso (C := X.Modules) heq
  exact ⟨e.hom.app ⊤ (Stacks.SectionProduct.globalSection X _ a),
    nonvanishingLocus_congr e (Stacks.SectionProduct.globalSection X _ a)⟩

/-- **`X_t ⊓ X_s` is an `X_u`, with `u` a global section of a tensor power.** The product of
Stacks Tag 01CV lives in the section ring, so this is `X_{st} = X_s ⊓ X_t`
(`Stacks.AmpleFiniteAvoidance.nvLocus_mul`) carried across the bridge in both directions. The
degree is `p + n`, so it is positive as soon as one of the two is. -/
theorem exists_powNonvanishingOpen_eq_inf (n p : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
    (t : Γ(tensorPowModule X L (p : ℤ), ⊤)) :
    ∃ u : Γ(tensorPowModule X L ((p + n : ℕ) : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen X L (p + n) u =
        Stacks.AmpleTheory.powNonvanishingOpen X L p t ⊓
          Stacks.AmpleTheory.powNonvanishingOpen X L n s := by
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨b, hb⟩ := exists_powSections_nvLocus_eq L p t
  obtain ⟨u, hu⟩ := exists_tensorPow_section_nonvanishingLocus_eq L (p + n)
    (Stacks.GradedSections.mul b a)
  refine ⟨u, TopologicalSpace.Opens.ext ?_⟩
  rw [Stacks.AmpleTheory.coe_powNonvanishingOpen, hu, nvLocus_mul, ha, hb, Opens.coe_inf,
    Stacks.AmpleTheory.coe_powNonvanishingOpen, Stacks.AmpleTheory.coe_powNonvanishingOpen]

end Bridge

/-! ### Stacks Tag 01PW, the surjectivity half -/

section Premise

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **The surjectivity half of Stacks Tag 01PW**, in the shape the consumers of the ample cluster
use it in. For every `X_s`, with `s` a global section of a positive tensor power of `L`, and every
function `g` on `X_s`, there is a tensor power `L ^⊗ p` and a pair of global sections `t`, `σ` of
it with `σ` nowhere vanishing on `X_s` and `t|_{X_s} = g • σ|_{X_s}`: that is, `g` is the ratio
`t / σ`.

**`X_s` carries no affineness hypothesis.** Tag 01PW has none, and part (2) of Stacks Tag 0892
needs the conclusion where `X_s` is only quasi-affine, so the affineness-restricted form
(`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`) cannot serve it. The restricted form follows
from this one by discarding the hypothesis.

Tag 01PW gives this with `σ = s^m` and `p = m d`; see the module documentation for why the
denominator is left general, and for why the generalisation is not a vacuity.

**No hypothesis on `X` is written into the predicate**, so this is a statement about `X` that is
only expected to hold when `X` is quasi-compact and quasi-separated — part (2) of Tag 01PW needs
both. Every consumer below also holds `Stacks.Ample.IsAmple X L`, which supplies quasi-compactness
outright and quasi-separatedness by Stacks Tag 01PY, so the predicate is applied only where the
source lemma asserts it; `Consumers.lean` keeps the ampleness hypothesis attached where the
premise has to be quantified over all schemes. -/
def IsSectionRatio : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
    ∀ g : Γ(X, Stacks.AmpleTheory.powNonvanishingOpen X L n s),
      ∃ (p : ℕ) (t σ : Γ(tensorPowModule X L (p : ℤ), ⊤)),
        Stacks.AmpleTheory.powNonvanishingOpen X L n s ≤
            Stacks.AmpleTheory.powNonvanishingOpen X L p σ ∧
          resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) t =
            g • resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ

/-- **Every basic open of an `X_s` is itself an `X_u`**, for `u` a global section of a positive
tensor power of `L`, on the premise `Stacks.SectionExtension.IsSectionRatio`. No affineness of
`X_s` is used.

This is the statement `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow`, written out so that nothing
here depends on that file; `Consumers.lean` records that the two agree and that it implies
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`. The proof is the product
trick: the premise writes `g` as `t / σ` on `X_s`, so `X_t ⊓ X_s = X.basicOpen g` by
`nonvanishingOpen_inf_eq_basicOpen`, and `X_t ⊓ X_s` is the nonvanishing locus of the product
`t s` in the section ring. -/
theorem exists_powNonvanishingOpen_eq_basicOpen (h : IsSectionRatio X L) (n : ℕ) (hn : 1 ≤ n)
    (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
    (g : Γ(X, Stacks.AmpleTheory.powNonvanishingOpen X L n s)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u : Γ(tensorPowModule X L (m : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen X L m u = X.basicOpen g := by
  obtain ⟨p, t, σ, hσ, hratio⟩ := h n hn s g
  obtain ⟨u, hu⟩ := exists_powNonvanishingOpen_eq_inf L n p s t
  refine ⟨p + n, by omega, u, ?_⟩
  rw [hu]
  exact nonvanishingOpen_inf_eq_basicOpen σ t hσ g hratio

end Premise

/-! ### Clauses (3) and (4) of Stacks Tag 01Q3 -/

section Clauses

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **Stacks Tag 01Q3, clause (1) implies clause (3)**, on the premise
`Stacks.SectionExtension.IsSectionRatio`: for `L` ample the opens `X_s`, with `s` a global section
of a positive tensor power, form a basis for the topology of `X`.

Ampleness puts an *affine* `X_s` through the given point; the basic opens of an affine open are a
basis of it, so a basic open of that `X_s` lies between the point and the prescribed open; and
`exists_powNonvanishingOpen_eq_basicOpen` says that basic open is itself an `X_u`. The source
reaches this clause only through clause (2) and the open immersion into `Proj Γ_*(X, L)`; neither
appears here. -/
theorem isBasisNonvanishing_of_isSectionRatio (h : IsSectionRatio X L) (hL : IsAmple X L) :
    Stacks.AmpleTheory.IsBasisNonvanishing X L := by
  intro x U hx
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨g, hgU, hxg⟩ := haff.exists_basicOpen_le (V := U) ⟨x, hx⟩ hxs
  obtain ⟨m, hm, u, hmu⟩ := exists_powNonvanishingOpen_eq_basicOpen X L h n hn s g
  exact ⟨m, hm, u, hmu ▸ hxg, hmu ▸ hgU⟩

/-- **Stacks Tag 01Q3, clause (1) implies clause (4)**, on the premise
`Stacks.SectionExtension.IsSectionRatio`: the affine `X_s` form a basis for the topology. Clause
(3) above, followed by Stacks Tag 01PX, which is unconditional in this repository since Tag 01PV
is proved. -/
theorem isBasisAffineNonvanishing_of_isSectionRatio (h : IsSectionRatio X L) (hL : IsAmple X L) :
    Stacks.AmpleTheory.IsBasisAffineNonvanishing X L :=
  Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing X L
    (isBasisNonvanishing_of_isSectionRatio X L h hL)

/-- **Stacks Tag 01Q3, (1) if and only if (3)**, for an arbitrary invertible `𝒪_X`-module, on the
premise `Stacks.SectionExtension.IsSectionRatio` and nothing else. The converse direction needs no
premise: it is Stacks Tag 01PX followed by Tag 01PV. -/
theorem isAmple_iff_isBasisNonvanishing (h : IsSectionRatio X L) :
    IsAmple X L ↔ CompactSpace X ∧ Stacks.AmpleTheory.IsBasisNonvanishing X L :=
  ⟨fun hL => ⟨hL.1, isBasisNonvanishing_of_isSectionRatio X L h hL⟩, fun hb =>
    Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X L hb.1
      (Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing
        X L hb.2)⟩

/-- **Stacks Tag 01Q3, (1) if and only if (4)**, for an arbitrary invertible `𝒪_X`-module, on the
premise `Stacks.SectionExtension.IsSectionRatio`.
`Stacks.AmpleTheory.isAmple_iff_isBasisAffineNonvanishing` proves the same equivalence for a
module with a nowhere-vanishing global basis in every degree, which is a strong restriction; this
drops it. -/
theorem isAmple_iff_isBasisAffineNonvanishing (h : IsSectionRatio X L) :
    IsAmple X L ↔ CompactSpace X ∧ Stacks.AmpleTheory.IsBasisAffineNonvanishing X L :=
  ⟨fun hL => ⟨hL.1, isBasisAffineNonvanishing_of_isSectionRatio X L h hL⟩, fun hb =>
    Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X L hb.1 hb.2⟩

end Clauses

end Stacks.SectionExtension

end
