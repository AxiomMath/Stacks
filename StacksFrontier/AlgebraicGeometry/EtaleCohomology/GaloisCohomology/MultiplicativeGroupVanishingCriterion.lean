module

public import Mathlib.FieldTheory.KrullTopology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProductSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Hilbert90
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import StacksCore.Tactic.StacksAttribute

/-!
# Galois cohomology of the units of a Galois extension under a Brauer hypothesis

Let `K` be a field with separable algebraic closure `Kˢᵉᵖ` and absolute Galois group
`G = Gal(Kˢᵉᵖ/K)`, and assume that `Br(K') = 0` for every finite extension `K'/K`. Stacks 03R8
(Serre, *Galois Cohomology*, Chapter II, Section 3, Proposition 5) asserts two things:

1. `H^q(G, (Kˢᵉᵖ)^*) = 0` for every `q ≥ 1`;
2. `H^q(G, M) = 0` for every torsion `G`-module `M` and every `q ≥ 2`.

**Part (1) is what this file delivers**, and for an arbitrary Galois extension `Ω/K` rather than
only for `Ω = Kˢᵉᵖ`; part (2) is not delivered here, and the implementation notes say why. Along
the way the discrete Galois module `Ωˣ` is constructed, as an object of the category of Stacks
04JP in which this library's continuous group cohomology (Stacks 04JR,
`continuousGroupCohomology`) takes its coefficients; it did not exist before.

## Main definitions

* `Stacks.GaloisCohomology.unitsContinuousGModule`: the discrete `Gal(Ω/K)`-module
  `Additive Ωˣ`, with its Krull-topology continuity.

## Main results

* `Stacks.GaloisCohomology.isContinuous_ofMulDistribMulAction_units`: the action of `Gal(Ω/K)` on
  `Ωˣ` is continuous for the Krull topology, the stabiliser of a unit containing the open
  subgroup fixing the simple extension it generates.
* `Stacks.GaloisCohomology.isMulCoboundary₂_of_brauerGroup_eq_one`: **Stacks 03R8 part (1) in
  degree two, in cocycle form, unconditionally.**
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units`: **Stacks 03R8 part (1)** for
  every `q ≥ 1`, over the three hypotheses `h03QU₁`, `h03QU₂` and `hhigh` described below.

## Implementation notes

**Why an arbitrary Galois extension.** Everything below is stated for a Galois extension `Ω/K`
and specialises to the tag at `Ω = Kˢᵉᵖ`, so the statements are more general than the tag rather
than narrower. The generality is also what keeps them usable: `SeparableClosure K` unfolds to
`separableClosure K (AlgebraicClosure K)`, and finding the action of `Gal(Ω/K)` on `Ωˣ` through
that unfolding exhausts the default instance-search budget — which is why
`Stacks.GaloisCohomology.isMulCoboundary₂_separableClosure_of_forall_brauer` has to raise it.
At a type variable `Ω` the search is immediate.

**Degrees one and two are proved, not carried.** In degree one the cocycle statement is Hilbert's
theorem 90 for an infinite Galois extension, which this library has unconditionally as
`Stacks.GaloisCohomology.isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁` and which needs
no hypothesis on Brauer groups at all. In degree two it is
`Stacks.GaloisCohomology.isMulCoboundary₂_of_forall_finiteGalois` fed with
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauer`, the crossed-product argument at each finite
Galois subextension; the tag's hypothesis supplies its premise at once, since `Br(K) = 0` makes
every relative Brauer group `Br(L/K)` vanish. So under the tag's hypothesis the degree-one and
degree-two statements of part (1) hold outright, in the explicit cocycle vocabulary, and the
degree-two one is recorded separately as
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauerGroup_eq_one` — stated from `Br(K) = 0` alone,
which is weaker than the tag's hypothesis.

**The three carried hypotheses.**

* `h03QU₁` and `h03QU₂`: the comparison, in degrees one and two, between the explicit cocycle
  description of Galois cohomology and the derived-functor description
  `continuousGroupCohomology` of Stacks 04JR — in each degree, the vanishing of the cocycle
  quotient implies the vanishing of the derived-functor group. The two descriptions are **not**
  related anywhere in this library above degree zero, as recorded in the module documentation of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TwoCocycleInflation` and of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GaloisCohomologyFunctionField`. The
  degree-zero comparison is `Stacks.GroupCohomology.invariantsIsoZerothCohomology`, and nothing
  above it exists. This is the standard comparison of the standard complex with the right
  derived functor, not a Stacks tag of its own.
* `hhigh`: the vanishing in degrees `q ≥ 3`. This is the one part of part (1) that is carried
  wholesale. The source obtains it from part (2) together with the four-term exact sequence
  `0 → A → M → M ⊗ 𝐐 → B → 0` for `M = Ωˣ`, in which `A` and `B` are torsion — so part (2) kills
  their cohomology in degrees `≥ 2` — and `M ⊗ 𝐐` has vanishing cohomology in positive degree.
  That last input **is** in this library, as `isZero_continuousGroupCohomology_of_module_rat`
  (Stacks 0DV3 part (2)), so the obstruction is not the divisible-coefficient step: it is part
  (2) itself, together with the construction of `M ⊗ 𝐐` as a discrete Galois module and the long
  exact sequence of `continuousGroupCohomology` attached to the two short exact sequences the
  four-term sequence splits into. Neither of those is present.

**Part (2) is not delivered.** Its proof in the source is an `ℓ`-primary decomposition of the
torsion module, compatibility of cohomology with filtered colimits, the Kummer sequence
(Stacks 03PL) for `ℓ ≠ char K`, the Artin–Schreier sequence (Stacks 0A3J) for `ℓ = char K`, and
Stacks 0DV9 — the reduction of a vanishing statement to the fixed field of a maximal pro-`ℓ`
subgroup — applied over fields written as filtered colimits of finite extensions. Of these the
library has none: Stacks 0DV9 is not formalized, there is no compatibility of
`continuousGroupCohomology` with filtered colimits, and the `ℓ`-primary decomposition of a
discrete torsion Galois module is not constructed. Stating part (2) over its own conclusion
would be a tautology, and no genuine reduction of it is available here, so it is not stated.

**Universes and local instances.** `continuousGroupCohomology.{u, v}` takes coefficients in
`ContinuousGModule.{u, max u v} G` for `G : Type u`; with `K Ω : Type u` both `Gal(Ω/K)` and
`Additive Ωˣ` live in `Type u`, so the instantiation is `continuousGroupCohomology.{u, u}`.
`HasDerivedCategory.standard` and the forgetful functor from `ℤ`-modules to spaces with the
discrete topology are made local instances, exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules`, where they are
local as well.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): the proposition; part
  (1) is delivered here and part (2) is not.
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category of
  discrete `G`-modules, in which `unitsContinuousGModule` is built.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): continuous group
  cohomology, the groups in which part (1) is stated.
* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7): the identification of
  the Brauer group with `H^2`, of which the direction used in degree two is the
  crossed-product argument.
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3): the torsion and
  divisible-coefficient statements for a profinite group, proved, and the one input of the
  source's degrees `≥ 3` argument that is available.
* [Stacks Project, Tag 0DV9](https://stacks.math.columbia.edu/tag/0DV9),
  [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL) and
  [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the inputs of part (2),
  none of which is in the library.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField groupCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.GaloisCohomology

/-- `ℤ`-modules are regarded as topological spaces with the discrete topology, which is what
makes continuity of an action of a topological group on them a meaningful condition. This is the
local instance of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules`, repeated here
because it is local there. -/
local instance : HasForget₂ (ModuleCat.{u} ℤ) TopCat.{u} :=
  { forget₂ := forget (ModuleCat.{u} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-! ### The discrete Galois module of units of a Galois extension -/

/-- **The action of `Gal(Ω/K)` on `Ωˣ` is continuous** for the Krull topology, `Ω/K` being
Galois. By the standard reformulation of continuity for a discrete module it is enough that each
stabiliser be open, and the stabiliser of a unit `u` contains the subgroup fixing the simple
extension `K⟮u⟯`, which is finite over `K` because `Ω/K` is algebraic and is therefore an open
subgroup of `Gal(Ω/K)`. -/
theorem isContinuous_ofMulDistribMulAction_units :
    (Stacks.GroupCohomology.actionOfRepresentation ℤ Gal(Ω/K) (Additive Ωˣ)
      (Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ)).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  intro x
  obtain ⟨u, rfl⟩ : ∃ u : Ωˣ, Additive.ofMul u = x := ⟨x.toMul, rfl⟩
  have hfd : FiniteDimensional K K⟮(u : Ω)⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (u : Ω))
  have hle : (K⟮(u : Ω)⟯).fixingSubgroup ≤ MulAction.stabilizer Gal(Ω/K) u := by
    intro g hg
    simp only [IntermediateField.mem_fixingSubgroup_iff] at hg
    have hga : g (u : Ω) = (u : Ω) :=
      hg (u : Ω) (IntermediateField.mem_adjoin_simple_self K (u : Ω))
    refine MulAction.mem_stabilizer_iff.mpr (Units.val_inj.mp ?_)
    simpa using hga
  have hset : {g : Gal(Ω/K) |
        Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ g (Additive.ofMul u) =
          Additive.ofMul u}
      = ((MulAction.stabilizer Gal(Ω/K) u : Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h ↦ Additive.ofMul.injective h, fun h ↦ congrArg Additive.ofMul h⟩
  rw [hset]
  exact Subgroup.isOpen_mono hle (K⟮(u : Ω)⟯).fixingSubgroup_isOpen

/-- **Stacks Project, Tag 04JP at the units of a Galois extension.** The multiplicative group of
`Ω`, written additively, as a discrete `Gal(Ω/K)`-module. At `Ω = Kˢᵉᵖ` these are the
coefficients of part (1) of Stacks 03R8, and this is the object at which this library's
continuous group cohomology of Stacks 04JR evaluates to the groups
`H^q(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)^*)`. -/
def unitsContinuousGModule : ContinuousGModule.{u, u} Gal(Ω/K) :=
  Stacks.GroupCohomology.ofRepresentation
    (Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ)
    (isContinuous_ofMulDistribMulAction_units K Ω)

/-! ### Stacks 03R8, part (1) -/

/-- **Stacks Project, Tag 03R8, part (1) in degree two**, in explicit cocycle form and with no
carried hypothesis: if `Br(K) = 0` then every locally constant `2`-cocycle on `Gal(Ω/K)` with
values in `Ωˣ` is a coboundary, which is the vanishing of `H^2(Gal(Ω/K), Ωˣ)`. At `Ω = Kˢᵉᵖ` this
is the degree-two case of the tag.

The hypothesis is weaker than the tag's, which asks for the Brauer group of every finite
extension of `K`: only `Br(K) = 0` is used, because it already makes every relative Brauer group
`Br(L/K)` vanish, which is the premise of
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauer` at each finite Galois subextension `L` of
`Ω`. -/
@[stacks 03R8 "part (1) in degree two, in explicit cocycle form, UNCONDITIONAL -- nothing is
carried. Under the tag's Brauer hypothesis every locally constant 2-cocycle of the Galois group
with values in the units is a coboundary, which is the vanishing of H^2(Gal(Ω/K), Ωˣ); at
Ω = K^sep this is the tag's degree-two case. Proved from
isMulCoboundary₂_of_forall_finiteGalois fed with the crossed-product argument
isMulCoboundary₂_of_brauer, whose premise the tag's hypothesis discharges at once since
Br(K) = 0 forces every relative Brauer group Br(L/K) to vanish. The hypothesis used here is only
Br(K) = 0, which is weaker than the tag's, and Ω is an arbitrary Galois extension rather than
the separable closure, so this is more general than the tag's degree-two case rather than
narrower. NOT proved here: the other degrees of part (1), for which see
isZero_continuousGroupCohomology_units, and part (2)"]
theorem isMulCoboundary₂_of_brauerGroup_eq_one (hBr : ∀ y : BrauerGroup K, y = 1)
    (f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (hloc : IsLocallyConstant f) (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ f :=
  isMulCoboundary₂_of_forall_finiteGalois
    (fun _ F hF ↦ isMulCoboundary₂_of_brauer (fun y _ ↦ hBr y) F hF) f hloc hf

/-- **Stacks Project, Tag 03R8, part (1).** Let `K` be a field with `Br(K) = 0` and let `Ω/K` be
a Galois extension. Then

`H^q(Gal(Ω/K), Ωˣ) = 0` for every `q ≥ 1`,

the groups being this library's continuous group cohomology of Stacks 04JR evaluated at the
discrete Galois module `Stacks.GaloisCohomology.unitsContinuousGModule`. At `Ω = Kˢᵉᵖ` this is
part (1) of the tag.

Three inputs are carried. `h03QU₁` and `h03QU₂` are the comparison, in degrees one and two,
between the cocycle description of Galois cohomology and the derived-functor description: the
vanishing of the cocycle quotient implies the vanishing of `continuousGroupCohomology`. The two
descriptions are not related anywhere in this library above degree zero. `hhigh` is the
vanishing in degrees `q ≥ 3`, which the source deduces from part (2) of the tag through the
four-term sequence `0 → A → M → M ⊗ 𝐐 → B → 0`; part (2) is not formalized here.

What is proved is degrees one and two: in degree one the cocycle premise of `h03QU₁` is Hilbert's
theorem 90 for an infinite Galois extension,
`Stacks.GaloisCohomology.isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁`, which needs no
hypothesis at all; in degree two it is
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauerGroup_eq_one`, which consumes the Brauer
hypothesis. So the Brauer hypothesis is genuinely used, and the tag's content in degrees one and
two is established rather than assumed. -/
@[stacks 03R8 "part (1), the full degree range q ≥ 1, over three carried hypotheses, and for an
arbitrary Galois extension Ω/K rather than only the separable closure. CARRIED as `h03QU₁` and
`h03QU₂`: the comparison in degrees one and two between the explicit cocycle description of
Galois cohomology and the derived-functor description continuousGroupCohomology of Stacks 04JR
-- the two are not related anywhere in this library above degree zero, where the comparison is
invariantsIsoZerothCohomology; this is the standard comparison of the standard complex with the
right derived functor and not a Stacks tag of its own. CARRIED as `hhigh`: the vanishing in
degrees q ≥ 3, which is the one part of part (1) assumed wholesale; the source gets it from part
(2) of this tag together with the four-term sequence 0 → A → M → M ⊗ Q → B → 0, whose
divisible-coefficient input IS proved (isZero_continuousGroupCohomology_of_module_rat, Stacks
0DV3 part (2)) but whose remaining ingredients -- part (2), the construction of M ⊗ Q as a
discrete Galois module, and the long exact sequence of continuousGroupCohomology -- are not.
PROVED: degrees one and two, where the cocycle premises of `h03QU₁` and `h03QU₂` are discharged
from proved results -- Hilbert 90 for an infinite Galois extension
(isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁, which needs no hypothesis) and the
crossed-product argument (isMulCoboundary₂_of_brauerGroup_eq_one above), the latter consuming the
Brauer hypothesis. So the hypothesis is genuinely used and the tag's content in degrees one and
two is established, not assumed. Also PROVED, and new: the coefficient module itself,
unitsContinuousGModule, the units of Ω as a discrete Galois module in the sense of Stacks 04JP,
together with the continuity of the Galois action on them. NOT proved: part (2) of the tag, for
which the library has none of the inputs -- see this file's module documentation"]
theorem isZero_continuousGroupCohomology_units (hBr : ∀ y : BrauerGroup K, y = 1)
    (h03QU₁ : (∀ f : Gal(Ω/K) → Ωˣ, IsLocallyConstant f → IsMulCocycle₁ f →
          IsMulCoboundary₁ f) →
        IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 1 (unitsContinuousGModule K Ω)))
    (h03QU₂ : (∀ f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ, IsLocallyConstant f → IsMulCocycle₂ f →
          IsMulCoboundary₂ f) →
        IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 2 (unitsContinuousGModule K Ω)))
    (hhigh : ∀ q : ℕ, 3 ≤ q →
      IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)))
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  by_cases h1 : q = 1
  · subst h1
    exact h03QU₁ fun f hloc hf ↦ isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ f hloc hf
  by_cases h2 : q = 2
  · subst h2
    exact h03QU₂ fun f hloc hf ↦ isMulCoboundary₂_of_brauerGroup_eq_one K Ω hBr f hloc hf
  exact hhigh q (by lia)

end Stacks.GaloisCohomology

end
