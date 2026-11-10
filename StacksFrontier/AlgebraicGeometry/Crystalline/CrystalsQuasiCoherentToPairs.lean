module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalFirstOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsToPairsEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The source category of [Stacks, Tag 07JH], and the statement of that tag

[Stacks, Proposition 60.17.4, Tag 07JH] asserts that the functor of [Stacks, Lemma 60.17.3,
Tag 07JG],

`{crystals in quasi-coherent 𝒪_{X/S}-modules on Cris(X/S)} ⟶ {pairs (M, ∇) of (07JB)-(07JE)}`,

is an equivalence of categories.  The target of that functor is `Crystalline.Pair`, and
`Crystalline.firstOrderCrystalsToPairs` is a functor into it whose source is the *algebraic*
first-order comparison data `Crystalline.FirstOrderCrystal` over a divided power ring `D`.  This
module builds the source category of the tag, the category of crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`, from the two predicates
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal` and
`SheafOfModules.IsQuasicoherentOnSite`; gives it the functor of sections, which needs no further
input; writes down the reduction datum from which the functor of the tag is built; and states the
tag against it.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`, except the
purely algebraic Taylor section, which is in `Crystalline`.

* `IsQuasiCoherentCrystal` — the object property "quasi-coherent and a crystal", as an
  `ObjectProperty`.
* `QuasiCoherentCrystal` — **the source category of [Stacks, Tag 07JH]**: the full subcategory of
  the sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)` cut out by that property, with
  `quasiCoherentCrystalι` its inclusion.
* `crystalSectionsFunctor` — the functor `F ↦ Γ(T, F_T)` on that category, for a fixed object
  `(U, T, δ)` of `Cris(X/S)`.  This is the underlying-module half of the assignment of
  [Stacks, Tag 07JG] and carries no hypothesis.
* `quasiCoherentCrystalUnit` — the structure sheaf `𝒪_{X/S}` as an object of that category, which
  witnesses that it is not empty.
* `levelRingLimit` — the ring `lim_e Γ(T_e, 𝒪_{T_e})` of a system of levels
  `T : ℕ ⥤ Cris(X/S)`, as the subring of compatible families in the product of the section rings.
  This is the ring `D` of [Stacks, Tag 07J8]: the completed envelope is a limit over the levels
  and is the section ring of no object of `Cris(X/S)`.
* `levelSectionsLimit` — the module `lim_e Γ(T_e, ℱ_{T_e})` of a crystal over such a system, as
  the subgroup of compatible families in the product of its modules of sections.  This is the
  module `M` of [Stacks, Tag 07JG].
* `PreReduction07JG` — the clauses of the reduction datum of [Stacks, Tag 07JG] with **no**
  condition on the system of levels of `Cris(X/S)` the sections are taken over: a functor from
  `QuasiCoherentCrystal` to `Crystalline.FirstOrderCrystal` together with the clauses that pin it
  to the tag's recipe.  No tag may be stated against it; see below.
* `PreReduction07JG.levelRingHom` — the reduction `D ⟶ Γ(T_e, 𝒪_{T_e})` of `D` to a level, read
  off the limit identification.
* `Reduction07JG` — **the reduction datum of [Stacks, Tag 07JG]**: that bundle together with the
  field `levelSystem_isLevel`, which pins the system to the one [Stacks, Tag 07JN] works over.
* `functor07JG` — the functor of [Stacks, Tag 07JG] with the tag's own source, given such a datum:
  the reduction followed by `Crystalline.firstOrderCrystalsToPairs`.
* `Equivalence07JH` — **the statement of [Stacks, Tag 07JH]** about that functor, as a `Prop`.
* `Crystalline.taylorMonomial`, `Crystalline.IsThetaMonomialFamily`,
  `Crystalline.IsTaylorComparison`, `Crystalline.HasTaylorComparison`,
  `Crystalline.TaylorCocycle` — the three inputs the proof of [Stacks, Tag 07JH] runs on: the
  divided power coefficients `∏ ξ_i^{[k_i]}` in total degree `≥ 2`, the `p`-adic convergence of
  the Taylor series, and the cocycle identity `c_{g,h} ∘ c_{f,g} = c_{f,h}`.  The convergence is
  `Crystalline.exists_hasTaylorSum`; `Crystalline.HasTaylorComparison` is not provable as stated
  (see below).

## Main results

* `instNonemptyQuasiCoherentCrystal` — the source category is not empty.  Its `Category` instance
  and the fullness and faithfulness of `quasiCoherentCrystalι` come from the full-subcategory
  construction and are not restated here.
* `nonempty_equivalence_of_equivalence07JH` — if [Stacks, Tag 07JH] holds for a reduction datum
  then the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` are equivalent to the
  pairs, which is the content the tag is used for downstream.
* `faithful_functor07JG_iff` — the faithfulness half of [Stacks, Tag 07JH] is exactly
  faithfulness of the reduction datum's functor, because
  `Crystalline.firstOrderCrystalsToPairs_faithful` is unconditional.
* `equivalence07JH_of_isEquivalence_functor` — given a reduction datum whose functor is an
  equivalence, [Stacks, Tag 07JH] follows from the two hypotheses `hinj` and `hlift` of
  `Crystalline.firstOrderCrystalsToPairs_isEquivalence` and nothing else.
* `Crystalline.injective_toCompletedTensor_iff_isHausdorff` — the hypothesis `hinj` of
  `Crystalline.firstOrderCrystalsToPairs_isEquivalence` is exactly `p`-adic Hausdorffness of
  `M ⊗_D Ω`, and `Crystalline.not_injective_toCompletedTensor_of_isUnit` is a situation in which
  it fails outright.
* `Reduction07JG.isOverWholeSpace_levelSystem` — every level of a reduction datum is a thickening
  of the whole of `X`, that is, lies in the subcategory `𝒞` of [Stacks, Tag 07JK] of
  [Stacks, Tag 07JN].  This is what rules the degenerate datum out.
* `isOverWholeSpace_of_isIsomorphic` — lying in `𝒞` is invariant under isomorphism of
  `Cris(X/S)`, which is what lets the field above be stated up to isomorphism.
* `levelSystem_isLevel_wholeSpaceSystem` and `Reduction07JG.ofWholeSpaceSystem` — the field is
  satisfied by the system [Stacks, Tag 07JN] works over, and a datum over that system is a
  reduction datum with nothing further to check, so the hypothesis is narrowed to the source's
  setting and not past it.
* `levelSectionsLimit_component_eq` — the product the limit sits inside is the product of the
  values of `crystalSectionsFunctor` at the levels, so the limit is a limit of that functor.
* `PreReduction07JG.levelRingHom_restrict` and `PreReduction07JG.sections_restrict` — the
  reductions of `D` and the level sections of a crystal are compatible with the system, which is
  what makes the two identifications limits and not products.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence` of
`SmallSite/CrystalPairEquivalence.lean`, and no `@[stacks 07JH]` attribute is placed in this
module.**  `Equivalence07JH` is a `Prop`, not a theorem.

Two theorems of the chapter have the shape of [Stacks, Tag 07JH] without stating it,
`Crystalline.taylorCrystalsToPairs_isEquivalence` and
`Crystalline.taylorCrystalsToPairs_isEquivalence_dividedPowerDifferentials`.  **Neither is about
`QuasiCoherentCrystal`.**  The functor in both is `Crystalline.taylorCrystalsToPairs`, whose source
is `Crystalline.TaylorCrystal`: the affine algebraic model over `D` of the data a crystal
supplies — a `D`-module with a first-order comparison datum, a tower of levels realising it as
`lim_e M_e`, and the composite coordinate operators of the expansion over `D(1)` — together with a
`Module.Basis` of `Ω` on finitely many differentials.  What separates that model from the category
built here is exactly `Reduction07JG` below, so those two theorems and `Equivalence07JH` are
statements about two different source categories and neither implies the other.

**The clauses `PreReduction07JG` alone are too weak a hypothesis to carry either
[Stacks, Tag 07JH] or [Stacks, Tag 07LG]; `Reduction07JG` adds the field `levelSystem_isLevel`.**
The clauses are satisfied, for *every* situation, by the degenerate datum
`...SmallSite.preReduction07JGBot`: its levels are all the empty open thickened by itself, whose
ring of sections is the zero ring, so every module in sight vanishes and every clause holds by
`Subsingleton.elim`.  At it, a statement about `functor07JG` asserts that a constant functor is an
equivalence and one about `crystalDeRhamComplex` asserts that a zero complex computes
`H^j(Cris(X/S), ℱ)` — both **false** whenever the crystalline cohomology is nonzero.  So a
universally quantified statement over the clauses alone is not vacuous but *refutable*.

The field `levelSystem_isLevel` excludes that datum, and this is proved: the field forces
`Reduction07JG.isOverWholeSpace_levelSystem`, every level lying in the subcategory `𝒞` of
[Stacks, Tag 07JK], and `...SmallSite.not_isOverWholeSpace_botObject` is the theorem that the
empty open fails exactly that, as soon as `X` has a point.  So no level of an
`R : Reduction07JG` is the degenerate datum's object, which is
`...SmallSite.levelSystem_obj_ne_botObject`, and the degenerate system satisfies the field for no
situation with a point, which is `...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`.

Two other conditions would not do as the field.  Faithfulness of `R.functor` is half of the
conclusion of [Stacks, Tag 07JH] — see `faithful_functor07JG_iff` — so assuming it would assume
what the tag asserts.  Weak finality of the object in `Cris(X/S)` is **not satisfied by the
source's objects** and so would make the two statements vacuous there rather than narrower: the
source's objects are the finite levels `T_e = Spec(D_e)`, the morphisms between them run
`T_e ⟶ T_{e + 1}` and not back, and an object of `Cris(X/S)` on which `p^m` does not vanish
admits no morphism to `T_e` with `N + e < m`.  Weak finality of the completed envelope `D` is a
true statement — it is [Stacks, Tag 07KI],
`Crystalline.exists_hom_from_completedPolynomialEnvelope` — but in the category
`Crystalline.CompletedCrystallineThickening` of an affine situation, of
which `D` is an object and to which no object of `Cris(X/S)` with a non-nilpotent `p` belongs; it
is not a statement about a level.

**The datum is over a system of levels.**  `levelSystem : ℕ ⥤ CrystallineThickening S` is the
whole tower `T_0 ⟶ T_1 ⟶ ⋯`, `ringEquiv` identifies `D` with `lim_e Γ(T_e, 𝒪_{T_e})`, and
`sections` identifies the module of the first-order crystal datum with `lim_e Γ(T_e, ℱ_{T_e})`.
So the pair `(M, ∇)` a datum carries is over the completed envelope, as [Stacks, Tag 07JG] says it
is, and not over one `D_e`.  This has three consequences for the other fields.

* **`thickeningRingHom` is a map and not an identification.**  The limit of the section rings of
  the first-order universal thickenings of the levels is `D ⊕ Ω̂`, the module of forms
  `p`-adically completed, and the parameter `Omega` of this bundle is the uncompleted module —
  the completion in a `Crystalline.Pair` is taken in the tensor product, not in `Omega`.  Asking
  for an isomorphism `D ⊕ Ω ≅ lim_e Γ(T'_e, 𝒪)` would therefore be asking for `Ω` to be
  `p`-adically complete, which [Stacks, Tag 07JG] does not say, so the field asks only for the
  compatible family of reductions, pinned on the `D` summand by `thickeningRingHom_p₀`.
* **`baseChange` is likewise a map and not an identification.**  At a level the base change of
  the sections is `(D_e ⊕ Ω_e) ⊗_{D_e} Γ(T_e, ℱ)`, not `(D ⊕ Ω) ⊗_D M`: the base change of the
  limit `M` is not the limit of the base changes.  What is true, and what the field asks, is that
  the canonical additive map `(D ⊕ Ω) ⊗_D M ⟶ Γ(T'_e, ℱ)` of `b ⊗ m ↦ b · p₀^* m` exists at every
  level; `baseChange_tmul` determines it outright.
* **`comparison_eq` pins the comparison map only up to the kernel of
  `(D ⊕ Ω) ⊗_D M ⟶ ∏_e Γ(T'_e, ℱ)`.**  That kernel is the `p`-adically non-separated part of the
  uncompleted tensor product, which is the same obstruction as the hypothesis `hinj` of
  `Crystalline.firstOrderCrystalsToPairs_isEquivalence`; see
  `Crystalline.injective_toCompletedTensor_iff_isHausdorff` below and
  `Crystalline.not_injective_toCompletedTensor_of_isUnit`, which is a situation where it fails.
  Nothing stronger is available: the sections of `ℱ` over the thickenings of the levels see only
  the `p`-adic completion of the tensor product.

The transition maps of the inverse system whose limit `sections` identifies `M` with are
surjective in the source's setting, by
`...SmallSite.surjective_affineSections_finiteLevelSystem_transition`, which runs on hypotheses
(1) and (2) of [Stacks, Tag 07JN].  So the limit is the one the source's proof computes with, and
not a limit with a derived-limit obstruction; that fact is not a field of this bundle and nothing
here consumes it.

At a single object the section rings of the object and of its first-order thickening are the
divided power ring and the trivial square-zero extension on the nose
(`...SmallSite.sectionsDividedPowerRingEquiv` and `...SmallSite.firstOrderSectionsRingEquiv`), but
these discharge no field: `ringEquiv` asks for `D` to be the *limit* of the section rings of the
levels, which is the identification of the completed divided power envelope of
[Stacks, Tag 07J8] that [Stacks, Tag 07JN] supplies.  For the system the field
`levelSystem_isLevel` pins, that identification is `...SmallSite.envelopeLevelRingLimitEquiv`, at
`D = D(n)` the completed envelope of the `(n + 1)`-fold tensor power of the situation's own
presentation: the section ring of the level `(n, e)` of `...SmallSite.wholeSpaceSystem` is
`D(n)/(p)^{N + e}` compatibly with the tower, which is
`...SmallSite.wholeSpaceSystemLevelRingEquiv` and
`...SmallSite.wholeSpaceSystemLevelRingEquiv_restrict`, and `D(n)` is the inverse limit of
those quotients because it is `p`-adically complete.

The fields of `Reduction07JG` fall into three groups.

1. **The identification of `D` with the limit of the section rings of the levels** — the fields
   `ringEquiv`, `thickeningRingHom` and `thickeningRingHom_p₀`.  For the system
   `...SmallSite.wholeSpaceSystem`, `ringEquiv` is `...SmallSite.envelopeLevelRingLimitEquiv`;
   the section rings of the *first-order thickenings* of the levels are not computed here, and
   their limit is `D ⊕ Ω̂` with the forms completed, which is why `thickeningRingHom` asks only for
   a compatible family of reductions.
2. **The sections of `F` over the first-order thickening as a base change** — the fields
   `baseChange` and `baseChange_tmul`.  This is the small-site form of the datum
   `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, and it is where the
   quasi-coherence clause in the source of the tag enters.  Its forward map is the
   `...diffAction` of [Stacks, Tag 07J6]; its inverse, `FirstOrderIdealBaseChange`, is constructed
   only for `ℱ = 𝒪_{X/S}`.  `Stacks.NoncommChangeOfRings.Presheaf.pullbackObjIso` and
   `Stacks.PullbackEquivalence.pullbackObjIsoBaseChange` identify the sections of
   `PresheafOfModules.pullback` with a base change, but the corresponding statement for
   `SheafOfModules.pullback` — the sheafification of the presheaf pullback — is false in general.
   `IsSheafCrystal` is a condition on the *sheaf*-level comparison maps, so the presheaf-level
   results do not reach it; they would apply to the strictly stronger presheaf-level
   `Crystalline.GlobalCrystallineSituation.IsCrystal`.
3. **The identification of the functor's value with the geometric datum** — the fields `sections`,
   `sections_smul`, `sections_naturality` and `comparison_eq`.  The last of these is the 07JG
   recipe itself: the comparison map of the first-order crystal datum is the restriction `s ↦ p₁^*
   s` along the second projection of the thickening of [Stacks, Tag 07J2], read at each level
   inside the base change of the sections.

`Reduction07JG.functor` lands in `Crystalline.FirstOrderCrystal`, whose fields
`isPAdicallyComplete`, `isIntegrable`, `isTopologicallyQuasiNilpotent` and
`hasCoordinateOperators` are items (07JB), (07JD), (07JE) and the non-vacuity of the last two;
they are carried by the datum and not derived from a crystal here.  Item (07JC), the connection
and its Leibniz rule, is built from a comparison datum by `Crystalline.firstOrderCrystalsToPairs`.

The Taylor section states three predicates and proves none of them.
`Crystalline.IsTaylorComparison` fixes the divided power `D`-algebra `B`; the proof of
[Stacks, Tag 07JH] needs the comparison for every such `B` arising from an object of `Cris(X/S)`,
which again is item 1 above.  Of the series only the part in total degree `≤ 1` is constructed, as
`Crystalline.firstOrderComparisonEquivConnection`.

* **The series converges**: `Crystalline.exists_hasTaylorSum` is the statement that it has
  finitely many nonzero terms and so has a sum in the `p`-adic topology, proved from the
  quasi-nilpotence condition (07JE).
* **`Crystalline.HasTaylorComparison` is not provable as stated**, and the fault is in the
  predicate.  Given the convergence it is equivalent to the *untwisted* `D`-linearity of the
  Taylor sum — `Crystalline.hasTaylorComparison_of_linearTaylorSum` and
  `Crystalline.taylorSum_smul_eq_of_isTaylorComparison` are the two directions — whereas the
  comparison `c_{f,g}` of the source runs `M ⊗_{D,f} B ⟶ M ⊗_{D,g} B` and obeys the `f`-twisted
  rule.  With `M = D` and `θ_K = ∂^K` the divided power partials, Taylor's formula turns the
  untwisted identity into `f = g`.  What the predicate lacks is the second divided power map `f`,
  a datum that does not occur in it at all.

## Implementation notes

The source category is a `CategoryTheory.ObjectProperty.FullSubcategory`, following
`SheafOfModules.isQuasicoherentOnSite`, so its `Category`, `Full` and `Faithful` instances come for
free and a morphism of the subcategory *is* a morphism of sheaves of modules.

`crystalSectionsFunctor` is assembled from `SheafOfModules.forget` and
`PresheafOfModules.evaluation` rather than written out, which is why it needs no lemma about
morphisms on sections.

`Reduction07JG.sections` is an `AddEquiv` with semilinearity recorded separately, rather than a
`LinearEquiv`, because its two sides are modules over two different rings — `D` and the limit
`lim_e Γ(T_e, 𝒪_{T_e})` — which the field `ringEquiv` identifies; the same device is used for
`baseChange`.  Semilinearity is stated level by level, as an equation in `Γ(T_e, ℱ_{T_e})`, rather
than over the limit ring: the limit of the modules of sections carries no module structure over
the limit of the section rings without a construction, and stating the clause at the levels asks
for exactly the same thing with none.

The two limits are `Subring` and `AddSubgroup` of the products of the levels' section rings and
modules of sections, not `CategoryTheory.Limits.limit` of a diagram in `RingCat` or
`AddCommGrpCat`.  The categorical limits of level sections `...SmallSite.sectionSystem`,
`...SmallSite.cosimplicialSections` and `...SmallSite.levelLimitSections` are limits of an
abelian presheaf at the coefficient universe `u + 1`, so they are not these: the module of a
`Crystalline.FirstOrderCrystal` lives in `Type u` and carries a `D`-action, and a categorical
limit in `AddCommGrpCat.{u}` would then need both a universe descent and a module structure
transported onto it before a clause could be stated.  The compatible-family description needs
neither and its components are the values of `crystalSectionsFunctor`, by
`levelSectionsLimit_component_eq`.

The Taylor comparison is a `B`-linear endomorphism of `B ⊗_{D} M` pinned by its value on `1 ⊗ m`,
rather than a semilinear map `M ⊗_{D,f} B → M ⊗_{D,g} B` as in the source.  The two carry the same
information, and the endomorphism form is the one in which the cocycle identity is a composition
of maps with one and the same source and target; writing the source's form would need two
different `Algebra D B` instances on one type, which the construction of
`Crystalline.firstOrderCrystalsToPairs` avoids too.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The source category of [Stacks, Tag 07JH] -/

/-- **Crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`**, as an object property of the
sheaves of `𝒪_{X/S}`-modules on the small crystalline site: quasi-coherence in the sense of
[Stacks, Tag 07IU] together with the crystal condition of [Stacks, Tag 07IS] on the comparison
maps of sheaves of modules.  Making the conjunction an `ObjectProperty` is what gives the source
category of [Stacks, Tag 07JH] below. -/
def IsQuasiCoherentCrystal (S : GlobalCrystallineSituation.{u}) :
    ObjectProperty (SheafOfModules.{u} (structureSheaf S)) :=
  fun F ↦ F.IsQuasicoherentOnSite ∧ IsSheafCrystal F

/-- **The source category of [Stacks, Tag 07JH]**: the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`, as the full subcategory of the sheaves of `𝒪_{X/S}`-modules cut
out by `Crystalline.GlobalCrystallineSituation.SmallSite.IsQuasiCoherentCrystal`.  A morphism is a
morphism of sheaves of modules, with no condition, which is what "full subcategory" means and what
[Stacks, Tag 07JH] asks of its source. -/
abbrev QuasiCoherentCrystal (S : GlobalCrystallineSituation.{u}) : Type _ :=
  (IsQuasiCoherentCrystal S).FullSubcategory

/-- The inclusion of the crystals in quasi-coherent `𝒪_{X/S}`-modules into the sheaves of
`𝒪_{X/S}`-modules on `Cris(X/S)`.  It is full and faithful. -/
abbrev quasiCoherentCrystalι (S : GlobalCrystallineSituation.{u}) :
    QuasiCoherentCrystal S ⥤ SheafOfModules.{u} (structureSheaf S) :=
  (IsQuasiCoherentCrystal S).ι

variable {S : GlobalCrystallineSituation.{u}}

/-- An object of the source category of [Stacks, Tag 07JH] is quasi-coherent. -/
instance instIsQuasicoherentOnSiteObj (F : QuasiCoherentCrystal S) :
    F.obj.IsQuasicoherentOnSite :=
  F.property.1

/-- An object of the source category of [Stacks, Tag 07JH] is a crystal. -/
theorem isSheafCrystal_obj (F : QuasiCoherentCrystal S) : IsSheafCrystal F.obj :=
  F.property.2

/-- **The sections of a crystal over an object of `Cris(X/S)`, as a functor** on the source
category of [Stacks, Tag 07JH]: for a fixed object `(U, T, δ)` the assignment `F ↦ Γ(T, F_T)`,
with its module structure over `Γ(T, 𝒪_T)`.  This is the underlying-module half of the assignment
of [Stacks, Tag 07JG] and it carries no hypothesis; what the tag's functor needs beyond it is the
connection, which is `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG`. -/
def crystalSectionsFunctor (S : GlobalCrystallineSituation.{u}) (B : CrystallineThickening S) :
    QuasiCoherentCrystal S ⥤ ModuleCat.{u} ((structureSheaf S).obj.obj (op B)) :=
  quasiCoherentCrystalι S ⋙ SheafOfModules.forget (structureSheaf S) ⋙
    PresheafOfModules.evaluation (structureSheaf S).obj (op B)

/-- The sections functor takes a crystal to its module of sections over the chosen object. -/
@[simp] theorem crystalSectionsFunctor_obj (B : CrystallineThickening S)
    (F : QuasiCoherentCrystal S) :
    (crystalSectionsFunctor S B).obj F = F.obj.val.obj (op B) :=
  rfl

/-- **The restriction to `Cris(X/S)` of the structure sheaf of `CRIS(X/S)` is the structure sheaf
of `Cris(X/S)`.**  Both have for sections over an object of the small site the ring of sections of
`𝒪_{X/S}` over the underlying object of the big site. -/
theorem restrictSheafOfModules_unit (S : GlobalCrystallineSituation.{u}) :
    restrictSheafOfModules (SheafOfModules.unit (crystallineStructureSheaf S)) =
      SheafOfModules.unit (structureSheaf S) :=
  rfl

/-- **The structure sheaf `𝒪_{X/S}` is an object of the source category of
[Stacks, Tag 07JH]**, which witnesses that the category is not empty: it is quasi-coherent by
`SheafOfModules.isQuasicoherentOnSite_unit` and a crystal by
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_restrictUnit`.  Its pair `(M, ∇)`
under the functor of [Stacks, Tag 07JG] is `(Γ(T, 𝒪_T), d_{T/S,δ})`, by
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_unit`. -/
noncomputable def quasiCoherentCrystalUnit (S : GlobalCrystallineSituation.{u}) :
    QuasiCoherentCrystal S where
  obj := SheafOfModules.unit (structureSheaf S)
  property := ⟨SheafOfModules.isQuasicoherentOnSite_unit (structureSheaf S),
    restrictSheafOfModules_unit S ▸ isSheafCrystal_restrictUnit S⟩

/-- The source category of [Stacks, Tag 07JH] is not empty: the structure sheaf is an object. -/
instance instNonemptyQuasiCoherentCrystal : Nonempty (QuasiCoherentCrystal S) :=
  ⟨quasiCoherentCrystalUnit S⟩

/-! ### The levels of a reduction datum and the limits over them -/

/-- **The ring `lim_e Γ(T_e, 𝒪_{T_e})` of a system of levels of `Cris(X/S)`**, as the subring of
compatible families inside the product of the section rings of the levels: a family
`e ↦ a_e ∈ Γ(T_e, 𝒪_{T_e})` belongs to it exactly when each `a_{e'}` restricts to `a_e` along the
structure map `T_e ⟶ T_{e'}` of the system.

This is the ring the source's proof of [Stacks, Tag 07JG] calls `D`.  The `p`-adically completed
divided power envelope of [Stacks, Tag 07J8] is the inverse limit of the section rings of the
finite levels `T_e = Spec(D_e)` — it is *not* the section ring of any object of `Cris(X/S)`, its
divided power ideal not being locally nilpotent — which is why the datum below identifies `D`
with this ring rather than with the sections over a single object. -/
def levelRingLimit (S : GlobalCrystallineSituation.{u}) (T : ℕ ⥤ CrystallineThickening S) :
    Subring (∀ e : ℕ, (structureSheaf S).obj.obj (op (T.obj e))) where
  carrier := {a | ∀ {e e' : ℕ} (h : e ⟶ e'),
    ((structureSheaf S).obj.map (T.map h).op).hom (a e') = a e}
  mul_mem' ha hb := by
    intro e e' h
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, ha h, hb h]
  one_mem' := by
    intro e e' h
    rw [Pi.one_apply, Pi.one_apply, map_one]
  add_mem' ha hb := by
    intro e e' h
    rw [Pi.add_apply, Pi.add_apply, map_add, ha h, hb h]
  zero_mem' := by
    intro e e' h
    rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  neg_mem' ha := by
    intro e e' h
    rw [Pi.neg_apply, Pi.neg_apply, map_neg, ha h]

/-- **The module `lim_e Γ(T_e, ℱ_{T_e})` of a crystal over a system of levels of `Cris(X/S)`**, as
the subgroup of compatible families inside the product of its modules of sections over the levels.
The components of the product are the values of
`Crystalline.GlobalCrystallineSituation.SmallSite.crystalSectionsFunctor` at the levels, by
`...SmallSite.levelSectionsLimit_component_eq`.

This is the module `M` of [Stacks, Tag 07JG]: the source sets `M = lim_e Γ(T_e, ℱ)`, and it is
over that limit — a module over the completed envelope `D` — that the pair `(M, ∇)` of the tag
lives, not over the sections at one level. -/
def levelSectionsLimit (S : GlobalCrystallineSituation.{u}) (T : ℕ ⥤ CrystallineThickening S)
    (F : QuasiCoherentCrystal S) :
    AddSubgroup (∀ e : ℕ, F.obj.val.obj (op (T.obj e))) where
  carrier := {s | ∀ {e e' : ℕ} (h : e ⟶ e'), F.obj.val.map (T.map h).op (s e') = s e}
  add_mem' hs ht := by
    intro e e' h
    rw [Pi.add_apply, Pi.add_apply, map_add, hs h, ht h]
    rfl
  zero_mem' := by
    intro e e' h
    rw [Pi.zero_apply, Pi.zero_apply, map_zero]
    rfl
  neg_mem' hs := by
    intro e e' h
    rw [Pi.neg_apply, Pi.neg_apply, map_neg, hs h]
    rfl

/-- **The product the limit of the level sections sits inside is the product of the values of the
sections functor.**  The `e`-th component of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsLimit` is the value at the crystal
of `...SmallSite.crystalSectionsFunctor` for the `e`-th level, so the limit really is a limit of
that functor over the system; the identification is definitional. -/
theorem levelSectionsLimit_component_eq (S : GlobalCrystallineSituation.{u})
    (T : ℕ ⥤ CrystallineThickening S) (F : QuasiCoherentCrystal S) (e : ℕ) :
    F.obj.val.obj (op (T.obj e)) = (crystalSectionsFunctor S (T.obj e)).obj F :=
  rfl

/-! ### The reduction datum of [Stacks, Tag 07JG] -/

/-- **The reduction datum of [Stacks, Tag 07JG] without its level condition**: a functor from the
crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the first-order crystal data over
the divided power ring `D` of [Stacks, Tag 07J8], together with the clauses pinning it to the
recipe of the tag, but with **no condition on the system of levels `levelSystem` over which the
sections are taken**.

The clauses say: there is a system `T_0 ⟶ T_1 ⟶ ⋯` of objects of `Cris(X/S)` whose section rings
have `D` for their inverse limit; the module the functor produces is the inverse limit of the
sections of the crystal over the levels, semilinearly for that identification and naturally in
the crystal; the section ring of the first-order universal thickening of [Stacks, Tag 07J2] of
each level receives `D ⊕ Ω` compatibly with the first projection; the sections of the crystal
over that thickening receive the base change `(D ⊕ Ω) ⊗_D M` by `b ⊗ m ↦ b · p₀^* m`; and, read
there, the comparison map of the first-order crystal datum is the restriction `s ↦ p₁^* s` along
the second projection.

`ringEquiv` is the identification of [Stacks, Tag 07J8] and [Stacks, Tag 07JN] of the completed
envelope with the limit of the section rings of the levels; `baseChange` and `baseChange_tmul` are
the small-site form of `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, which is
not a consequence of the sheaf-level crystal condition.  See the module documentation.

This bundle is too weak a hypothesis for [Stacks, Tag 07JH], which is why it is separate from
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG`: it is satisfied by the
degenerate datum `...SmallSite.preReduction07JGBot` whose levels are all the empty open of `X`,
whose section rings are the zero ring and at which every clause holds between elements of a
subsingleton. -/
structure PreReduction07JG (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
    (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega) where
  /-- The system of levels `T_0 ⟶ T_1 ⟶ ⋯` of `Cris(X/S)` over which the sections are taken. -/
  levelSystem : ℕ ⥤ CrystallineThickening S
  /-- The reduction functor itself. -/
  functor : QuasiCoherentCrystal S ⥤ FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx
  /-- **The ring `D` is the inverse limit of the section rings of the levels.**  This is the
  system form of what a single section ring cannot say: `D` is the completed envelope, and the
  completion is the limit over the levels. -/
  ringEquiv : (D : Type u) ≃+* ↥(levelRingLimit S levelSystem)
  /-- The ring `D ⊕ Ω` maps to the ring of sections of `𝒪_{X/S}` over the first-order universal
  thickening of the level `e`.  Unlike `ringEquiv` this is **not** an identification with a
  limit: the sections over the first-order thickenings have `D ⊕ Ω̂` for their limit, the forms
  completed, and `Omega` is the uncompleted module. -/
  thickeningRingHom : ∀ e : ℕ, firstOrderExtension D Omega →+*
    (structureSheaf S).obj.obj (op (firstOrderThickeningCrysObject S (levelSystem.obj e)))
  /-- That map restricted along the first projection `p₀ : D → D ⊕ Ω` is the reduction of `D` to
  the level `e` followed by the restriction of sections along the projection of
  [Stacks, Tag 07J2].  This is what pins it to the canonical map on the `D` summand. -/
  thickeningRingHom_p₀ : ∀ (e : ℕ) (a : (D : Type u)),
    thickeningRingHom e (firstOrderP₀ D Omega a) =
      ((structureSheaf S).obj.map
        (firstOrderThickeningCrysP₀ S (levelSystem.obj e)).op).hom ((ringEquiv a).val e)
  /-- **The limit identification.**  The module the functor produces is the inverse limit over
  the levels of the modules of sections of the crystal, which is the module `M = lim_e Γ(T_e, ℱ)`
  of [Stacks, Tag 07JG]. -/
  sections : ∀ F : QuasiCoherentCrystal S,
    (functor.obj F).carrier ≃+ ↥(levelSectionsLimit S levelSystem F)
  /-- That identification is semilinear, level by level, for the identification of `D` with the
  limit of the section rings. -/
  sections_smul : ∀ (F : QuasiCoherentCrystal S) (a : (D : Type u))
    (m : (functor.obj F).carrier) (e : ℕ),
    (sections F (a • m)).val e = (ringEquiv a).val e • (sections F m).val e
  /-- That identification is natural in the crystal, level by level, which is what makes the
  assignment a functor in the sense of [Stacks, Tag 07JG]. -/
  sections_naturality : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (m : (functor.obj F).carrier) (e : ℕ),
    (sections G ((functor.map psi).toLinearMap m)).val e =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
        (op (levelSystem.obj e))).hom ((sections F m).val e)
  /-- The base change `(D ⊕ Ω) ⊗_D M` maps to the sections over the first-order thickening of the
  level `e`.  It is a map and not an identification: the base change of the limit `M` is not the
  limit of the base changes. -/
  baseChange : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
    (firstOrderExtension D Omega ⊗[D] (functor.obj F).carrier) →+
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (levelSystem.obj e)))
  /-- The base change map sends `b ⊗ m` to `b · p₀^* m`, which is what makes it the canonical one
  and not an arbitrary additive map; it determines `baseChange` outright. -/
  baseChange_tmul : ∀ (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : firstOrderExtension D Omega) (m : (functor.obj F).carrier),
    baseChange F e (b ⊗ₜ[D] m) = thickeningRingHom e b •
      F.obj.val.map (firstOrderThickeningCrysP₀ S (levelSystem.obj e)).op
        ((sections F m).val e)
  /-- **The recipe of [Stacks, Tag 07JG].**  Read at each level inside the base change, the
  comparison map of the first-order crystal datum is the restriction along the second
  projection. -/
  comparison_eq : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (m : (functor.obj F).carrier),
    baseChange F e ((functor.obj F).comparison m) =
      F.obj.val.map (firstOrderThickeningCrysP₁ S (levelSystem.obj e)).op
        ((sections F m).val e)

/-- **The reduction datum of [Stacks, Tag 07JG]**, assembled from levelwise inputs by
`...SmallSite.reduction07JGWholeSpaceOfLevelwise`: the clauses
of `Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` together with the condition
that the system of levels over which the sections are taken is the one [Stacks, Tag 07JN] works
over.

The standing hypotheses `[IsAffine S.X]`, `[IsAffine S.S.scheme]` and `hp` are the source's own:
the section this tag belongs to opens "In Situation [Stacks, Tag 07MD].  Set `X = Spec(C)` and
`S = Spec(A)`", and `p` is nilpotent on `Γ(X, 𝒪_X)` in that situation.  They are what makes the
system of [Stacks, Tag 07JN] available to the field below, and they are exactly the hypotheses
of `Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG`. -/
structure Reduction07JG (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
    (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
    [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    extends PreReduction07JG S A D g Omega d p dx where
  /-- **The system of levels is the system [Stacks, Tag 07JN] works over**: it is isomorphic, as
  a functor `ℕ ⥤ Cris(X/S)`, to the degree-zero member
  `e ↦ (X, T(0)_e, δ(0))` of the cosimplicial system
  `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` of that tag, whose `e`-th
  object is `D/(p)^{N + e}` for `D` the `p`-adically completed divided power envelope of
  [Stacks, Tag 07J8].  These are the objects `T_e = Spec(D_e)` whose sections the source's proof
  of [Stacks, Tag 07JG] takes the limit of.

  The condition is up to isomorphism of the functor, not on the nose, so that an isomorphic copy
  of the source's system is still admissible; being an isomorphism of functors it pins the
  structure maps `T_e ⟶ T_{e + 1}` as well as the objects, which is what the limit depends on.
  It pins the presentation of `Γ(X, 𝒪_X)` to the tautological one, which is the presentation
  used for [Stacks, Tag 07JN] here and a choice of presentation the source makes too. -/
  levelSystem_isLevel : IsIsomorphic levelSystem
    ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))

/-- **Being a thickening of the whole of `X` is invariant under isomorphism in `Cris(X/S)`.**  An
isomorphism carries the structure map `U ⟶ X` of one object to that of the other through an
isomorphism of the thickened schemes, so one is an isomorphism as soon as the other is. -/
theorem isOverWholeSpace_of_isIsomorphic {B C : CrystallineThickening S} (h : IsIsomorphic B C)
    (hC : IsOverWholeSpace S C) : IsOverWholeSpace S B := by
  obtain ⟨e⟩ := h
  have hiso : IsIso (((CrystallineThickening.ι S).mapIso e).hom.sourceHom) := by
    refine ⟨⟨((CrystallineThickening.ι S).mapIso e).inv.sourceHom, ?_, ?_⟩⟩
    · rw [← Thickening.comp_sourceHom, ((CrystallineThickening.ι S).mapIso e).hom_inv_id,
        Thickening.id_sourceHom]
    · rw [← Thickening.comp_sourceHom, ((CrystallineThickening.ι S).mapIso e).inv_hom_id,
        Thickening.id_sourceHom]
  have hC' : IsIso C.obj.toX := hC
  have hnat : ((CrystallineThickening.ι S).mapIso e).hom.sourceHom ≫ C.obj.toX = B.obj.toX :=
    ((CrystallineThickening.ι S).mapIso e).hom.toX_naturality
  change IsIso B.obj.toX
  rw [← hnat]
  infer_instance

/-- **The field `levelSystem_isLevel` is satisfied by the system [Stacks, Tag 07JN] works
over.**  The degree-zero member of
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` satisfies the condition, by
the identity isomorphism, so adding the field narrows the hypothesis of [Stacks, Tag 07JH] and
[Stacks, Tag 07LG] to the source's setting and not past it.  Together with
`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot` this brackets the field: the source's
own system has it, the degenerate system of empty objects does not. -/
theorem levelSystem_isLevel_wholeSpaceSystem [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    IsIsomorphic ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
      ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) :=
  ⟨Iso.refl _⟩

section PreLevels

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

/-- **The reduction of `D` to a level**, the ring homomorphism `D ⟶ Γ(T_e, 𝒪_{T_e})` read off
the identification of `D` with the limit of the section rings.  In the source's setting it is the
quotient map `D ⟶ D/(p)^{N + e}`. -/
def PreReduction07JG.levelRingHom (R : PreReduction07JG S A D g Omega d p dx) (e : ℕ) :
    (D : Type u) →+* (structureSheaf S).obj.obj (op (R.levelSystem.obj e)) where
  toFun a := (R.ringEquiv a).val e
  map_one' := congrFun (congrArg Subtype.val (map_one R.ringEquiv)) e
  map_mul' a b := congrFun (congrArg Subtype.val (map_mul R.ringEquiv a b)) e
  map_zero' := congrFun (congrArg Subtype.val (map_zero R.ringEquiv)) e
  map_add' a b := congrFun (congrArg Subtype.val (map_add R.ringEquiv a b)) e

/-- The reduction of `D` to the level `e` is the `e`-th component of the image of `D` in the
limit of the section rings. -/
@[simp] theorem PreReduction07JG.levelRingHom_apply
    (R : PreReduction07JG S A D g Omega d p dx) (e : ℕ) (a : (D : Type u)) :
    R.levelRingHom e a = (R.ringEquiv a).val e :=
  rfl

/-- **The reductions of `D` to the levels are compatible with the system.**  This is the
membership condition of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelRingLimit`, read through `ringEquiv`. -/
theorem PreReduction07JG.levelRingHom_restrict (R : PreReduction07JG S A D g Omega d p dx)
    {e e' : ℕ} (h : e ⟶ e') (a : (D : Type u)) :
    ((structureSheaf S).obj.map (R.levelSystem.map h).op).hom (R.levelRingHom e' a) =
      R.levelRingHom e a :=
  (R.ringEquiv a).2 h

/-- **The sections of a crystal over the levels of a reduction datum are compatible with the
system.**  This is the membership condition of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsLimit`, read through `sections`,
and it is the statement that the module of the first-order crystal datum really is a limit and
not a product. -/
theorem PreReduction07JG.sections_restrict (R : PreReduction07JG S A D g Omega d p dx)
    (F : QuasiCoherentCrystal S) {e e' : ℕ} (h : e ⟶ e')
    (m : (R.functor.obj F).carrier) :
    F.obj.val.map (R.levelSystem.map h).op ((R.sections F m).val e') =
      (R.sections F m).val e :=
  (R.sections F m).2 h

end PreLevels

section Statement

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  [IsAffine S.X] [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-- **Every level of a reduction datum is a thickening of the whole of `X`**, that is, lies in
the subcategory `𝒞` of [Stacks, Tag 07JK] that [Stacks, Tag 07JN] works over.  This is the
weakest consequence of the field
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG.levelSystem_isLevel`, and it is
already enough to exclude the degenerate datum over the empty open of `X`; see
`Crystalline.GlobalCrystallineSituation.SmallSite.not_isOverWholeSpace_botObject`. -/
theorem Reduction07JG.isOverWholeSpace_levelSystem (R : Reduction07JG S A D g Omega d p dx hp)
    (e : ℕ) : IsOverWholeSpace S (R.levelSystem.obj e) := by
  obtain ⟨iso⟩ := R.levelSystem_isLevel
  exact isOverWholeSpace_of_isIsomorphic ⟨iso.app e⟩
    (isWholeSpaceSystem_wholeSpaceSystem S hp 0 e)

/-- **The source's own system of levels satisfies the field `levelSystem_isLevel`**: a datum
satisfying
the clauses of
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` whose system of levels *is*
the degree-zero member of the system of [Stacks, Tag 07JN] is a reduction datum, the field being
discharged by the identity isomorphism.  So the field narrows the hypothesis of
[Stacks, Tag 07JH] and [Stacks, Tag 07LG] to the source's setting and not past it: it excludes
the degenerate systems and nothing the source provides. -/
def Reduction07JG.ofWholeSpaceSystem (R : PreReduction07JG S A D g Omega d p dx)
    (h : R.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) :
    Reduction07JG S A D g Omega d p dx hp where
  toPreReduction07JG := R
  levelSystem_isLevel := by rw [h]; exact ⟨Iso.refl _⟩

/-- **The functor of [Stacks, Tag 07JG] with the source the tag gives it**, given a reduction
datum: the reduction from the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the
first-order crystal data over `D`, followed by `Crystalline.firstOrderCrystalsToPairs`.  This is
the functor [Stacks, Tag 07JH] is about. -/
noncomputable def functor07JG (R : Reduction07JG S A D g Omega d p dx hp) :
    QuasiCoherentCrystal S ⥤ Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d) :=
  R.functor ⋙ (firstOrderCrystalsToPairs A D g Omega d p dx :
    FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx ⥤
      Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d))

/-- **The statement of [Stacks, Proposition 60.17.4, Tag 07JH]**: the functor of
[Stacks, Tag 07JG] from the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the
pairs `(M, ∇)` satisfying items (07JB), (07JC), (07JD) and (07JE) is an equivalence of categories.

The functor is `Crystalline.GlobalCrystallineSituation.SmallSite.functor07JG`, which is pinned to
the tag's recipe by the clauses of the reduction datum `R`.

This is a proposition, not a theorem: nothing here proves it, and no `@[stacks 07JH]` attribute is
placed.  The module documentation discusses the inputs of its proof — the degree `≥ 2` Taylor
coefficients and the cocycle identity, stated below as `Crystalline.HasTaylorComparison` and
`Crystalline.TaylorCocycle`, and the `p`-adic convergence of the series,
`Crystalline.exists_hasTaylorSum` — and the fields of `R`. -/
def Equivalence07JH (R : Reduction07JG S A D g Omega d p dx hp) : Prop :=
  Functor.IsEquivalence (functor07JG R)

/-- **If [Stacks, Tag 07JH] holds then its two categories are equivalent.**  This is the form in
which the tag is used downstream — [Stacks, Tag 07MF] and the comparison theorems quote it as an
identification of the crystals in quasi-coherent `𝒪_{X/S}`-modules with the pairs `(M, ∇)` — so it
records that `Crystalline.GlobalCrystallineSituation.SmallSite.Equivalence07JH` has the content the
tag is quoted for. -/
theorem nonempty_equivalence_of_equivalence07JH {R : Reduction07JG S A D g Omega d p dx hp}
    (h : Equivalence07JH R) :
    Nonempty (QuasiCoherentCrystal S ≌
      Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d)) :=
  have : Functor.IsEquivalence (functor07JG R) := h
  ⟨(functor07JG R).asEquivalence⟩

/-- **The faithfulness half of [Stacks, Tag 07JH] is exactly faithfulness of the reduction.**
`Crystalline.firstOrderCrystalsToPairs_faithful` is unconditional, so the functor of
[Stacks, Tag 07JG] is faithful if and only if the reduction datum's functor is: all of the content
of that half of the tag sits in the passage from a crystal to its first-order comparison datum, and
none of it in the passage from that datum to the pair. -/
theorem faithful_functor07JG_iff (R : Reduction07JG S A D g Omega d p dx hp) :
    Functor.Faithful (functor07JG R) ↔ Functor.Faithful R.functor := by
  have := firstOrderCrystalsToPairs_faithful A D g Omega d p dx
  unfold functor07JG
  exact ⟨fun h ↦ Functor.Faithful.of_comp (F := R.functor) (G := firstOrderCrystalsToPairs ..),
    fun h ↦ Functor.Faithful.comp _ _⟩

/-- **What [Stacks, Tag 07JH] reduces to once the reduction datum is available.**  Given a
reduction datum whose functor is itself an equivalence, the tag follows from the two hypotheses
`hinj` and `hlift` of `Crystalline.firstOrderCrystalsToPairs_isEquivalence`.  So the tag splits
into three statements: that the passage from a crystal in quasi-coherent `𝒪_{X/S}`-modules to its
first-order comparison datum over `D` is an equivalence, injectivity of the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω` on the modules of the first-order crystal data, and the factorisation of the
connection of every pair through `M ⊗_D Ω`.

The theorem `Crystalline.injective_toCompletedTensor_iff_isHausdorff` below says what `hinj`
amounts to, and `hinj` is discharged when `Ω` is free over `D` — in general from a basis carried
as a hypothesis, and with nothing carried when `Ω` is the module of divided power differentials
of the divided power polynomial algebra, by
`Crystalline.equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials`.

`hlift` is discharged when `Ω` is free of **finite** rank over `D`, by
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis`: it follows from
*bijectivity* of the same canonical map through
`Crystalline.exists_firstOrderConnection_of_bijective`, bijectivity is `IsAdicComplete` on
`M ⊗_D Ω` by `AdicCompletion.of_bijective_iff`, and a finite basis makes that module a finite
product of copies of `M`, which item (07JB) already says is `p`-adically complete.  The finiteness
is used there; for a general `Ω` the hypothesis `hlift` is carried. -/
theorem equivalence07JH_of_isEquivalence_functor (R : Reduction07JG S A D g Omega d p dx hp)
    (hR : Functor.IsEquivalence R.functor)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (hlift : ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Equivalence07JH R := by
  have := hR
  have := firstOrderCrystalsToPairs_isEquivalence A D g Omega d p dx hinj hlift
  exact Functor.isEquivalence_trans R.functor _

end Statement

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline

/-! ### The hypothesis `hinj` of the conditional equivalence -/

section Hinj

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type u) [AddCommGroup Omega]
  [Module D Omega] (M : Type u) [AddCommGroup M] [Module D M]

/-- **The hypothesis `hinj` is exactly `p`-adic Hausdorffness of `M ⊗_D Ω`.**  The hypothesis
`hinj` of `Crystalline.firstOrderCrystalsToPairs_isEquivalence` is injectivity of the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω`, and for a `p`-adic completion that is the vanishing of `⋂_n p^n (M ⊗_D Ω)`.
So it is a condition on the uncompleted tensor product alone and does **not** follow from `p`-adic
completeness of `M`, which is item (07JB): the tensor product of two `p`-adically separated modules
need not be separated. -/
theorem injective_toCompletedTensor_iff_isHausdorff :
    Function.Injective (toCompletedTensor p D Omega M) ↔
      IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega) :=
  AdicCompletion.of_injective_iff

/-- **A situation in which `hinj` fails outright.**  If `p` is invertible in `D` then the `p`-adic
ideal is the unit ideal, the `p`-adic completion of any module is zero, and the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω` is injective only when `M ⊗_D Ω` itself vanishes.  So `hinj` is a genuine
hypothesis on the situation and not a harmless normalisation; carrying it is carrying something
that can be false. -/
theorem not_injective_toCompletedTensor_of_isUnit (hp : IsUnit (p : D))
    (hM : ¬ Subsingleton (M ⊗[D] Omega)) :
    ¬ Function.Injective (toCompletedTensor p D Omega M) := by
  intro hinj
  have htop : DividedPowers.pAdicIdeal (A := D) p = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hp
  exact hM (IsHausdorff.subsingleton
    (htop ▸ (injective_toCompletedTensor_iff_isHausdorff p D Omega M).mp hinj))

end Hinj

/-! ### The Taylor series of the proof of [Stacks, Tag 07JH] -/

section Taylor

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module D M]
  {ι : Type uI}

/-- **The divided power monomial `∏_i ξ_i^{[k_i]}`** of the Taylor series in the proof of
[Stacks, Tag 07JH], for a multi-index `k` with finite support and a family `ξ : ι → B` of elements
of the divided power ideal of `B`.  In the tag `ξ_i = f(x_i) - g(x_i)` for two divided power maps
`f, g : D → B` agreeing modulo that ideal.  The total degree of the monomial is `∑_i k_i`; the
terms with `k` of total degree `≤ 1` are the ones of
`Crystalline.firstOrderComparisonEquivConnection`. -/
noncomputable def taylorMonomial (xi : ι → (B : Type u)) (k : ι →₀ ℕ) : (B : Type u) :=
  ∏ i ∈ k.support, B.dividedPowers.dpow (k i) (xi i)

/-- The divided power monomial of the empty multi-index is `1`. -/
@[simp] theorem taylorMonomial_zero (xi : ι → (B : Type u)) :
    taylorMonomial B xi (0 : ι →₀ ℕ) = 1 := by
  rw [taylorMonomial, Finsupp.support_zero, Finset.prod_empty]

/-- **The composite coordinate operators `θ_K = ∏_i θ_i^{k_i}` of [Stacks, Tag 07JH]**, as a
predicate on a candidate family indexed by the multi-indices: the family is the identity at the
empty multi-index and is obtained from the next smaller one by applying one more coordinate
operator.  Stated as a predicate rather than defined, because the product `∏_i θ_i^{k_i}` is well
defined only once the coordinate operators commute, which is item (07JD) — integrability — and is
not available here. -/
def IsThetaMonomialFamily (theta : ι → (M → M)) (thetaPow : (ι →₀ ℕ) → (M → M)) : Prop :=
  thetaPow 0 = id ∧
    ∀ (i : ι) (k : ι →₀ ℕ), thetaPow (k + Finsupp.single i 1) = theta i ∘ thetaPow k

/-- **The Taylor comparison of the proof of [Stacks, Tag 07JH]**, as a predicate on a `B`-linear
endomorphism `c` of the base change `B ⊗_D M`: on the generator `1 ⊗ m` it is the sum

`c (1 ⊗ m) = ∑_K ξ^{[K]} ⊗ θ_K(m)`

over all multi-indices `K`, converging in the `p`-adic topology of `B ⊗_D M`.  Both the divided
power coefficients `ξ^{[K]} = ∏_i ξ_i^{[k_i]}` in total degree `≥ 2` and the convergence of the
series are contained in this one condition, the sum being a `HasSum` for the `p`-adic topology. -/
noncomputable def IsTaylorComparison (thetaPow : (ι →₀ ℕ) → (M → M)) (xi : ι → (B : Type u))
    (c : ((B : Type u) ⊗[D] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[D] M)) : Prop :=
  letI := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := (B : Type u)) p)
    ((B : Type u) ⊗[D] M)
  ∀ m : M, HasSum (fun k : ι →₀ ℕ ↦ taylorMonomial B xi k ⊗ₜ[D] thetaPow k m)
    (c ((1 : (B : Type u)) ⊗ₜ[D] m))

/-- **The first input of the proof of [Stacks, Tag 07JH]: the Taylor comparison exists.**  For
every family `ξ : ι → B` of elements of the divided power ideal of `B` there is a `B`-linear
endomorphism of `B ⊗_D M` whose value on `1 ⊗ m` is the Taylor series `∑_K ξ^{[K]} ⊗ θ_K(m)`.

This is a proposition, not a theorem.  It is where the divided power coefficients in total degree
`≥ 2` and the `p`-adic convergence of the series enter; the part of the series in total degree
`≤ 1` is `Crystalline.firstOrderComparisonEquivConnection`.  Given the convergence, it is
equivalent to the untwisted `D`-linearity of the Taylor sum, which is not the source's condition;
see the module documentation. -/
noncomputable def HasTaylorComparison (thetaPow : (ι →₀ ℕ) → (M → M)) : Prop :=
  ∀ xi : ι → (B : Type u), (∀ i, xi i ∈ B.ideal) →
    ∃ c : ((B : Type u) ⊗[D] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[D] M),
      IsTaylorComparison p D B M thetaPow xi c

/-- **The second input of the proof of [Stacks, Tag 07JH]: the cocycle identity**
`c_{g,h} ∘ c_{f,g} = c_{f,h}`.  For three divided power maps `f, g, h : D → B` agreeing modulo the
divided power ideal of `B` the three families of differences satisfy
`ξ_{f,h} = ξ_{f,g} + ξ_{g,h}`, so the identity reads: the composite of the Taylor comparisons of
`ξ` and of `η` is the Taylor comparison of `ξ + η`.  It is this identity that makes the pairs
`(M, ∇)` of [Stacks, Tag 07JH] into a crystal rather than a mere family of comparison maps.

This is a proposition, not a theorem.  The quasi-nilpotence condition (07JE) is what makes the
series finite modulo `p`, hence the composite computable term by term. -/
noncomputable def TaylorCocycle (thetaPow : (ι →₀ ℕ) → (M → M)) : Prop :=
  ∀ (xi eta : ι → (B : Type u)), (∀ i, xi i ∈ B.ideal) → (∀ i, eta i ∈ B.ideal) →
    ∀ c c' c'' : ((B : Type u) ⊗[D] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[D] M),
      IsTaylorComparison p D B M thetaPow xi c →
        IsTaylorComparison p D B M thetaPow eta c' →
          IsTaylorComparison p D B M thetaPow (xi + eta) c'' → c' ∘ₗ c = c''

end Taylor

end Crystalline

end
