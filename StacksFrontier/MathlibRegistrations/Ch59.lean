module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Etale.StandardEtale
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.RingTheory.Henselian
import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-! # Mathlib declarations carrying tags of Stacks Chapter 59 (Étale Cohomology)

Each registration names a Mathlib declaration that states the tag (or the part named in its
comment).

The `example`s only record, as checked statements, how the registered declarations combine
where a tag is covered by more than one of them.

## Sites given by coverings

The sites of this chapter (Tag 03NH) are categories with a set `Cov(C)` of covering families,
stable under isomorphisms, composition and base change, the fibre products of a covering along
any morphism existing.  In Mathlib this is a `CategoryTheory.Precoverage` with the instances
`HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange` and `HasPullbacks`; Mathlib's
sheaf conditions are stated for the Grothendieck topology `J.toGrothendieck` it generates, and
the registrations below record the Mathlib lemmas that reduce them to the coverings themselves.
Since `{id_U}` is a covering of every object `U`, the objects of such a site form a set, so a
Stacks site is a small category.

* Tag 03NK (separated presheaves and sheaves, of sets and of abelian groups).  For one covering,
  `Presieve.IsSeparatedFor` is injectivity of `F(U) → ∏ F(Uᵢ)` (second `example`) and
  `Equalizer.Presieve.Arrows.sheaf_condition` says the sheaf condition for the covering is the
  equalizer diagram of the tag, indexed by the family itself (with repetitions) and built on the
  fibre products `Uᵢ ×_U Uⱼ`.  Over the whole site: `Presieve.IsSeparated` and `Presieve.IsSheaf`
  for `J.toGrothendieck`, which are separatedness, resp. the sheaf property, for every covering
  (first `example`, resp. `Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange`).
  For abelian presheaves: `Presheaf.IsSeparated` (injectivity on the underlying sets) and
  `Presheaf.IsSheaf`, which by `Presheaf.isSheaf_iff_isSheaf_forget` holds iff the underlying
  presheaf of sets is a sheaf (third `example`); the forgetful functor from abelian groups
  preserves and reflects limits, so that is the equalizer diagram in abelian groups.
* Tag 03NM (the empty covering): `Presieve.isTerminal_of_isSheafFor_empty_presieve` (a presheaf
  of sets that is a sheaf for the empty family on `U` has `F(U)` terminal) and
  `Sheaf.isTerminalOfBotCover` (for sheaves with values in any category, e.g. abelian groups).
* Tag 03NN (on `X_Zar` these are the usual sheaves): `Opens.pretopology_toGrothendieck` says the
  open coverings generate Mathlib's topology on the opens of a space, and
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types` (sets) and
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing` (concrete categories such as abelian groups)
  say that the site sheaf condition is the usual unique-gluing condition.
* Tag 03NO (the categories `Sh(C)` and `Ab(C)`): Mathlib's `Sheaf J A` is by definition the full
  subcategory of presheaves that are sheaves (`ObjectProperty.FullSubcategory`), its inclusion
  is `fullyFaithfulSheafToPresheaf`, and `isSheaf_iff_isSheaf_of_type` identifies the objects of
  `Sheaf J (Type w)` with the sheaves of sets of Tag 03NK.
* Tag 03NR (zeroth Čech cohomology for a covering): `Presieve.Arrows.PullbackCompatible` is the
  condition `sᵢ|_{Uᵢ ×_U Uⱼ} = sⱼ|_{Uᵢ ×_U Uⱼ}` on `(sᵢ) ∈ ∏ F(Uᵢ)`, so `Ȟ⁰(𝒰, F)` is the set of
  families satisfying it; `Equalizer.Presieve.Arrows.compatible_iff` says this is the equalizer
  of the two maps `∏ F(Uᵢ) ⇉ ∏ F(Uᵢ ×_U Uⱼ)`; for a covering written as a pre-`0`-hypercover,
  `PreOneHypercover.multicospanIndex` is the Čech diagram in any target category (its
  multiequalizer in abelian groups is the group `Ȟ⁰(𝒰, F)`) and
  `PreZeroHypercover.sectionsEquivOfHasPullbacks` identifies its sections with the compatible
  families.
* Tag 03NU (abelian sheaves form an abelian category with enough injectives): the instances
  `sheafIsAbelian` (abelian, whenever sheafification exists) and, for a small site,
  `Sheaf.instIsGrothendieckAbelian` (Grothendieck abelian) with
  `IsGrothendieckAbelian.enoughInjectives` (enough injectives).  Mathlib's smallness hypothesis
  is not an extra one: Stacks sites are small, see above.  The fourth and fifth `example`s state
  both parts for `Sheaf J AddCommGrpCat` on a small site.

## The fpqc topology

* Tag 03NW (fpqc coverings): `AlgebraicGeometry.Scheme.fpqcPrecoverage`, whose coverings are the
  families that are jointly surjective, consist of flat morphisms (condition (1)) and form a
  `AlgebraicGeometry.QuasiCompactCover` (condition (2)); the sixth `example` unfolds membership.
  `QuasiCompactCover` asks every affine open to be a finite union of images of quasi-compact
  opens; `QuasiCompactCover.exists_isAffineOpen_of_isCompact` gives the affine opens of
  condition (2), and the seventh `example` proves the two forms of condition (2) equivalent.
* Tag 03O3 (representable presheaves on `Sch/S` are fpqc sheaves): the instance
  `Scheme.instSubcanonicalFpqcTopology` (the fpqc topology on schemes is subcanonical) and
  `GrothendieckTopology.subcanonical_over`, which passes subcanonicity to the topology
  `J.over S` on `Over S`, whose coverings are the families over `S` that are coverings of
  schemes, i.e. the big fpqc site `Sch/S` (eighth and ninth `example`).

## Yoneda

* Tag 03ON: `yonedaEquiv` is the bijection `Hom(h_U, F) ≃ F(U)` and `yonedaLemma` is the
  isomorphism of functors of `(U, F)`, i.e. its functoriality.

## Not registered here

Tag 03OH (quasi-coherent modules on a ringed site) is registered on the draft predicate
`SheafOfModules.IsQuasicoherentOnSite` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSheaves.Basic`, not on a Mathlib
declaration.  Mathlib's `SheafOfModules.IsQuasicoherent` asks for one family of objects covering
the terminal object (`GrothendieckTopology.CoversTop`) with a presentation of the restriction to
each member, while the Stacks definition asks, for every object `U`, for a covering of `U` with
presentations on the members.

This file records Stacks Project tags from Chapter 59 (Étale Cohomology) whose statements are
already available in Mathlib, by attaching each tag to the Mathlib declarations that state it.
When a tag is covered by several declarations, each registration names the part it covers.
Mathlib has no notion of étale neighbourhood; an étale neighbourhood `(U, u) → (S, s)` is an
étale morphism `U → S` sending `u` to `s`. Geometric points are morphisms from the spectrum of a
separably closed field, which includes the algebraically closed fields of the Stacks definition.
* 04HT: only the converse direction, that an étale neighbourhood `(U, u)` of `(S, s)` lifts to
  an étale neighbourhood `(U, ū)` of `(S, s̄)`. The first direction, taking for `u` the image of
  `ū`, is not a separate Mathlib statement.
* [Stacks: Étale Cohomology](https://stacks.math.columbia.edu/tag/04HT)

## References

* [Stacks Project, Chapter 59](https://stacks.math.columbia.edu/tag/03N1)
-/

@[expose] public section

add_to_stacks 03N5 AlgebraicGeometry.Scheme.etalePrecoverage

add_to_stacks 03NC CategoryTheory.Functor

add_to_stacks 03ND "definition of h_X, the representable presheaf `U ↦ Mor(U, X)`" CategoryTheory.yoneda

add_to_stacks 03NE CategoryTheory.Yoneda.fullyFaithful

add_to_stacks 03NG CategoryTheory.PreZeroHypercover

add_to_stacks 03NI "the site itself: the opens of `X` with the inclusions as morphisms, and the
  jointly covering families as coverings" Opens.pretopology

add_to_stacks 03NI "the category of opens has fibre products, with `U ×_W V = U ⊓ V`"
  CategoryTheory.Limits.CompleteLattice.pullback_eq_inf

add_to_stacks 03OO "Z_G(U) = Z[G(U)]: the free presheaf of modules on G, over the constant \
  presheaf of rings Z (Z_U is the case G = h_U)" PresheafOfModules.freeObj
add_to_stacks 03PB "Mathlib's étale morphisms are exactly the smooth morphisms of relative \
  dimension 0" AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero
add_to_stacks 03PD "B is standard étale over A: B ≅ (A[t]/(f))_g with f monic and df/dt \
  invertible in B" Algebra.IsStandardEtale
add_to_stacks 03PG "the étale coverings: families of étale morphisms that are jointly surjective"
  AlgebraicGeometry.Scheme.etalePrecoverage
add_to_stacks 03PP "an S-morphism between étale S-schemes is étale"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
open AlgebraicGeometry.Scheme in
add_to_stacks 03PQ "the étale neighborhoods of a geometric point s : Spec Ω → S (Ω separably \
  closed) form a cofiltered category"
  instIsCofilteredElementsEtaleCompOverForgetObjOppositeFunctorTypeCoyonedaOpMk

namespace Stacks.Ch59MathlibRegistrations

open CategoryTheory Limits Opposite

universe w v u

section Sites

variable {C : Type u} [Category.{v} C]

/-- Tag 03NK, separated presheaves of sets: for the topology generated by the coverings of a
site, Mathlib's `Presieve.IsSeparated` is separatedness for every covering. -/
example (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSeparated J.toGrothendieck P ↔
      ∀ ⦃X : C⦄ (R : Presieve X), R ∈ J X → R.IsSeparatedFor P := by
  refine ⟨fun h X R hR ↦ ?_, fun h X S hS ↦ ?_⟩
  · rw [Presieve.isSeparatedFor_iff_generate]
    exact h _ (Precoverage.generate_mem_toGrothendieck hR)
  · obtain ⟨R, hR, hle⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.1 hS
    intro x t₁ t₂ h₁ h₂
    exact h R hR (x.restrict hle) t₁ t₂ (Presieve.isAmalgamation_restrict hle x t₁ h₁)
      (Presieve.isAmalgamation_restrict hle x t₂ h₂)

/-- Tag 03NK, one covering: separatedness for a family `{πᵢ : Uᵢ → X}` is injectivity of
`F(X) → ∏ᵢ F(Uᵢ)`, `s ↦ (s|_{Uᵢ})ᵢ`. -/
example {X : C} {ι : Type*} (U : ι → C) (π : ∀ i, U i ⟶ X) (P : Cᵒᵖ ⥤ Type w) :
    (Presieve.ofArrows U π).IsSeparatedFor P ↔
      Function.Injective (fun (s : P.obj (op X)) (i : ι) ↦ P.map (π i).op s) := by
  refine ⟨fun h s t hst ↦ h.ext ?_, fun h x t₁ t₂ h₁ h₂ ↦ h ?_⟩
  · rintro _ _ ⟨i⟩
    exact congr_fun hst i
  · funext i
    exact (h₁ _ (Presieve.ofArrows.mk i)).trans (h₂ _ (Presieve.ofArrows.mk i)).symm

end Sites

section Abelian

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)

/-- Tag 03NK, abelian sheaves: an abelian presheaf is a sheaf iff its underlying presheaf of
sets is one. -/
example (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J (P ⋙ forget AddCommGrpCat) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J P (forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]

/-- Tag 03NU, first part: abelian sheaves on a small site form an abelian category. -/
noncomputable example : Abelian (Sheaf J AddCommGrpCat.{v}) := inferInstance

/-- Tag 03NU, second part: abelian sheaves on a small site have enough injectives. -/
example : EnoughInjectives (Sheaf J AddCommGrpCat.{v}) := inferInstance

end Abelian

section Fpqc

open AlgebraicGeometry

/-- Tag 03NW: a family is an fpqc covering iff it is jointly surjective, consists of flat
morphisms, and is a quasi-compact cover. -/
example {S : Scheme.{u}} (E : PreZeroHypercover.{w} S) :
    E.presieve₀ ∈ Scheme.fpqcPrecoverage S ↔
      ((∀ x, ∃ i, x ∈ Set.range (E.f i)) ∧ ∀ i, Flat (E.f i)) ∧ QuasiCompactCover E :=
  (and_congr Scheme.presieve₀_mem_qcPrecoverage_iff
    (Scheme.presieve₀_mem_precoverage_iff E)).trans and_comm

/-- Tag 03NW, condition (2): Mathlib's quasi-compact covers are exactly the families for which
every affine open is the union of the images of finitely many affine opens of the members. -/
example {S : Scheme.{u}} (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E ↔ ∀ {U : S.Opens}, IsAffineOpen U →
      ∃ (n : ℕ) (f : Fin n → E.I₀) (V : ∀ i, (E.X (f i)).Opens),
        (∀ i, IsAffineOpen (V i)) ∧ ⋃ i, E.f (f i) '' (V i) = U := by
  refine ⟨fun _ U hU ↦ QuasiCompactCover.exists_isAffineOpen_of_isCompact E hU.isCompact,
    fun h ↦ ⟨fun {U} hU ↦ ?_⟩⟩
  obtain ⟨n, f, V, hV, hU'⟩ := h hU
  exact .of_finite f V (fun i ↦ (hV i).isCompact) hU'

/-- Tag 03O3: the fpqc topology on `Sch/S` is subcanonical. -/
example (S : Scheme.{u}) : (Scheme.fpqcTopology.over S).Subcanonical := inferInstance

/-- Tag 03O3: a representable presheaf on `Sch/S` is a sheaf for the fpqc topology. -/
example (S : Scheme.{u}) (T : Over S) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj T) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end Fpqc

end Stacks.Ch59MathlibRegistrations

add_to_stacks 03NK "separated presheaf of sets, for one covering"
  CategoryTheory.Presieve.IsSeparatedFor
add_to_stacks 03NK "separated presheaf of sets on a site" CategoryTheory.Presieve.IsSeparated
add_to_stacks 03NK "separated abelian presheaf" CategoryTheory.Presheaf.IsSeparated
add_to_stacks 03NK "the sheaf condition for one covering, as the equalizer diagram"
  CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition
add_to_stacks 03NK "sheaf of sets on a site" CategoryTheory.Presieve.IsSheaf
add_to_stacks 03NK "the sheaf condition is checked on the coverings"
  CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange
add_to_stacks 03NK "abelian sheaf" CategoryTheory.Presheaf.IsSheaf
add_to_stacks 03NK "an abelian presheaf is a sheaf iff its presheaf of sets is one"
  CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget

add_to_stacks 03NM "sheaves of sets"
  CategoryTheory.Presieve.isTerminal_of_isSheafFor_empty_presieve
add_to_stacks 03NM "sheaves with values in any category, e.g. abelian groups"
  CategoryTheory.Sheaf.isTerminalOfBotCover

add_to_stacks 03NN "the open coverings generate the topology of X_Zar"
  Opens.pretopology_toGrothendieck
add_to_stacks 03NN "sheaves of sets" TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
add_to_stacks 03NN "sheaves with values in a concrete category, e.g. abelian groups"
  TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing

add_to_stacks 03NO "the full subcategory of sheaves" CategoryTheory.Sheaf
add_to_stacks 03NO "the inclusion into presheaves is fully faithful"
  CategoryTheory.fullyFaithfulSheafToPresheaf
add_to_stacks 03NO "the objects of Sh(C) are the sheaves of sets"
  CategoryTheory.isSheaf_iff_isSheaf_of_type

add_to_stacks 03NR "the compatibility condition defining the zeroth Čech cohomology"
  CategoryTheory.Presieve.Arrows.PullbackCompatible
add_to_stacks 03NR "as the equalizer of the two maps to the products over the Uᵢ ×_U Uⱼ"
  CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff
add_to_stacks 03NR "the Čech diagram, whose multiequalizer is the zeroth Čech cohomology"
  CategoryTheory.PreOneHypercover.multicospanIndex
add_to_stacks 03NR "the sections of the Čech diagram are the compatible families"
  CategoryTheory.PreZeroHypercover.sectionsEquivOfHasPullbacks

add_to_stacks 03NU "abelian category" CategoryTheory.sheafIsAbelian
add_to_stacks 03NU "Grothendieck abelian category, for a small site"
  CategoryTheory.Sheaf.instIsGrothendieckAbelian
add_to_stacks 03NU "enough injectives, for a Grothendieck abelian category"
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

add_to_stacks 03NW "fpqc coverings" AlgebraicGeometry.Scheme.fpqcPrecoverage
add_to_stacks 03NW "condition (2)" AlgebraicGeometry.QuasiCompactCover
add_to_stacks 03NW "condition (2) with affine opens"
  AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact

add_to_stacks 03O3 "on the category of all schemes"
  AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_stacks 03O3 "passage to Sch/S" CategoryTheory.GrothendieckTopology.subcanonical_over

add_to_stacks 03ON "the bijection" CategoryTheory.yonedaEquiv
add_to_stacks 03ON "functoriality" CategoryTheory.yonedaLemma

add_to_stacks 04HT "converse: a geometric point ū of U over u with (U, ū) → (S, s̄)"
  AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed

-- Definition: a henselian local ring.
add_to_stacks 03QF HenselianLocalRing
add_to_stacks 03QF "Stacks' formulation, with `a₀` in the residue field (item 2)"
  HenselianLocalRing.TFAE

-- Complete local rings are henselian.
add_to_stacks 03QG
  "for `I = maximalIdeal R`, `HenselianRing R (maximalIdeal R)` is the condition of 03QF"
  IsAdicComplete.henselianRing

-- Definition: two finite central simple algebras are similar if their matrix algebras agree.
add_to_stacks 03R3 IsBrauerEquivalent
