module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TruncatingApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# Bounded local strictly perfect approximations on a ringed site

Let `(C, O)` be a ringed site and let `K` be an `m`-pseudo-coherent object of `D(O)` whose
cohomology vanishes in degrees `> a`, with `m ≤ a`. This file proves that `K` is represented
by a complex `E` such that every object `U` of `C` carries a covering family over each member
`V` of which `E|_V` receives a map from a strictly perfect complex *with no terms above degree
`a`* which is an isomorphism on cohomology in degrees `> m` and an epimorphism in degree `m`.

This is the shrinking step that the Stacks proof of Tag 08DN performs inline — "the map
`E^{n-1} ⟶ E^n` is surjective as `H^n(E) = 0`; we can locally find a section of this
surjection and write `E^{n-1} = E' ⊕ E^n` " — carried out on a site and run as a downward
induction over the finitely many degrees between `a` and the top nonzero degree. The ringed
space analogue is
`StrictlyPerfect.exists_local_isStrictlyPerfect_approximation_boundedAbove` of
`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximationLocal.lean`; neither statement
specialises to the other inside Lean, one being about a point-indexed cover of a `RingedSpace`
and the other about covering sieves of a site. The two *predicates* do agree where both are
defined — `StrictlyPerfect.IsStrictlyPerfect` on a ringed space and the `IsStrictlyPerfect` of
Stacks 08FL at that space's structure sheaf of rings are equivalent, by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff` — so that difference of
vocabulary is not the reason.

## Main definitions

* `Stacks.SheafOfModules.overMapComp`: restricting sheaves of modules along `f : V ⟶ U` and
  then along `g : W ⟶ V` is restricting along `g ≫ f`.
* `Stacks.SheafOfModules.restrictComplexAlong`: the degreewise restriction `P|_W` of a complex
  of `O|_V`-modules along an arrow `g : W ⟶ V` of the site, together with the two comparison
  isomorphisms `restrictComplexAlongCompIso` and `restrictComplexAlongOverIso`.
* `Stacks.SheafOfModules.restrictCyclesAlongIso`: the cycles comparison for that restriction.

## Main results

* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_overMap` and
  `isStrictlyPerfect_restrictComplexAlong`: restriction along an arrow of the site preserves
  "direct summand of a finite free module" and strict perfection.
* `Stacks.SheafOfModules.epi_toCycles_restrictComplexAlong`: it preserves surjectivity of
  `P^i ⟶ Z^j(P)`.
* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_cycles_of_section`: a section of
  `P^k ⟶ Z^{k+1}(P)` exhibits `Z^k(P)` as a retract of `P^k`, hence as a direct summand of a
  finite free module as soon as `P^k` is one.
* `Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles`: **the
  shrinking induction** — the degree-`r` cycles of a strictly perfect complex in which
  `P^k ⟶ Z^{k+1}(P)` is surjective for every `k ≥ r` become a direct summand of a finite free
  module over the members of a covering sieve.
* `AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex`: restriction to a slice
  preserves vanishing of a cohomology sheaf.
* `AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove`: the
  statement described above.

## Implementation notes

**Where the local lifting comes from.** The one non-formal input is that a map out of a direct
summand of a finite free module lifts through an epimorphism after passing to a covering
family. It is taken here as
`Stacks.SheafOfModules.LocalCokernel.exists_local_lift`, whose conclusion is already phrased
over a *single* slice `C/W` through `SheafOfModules.overMap`. The alternative,
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift` (Stacks 08FN), produces its lift over
the iterated slice `(C/V)/W` and is stated only at equal site universes, so using it would
have required both a universe generalization and the iterated-slice identification
`Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`. Neither is needed.

**Why the restriction functors compose.** The shrinking induction produces one covering sieve
per degree and composes the finitely many refinements with `Sieve.bind`, which turns the
arrow `W ⟶ V` of the composite sieve into a factorization `g₂ ≫ g₁`. The statement proved at
each step is about `(P|_{g₁})|_{g₂}` and the statement needed is about `P|_{g₂ ≫ g₁}`; the
bridge is `overMapComp`, the sheaf-of-modules form of `CategoryTheory.Over.mapComp`. Its
construction goes through Mathlib's `SheafOfModules.pushforwardComp` and
`pushforwardCongr₂`: the two pushforward functors are definitionally equal, and the
comparison of the structure maps of the sheaves of rings is the identity on sections.

**Two spellings of one complex.** `restrictComplexAlong R g P` and
`((SheafOfModules.overMap R g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P` are the same
term, but `((P.sc j).map (SheafOfModules.overMap R g)).cycles` and
`(restrictComplexAlong R g P).cycles j` are only definitionally equal, and a `rw` does not
cross between them. `restrictCyclesAlongIso` therefore repackages Mathlib's
`ShortComplex.mapCyclesIso` with its source spelled in the second form, and the two places
below where a morphism has to be re-ascribed before being composed go through
`obtain ⟨_, _⟩ : ∃ _, _`. No `erw` and no `set_option` is used.

**Reuse rather than restatement.** `AlgebraicGeometry.RingedSpace.isIso_homologyMap_map` and
`epi_homologyMap_map` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BoundedApproximation.lean` are stated for an
arbitrary exact additive functor between abelian categories, so they apply verbatim here
despite their ringed-space namespace; that is why this file imports a ringed-space module. For
the same reason no analogue of `StrictlyPerfect.Truncation.retractCyclesOfSection` is
declared: the retract is built inline inside
`isDirectSummandOfFiniteFree_cycles_of_section`, whose conclusion is the summand statement the
three existing ringed-space copies are only ever used for, and the surjectivity of
`P^k ⟶ Z^{k+1}(P)` is obtained from the vanishing of `H^{k+1}` by
`Preadditive.epi_of_isZero_cokernel'` applied directly to
`HomologicalComplex.homologyIsCokernel`.

## References

* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v d

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{0}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Restriction of sheaves of modules along an arrow of the site preserves finite colimits. -/
local instance preservesFiniteColimitsOverMap {U V : C} (g : V ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{0} R g) :=
  LocalCokernel.overMap_preservesFiniteColimits g

/-- Restriction of sheaves of modules along an arrow of the site preserves finite limits. -/
local instance preservesFiniteLimitsOverMap {U V : C} (g : V ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{0} R g) :=
  LocalCokernel.overMap_preservesFiniteLimits g

/-! ### Restriction of complexes along an arrow of the site -/

/-- Restricting sheaves of modules along `f : V ⟶ U` and then along `g : W ⟶ V` is restricting
along `g ≫ f`.

Both functors are pushforwards, along `Over.map g ⋙ Over.map f` and along `Over.map (g ≫ f)`
respectively; those two functors of slice categories are naturally isomorphic by
`CategoryTheory.Over.mapComp`, and the induced comparison of the structure maps of the sheaves
of rings is the identity on sections. -/
def overMapComp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    SheafOfModules.overMap.{0} R f ⋙ SheafOfModules.overMap.{0} R g ≅
      SheafOfModules.overMap.{0} R (g ≫ f) := by
  have : (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_
  refine SheafOfModules.pushforwardCongr₂ _ (Over.mapComp g f) ?_
  ext T : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have h1 : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapComp g f).hom RingCat
      (J.over W) (J.over U)).app (R.over U)).hom.app T = 𝟙 _ := by
    simp; rfl
  rw [h1]
  rfl

/-- The restriction `P|_W` of a cochain complex of `O|_V`-modules along an arrow `g : W ⟶ V`
of the site, formed degreewise. -/
abbrev restrictComplexAlong {V W : C} (g : W ⟶ V)
    (P : CochainComplex (SheafOfModules.{0} (R.over V)) ℤ) :
    CochainComplex (SheafOfModules.{0} (R.over W)) ℤ :=
  ((SheafOfModules.overMap.{0} R g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- Restricting a complex along `f` and then along `g` is restricting it along `g ≫ f`. -/
def restrictComplexAlongCompIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ) :
    restrictComplexAlong R g (restrictComplexAlong R f P) ≅
      restrictComplexAlong R (g ≫ f) P :=
  (Functor.mapHomologicalComplexCompIso (overMapComp R f g) (ComplexShape.up ℤ)).app P

/-- Restricting a complex of `O`-modules to `V` and then along `g : W ⟶ V` is restricting it
to `W`. -/
def restrictComplexAlongOverIso {V W : C} (g : W ⟶ V)
    (E : CochainComplex (SheafOfModules.{0} R) ℤ) :
    restrictComplexAlong R g
        (((SheafOfModules.overFunctor R V).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      ((SheafOfModules.overFunctor R W).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  (Functor.mapHomologicalComplexCompIso (SheafOfModules.overFunctorMap R g)
    (ComplexShape.up ℤ)).app E

/-! ### What restriction along an arrow of the site preserves -/

/-- Restriction along an arrow of the site preserves being a direct summand of a finite free
module: it carries a finite free module to a finite free module of the same rank, by
`SheafOfModules.mapFreeIso`, and a retraction to a retraction. -/
theorem isDirectSummandOfFiniteFree_overMap {U V : C} (g : V ⟶ U)
    {F : SheafOfModules.{0} (R.over U)} (hF : IsDirectSummandOfFiniteFree (R.over U) F) :
    IsDirectSummandOfFiniteFree (R.over V) ((SheafOfModules.overMap.{0} R g).obj F) := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free (R.over U) F).mp hF
  have e : SheafOfModules.free (R := R.over V) (ULift.{0} (Fin n)) ≅
      (SheafOfModules.overMap.{0} R g).obj (SheafOfModules.free (ULift.{0} (Fin n))) :=
    SheafOfModules.mapFreeIso (SheafOfModules.overMap.{0} R g) (ULift.{0} (Fin n))
      (SheafOfModules.overMapUnitIso (R := R) g)
  refine (isDirectSummandOfFiniteFree_iff_free (R.over V) _).mpr
    ⟨n, (SheafOfModules.overMap.{0} R g).map i ≫ e.inv,
      e.hom ≫ (SheafOfModules.overMap.{0} R g).map r, ?_⟩
  rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
    ← Functor.map_comp, hir, CategoryTheory.Functor.map_id]

/-- Restriction along an arrow of the site preserves strict perfection. -/
theorem isStrictlyPerfect_restrictComplexAlong {U V : C} (g : V ⟶ U)
    {P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ}
    (hP : IsStrictlyPerfect (R.over U) P) :
    IsStrictlyPerfect (R.over V) (restrictComplexAlong R g P) where
  bounded := hP.bounded.subset (fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi ((SheafOfModules.overMap.{0} R g).map_isZero hz))
  termDirectSummand i := isDirectSummandOfFiniteFree_overMap R g (hP.termDirectSummand i)

/-- An exact functor commutes with the cycles of a complex; here the comparison for
restriction along an arrow of the site, with its source spelled as the cycles of the
restricted complex rather than as the cycles of a mapped short complex. -/
def restrictCyclesAlongIso {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ) (k : ℤ) :
    (restrictComplexAlong R g P).cycles k ≅
      (SheafOfModules.overMap.{0} R g).obj (P.cycles k) :=
  ShortComplex.mapCyclesIso (P.sc k) (SheafOfModules.overMap.{0} R g)

/-- The cycles comparison for restriction along an arrow of the site is compatible with the
inclusions of the cycles. -/
@[reassoc]
lemma restrictCyclesAlongIso_hom_iCycles {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ) (k : ℤ) :
    (restrictCyclesAlongIso R g P k).hom ≫ (SheafOfModules.overMap.{0} R g).map (P.iCycles k) =
      (restrictComplexAlong R g P).iCycles k :=
  ShortComplex.mapCyclesIso_hom_iCycles (P.sc k) (SheafOfModules.overMap.{0} R g)

/-- The cycles comparison for restriction along an arrow of the site is compatible with
`toCycles`. -/
lemma toCycles_comp_restrictCyclesAlongIso_hom {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ) (i j : ℤ) :
    (restrictComplexAlong R g P).toCycles i j ≫ (restrictCyclesAlongIso R g P j).hom =
      (SheafOfModules.overMap.{0} R g).map (P.toCycles i j) := by
  have hmono : Mono ((SheafOfModules.overMap.{0} R g).map (P.iCycles j)) := inferInstance
  rw [← cancel_mono ((SheafOfModules.overMap.{0} R g).map (P.iCycles j)), Category.assoc,
    restrictCyclesAlongIso_hom_iCycles, HomologicalComplex.toCycles_i,
    ← Functor.map_comp, HomologicalComplex.toCycles_i]
  rfl

/-- Restriction along an arrow of the site preserves surjectivity of `P^i ⟶ Z^j(P)`. -/
theorem epi_toCycles_restrictComplexAlong {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{0} (R.over U)) ℤ) (i j : ℤ)
    (h : Epi (P.toCycles i j)) :
    Epi ((restrictComplexAlong R g P).toCycles i j) := by
  have : (SheafOfModules.overMap.{0} R g).PreservesEpimorphisms :=
    LocalCokernel.overMap_preservesEpimorphisms g
  have := h
  have hT := (SheafOfModules.overMap.{0} R g).map_epi (P.toCycles i j)
  rw [← toCycles_comp_restrictCyclesAlongIso_hom] at hT
  exact (epi_comp_iff_of_isIso _ _).mp hT

/-! ### The shrinking induction -/

/-- A section of `P^k ⟶ Z^{k+1}(P)` exhibits `Z^k(P)` as a retract of `P^k`, hence as a direct
summand of a finite free module as soon as `P^k` is one.

The retraction of `Z^k(P)` onto `P^k` is `1 - d ∘ s` read on cycles; it kills the differential
because `s` is a section, and it restricts to the identity on cycles because the cycles are
killed by `P^k ⟶ Z^{k+1}(P)`. -/
theorem isDirectSummandOfFiniteFree_cycles_of_section {V : C}
    {P : CochainComplex (SheafOfModules.{0} (R.over V)) ℤ} (k : ℤ)
    (s : P.cycles (k + 1) ⟶ P.X k) (hs : s ≫ P.toCycles k (k + 1) = 𝟙 (P.cycles (k + 1)))
    (hXk : IsDirectSummandOfFiniteFree (R.over V) (P.X k)) :
    IsDirectSummandOfFiniteFree (R.over V) (P.cycles k) := by
  have hiz : P.iCycles k ≫ P.toCycles k (k + 1) = 0 := by
    rw [← cancel_mono (P.iCycles (k + 1)), Category.assoc, P.toCycles_i, zero_comp,
      P.iCycles_d k (k + 1)]
  have hsd : s ≫ P.d k (k + 1) = P.iCycles (k + 1) := by
    rw [← P.toCycles_i k (k + 1), ← Category.assoc, hs, Category.id_comp]
  have hp : (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) ≫ P.d k (k + 1) = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsd, P.toCycles_i, sub_self]
  refine IsDirectSummandOfFiniteFree.of_retract (R.over V)
    ⟨P.iCycles k,
      P.liftCycles (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) (k + 1) (by simp) hp, ?_⟩ hXk
  rw [← cancel_mono (P.iCycles k), Category.assoc, P.liftCycles_i, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hiz, zero_comp, sub_zero, Category.id_comp]

/-- **The shrinking induction on a site.** Let `P` be a strictly perfect complex of
`O|_V`-modules in which `P^k ⟶ Z^{k+1}(P)` is surjective in every degree `k ≥ r`. Then there
is a covering sieve of `V` over each member of which the degree-`r` cycles of `P` are a direct
summand of a finite free module.

The induction runs downwards from the top nonzero degree of `P`, where the cycles vanish, to
`r`. At each step the already-known retraction of `Z^{k+1}` onto a finite free module turns,
by the local lifting of `Stacks.SheafOfModules.LocalCokernel.exists_local_lift`, into a
*section* of `P^k ⟶ Z^{k+1}(P)` over the members of a covering sieve — which is exactly what
exhibits `Z^k(P)` as a retract of `P^k`. The finitely many refinements are composed with
`Sieve.bind`, and the two restrictions a composed arrow carries are identified with the single
restriction along it by `restrictComplexAlongCompIso`. -/
theorem exists_coveringSieve_isDirectSummandOfFiniteFree_cycles {V : C}
    (P : CochainComplex (SheafOfModules.{0} (R.over V)) ℤ)
    (hP : IsStrictlyPerfect (R.over V) P) (r : ℤ)
    (hepi : ∀ k : ℤ, r ≤ k → Epi (P.toCycles k (k + 1))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      IsDirectSummandOfFiniteFree (R.over W) ((restrictComplexAlong R g P).cycles r) := by
  classical
  have hweak : ∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{0} := fun _ => inferInstance
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i) := by
    obtain ⟨N, hNb⟩ := hP.bounded.bddAbove
    refine ⟨N, fun i hi => ?_⟩
    by_contra hcon
    exact absurd (hNb hcon) (not_le.2 hi)
  have main : ∀ j : ℕ, ∀ k : ℤ, r ≤ k → (∀ i : ℤ, k + (j : ℤ) ≤ i → IsZero (P.X i)) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
        IsDirectSummandOfFiniteFree (R.over W) ((restrictComplexAlong R g P).cycles k) := by
    intro j
    induction j with
    | zero =>
      intro k _ hk
      refine ⟨⊤, J.top_mem V, fun W g _ => ?_⟩
      refine IsDirectSummandOfFiniteFree.of_isZero (R.over W)
        (IsZero.of_mono ((restrictComplexAlong R g P).iCycles k) ?_)
      exact (SheafOfModules.overMap.{0} R g).map_isZero (hk k (by simp))
    | succ j ih =>
      intro k hrk hk
      obtain ⟨T₁, hT₁, hcyc₁⟩ := ih (k + 1) (by omega) (by
        intro i hi
        exact hk i (by push_cast at hi ⊢; omega))
      have key : ∀ (V₁ : C) (g₁ : V₁ ⟶ V), T₁ g₁ →
          ∃ T₂ : Sieve V₁, T₂ ∈ J V₁ ∧ ∀ ⦃W : C⦄ (g₂ : W ⟶ V₁), T₂ g₂ →
            IsDirectSummandOfFiniteFree (R.over W)
              ((restrictComplexAlong R (g₂ ≫ g₁) P).cycles k) := by
        intro V₁ g₁ hg₁
        have hQsp : IsStrictlyPerfect (R.over V₁) (restrictComplexAlong R g₁ P) :=
          isStrictlyPerfect_restrictComplexAlong R g₁ hP
        have hQepi : Epi ((restrictComplexAlong R g₁ P).toCycles k (k + 1)) :=
          epi_toCycles_restrictComplexAlong R g₁ P k (k + 1) (hepi k hrk)
        obtain ⟨n, iX, rX, hX⟩ :=
          (isDirectSummandOfFiniteFree_iff_free (R.over V₁) _).mp (hQsp.termDirectSummand k)
        obtain ⟨mm, jZ, sZ, hZ⟩ :=
          (isDirectSummandOfFiniteFree_iff_free (R.over V₁) _).mp (hcyc₁ g₁ hg₁)
        have : IsSplitEpi rX := IsSplitEpi.mk' ⟨iX, hX⟩
        have : Epi (rX ≫ (restrictComplexAlong R g₁ P).toCycles k (k + 1)) := epi_comp _ _
        obtain ⟨S₂, hS₂, hlift⟩ :=
          LocalCokernel.exists_local_lift (R := R) (U := V₁)
            (N := (restrictComplexAlong R g₁ P).cycles (k + 1))
            (I := ULift.{0} (Fin mm)) (K := ULift.{0} (Fin n))
            (rX ≫ (restrictComplexAlong R g₁ P).toCycles k (k + 1)) sZ
        refine ⟨Sieve.overEquiv (Over.mk (𝟙 V₁)) S₂, (J.mem_over_iff S₂).mp hS₂, ?_⟩
        intro W g₂ hg₂
        have harr : S₂.arrows
            (Over.homMk (U := Over.mk g₂) (V := Over.mk (𝟙 V₁)) g₂ (by simp)) := by
          have h1 : S₂ (Over.homMk (U := Over.mk (g₂ ≫ (Over.mk (𝟙 V₁)).hom)) g₂) :=
            (Sieve.overEquiv_iff S₂ g₂).mp hg₂
          have h2 := S₂.downward_closed h1
            (Over.homMk (U := Over.mk g₂) (V := Over.mk (g₂ ≫ (Over.mk (𝟙 V₁)).hom))
              (𝟙 W) (by simp))
          have h3 : (Over.homMk (U := Over.mk g₂)
                (V := Over.mk (g₂ ≫ (Over.mk (𝟙 V₁)).hom)) (𝟙 W) (by simp)) ≫
              (Over.homMk (U := Over.mk (g₂ ≫ (Over.mk (𝟙 V₁)).hom)) g₂ :
                _ ⟶ Over.mk (𝟙 V₁)) =
              Over.homMk (U := Over.mk g₂) (V := Over.mk (𝟙 V₁)) g₂ (by simp) := by
            apply Over.OverMorphism.ext
            simp
          rwa [h3] at h2
        obtain ⟨ℓ, hℓ⟩ := hlift g₂ harr
        obtain ⟨eI, eK, hℓ'⟩ :
            ∃ (eI : SheafOfModules.free (R := R.over W) (ULift.{0} (Fin mm)) ≅
                (SheafOfModules.overMap.{0} R g₂).obj
                  (SheafOfModules.free (ULift.{0} (Fin mm))))
              (eK : SheafOfModules.free (R := R.over W) (ULift.{0} (Fin n)) ≅
                (SheafOfModules.overMap.{0} R g₂).obj
                  (SheafOfModules.free (ULift.{0} (Fin n)))),
              ℓ ≫ eK.hom ≫ (SheafOfModules.overMap.{0} R g₂).map
                  (rX ≫ (restrictComplexAlong R g₁ P).toCycles k (k + 1)) =
                eI.hom ≫ (SheafOfModules.overMap.{0} R g₂).map sZ :=
          ⟨_, _, hℓ⟩
        obtain ⟨σ, hσ⟩ : ∃ σ : (SheafOfModules.overMap.{0} R g₂).obj
              ((restrictComplexAlong R g₁ P).cycles (k + 1)) ⟶
              (restrictComplexAlong R g₂ (restrictComplexAlong R g₁ P)).X k,
            σ ≫ (SheafOfModules.overMap.{0} R g₂).map
                ((restrictComplexAlong R g₁ P).toCycles k (k + 1)) = 𝟙 _ := by
          refine ⟨(SheafOfModules.overMap.{0} R g₂).map jZ ≫ eI.inv ≫ ℓ ≫ eK.hom ≫
            (SheafOfModules.overMap.{0} R g₂).map rX, ?_⟩
          simp only [Category.assoc]
          rw [← Functor.map_comp, hℓ', Iso.inv_hom_id_assoc, ← Functor.map_comp, hZ,
            CategoryTheory.Functor.map_id]
        refine IsDirectSummandOfFiniteFree.of_iso (R.over W)
          (HomologicalComplex.cyclesMapIso (restrictComplexAlongCompIso R g₁ g₂ P) k).symm ?_
        refine isDirectSummandOfFiniteFree_cycles_of_section R k
          ((restrictCyclesAlongIso R g₂ (restrictComplexAlong R g₁ P) (k + 1)).hom ≫ σ) ?_
          ((isStrictlyPerfect_restrictComplexAlong R g₂ hQsp).termDirectSummand k)
        rw [← cancel_mono (restrictCyclesAlongIso R g₂ (restrictComplexAlong R g₁ P) (k + 1)).hom,
          Category.id_comp]
        simp only [Category.assoc]
        rw [toCycles_comp_restrictCyclesAlongIso_hom, hσ, Category.comp_id]
      refine ⟨Sieve.bind T₁ (fun V₁ g₁ hg₁ => (key V₁ g₁ hg₁).choose),
        J.bind_covering hT₁ (fun V₁ g₁ hg₁ => (key V₁ g₁ hg₁).choose_spec.1), ?_⟩
      intro W h hmem
      obtain ⟨Z, g, f, hf, hg, rfl⟩ := hmem
      exact (key Z f hf).choose_spec.2 g hg
  exact main (N + 1 - r).toNat r le_rfl (fun i hi => hN i (by omega))

end Stacks.SheafOfModules

/-! ### Pseudo-coherence, and the bounded-above local approximation -/

namespace AlgebraicGeometry.RingedSite

/-- Strict perfectness transported along a degreewise isomorphism of complexes: the two
conditions are a finiteness condition on the terms and a retract condition on each term, and an
isomorphism preserves both. -/
theorem isStrictlyPerfect_of_isoX {C : Type} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
    {P Q : CochainComplex (SheafOfModules.{0} R) ℤ} (e : ∀ i : ℤ, P.X i ≅ Q.X i)
    (hP : IsStrictlyPerfect R P) : IsStrictlyPerfect R Q where
  bounded := hP.bounded.subset fun i hi hz => hi ((e i).symm.isZero_iff.mpr hz)
  termDirectSummand i :=
    IsDirectSummandOfFiniteFree.of_retract R ⟨(e i).inv, (e i).hom, (e i).inv_hom_id⟩
      (hP.termDirectSummand i)

variable (X : RingedSite.{u, v, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Restriction to a slice of the site preserves finite limits. -/
local instance preservesFiniteLimitsOverFunctor (U : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction to a slice of the site preserves finite colimits. -/
local instance preservesFiniteColimitsOverFunctor (U : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- Restriction along an arrow of the site preserves finite limits. -/
local instance preservesFiniteLimitsOverMap' {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits. -/
local instance preservesFiniteColimitsOverMap' {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- Restriction to a slice of the site carries a complex of `O`-modules whose cohomology
vanishes in a degree to one whose cohomology vanishes in that degree: restriction is exact, and
an additive functor carries a zero object to a zero object. -/
theorem isZero_homology_restrictComplex (U : X.C)
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (i : ℤ)
    (h : IsZero (E.homology i)) : IsZero ((X.restrictComplex E U).homology i) :=
  IsZero.of_iso
    ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero h)
    (ShortComplex.mapHomologyIso (E.sc i)
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))

/-- **A pseudo-coherent derived object whose cohomology vanishes above `a` has local strictly
perfect approximations concentrated in degrees at most `a`.**

This is the shrinking step that the Stacks proof of Tag 08DN performs inline, stated once and
for all on a ringed site. It combines
`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles` — which
refines the covering until the degree-`a` cycles of the given approximation are a direct
summand of a finite free module — with the truncation
`SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation`. The approximation is
carried to the members of the refined covering by the exactness of restriction, and the
pseudo-coherence covering is composed with the refinements by `Sieve.bind`. -/
theorem exists_local_strictlyPerfect_approximation_boundedAbove
    [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m a : ℤ) (hma : m ≤ a) (hK : X.IsPseudoCoherentFrom K m)
    (hzero : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K)) :
    ∃ E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
      ∀ U : X.C, ∃ S : Presieve U, (Sieve.generate S ∈ X.J U) ∧
        ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
          ∃ P : CochainComplex
              (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
            (∀ i : ℤ, a < i → IsZero (P.X i)) ∧
            ∃ α : P ⟶ X.restrictComplex E V,
              (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
              Epi (HomologicalComplex.homologyMap α m) := by
  classical
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  have hEzero : ∀ i : ℤ, a < i → IsZero (E.homology i) := fun i hi =>
    (hzero i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors
            (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).app E).symm.trans
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).mapIso eE))
  refine ⟨E, ⟨eE⟩, fun U => ?_⟩
  obtain ⟨S₀, hS₀, hprop⟩ := hE U
  have key : ∀ (V : X.C) (f : V ⟶ U), S₀ f →
      ∃ T : Sieve V, T ∈ X.J V ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P : CochainComplex
            (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
          (∀ i : ℤ, a < i → IsZero (P.X i)) ∧
          ∃ α : P ⟶ X.restrictComplex E W,
            (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
            Epi (HomologicalComplex.homologyMap α m) := by
    intro V f hf
    obtain ⟨P₀, hP₀, α₀, hiso₀, hepi₀⟩ := hprop f hf
    have hP₀zero : ∀ i : ℤ, a < i → IsZero (P₀.homology i) := by
      intro i hi
      have : IsIso (HomologicalComplex.homologyMap α₀ i) := hiso₀ i (lt_of_le_of_lt hma hi)
      exact (X.isZero_homology_restrictComplex V E i (hEzero i hi)).of_iso
        (asIso (HomologicalComplex.homologyMap α₀ i))
    have hP₀epi : ∀ k : ℤ, a ≤ k → Epi (P₀.toCycles k (k + 1)) := fun k hk =>
      Preadditive.epi_of_isZero_cokernel' _ (P₀.homologyIsCokernel k (k + 1) (by simp))
        (hP₀zero (k + 1) (by omega))
    obtain ⟨T, hT, hcyc⟩ :=
      Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P₀ hP₀ a hP₀epi
    refine ⟨T, hT, ?_⟩
    intro W g hg
    obtain ⟨αW, hαWiso, hαWepi⟩ :
        ∃ αW : Stacks.SheafOfModules.restrictComplexAlong
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g P₀ ⟶
            X.restrictComplex E W,
          (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap αW i)) ∧
          Epi (HomologicalComplex.homologyMap αW m) := by
      have hι : ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap
          (Stacks.SheafOfModules.restrictComplexAlongOverIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E).hom i) := fun i =>
        (HomologicalComplex.homologyMapIso
          (Stacks.SheafOfModules.restrictComplexAlongOverIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E) i).isIso_hom
      refine ⟨((SheafOfModules.overMap.{0}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α₀ ≫
          (Stacks.SheafOfModules.restrictComplexAlongOverIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E).hom, fun i hi => ?_, ?_⟩
      · have := AlgebraicGeometry.RingedSpace.isIso_homologyMap_map
          (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α₀ i
          (hiso₀ i hi)
        rw [HomologicalComplex.homologyMap_comp]
        infer_instance
      · have := AlgebraicGeometry.RingedSpace.epi_homologyMap_map
          (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α₀ m hepi₀
        rw [HomologicalComplex.homologyMap_comp]
        infer_instance
    exact SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation
      (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP₀) m a hma
      (fun i hi => X.isZero_homology_restrictComplex W E i (hEzero i hi)) αW hαWiso hαWepi
      (hcyc g hg)
  refine ⟨(Sieve.bind S₀ (fun V f hf => (key V f hf).choose)).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    refine X.J.transitive hS₀ _ ?_
    intro Y h hh
    obtain ⟨Z, p, f₀, hf₀, rfl⟩ := hh
    refine X.J.superset_covering ?_
      (X.J.pullback_stable p ((key Z f₀ hf₀).choose_spec.1))
    intro Y' q hq
    exact ⟨Z, q ≫ p, f₀, hf₀, hq, by simp⟩
  · intro W h hmem
    obtain ⟨Z, p, f₀, hf₀, hp, rfl⟩ := hmem
    exact (key Z f₀ hf₀).choose_spec.2 p hp

end AlgebraicGeometry.RingedSite

end
