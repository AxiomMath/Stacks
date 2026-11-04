module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.AlgebraicGeometry.Sites.OverMapComp

/-!
# Bounded local strictly perfect approximations at independent universes

Let `X : RingedSite.{u, v, w}` be a ringed site and consider modules in `SheafOfModules.{w}`, as
for the small Zariski or étale site of a scheme, whose structure sheaf has sections in `Type u`.
A pseudo-coherent object of the derived category whose cohomology vanishes above `a` has local
strictly perfect approximations concentrated in degrees at most `a` (Stacks 08FT, bounded above).
This is the form at independent universes of the statement for `X : RingedSite.{u, v, 0}` and
modules in `SheafOfModules.{0}`.

## Main definitions

* `Stacks.SheafOfModules.restrictComplexAlongCompIsoGeneral` and
  `restrictComplexAlongOverIsoGeneral`: the two comparison isomorphisms of the degreewise
  restriction `Stacks.SheafOfModules.restrictComplexAlongGeneral`.
* `Stacks.SheafOfModules.restrictCyclesAlongIsoGeneral`: the cycles comparison for that
  restriction.

## Main results

* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_overMap_general`: restriction along an
  arrow of the site preserves "direct summand of a finite free module".
* `Stacks.SheafOfModules.epi_toCycles_restrictComplexAlong_general`: it preserves surjectivity
  of `P^i ⟶ Z^j(P)`.
* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_cycles_of_section_general`: a section of
  `P^k ⟶ Z^{k+1}(P)` exhibits `Z^k(P)` as a retract of `P^k`.
* `Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles_general`: the
  shrinking induction.
* `AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex_general`: restriction to a
  slice preserves vanishing of a cohomology sheaf.
* `AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove_general`:
  Stacks 08FT bounded above, at independent universes.

## Implementation notes

The predicates `IsDirectSummandOfFiniteFree` and `IsStrictlyPerfect` keep the ring universe `w`
and the module universe independent, and at module universe `w` reduce to the plain retract
condition by `isDirectSummandOfFiniteFree_iff_free`. The isomorphism
`SheafOfModules.overMapUnitIso` exists only at module universe equal to ring universe, which is
where this file works.

## References

* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] generalPreservesFiniteColimitsOverMap

/-- Restriction of sheaves of modules along an arrow of the site preserves finite limits. -/
local instance preservesFiniteLimitsOverMapGeneral {U V : C} (g : V ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{w} R g) :=
  LocalCokernel.overMap_preservesFiniteLimits g

/-! ### Restriction of complexes along an arrow of the site -/

/-- Restricting a complex along `f` and then along `g` is restricting it along `g ≫ f`. -/
def restrictComplexAlongCompIsoGeneral {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) :
    restrictComplexAlongGeneral R g (restrictComplexAlongGeneral R f P) ≅
      restrictComplexAlongGeneral R (g ≫ f) P :=
  (Functor.mapHomologicalComplexCompIso (overMapCompIso R f g) (ComplexShape.up ℤ)).app P

/-- Restricting a complex of `O`-modules to `V` and then along `g : W ⟶ V` is restricting it
to `W`. -/
def restrictComplexAlongOverIsoGeneral {V W : C} (g : W ⟶ V)
    (E : CochainComplex (SheafOfModules.{w} R) ℤ) :
    restrictComplexAlongGeneral R g
        (((SheafOfModules.overFunctor R V).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      ((SheafOfModules.overFunctor R W).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  (Functor.mapHomologicalComplexCompIso (SheafOfModules.overFunctorMap R g)
    (ComplexShape.up ℤ)).app E

/-! ### What restriction along an arrow of the site preserves -/

/-- Restriction along an arrow of the site preserves being a direct summand of a finite free
module: it carries a finite free module to a finite free module of the same rank, by
`SheafOfModules.mapFreeIso`, and a retraction to a retraction.

The universe-general form of `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_overMap`. -/
theorem isDirectSummandOfFiniteFree_overMap_general {U V : C} (g : V ⟶ U)
    {F : SheafOfModules.{w} (R.over U)} (hF : IsDirectSummandOfFiniteFree (R.over U) F) :
    IsDirectSummandOfFiniteFree (R.over V) ((SheafOfModules.overMap.{w} R g).obj F) := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free (R.over U) F).mp hF
  have e : SheafOfModules.free (R := R.over V) (ULift.{w} (Fin n)) ≅
      (SheafOfModules.overMap.{w} R g).obj (SheafOfModules.free (ULift.{w} (Fin n))) :=
    SheafOfModules.mapFreeIso (SheafOfModules.overMap.{w} R g) (ULift.{w} (Fin n))
      (SheafOfModules.overMapUnitIso (R := R) g)
  refine (isDirectSummandOfFiniteFree_iff_free (R.over V) _).mpr
    ⟨n, (SheafOfModules.overMap.{w} R g).map i ≫ e.inv,
      e.hom ≫ (SheafOfModules.overMap.{w} R g).map r, ?_⟩
  rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
    ← Functor.map_comp, hir, CategoryTheory.Functor.map_id]

/-- An exact functor commutes with the cycles of a complex; here the comparison for
restriction along an arrow of the site, with its source spelled as the cycles of the
restricted complex rather than as the cycles of a mapped short complex.

The universe-general form of `Stacks.SheafOfModules.restrictCyclesAlongIso`. -/
def restrictCyclesAlongIsoGeneral {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) (k : ℤ) :
    (restrictComplexAlongGeneral R g P).cycles k ≅
      (SheafOfModules.overMap.{w} R g).obj (P.cycles k) :=
  ShortComplex.mapCyclesIso (P.sc k) (SheafOfModules.overMap.{w} R g)

/-- The cycles comparison for restriction along an arrow of the site is compatible with the
inclusions of cycles. -/
@[reassoc]
lemma restrictCyclesAlongIsoGeneral_hom_iCycles {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) (k : ℤ) :
    (restrictCyclesAlongIsoGeneral R g P k).hom ≫
        (SheafOfModules.overMap.{w} R g).map (P.iCycles k) =
      (restrictComplexAlongGeneral R g P).iCycles k :=
  ShortComplex.mapCyclesIso_hom_iCycles (P.sc k) (SheafOfModules.overMap.{w} R g)

/-- The cycles comparison for restriction along an arrow of the site is compatible with
`toCycles`. -/
lemma toCycles_comp_restrictCyclesAlongIsoGeneral_hom {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) (i j : ℤ) :
    (restrictComplexAlongGeneral R g P).toCycles i j ≫
        (restrictCyclesAlongIsoGeneral R g P j).hom =
      (SheafOfModules.overMap.{w} R g).map (P.toCycles i j) := by
  have hmono : Mono ((SheafOfModules.overMap.{w} R g).map (P.iCycles j)) := inferInstance
  rw [← cancel_mono ((SheafOfModules.overMap.{w} R g).map (P.iCycles j)), Category.assoc,
    restrictCyclesAlongIsoGeneral_hom_iCycles, HomologicalComplex.toCycles_i,
    ← Functor.map_comp, HomologicalComplex.toCycles_i]
  rfl

/-- Restriction along an arrow of the site preserves surjectivity of `P^i ⟶ Z^j(P)`.

The universe-general form of `Stacks.SheafOfModules.epi_toCycles_restrictComplexAlong`. -/
theorem epi_toCycles_restrictComplexAlong_general {U V : C} (g : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ) (i j : ℤ)
    (h : Epi (P.toCycles i j)) :
    Epi ((restrictComplexAlongGeneral R g P).toCycles i j) := by
  have : (SheafOfModules.overMap.{w} R g).PreservesEpimorphisms :=
    LocalCokernel.overMap_preservesEpimorphisms g
  have := h
  rw [← epi_comp_iff_of_isIso _ (restrictCyclesAlongIsoGeneral R g P j).hom,
    toCycles_comp_restrictCyclesAlongIsoGeneral_hom]
  exact (SheafOfModules.overMap.{w} R g).map_epi _

/-! ### The shrinking induction -/

/-- A section of `P^k ⟶ Z^{k+1}(P)` exhibits `Z^k(P)` as a retract of `P^k`, hence as a direct
summand of a finite free module as soon as `P^k` is one.

The retraction of `Z^k(P)` onto `P^k` is `1 - d ∘ s` read on cycles; it kills the differential
because `s` is a section, and it restricts to the identity on cycles because the cycles are
killed by `P^k ⟶ Z^{k+1}(P)`.

The universe-general form of
`Stacks.SheafOfModules.isDirectSummandOfFiniteFree_cycles_of_section`. -/
theorem isDirectSummandOfFiniteFree_cycles_of_section_general {V : C}
    {P : CochainComplex (SheafOfModules.{w} (R.over V)) ℤ} (k : ℤ)
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
  refine IsDirectSummandOfFiniteFree.of_retract_general (R.over V)
    ⟨P.iCycles k,
      P.liftCycles (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) (k + 1) (by simp) hp, ?_⟩ hXk
  rw [← cancel_mono (P.iCycles k), Category.assoc, P.liftCycles_i, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hiz, zero_comp, sub_zero, Category.id_comp]

/-- **The shrinking induction on a site, at an arbitrary ring universe.** Let `P` be a strictly
perfect complex of `O|_V`-modules in which `P^k ⟶ Z^{k+1}(P)` is surjective in every degree
`k ≥ r`. Then there is a covering sieve of `V` over each member of which the degree-`r` cycles
of `P` are a direct summand of a finite free module.

The induction runs downwards from the top nonzero degree of `P`, where the cycles vanish, to
`r`. At each step the already-known retraction of `Z^{k+1}` onto a finite free module turns,
by the local lifting of `Stacks.SheafOfModules.LocalCokernel.exists_local_lift`, into a
*section* of `P^k ⟶ Z^{k+1}(P)` over the members of a covering sieve — which is exactly what
exhibits `Z^k(P)` as a retract of `P^k`. The finitely many refinements are composed with
`Sieve.bind`, and the two restrictions a composed arrow carries are identified with the single
restriction along it by `restrictComplexAlongCompIsoGeneral`.

The universe-general form of
`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles`. -/
theorem exists_coveringSieve_isDirectSummandOfFiniteFree_cycles_general {V : C}
    (P : CochainComplex (SheafOfModules.{w} (R.over V)) ℤ)
    (hP : IsStrictlyPerfect (R.over V) P) (r : ℤ)
    (hepi : ∀ k : ℤ, r ≤ k → Epi (P.toCycles k (k + 1))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      IsDirectSummandOfFiniteFree (R.over W)
        ((restrictComplexAlongGeneral R g P).cycles r) := by
  classical
  have hweak : ∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w} := fun _ => inferInstance
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i) := by
    obtain ⟨N, hNb⟩ := hP.bounded.bddAbove
    refine ⟨N, fun i hi => ?_⟩
    by_contra hcon
    exact absurd (hNb hcon) (not_le.2 hi)
  have main : ∀ j : ℕ, ∀ k : ℤ, r ≤ k → (∀ i : ℤ, k + (j : ℤ) ≤ i → IsZero (P.X i)) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
        IsDirectSummandOfFiniteFree (R.over W)
          ((restrictComplexAlongGeneral R g P).cycles k) := by
    intro j
    induction j with
    | zero =>
      intro k _ hk
      refine ⟨⊤, J.top_mem V, fun W g _ => ?_⟩
      refine IsDirectSummandOfFiniteFree.of_isZero_general (R.over W)
        (IsZero.of_mono ((restrictComplexAlongGeneral R g P).iCycles k) ?_)
      exact (SheafOfModules.overMap.{w} R g).map_isZero (hk k (by simp))
    | succ j ih =>
      intro k hrk hk
      obtain ⟨T₁, hT₁, hcyc₁⟩ := ih (k + 1) (by omega) (by
        intro i hi
        exact hk i (by push_cast at hi ⊢; omega))
      have key : ∀ (V₁ : C) (g₁ : V₁ ⟶ V), T₁ g₁ →
          ∃ T₂ : Sieve V₁, T₂ ∈ J V₁ ∧ ∀ ⦃W : C⦄ (g₂ : W ⟶ V₁), T₂ g₂ →
            IsDirectSummandOfFiniteFree (R.over W)
              ((restrictComplexAlongGeneral R (g₂ ≫ g₁) P).cycles k) := by
        intro V₁ g₁ hg₁
        have hQsp : IsStrictlyPerfect (R.over V₁) (restrictComplexAlongGeneral R g₁ P) :=
          isStrictlyPerfect_restrictComplexAlong_general R g₁ hP
        have hQepi : Epi ((restrictComplexAlongGeneral R g₁ P).toCycles k (k + 1)) :=
          epi_toCycles_restrictComplexAlong_general R g₁ P k (k + 1) (hepi k hrk)
        obtain ⟨n, iX, rX, hX⟩ :=
          (isDirectSummandOfFiniteFree_iff_free (R.over V₁) _).mp (hQsp.termDirectSummand k)
        obtain ⟨mm, jZ, sZ, hZ⟩ :=
          (isDirectSummandOfFiniteFree_iff_free (R.over V₁) _).mp (hcyc₁ g₁ hg₁)
        have : IsSplitEpi rX := IsSplitEpi.mk' ⟨iX, hX⟩
        have : Epi (rX ≫ (restrictComplexAlongGeneral R g₁ P).toCycles k (k + 1)) :=
          epi_comp _ _
        obtain ⟨S₂, hS₂, hlift⟩ :=
          LocalCokernel.exists_local_lift (R := R) (U := V₁)
            (N := (restrictComplexAlongGeneral R g₁ P).cycles (k + 1))
            (I := ULift.{w} (Fin mm)) (K := ULift.{w} (Fin n))
            (rX ≫ (restrictComplexAlongGeneral R g₁ P).toCycles k (k + 1)) sZ
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
            ∃ (eI : SheafOfModules.free (R := R.over W) (ULift.{w} (Fin mm)) ≅
                (SheafOfModules.overMap.{w} R g₂).obj
                  (SheafOfModules.free (ULift.{w} (Fin mm))))
              (eK : SheafOfModules.free (R := R.over W) (ULift.{w} (Fin n)) ≅
                (SheafOfModules.overMap.{w} R g₂).obj
                  (SheafOfModules.free (ULift.{w} (Fin n)))),
              ℓ ≫ eK.hom ≫ (SheafOfModules.overMap.{w} R g₂).map
                  (rX ≫ (restrictComplexAlongGeneral R g₁ P).toCycles k (k + 1)) =
                eI.hom ≫ (SheafOfModules.overMap.{w} R g₂).map sZ :=
          ⟨_, _, hℓ⟩
        obtain ⟨σ, hσ⟩ : ∃ σ : (SheafOfModules.overMap.{w} R g₂).obj
              ((restrictComplexAlongGeneral R g₁ P).cycles (k + 1)) ⟶
              (restrictComplexAlongGeneral R g₂ (restrictComplexAlongGeneral R g₁ P)).X k,
            σ ≫ (SheafOfModules.overMap.{w} R g₂).map
                ((restrictComplexAlongGeneral R g₁ P).toCycles k (k + 1)) = 𝟙 _ := by
          refine ⟨(SheafOfModules.overMap.{w} R g₂).map jZ ≫ eI.inv ≫ ℓ ≫ eK.hom ≫
            (SheafOfModules.overMap.{w} R g₂).map rX, ?_⟩
          simp only [Category.assoc]
          rw [← Functor.map_comp, hℓ', Iso.inv_hom_id_assoc, ← Functor.map_comp, hZ,
            CategoryTheory.Functor.map_id]
        refine IsDirectSummandOfFiniteFree.of_iso (R.over W)
          (HomologicalComplex.cyclesMapIso
            (restrictComplexAlongCompIsoGeneral R g₁ g₂ P) k).symm ?_
        refine isDirectSummandOfFiniteFree_cycles_of_section_general R k
          ((restrictCyclesAlongIsoGeneral R g₂
            (restrictComplexAlongGeneral R g₁ P) (k + 1)).hom ≫ σ) ?_
          ((isStrictlyPerfect_restrictComplexAlong_general R g₂ hQsp).termDirectSummand k)
        rw [← cancel_mono (restrictCyclesAlongIsoGeneral R g₂
            (restrictComplexAlongGeneral R g₁ P) (k + 1)).hom,
          Category.id_comp]
        simp only [Category.assoc]
        rw [toCycles_comp_restrictCyclesAlongIsoGeneral_hom, hσ, Category.comp_id]
      refine ⟨Sieve.bind T₁ (fun V₁ g₁ hg₁ => (key V₁ g₁ hg₁).choose),
        J.bind_covering hT₁ (fun V₁ g₁ hg₁ => (key V₁ g₁ hg₁).choose_spec.1), ?_⟩
      intro W h hmem
      obtain ⟨Z, g, f, hf, hg, rfl⟩ := hmem
      exact (key Z f hf).choose_spec.2 g hg
  exact main (N + 1 - r).toNat r le_rfl (fun i hi => hN i (by omega))

end Stacks.SheafOfModules

/-! ### Pseudo-coherence, and the bounded-above local approximation -/

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits

/-- Restriction to a slice of the site carries a complex of `O`-modules whose cohomology
vanishes in a degree to one whose cohomology vanishes in that degree: restriction is exact, and
an additive functor carries a zero object to a zero object.

The universe-general form of
`AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex`. -/
theorem isZero_homology_restrictComplex_general (U : X.C)
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (i : ℤ)
    (h : IsZero (E.homology i)) : IsZero ((X.restrictComplex E U).homology i) :=
  IsZero.of_iso
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero h)
    (ShortComplex.mapHomologyIso (E.sc i)
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))

/-- **A pseudo-coherent derived object whose cohomology vanishes above `a` has local strictly
perfect approximations concentrated in degrees at most `a`, at independent universes.**

This is the shrinking step that the Stacks proof of Tag 08DN performs inline, stated once and
for all on a ringed site. It combines
`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles_general` — which
refines the covering until the degree-`a` cycles of the given approximation are a direct
summand of a finite free module — with the truncation
`SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation_general`. The
approximation is carried to the members of the refined covering by the exactness of
restriction, and the pseudo-coherence covering is composed with the refinements by
`Sieve.bind`.

The universe-general form of
`AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove`: that
one is stated at `RingedSite.{u, v, 0}` and `SheafOfModules.{0}`, this one at
`RingedSite.{u, v, w}` and `SheafOfModules.{w}`. -/
theorem exists_local_strictlyPerfect_approximation_boundedAbove_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m a : ℤ) (hma : m ≤ a) (hK : X.IsPseudoCoherentFrom K m)
    (hzero : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K)) :
    ∃ E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
      ∀ U : X.C, ∃ S : Presieve U, (Sieve.generate S ∈ X.J U) ∧
        ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
          ∃ P : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
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
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).app E).symm.trans
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).mapIso eE))
  refine ⟨E, ⟨eE⟩, fun U => ?_⟩
  obtain ⟨S₀, hS₀, hprop⟩ := hE U
  have key : ∀ (V : X.C) (f : V ⟶ U), S₀ f →
      ∃ T : Sieve V, T ∈ X.J V ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
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
      exact (X.isZero_homology_restrictComplex_general V E i (hEzero i hi)).of_iso
        (asIso (HomologicalComplex.homologyMap α₀ i))
    have hP₀epi : ∀ k : ℤ, a ≤ k → Epi (P₀.toCycles k (k + 1)) := fun k hk =>
      Preadditive.epi_of_isZero_cokernel' _ (P₀.homologyIsCokernel k (k + 1) (by simp))
        (hP₀zero (k + 1) (by omega))
    obtain ⟨T, hT, hcyc⟩ :=
      Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_cycles_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P₀ hP₀ a hP₀epi
    refine ⟨T, hT, ?_⟩
    intro W g hg
    obtain ⟨αW, hαWiso, hαWepi⟩ :
        ∃ αW : Stacks.SheafOfModules.restrictComplexAlongGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g P₀ ⟶ X.restrictComplex E W,
          (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap αW i)) ∧
          Epi (HomologicalComplex.homologyMap αW m) := by
      have hiso : ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap
          (Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E).hom i) := fun i =>
        (HomologicalComplex.homologyMapIso
          (Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E) i).isIso_hom
      refine ⟨((SheafOfModules.overMap.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α₀ ≫
          (Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g E).hom, fun i hi => ?_, ?_⟩
      · rw [HomologicalComplex.homologyMap_comp]
        exact IsIso.comp_isIso' (AlgebraicGeometry.RingedSpace.isIso_homologyMap_map _ α₀ i
          (hiso₀ i hi)) (hiso i)
      · rw [HomologicalComplex.homologyMap_comp]
        have := AlgebraicGeometry.RingedSpace.epi_homologyMap_map
          (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α₀ m hepi₀
        have := hiso m
        exact epi_comp _ _
    exact SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation_general
      (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP₀)
      m a hma
      (fun i hi => X.isZero_homology_restrictComplex_general W E i (hEzero i hi)) αW hαWiso
      hαWepi (hcyc g hg)
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
