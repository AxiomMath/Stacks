module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Localization.LocallySmall
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.PseudoCoherent.Triangle
import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of pseudo-coherence

Let `R` be a ring. An object `K` of the derived category `D(R)` is pseudo-coherent exactly when
it is `m`-pseudo-coherent for every integer `m`, and exactly when it is represented by a
bounded-above complex of finite projective `R`-modules. If the cohomology of `K` vanishes above
a degree `b`, the finite free representative may be chosen to vanish above `b` as well.
Pseudo-coherence is moreover a two-out-of-three property along a distinguished triangle.

## Main results

* `StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective`:
  the three equivalent characterizations of pseudo-coherence, Stacks 064U.
* `StacksDraft.PseudoCoherence.pseudoCoherent_iff_all`: the all-degree characterization, valid
  for module carriers smaller than the coefficient ring.
* `StacksDraft.PseudoCoherence.exists_finiteFree_representative_le`: the prescribed upper bound
  on a finite free representative.
* `StacksDraft.PseudoCoherence.isPseudoCoherent_of_distinguished`: pseudo-coherence of two of
  the three objects of a distinguished triangle gives pseudo-coherence of the third,
  Stacks 064V.

## Implementation notes

Complexes are represented by objects of the derived category, so a quasi-isomorphism of
complexes becomes an isomorphism in `D(R)` and vanishing of cohomology becomes
`CategoryTheory.Limits.IsZero` of the corresponding homology object. The characterization is
proved first in a common ambient universe containing both the ring and the module carriers, so
that finite free complements fit; the all-degree and prescribed-bound forms then transport to a
smaller module universe along a coefficient ring equivalence when the ring is small, and use
vanishing otherwise. The derived category over the isomorphic ring is then read in the model
transported from the given model of `D(R)` along the coefficient equivalence.

This module also collects the elementary pseudo-coherence API shared by the criteria proved in
`StacksFrontier.Homology.PseudoCoherent.Module` and
`StacksDraft.Homology.PseudoCoherent.Summand`: transport along isomorphisms, weakening in the
degree, the zero-complex witness, and the single-degree witnesses.

## References

* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
* [Stacks Project, Tag 064V](https://stacks.math.columbia.edu/tag/064V)
-/

@[expose] public section

-- Needed so that the mapping-cone and single-complex normalisations below close by `rfl`.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace StacksDraft.PseudoCoherence

universe u v u' w wD wE uC vC uD vD

/-! ### Elementary API

Transport along isomorphisms, weakening in the degree, and the two basic witnesses: the zero
complex and a complex concentrated in a single degree. -/

/-- Pseudo-coherence depends only on the isomorphism class of the object in `D(R)`. -/
theorem IsPseudoCoherent.ofIso {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    {K L : DerivedCategory (ModuleCat.{v} R)} (hK : IsPseudoCoherent K) (e : K ≅ L) :
    IsPseudoCoherent L := by
  obtain ⟨E, hE, ⟨f⟩⟩ := hK
  exact ⟨E, hE, ⟨f ≪≫ e⟩⟩

/-- `m`-pseudo-coherence becomes weaker as `m` increases: the same approximation works, and
above `m` an isomorphism on cohomology is in particular an epimorphism. -/
theorem IsPseudoCoherentFrom.mono {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    {K : DerivedCategory (ModuleCat.{v} R)} {m n : ℤ}
    (hK : IsPseudoCoherentFrom K m) (hmn : m ≤ n) : IsPseudoCoherentFrom K n := by
  obtain ⟨E, hE, α, hi, he⟩ := hK
  refine ⟨E, hE, α, fun i h => hi i (lt_of_le_of_lt hmn h), ?_⟩
  rcases hmn.eq_or_lt with rfl | h
  · exact he
  · have := hi n h
    infer_instance

/-- The terms of the zero complex are finite free. -/
private theorem finite_free_zero_X {R : Type u} [Ring R] (i : ℤ) :
    Module.Finite R ((0 : CochainComplex (ModuleCat.{v} R) ℤ).X i) ∧
      Module.Free R ((0 : CochainComplex (ModuleCat.{v} R) ℤ).X i) := by
  have : Subsingleton ((0 : CochainComplex (ModuleCat.{v} R) ℤ).X i) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero
        (isZero_zero _))
  exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩

/-- Vanishing of cohomology in all degrees at least `m` gives an approximation by the zero
complex, without any size assumption on the ring. -/
theorem isPseudoCoherentFrom_of_homology_isZero {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : ∀ i : ℤ, m ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    IsPseudoCoherentFrom K m := by
  refine ⟨0, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, finite_free_zero_X⟩, 0, ?_, ?_⟩
  · intro i hi
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
      (DerivedCategory.Q.map_isZero (isZero_zero _))).isIso (hK i hi.le) _
  · exact (hK m le_rfl).epi _

/-- `m`-pseudo-coherence of a module depends only on its isomorphism class. -/
theorem IsModulePseudoCoherentFrom.ofIso {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] {M N : ModuleCat.{v} R}
    (e : M ≅ N) (m : ℤ) (hM : IsModulePseudoCoherentFrom (R := R) M m) :
    IsModulePseudoCoherentFrom (R := R) N m :=
  IsPseudoCoherentFrom.ofIso hM ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).mapIso e)

/-- A zero module is `m`-pseudo-coherent for every `m`. -/
theorem isModulePseudoCoherentFrom_of_isZero {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (M : ModuleCat.{v} R)
    (hM : IsZero M) (m : ℤ) : IsModulePseudoCoherentFrom (R := R) M m :=
  isPseudoCoherentFrom_of_homology_isZero
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) m fun i _ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map_isZero hM)

/-- A finite free module placed in degree `m` is a bounded complex of finite free modules. -/
theorem isBoundedFiniteFree_single {R : Type u} [Ring R]
    (P : ModuleCat.{v} R) [Module.Finite R P] [Module.Free R P] (m : ℤ) :
    IsBoundedFiniteFree ((CochainComplex.singleFunctor (ModuleCat.{v} R) m).obj P) := by
  refine ⟨⟨m, inferInstance⟩, ⟨m, inferInstance⟩, fun i ↦ ?_⟩
  by_cases hi : i = m
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m P).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · have : Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{v} R) m).obj P).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m P i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩

/-- A finite module over a ring which is small in the module universe receives an epimorphism
from a finite free module. -/
theorem exists_finite_free_epi {R : Type u} [Ring R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] :
    ∃ P : ModuleCat.{v} R, Module.Finite R P ∧ Module.Free R P ∧ ∃ f : P ⟶ M, Epi f := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let P := ModuleCat.of R (Shrink.{v} (Fin n → R))
  let e := Shrink.linearEquiv.{v} R (Fin n → R)
  refine ⟨P, inferInstance, inferInstance, ModuleCat.ofHom (f.comp e.toLinearMap), ?_⟩
  exact (ModuleCat.epi_iff_surjective _).2 (hf.comp e.surjective)

/-- A projective object mapping onto `Hᵐ(K)` gives a morphism from the complex concentrated in
degree `m` whose effect on `Hᵐ` is an epimorphism. -/
theorem exists_hom_from_single_of_projective
    {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)
    (P : C) [Projective P] (f : P ⟶ K.homology m) [Epi f] :
    ∃ φ : (CochainComplex.singleFunctor C m).obj P ⟶ K,
      Epi (HomologicalComplex.homologyMap φ m) := by
  let g := Projective.factorThru f (K.homologyπ m)
  let φ := HomologicalComplex.mkHomFromSingle (g ≫ K.iCycles m)
    (fun j _ ↦ by simp)
  refine ⟨φ, ?_⟩
  have hcycles : HomologicalComplex.cyclesMap φ m =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) m P).hom ≫ g := by
    apply (cancel_mono (K.iCycles m)).1
    simp [φ, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
  have h : ((CochainComplex.singleFunctor C m).obj P).homologyπ m ≫
      HomologicalComplex.homologyMap φ m =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) m P).hom ≫ f := by
    rw [HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc]
    simp [g]
  have : Epi (((CochainComplex.singleFunctor C m).obj P).homologyπ m ≫
      HomologicalComplex.homologyMap φ m) := by rw [h]; infer_instance
  exact epi_of_epi (((CochainComplex.singleFunctor C m).obj P).homologyπ m) _

/-- If a module is `(m - d)`-pseudo-coherent, the object of `D(R)` concentrated in degree `d`
with that value is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_single {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (M : ModuleCat.{v} R) (d m : ℤ)
    (hM : IsModulePseudoCoherentFrom (R := R) M (m - d)) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (ModuleCat.{v} R) d).obj M) m := by
  have h := IsPseudoCoherentFrom.shift hM (-d)
  exact IsPseudoCoherentFrom.ofIso (by simpa using h)
    (((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-d) d 0 (by omega)).app M)

/-! ### Transport along exact functors and along coefficient equivalences -/

/-- Exact functors between abelian categories commute with derived homology. -/
noncomputable def mapDerivedCategoryHomologyIso
    {C : Type uC} [Category.{vC} C] [Abelian C] {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory.{wD} C] [HasDerivedCategory.{wE} D]
    (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F := by
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
    NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map φ) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor _ n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor _ n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors _ n) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ n).symm F)

/-- An exact functor that preserves finite free modules preserves both forms of
pseudo-coherence. The module universes of the source and target are independent. -/
theorem exactFunctor_preserves_pseudoCoherent
    {R : Type u} {A : Type u'} [Ring R] [Ring A]
    [HasDerivedCategory (ModuleCat.{v} R)] [HasDerivedCategory (ModuleCat.{w} A)]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : ModuleCat.{v} R, Module.Finite R M → Module.Free R M →
      Module.Finite A (F.obj M) ∧ Module.Free A (F.obj M))
    (K : DerivedCategory (ModuleCat.{v} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
      IsPseudoCoherentFrom (F.mapDerivedCategory.obj K) m) ∧
    (IsPseudoCoherent K → IsPseudoCoherent (F.mapDerivedCategory.obj K)) := by
  have hfrom : ∀ m : ℤ, IsPseudoCoherentFrom K m →
      IsPseudoCoherentFrom (F.mapDerivedCategory.obj K) m := by
    intro m ⟨E, hE, α, hiso, hepi⟩
    let E' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
    have hE' : IsBoundedFiniteFree E' := by
      obtain ⟨a, ha⟩ := hE.lowerBound
      obtain ⟨b, hb⟩ := hE.upperBound
      have := ha
      have := hb
      exact ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩,
        fun i ↦ hF (E.X i) (hE.finiteFree i).1 (hE.finiteFree i).2⟩
    let α' := F.mapDerivedCategoryFactors.inv.app E ≫ F.mapDerivedCategory.map α
    have hmap (i : ℤ) :
        (DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).map
          (F.mapDerivedCategory.map α) =
        (mapDerivedCategoryHomologyIso F i).hom.app _ ≫
          F.map ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) ≫
          (mapDerivedCategoryHomologyIso F i).inv.app _ := by
      simpa using (NatIso.naturality_2 (mapDerivedCategoryHomologyIso F i) α).symm
    refine ⟨E', hE', α', ?_, ?_⟩
    · intro i hi
      have := hiso i hi
      dsimp only [α']
      rw [Functor.map_comp, hmap]
      infer_instance
    · have := hepi
      dsimp only [α']
      rw [Functor.map_comp, hmap]
      infer_instance
  refine ⟨hfrom, ?_⟩
  rintro ⟨E, hE, ⟨e⟩⟩
  obtain ⟨b, hb⟩ := hE.upperBound
  have := hb
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E,
    ⟨⟨b, inferInstance⟩, fun i => hF (E.X i) (hE.finiteFree i).1 (hE.finiteFree i).2⟩,
    ⟨(F.mapDerivedCategoryFactors.app E).symm ≪≫ F.mapDerivedCategory.mapIso e⟩⟩

/-- Changing coefficients along a ring isomorphism preserves finite free modules, without
changing the carrier universe. -/
theorem restrictScalars_finiteFree {R : Type u} {S : Type u'} [Ring R] [Ring S]
    (e : S ≃+* R) (M : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Free R M] :
    Module.Finite S ((ModuleCat.restrictScalars.{v} e.toRingHom).obj M) ∧
      Module.Free S ((ModuleCat.restrictScalars.{v} e.toRingHom).obj M) := by
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  let l : LinearEquiv (σ' := e.symm.toRingHom) e.toRingHom
      ((ModuleCat.restrictScalars.{v} e.toRingHom).obj M) M :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact ⟨(l.toLinearMap.finite_iff_of_bijective l.bijective).mpr inferInstance,
    Module.Free.of_equiv l.symm⟩

/-- Restriction of coefficients along a ring isomorphism, at a fixed carrier universe. -/
noncomputable abbrev coefficientRestriction
    {R : Type u} {S : Type u'} [Ring R] [Ring S] (e : S ≃+* R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor

/-- Restriction of coefficients along a ring isomorphism is an equivalence. -/
private lemma coefficientRestriction_equivalence
    {R : Type u} {S : Type u'} [Ring R] [Ring S] (e : S ≃+* R) :
    (coefficientRestriction.{u, v, u'} e).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

attribute [local instance] coefficientRestriction_equivalence

/-- Along a ring isomorphism `e : S ≃+* R`, a model of `D(R)` localizes the complexes of
`S`-modules at their quasi-isomorphisms, through the inverse of the coefficient equivalence. -/
private lemma isLocalization_coefficientInverse_Q
    {R : Type u} {S : Type u'} [Ring R] [Ring S] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (e : S ≃+* R) :
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
        ModuleCat.{v} R ≌ ModuleCat.{v} S).inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).IsLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{v} S) (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) _ _
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
      ModuleCat.{v} R ≌ ModuleCat.{v} S).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun _ _ f (_ : QuasiIso f) => MorphismProperty.le_isoClosure _ _
      ((HomologicalComplex.mem_quasiIso_iff _).2 (show QuasiIso
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
          ModuleCat.{v} R ≌ ModuleCat.{v} S).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) from inferInstance)))
    (fun _ _ g (_ : QuasiIso g) => Localization.inverts DerivedCategory.Q _ _
      ((HomologicalComplex.mem_quasiIso_iff _).2 (show QuasiIso
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
          ModuleCat.{v} R ≌ ModuleCat.{v} S).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) from inferInstance)))
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
        ModuleCat.{v} R ≌ ModuleCat.{v} S).mapHomologicalComplex
          (ComplexShape.up ℤ)).unitIso.symm _ ≪≫ Functor.leftUnitor _)

/-- The model of `D(S)` transported from a model of `D(R)` along a ring isomorphism
`e : S ≃+* R`: complexes of `S`-modules are localized in the given model of `D(R)` through the
coefficient equivalence. -/
@[instance_reducible]
private noncomputable def hasDerivedCategoryOfRingEquiv
    {R : Type u} {S : Type u'} [Ring R] [Ring S] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (e : S ≃+* R) : HasDerivedCategory.{w} (ModuleCat.{v} S) :=
  have := isLocalization_coefficientInverse_Q e
  MorphismProperty.hasLocalizationOfLocallySmall'
    (HomologicalComplex.quasiIso (ModuleCat.{v} S) (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
        ModuleCat.{v} R ≌ ModuleCat.{v} S).inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)

/-- The composite of the derived functors of a coefficient equivalence returns the original
object. All module carriers stay in the same universe. -/
private noncomputable def restrictScalarsDerivedUnitIso
    {R : Type u} {S : Type u'} [Ring R] [Ring S]
    [HasDerivedCategory (ModuleCat.{v} R)] [HasDerivedCategory (ModuleCat.{v} S)] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{v} R)) :
    (coefficientRestriction.{u', v, u} e.symm).mapDerivedCategory.obj
      ((coefficientRestriction.{u, v, u'} e).mapDerivedCategory.obj K) ≅ K := by
  let F := coefficientRestriction.{u, v, u'} e
  let G := coefficientRestriction.{u', v, u} e.symm
  let P := DerivedCategory.Q.objPreimage K
  let k := DerivedCategory.Q.objObjPreimageIso K
  let E := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e :
    ModuleCat.{v} R ≌ ModuleCat.{v} S).mapHomologicalComplex
    (ComplexShape.up ℤ)
  exact G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso k.symm) ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (E.unitIso.app P).symm ≪≫ k

/-- Coefficient ring equivalences preserve and reflect both forms of pseudo-coherence at a
fixed carrier universe. This is a genuine equivalence, including when the ring is larger. -/
theorem pseudoCoherent_iff_of_ringEquiv
    {R : Type u} {S : Type u'} [Ring R] [Ring S]
    [HasDerivedCategory (ModuleCat.{v} R)] [HasDerivedCategory (ModuleCat.{v} S)] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{v} R)) :
    (∀ m, IsPseudoCoherentFrom K m ↔ IsPseudoCoherentFrom
      ((coefficientRestriction.{u, v, u'} e).mapDerivedCategory.obj K) m) ∧
    (IsPseudoCoherent K ↔ IsPseudoCoherent
      ((coefficientRestriction.{u, v, u'} e).mapDerivedCategory.obj K)) := by
  let F := coefficientRestriction.{u, v, u'} e
  have hF := exactFunctor_preserves_pseudoCoherent F
    (fun M _ _ => restrictScalars_finiteFree e M) K
  have hG := exactFunctor_preserves_pseudoCoherent (coefficientRestriction.{u', v, u} e.symm)
    (fun M _ _ => restrictScalars_finiteFree e.symm M) (F.mapDerivedCategory.obj K)
  exact ⟨fun m => ⟨hF.1 m, fun h =>
      IsPseudoCoherentFrom.ofIso (hG.1 m h) (restrictScalarsDerivedUnitIso e K)⟩,
    ⟨hF.2, fun h => IsPseudoCoherent.ofIso (hG.2 h) (restrictScalarsDerivedUnitIso e K)⟩⟩

/-! ### The degenerate case of a ring too large for the module universe -/

/-- A nonzero free module makes its coefficient ring small in the module universe. -/
theorem small_of_nontrivial_free {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) [Module.Free R M] [Nontrivial M] : Small.{v} R :=
  small_of_injective (smul_left_injective' (M := R) (α := M))

/-- When the ring does not fit in the carrier universe, every complex with free terms is zero. -/
theorem complex_isZero_of_not_small {R : Type u} [Ring R]
    (hR : ¬ Small.{v} R) (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i, Module.Free R (E.X i)) : IsZero E := by
  have hz (i : ℤ) : IsZero (E.X i) := by
    let := hE i
    have : Subsingleton (E.X i) := by
      by_contra hn
      have : Nontrivial (E.X i) := not_subsingleton_iff_nontrivial.mp hn
      exact hR (small_of_nontrivial_free (E.X i))
    exact ModuleCat.isZero_iff_subsingleton.mpr this
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun i => (hz i).eq_of_src _ _

/-- When the ring does not fit in the carrier universe, a bounded-above finite free complex is
zero in `D(R)`. -/
private theorem isZero_Q_obj_of_not_small {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (hR : ¬ Small.{v} R)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hE : IsBoundedAboveFiniteFree E) :
    IsZero (DerivedCategory.Q.obj E) :=
  DerivedCategory.Q.map_isZero (complex_isZero_of_not_small hR E fun i => (hE.finiteFree i).2)

/-- A zero object is pseudo-coherent and `m`-pseudo-coherent in every degree. -/
theorem pseudoCoherent_of_isZero {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsZero K) :
    IsPseudoCoherent K ∧ ∀ m, IsPseudoCoherentFrom K m := by
  have hz := DerivedCategory.Q.map_isZero
    (isZero_zero (CochainComplex (ModuleCat.{v} R) ℤ))
  refine ⟨⟨0, ⟨⟨0, inferInstance⟩, finite_free_zero_X⟩, ⟨hz.iso hK⟩⟩, fun m => ?_⟩
  refine ⟨0, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, finite_free_zero_X⟩, (hz.iso hK).hom, ?_, ?_⟩
  · intro i _
    infer_instance
  · infer_instance

/-- Pseudo-coherence gives a bounded-above finite projective representative without any
restriction on carrier universes: use its finite free representative. -/
theorem finiteProjectiveRepresentative_of_pseudoCoherent
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPseudoCoherent K) :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, hP, e⟩ := hK
  exact ⟨P, hP.upperBound, fun i =>
    ⟨(hP.finiteFree i).1, let := (hP.finiteFree i).2; inferInstance⟩, e⟩

/-! ### Building finite free resolutions

The heart of Stacks 064U: a complex all of whose finite free approximations have finite cone
cohomology admits a genuine finite free representative, obtained as the colimit of a sequence
of approximations each extending the previous one one degree further down. -/

/-- Pseudo-coherence implies `m`-pseudo-coherence for every `m`: truncate a bounded-above
finite free representative brutally at `m`. -/
private lemma isPseudoCoherentFrom_of_isPseudoCoherent
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPseudoCoherent K) (m : ℤ) : IsPseudoCoherentFrom K m := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have := hb
  refine ⟨_root_.PseudoCoherence.truncGEaux.Ptrunc m E,
    ⟨⟨m, inferInstance⟩, ⟨b, inferInstance⟩,
      _root_.PseudoCoherence.truncGEaux.Ptrunc_finiteFree m E hE.finiteFree⟩,
    DerivedCategory.Q.map (_root_.PseudoCoherence.truncGEaux.ιmap m E) ≫ e.hom, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have := _root_.PseudoCoherence.truncGEaux.isIso_cohomology_Qmap_ι m E i hi
    infer_instance
  · rw [Functor.map_comp]
    have := _root_.PseudoCoherence.truncGEaux.epi_cohomology_Qmap_ι m E
    infer_instance

/-- A bounded complex of finite free modules is K-projective. -/
lemma isKProjective_of_boundedFiniteFree
    {R : Type u} [Ring R] {E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hE : IsBoundedFiniteFree E) : E.IsKProjective := by
  have (i : ℤ) : Projective (E.X i) := by
    have := (hE.finiteFree i).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (E.X i))
  obtain ⟨b, hb⟩ := hE.upperBound
  exact CochainComplex.isKProjective_of_projective E b

/-- Out of a K-projective complex, every morphism in `D(R)` is induced by a chain map. -/
lemma exists_chainMap_of_isKProjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P E : CochainComplex C ℤ) [P.IsKProjective]
    (ψ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E) :
    ∃ γ : P ⟶ E, DerivedCategory.Q.map γ = ψ := by
  have hbij := (Iso.homCongr
      ((DerivedCategory.quotientCompQhIso C).app P)
      ((DerivedCategory.quotientCompQhIso C).app E)).bijective.comp
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj E))
  obtain ⟨f, hf⟩ := hbij.surjective ψ
  obtain ⟨γ, hγ⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
  refine ⟨γ, ?_⟩
  rw [← hf, ← hγ]
  simp only [Function.comp_apply, Iso.homCongr_apply, Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Out of a K-projective complex, two chain maps with the same image in `D(R)` are
homotopic. -/
lemma homotopic_of_Q_map_eq
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P E : CochainComplex C ℤ} [P.IsKProjective] (f g : P ⟶ E)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Nonempty (Homotopy f g) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKProjective.Qh_map_bijective P _).injective
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app E)]
  simpa only [DerivedCategory.quotientCompQhIso_hom_naturality] using
    congrArg (((DerivedCategory.quotientCompQhIso C).hom.app P) ≫ ·) h

/-- An object concentrated in degrees `≤ n` with finite top cohomology is approximated in
degree `n` by a finite free module placed in degree `n`. -/
private lemma exists_finiteFree_top_approximation
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) [K.IsLE n]
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)] :
    ∃ (E : CochainComplex (ModuleCat.{v} R) ℤ), IsBoundedFiniteFree E ∧
      E.IsStrictlyGE n ∧ E.IsStrictlyLE n ∧
      ∃ α : DerivedCategory.Q.obj E ⟶ K,
        (∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor _ n).map α) := by
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let eh : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K ≅ L.homology n :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app L
  obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)
  have : Epi (p ≫ eh.hom) := by infer_instance
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_of_projective L n P (p ≫ eh.hom)
  let E := (CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj P
  refine ⟨E, isBoundedFiniteFree_single P n, inferInstance, inferInstance,
    DerivedCategory.Q.map φ ≫ e.hom, ?_, ?_⟩
  · intro i hi
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) n i hi).isIso
      (DerivedCategory.isZero_of_isLE K n i hi) _
  · rw [Functor.map_comp]
    have heq : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
        (DerivedCategory.Q.map φ) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).hom.app E ≫
        HomologicalComplex.homologyMap φ n ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).inv.app L := by
      simpa using (NatIso.naturality_2
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n) φ).symm
    rw [heq]
    infer_instance

/-- A morphism out of a degreewise split extension of K-projective complexes can be corrected
by a null-homotopic map so that it strictly extends a given morphism on the subcomplex. -/
lemma exists_chainMap_lift_under
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {E F K : CochainComplex C ℤ} [E.IsKProjective] [F.IsKProjective]
    (ι : E ⟶ F) (r : ∀ i, F.X i ⟶ E.X i) (hr : ∀ i, ι.f i ≫ r i = 𝟙 _)
    (α : E ⟶ K) (ψ : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj K)
    (hψ : DerivedCategory.Q.map ι ≫ ψ = DerivedCategory.Q.map α) :
    ∃ β : F ⟶ K, ι ≫ β = α ∧ DerivedCategory.Q.map β = ψ := by
  obtain ⟨β, hβ⟩ := exists_chainMap_of_isKProjective F K ψ
  obtain ⟨h⟩ := homotopic_of_Q_map_eq (ι ≫ β) α (by simpa [hβ] using hψ)
  let c := Homotopy.nullHomotopicMap (fun i j => r i ≫ h.hom i j)
  have hc : ι ≫ c = ι ≫ β - α := by
    rw [Homotopy.sub_eq_nullHomotopicMap h]
    simp only [c, Homotopy.comp_nullHomotopicMap, ← Category.assoc, hr, Category.id_comp]
  refine ⟨β - c, ?_, ?_⟩
  · rw [Preadditive.comp_sub, hc]
    abel
  · have hcz : DerivedCategory.Q.map c = 0 := by
      simpa using DerivedCategory.Q_map_eq_of_homotopy C
        (Homotopy.nullHomotopy (fun i j => r i ≫ h.hom i j)
          (fun i j hij => by rw [h.zero i j hij, HasZeroMorphisms.comp_zero]))
    simp [hβ, hcz]

/-- The mapping cone of `γ : P ⟶ E` is strictly `≥ n` when `P` is strictly `≥ n₁` with
`n < n₁` and `E` is strictly `≥ n₂` with `n ≤ n₂`. -/
private lemma isStrictlyGE_mappingCone {C : Type*} [Category C] [Abelian C]
    {P E : CochainComplex C ℤ} (γ : P ⟶ E) (n₁ n₂ n : ℤ) [P.IsStrictlyGE n₁] [E.IsStrictlyGE n₂]
    (hn₁ : n < n₁ := by lia) (hn₂ : n ≤ n₂ := by lia) :
    (CochainComplex.mappingCone γ).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨P.isZero_of_isStrictlyGE n₁ _ (by lia), E.isZero_of_isStrictlyGE n₂ _ (by lia)⟩

/-- The mapping cone of `γ : P ⟶ E` is strictly `≤ n` when `P` is strictly `≤ n₁` with
`n₁ ≤ n + 1` and `E` is strictly `≤ n₂` with `n₂ ≤ n`. -/
private lemma isStrictlyLE_mappingCone {C : Type*} [Category C] [Abelian C]
    {P E : CochainComplex C ℤ} (γ : P ⟶ E) (n₁ n₂ n : ℤ) [P.IsStrictlyLE n₁] [E.IsStrictlyLE n₂]
    (hn₁ : n₁ ≤ n + 1 := by lia) (hn₂ : n₂ ≤ n := by lia) :
    (CochainComplex.mappingCone γ).IsStrictlyLE n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨P.isZero_of_isStrictlyLE n₁ _ (by lia), E.isZero_of_isStrictlyLE n₂ _ (by lia)⟩

/-- The degree `i` term of a mapping cone is linearly equivalent to `P.X (i + 1) × E.X i`. -/
private lemma nonempty_mappingCone_X_linearEquiv {R : Type u} [Ring R]
    {P E : CochainComplex (ModuleCat.{v} R) ℤ} (γ : P ⟶ E) (i : ℤ) :
    Nonempty ((CochainComplex.mappingCone γ).X i ≃ₗ[R] P.X (i + 1) × E.X i) :=
  ⟨(HomologicalComplex.homotopyCofiber.XIsoBiprod γ i (i + 1) rfl ≪≫
    ModuleCat.biprodIsoProd (P.X (i + 1)) (E.X i)).toLinearEquiv⟩

/-- The mapping cone of a chain map between bounded complexes of finite free modules is again
a bounded complex of finite free modules. -/
lemma boundedFiniteFree_mappingCone
    {R : Type u} [Ring R] {P E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : IsBoundedFiniteFree P) (hE : IsBoundedFiniteFree E) (γ : P ⟶ E) :
    IsBoundedFiniteFree (CochainComplex.mappingCone γ) := by
  obtain ⟨a, ha⟩ := hP.lowerBound
  obtain ⟨b, hb⟩ := hE.lowerBound
  obtain ⟨a', ha'⟩ := hP.upperBound
  obtain ⟨b', hb'⟩ := hE.upperBound
  refine ⟨⟨min (a - 1) b, isStrictlyGE_mappingCone γ a b _⟩,
    ⟨max (a' - 1) b', isStrictlyLE_mappingCone γ a' b' _⟩, fun i => ?_⟩
  obtain ⟨hPf, hPfr⟩ := hP.finiteFree (i + 1)
  obtain ⟨hEf, hEfr⟩ := hE.finiteFree i
  obtain ⟨e⟩ := nonempty_mappingCone_X_linearEquiv γ i
  have := Module.Free.prod R (P.X (i + 1)) (E.X i)
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩

/-- The inductive step: a finite free approximation accurate in degrees `≥ n` extends, through
a degreewise split inclusion, to one accurate in degrees `≥ n - 1`. -/
private lemma exists_next_approximation
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    {E K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hE : IsBoundedFiniteFree E) (α : E ⟶ K) (n b : ℤ) (hnb : n ≤ b + 1)
    [E.IsStrictlyGE n] [E.IsStrictlyLE b]
    (hiso : ∀ i, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (DerivedCategory.Q.map α)))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Q.map α)))
    (hfin : ((DerivedCategory.Q.obj (CochainComplex.mappingCone α))⟦(-1 : ℤ)⟧).IsLE n →
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((DerivedCategory.Q.obj (CochainComplex.mappingCone α))⟦(-1 : ℤ)⟧))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ) (ι : E ⟶ F) (β : F ⟶ K),
      IsBoundedFiniteFree F ∧ F.IsStrictlyGE (n - 1) ∧ F.IsStrictlyLE b ∧
      ι ≫ β = α ∧ (∀ i, n ≤ i → IsIso (ι.f i)) ∧
      (∀ i, n - 1 < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (DerivedCategory.Q.map β))) ∧
      Epi ((DerivedCategory.homologyFunctor _ (n - 1)).map (DerivedCategory.Q.map β)) := by
  let T₀ := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT₀ : T₀ ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished α
  let T := T₀.invRotate
  have hT : T ∈ distTriang _ := inv_rot_of_distTriang _ hT₀
  have hC : T₀.obj₃.IsLE (n - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation T₀ hT₀ n hiso hepi
  have hCn : T.obj₁.IsLE n :=
    DerivedCategory.TStructure.t.isLE_shift T₀.obj₃ (n - 1) (-1) n (by omega)
  have hfinite : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj T.obj₁) := hfin hCn
  obtain ⟨P, hP, hPge, hPle, g, hgiso, hgepi⟩ := exists_finiteFree_top_approximation T.obj₁ n
  have := isKProjective_of_boundedFiniteFree hP
  have := isKProjective_of_boundedFiniteFree hE
  obtain ⟨δ, hδ⟩ := exists_chainMap_of_isKProjective P E (g ≫ T.mor₁)
  let F := CochainComplex.mappingCone δ
  have hF : IsBoundedFiniteFree F := boundedFiniteFree_mappingCone hP hE δ
  have := isKProjective_of_boundedFiniteFree hF
  let S := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle δ)
  have hS : S ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished δ
  have hsq : S.mor₁ ≫ 𝟙 _ = g ≫ T.mor₁ := by
    change DerivedCategory.Q.map δ ≫ 𝟙 _ = _
    simpa using hδ
  obtain ⟨ψ, hψ₁, hψ₂⟩ := complete_distinguished_triangle_morphism S T hS hT g (𝟙 _) hsq
  let φ : S ⟶ T := Triangle.homMk _ _ g (𝟙 _) ψ hsq hψ₁ hψ₂
  let ι := CochainComplex.mappingCone.inr δ
  obtain ⟨β, hβ, hQβ⟩ := exists_chainMap_lift_under ι
    (fun i => (CochainComplex.mappingCone.snd δ).v i i (add_zero i))
    (fun i => CochainComplex.mappingCone.inr_f_snd_v δ i) α ψ (by
      change DerivedCategory.Q.map ι ≫ ψ = 𝟙 _ ≫ DerivedCategory.Q.map α at hψ₁
      simpa only [Category.id_comp] using hψ₁)
  refine ⟨F, ι, β, hF, ?_, ?_, hβ, ?_, ?_, ?_⟩
  · exact isStrictlyGE_mappingCone δ n n (n - 1)
  · exact isStrictlyLE_mappingCone δ n b b
  · intro i hi
    let r := (CochainComplex.mappingCone.snd δ).v i i (add_zero i)
    refine ⟨r, CochainComplex.mappingCone.inr_f_snd_v δ i, ?_⟩
    have hz := P.isZero_of_isStrictlyLE n (i + 1) (by omega)
    have hh := CochainComplex.mappingCone.id_X δ i (i + 1) rfl
    have hzero : (CochainComplex.mappingCone.fst δ).1.v i (i + 1) rfl = 0 :=
      hz.eq_of_tgt _ _
    simpa only [hzero, HasZeroMorphisms.zero_comp, zero_add] using hh
  · intro i hi
    rw [hQβ]
    apply _root_.PseudoCoherence.isIso_homology_of_triangleMorphism hS hT φ i
    · change Epi ((DerivedCategory.homologyFunctor _ i).map g)
      rcases (show n ≤ i by omega).eq_or_lt with rfl | h
      · exact hgepi
      · have := hgiso i h
        infer_instance
    · change IsIso ((DerivedCategory.homologyFunctor _ i).map (𝟙 _))
      infer_instance
    · exact hgiso (i + 1) (by omega)
    · change Mono ((DerivedCategory.homologyFunctor _ (i + 1)).map (𝟙 _))
      infer_instance
  · rw [hQβ]
    apply _root_.PseudoCoherence.epi_homology_of_triangleMorphism hS hT φ (n - 1)
    · change Epi ((DerivedCategory.homologyFunctor _ (n - 1)).map (𝟙 _))
      infer_instance
    · change Epi ((DerivedCategory.homologyFunctor _ (n - 1 + 1)).map g)
      rw [sub_add_cancel]
      exact hgepi
    · change Mono ((DerivedCategory.homologyFunctor _ (n - 1 + 1)).map (𝟙 _))
      infer_instance

/-- A finite free approximation of `K` which is bounded in `[n, b]` and accurate in degrees
`≥ n`. -/
private structure FiniteFreeApproximation {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b n : ℤ) where
  /-- The approximating complex. -/
  complex : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The approximating chain map. -/
  map : complex ⟶ K
  /-- The approximating complex is bounded with finite free terms. -/
  finiteFree : IsBoundedFiniteFree complex
  /-- The approximating complex vanishes below `n`. -/
  ge : complex.IsStrictlyGE n
  /-- The approximating complex vanishes above `b`. -/
  le : complex.IsStrictlyLE b
  /-- The approximation is an isomorphism on cohomology above `n`. -/
  iso : ∀ i, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
    (DerivedCategory.Q.map map))
  /-- The approximation is an epimorphism on cohomology in degree `n`. -/
  epi : Epi ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Q.map map))

/-- A sequence of maps which is an isomorphism at each successive step from `q` on is an
isomorphism on each comparison map between indices at least `q`. -/
lemma isIso_map_of_nat
    {C : Type*} [Category C] (D : ℕ ⥤ C) {q r : ℕ} (h : q ≤ r)
    (hs : ∀ k, q ≤ k → IsIso (D.map (homOfLE (Nat.le_succ k)))) :
    IsIso (D.map (homOfLE h)) := by
  induction r, h using Nat.le_induction with
  | base => simp only [homOfLE_refl]; infer_instance
  | succ r h ih =>
    rw [← homOfLE_comp h (Nat.le_succ r), Functor.map_comp]
    have := hs r h
    infer_instance

/-- A chain map which is an isomorphism in the three degrees around `i` is a
quasi-isomorphism at `i`. -/
lemma quasiIsoAt_of_isIso_components
    {C : Type*} [Category C] [Abelian C]
    {E F : CochainComplex C ℤ} (f : E ⟶ F) (i : ℤ)
    [IsIso (f.f (i - 1))] [IsIso (f.f i)] [IsIso (f.f (i + 1))] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff' f (i - 1) i (i + 1) (by simp) (by simp)]
  let φ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
    (i - 1) i (i + 1)).map f
  have : IsIso φ.τ₁ := by change IsIso (f.f (i - 1)); infer_instance
  have : IsIso φ.τ₂ := by change IsIso (f.f i); infer_instance
  have : IsIso φ.τ₃ := by change IsIso (f.f (i + 1)); infer_instance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- The finiteness input to the resolution construction: every shifted cone of a finite free
approximation of `K` has finite cohomology in the relevant degree. -/
private abbrev HasFiniteConeHomology {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  ∀ (E : CochainComplex (ModuleCat.{v} R) ℤ), IsBoundedFiniteFree E →
    ∀ (α : E ⟶ K) (n : ℤ),
      ((DerivedCategory.Q.obj (CochainComplex.mappingCone α))⟦(-1 : ℤ)⟧).IsLE n →
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
        ((DerivedCategory.Q.obj (CochainComplex.mappingCone α))⟦(-1 : ℤ)⟧))

/-- The resolution construction: a complex with finite cone cohomology and cohomology
vanishing above `b` is quasi-isomorphic to a complex of finite free modules vanishing
above `b`, namely the colimit of the sequence of approximations. -/
private lemma exists_finiteFree_resolution
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    (hK : HasFiniteConeHomology K)
    (hvan : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj K))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ) (α : F ⟶ K),
      (∀ i, Module.Finite R (F.X i) ∧ Module.Free R (F.X i)) ∧
      F.IsStrictlyLE b ∧ IsIso (DerivedCategory.Q.map α) := by
  classical
  have hzero : IsBoundedFiniteFree (0 : CochainComplex (ModuleCat.{v} R) ℤ) :=
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, finite_free_zero_X⟩
  have hzeroiso (i : ℤ) (hi : b < i) : IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (0 : (0 : CochainComplex (ModuleCat.{v} R) ℤ) ⟶ K))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
      (DerivedCategory.Q.map_isZero (isZero_zero _))).isIso (hvan i hi) _
  let a₀ : FiniteFreeApproximation K b (b + 1 - (0 : ℕ)) := {
    complex := 0
    map := 0
    finiteFree := hzero
    ge := by infer_instance
    le := by infer_instance
    iso := fun i hi => hzeroiso i (by omega)
    epi := by have := hzeroiso (b + 1 - (0 : ℕ)) (by omega); infer_instance }
  have hnext (k : ℕ) (a : FiniteFreeApproximation K b (b + 1 - k)) :
      ∃ a' : FiniteFreeApproximation K b (b + 1 - (k + 1 : ℕ)),
        ∃ f : a.complex ⟶ a'.complex, f ≫ a'.map = a.map ∧
          ∀ i, b + 1 - k ≤ i → IsIso (f.f i) := by
    have := a.ge
    have := a.le
    obtain ⟨F, f, β, hF, hge, hle, hcomm, hf, hi, he⟩ :=
      exists_next_approximation a.finiteFree a.map (b + 1 - k) b (by omega)
        a.iso a.epi (hK a.complex a.finiteFree a.map _)
    have heq : b + 1 - (k + 1 : ℕ) = b + 1 - k - 1 := by omega
    refine ⟨⟨F, β, hF, ?_, hle, ?_, ?_⟩, f, hcomm, hf⟩
    · simpa only [heq] using hge
    · simpa only [heq] using hi
    · rw [heq]
      exact he
  choose next f hcomm hf using hnext
  let a : ∀ k : ℕ, FiniteFreeApproximation K b (b + 1 - k) :=
    Nat.rec a₀ (fun k x => next k x)
  let D : ℕ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
    Functor.ofSequence (fun k => f k (a k))
  let coc : Cocone D := ⟨K, NatTrans.ofSequence (fun k => (a k).map) (fun k => by
    change D.map (homOfLE (Nat.le_succ k)) ≫ (a (k + 1)).map = (a k).map ≫ 𝟙 _
    rw [Category.comp_id]
    dsimp only [D]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hcomm k (a k))⟩
  have hstable (k : ℕ) (i : ℤ) (hi : b + 1 - k ≤ i) :
      (D ⋙ HomologicalComplex.eval _ _ i).IsEventuallyConstantFrom k := by
    intro l g
    have hg : k ≤ l := leOfHom g
    have heq : g = homOfLE hg := Subsingleton.elim _ _
    rw [heq]
    apply isIso_map_of_nat
    intro j hj
    change IsIso ((D.map (homOfLE (Nat.le_succ j))).f i)
    simpa only [D, Functor.ofSequence_map_homOfLE_succ] using
      hf j (a j) i (by omega)
  have hι (k : ℕ) (i : ℤ) (hi : b + 1 - k ≤ i) :
      IsIso ((colimit.ι D k).f i) :=
    (hstable k i hi).isIso_ι_of_isColimit
      (isColimitOfPreserves (HomologicalComplex.eval _ _ i) (colimit.isColimit D))
  let α := colimit.desc D coc
  have hfac (k : ℕ) : colimit.ι D k ≫ α = (a k).map := colimit.ι_desc _ _
  refine ⟨colimit D, α, ?_, ?_, ?_⟩
  · intro i
    let k := (b + 1 - i).toNat
    have := hι k i (by dsimp [k]; omega)
    obtain ⟨hfinite, hfree⟩ := (a k).finiteFree.finiteFree i
    have : Module.Finite R ((D.obj k).X i) := hfinite
    have : Module.Free R ((D.obj k).X i) := hfree
    let e := (asIso ((colimit.ι D k).f i)).toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := hι 0 i (by omega)
    have := (a 0).le
    exact ((a 0).complex.isZero_of_isStrictlyLE b i hi).of_iso
      (asIso ((colimit.ι D 0).f i)).symm
  · rw [DerivedCategory.isIso_iff]
    intro i
    let k := (b + 2 - i).toNat
    have hm := hι k (i - 1) (by dsimp [k]; omega)
    have hz := hι k i (by dsimp [k]; omega)
    have hp := hι k (i + 1) (by dsimp [k]; omega)
    have hq := quasiIsoAt_of_isIso_components (colimit.ι D k) i
    have hmap : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (colimit.ι D k))) := by
      change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ i).map _)
      rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ i)]
      exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp hq
    have hcomp := (a k).iso i (by dsimp [k]; omega)
    rw [← hfac k, Functor.map_comp, Functor.map_comp] at hcomp
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (colimit.ι D k)))
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (DerivedCategory.Q.map α))

/-- Approximation in every degree gives the finiteness input to the resolution construction,
by Stacks 064R (3) and Stacks 064S (1). -/
private lemma hasFiniteConeHomology_of_allDegrees
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ∀ n, IsPseudoCoherentFrom (DerivedCategory.Q.obj K) n) :
    HasFiniteConeHomology K := by
  intro E hE α n hn
  let T := (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)).invRotate
  have hT : T ∈ distTriang _ :=
    inv_rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished α)
  have hpc : IsPseudoCoherentFrom T.obj₁ n := by
    have he : IsPseudoCoherent (DerivedCategory.Q.obj E) :=
      ⟨E, ⟨hE.upperBound, hE.finiteFree⟩, ⟨Iso.refl _⟩⟩
    have ht := _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three (n - 1) T hT
      (isPseudoCoherentFrom_of_isPseudoCoherent he (n - 1 + 1)) (hK (n - 1))
    rwa [sub_add_cancel] at ht
  exact _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom T.obj₁ n hpc
    ((DerivedCategory.isLE_iff T.obj₁ n).mp hn)

/-- Approximation in every degree gives a finite free representative with a prescribed upper
bound, in a module universe containing the ring. -/
private lemma exists_finiteFree_representative_of_allDegrees
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (b : ℤ)
    (hK : ∀ n, IsPseudoCoherentFrom K n)
    (hvan : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ) (α : DerivedCategory.Q.obj F ⟶ K),
      (∀ i, Module.Finite R (F.X i) ∧ Module.Free R (F.X i)) ∧
      F.IsStrictlyLE b ∧ IsIso α := by
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  have hL : ∀ n, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) n :=
    fun n => IsPseudoCoherentFrom.ofIso (hK n) e.symm
  obtain ⟨F, α, hF, hb, hα⟩ := exists_finiteFree_resolution L b
    (hasFiniteConeHomology_of_allDegrees L hL)
    (fun i hi => (hvan i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e))
  exact ⟨F, DerivedCategory.Q.map α ≫ e.hom, hF, hb, inferInstance⟩

/-- Approximation in every degree implies pseudo-coherence, in a module universe containing
the ring. -/
private lemma isPseudoCoherent_of_allDegrees
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ n, IsPseudoCoherentFrom K n) : IsPseudoCoherent K := by
  obtain ⟨E, hE, α, hiso, _⟩ := hK 0
  obtain ⟨b, hb⟩ := hE.upperBound
  have hvan (i : ℤ) (hi : max b 0 < i) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
    have := hiso i (by omega)
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i (by omega)).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map α)).symm
  obtain ⟨F, β, hF, hb, hβ⟩ := exists_finiteFree_representative_of_allDegrees K (max b 0) hK hvan
  exact ⟨F, ⟨⟨max b 0, hb⟩, hF⟩, ⟨asIso β⟩⟩

/-! ### From a finite projective representative back to pseudo-coherence -/

/-- Splitting off a projective image: for a map out of a finite projective module whose image
is projective, the kernel is finite and projective. -/
private lemma finite_projective_ker_of_projective_range
    {R : Type*} [Ring R] {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R A] [Module.Projective R A]
    (f : A →ₗ[R] B) [Module.Projective R (LinearMap.range f)] :
    Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  let g := f.rangeRestrict
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  let r : A →ₗ[R] LinearMap.ker g :=
    (LinearMap.id - s ∘ₗ g).codRestrict (LinearMap.ker g) (fun x => by
      change g (x - s (g x)) = 0
      have hx := LinearMap.congr_fun hs (g x)
      simpa only [map_sub, LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr hx.symm)
  have hr : r ∘ₗ (LinearMap.ker g).subtype = LinearMap.id := by
    ext x
    change (x : A) - s (g x) = x
    rw [x.property, map_zero, sub_zero]
  have hsurj : Function.Surjective r := fun x => ⟨x, LinearMap.congr_fun hr x⟩
  have hk : LinearMap.ker g = LinearMap.ker f := LinearMap.ker_rangeRestrict f
  have hf : Module.Finite R (LinearMap.ker g) := Module.Finite.of_surjective r hsurj
  have hp : Module.Projective R (LinearMap.ker g) :=
    Module.Projective.of_split (LinearMap.ker g).subtype r hr
  rw [hk] at hf hp
  exact ⟨hf, hp⟩

/-- Top cohomology of a bounded-above complex of finite projective modules is finite, by the
same descending split-off induction as Stacks 064S. -/
@[sga "6 I 2.1.1" "special case"]
private lemma finite_homology_of_boundedAbove_finiteProjective
    {R : Type u} [Ring R] (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i))
    (b m : ℤ) [E.IsStrictlyLE b]
    (hvan : ∀ i, m < i → IsZero (E.homology i)) :
    Module.Finite R (E.homology m) := by
  let f (i : ℤ) := (E.d i (i + 1)).hom
  have hex (i : ℤ) (hi : m ≤ i) : LinearMap.range (f i) = LinearMap.ker (f (i + 1)) := by
    have he : E.ExactAt (i + 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hvan (i + 1) (by omega))
    rw [HomologicalComplex.exactAt_iff' E i (i + 1) (i + 1 + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at he
    exact he
  have key (n : ℕ) : ∀ i : ℤ, m ≤ i → (b + 1 - i).toNat ≤ n →
      Module.Finite R (LinearMap.ker (f i)) ∧ Module.Projective R (LinearMap.ker (f i)) := by
    induction n with
    | zero =>
      intro i hi hn
      have : Subsingleton (E.X i) :=
        ModuleCat.subsingleton_of_isZero (E.isZero_of_isStrictlyLE b i (by omega))
      exact ⟨Module.Finite.of_finite, inferInstance⟩
    | succ n ih =>
      intro i hi hn
      by_cases hbi : b < i
      · have : Subsingleton (E.X i) :=
          ModuleCat.subsingleton_of_isZero (E.isZero_of_isStrictlyLE b i hbi)
        exact ⟨Module.Finite.of_finite, inferInstance⟩
      · obtain ⟨hfinite, hprojective⟩ := ih (i + 1) (by omega) (by omega)
        rw [← hex i hi] at hfinite hprojective
        obtain ⟨hfin, hproj⟩ := hE i
        exact finite_projective_ker_of_projective_range (f i)
  have hk := (key (b + 1 - m).toNat m le_rfl le_rfl).1
  have hcycles : Module.Finite R (LinearMap.ker (E.sc m).g.hom) := by
    change Module.Finite R (LinearMap.ker (E.d m ((ComplexShape.up ℤ).next m)).hom)
    rw [show (ComplexShape.up ℤ).next m = m + 1 by simp]
    exact hk
  have hh : Module.Finite R (E.sc m).moduleCatLeftHomologyData.H := by
    dsimp [ShortComplex.moduleCatLeftHomologyData]
    infer_instance
  exact Module.Finite.equiv (E.sc m).moduleCatHomologyIso.symm.toLinearEquiv

/-- A bounded-above complex of finite projective modules has finite cone cohomology. -/
private lemma hasFiniteConeHomology_of_boundedAbove_finiteProjective
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i)) :
    HasFiniteConeHomology K := by
  intro E hE α n hn
  obtain ⟨a, ha⟩ := hE.upperBound
  let C := CochainComplex.mappingCone α
  have hC : C.IsStrictlyLE (max (a - 1) b) := isStrictlyLE_mappingCone α a b _
  have hCfin (i : ℤ) : Module.Finite R (C.X i) ∧ Module.Projective R (C.X i) := by
    obtain ⟨hfE, hfrE⟩ := hE.finiteFree (i + 1)
    obtain ⟨hfK, hpK⟩ := hK i
    obtain ⟨e⟩ := nonempty_mappingCone_X_linearEquiv α i
    have : Module.Projective R (E.X (i + 1) × K.X i) := inferInstance
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
  let D := C⟦(-1 : ℤ)⟧
  have hD : D.IsStrictlyLE (max (a - 1) b + 1) :=
    C.isStrictlyLE_shift (max (a - 1) b) (-1) (max (a - 1) b + 1) (by omega)
  have hDfin (i : ℤ) : Module.Finite R (D.X i) ∧ Module.Projective R (D.X i) :=
    hCfin (i + (-1))
  let e : DerivedCategory.Q.obj D ≅ (DerivedCategory.Q.obj C)⟦(-1 : ℤ)⟧ :=
    (DerivedCategory.Q.commShiftIso (-1)).app C
  let eh (i : ℤ) := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).symm.app D ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e
  have hvan (i : ℤ) (hi : n < i) : IsZero (D.homology i) :=
    (DerivedCategory.isZero_of_isLE _ n i hi).of_iso (eh i)
  have hf := finite_homology_of_boundedAbove_finiteProjective D hDfin
    (max (a - 1) b + 1) n hvan
  have : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).obj D) := hf
  exact Module.Finite.equiv (eh n).toLinearEquiv

/-- A bounded-above complex of finite projective modules is pseudo-coherent, in a module
universe containing the ring. -/
private lemma isPseudoCoherent_of_boundedAbove_finiteProjective
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) :
    IsPseudoCoherent (DerivedCategory.Q.obj P) := by
  obtain ⟨F, α, hF, hb, hα⟩ := exists_finiteFree_resolution P b
    (hasFiniteConeHomology_of_boundedAbove_finiteProjective P b hP)
    (fun i hi => DerivedCategory.isZero_of_isLE _ b i hi)
  exact ⟨F, ⟨⟨b, hb⟩, hF⟩, ⟨asIso (DerivedCategory.Q.map α)⟩⟩

/-! ### The characterizations -/

/-- **Stacks 064U.** Pseudo-coherence is equivalent both to `m`-pseudo-coherence for every
integer `m` and to admitting a bounded-above finite projective representative. If cohomology
vanishes above `b`, a finite free representative can be chosen to vanish above `b`. -/
@[stacks 064U]
theorem pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (b : ℤ) :
    let allDegrees := ∀ m : ℤ, IsPseudoCoherentFrom K m
    let finiteProjectiveRepresentative :=
      ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
        (∃ n : ℤ, P.IsStrictlyLE n) ∧
          (∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
          Nonempty (DerivedCategory.Q.obj P ≅ K)
    (IsPseudoCoherent K ↔ allDegrees) ∧
      (IsPseudoCoherent K ↔ finiteProjectiveRepresentative) ∧
      (IsPseudoCoherent K →
        (∀ i : ℤ, b < i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
        ∃ (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
          (α : DerivedCategory.Q.obj F ⟶ K),
            (∀ i : ℤ, Module.Finite R (F.X i) ∧ Module.Free R (F.X i)) ∧
              F.IsStrictlyLE b ∧ IsIso α) := by
  dsimp only
  refine ⟨⟨fun h n => isPseudoCoherentFrom_of_isPseudoCoherent h n,
    isPseudoCoherent_of_allDegrees K⟩, ⟨finiteProjectiveRepresentative_of_pseudoCoherent, ?_⟩, ?_⟩
  · rintro ⟨P, ⟨n, hn⟩, hP, ⟨e⟩⟩
    exact IsPseudoCoherent.ofIso (isPseudoCoherent_of_boundedAbove_finiteProjective P n hP) e
  · intro hK hvan
    exact exists_finiteFree_representative_of_allDegrees K b
      (fun n => isPseudoCoherentFrom_of_isPseudoCoherent hK n) hvan

/-- The all-degree characterization at a fixed carrier universe containing a copy of the
coefficient ring. The copy is obtained by shrinking coefficients, not modules. -/
theorem pseudoCoherent_iff_all_of_small
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) :
    IsPseudoCoherent K ↔ ∀ m, IsPseudoCoherentFrom K m := by
  let := hasDerivedCategoryOfRingEquiv (Shrink.ringEquiv.{v} R)
  have h := pseudoCoherent_iff_of_ringEquiv (Shrink.ringEquiv.{v} R) K
  rw [h.2, (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective _ 0).1]
  exact forall_congr' fun m => (h.1 m).symm

/-- The all-degree characterization is valid even for smaller module carriers. In the non-small
coefficient case both sides force vanishing. -/
theorem pseudoCoherent_iff_all
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : DerivedCategory (ModuleCat.{v} R)) :
    IsPseudoCoherent K ↔ ∀ m, IsPseudoCoherentFrom K m := by
  classical
  by_cases hR : Small.{v} R
  · let := hR
    exact pseudoCoherent_iff_all_of_small K
  refine ⟨fun ⟨E, hE, ⟨e⟩⟩ =>
    (pseudoCoherent_of_isZero K ((isZero_Q_obj_of_not_small hR hE).of_iso e.symm)).2, fun h => ?_⟩
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
    obtain ⟨E, hE, α, hi, _⟩ := h (i - 1)
    have := hi i (by omega)
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
      (isZero_Q_obj_of_not_small hR hE.isBoundedAboveFiniteFree)).of_iso (asIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α)).symm
  have : IsIso (0 : (0 : DerivedCategory (ModuleCat.{v} R)) ⟶ K) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
      (isZero_zero _)).isIso (hz i) _
  exact (pseudoCoherent_of_isZero K ((isZero_zero _).of_iso
    (asIso (0 : (0 : DerivedCategory (ModuleCat.{v} R)) ⟶ K)).symm)).1

/-- The upper bound on a finite free representative can be prescribed even when module carriers
are smaller than the coefficient ring. -/
theorem exists_finiteFree_representative_le
    {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : DerivedCategory (ModuleCat.{v} R)) (b : ℤ)
    (hK : IsPseudoCoherent K)
    (hvan : ∀ i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ) (α : DerivedCategory.Q.obj P ⟶ K),
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      P.IsStrictlyLE b ∧ IsIso α := by
  classical
  by_cases hR : Small.{v} R
  · let := hR
    let := hasDerivedCategoryOfRingEquiv (Shrink.ringEquiv.{v} R)
    let e := Shrink.ringEquiv.{v} R
    let F : ModuleCat.{v} R ⥤ ModuleCat.{v} (Shrink.{v} R) := coefficientRestriction e
    let G : ModuleCat.{v} (Shrink.{v} R) ⥤ ModuleCat.{v} R := coefficientRestriction e.symm
    have hFK := (pseudoCoherent_iff_of_ringEquiv e K).2.mp hK
    have hFvan (i : ℤ) (hi : b < i) : IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} (Shrink.{v} R)) i).obj
          (F.mapDerivedCategory.obj K)) :=
      (F.map_isZero (hvan i hi)).of_iso ((mapDerivedCategoryHomologyIso F i).app K)
    obtain ⟨P, α, hP, hPle, hα⟩ :=
      (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
        (F.mapDerivedCategory.obj K) b).2.2 hFK hFvan
    have := hPle
    have := hα
    let k : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ K :=
      (G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso (asIso α) ≪≫
        restrictScalarsDerivedUnitIso e K
    refine ⟨_, k.hom, fun i => ?_, inferInstance, inferInstance⟩
    have := (hP i).1
    have := (hP i).2
    exact restrictScalars_finiteFree e.symm (P.X i)
  · obtain ⟨P, hP, ⟨e⟩⟩ := hK
    have hKzero := (isZero_Q_obj_of_not_small hR hP).of_iso e.symm
    let k := (DerivedCategory.Q.map_isZero
      (isZero_zero (CochainComplex (ModuleCat.{v} R) ℤ))).iso hKzero
    exact ⟨0, k.hom, finite_free_zero_X, inferInstance, inferInstance⟩

/-! ### The two-out-of-three property -/

/-- **Stacks 064V.** In a distinguished triangle in `D(R)`, if two of the three objects are
pseudo-coherent, then so is the third. -/
@[stacks 064V, sga "6 I 2.5" "b), pseudo-coherent case", sga "6 I 2.6" "partial"]
theorem isPseudoCoherent_of_distinguished
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles) :
    (IsPseudoCoherent T.obj₁ → IsPseudoCoherent T.obj₂ → IsPseudoCoherent T.obj₃) ∧
    (IsPseudoCoherent T.obj₁ → IsPseudoCoherent T.obj₃ → IsPseudoCoherent T.obj₂) ∧
    (IsPseudoCoherent T.obj₂ → IsPseudoCoherent T.obj₃ → IsPseudoCoherent T.obj₁) := by
  have h_iff (K : DerivedCategory (ModuleCat.{v} R)) :
      IsPseudoCoherent K ↔ ∀ m : ℤ, IsPseudoCoherentFrom K m := pseudoCoherent_iff_all K
  refine ⟨fun h₁ h₂ ↦ (h_iff T.obj₃).2 fun m ↦
      _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m T hT
        ((h_iff T.obj₁).1 h₁ (m + 1)) ((h_iff T.obj₂).1 h₂ m),
    fun h₁ h₃ ↦ (h_iff T.obj₂).2 fun m ↦
      _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
        ((h_iff T.obj₁).1 h₁ m) ((h_iff T.obj₃).1 h₃ m),
    fun h₂ h₃ ↦ (h_iff T.obj₁).2 fun m ↦ ?_⟩
  simpa only [sub_add_cancel] using
    _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three (m - 1) T hT
      ((h_iff T.obj₂).1 h₂ ((m - 1) + 1)) ((h_iff T.obj₃).1 h₃ (m - 1))

end StacksDraft.PseudoCoherence
