module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local finite free and finite locally free representatives of a derived object

Let `X` be a ringed space. An object `K` of the derived category of `𝒪_X`-modules *has a
finite locally free representation* if some complex `E` representing `K` admits, on an open
covering of `X`, bounded complexes with finite locally free terms mapping quasi-isomorphically
to the restrictions of `E`; it *has a finite free representation* if the same holds with the
terms isomorphic to `𝒪^{⊕ n}`. This file proves the two conditions are equivalent: a finite
locally free module is free on a smaller open, and shrinking the covering turns local charts
for the finitely many nonzero terms of each local complex into a single finite free model.

## Main definitions

* `AlgebraicGeometry.RingedSpace.HasFiniteLocallyFreeRepresentation`: local bounded finite
  locally free representatives of a derived object.
* `AlgebraicGeometry.RingedSpace.HasFiniteFreeRepresentation`: local bounded finite free
  representatives.

## Main results

* `RingedSpace.hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation`: the two
  conditions agree.
* `AlgebraicGeometry.RingedSpace.isPerfect_of_hasFiniteFreeRepresentation`: a derived object
  with local bounded finite free representatives is perfect.
* `AlgebraicGeometry.RingedSpace.isFiniteLocallyFree_finiteFree`: `𝒪^{⊕ n}` is finite locally
  free.
* `AlgebraicGeometry.RingedSpace.isFiniteLocallyFree_of_iso`: finite local freeness transports
  along an isomorphism.
* `AlgebraicGeometry.RingedSpace.exists_free_iso_over_of_bounded`: the terms of a bounded
  complex with finite locally free terms are simultaneously free on some open neighbourhood of
  any given point.

## Implementation notes

Both conditions phrase "the restriction of `E` to `U i` is represented by `P`" through an
actual quasi-isomorphism `P ⟶ E|_{U i}` of complexes, which avoids choosing a restriction
functor on derived categories; this is also the shape in which
`AlgebraicGeometry.RingedSpace.IsPerfectComplex` is stated, so the comparison with perfectness
is immediate.

Finite local freeness is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, whose local
data is a family of generating sections on a covering; it is stated for modules on a site, so
the charts it produces are isomorphisms with a free module on the slice site over an open
rather than with `StrictlyPerfect.finiteFree` on the restricted ringed space. The two are
compared by `AlgebraicGeometry.RingedSpace.nonempty_restrictModules_obj_iso_finiteFree`,
which goes through `AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`. Free modules are
indexed by a type in the module universe, so `𝒪^{⊕ n}` is the free module on
`ULift (Fin n)`, which is `AlgebraicGeometry.RingedSpace.finiteFreeIsoFree`.

Refining the covering produces opens of an open subspace of `X`, and the statement needs opens
of `X`. That passage is `AlgebraicGeometry.RingedSpace.nestedComplex` together with
`AlgebraicGeometry.RingedSpace.exists_quasiIso_nestedComplex_restrictComplex`.

All universes coincide, as they must for `StrictlyPerfect.OXMod` to exist; the index type of a
covering is then taken in that same universe, and the universe of the derived category is left
free.

## References

* [Stacks Project, Tag 0BCJ](https://stacks.math.columbia.edu/tag/0BCJ)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

attribute [local instance 10] nestedModulesEquivalence_functor_additive

/-! ### Finite free modules are finite locally free -/

/-- `𝒪_X^{⊕ n}` is the free `𝒪_X`-module on `ULift (Fin n)`: the `n`-fold biproduct of the
structure module is the coproduct over a type in the module universe with `n` elements. -/
def finiteFreeIsoFree (X : RingedSpace.{u, u}) (n : ℕ) :
    finiteFree X n ≅
      SheafOfModules.free (R := structureSheafOfRings X) (ULift.{u} (Fin n)) :=
  (biproduct.whiskerEquiv (Equiv.ulift.{u, 0}.symm : Fin n ≃ ULift.{u} (Fin n))
      (fun _ => Iso.refl _)).trans
    (biproduct.isoCoproduct (fun _ : ULift.{u} (Fin n) => structureModule X))

/-- Generating sections pushed forward along an epimorphism, with the structural map presented
as a composite.

This is `SheafOfModules.GeneratingSections.ofEpi` with the family of sections given as the image
of `σ.π ≫ p` under `freeHomEquiv` rather than sectionwise. The two constructions agree, but only
this presentation makes the structural map of the result *equal* to `σ.π ≫ p` by
`Equiv.symm_apply_apply`: the corresponding Mathlib lemma
`SheafOfModules.GeneratingSections.ofEpi_π` does not elaborate within the heartbeat budget for
sheaves of modules on a ringed space, because matching its statement compares two
`freeHomEquiv`s through the sheafification adjunction. -/
def generatingSectionsComp {V : Opens X.carrier}
    {A B : _root_.SheafOfModules.{u} ((structureSheafOfRings X).over V)}
    (σ : A.GeneratingSections) (p : A ⟶ B) [Epi p] : B.GeneratingSections where
  I := σ.I
  s := B.freeHomEquiv (σ.π ≫ p)
  epi := by
    rw [Equiv.symm_apply_apply]
    have hσ : Epi σ.π := σ.epi
    infer_instance

/-- Invertibility of a morphism of sheaves of modules transports along an equality of
morphisms. Stated so that the rewrite happens over morphism *variables*: rewriting with the
equation at the use site instead makes `rw` abstract the goal over a structural map built from
`freeHomEquiv`, which does not fit in the heartbeat budget. -/
theorem isIso_of_hom_eq {V : Opens X.carrier}
    {A B : _root_.SheafOfModules.{u} ((structureSheafOfRings X).over V)} {f g : A ⟶ B}
    (h : f = g) (hg : IsIso g) : IsIso f := by
  rw [h]
  exact hg

/-- The structural map of the pushed-forward generating sections is the composite. -/
theorem generatingSectionsComp_π {V : Opens X.carrier}
    {A B : _root_.SheafOfModules.{u} ((structureSheafOfRings X).over V)}
    (σ : A.GeneratingSections) (p : A ⟶ B) [Epi p] :
    (generatingSectionsComp σ p).π = σ.π ≫ p :=
  B.freeHomEquiv.symm_apply_apply _

/-- Pushing generating sections forward along an epimorphism keeps the index type, so it keeps
finite type. -/
theorem generatingSectionsComp_isFiniteType {V : Opens X.carrier}
    {A B : _root_.SheafOfModules.{u} ((structureSheafOfRings X).over V)}
    (σ : A.GeneratingSections) (p : A ⟶ B) [Epi p] (hσ : σ.IsFiniteType) :
    (generatingSectionsComp σ p).IsFiniteType :=
  ⟨hσ.finite⟩

/-- Finite local freeness transports along an isomorphism: the local generating sections of
the target compose with the isomorphism to give local generating sections of the source. -/
theorem isFiniteLocallyFree_of_iso {M N : OXMod.{u, u} X} (e : M ≅ N)
    (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X) N) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X) M := by
  obtain ⟨q, hq, hfinite⟩ := hN.exists_isFiniteLocallyFreeData
  constructor
  refine ⟨({ I := q.I
             X := q.X
             coversTop := q.coversTop
             generators := fun i => generatingSectionsComp (q.generators i)
               (e.inv.over (q.X i)) } :
            _root_.SheafOfModules.LocalGeneratorsData.{u} M), ?_, ?_⟩
  · constructor
    intro i
    show IsIso (generatingSectionsComp (q.generators i) (e.inv.over (q.X i))).π
    have hiso : IsIso (q.generators i).π := hq.isIso i
    have hover : IsIso (e.inv.over (q.X i)) := inferInstance
    exact isIso_of_hom_eq
      (generatingSectionsComp_π (q.generators i) (e.inv.over (q.X i)))
      (IsIso.comp_isIso' hiso hover)
  · constructor
    intro i
    exact generatingSectionsComp_isFiniteType _ _ (hfinite.isFiniteType i)

/-- `𝒪_X^{⊕ n}` is finite locally free: it is free, and its basis is finite. -/
theorem isFiniteLocallyFree_finiteFree (X : RingedSpace.{u, u}) (n : ℕ) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X)
      (finiteFree X n) := by
  have hfree : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X)
      (SheafOfModules.free (R := structureSheafOfRings X) (ULift.{u} (Fin n))) := by
    constructor
    refine ⟨(SheafOfModules.free.generatingSections
        (R := structureSheafOfRings X) (ULift.{u} (Fin n))).localGeneratorsData,
      inferInstance, ?_⟩
    constructor
    intro _
    exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
  exact isFiniteLocallyFree_of_iso (finiteFreeIsoFree X n) hfree

/-! ### Local charts for a finite locally free module -/

/-- A finite locally free module is, on some open neighbourhood of any given point, isomorphic
to a free module on a finite type. -/
theorem exists_free_iso_over_near {M : OXMod.{u, u} X}
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X) M)
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (M.over U ≅ SheafOfModules.free
        (R := (structureSheafOfRings X).over U) (ULift.{u} (Fin n))) := by
  classical
  obtain ⟨q, hq, hfinite⟩ := hM.exists_isFiniteLocallyFreeData
  obtain ⟨i, hxi⟩ := IsOpenCover.exists_mem
    ((Opens.coversTop_iff X.carrier q.X).mp q.coversTop) x
  let G := q.generators i
  let _ : G.IsFiniteType := hfinite.isFiniteType i
  let _ : IsIso G.π := hq.isIso i
  let _ : Fintype G.I := Fintype.ofFinite G.I
  refine ⟨q.X i, hxi, Fintype.card G.I, ⟨(asIso G.π).symm.trans
    ((SheafOfModules.freeFunctor (R := (structureSheafOfRings X).over (q.X i))).mapIso
      (Equiv.toIso ?_))⟩⟩
  exact
    { toFun := fun j => ⟨Fintype.equivFin G.I j⟩
      invFun := fun j => (Fintype.equivFin G.I).symm j.down
      left_inv := fun j => (Fintype.equivFin G.I).left_inv j
      right_inv := fun j => by cases j; simp }

/-- A chart for a module on an open set restricts to a chart on any smaller open set. -/
theorem nonempty_free_iso_over_of_le (M : OXMod.{u, u} X) {U V : Opens X.carrier}
    (h : V ≤ U) (n : ℕ)
    (e : M.over U ≅ SheafOfModules.free
      (R := (structureSheafOfRings X).over U) (ULift.{u} (Fin n))) :
    Nonempty (M.over V ≅ SheafOfModules.free
      (R := (structureSheafOfRings X).over V) (ULift.{u} (Fin n))) := by
  let F := SheafOfModules.overMap (structureSheafOfRings X) (homOfLE h)
  let η := SheafOfModules.overMapUnitIso (R := structureSheafOfRings X) (homOfLE h)
  exact ⟨((SheafOfModules.overFunctorMap (structureSheafOfRings X) (homOfLE h)).app M).symm ≪≫
    F.mapIso e ≪≫ (SheafOfModules.mapFreeIso F (ULift.{u} (Fin n)) η).symm⟩

/-- A bounded complex whose terms are finite locally free has, on some open neighbourhood of
any given point, all of its terms free: the finitely many nonzero terms have charts near the
point, and one intersects them. -/
theorem exists_free_iso_over_of_bounded (P : CochainComplex (OXMod.{u, u} X) ℤ)
    (hbounded : {j : ℤ | ¬ IsZero (P.X j)}.Finite)
    (hterms : ∀ j : ℤ,
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := structureSheafOfRings X) (P.X j))
    (x : X.carrier) :
    ∃ V : Opens X.carrier, x ∈ V ∧ ∀ j : ℤ, ∃ n : ℕ,
      Nonempty ((P.X j).over V ≅ SheafOfModules.free
        (R := (structureSheafOfRings X).over V) (ULift.{u} (Fin n))) := by
  classical
  let S : Finset ℤ := hbounded.toFinset
  let J := {j : ℤ // j ∈ S}
  have hcharts : ∀ j : J, ∃ V : Opens X.carrier, x ∈ V ∧ ∃ n : ℕ,
      Nonempty ((P.X j.1).over V ≅ SheafOfModules.free
        (R := (structureSheafOfRings X).over V) (ULift.{u} (Fin n))) :=
    fun j => exists_free_iso_over_near (hterms j.1) x
  choose V hV n hchart using hcharts
  refine ⟨⨅ j : J, V j, ?_, fun j => ?_⟩
  · have hcoe :
        ((⨅ j : J, V j : Opens X.carrier) : Set X.carrier) = ⋂ j : J, (V j : Set _) := by
      simp only [Opens.coe_iInf]
    show x ∈ ((⨅ j : J, V j : Opens X.carrier) : Set X.carrier)
    rw [hcoe]
    exact Set.mem_iInter.mpr hV
  · by_cases hj : j ∈ S
    · exact ⟨n ⟨j, hj⟩, nonempty_free_iso_over_of_le (P.X j)
        (iInf_le (fun k : J => V k) ⟨j, hj⟩) (n ⟨j, hj⟩) (Classical.choice (hchart ⟨j, hj⟩))⟩
    · have hz : IsZero (P.X j) := by
        by_contra hnz
        exact (by simpa [S] using hj : j ∉ {j : ℤ | ¬ IsZero (P.X j)}) hnz
      refine ⟨0, ⟨IsZero.iso ?_ ?_⟩⟩
      · have hpz := overFunctor_preservesZeroMorphisms X (⨅ j : J, V j)
        exact Functor.map_isZero
          (SheafOfModules.overFunctor (structureSheafOfRings X) (⨅ j : J, V j)) hz
      · let Z := SheafOfModules.free
          (R := (structureSheafOfRings X).over (⨅ j : J, V j)) (ULift.{u} (Fin 0))
        have hunique : ∀ Y : SheafOfModules ((structureSheafOfRings X).over (⨅ j : J, V j)),
            Unique (Z ⟶ Y) := fun Y =>
          { default := 0
            uniq := by
              intro f
              apply (SheafOfModules.freeHomEquiv Y).injective
              funext i
              exact isEmptyElim i.down }
        exact (isZero_zero _).of_iso
          ((IsInitial.ofUnique Z).uniqueUpToIso (isZero_zero _).isInitial)

/-! ### Comparison with `StrictlyPerfect.finiteFree` on the restricted space -/

/-- A module which is free of rank `n` on the slice site over `U` restricts to `𝒪^{⊕ n}` on the
open subspace `U`. -/
theorem nonempty_restrictModules_obj_iso_finiteFree (M : OXMod.{u, u} X) (U : Opens X.carrier)
    (n : ℕ)
    (e : M.over U ≅ SheafOfModules.free
      (R := (structureSheafOfRings X).over U) (ULift.{u} (Fin n))) :
    Nonempty ((restrictModules X U).obj M ≅
      finiteFree (X.restrict U.isOpenEmbedding) n) := by
  let _ := overToRestricted_additive X U
  let _ := overToRestricted_isEquivalence X U
  let _ : PreservesColimitsOfSize.{u, u} (overToRestricted X U) :=
    Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _
  exact ⟨(restrictModulesIsoOverComp X U).symm.app M ≪≫
    (overToRestricted X U).mapIso e ≪≫
      (SheafOfModules.mapFreeIso (overToRestricted X U) (ULift.{u} (Fin n))
        (U.sheafOfModulesEquivOverUnit (structureSheafOfRings X))).symm ≪≫
        (finiteFreeIsoFree (X.restrict U.isOpenEmbedding) n).symm⟩

/-- The identification of modules on `(X|_U)|_V` with modules on the corresponding open
subspace of `X` sends `𝒪^{⊕ n}` to `𝒪^{⊕ n}`. -/
def nestedFiniteFreeIso (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) (n : ℕ) :
    (nestedModulesEquivalence U V).functor.obj
        (finiteFree ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) n) ≅
      finiteFree (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) n :=
  letI : PreservesFiniteBiproducts (nestedModulesEquivalence U V).functor :=
    Functor.preservesFiniteBiproductsOfAdditive _
  (nestedModulesEquivalence U V).functor.mapBiproduct
      (fun _ : Fin n =>
        structureModule ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ≪≫
    biproduct.mapIso (fun _ => nestedStructureIso U V)

/-! ### The two notions of local representation -/

/-- An object of the derived category of `𝒪_X`-modules *has a finite locally free
representation* if it is represented by a complex which, on an open covering of `X`, receives
quasi-isomorphisms from bounded complexes all of whose terms are finite locally free. -/
def HasFiniteLocallyFreeRepresentation [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ E : CochainComplex (OXMod.{u, u} X) ℤ,
    Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
      ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
        ∀ i : I,
          ∃ P : CochainComplex (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
            {j : ℤ | ¬ IsZero (P.X j)}.Finite ∧
              (∀ j : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
                (R := structureSheafOfRings (X.restrict (U i).isOpenEmbedding)) (P.X j)) ∧
                ∃ f : P ⟶ restrictComplex E (U i), QuasiIso f

/-- An object of the derived category of `𝒪_X`-modules *has a finite free representation* if it
is represented by a complex which, on an open covering of `X`, receives quasi-isomorphisms from
bounded complexes all of whose terms are isomorphic to some `𝒪^{⊕ n}`. -/
def HasFiniteFreeRepresentation [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ E : CochainComplex (OXMod.{u, u} X) ℤ,
    Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
      ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
        ∀ i : I,
          ∃ P : CochainComplex (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
            {j : ℤ | ¬ IsZero (P.X j)}.Finite ∧
              (∀ j : ℤ, ∃ n : ℕ,
                Nonempty (P.X j ≅ finiteFree (X.restrict (U i).isOpenEmbedding) n)) ∧
                ∃ f : P ⟶ restrictComplex E (U i), QuasiIso f

/-- Local bounded finite locally free representatives can be replaced, after refining the
cover, by bounded finite free representatives.

Forwards: index the refinement by the pairs consisting of a member `U i` of the given covering
and a point of it, shrink `U i` around that point until every term of its local model is free,
and transport the model and its quasi-isomorphism to the corresponding open subspace of `X`.
Backwards: `𝒪^{⊕ n}` is finite locally free, and finite local freeness transports along an
isomorphism. -/
theorem hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X)) :
    HasFiniteLocallyFreeRepresentation K ↔ HasFiniteFreeRepresentation K := by
  classical
  constructor
  · rintro ⟨E, hEK, I, U, hU, hmodels⟩
    let J := Σ i : I, (X.restrict (U i).isOpenEmbedding).carrier
    let P : ∀ a : J, CochainComplex
        (OXMod.{u, u} (X.restrict (U a.1).isOpenEmbedding)) ℤ := fun a =>
      Classical.choose (hmodels a.1)
    have hP (a : J) :
        {j : ℤ | ¬ IsZero ((P a).X j)}.Finite ∧
          (∀ j : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            (R := structureSheafOfRings (X.restrict (U a.1).isOpenEmbedding)) ((P a).X j)) ∧
            ∃ f : P a ⟶ restrictComplex E (U a.1), QuasiIso f :=
      Classical.choose_spec (hmodels a.1)
    let g (a : J) : P a ⟶ restrictComplex E (U a.1) := Classical.choose (hP a).2.2
    have hg (a : J) : QuasiIso (g a) := Classical.choose_spec (hP a).2.2
    let chart (a : J) := exists_free_iso_over_of_bounded (P a) (hP a).1 (hP a).2.1 a.2
    let V (a : J) : Opens (X.restrict (U a.1).isOpenEmbedding).carrier :=
      Classical.choose (chart a)
    have hchart (a : J) : a.2 ∈ V a ∧ ∀ j : ℤ, ∃ n : ℕ,
        Nonempty (((P a).X j).over (V a) ≅ SheafOfModules.free
          (R := (structureSheafOfRings (X.restrict (U a.1).isOpenEmbedding)).over (V a))
            (ULift.{u} (Fin n))) := Classical.choose_spec (chart a)
    refine ⟨E, hEK, J, fun a => (U a.1).isOpenEmbedding.functor.obj (V a), ?_, fun a => ?_⟩
    · refine top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
      obtain ⟨i, hxi⟩ := IsOpenCover.exists_mem hU x
      exact ⟨⟨i, ⟨x, hxi⟩⟩, ⟨⟨x, hxi⟩, (hchart ⟨i, ⟨x, hxi⟩⟩).1, rfl⟩⟩
    · refine ⟨nestedComplex (U a.1) (V a) (restrictComplex (P a) (V a)), ?_, ?_,
        exists_quasiIso_nestedComplex_restrictComplex (U a.1) (V a) E (g a) (hg a)⟩
      · refine (hP a).1.subset fun j hj hz => hj ?_
        exact (nestedModulesEquivalence (U a.1) (V a)).functor.isZero_obj
          (Functor.map_isZero
            (restrictModules (X.restrict (U a.1).isOpenEmbedding) (V a)) hz)
      · intro j
        obtain ⟨n, ⟨eV⟩⟩ := (hchart a).2 j
        exact ⟨n, ⟨(nestedModulesEquivalence (U a.1) (V a)).functor.mapIso
          (Classical.choice (nonempty_restrictModules_obj_iso_finiteFree
            ((P a).X j) (V a) n eV)) ≪≫ nestedFiniteFreeIso (U a.1) (V a) n⟩⟩
  · rintro ⟨E, hEK, I, U, hU, hmodels⟩
    refine ⟨E, hEK, I, U, hU, fun i => ?_⟩
    obtain ⟨P, hbounded, hterms, f, hf⟩ := hmodels i
    refine ⟨P, hbounded, fun j => ?_, f, hf⟩
    obtain ⟨n, hiso⟩ := hterms j
    exact isFiniteLocallyFree_of_iso (Classical.choice hiso)
      (isFiniteLocallyFree_finiteFree (X.restrict (U i).isOpenEmbedding) n)

/-- A derived object with local bounded finite free representatives is perfect: a bounded
complex whose terms are isomorphic to finite free modules is strictly perfect. -/
@[sga "6 I 4.8" "partial"]
theorem isPerfect_of_hasFiniteFreeRepresentation [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {K : DerivedCategory (OXMod.{u, u} X)} (h : HasFiniteFreeRepresentation K) :
    IsPerfect K := by
  obtain ⟨E, hEK, I, U, hU, hmodels⟩ := h
  refine ⟨E, ⟨I, U, hU, fun i => ?_⟩, hEK⟩
  obtain ⟨P, hbounded, hterms, f, hf⟩ := hmodels i
  refine ⟨P, ⟨hbounded, fun j => ?_⟩, f, hf⟩
  obtain ⟨n, ⟨e⟩⟩ := hterms j
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨n, ⟨⟨e.hom, e.inv, by simp⟩⟩⟩

end AlgebraicGeometry.RingedSpace

end
