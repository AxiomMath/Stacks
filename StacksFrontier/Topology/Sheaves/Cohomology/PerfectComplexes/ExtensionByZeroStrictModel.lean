module

public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.SupportFromRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality

/-!
# A strict model near a point for a module supported at that point

Let `X` be a regular scheme, let `x` be a point of `X` and let `ℱ` be a coherent `𝒪_X`-module
whose stalks vanish away from `x`. Then there is an open neighbourhood `V` of `x` and a
*bounded* complex `E` of `𝒪_X`-modules on the whole of `X` which represents `ℱ` in degree zero
in the derived category and whose terms are, *after restriction to `V`*, direct summands of
finite free modules. Away from `V` nothing at all is asserted about the terms of `E`.

Such a complex is what a consumer needs in order to compute a derived internal Hom out of `ℱ`
by a germ-local argument at `x`: strict perfection of a global complex is unavailable (a
coherent module supported at one point is not locally a summand of a finite free module there),
while strict perfection on `V` only would give a complex living on `V` and not on `X`.

## Main results

All names below are in the namespace `Stacks.Cohomology.ExtensionByZeroStrictModel`.

* `exists_boundedStrictModel_nearPoint`: the statement above, with the termwise condition in the
  form of [Stacks, Tag 08FL] — each term of `E`, restricted to the site over `V`, is a retract of
  `𝒪^{⊕r}`.
* `exists_boundedStrictModel_nearPoint_isDirectSummandOfFiniteFree`: the same, with the termwise
  condition in the open-subspace form `StrictlyPerfect.IsDirectSummandOfFiniteFree`, which is the
  condition `StrictlyPerfect.IsStrictlyPerfect` is built out of.
* `exists_strictlyPerfect_jShriek_model`: the data both of those are read off — the open `V`, a
  strictly perfect complex `P` on the open subspace `V`, and an isomorphism `Q(j_{V,!}P) ≅ ℱ[0]`.
* `quasiIso_extensionRestrictionComplexCounit` and `nonempty_iso_Q_jShriek`: the general
  mechanism, for an arbitrary ringed space — the degreewise counit `j_{V,!}j_V^*E ⟶ E` is a
  quasi-isomorphism as soon as the cohomology sheaves of `E` have vanishing stalks outside `V`, so
  the extension by zero of a local model of `E` over `V` represents `E`.

## Implementation notes

The complex is produced by **extension by zero**. [Stacks, Tag 0FDC] (here
`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`) gives a complex `E₀` on `X`
representing `ℱ[0]`, an open cover of `X`, and over each member a strictly perfect complex with
a quasi-isomorphism to the restriction of `E₀`; `V` is a member of that cover containing `x` and
`P` is the strictly perfect complex over it. The complex on `X` is `E := j_{V,!}P`, the
extension by zero of [Stacks, Tag 00AB].

The isomorphism `Q(j_{V,!}P) ≅ ℱ[0]` is obtained **at the level of complexes**, not in the
derived category: the composite
`j_{V,!}P ⟶ j_{V,!}j_V^*E₀ ⟶ E₀`
of `j_{V,!}` applied to the local quasi-isomorphism with the degreewise counit of
`j_{V,!} ⊣ j_V^*` is a quasi-isomorphism, so `Q` inverts it. No derived adjunction and no
derived pushforward is used, and in particular `{x}` is *not* assumed closed, which the route
through [Stacks, Tag 08DF] would have required. That the counit is a quasi-isomorphism is
checked stalkwise ([Stacks, Tag 08TL]): inside `V` it is a degreewise isomorphism on stalks,
and outside `V` the stalks of `j_{V,!}j_V^*E₀` vanish by [Stacks, Tag 00AB] while the stalks of
the cohomology sheaves of `E₀` vanish because those sheaves are `ℱ` and `0`, supported in
`{x} ⊆ V`.

Three spellings of the structure sheaf of rings meet here, as they do in
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean`:
`StrictlyPerfect.structureSheafOfRings X.toRingedSpace` (used by `OXMod` and so by Tag 08CM),
`structureSheafRing X.toRingedSpace` (used by the extension-by-zero material) and
`structureSheaf X.sheaf` (used by the ringed site and by the statements below). All three are
equal by `rfl`, and so are `StrictlyPerfect.OXMod X.toRingedSpace`, `X.Modules` and
`Stacks.SheafOfModules.StructureSheafModules X.sheaf`, and likewise
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace V` and
`ExtensionByZeroModules.jStar V (structureSheaf X.sheaf)`; the identifications are discharged by
the defeq checks of the applications themselves, at default transparency, so no transparency
attribute is needed. The two general lemmas are stated at the `structureSheafRing` spelling,
which is where `ExtensionByZeroModules` and
`Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.extensionRestrictionComplexCounit` live, and
the results about a scheme at `structureSheaf X.sheaf`, which is what the consumers use.

Passing from the open-subspace form of the termwise condition to the slice-site form of
Tag 08FL goes through `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward`, the
equivalence between modules on the open subspace `V` and modules over the slice sheaf of rings,
which is exact and carries the unit sheaf to the unit sheaf, so
`SheafOfModules.isDirectSummandOfFiniteFree_map` applies to it;
`restrictModulesCompBackwardIso` identifies its value on the restriction of a module to `V` with
the restriction of that module to the slice over `V`.

## References

* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC), a coherent module on a
  regular scheme is perfect.
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB), extension by zero along
  an open immersion.
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM), perfect complexes on a
  ringed space.
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL), strictly perfect
  complexes on a ringed site.
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4), strictly perfect
  complexes on a ringed space.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), quasi-isomorphy is
  stalkwise.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open ExtensionByZeroModules
open Stacks.Cohomology.SupportedComplexes (exactFunctorHomologyIso)
open Stacks.Cohomology.ExtensionByZeroBaseChange (isZero_stalkObj_iff)
open Stacks.Cohomology.ExtensionByZeroBaseChangeDerived (extensionRestrictionComplexCounit
  isIso_stalkMap_extensionRestrictionComplexCounit)

namespace Stacks.Cohomology.ExtensionByZeroStrictModel

universe u d

attribute [local instance] HasDerivedCategory.standard

/-- Away from the support of a sheaf of modules its stalk is a zero object. -/
theorem isZero_stalk_of_notMem_supp {Y : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} Y}
    (M : SheafOfModules.{u} R) {y : Y} (hy : y ∉ SheafOfModules.supp M) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf y) := by
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk] at hy
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact not_nontrivial_iff_subsingleton.mp hy

/-- A morphism between two zero objects is an isomorphism. -/
theorem isIso_of_isZero_of_isZero {C : Type*} [Category* C] [HasZeroMorphisms C] {A B : C}
    (hA : IsZero A) (hB : IsZero B) (f : A ⟶ B) : IsIso f :=
  ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

/-- The degreewise counit of `j_! ⊣ j^*` is a quasi-isomorphism on a complex whose cohomology
sheaves have vanishing stalks outside the open subspace. -/
theorem quasiIso_extensionRestrictionComplexCounit {Y : RingedSpace.{u, u}} (V : Opens Y.carrier)
    (E : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hstalk : ∀ (n : ℤ) (y : Y.carrier), y ∉ V →
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ) n).obj E).val.presheaf y)) :
    QuasiIso (extensionRestrictionComplexCounit V E) := by
  refine AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ fun y => ?_
  by_cases hy : y ∈ V
  · have hcomp : ∀ n : ℤ, IsIso ((((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing Y) y).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extensionRestrictionComplexCounit V E)).f n) := fun n =>
      isIso_stalkMap_extensionRestrictionComplexCounit V E y hy n
    have : IsIso (((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        y).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extensionRestrictionComplexCounit V E)) :=
      HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  · rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine isIso_of_isZero_of_isZero ?_ ?_ _
    · rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      refine HomologicalComplex.ExactAt.of_isZero ?_
      exact (isZero_stalkObj_iff (structureSheafRing Y) y _).2
        (isZero_stalk_jShriek V (structureSheafRing Y)
          ((jStar V (structureSheafRing Y)).obj (E.X n)) y hy)
    · refine IsZero.of_iso ?_ ((exactFunctorHomologyIso
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y) n).app E)
      exact (isZero_stalkObj_iff (structureSheafRing Y) y _).2 (hstalk n y hy)

/-- **Extension by zero of a local model.** If the cohomology sheaves of `E` have vanishing
stalks outside the open subspace `V` and `P` is quasi-isomorphic to the restriction of `E` to
`V`, then the extension by zero of `P` represents the same object of the derived category as
`E`. -/
theorem nonempty_iso_Q_jShriek {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (SheafOfModules.{u} (structureSheafRing Y))]
    (V : Opens Y.carrier) (E : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hstalk : ∀ (n : ℤ) (y : Y.carrier), y ∉ V →
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ) n).obj E).val.presheaf y))
    (P : CochainComplex (SheafOfModules.{u} (resRing V (structureSheafRing Y))) ℤ)
    (f : P ⟶ ((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
    (hf : QuasiIso f) :
    Nonempty (DerivedCategory.Q.obj (((jShriek V (structureSheafRing Y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅ DerivedCategory.Q.obj E) := by
  have := hf
  have := quasiIso_extensionRestrictionComplexCounit V E hstalk
  have : QuasiIso (((jShriek V (structureSheafRing Y)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ extensionRestrictionComplexCounit V E) := inferInstance
  have : IsIso (DerivedCategory.Q.map
      (((jShriek V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
        extensionRestrictionComplexCounit V E)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact ⟨asIso (DerivedCategory.Q.map
    (((jShriek V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
      extensionRestrictionComplexCounit V E))⟩

variable {X : Scheme.{u}}

/-- The extension by zero of a strictly perfect complex has finitely many nonzero terms. -/
private theorem finite_not_isZero_jShriek {X : Scheme.{u}} (V : Opens X)
    (P : CochainComplex (SheafOfModules.{u} (resRing V (structureSheaf X.sheaf))) ℤ)
    (hP : IsStrictlyPerfect (X := X.toRingedSpace.restrict V.isOpenEmbedding) P) :
    {i : ℤ | ¬ IsZero ((((jShriek V (structureSheaf X.sheaf)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).X i)}.Finite :=
  hP.bounded.subset fun _ hi hz => hi (Functor.map_isZero (jShriek V (structureSheaf X.sheaf)) hz)

/-- The unit of `j_! ⊣ j^*` is an isomorphism at every object. -/
private theorem isIso_jShriekAdjunction_unit_app {X : Scheme.{u}} (V : Opens X)
    (A : SheafOfModules.{u} (resRing V (structureSheaf X.sheaf))) :
    IsIso ((jShriekAdjunction V (structureSheaf X.sheaf)).unit.app A) :=
  have := isIso_jShriekAdjunction_unit V (structureSheaf X.sheaf)
  inferInstance

/-- The data behind the main results: an open neighbourhood `V` of `x`, a strictly perfect
complex `P` on the open subspace `V`, and an isomorphism in the derived category between the
extension by zero of `P` and `F` placed in degree zero. -/
theorem exists_strictlyPerfect_jShriek_model (x : X) (F : X.Modules) [F.IsCoherent]
    (hX : IsRegular X) (hsupp : (SheafOfModules.supp F : Set X) ⊆ {x}) :
    ∃ (V : Opens X) (_ : x ∈ V)
      (P : CochainComplex (SheafOfModules.{u} (resRing V (structureSheaf X.sheaf))) ℤ),
      IsStrictlyPerfect (X := X.toRingedSpace.restrict V.isOpenEmbedding) P ∧
        Nonempty (DerivedCategory.Q.obj
            (((jShriek V (structureSheaf X.sheaf)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≅
          (DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  classical
  -- Tag 0FDC: `F` placed in degree zero is a perfect object.
  obtain ⟨E₀, hE₀, ⟨e₀⟩⟩ :=
    AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular hX F
  obtain ⟨I, U, hU, hloc⟩ := hE₀
  obtain ⟨i₀, hi₀⟩ : ∃ i : I, x ∈ U i := by
    have hx : x ∈ iSup U := by rw [hU]; trivial
    simpa only [Opens.mem_iSup] using hx
  obtain ⟨P, hP, f, hf⟩ := hloc i₀
  refine ⟨U i₀, hi₀, P, hP, ⟨?_⟩⟩
  -- Cohomological support of `E₀`: its cohomology sheaves vanish away from `x`.
  have hFst : ∀ y : X.carrier, y ∉ ({x} : Set X.carrier) →
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf y) :=
    fun y hy => isZero_stalk_of_notMem_supp F fun hmem => hy (hsupp hmem)
  have hsuppE :
      Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn (structureSheaf X.sheaf)
        ({x} : Set X.carrier) (DerivedCategory.Q.obj E₀) :=
    Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _ e₀.symm
      (Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleFunctor_obj
        (structureSheaf X.sheaf) ({x} : Set X.carrier) 0 F hFst)
  have hstalkE₀ : ∀ (n : ℤ) (y : X.carrier), y ∉ U i₀ →
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) n).obj E₀).val.presheaf y) := by
    intro n y hy
    have hyx : y ∉ ({x} : Set X.carrier) := by
      rintro rfl
      exact hy hi₀
    refine (hsuppE n y hyx).of_iso ?_
    exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb (structureSheaf X.sheaf)).mapIso ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheaf X.sheaf)) n).app E₀))).symm
  exact (nonempty_iso_Q_jShriek (Y := X.toRingedSpace) (U i₀) E₀ hstalkE₀ P f hf).some ≪≫ e₀

/-- **A bounded complex on the whole of `X` representing a module supported at `x`, strictly
perfect near `x`.** Termwise condition in the form of [Stacks, Tag 08FL]: each term of `E`,
restricted to the site over `V`, is a retract of a finite free module. -/
theorem exists_boundedStrictModel_nearPoint (x : X) (F : X.Modules) [F.IsCoherent]
    (hX : IsRegular X) (hsupp : (SheafOfModules.supp F : Set X) ⊆ {x}) :
    ∃ (V : TopologicalSpace.Opens X) (_ : x ∈ V)
      (E : CochainComplex (Stacks.SheafOfModules.StructureSheafModules X.sheaf) ℤ),
      {i : ℤ | ¬ CategoryTheory.Limits.IsZero (E.X i)}.Finite ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (CategoryTheory.Retract ((E.X i).over V)
        (_root_.SheafOfModules.free (R := (_root_.structureSheaf X.sheaf).over V)
          (ULift.{u} (Fin r))))) ∧
      Nonempty (DerivedCategory.Q.obj E ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  obtain ⟨V, hxV, P, hP, hiso⟩ := exists_strictlyPerfect_jShriek_model x F hX hsupp
  refine ⟨V, hxV, ((jShriek V (structureSheaf X.sheaf)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P, finite_not_isZero_jShriek V P hP, fun i => ?_, hiso⟩
  · have := isIso_jShriekAdjunction_unit_app V (P.X i)
    have h2 : _root_.IsDirectSummandOfFiniteFree
        (StrictlyPerfect.structureSheafOfRings
          (X.toRingedSpace.restrict V.isOpenEmbedding))
        ((jStar V (structureSheaf X.sheaf)).obj
          ((jShriek V (structureSheaf X.sheaf)).obj (P.X i))) :=
      _root_.IsDirectSummandOfFiniteFree.of_iso
        (StrictlyPerfect.structureSheafOfRings (X.toRingedSpace.restrict V.isOpenEmbedding))
        (asIso ((jShriekAdjunction V (structureSheaf X.sheaf)).unit.app (P.X i))).symm
        (((AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff
          (X.toRingedSpace.restrict V.isOpenEmbedding) P).1 hP).termDirectSummand i)
    have h3 := SheafOfModules.isDirectSummandOfFiniteFree_map
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward X.toRingedSpace V)
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackwardUnitIso
        X.toRingedSpace V).symm _ h2
    have h5 := _root_.IsDirectSummandOfFiniteFree.of_iso
      ((StrictlyPerfect.structureSheafOfRings X.toRingedSpace).over V)
      (((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModulesCompBackwardIso
        X.toRingedSpace V).app ((jShriek V (structureSheaf X.sheaf)).obj (P.X i))).symm) h3
    obtain ⟨r, j, q, hjq⟩ := (_root_.isDirectSummandOfFiniteFree_iff_free
      ((StrictlyPerfect.structureSheafOfRings X.toRingedSpace).over V) _).1 h5
    exact ⟨r, ⟨⟨j, q, hjq⟩⟩⟩

/-- The same complex, with the termwise condition in the open-subspace form: the restriction of
each term of `E` to the open subspace `V` is a direct summand of a finite free module, which is
the termwise condition of `StrictlyPerfect.IsStrictlyPerfect`. -/
theorem exists_boundedStrictModel_nearPoint_isDirectSummandOfFiniteFree (x : X) (F : X.Modules)
    [F.IsCoherent] (hX : IsRegular X) (hsupp : (SheafOfModules.supp F : Set X) ⊆ {x}) :
    ∃ (V : TopologicalSpace.Opens X) (_ : x ∈ V)
      (E : CochainComplex (Stacks.SheafOfModules.StructureSheafModules X.sheaf) ℤ),
      {i : ℤ | ¬ CategoryTheory.Limits.IsZero (E.X i)}.Finite ∧
      (∀ i : ℤ, StrictlyPerfect.IsDirectSummandOfFiniteFree
        (X := X.toRingedSpace.restrict V.isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace V).obj
          (E.X i))) ∧
      Nonempty (DerivedCategory.Q.obj E ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  obtain ⟨V, hxV, P, hP, hiso⟩ := exists_strictlyPerfect_jShriek_model x F hX hsupp
  refine ⟨V, hxV, ((jShriek V (structureSheaf X.sheaf)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P, finite_not_isZero_jShriek V P hP, fun i => ?_, hiso⟩
  · have := isIso_jShriekAdjunction_unit_app V (P.X i)
    exact StrictlyPerfect.isDirectSummandOfFiniteFree_of_iso
      (asIso ((jShriekAdjunction V (structureSheaf X.sheaf)).unit.app (P.X i))).symm
      (hP.directSummand i)

end Stacks.Cohomology.ExtensionByZeroStrictModel

end
