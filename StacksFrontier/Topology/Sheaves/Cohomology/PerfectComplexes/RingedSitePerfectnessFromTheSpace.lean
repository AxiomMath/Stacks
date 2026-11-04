module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite

/-!
# Perfectness on a ringed space is site-level perfectness

This is the converse of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite`, whose
module documentation describes the two notions and proves that the site one implies the space
one. Together the two files make the notions equivalent, so that the duality results of
[Stacks, Tag 08DQ] — all stated with site-level perfectness — apply under the ringed-space
hypothesis of the source.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_of_subspace`: a strictly perfect complex
  of modules on the open subspace `V` is strictly perfect on the slice of the site of opens
  over `V`. This is the inverse direction of
  `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_of_slice`.
* `Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`: an object of `D(O_X)`
  perfect in the sense of [Stacks, Tag 08CM] is perfect for the ringed site of opens of `X`,
  i.e. in the sense of [Stacks, Tag 08G5].

## Implementation notes

The hypothesis of [Stacks, Tag 08CM] supplies one open covering of the space; the conclusion of
[Stacks, Tag 08G5] asks for a covering of *every* object of the site. The two are reconciled not
by hand but by [Stacks, Tag 08G6] part (1),
`AlgebraicGeometry.RingedSite.isPerfect_of_coveringFamily_strictlyPerfect`, which takes a
covering of a terminal object — here the open `⊤` — and produces perfectness above every object.
That is why this direction needs no refinement of coverings, whereas the opposite direction
discards the hypotheses above the non-terminal objects.

The passage from the open subspace to the slice is the inverse of the equivalence
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict` used in the opposite
direction, and it carries the structure sheaf of the subspace to the structure sheaf of the
slice, so `SheafOfModules.isStrictlyPerfect_map` transports strict perfectness along it; the two
direct-summand predicates are again reconciled by their plain-retract characterisations. The
restriction functor of [Stacks, Tag 08CM],
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, is the composite of restriction
to the slice with that equivalence, so the quasi-isomorphism the hypothesis supplies becomes,
after applying the inverse equivalence degreewise and cancelling the unit of the equivalence, a
quasi-isomorphism onto the slice restriction.

All universes of the ringed space coincide, as they must for `StrictlyPerfect.OXMod` to be
stated; the universe of the derived category is left free.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.PerfectComplexes

universe u d

variable (X : RingedSpace.{u, u})

/-- The slice-to-subspace equivalence of the site of opens over an open. -/
local notation "sliceEquiv" =>
  AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict

/-- **The inverse of the slice-to-subspace equivalence carries the structure sheaf to the
structure sheaf.** This is `TopologicalSpace.Opens.sheafOfModulesEquivOverUnit` read backwards
through the unit of the equivalence. -/
def sliceEquivInverseUnitIso (V : Opens X.carrier) :
    (sliceEquiv X V).inverse.obj
        (SheafOfModules.unit (structureSheafOfRings (X.restrict V.isOpenEmbedding))) ≅
      SheafOfModules.unit ((structureSheafOfRings X).over V) :=
  (sliceEquiv X V).inverse.mapIso
      (V.sheafOfModulesEquivOverUnit (structureSheafOfRings X)).symm ≪≫
    ((sliceEquiv X V).unitIso.app
      (SheafOfModules.unit ((structureSheafOfRings X).over V))).symm

/-- **A strictly perfect complex on the open subspace `V` is strictly perfect on the slice over
`V`.** The inverse of the equivalence of the two models of `O_V`-modules carries the structure
sheaf to the structure sheaf, so it carries a direct summand of a finite free module to one; the
hypothesis is first rewritten from the ringed-space direct-summand predicate to the ringed-site
one through the plain-retract characterisation of each. This is the inverse direction of
`Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_of_slice`. -/
theorem isStrictlyPerfect_of_subspace (V : Opens X.carrier)
    (P : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect P) :
    _root_.IsStrictlyPerfect ((structureSheafOfRings X).over V)
      ((Functor.mapHomologicalComplex (sliceEquiv X V).inverse (ComplexShape.up ℤ)).obj P) := by
  have hP' : _root_.IsStrictlyPerfect
      (structureSheafOfRings (X.restrict V.isOpenEmbedding)) P := by
    refine ⟨hP.bounded, fun i => ?_⟩
    rw [_root_.isDirectSummandOfFiniteFree_iff_free]
    obtain ⟨n, ⟨⟨j, r, hjr⟩⟩⟩ :=
      (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract (P.X i)).1 (hP.directSummand i)
    refine ⟨n, j ≫ (StrictlyPerfect.finiteFreeIsoFree _ n).hom,
      (StrictlyPerfect.finiteFreeIsoFree _ n).inv ≫ r, ?_⟩
    rw [Category.assoc, ← Category.assoc (StrictlyPerfect.finiteFreeIsoFree _ n).hom,
      Iso.hom_inv_id, Category.id_comp, hjr]
  exact SheafOfModules.isStrictlyPerfect_map _ (sliceEquivInverseUnitIso X V) hP'

/-- The complex-level cancellation of the unit of the slice-to-subspace equivalence: restricting
a complex on the slice to the subspace and coming back is the complex itself. -/
def sliceEquivInverseFunctorComplexIso (V : Opens X.carrier)
    (Y : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over V)) ℤ) :
    (Functor.mapHomologicalComplex (sliceEquiv X V).inverse (ComplexShape.up ℤ)).obj
        ((Functor.mapHomologicalComplex (sliceEquiv X V).functor (ComplexShape.up ℤ)).obj Y) ≅
      Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((sliceEquiv X V).unitIso.app (Y.X i)).symm)
    (fun i j _ => ((sliceEquiv X V).unitIso.symm.hom.naturality (Y.d i j)).symm)

/-- The top open is a terminal object of the site of opens: a morphism of opens is an inequality,
and `U ≤ ⊤` always holds and holds in only one way. -/
def isTerminalTop : IsTerminal (⊤ : Opens X.carrier) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) fun _ _ => Subsingleton.elim _ _

section Site

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [hDer : ∀ V : Opens X.carrier,
    HasDerivedCategory.{d} (SheafOfModules.{u} ((structureSheafOfRings X).over V))]

/-- `HasDerivedCategory` at the spelling the ringed-site statements use, as in
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite`. -/
local instance hasDerivedCategoryRingedSiteModules' :
    HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSpace.ringedSite X).O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u, u} X))

/-- `HasDerivedCategory` on the slices, at the spelling the ringed-site statements use. -/
local instance hasDerivedCategoryRingedSiteSliceModules
    (V : (AlgebraicGeometry.RingedSpace.ringedSite X).C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (AlgebraicGeometry.RingedSpace.ringedSite X).O).over V)) :=
  hDer V

/-- **Stacks 08CM implies Stacks 08G5 at the site of opens.** An object of `D(O_X)` which is
perfect as an object of the derived category of the ringed space `X` is perfect for the ringed
site of opens of `X`.

The covering of `⊤` required by [Stacks, Tag 08G6] part (1) is the covering of the space that
[Stacks, Tag 08CM] supplies, read as a presieve of `⊤`; the strictly perfect model over a member
is the model on the open subspace carried to the slice by `isStrictlyPerfect_of_subspace`, and
the quasi-isomorphism of the hypothesis becomes a quasi-isomorphism onto the slice restriction
after the unit of the equivalence is cancelled.

Together with `Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite`, which is the
opposite implication, this makes the two notions of perfectness equivalent. -/
theorem isPerfect_ringedSite_of_isPerfect (K : DerivedCategory (OXMod.{u, u} X))
    (h : IsPerfect K) :
    (AlgebraicGeometry.RingedSpace.ringedSite X).IsPerfect K := by
  classical
  obtain ⟨E, ⟨I, U, hU, hdata⟩, ⟨eEK⟩⟩ := h
  refine AlgebraicGeometry.RingedSite.isPerfect_of_coveringFamily_strictlyPerfect
    (AlgebraicGeometry.RingedSpace.ringedSite X) ⊤ (isTerminalTop X) K
    ⟨fun V _ => ∃ i, U i = V, ?_, ?_⟩
  · refine (Opens.mem_grothendieckTopology X.carrier).2 fun x _ => ?_
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU ▸ Set.mem_univ x : x ∈ iSup U)
    exact ⟨U i, homOfLE le_top, ⟨U i, 𝟙 _, homOfLE le_top, ⟨i, rfl⟩, by simp⟩, hxi⟩
  · rintro V f ⟨i, rfl⟩
    obtain ⟨P, hP, q, hq⟩ := hdata i
    have := hq
    refine ⟨_, isStrictlyPerfect_of_subspace X (U i) P hP, ?_⟩
    have hq' : QuasiIso
        ((Functor.mapHomologicalComplex (sliceEquiv X (U i)).inverse
          (ComplexShape.up ℤ)).map q) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology q (sliceEquiv X (U i)).inverse
    have hiso : IsIso (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplex (sliceEquiv X (U i)).inverse
          (ComplexShape.up ℤ)).map q)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq'
    exact ⟨@asIso _ _ _ _ _ hiso ≪≫
      DerivedCategory.Q.mapIso (sliceEquivInverseFunctorComplexIso X (U i)
        ((Functor.mapHomologicalComplex
          (SheafOfModules.overFunctor (structureSheafOfRings X) (U i))
          (ComplexShape.up ℤ)).obj E)) ≪≫
      ((SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSpace.ringedSite X).O)
          (U i)).mapDerivedCategoryFactors.app E).symm ≪≫
      (SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSpace.ringedSite X).O)
          (U i)).mapDerivedCategory.mapIso eEK⟩

end Site

end Stacks.Cohomology.PerfectComplexes

end
