module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy

/-!
# The ringed-site and ringed-space strict perfectness of Stacks 08FL agree

Stacks 08FL has a version for a sheaf of modules on a ringed site, `IsStrictlyPerfect`, and a
version for an `𝒪_X`-module on a ringed space, `StrictlyPerfect.IsStrictlyPerfect`. On a ringed
space the two are equivalent: the boundedness clauses coincide, and the finite free modules of the
termwise clauses, `SheafOfModules.free (ULift (Fin n))` on the site side and
`StrictlyPerfect.finiteFree X n` on the space side, are isomorphic.

Strict perfectness also crosses the equivalence between modules on the slice site over an open
`U` and modules on the open subspace `U`. Consequently pseudo-coherence (Stacks 08FT) on the
small Zariski ringed site of a scheme is pseudo-coherence (Stacks 08CB) on its underlying ringed
space.

## Main results

* `StrictlyPerfect.isDirectSummandOfFiniteFree_iff_site`: the two "direct summand of a finite
  free module" predicates agree.
* `StrictlyPerfect.isStrictlyPerfect_iff_site`: the two strict perfectness predicates agree.
* `AlgebraicGeometry.Scheme.isStrictlyPerfect_zariskiRingedSite_iff`: the same for a scheme, with
  the site side read at `AlgebraicGeometry.Scheme.zariskiRingedSite`.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_equivRestrict_functor` and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_equivRestrict_inverse`: strict
  perfectness crosses the equivalence between modules on the slice site over an open and modules
  on the open subspace, in both directions.
* `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff`: pseudo-coherence on the
  small Zariski ringed site of a scheme is pseudo-coherence on its underlying ringed space.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u d

namespace StrictlyPerfect

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  [HasWeakSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

omit [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The two "direct summand of a finite free module" predicates of Stacks 08FL agree** on a
ringed space. -/
public theorem isDirectSummandOfFiniteFree_iff_site (E : OXMod.{u, u} X) :
    _root_.IsDirectSummandOfFiniteFree (structureSheafOfRings X) E ↔
      StrictlyPerfect.IsDirectSummandOfFiniteFree E :=
  (AlgebraicGeometry.RingedSpace.PseudoCoherence.isDirectSummandOfFiniteFree_iff X E).symm

omit [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The ringed-site and ringed-space strict perfectness of Stacks 08FL agree** on a ringed
space. -/
public theorem isStrictlyPerfect_iff_site (E : CochainComplex (OXMod.{u, u} X) ℤ) :
    _root_.IsStrictlyPerfect (structureSheafOfRings X) E ↔
      StrictlyPerfect.IsStrictlyPerfect E :=
  (AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff X E).symm

end StrictlyPerfect

namespace AlgebraicGeometry.Scheme

/-- **Strict perfectness on the small Zariski ringed site of a scheme is strict perfectness on
its underlying ringed space.** -/
public theorem isStrictlyPerfect_zariskiRingedSite_iff (S : Scheme.{u})
    (E : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ℤ) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) E ↔
      StrictlyPerfect.IsStrictlyPerfect (X := S.toRingedSpace) E :=
  StrictlyPerfect.isStrictlyPerfect_iff_site S.toRingedSpace E

end AlgebraicGeometry.Scheme

/-! ### Crossing the slice equivalence -/

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **Strict perfectness crosses the slice equivalence.** A strictly perfect complex of modules on
the slice site over `U` becomes a strictly perfect complex of `𝒪`-modules on the open subspace
`U`. -/
public theorem isStrictlyPerfect_equivRestrict_functor
    {P : CochainComplex
      (SheafOfModules.{u} ((_root_.StrictlyPerfect.structureSheafOfRings X).over U)) ℤ}
    (hP : _root_.IsStrictlyPerfect
      ((_root_.StrictlyPerfect.structureSheafOfRings X).over U) P) :
    _root_.StrictlyPerfect.IsStrictlyPerfect
      (((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  (_root_.StrictlyPerfect.isStrictlyPerfect_iff_site (X.restrict U.isOpenEmbedding) _).mp
    (SheafOfModules.isStrictlyPerfect_map (sheafOfModulesEquivRestrict.{u} X U).functor
      (U.sheafOfModulesEquivOverUnit (_root_.StrictlyPerfect.structureSheafOfRings X)) hP)

/-- **Strict perfectness crosses the slice equivalence backwards.** A strictly perfect complex of
`𝒪`-modules on the open subspace `U` becomes a strictly perfect complex of modules on the slice
site over `U`. -/
public theorem isStrictlyPerfect_equivRestrict_inverse
    {Q : CochainComplex
      (_root_.StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hQ : _root_.StrictlyPerfect.IsStrictlyPerfect Q) :
    _root_.IsStrictlyPerfect ((_root_.StrictlyPerfect.structureSheafOfRings X).over U)
      (((sheafOfModulesEquivRestrict.{u} X U).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) :=
  SheafOfModules.isStrictlyPerfect_map (sheafOfModulesEquivRestrict.{u} X U).inverse
    (U.sheafOfModulesEquivOverInverseUnit (_root_.StrictlyPerfect.structureSheafOfRings X))
    ((_root_.StrictlyPerfect.isStrictlyPerfect_iff_site
      (X.restrict U.isOpenEmbedding) Q).mpr hQ)

/-- **The slice restriction of a complex, pushed across the equivalence, is its restriction to
the open subspace.** -/
public theorem mapHomologicalComplex_equivRestrict_overFunctor
    (K : CochainComplex (_root_.StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    ((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((SheafOfModules.overFunctor.{u}
        (_root_.StrictlyPerfect.structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) =
      restrictComplex K U :=
  rfl

/-- **The local approximation datum of Stacks 08FT crosses the slice equivalence.** A strictly
perfect approximation of `K` over the slice site at `U` becomes one over the open subspace `U`. -/
public theorem exists_restrict_approximation_of_slice
    (K : CochainComplex (_root_.StrictlyPerfect.OXMod.{u, u} X) ℤ) (m : ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} ((_root_.StrictlyPerfect.structureSheafOfRings X).over U)) ℤ)
    (hP : _root_.IsStrictlyPerfect
      ((_root_.StrictlyPerfect.structureSheafOfRings X).over U) P)
    (α : P ⟶ ((SheafOfModules.overFunctor.{u}
      (_root_.StrictlyPerfect.structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P' : CochainComplex
        (_root_.StrictlyPerfect.OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      _root_.StrictlyPerfect.IsStrictlyPerfect P' ∧
      ∃ α' : P' ⟶ restrictComplex K U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
        Epi (HomologicalComplex.homologyMap α' m) := by
  refine ⟨((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P, isStrictlyPerfect_equivRestrict_functor X U hP, ?_⟩
  rw [← mapHomologicalComplex_equivRestrict_overFunctor X U K]
  exact ⟨((sheafOfModulesEquivRestrict.{u} X U).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map α,
    fun j hj => AlgebraicGeometry.RingedSpace.isIso_homologyMap_map _ α j (hiso j hj),
    AlgebraicGeometry.RingedSpace.epi_homologyMap_map _ α m hepi⟩

end AlgebraicGeometry.RingedSpace.PseudoCoherence

/-! ### Pseudo-coherence on the small Zariski site is pseudo-coherence on the space -/

namespace AlgebraicGeometry.Scheme

/-- **Stacks 08FT (1) at the small Zariski ringed site of a scheme implies Stacks 08CB (1) on
its underlying ringed space.** -/
public theorem isPseudoCoherentComplexFrom_toRingedSpace_of_zariskiRingedSite (S : Scheme.{u})
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ℤ) (m : ℤ)
    (h : S.zariskiRingedSite.IsPseudoCoherentComplexFrom K m) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
      (X := S.toRingedSpace) K m := by
  intro x
  obtain ⟨T, hT, hdata⟩ := h ⊤
  obtain ⟨V, i, ⟨W, g, f, hf, -⟩, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hT x trivial
  obtain ⟨P, hP, α, hiso, hepi⟩ := hdata f hf
  exact ⟨W, leOfHom g hxV,
    AlgebraicGeometry.RingedSpace.PseudoCoherence.exists_restrict_approximation_of_slice
      S.toRingedSpace W K m P hP α hiso hepi⟩

/-- The derived category of the `𝒪`-modules on the underlying ringed space of a scheme `S`,
given by that of the `𝒪_S`-modules on its small Zariski ringed site. -/
local instance hasDerivedCategoryToRingedSpace (S : Scheme.{u})
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))] :
    HasDerivedCategory.{d} (_root_.StrictlyPerfect.OXMod.{u, u} S.toRingedSpace) :=
  inferInstanceAs (HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))

/-- **Stacks 08FT (3) at the small Zariski ringed site of a scheme implies Stacks 08CB (3) on
its underlying ringed space.** -/
public theorem isPseudoCoherentFrom_toRingedSpace_of_zariskiRingedSite (S : Scheme.{u})
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) (m : ℤ)
    (h : S.zariskiRingedSite.IsPseudoCoherentFrom E m) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom
      (X := S.toRingedSpace) E m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_toRingedSpace_of_zariskiRingedSite S K m hK, ⟨e⟩⟩

/-- **Pseudo-coherence on the small Zariski ringed site of a scheme is pseudo-coherence on its
underlying ringed space.** Stacks 08FT (3) at `AlgebraicGeometry.Scheme.zariskiRingedSite` and
Stacks 08CB (3) at `AlgebraicGeometry.Scheme.toRingedSpace` are the same condition. -/
public theorem isPseudoCoherentFrom_zariskiRingedSite_iff (S : Scheme.{u})
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) (m : ℤ) :
    S.zariskiRingedSite.IsPseudoCoherentFrom E m ↔
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom
        (X := S.toRingedSpace) E m :=
  ⟨isPseudoCoherentFrom_toRingedSpace_of_zariskiRingedSite S E m,
    AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite
      S.toRingedSpace E m⟩

end AlgebraicGeometry.Scheme

end
