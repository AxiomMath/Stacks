module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalNullHomotopyOverSlices

/-!
# Site-level perfectness on a ringed space is perfectness

A ringed space carries two notions of a perfect complex, and the library has had no comparison
between them:

* **Stacks 08CM**, `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex`: one open covering of
  the space, with a strictly perfect model of the restriction of the complex to each member,
  the member being read as an open *subspace*;
* **Stacks 08G5**, `AlgebraicGeometry.RingedSite.IsPerfectComplex`, read at
  `AlgebraicGeometry.RingedSpace.ringedSite`: for *every* open `U`, a covering presieve of `U`
  with a strictly perfect model of the restriction of the complex to each member, the member
  being read as a *slice* of the site of opens.

This file proves that the second implies the first, so that the duality results — which are all
stated at the site spelling — can be fed to the Tor-amplitude results, which are all stated at
the subspace spelling.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isPerfectComplex_of_ringedSite` and
  `Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite`: a complex, resp. an object of
  `D(O_X)`, perfect for the site of opens of `X` is perfect for `X`.
* `Stacks.Cohomology.PerfectComplexes.isStrictlyPerfect_of_slice`: a strictly perfect complex of
  modules on the slice of the site of opens over `V` is strictly perfect on the open subspace
  `V`.

## Implementation notes

The covering is extracted from the site hypothesis at the single object `⊤`: the sieve generated
by the chosen presieve covers `⊤`, so the sources of the arrows of the presieve cover the space,
and the covering of Stacks 08CM is indexed by the opens admitting such an arrow. Only the
hypothesis at `⊤` is used; the hypotheses at the other objects are discarded, which is why the
implication goes this way and not the other.

The slice-to-subspace passage is Mathlib's equivalence
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, available in this library as
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`, whose target is
already retyped at the `StrictlyPerfect.OXMod` spelling. It carries the structure sheaf of the
slice to the structure sheaf of the subspace
(`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit`), so
`SheafOfModules.isStrictlyPerfect_map` transports strict perfectness along it; what that lemma
produces is the *site* direct-summand predicate on the subspace, and the plain-retract
characterisations of the two predicates
(`Stacks.SheafOfModules.isDirectSummandOfFiniteFree_iff_free` and
`StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract`, both available because the module and
ring universes agree here) convert it to the subspace one, with
`StrictlyPerfect.finiteFreeIsoFree` identifying `O^{⊕n}` with the free module on `ULift (Fin n)`.

The complex that the conclusion's model maps into is taken as a **variable** `R` together with
an equation, and the equation is discharged by `rfl` at the call site. The three definitional
identities involved — the two spellings of the structure sheaf of rings, the slice restriction
of a complex, and the composite of the slice restriction with the equivalence against
`AlgebraicGeometry.RingedSpace.restrictModules` — each check instantly on their own, but the
unifier does not find them inside the existential statement of Stacks 08CM, whose `QuasiIso`
carries `HasHomology` instance arguments depending on the complex being converted: elaborating
the application directly exhausts the default heartbeat budget, and `rw` cannot be used because
rewriting the complex leaves those instance arguments behind and the motive is not type correct.

All universes of the ringed space coincide, as they must for `StrictlyPerfect.OXMod` to be
stated; the derived category of `X` is left arbitrary.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.PerfectComplexes

universe u d

variable (X : RingedSpace.{u, u})

/-- `HasDerivedCategory` at the spelling the ringed-site statements use. The type is
`StrictlyPerfect.OXMod X` by `rfl`, but an instance proved at one spelling does not fire at the
other, and the two spellings must carry the *same* instance for the two `DerivedCategory`s to be
the same type. -/
local instance hasDerivedCategoryRingedSiteModules [HasDerivedCategory.{d} (OXMod.{u, u} X)] :
    HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSpace.ringedSite X).O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u, u} X))

/-- The slice-to-subspace equivalence is additive: it is the identity on the underlying maps of
sheaves. Re-seated at the
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict` spelling, at which
the library instance does not fire. -/
instance sheafOfModulesEquivRestrict_functor_additive (V : Opens X.carrier) :
    (RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X V).functor.Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- The slice-to-subspace equivalence preserves homology, being half of an equivalence. -/
instance sheafOfModulesEquivRestrict_functor_preservesHomology (V : Opens X.carrier) :
    (RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X V).functor.PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **A strictly perfect complex on the slice over `V` is strictly perfect on the open subspace
`V`.** The equivalence of the two models of `O_V`-modules carries the structure sheaf to the
structure sheaf, so it carries a direct summand of a finite free module to one; the conclusion
is then rewritten from the ringed-site direct-summand predicate to the ringed-space one through
the plain-retract characterisation of each. -/
theorem isStrictlyPerfect_of_slice (V : Opens X.carrier)
    (P : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over V)) ℤ)
    (hP : _root_.IsStrictlyPerfect ((structureSheafOfRings X).over V) P) :
    StrictlyPerfect.IsStrictlyPerfect
      ((Functor.mapHomologicalComplex
        (RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X V).functor
        (ComplexShape.up ℤ)).obj P) := by
  have h := SheafOfModules.isStrictlyPerfect_map
    (RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X V).functor
    (V.sheafOfModulesEquivOverUnit (structureSheafOfRings X)) hP
  refine ⟨h.bounded, fun i => ?_⟩
  rw [StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract]
  obtain ⟨n, j, r, hjr⟩ :=
    (_root_.isDirectSummandOfFiniteFree_iff_free _ _).1 (h.termDirectSummand i)
  refine ⟨n, ⟨⟨j ≫ (StrictlyPerfect.finiteFreeIsoFree _ n).inv,
    (StrictlyPerfect.finiteFreeIsoFree _ n).hom ≫ r, ?_⟩⟩⟩
  rw [Category.assoc, ← Category.assoc (StrictlyPerfect.finiteFreeIsoFree _ n).inv,
    Iso.inv_hom_id, Category.id_comp, hjr]

/-- **A strictly perfect model of a restriction to a slice is a strictly perfect model of the
restriction to the open subspace.** The target complex is a variable with an equation, which the
consumer discharges by `rfl`; see the implementation notes. -/
theorem exists_subspace_model (V : Opens X.carrier)
    (E : CochainComplex (OXMod.{u, u} X) ℤ)
    (R : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ)
    (hR : R = (Functor.mapHomologicalComplex
      (RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict X V).functor
      (ComplexShape.up ℤ)).obj ((Functor.mapHomologicalComplex
        (SheafOfModules.overFunctor (structureSheafOfRings X) V) (ComplexShape.up ℤ)).obj E))
    (P : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over V)) ℤ)
    (hP : _root_.IsStrictlyPerfect ((structureSheafOfRings X).over V) P)
    (q : P ⟶ (Functor.mapHomologicalComplex
      (SheafOfModules.overFunctor (structureSheafOfRings X) V) (ComplexShape.up ℤ)).obj E)
    (hq : QuasiIso q) :
    ∃ Q : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ,
      StrictlyPerfect.IsStrictlyPerfect Q ∧ ∃ g : Q ⟶ R, QuasiIso g := by
  subst hR
  have := hq
  exact ⟨_, isStrictlyPerfect_of_slice X V P hP, _,
    HomologicalComplex.quasiIso_map_of_preservesHomology q _⟩

/-- **Stacks 08G5 at the site of opens implies Stacks 08CM.** A complex of `O_X`-modules which is
perfect as a complex on the ringed site of opens of `X` is perfect as a complex on the ringed
space `X`.

The covering of Stacks 08CM is indexed by the opens admitting an arrow into `⊤` in the presieve
the site hypothesis supplies at `⊤`; those opens cover the space because the sieve generated by
the presieve is a covering sieve of `⊤`, and an arrow of the generated sieve factors through a
member of the presieve. -/
theorem isPerfectComplex_of_ringedSite (E : CochainComplex (OXMod.{u, u} X) ℤ)
    (h : (AlgebraicGeometry.RingedSpace.ringedSite X).IsPerfectComplex E) :
    IsPerfectComplex E := by
  classical
  obtain ⟨S, hS, hdata⟩ := h ⊤
  refine ⟨{V : Opens X.carrier // ∃ f : V ⟶ (⊤ : Opens X.carrier), S f}, Subtype.val, ?_, ?_⟩
  · refine le_antisymm le_top fun x _ => ?_
    obtain ⟨V, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology X.carrier).1 hS x trivial
    obtain ⟨Z, g, hmor, hSmor, -⟩ := hf
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨Z, ⟨hmor, hSmor⟩⟩, leOfHom g hxV⟩
  · rintro ⟨V, ⟨f, hf⟩⟩
    obtain ⟨P, hP, q, hq⟩ := hdata f hf
    exact exists_subspace_model X V E _ rfl P hP q hq

/-- **Stacks 08G5 at the site of opens implies Stacks 08CM, for an object of the derived
category.** Perfectness of either flavour is the existence of a perfect complex representative,
so this is `Stacks.Cohomology.PerfectComplexes.isPerfectComplex_of_ringedSite` applied to the
representative the site hypothesis supplies. -/
theorem isPerfect_of_ringedSite [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X))
    (h : (AlgebraicGeometry.RingedSpace.ringedSite X).IsPerfect K) :
    IsPerfect K := by
  obtain ⟨E, hE, hEK⟩ := h
  exact ⟨E, isPerfectComplex_of_ringedSite X E hE, hEK⟩

end Stacks.Cohomology.PerfectComplexes

end
