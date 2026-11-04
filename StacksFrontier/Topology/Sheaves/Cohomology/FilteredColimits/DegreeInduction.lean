module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.ModuleCohomologyDeltaFunctor

/-!
# Cohomology over a quasi-compact open and filtered colimits: the induction

Stacks 01FF asserts that on a ringed space with a basis of quasi-compact opens whose binary
intersections are quasi-compact, the canonical map
`colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism for every quasi-compact open `U`, every
filtered system of `O_X`-modules and every degree `q`.  Its proof is an induction on `q` whose
inductive step is the long exact cohomology sequence of a short exact sequence of systems
obtained from a functorial injective embedding, and whose two external inputs are

* the degree-zero statement, `colimᵢ Γ(V, Fᵢ) = Γ(V, colimᵢ Fᵢ)` for quasi-compact `V`
  (Stacks 009F, whose hypothesis is supplied by Stacks 0069), and
* the vanishing `Hⁿ⁺¹(V, colimᵢ Iᵢ) = 0` for a system of injectives, which Stacks obtains from
  Stacks 01EW (Čech vanishing on a basis forces cohomology vanishing) together with Stacks 01EP
  (the Čech complex of an injective is acyclic in positive degrees).

The induction is carried out, for an arbitrary cohomological δ-functor, in
`StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit`; in particular the functorial
injective embedding of a *system* that Stacks takes from Stacks 01DI is proved there for any
Grothendieck abelian category.  This file plugs the δ-functor
`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor` of `StacksDraft.Ch20.Sec18.Tag01FF` into
that engine, so that Stacks 01FF is reduced to exactly the two statements above.

## Main results

* `Stacks.Cohomology.Colimit.isIso_colimit_post_Hfunctor_of_degreeZero_of_isZero`: Stacks 01FF
  for a fixed open `U`, conditional on the degree-zero comparison over `U` for every system and
  on the vanishing of `Hⁿ⁺¹(U, -)` on the colimit of every system of injectives.  Nothing about
  quasi-compactness enters here: quasi-compactness of `U` and the two hypotheses of Stacks 01FF
  on `X` are exactly what is needed to supply those two inputs, and nothing else.
* `Stacks.Cohomology.Colimit.isIso_colimit_post_Hfunctor_of_preservesColimitsOfShape`: the same,
  with the degree-zero input replaced by the statement that the sections functor `Γ(U, -)`
  preserves `I`-colimits, which is literally Stacks 009F for sheaves of modules.

## Implementation notes

The hypothesis `PreservesColimitsOfShape I (secF R U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u})`
carries its ascription because the module universe of `SheafOfModules R` is implicit in `secF`:
written as `PreservesColimitsOfShape I (secF R U)` the elaborator invents a fresh universe for
it, and the instance then does not apply to systems of `SheafOfModules.{u} R`.

The hypotheses are stated for a *fixed* `U`, not for all quasi-compact opens at once, which is
possible because the vanishing input is taken as a hypothesis: in the source, the induction runs
over all quasi-compact opens simultaneously only because the vanishing claim is proved inside
the induction from the degree-zero statement on the multiple intersections of a covering.

The universes are all equal.  This is not a convenience: `cohomologyDeltaFunctor` is built from
`Ext` on `SheafOfModules R`, so it needs the `AddCommGrpCat` universe to agree with the
hom-universe `max u w` of `SheafOfModules.{w} R` over a space with underlying type in `Type u`;
and Mathlib's `IsGrothendieckAbelian` instance for `SheafOfModules` likewise pins the module
universe to the universe of the site.  The three-universe form in which Stacks 01FF is stated in
the source is therefore out of reach of both the long exact sequence and of Stacks 01EW as
they currently stand.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleDelta

universe u

namespace Stacks.Cohomology.Colimit

/-- **Stacks 01FF, modulo its two external inputs.** Let `X` be a ringed space, `U` an open of
`X` and `I` a filtered index category.  Assume

* `h0`: the canonical map `colimᵢ Γ(U, Gᵢ) ⟶ Γ(U, colimᵢ Gᵢ)` is an isomorphism for every system
  `G : I ⥤ Mod(O_X)` — this is Stacks 009F, available when `U` is quasi-compact and `X` has a
  basis of quasi-compact opens closed under binary intersection; and
* `hvan`: `Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0` for every system `E` of injective `O_X`-modules — this is the
  claim that Stacks proves from Stacks 01EW and Stacks 01EP.

Then the canonical map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism in every degree.

The proof is the induction of Stacks 01FF, performed for an arbitrary δ-functor in
`CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`; the long exact sequence it
consumes is `cohomologyDeltaFunctor`, whose degree-`n` component *is* `Hfunctor R U n`.  The
third input of the engine, that `Hⁿ⁺¹(U, -)` kills injectives, is automatic: `Hⁿ⁺¹(U, -)` is a
right derived functor. -/
theorem isIso_colimit_post_Hfunctor_of_degreeZero_of_isZero
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (U : Opens X)
    (h0 : ∀ G : I ⥤ SheafOfModules.{u} R, IsIso (colimit.post G (Hfunctor R U 0)))
    (hvan : ∀ E : I ⥤ SheafOfModules.{u} R, (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero ((Hfunctor R U (n + 1)).obj (colimit E)))
    (F : I ⥤ SheafOfModules.{u} R) (q : ℕ) :
    IsIso (colimit.post F (Hfunctor R U q)) :=
  DeltaFunctor.isIso_colimit_post_of_isIso_zero (cohomologyDeltaFunctor R U) h0
    (fun Y hY n => have := hY; (secF R U).isZero_rightDerived_obj_injective_succ n Y) hvan q F

/-- **Stacks 01FF, with its degree-zero input phrased on the sections functor.**  If the
sections functor `Γ(U, -) : Mod(O_X) ⥤ Ab` preserves `I`-colimits — which is the content of
Stacks 009F for a quasi-compact `U` on a space satisfying the two hypotheses of Stacks 01FF —
and if `Hⁿ⁺¹(U, -)` kills the colimit of every system of injectives, then
`colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism in every degree.

The degree-zero hypothesis of
`isIso_colimit_post_Hfunctor_of_degreeZero_of_isZero` is discharged from this one because
`H⁰(U, -)` is isomorphic to `Γ(U, -)`: the sections functor is left exact, so
`Functor.rightDerivedZeroIsoSelf` applies, and whether the comparison morphism is an isomorphism
only depends on the isomorphism class of the functor. -/
theorem isIso_colimit_post_Hfunctor_of_preservesColimitsOfShape
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (U : Opens X)
    [PreservesColimitsOfShape I (secF R U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u})]
    (hvan : ∀ E : I ⥤ SheafOfModules.{u} R, (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero ((Hfunctor R U (n + 1)).obj (colimit E)))
    (F : I ⥤ SheafOfModules.{u} R) (q : ℕ) :
    IsIso (colimit.post F (Hfunctor R U q)) :=
  isIso_colimit_post_Hfunctor_of_degreeZero_of_isZero R U
    (fun G =>
      have : PreservesColimit G (secF R U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) :=
        PreservesColimitsOfShape.preservesColimit
      isIso_colimit_post_of_natIso G (secF R U).rightDerivedZeroIsoSelf) hvan F q

end Stacks.Cohomology.Colimit

end
