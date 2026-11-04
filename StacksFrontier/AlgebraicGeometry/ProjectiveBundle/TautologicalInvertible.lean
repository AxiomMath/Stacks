module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalBaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf

/-!
# The tautological datum of the projective bundle of an invertible module

A tautological datum on `𝐏(F)`, `Stacks.RelativeProj.TautologicalDatum`, is an invertible module
on `𝐏(F)` together with a surjection onto it from `π^*F`. When `F` is itself invertible, `π^*F`
*is* such a module: the pullback of an invertible module is invertible
(`Stacks.Modules.isInvertible_pullback`, unconditional), and the identity is a surjection onto
it. That datum is `Stacks.RelativeProj.TautologicalDatum.ofInvertible`, and specialising `F` to
the structure sheaf gives `Stacks.RelativeProj.tautologicalDatumUnit`, a datum on every scheme
with no hypothesis at all.

Two consequences of having one, both about the base-change clause of Tag 0B3V. First, the datum
obtained by pulling `ofInvertible` back along the comparison morphism `b : 𝐏(F') ⟶ 𝐏(F)` **is**
`𝐏(F')`'s own `ofInvertible`, identified by the canonical
`Stacks.RelativeProj.tautologicalBaseChangeIso`. Second, Tag 0B3V's clause therefore holds with
*both* tautological data canonical rather than with one of them pulled back or existentially
quantified.

## Main definitions

* `Stacks.RelativeProj.TautologicalDatum.ofInvertible`: the tautological datum `π^*F` on `𝐏(F)`
  of an invertible quasi-coherent `F`, with the identity as its universal surjection.
* `Stacks.RelativeProj.tautologicalDatumUnit`: that datum at the structure sheaf, so a datum on
  the projective bundle of `𝒪_X` for every scheme `X`.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.baseChange_ofInvertible_univ`: the universal surjection
  of the base change of `ofInvertible` is the inverse of the canonical identification — in
  particular it carries no information beyond that identification.
* `Stacks.RelativeProj.TautologicalDatum.baseChange_ofInvertible_univ_comp_iso_hom`: **the base
  change of the canonical datum is the canonical datum**, in the precise sense the transport
  lemma `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_of_iso` consumes.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_ofInvertible`: **Tag 0B3V's
  clause on the universal quotient of the base-change comparison, with both tautological data
  canonical.** Nothing is assumed beyond invertibility of the two modules.
* `Stacks.RelativeProj.projectiveBundleBaseChange_tautological_unit`: that clause at the
  structure sheaves of an arbitrary morphism of schemes, with no hypothesis on the morphism.

## Implementation notes

**What this does and does not settle about inhabitation.** For an invertible `F` the projective
bundle is the base itself and `𝒪(1)` is `π^*F`, which the unconditional pullback-invertibility
result already supplies, so the rank-one datum below needs no twist. Nothing in this file
exercises a non-trivial twist.

The rank `≥ 2` case is **inhabited**: `Stacks.RelativeProj.tautologicalDatum` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumExists.lean` is a datum for an
arbitrary quasi-coherent `F`, obtained by transporting the twist and tautological
surjection of `Stacks.ProjectiveBundleSplitting` along
`AlgebraicGeometry.projectiveBundlePresentationsAgree`. What this file adds over the general
datum is that for an invertible `F` the datum is canonical on the nose rather than up to the
choice of that comparison, which is what the base-change clauses below are stated at.

**`Stacks.RelativeProj.TautologicalDatum.IsUniversal` is a separate gap and is untouched here.**
`isUniversal_of_equiv` takes the bijection of Tag 0B3V as its input, so it inhabits nothing, and
nothing in this file reaches the declarations quantified over `IsUniversal`.
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Universal.lean` inhabits it over a scheme
with no points, and shows that for the canonical datum of this file `IsUniversal` is equivalent
to every invertible quotient of the module being an isomorphism together with the projection
having exactly one section.

**The invertibility hypothesis is an explicit argument, not an instance binder.** The class is
recorded in `TautologicalDatum` at the `X.presheaf` / `X.ringCatSheaf.2` spelling, while the
instance for the structure sheaf,
`AlgebraicGeometry.Scheme.Modules.isInvertible_unit`, concludes at the
`X.toRingedSpace.presheaf` / `structureSheafRing
  X.toRingedSpace` spelling.
Instance search does not cross that gap (`synthInstanceFailed`), while the *term* is
accepted against the declared type. An explicit argument is what lets a caller pass it.

**Why the two base-change statements are separate declarations.** The universal surjection of
the base change is `(tautologicalBaseChangeIso).inv ≫ b^*(𝟙)`, and reducing `b^*(𝟙)` to `𝟙`
inside a composite leaves a goal that is not type-correct at `implicit` transparency —
`(ofInvertible X F hF).twist` and `(Scheme.Modules.pullback π).obj F` are equal only by
unfolding the structure instance, the wall `TautologicalBaseChange.lean` records at three sites.
Both statements are therefore proved in term mode, the first with the functoriality step bound
to a declared type.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

/-- **The tautological datum of the projective bundle of an invertible module**: its twist is
`π^*F`, invertible because pullback preserves invertibility, and its universal surjection is the
identity. For invertible `F` the bundle `𝐏(F)` is the base and `𝒪(1)` is `π^*F`, so this is the
tautological datum rather than a degenerate choice; the identification of `𝐏(F)` with the base
is not formalised here and is not needed. -/
def TautologicalDatum.ofInvertible (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    TautologicalDatum X F where
  twist := (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F
  invertible :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@Stacks.Modules.isInvertible_pullback _ _ (projectiveBundleToBase X F) F
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hF))
  univ := 𝟙 _
  epi_univ := inferInstance

/-- The twist of `TautologicalDatum.ofInvertible X F hF` is the pullback `π^*F` of `F` along the
projection `projectiveBundleToBase X F`. -/
@[simp] theorem TautologicalDatum.ofInvertible_twist (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    (TautologicalDatum.ofInvertible X F hF).twist =
      (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F :=
  rfl

/-- The universal surjection of `TautologicalDatum.ofInvertible X F hF` is the identity of
`π^*F`. -/
@[simp] theorem TautologicalDatum.ofInvertible_univ (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    (TautologicalDatum.ofInvertible X F hF).univ = 𝟙 _ :=
  rfl

/-- **A tautological datum on the projective bundle of the structure sheaf of any scheme**, with
no hypothesis. The structure sheaf is invertible (Tag 01CT) and quasi-coherent. -/
def tautologicalDatumUnit (X : Scheme.{u}) :
    TautologicalDatum X (SheafOfModules.unit X.ringCatSheaf) :=
  TautologicalDatum.ofInvertible X _ (AlgebraicGeometry.Scheme.Modules.isInvertible_unit X)

section BaseChange

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (hEY : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 E)
  (hEX : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E')

/-- **The universal surjection of the base change of the canonical datum is the inverse of the
canonical identification** `b^*π^*E ≅ π'^*E'`. Its universal surjection being the identity,
pulling it back along `b` leaves only that identification. -/
theorem TautologicalDatum.baseChange_ofInvertible_univ :
    ((TautologicalDatum.ofInvertible Y E hEY).baseChange g E E' hE).univ =
      (tautologicalBaseChangeIso g E E' hE).inv := by
  have h : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
      ((TautologicalDatum.ofInvertible Y E hEY).univ) =
      𝟙 ((Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        (TautologicalDatum.ofInvertible Y E hEY).twist) :=
    CategoryTheory.Functor.map_id _ _
  exact Eq.trans
    (congrArg (fun m => (tautologicalBaseChangeIso g E E' hE).inv ≫ m) h)
    (Category.comp_id _)

/-- **The base change of the canonical tautological datum is the canonical tautological datum**,
in the form the transport lemma `projectiveBundleBaseChange_tautological_of_iso` consumes: the
canonical identification of twists carries the universal surjection of the base change to the
universal surjection of `𝐏(E')`'s own canonical datum.

This is the identification that `TautologicalBaseChange.lean` records as owed and as *not*
supplied by `TautologicalDatum.IsUniversal`, which is the mapping-in property at the base alone
and so is not stable under base change. At an invertible module no mapping-in property is
needed: both data are `π^*` of the module and the identification is the canonical one. -/
theorem TautologicalDatum.baseChange_ofInvertible_univ_comp_iso_hom :
    ((TautologicalDatum.ofInvertible Y E hEY).baseChange g E E' hE).univ ≫
        (tautologicalBaseChangeIso g E E' hE).hom =
      (TautologicalDatum.ofInvertible X E' hEX).univ :=
  Eq.trans
    (congrArg (fun m => m ≫ (tautologicalBaseChangeIso g E E' hE).hom)
      (TautologicalDatum.baseChange_ofInvertible_univ g E E' hE hEY))
    (tautologicalBaseChangeIso g E E' hE).inv_hom_id

/-- **Tag 0B3V's clause on the universal quotient of the base-change comparison, with both
tautological data canonical.** For invertible quasi-coherent modules the clause needs no datum
as a hypothesis and quantifies none existentially: the comparison of tautological modules is the
canonical identification `b^*π^*E ≅ π'^*E'`.

The attribute is withheld. The tag's clause carries neither invertibility hypothesis, and this
statement is its specialisation to modules of rank one, the case in which the twist `𝒪(1)` is
the pullback of the module itself. -/
theorem projectiveBundleBaseChange_tautological_ofInvertible :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        (TautologicalDatum.ofInvertible Y E hEY).twist ≅
        (TautologicalDatum.ofInvertible X E' hEX).twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          (TautologicalDatum.ofInvertible Y E hEY).univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
            (projectiveBundleToBase Y E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X E')).map hE.inv ≫
          (TautologicalDatum.ofInvertible X E' hEX).univ :=
  projectiveBundleBaseChange_tautological_of_iso g E E' hE
    (TautologicalDatum.ofInvertible Y E hEY) (TautologicalDatum.ofInvertible X E' hEX)
    (tautologicalBaseChangeIso g E E' hE)
    (TautologicalDatum.baseChange_ofInvertible_univ_comp_iso_hom g E E' hE hEY hEX)

end BaseChange

/-- **The base-change clause at the structure sheaves, for an arbitrary morphism of schemes.**
Both projective bundles are those of the structure sheaf, the identification of `𝒪_X` with
`g^*𝒪_Y` is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, and both tautological data
are canonical. There is no hypothesis on `g`, so the statements of this file and the
`TautologicalDatum` API they feed are satisfiable on data the development exhibits. -/
theorem projectiveBundleBaseChange_tautological_unit {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃ α : (Scheme.Modules.pullback (projectiveBundleBaseChange g
          (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm)).obj
        (tautologicalDatumUnit Y).twist ≅ (tautologicalDatumUnit X).twist,
      (Scheme.Modules.pullback (projectiveBundleBaseChange g
            (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
            (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm)).map
          (tautologicalDatumUnit Y).univ ≫ α.hom =
        (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g
              (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
              (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm)
            (projectiveBundleToBase Y (SheafOfModules.unit Y.ringCatSheaf))).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_projectiveBundleToBase g
              (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
              (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm)).hom.app
            (SheafOfModules.unit Y.ringCatSheaf) ≫
          (Scheme.Modules.pullbackComp
              (projectiveBundleToBase X (SheafOfModules.unit X.ringCatSheaf)) g).inv.app
            (SheafOfModules.unit Y.ringCatSheaf) ≫
          (Scheme.Modules.pullback
              (projectiveBundleToBase X (SheafOfModules.unit X.ringCatSheaf))).map
            (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm.inv ≫
          (tautologicalDatumUnit X).univ :=
  projectiveBundleBaseChange_tautological_ofInvertible g
    (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm
    (AlgebraicGeometry.Scheme.Modules.isInvertible_unit Y)
    (AlgebraicGeometry.Scheme.Modules.isInvertible_unit X)

end Stacks.RelativeProj

end
