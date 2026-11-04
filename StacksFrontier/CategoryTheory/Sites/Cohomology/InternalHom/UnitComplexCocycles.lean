module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-! # Maps of complexes out of the structure sheaf complex on a slice

Let `(C, O)` be a ringed site, `U` an object of `C` and `A` a cochain complex of `O`-modules. A
map of complexes `O[0]|_U ⟶ A|_U` is the same thing as a section of `A^0` over `U` killed by the
differential: the map is recovered from its value at the unit section `1`, and every cocycle
section arises this way.

This is the dictionary the direct-summand step of Stacks 0FPD and of the first assertion of
Stacks 0FPV runs on. There the section is `η(1)`, the value at `1` of the map of complexes which
represents the coevaluation, and the step replaces it by a sum of pure tensors lifted through a
subcomplex, which has to be turned back into a map of complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.cocycleOfUnitComplexHom`: the value at `1` of a map of complexes
  `O[0]|_U ⟶ A|_U`.
* `AlgebraicGeometry.RingedSite.unitComplexHomOfCocycle`: the map of complexes prescribed by a
  cocycle section.
* `AlgebraicGeometry.RingedSite.unitComplexHomEquivCocycles`: taking the value at the unit
  section identifies the maps of complexes `O[0]|_U ⟶ A|_U` with the sections of `A^0` over `U`
  killed by the differential.

## Main results

* `AlgebraicGeometry.RingedSite.unitComplexHom_ext`: a map of complexes out of `O[0]|_U` is
  determined by its value at `1`.
* `AlgebraicGeometry.RingedSite.cocycleOfUnitComplexHom_restrict`: the compatibility of the
  dictionary with restriction along an arrow of the site.

## Implementation notes

**No terminal object is assumed.** The ringed-space form of this dictionary —
`Stacks.Cohomology.LeftDualPerfect.unitHomOfTop`, `cocycleHom` and `cocycleOf` of
`Topology/Sheaves/Cohomology/PerfectComplexes/UnitComplexMaps.lean` — spreads a section over
`op ⊤` using `homOfLE le_top`, a lattice fact about `Opens T`, and so does not port to a site by
widening a binder. A port under `[HasTerminal C]` would be *faithful*, since the source's own
first move is "we may replace `C, O, M, N, η, ε` by `C/U, O_U, M|_U, …` and assume `C` has a
final object `X`" — but it is not needed and is not assumed here. The terminal object of the
slice site `C/U` is `𝟙 U`, which exists for every `U` with no hypothesis on `C`, and the
dictionary is stated over the slice throughout. What makes that work is that a morphism out of
the free module of rank one on `C/U` is determined by, and can be prescribed by, its value at `1`
over `𝟙 U`: that is `AlgebraicGeometry.RingedSite.unitOverHomEquiv` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource`.
`unitComplexDegreeZero` and `unitComplexHomOfCocycle` are `@[no_expose]`: what a consumer needs
of them — `unitComplexHomEquivCocycles` and the two round-trip lemmas — does not require the
body.

The structure sheaf complex has zero differentials, so the commutation condition of a map of
complexes out of it is the vanishing of `d` on the single component, which is exactly the cocycle
condition; in the degrees other than zero the source vanishes and there is nothing to check.

**How the existence half is built.** Uniqueness needs no new vocabulary: `unitOverHomEquiv`
gives it in degree zero and the source complex vanishes elsewhere. Existence has to *produce* a
map of complexes, and the route is `HomologicalComplex.mkHomFromSingle` — Mathlib's general form
for maps out of a complex concentrated in one degree — rather than a hand-rolled `dif` on the
degree, which would need a cast to move along `n = 0`. What `mkHomFromSingle` asks is that the
source be *literally* `HomologicalComplex.single`, and
`(SheafOfModules.overFunctor O U).mapHomologicalComplex` of a `single` is not: the two differ in
the degrees away from zero, where one has `F.obj 0` and the other `0`. The identification is
Mathlib's own `HomologicalComplex.singleMapHomologicalComplex`, used here directly rather than
through the special case `AlgebraicGeometry.RingedSite.restrictStructureSheafComplexIso`
(`Perfect/Duals.lean`), which names the same natural isomorphism but is sealed to `simp` and
drags a three-hundred-module closure.

Two things keep this short. The detour through
`Stacks.SheafOfModules.overFunctorUnitIso`, to separate `(unit O).over U` from `unit (O|_U)`, is
not needed: those are definitionally equal here, which is already what lets `unitOverHomEquiv` be
applied to the degree-zero component of a map out of the structure sheaf complex. And the
degree-zero component of the composite is *definitionally* the prescribed morphism — every
`eqToHom` in `singleMapHomologicalComplex` and in `mkHomFromSingle` sits between definitionally
equal objects — so the round trip `cocycleOfUnitComplexHom_unitComplexHomOfCocycle` is `rfl` and no
`eqToHom` calculus appears.

This material is kept apart from
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf`, whose
`structureSheafOver_hom_bijective` is the same bijection stated privately there, so that that
file keeps its own import closure.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

section UnitComplexCocycles

variable {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The value at the unit section `1` of a map of complexes out of the structure sheaf complex
on the slice over `U`. This is the `η(1)` of the source's direct-summand argument. -/
def cocycleOfUnitComplexHom {U : X.C}
    (β : X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U) :
    (A.X 0).val.obj (op U) :=
  (β.f 0).val.app (op (Over.mk (𝟙 U))) (show _ from structureSheafOne X U)

/-- Restriction to the slice over `U` preserves zero morphisms. -/
private theorem overFunctor_preservesZeroMorphisms (U : X.C) :
    Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  ⟨fun {_ _} ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))⟩

/-- **A map of complexes out of `O[0]|_U` is determined by its value at `1`.** -/
theorem unitComplexHom_ext {U : X.C}
    {β γ : X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U}
    (h : cocycleOfUnitComplexHom X β = cocycleOfUnitComplexHom X γ) : β = γ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    apply (unitOverHomEquiv X (A.X 0) U).injective
    exact h
  · have := overFunctor_preservesZeroMorphisms X U
    exact (show IsZero ((X.restrictComplex (structureSheafComplex X) U).X n) from
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn)).eq_of_src _ _

/-- **The value at `1` of a map of complexes is a cocycle.** The differential of the structure
sheaf complex vanishes, so the commutation condition in degrees `0` and `1` says exactly
this. -/
theorem cocycleOfUnitComplexHom_d {U : X.C}
    (β : X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U) :
    (A.d 0 1).val.app (op U) (cocycleOfUnitComplexHom X β) = 0 := by
  have hd : (X.restrictComplex (structureSheafComplex X) U).d 0 1 = 0 := by
    change (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((structureSheafComplex X).d 0 1) = 0
    have := overFunctor_preservesZeroMorphisms X U
    rw [show (structureSheafComplex X).d 0 1 = 0 from rfl, Functor.map_zero]
  have hcomm := β.comm 0 1
  rw [hd, zero_comp] at hcomm
  have key : (A.d 0 1).val.app (op U) (cocycleOfUnitComplexHom X β) =
      (β.f 0 ≫ (X.restrictComplex A U).d 0 1).val.app (op (Over.mk (𝟙 U)))
        (show _ from structureSheafOne X U) := rfl
  rw [key, hcomm]
  rfl

/-- The degree-zero component prescribed by a section: the morphism out of the free module of
rank one on the slice over `U` whose value at the unit section `1` is `s`. -/
@[no_expose]
def unitComplexDegreeZero {U : X.C} (s : (A.X 0).val.obj (op U)) :
    (X.restrictComplex (structureSheafComplex X) U).X 0 ⟶ (X.restrictComplex A U).X 0 :=
  (unitOverHomEquiv X (A.X 0) U).symm s

/-- The value of `AlgebraicGeometry.RingedSite.unitComplexDegreeZero` at the unit section. -/
theorem unitComplexDegreeZero_app_one {U : X.C} (s : (A.X 0).val.obj (op U)) :
    (unitComplexDegreeZero X s).val.app (op (Over.mk (𝟙 U)))
      (show _ from structureSheafOne X U) = s :=
  (unitOverHomEquiv X (A.X 0) U).apply_symm_apply s

/-- **Every cocycle section over `U` is the value at `1` of a map of complexes
`O[0]|_U ⟶ A|_U`.** The source is presented as a literal `HomologicalComplex.single` by
Mathlib's `HomologicalComplex.singleMapHomologicalComplex`, which lets
`HomologicalComplex.mkHomFromSingle` do the degree bookkeeping; the hypothesis it asks for in
degree one is the cocycle condition, read through `unitOverHomEquiv` one degree
up. -/
@[no_expose]
def unitComplexHomOfCocycle {U : X.C} (s : (A.X 0).val.obj (op U))
    (hs : (A.d 0 1).val.app (op U) s = 0) :
    X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U :=
  (HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (ComplexShape.up ℤ) 0).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
    HomologicalComplex.mkHomFromSingle (unitComplexDegreeZero X s) (fun k hk => by
      obtain rfl : k = 1 := by simpa using hk.symm
      apply (unitOverHomEquiv X (A.X 1) U).injective
      change (A.d 0 1).val.app (op U)
        ((unitComplexDegreeZero X s).val.app (op (Over.mk (𝟙 U)))
          (show _ from structureSheafOne X U)) = _
      rw [unitComplexDegreeZero_app_one, hs]
      rfl)

/-- **The dictionary is a bijection.** The map of complexes
`AlgebraicGeometry.RingedSite.unitComplexHomOfCocycle` prescribed by a cocycle section has that
section as its value at the unit section. With
`AlgebraicGeometry.RingedSite.unitComplexHom_ext` this says that taking the value at `1` is a
bijection from maps of complexes `O[0]|_U ⟶ A|_U` onto the cocycle sections of `A^0` over
`U`. -/
theorem cocycleOfUnitComplexHom_unitComplexHomOfCocycle {U : X.C}
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) :
    cocycleOfUnitComplexHom X (unitComplexHomOfCocycle X s hs) = s := by
  have hf : (unitComplexHomOfCocycle X s hs).f 0 = unitComplexDegreeZero X s := rfl
  rw [cocycleOfUnitComplexHom, hf, unitComplexDegreeZero_app_one]

/-- **The dictionary, as a bijection.** Taking the value at the unit section `1` identifies the
maps of complexes `O[0]|_U ⟶ A|_U` with the sections of `A^0` over `U` killed by the
differential. This is the site form, over every object and with no terminal object anywhere, of
what `Stacks.Cohomology.LeftDualPerfect.cocycleHom` and `cocycleOf` do over `op ⊤` on a ringed
space. -/
def unitComplexHomEquivCocycles (U : X.C) :
    (X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U) ≃
      {s : (A.X 0).val.obj (op U) // (A.d 0 1).val.app (op U) s = 0} where
  toFun β := ⟨cocycleOfUnitComplexHom X β, cocycleOfUnitComplexHom_d X β⟩
  invFun s := unitComplexHomOfCocycle X s.1 s.2
  left_inv β := unitComplexHom_ext X
    (cocycleOfUnitComplexHom_unitComplexHomOfCocycle X _ (cocycleOfUnitComplexHom_d X β))
  right_inv s := Subtype.ext (cocycleOfUnitComplexHom_unitComplexHomOfCocycle X s.1 s.2)

/-- The comparison of a restriction to the slice over `U` followed by restriction along
`g : V ⟶ U` with the restriction to the slice over `V`, degreewise on complexes. This is
`Functor.mapHomologicalComplexCompIso` at Mathlib's `SheafOfModules.overFunctorMap`. -/
abbrev restrictComplexCompIso {U V : X.C} (g : V ⟶ U)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (X.restrictComplex K U) ≅ X.restrictComplex K V :=
  (Functor.mapHomologicalComplexCompIso
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (ComplexShape.up ℤ)).app K

/-- **The dictionary commutes with restriction.** Restricting a map of complexes
`O[0]|_U ⟶ A|_U` along an arrow `g : V ⟶ U` of the site restricts its value at `1`. This is the
role played on a ringed space by `Stacks.Cohomology.LeftDualPerfect.cocycleOf_restrict`. -/
theorem cocycleOfUnitComplexHom_restrict {U V : X.C} (g : V ⟶ U)
    (β : X.restrictComplex (structureSheafComplex X) U ⟶ X.restrictComplex A U) :
    cocycleOfUnitComplexHom X ((restrictComplexCompIso X g (structureSheafComplex X)).inv ≫
        ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          g).mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫
            (restrictComplexCompIso X g A).hom) =
      (A.X 0).val.restrictₛₗ g.op (cocycleOfUnitComplexHom X β) := by
  have key : cocycleOfUnitComplexHom X ((restrictComplexCompIso X g (structureSheafComplex X)).inv ≫
        ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          g).mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫
            (restrictComplexCompIso X g A).hom) =
      (β.f 0).val.app (op (Over.mk (𝟙 V ≫ g)))
        (show _ from structureSheafOne X V) := rfl
  rw [key]
  have hnat := PresheafOfModules.naturality_apply (β.f 0).val
    (Over.homMk g (by simp) : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)).op
    (show _ from structureSheafOne X U)
  rw [show ((X.restrictComplex (structureSheafComplex X) U).X 0).val.map
      (Over.homMk g (by simp) : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)).op
      (show _ from structureSheafOne X U) = (show _ from structureSheafOne X V) from
    PresheafOfModules.unit_map_one (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj _] at hnat
  exact hnat

end UnitComplexCocycles

end AlgebraicGeometry.RingedSite

end
