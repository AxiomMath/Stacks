module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorHomTransposeScalarLift

/-!
# The keystone's [stacks 0E1W] chain map as a transpose of a restricted evaluation

`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift` values the one chain
map the [stacks 0E1W] side of the keystone carries, the localization of
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q` at the scalar lift `f'` of
the ring map and the scalar lift `K₀` of the K-flat complex `L`.  Its value is a [stacks 0A63]
transpose, and the chain map transposed there is

`W = homEquiv (P ⊗ K₀) J ((extendScalarsMonoidalIso f' P K₀).inv ≫ uncurry (ε Z)) ≫ q`

for `Z = Hom_{A'}(A' ⊗ K₀, J)` the internal Hom complex over `ULift A` and `P = Z|_{R'}`.

That display carries `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` **at the pair
`(P, K₀)`**, whose first entry is an internal-Hom complex, while the [stacks 068I] side carries
the same natural isomorphism at the pair `(K, L)` of ordinary complexes -- identified there by
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`.  Two
occurrences of one natural isomorphism at unrelated arguments are related by no coherence law,
which is the obstruction recorded in
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation`.

This file removes the mismatched occurrence from the keystone's data.
`Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit_comp` evaluates `W` as
the **restricted evaluation**

`(𝟙 P ⊗ₘ η K₀) ≫ ρ ≫ (ev)|_{R'} ≫ q`,

with `η` the unit of degreewise extension--restriction, `ρ` the lax monoidal structure map
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars and
`ev : Z ⊗_{A'} (A' ⊗ K₀) ⟶ J` the evaluation of the internal Hom complex.  Neither
`extendScalarsMonoidalIso` nor `StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry` survives
in the value: the first is visible only inside `ρ`, which is a structure map of restriction of
scalars and not an argument to be matched against the [stacks 068I] side.

**What is not done here.**  No tag is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open, and in particular
the comparison identity `h` is untouched; its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is the display of
one factor of the other hypothesis.

## Main results

* `Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation` -- the
  keystone's localized [stacks 0E1W] chain map as the [stacks 0A63] transpose of a restricted
  evaluation, with no occurrence of
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` at an internal-Hom argument.

## Implementation notes

The substitution is a single `congrArg` with a hand-written motive in the transposed chain map,
which is where the two statements differ; no rewriting is involved, and in particular the two
spellings of degreewise extension of scalars never have to be reconciled inside a tactic block.

`Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit_comp` is stated for two
rings of one universe, which is what the scalar-lift world supplies: `ULift R` and `ULift A` and
all their modules live in `max uR uA uM` together.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The keystone's [stacks 0E1W] chain map as the [stacks 0A63] transpose of a restricted
evaluation.**

`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift` with the transposed
chain map replaced by its value
`Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit_comp`: the unit of
degreewise extension--restriction whiskered into the second variable, the lax monoidal structure
map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars, the
restriction of the evaluation of the internal Hom complex over `ULift A`, and the chosen
K-injective resolution `q`.  The value displays no
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` at the pair `(P, K₀)`.

The K-flatness of the Hom-source is `Stacks.DerivedHom.BaseChange.kFlat_scalarLift` at `L`, and
`J` may be any complex of `ULift A`-modules; only `I` has to be K-injective. -/
theorem Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I),
    let EK := (CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
      max uR uA uM} f').obj K₀
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A) EK J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := (𝟙 P ⊗ₘ ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K₀) ≫
      restrictScalarsLaxTensor f' Z EK ≫
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').map
            (DerivedInternalHom.Model.evaluationMor EK J) ≫ q
    DerivedCategory.Q.map
          (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q) =
      (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K₀)
            (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W) ≫
        ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).hom := by
  intro f' K₀ J I hI q EK Z P W
  refine (Q_map_homComplexChangeOfRingsMap_scalarLift.{uR, uA, uM} f L hL J I q).trans ?_
  exact congrArg
    (fun z => (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
        (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
            (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫ DerivedCategory.Q.map z) ≫
      ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).hom)
    (Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit_comp f' K₀ J q)

end Stacks.DerivedHom.BaseChange

end
