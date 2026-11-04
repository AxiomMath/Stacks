module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareDerived

/-!
# The lifted algebra of a pushout square, derived

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareDerived` proves
`Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square`, the derived projection
formula at the two ring maps of a pushout square

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

with the comparisons of the square read at chain level, through `DerivedCategory.Q`.  Its
implementation notes list the identifications that replace them by the *derived* comparisons the
keystone `Dualizing.TensorComparisonCompatibility` is stated with, one per factor.  This file
discharges the one for the lifted algebra, the factor
`DerivedCategory.Q (pushoutAlgebraIsoComplex.inv ▷ -)`.

`Dualizing.derivedBaseChangeAlgebraIso` is the keystone's identification `A' = A ⊗ᴸ_R R'`, and
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` computes it as five factors: the counit of
derived base change along `R → R'` at the degree-zero complex on the algebra, then
`DerivedCategory.Q` of a chain-level morphism built from the **underived** comparison of
[stacks 065Z], then the two canonical isomorphisms of restriction of scalars along `R' → A'` with
the degree-zero complex of the base change of the algebra between them.  What is proved here is
that `Dualizing.pushoutAlgebraIsoComplex`, read through `DerivedCategory.Q`, is exactly the last
four of those factors: over a pushout square the derived lifted algebra is the counit at the
degree-zero complex on `T` followed by `DerivedCategory.Q` of the chain-level comparison, and no
other input is involved.

The two readings differ only in the two places where the keystone's statement is less general than
a pushout square: the algebra appears there as `ModuleCat.of A (ULift A)` rather than as
`ModuleCat.of T T`, and its base change as the ring `TensorProduct R A R'` rather than as `T'`, so
`Dualizing.extendScalarsULiftUnitIso` stands where `ModuleCat.ExtendScalars.objSelfIso` stands
here.  `Dualizing.derivedBaseChangeAlgebraIso` therefore cannot itself occur in a statement about
a general pushout square — its type names `TensorProduct R A R'` and `ULift` — and neither can it
occur in `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square`, whose algebra is
`ModuleCat.of T T` for a ring `T`; crossing that gap is the business of the universe-lift
transport, which is a separate step.  The statements below are therefore in the shape of
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single`, factor for factor, at the square's own
data.

## Main results

* `Dualizing.pushoutAlgebraIsoComplex_hom_eq` — **the chain-level identification**: the lifted
  algebra of the square is the degree-zero crossing of restriction of scalars along `g`, the
  pushout comparison `MilnorPatching.pushoutBaseChange` at the degree-zero complex on `T`, the
  degree-zero crossing of extension of scalars along `w` with `S' ⊗_S T = T'`, and the degree-zero
  crossing of restriction of scalars along `h`.
* `Dualizing.pushoutAlgebraIsoComplex_hom_eq_single` — **the derived component value**: the same
  equation after `DerivedCategory.Q`, with the pushout comparison replaced by the underived
  comparison of [stacks 065Z] that `RingTheory.TorIndependence.derivedBaseChangeComparison`
  carries, and the trailing chain-level factors replaced by the components of
  `CategoryTheory.Functor.mapDerivedCategoryFactors` and
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` they are read with in
  `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single`.

## Implementation notes

The chain-level identification is proved degreewise.  Away from degree zero the target is a zero
object, so both sides agree there by `CategoryTheory.Limits.IsZero.eq_of_tgt` — the source is a
zero object too, but only the target is needed, and reading the target avoids having to know that
extension of scalars preserves zero objects.  In degree zero every factor is evaluated by the
`HomologicalComplex.singleMapHomologicalComplex` component lemmas, and what is left is the
naturality of the pushout comparison at `HomologicalComplex.singleObjXSelf`, which is isolated as
the hypothesis `hP` so that the two `Iso.inv_hom_id` cancellations around it can be done by `rw`
rather than by a `simp` set that loops between `Functor.map_comp` and `Category.assoc`.

Passing from the chain-level equation to the derived one needs two crossings that `rw` cannot make
in place.  `DerivedCategory.singleFunctor C n` and `CochainComplex.singleFunctor C n ⋙
DerivedCategory.Q` are equal by `rfl`, since Mathlib defines the former as the latter, so the
`DerivedCategory.singleFunctor` factor of `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` is
moved under `DerivedCategory.Q` by a `rfl` hypothesis.  And Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`
states its left-hand side at `HomologicalComplex.single _ (ComplexShape.up ℤ) 0` while the
composite here carries `CochainComplex.singleFunctor _ 0`; the two are definitionally but not
syntactically equal, so that lemma is instantiated by `exact` against a written-out type, where
the gap is crossed at default transparency.

No `@[stacks]` attribute is placed here: the obligation of
`Dualizing.TensorComparisonCompatibility` is still open, so nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor

universe u

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']

section Square

variable (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
  (comm : w.comp g = h.comp p)

/-- **The lifted algebra of a pushout square, at chain level.**  For a pushout square
`w ∘ g = h ∘ p`, the comparison `Dualizing.pushoutAlgebraIsoComplex` — the base change along `p` of
the algebra `T` placed in degree zero, identified with the algebra `T'` placed in degree zero — is
the composite of four canonical factors: the crossing of `Dualizing.mapComplexCompIso` type that
takes the degree-zero complex on the restriction of `T` to the restriction of the degree-zero
complex on `T`, the pushout comparison `MilnorPatching.pushoutBaseChange` of [stacks 065Z] at that
complex, the crossing of extension of scalars along `w` past the degree-zero complex followed by
`ModuleCat.ExtendScalars.objSelfIso`, which is the identification `S' ⊗_S T = T'` in degree zero,
and the crossing back of restriction of scalars along `h`.

This is the chain-level content of the derived identification: the right-hand side is, factor for
factor, the chain-level part of the composite that
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` evaluates the keystone's lifted algebra to,
with `ModuleCat.of T T` for the keystone's `ModuleCat.of A (ULift A)`.

Proved degreewise; see the implementation notes of this file. -/
theorem pushoutAlgebraIsoComplex_hom_eq (hp : MilnorPatching.IsPushoutSquare g p w h comm) :
    (pushoutAlgebraIsoComplex g p w h comm hp).hom =
      ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((ModuleCat.restrictScalars.{u} g).mapCochainComplexSingleFunctor 0).inv.app
            (ModuleCat.of T T)) ≫
        (NatTrans.mapHomologicalComplex
            (MilnorPatching.pushoutBaseChange.{u} g p w h comm hp).inv
            (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor (ModuleCat.{u} T) 0).obj (ModuleCat.of T T)) ≫
        ((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.extendScalars.{u, u, u} w) (ComplexShape.up ℤ) 0).hom.app
              (ModuleCat.of T T) ≫
            (CochainComplex.singleFunctor (ModuleCat.{u} T') 0).map
              (ModuleCat.ExtendScalars.objSelfIso w).hom) ≫
        ((ModuleCat.restrictScalars.{u} h).mapCochainComplexSingleFunctor 0).hom.app
          (ModuleCat.of T' T') := by
  have hnat := (MilnorPatching.pushoutBaseChange.{u} g p w h comm hp).inv.naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of T T)).inv
  simp only [Functor.comp_map] at hnat
  have hP : (pushoutAlgebraIso g p w h comm hp).hom =
      (ModuleCat.extendScalars.{u, u, u} p).map ((ModuleCat.restrictScalars.{u} g).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of T T)).inv) ≫
        (MilnorPatching.pushoutBaseChange.{u} g p w h comm hp).inv.app
            (((HomologicalComplex.single (ModuleCat.{u} T) (ComplexShape.up ℤ) 0).obj
              (ModuleCat.of T T)).X 0) ≫
          (ModuleCat.restrictScalars.{u} h).map
            ((ModuleCat.extendScalars.{u, u, u} w).map
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  (ModuleCat.of T T)).hom ≫
              (ModuleCat.ExtendScalars.objSelfIso w).hom) := by
    rw [← Category.assoc, hnat, Category.assoc,
      ← Functor.map_comp (ModuleCat.restrictScalars.{u} h), ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    simp only [pushoutAlgebraIsoComplex, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.mapCochainComplexSingleFunctor,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc (ModuleCat.restrictScalars.{u} h)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hP]
    simp only [Functor.map_comp, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of T' T')) n hn).eq_of_tgt _ _

attribute [local instance] HasDerivedCategory.standard

/-- **The derived component value of the lifted algebra of a pushout square.**  For a pushout
square `w ∘ g = h ∘ p` and arbitrary models `Bp`, `Bw` of derived extension of scalars along `p`
and `w` with comparison morphisms `βp`, `βw`: the image under `DerivedCategory.Q` of the
chain-level lifted algebra `Dualizing.pushoutAlgebraIsoComplex` is the composite of the underived
comparison of [stacks 065Z] at the degree-zero complex on `T`, read after the degree-zero crossing
of restriction of scalars along `g`, with the two components of
`CategoryTheory.Functor.mapDerivedCategoryFactors` and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` of restriction of scalars along `h` and
the identification `S' ⊗_S T = T'` between them.

That composite is the right-hand side of
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` — the computed value of the keystone's
lifted algebra `Dualizing.derivedBaseChangeAlgebraIso` — with its leading counit component
dropped and with `ModuleCat.of T T`, `ModuleCat.of T' T'` and
`ModuleCat.ExtendScalars.objSelfIso` in place of `ModuleCat.of A (ULift A)`,
`ModuleCat.of (A ⊗_R R') (ULift (A ⊗_R R'))` and `Dualizing.extendScalarsULiftUnitIso`.  So over a
pushout square the derived lifted algebra is `βp` at the degree-zero complex on `T` followed by
`DerivedCategory.Q` of the chain-level comparison, which is what reads the chain-level square of
`Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square` against the keystone at this
factor.

Only the naturality of the two comparison morphisms is used; neither model carries a universal
property here beyond the one its `IsLeftDerivedFunctor` instance supplies to
`RingTheory.TorIndependence.derivedBaseChangeComparison`, whose first component — the underived
comparison — is all that occurs. -/
theorem pushoutAlgebraIsoComplex_hom_eq_single
    (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (Bp : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} S'))
    (Bw : DerivedCategory (ModuleCat.{u} T) ⥤ DerivedCategory (ModuleCat.{u} T'))
    (βp : DerivedCategory.Q ⋙ Bp ⟶
      (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (βw : DerivedCategory.Q ⋙ Bw ⟶
      (ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Bp.IsLeftDerivedFunctor βp
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))]
    [Bw.IsLeftDerivedFunctor βw
      (HomologicalComplex.quasiIso (ModuleCat.{u} T) (ComplexShape.up ℤ))] :
    DerivedCategory.Q.map (pushoutAlgebraIsoComplex g p w h comm hp).hom =
      DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              (((ModuleCat.restrictScalars.{u} g).mapCochainComplexSingleFunctor 0).inv.app
                (ModuleCat.of T T)) ≫
            (NatTrans.mapHomologicalComplex
              (RingTheory.TorIndependence.derivedBaseChangeComparison
                g p w h comm Bp Bw βp βw).1 (ComplexShape.up ℤ)).app
              ((HomologicalComplex.single (ModuleCat.{u} T) (ComplexShape.up ℤ) 0).obj
                (ModuleCat.of T T))) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (ModuleCat.{u} T) (ComplexShape.up ℤ) 0).obj
              (ModuleCat.of T T))) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map
          (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex
                (ModuleCat.extendScalars.{u, u, u} w) (ComplexShape.up ℤ) 0).hom.app
                (ModuleCat.of T T)) ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} T') 0).map
              (ModuleCat.ExtendScalars.objSelfIso w).hom) ≫
        ((ModuleCat.restrictScalars.{u} h).mapDerivedCategorySingleFunctor 0).hom.app
          (ModuleCat.of T' T') := by
  have hs : (DerivedCategory.singleFunctor (ModuleCat.{u} T') 0).map
        (ModuleCat.ExtendScalars.objSelfIso w).hom =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} T') 0).map
        (ModuleCat.ExtendScalars.objSelfIso w).hom) := rfl
  have hnat2 := (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} w) (ComplexShape.up ℤ) 0).hom.app
        (ModuleCat.of T T) ≫
      (CochainComplex.singleFunctor (ModuleCat.{u} T') 0).map
        (ModuleCat.ExtendScalars.objSelfIso w).hom)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat2
  have hcross : (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor (ModuleCat.{u} T') 0).obj (ModuleCat.of T' T')) ≫
        ((ModuleCat.restrictScalars.{u} h).mapDerivedCategorySingleFunctor 0).hom.app
          (ModuleCat.of T' T') =
      DerivedCategory.Q.map
        (((ModuleCat.restrictScalars.{u} h).mapCochainComplexSingleFunctor 0).hom.app
          (ModuleCat.of T' T')) :=
    Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app _ _
  have key : (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (ModuleCat.{u} T) (ComplexShape.up ℤ) 0).obj
              (ModuleCat.of T T))) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map
            (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex
                  (ModuleCat.extendScalars.{u, u, u} w) (ComplexShape.up ℤ) 0).hom.app
                  (ModuleCat.of T T) ≫
                (CochainComplex.singleFunctor (ModuleCat.{u} T') 0).map
                  (ModuleCat.ExtendScalars.objSelfIso w).hom)) ≫
          ((ModuleCat.restrictScalars.{u} h).mapDerivedCategorySingleFunctor 0).hom.app
            (ModuleCat.of T' T') =
      DerivedCategory.Q.map
        (((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex
                (ModuleCat.extendScalars.{u, u, u} w) (ComplexShape.up ℤ) 0).hom.app
                (ModuleCat.of T T) ≫
              (CochainComplex.singleFunctor (ModuleCat.{u} T') 0).map
                (ModuleCat.ExtendScalars.objSelfIso w).hom) ≫
          ((ModuleCat.restrictScalars.{u} h).mapCochainComplexSingleFunctor 0).hom.app
            (ModuleCat.of T' T')) := by
    rw [← Category.assoc, ← hnat2, Category.assoc, hcross,
      ← CategoryTheory.Functor.map_comp]
  rw [← pushoutBaseChange_inv_eq_derivedBaseChangeComparison g p w h comm hp Bp Bw βp βw,
    pushoutAlgebraIsoComplex_hom_eq g p w h comm hp, hs,
    ← CategoryTheory.Functor.map_comp DerivedCategory.Q, key,
    ← CategoryTheory.Functor.map_comp DerivedCategory.Q]
  simp only [Category.assoc, CochainComplex.singleFunctor, CochainComplex.singleFunctors]

end Square

end Dualizing

end
