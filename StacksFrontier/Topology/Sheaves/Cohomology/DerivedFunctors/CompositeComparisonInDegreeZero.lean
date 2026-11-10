module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# The two composite right-derived comparisons in degree zero

`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` and
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` are the two engines out of which the
comparisons of Stacks 01E5 and 01F1 are assembled, and both are built degreewise on a chosen
injective resolution.  `StacksDraft.Ch20.Sec14.DerivedCompTransport` reads each of them on an
arbitrary resolution; this file identifies them in degree zero with the canonical maps
`CategoryTheory.Functor.toRightDerivedZero`, which is what a degree-zero clause of either tag
consumes and what no resolution-level statement can supply.

## Main results

* `compRightDerivedNatIso_hom_app_zero` and `compRightDerivedNatIso_zero`: for `L` exact and
  preserving injective objects, the comparison `(L ⋙ G).rightDerived 0 ≅ L ⋙ G.rightDerived 0`
  intertwines `(L ⋙ G).toRightDerivedZero` with `G.toRightDerivedZero` whiskered by `L`.
* `rightDerivedCompIso_hom_app_zero` and `rightDerivedCompIso_zero`: for `G` exact and
  `e : F ⋙ G ≅ H`, the comparison `F.rightDerived 0 ⋙ G ≅ H.rightDerived 0` intertwines
  `F.toRightDerivedZero` whiskered by `G` with `H.toRightDerivedZero`, through `e`.

## Implementation notes

For `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` both sides are computed on
  resolutions that differ
only in spelling — `Stacks.Cohomology.CompositeRightDerived.mapInjRes L I` *is* the image of `I`
  under `L` — so the whole
content is `toRightDerivedZero'_mapInjRes`, which is
`CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles` on both sides followed by
cancellation of the monomorphism `HomologicalComplex.iCycles`.

For `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` the two sides are computed on
genuinely different complexes, `F` applied degreewise and then `G`, against `H` applied
degreewise, and the comparison between them is
`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`, whose degree-zero component is
`CategoryTheory.ShortComplex.mapHomologyIso` followed by the homology of `e` applied
degreewise.  Pulling `CategoryTheory.Functor.toRightDerivedZero` through that is exactly the
compatibility of `CategoryTheory.ShortComplex.mapHomologyIso` with
`CategoryTheory.ShortComplex.homologyπ`, i.e.
`CategoryTheory.ShortComplex.π_comp_mapHomologyIso_inv`; once that is available the remaining
step is on cycles and is again `toRightDerivedZero'_comp_iCycles` plus the naturality of `e`.

`CategoryTheory.InjectiveResolution.isoRightDerivedObj` presents the homology of the image of a
resolution through `(HomologicalComplex.homologyFunctor _ _ n).obj
((F.mapHomologicalComplex _).obj K)`, whereas a composite presents the same object through
`(F ⋙ G).mapHomologicalComplex _`; the two agree only after unfolding
`CategoryTheory.Functor.comp` and `CategoryTheory.Functor.mapHomologicalComplex`, so
`Category.assoc` does not fire across the junction and the reassociations below are terms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

/-- Cancelling an inverse against its own `hom` across a three-fold composite, as a term: the
objects on either side of the junction between the computation of a right derived functor on a
resolution and the homology of the image of that resolution are definitionally but not
syntactically equal, so `Category.assoc` cannot be used as a rewrite there. -/
private theorem comp_inv_comp_hom {E : Type*} [Category* E] {V W W' Y Z : E}
    (a : W' ⟶ W) (b : W ⟶ Y) (c : V ≅ Y) (k : Y ⟶ Z) :
    (a ≫ b ≫ c.inv) ≫ c.hom ≫ k = a ≫ b ≫ k := by
  simp

/-- Reassociating the middle two factors of a four-fold composite, as a term. -/
private theorem reassoc_mid {E : Type*} [Category* E] {V W X Y Z : E}
    (p : V ⟶ W) (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) :
    p ≫ u ≫ v ≫ w = p ≫ (u ≫ v) ≫ w := by
  simp

/-- Reassociating the first three factors of a four-fold composite, as a term. -/
private theorem reassoc_left {E : Type*} [Category* E] {V W X Y Z : E}
    (p : V ⟶ W) (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) :
    p ≫ u ≫ v ≫ w = (p ≫ u ≫ v) ≫ w := by
  simp

/-! ### `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` in degree zero -/

section Comp

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D] [Abelian E]
  (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The canonical map to the degree-zero cycles of the image of a resolution does not see the
difference between resolving `X` by `I` and deriving `L ⋙ G`, and resolving `L.obj X` by the
image of `I` under `L` and deriving `G`. -/
theorem toRightDerivedZero'_mapInjRes {X : C} (I : InjectiveResolution X) :
    I.toRightDerivedZero' (L ⋙ G) = (Stacks.Cohomology.CompositeRightDerived.mapInjRes L
      I).toRightDerivedZero' G :=
  (cancel_mono (HomologicalComplex.iCycles
      (((L ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0)).mp
    ((I.toRightDerivedZero'_comp_iCycles (L ⋙ G)).trans
      ((congrArg G.map (mapInjRes_ι_f_zero L I)).symm.trans
        ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).toRightDerivedZero'_comp_iCycles
          G).symm))

/-- **The degree-zero normalization of
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, pointwise.**
The comparison `(L ⋙ G).rightDerived 0 ≅ L ⋙ G.rightDerived 0` carries the canonical map of
`L ⋙ G` to the canonical map of `G` at `L.obj X`. -/
theorem compRightDerivedNatIso_hom_app_zero (X : C) :
    (L ⋙ G).toRightDerivedZero.app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G 0).hom.app X =
      G.toRightDerivedZero.app (L.obj X) := by
  rw [compRightDerivedNatIso_hom_app L G 0 X,
    (injectiveResolution X).toRightDerivedZero_eq (L ⋙ G),
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution
      X)).toRightDerivedZero_eq G,
    ← toRightDerivedZero'_mapInjRes L G (injectiveResolution X)]
  exact comp_inv_comp_hom _ _ _ _

/-- **The degree-zero normalization of
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.** -/
theorem compRightDerivedNatIso_zero :
    (L ⋙ G).toRightDerivedZero ≫ (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G
      0).hom =
      Functor.whiskerLeft L G.toRightDerivedZero :=
  NatTrans.ext (funext fun X => compRightDerivedNatIso_hom_app_zero L G X)

end Comp

/-! ### `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` in degree zero -/

section CompIso

variable {A : Type*} {B : Type*} {D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] (e : F ⋙ G ≅ H)

omit [HasInjectiveResolutions A] in
/-- The degree-zero component of
`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`: compare the homology of `G` applied
to the complex `F` of a resolution with `G` of its homology, then take the homology of `e`
applied degreewise. -/
theorem mapComplexHomologyIso_hom_app_zero
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (ModuleComparison.mapComplexHomologyIso F G H e 0).hom.app K =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc 0).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) 0 := rfl

omit [HasInjectiveResolutions A] in
/-- The cycles-level content of the degree-zero normalization of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`: the canonical map into the cycles of
`G` of the complex of `F` of a resolution, compared through `G` and then pushed along `e`
degreewise, is the canonical map into the cycles of the complex of `H`, composed with `e`. -/
theorem toRightDerivedZero'_comp_mapCyclesIso_inv {M : A} (I : InjectiveResolution M) :
    G.map (I.toRightDerivedZero' F) ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapCyclesIso
            G).inv ≫
          HomologicalComplex.cyclesMap
            ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app
              I.cocomplex) 0 =
      e.hom.app M ≫ I.toRightDerivedZero' H :=
  (cancel_mono (HomologicalComplex.iCycles
      ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0)).mp
    ((Category.assoc _ _ _).trans
      ((whisker_eq _ (Category.assoc _ _ _)).trans
        ((whisker_eq _ (whisker_eq _
              (HomologicalComplex.cyclesMap_i
                ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app
                  I.cocomplex) 0))).trans
          ((whisker_eq _
                (ShortComplex.mapCyclesIso_inv_comp_iCycles_assoc _ G _)).trans
            ((Category.assoc _ _ _).symm.trans
              ((eq_whisker (((G.map_comp _ _).symm).trans
                    (congrArg G.map (I.toRightDerivedZero'_comp_iCycles F))) _).trans
                ((e.hom.naturality (I.ι.f 0)).trans
                  ((whisker_eq _
                      (I.toRightDerivedZero'_comp_iCycles H).symm).trans
                    (Category.assoc _ _ _).symm))))))))

omit [HasInjectiveResolutions A] in
/-- The complex-level content of the degree-zero normalization of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`: the canonical map of `F` into the
degree-zero homology of the complex of a resolution, pushed through `G` and then along
`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`, is the canonical map of `H`,
composed with `e`.  This is `toRightDerivedZero'_comp_mapCyclesIso_inv` read on homology
through `CategoryTheory.ShortComplex.π_comp_mapHomologyIso_inv`. -/
theorem toRightDerivedZero'_comp_mapComplexHomologyIso {M : A} (I : InjectiveResolution M) :
    G.map (I.toRightDerivedZero' F) ≫
        G.map (CochainComplex.isoHomologyπ₀
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom ≫
          (ModuleComparison.mapComplexHomologyIso F G H e 0).hom.app I.cocomplex =
      e.hom.app M ≫ I.toRightDerivedZero' H ≫
        (CochainComplex.isoHomologyπ₀
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom :=
  (whisker_eq _ (whisker_eq _
        (mapComplexHomologyIso_hom_app_zero F G H e I.cocomplex))).trans
    ((reassoc_mid _ _ _ _).trans
      ((whisker_eq _ (eq_whisker (ShortComplex.π_comp_mapHomologyIso_inv _ G) _)).trans
        ((whisker_eq _ (Category.assoc _ _ _)).trans
          ((whisker_eq _ (whisker_eq _
                (HomologicalComplex.homologyπ_naturality
                  ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app
                    I.cocomplex) 0))).trans
            ((reassoc_left _ _ _ _).trans
              ((eq_whisker (toRightDerivedZero'_comp_mapCyclesIso_inv F G H e I) _).trans
                (Category.assoc _ _ _)))))))

/-- **The degree-zero normalization of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, pointwise, on an arbitrary injective
resolution.** -/
theorem rightDerivedCompIso_hom_app_zero_of_resolution {M : A} (I : InjectiveResolution M) :
    G.map (F.toRightDerivedZero.app M) ≫
        (ModuleComparison.rightDerivedCompIso F G H e 0).hom.app M =
      e.hom.app M ≫ H.toRightDerivedZero.app M :=
  (eq_whisker (congrArg G.map (I.toRightDerivedZero_eq F)) _).trans
    ((whisker_eq _ (rightDerivedCompIso_hom_app_eq F G H e 0 I)).trans
      ((eq_whisker (G.map_comp _ _) _).trans
        ((eq_whisker (whisker_eq _ (G.map_comp _ _)) _).trans
          ((comp_inv_comp_hom _ _ (G.mapIso (I.isoRightDerivedObj F 0)) _).trans
            ((reassoc_left _ _ _ _).trans
              ((eq_whisker (toRightDerivedZero'_comp_mapComplexHomologyIso F G H e I) _).trans
                ((Category.assoc _ _ _).trans
                  ((whisker_eq _ (Category.assoc _ _ _)).trans
                    (whisker_eq _ (I.toRightDerivedZero_eq H).symm)))))))))

/-- **The degree-zero normalization of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, pointwise.** -/
theorem rightDerivedCompIso_hom_app_zero (M : A) :
    G.map (F.toRightDerivedZero.app M) ≫
        (ModuleComparison.rightDerivedCompIso F G H e 0).hom.app M =
      e.hom.app M ≫ H.toRightDerivedZero.app M :=
  rightDerivedCompIso_hom_app_zero_of_resolution F G H e (injectiveResolution M)

/-- **The degree-zero normalization of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.** -/
theorem rightDerivedCompIso_zero :
    Functor.whiskerRight F.toRightDerivedZero G ≫
        (ModuleComparison.rightDerivedCompIso F G H e 0).hom =
      e.hom ≫ H.toRightDerivedZero :=
  NatTrans.ext (funext fun M => rightDerivedCompIso_hom_app_zero F G H e M)

end CompIso

end Stacks.Cohomology.DerivedCompTransport

end
