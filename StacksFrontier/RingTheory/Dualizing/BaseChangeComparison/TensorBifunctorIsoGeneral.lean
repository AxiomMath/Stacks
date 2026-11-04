module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormula

/-!
# The two derived tensor products agree as bifunctors, at an independent module universe

`Dualizing.derivedHomAdjunctionTensorNatIso` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso` identifies the
canonical derived tensor product of [stacks 0FNQ] with the tensor half of the tensor--Hom
bundle of [stacks 0A63] as bifunctors, with the module universe equal to the ring's.  The
base-change comparison of this directory works at an *independent* module universe: the lax
monoidal structure map `Dualizing.derivedTensorBaseChange` lives on
`D(ModuleCat.{max uR uA uM} A)`, and [stacks 068I] is stated for
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral` data there.

This file gives the same identification at that universe:
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` identifies
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral` -- which is exactly the
`DerivedTensorProductGeneral` datum [stacks 068I] asks for -- with the tensor of
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is the bundle
`Dualizing.derivedTensorBaseChange` is phrased in.  So a monoidality isomorphism obtained from
[stacks 068I] can be read in the vocabulary of [stacks 0A63].

## Main results

* `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` — the isomorphism of bifunctors at an
  independent module universe.
* `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat` — its value at a pair of
  K-flat complexes.

## Implementation notes

This is not obtained by conjugating the equal-universe isomorphism of
`…BaseChangeComparison.TensorBifunctorIso` along
`StacksDraft.DerivedHom.derivedScalarEquivalence`.  Conjugation would have to reconcile the two
`ULift` universe parameters that the two sides are built from, and it is unnecessary: both
bifunctors already carry a K-flat comparison *at the independent module universe*, namely
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral.comparison` on one side and
`CochainComplex.DerivedTensor.derivedTensor_comparison` on the other, and the two land on the
same object, the localization of `CochainComplex.DerivedTensor.tensorComplex`.  Their
naturality statements — `comparison_naturality` and
`Dualizing.ProjectionFormula.derivedTensor_comparison_naturality` — are literally the same
equation.  So the descent of `…BaseChangeComparison.TensorBifunctorIso` runs again verbatim,
with `CochainComplex.DerivedTensor.IsKFlat` as the resolving class.

Only `Dualizing.natTransOfResolutions_app_of_prop` is reused from that file.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped MonoidalCategory
open CochainComplex.DerivedTensor
open ModuleSystemRlimTensor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- K-flatness at an independent module universe, as a predicate, spelled once so that every
appeal to the descent lemmas of `ModuleSystemRlimTensor` uses the same resolving class. -/
private abbrev isKFlatProp (A : Type u) [CommRing A] :
    CochainComplex (ModuleCat.{max u v} A) ℤ → Prop := fun L => IsKFlat.{u, v} L

/-- Every cochain complex of `A`-modules in an independent module universe has a K-flat
resolution: [stacks 06Y4], in the shape the descent lemmas ask for. -/
private lemma exists_isKFlat (M : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ∃ (L : CochainComplex (ModuleCat.{max u v} A) ℤ) (s : L ⟶ M),
      isKFlatProp.{u, v} A L ∧ QuasiIso s := by
  obtain ⟨K, f, hK, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, v} M
  exact ⟨K, f, (isKFlat_iff_kFlat K).mpr hK, hf⟩

/-- On a pair of K-flat complexes both derived tensor products are computed by the ordinary
total tensor product, so they agree there. -/
noncomputable def kFlatDerivedTensorIsoGeneral (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) :
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  (canonicalDerivedTensorProductGeneral.{u, v} A).comparison K L hK hL ≪≫
    (derivedTensor_comparison.{u, v} A K L hL).symm

/-- Naturality of `c ≪≫ d.symm` when both `c` and `d` are natural over a common target. -/
private lemma trans_symm_hom_naturality {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (a : X ⟶ X') (b : Y ⟶ Y') (r : Z ⟶ Z') (c : X ≅ Z) (c' : X' ≅ Z') (d : Y ≅ Z) (d' : Y' ≅ Z')
    (hc : a ≫ c'.hom = c.hom ≫ r) (ht : b ≫ d'.hom = d.hom ≫ r) :
    a ≫ (c' ≪≫ d'.symm).hom = (c ≪≫ d.symm).hom ≫ b := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, ← Category.assoc, hc,
    Category.assoc, Category.assoc, ← cancel_mono d'.hom]
  simp [ht]

/-- The K-flat comparison is natural in the first variable. -/
@[reassoc]
private lemma kFlatDerivedTensorIsoGeneral_naturality_left
    {K K' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (f : K ⟶ K') (hK : IsKFlat.{u, v} K) (hK' : IsKFlat.{u, v} K') (hL : IsKFlat.{u, v} L) :
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫ (kFlatDerivedTensorIsoGeneral K' L hK' hL).hom =
      (kFlatDerivedTensorIsoGeneral K L hK hL).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (show (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L) from
            (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L))) := by
  have hc := (canonicalDerivedTensorProductGeneral.{u, v} A).comparison_naturality
    f (𝟙 L) hK hK' hL hL
  have ht := ProjectionFormula.derivedTensor_comparison_naturality.{u, v} A f (𝟙 L) hL hL
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hc
  rw [CategoryTheory.Functor.map_id] at ht
  exact trans_symm_hom_naturality _ _ _ _ _ _ _ hc ht

/-- The K-flat comparison is natural in the second variable. -/
@[reassoc]
private lemma kFlatDerivedTensorIsoGeneral_naturality_right
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    {L L' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (g : L ⟶ L') (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) (hL' : IsKFlat.{u, v} L') :
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫ (kFlatDerivedTensorIsoGeneral K L' hK hL').hom =
      (kFlatDerivedTensorIsoGeneral K L hK hL).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (show (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L') from
            (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map g)) := by
  have hc := (canonicalDerivedTensorProductGeneral.{u, v} A).comparison_naturality
    (𝟙 K) g hK hK hL hL'
  have ht := ProjectionFormula.derivedTensor_comparison_naturality.{u, v} A (𝟙 K) g hL hL'
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hc
  rw [CategoryTheory.Functor.map_id] at ht
  exact trans_symm_hom_naturality _ _ _ _ _ _ _ hc ht

/-- The comparison in the second variable, descended from K-flat complexes to all of `D(A)`,
with the first variable a K-flat complex. -/
private noncomputable def tensorNatTransRightGeneral
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (hK : IsKFlat.{u, v} K) :
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K) ⟶
      (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).tensor).obj (DerivedCategory.Q.obj K) :=
  natTransOfResolutions (isKFlatProp.{u, v} A) exists_isKFlat
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor).obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIsoGeneral K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIsoGeneral_naturality_right K g hK hL hL')

/-- The component formula for the second-variable descent. -/
private lemma tensorNatTransRightGeneral_app (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (tensorNatTransRightGeneral K hK).app X =
      ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj
            (DerivedCategory.Q.obj K)).map
          (resolutionIso (isKFlatProp.{u, v} A) exists_isKFlat X).inv ≫
        (kFlatDerivedTensorIsoGeneral K
            (resolutionComplex (isKFlatProp.{u, v} A) exists_isKFlat X) hK
          (resolutionComplex_prop (isKFlatProp.{u, v} A) exists_isKFlat X)).hom ≫
        ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
              max u v + 1} A).tensor).obj (DerivedCategory.Q.obj K)).map
          (resolutionIso (isKFlatProp.{u, v} A) exists_isKFlat X).hom :=
  natTransOfResolutions_app (isKFlatProp.{u, v} A) exists_isKFlat
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor).obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIsoGeneral K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIsoGeneral_naturality_right K g hK hL hL') X

/-- The second-variable descent is the K-flat comparison at a K-flat second complex. -/
private lemma tensorNatTransRightGeneral_app_kFlat
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) :
    (tensorNatTransRightGeneral K hK).app (DerivedCategory.Q.obj L) =
      (kFlatDerivedTensorIsoGeneral K L hK hL).hom :=
  natTransOfResolutions_app_of_prop (isKFlatProp.{u, v} A) exists_isKFlat
    ((canonicalDerivedTensorProductGeneral.{u, v} A).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor).obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIsoGeneral K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIsoGeneral_naturality_right K g hK hL hL') L hL

/-- Every component of the second-variable descent is an isomorphism. -/
private instance tensorNatTransRightGeneral_app_isIso
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (hK : IsKFlat.{u, v} K)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((tensorNatTransRightGeneral K hK).app X) := by
  rw [tensorNatTransRightGeneral_app]
  infer_instance

/-- The second-variable descent is an isomorphism of functors. -/
private instance tensorNatTransRightGeneral_isIso
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (hK : IsKFlat.{u, v} K) :
    IsIso (tensorNatTransRightGeneral K hK) :=
  NatIso.isIso_of_isIso_app _

/-- The second-variable descents are natural in chain maps between K-flat first complexes. -/
@[reassoc]
private lemma tensorNatTransRightGeneral_naturality
    {K K' : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (f : K ⟶ K') (hK : IsKFlat.{u, v} K) (hK' : IsKFlat.{u, v} K') :
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor.map (DerivedCategory.Q.map f) ≫
        tensorNatTransRightGeneral K' hK' =
      tensorNatTransRightGeneral K hK ≫
        (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
            max u v + 1} A).tensor).map (DerivedCategory.Q.map f) := by
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app, tensorNatTransRightGeneral_app,
    tensorNatTransRightGeneral_app]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [curry_obj_obj_map, curry_obj_map_app, Prod.mkHom]
  rw [kFlatDerivedTensorIsoGeneral_naturality_left_assoc _ f hK hK'
    (resolutionComplex_prop (isKFlatProp.{u, v} A) exists_isKFlat X)]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  simp

/-- The comparison descended in the first variable too: a morphism of bifunctors, in curried
form. -/
private noncomputable def tensorNatTransGeneral (A : Type u) [CommRing A] :
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor ⟶
      curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor :=
  natTransOfResolutions (isKFlatProp.{u, v} A) exists_isKFlat
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).tensor)
    (fun K hK => tensorNatTransRightGeneral K hK)
    (fun _K _K' hK hK' f => tensorNatTransRightGeneral_naturality f hK hK')

/-- The component formula for the first-variable descent. -/
private lemma tensorNatTransGeneral_app (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (tensorNatTransGeneral.{u, v} A).app X =
      (canonicalDerivedTensorProductGeneral.{u, v} A).tensor.map
          (resolutionIso (isKFlatProp.{u, v} A) exists_isKFlat X).inv ≫
        tensorNatTransRightGeneral
          (resolutionComplex (isKFlatProp.{u, v} A) exists_isKFlat X)
          (resolutionComplex_prop (isKFlatProp.{u, v} A) exists_isKFlat X) ≫
        (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
            max u v + 1} A).tensor).map
          (resolutionIso (isKFlatProp.{u, v} A) exists_isKFlat X).hom :=
  natTransOfResolutions_app (isKFlatProp.{u, v} A) exists_isKFlat
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).tensor)
    (fun K hK => tensorNatTransRightGeneral K hK)
    (fun _K _K' hK hK' f => tensorNatTransRightGeneral_naturality f hK hK') X

/-- The first-variable descent is the second-variable descent at a K-flat first complex. -/
private lemma tensorNatTransGeneral_app_kFlat (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) :
    (tensorNatTransGeneral.{u, v} A).app (DerivedCategory.Q.obj K) =
      tensorNatTransRightGeneral K hK :=
  natTransOfResolutions_app_of_prop (isKFlatProp.{u, v} A) exists_isKFlat
    (canonicalDerivedTensorProductGeneral.{u, v} A).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).tensor)
    (fun K hK => tensorNatTransRightGeneral K hK)
    (fun _K _K' hK hK' f => tensorNatTransRightGeneral_naturality f hK hK') K hK

/-- Every component of the first-variable descent is an isomorphism of functors. -/
private instance tensorNatTransGeneral_app_isIso (X : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((tensorNatTransGeneral.{u, v} A).app X) := by
  rw [tensorNatTransGeneral_app]
  infer_instance

/-- The first-variable descent is an isomorphism. -/
private instance tensorNatTransGeneral_isIso : IsIso (tensorNatTransGeneral.{u, v} A) :=
  NatIso.isIso_of_isIso_app _

/-- **The derived tensor product datum of [stacks 068I] and the tensor half of the tensor--Hom
bundle of [stacks 0A63] agree as bifunctors, at an independent module universe.**

`CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral` is the
`DerivedTensorProductGeneral` datum that [stacks 068I] takes as input;
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is the bundle that
`Dualizing.derivedTensorBaseChange` — the lax monoidal structure map of derived base change —
is phrased in.  This is one isomorphism of functors `D(A) × D(A) ⥤ D(A)` between them, natural
in both variables, so a monoidality isomorphism supplied by [stacks 068I] can be read in the
vocabulary of [stacks 0A63].  Its value on a pair of K-flat complexes is
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat`, which is the level at which
[stacks 068I] itself is characterized. -/
@[no_expose] noncomputable def derivedHomAdjunctionTensorNatIsoGeneral
    (A : Type u) [CommRing A] :
    uncurry.obj (canonicalDerivedTensorProductGeneral.{u, v} A).tensor ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor :=
  uncurry.mapIso (asIso (tensorNatTransGeneral.{u, v} A)) ≪≫ currying.counitIso.app _

/-- The bifunctorial comparison is the K-flat comparison on a pair of K-flat complexes. -/
lemma derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat
    (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) :
    (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (kFlatDerivedTensorIsoGeneral K L hK hL).hom := by
  dsimp only [derivedHomAdjunctionTensorNatIsoGeneral, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom]
  rw [NatTrans.comp_app]
  simp only [currying_counitIso_hom_app_app, uncurry_map_app]
  rw [tensorNatTransGeneral_app_kFlat K hK, tensorNatTransRightGeneral_app_kFlat K L hK hL]
  exact Category.comp_id _

end Dualizing

end
