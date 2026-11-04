module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness

/-!
# The two derived tensor products agree as bifunctors

Two derived tensor products on `D(R)` are in play in this chapter.  One is the canonical
derived tensor product of [stacks 0FNQ],
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`, a curried bifunctor
`D(R) ⥤ D(R) ⥤ D(R)`.  The other is the tensor half of the tensor--Hom bundle of [stacks 0A63],
`StacksDraft.DerivedHom.derivedHomAdjunction`, a functor on the product category
`D(R) × D(R) ⥤ D(R)` carrying the Hom equivalence.

`Dualizing.derivedHomAdjunctionTensorIso` of
`StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness` identifies the two **object by
object**: its value at a pair `(P, Q)` is built from an arbitrary choice of K-flat resolution of
each of `P` and `Q`, and no naturality is recorded.  That is not enough to transport a
monoidality isomorphism from one vocabulary into the other, which is what the base-change
comparison of this directory needs.

This file supplies the bifunctorial upgrade: a single isomorphism of functors
`D(R) × D(R) ⥤ D(R)`, natural in both variables at once.

## Main results

* `Dualizing.derivedHomAdjunctionTensorNatIso` — the isomorphism of bifunctors.
* `Dualizing.derivedHomAdjunctionTensorNatIso_hom_app_kFlat` — its value at a pair of K-flat
  complexes is `Dualizing.kFlatDerivedTensorIso`, the comparison of the two K-flat
  characterizations.  This is what makes the isomorphism usable: it pins the component down on
  the complexes at which [stacks 068I] is itself characterized.

## Implementation notes

Both bifunctors are left-derived in each variable and each carries a K-flat comparison --
`CochainComplex.DerivedTensor.DerivedTensorProduct.comparison` on one side,
`StacksDraft.DerivedHom.DerivedHomData.tensorIso` on the other -- and on a pair of K-flat
complexes both comparisons land on the *same* object, the localization of the ordinary total
tensor product.  So the two bifunctors are canonically identified on K-flat pairs, by
`Dualizing.kFlatDerivedTensorIso`.

The identification is then descended one variable at a time with
`ModuleSystemRlimTensor.natTransOfResolutions`, which turns a family of morphisms on a
resolving class of complexes, natural in chain maps between them, into a natural transformation
on all of `D(R)`.  That instrument descends in a single variable, and its target category is
arbitrary, so the second pass is run with the target taken to be the functor category
`D(R) ⥤ D(R)`: the family descended there is `K ↦ (the first pass at K)`, whose naturality in
chain maps `K ⟶ K'` is checked componentwise and reduces, after cancelling the resolution
isomorphism of the component, to the first-variable K-flat naturality
`Dualizing.kFlatDerivedTensorIso_naturality_left`.

Only after both passes is the transformation turned into an isomorphism, by
`CategoryTheory.NatIso.isIso_of_isIso_app` at each stage; the component formula
`ModuleSystemRlimTensor.natTransOfResolutions_app` is what exhibits every component as a
composite of isomorphisms.  Working with transformations rather than isomorphisms throughout is
what keeps the component formula available: `ModuleSystemRlimTensor.natIsoOfResolutions` has no
such formula attached, and its body cannot be unfolded past the `no_expose` definitions of
`CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct` and
`StacksDraft.DerivedHom.derivedHomAdjunction`.

`Dualizing.natTransOfResolutions_app_of_prop` is the small general fact that a descended
transformation is the given family at a complex of the resolving class; it is what makes the
descent reversible on K-flat complexes, and it follows from
`ModuleSystemRlimTensor.map_comp_eq_of_resolutions` applied to the resolution isomorphism
itself.

No `@[stacks]` attribute is placed here: this compares two formalizations of one notion, and
both are tagged where they are constructed.

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

universe u

namespace Dualizing

variable {R : Type u} [CommRing R]

/-- K-flatness as a predicate on cochain complexes, spelled once so that every appeal to the
descent lemmas of `ModuleSystemRlimTensor` uses the same resolving class. -/
private abbrev kFlatProp (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ → Prop := fun L => L.KFlat

/-- Every cochain complex of `R`-modules has a K-flat resolution: [stacks 06Y4], in the shape
the descent lemmas of `ModuleSystemRlimTensor` ask for. -/
private lemma exists_kFlat (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ) (s : L ⟶ M), kFlatProp R L ∧ QuasiIso s := by
  obtain ⟨K, f, hK, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} M
  exact ⟨K, f, hK, hf⟩

/-- **A descended natural transformation is the given family at a complex of the resolving
class.** The component at `Q K` is by definition conjugated from the component at a resolution
of `Q K`; when `K` itself lies in the class the conjugation is by the resolution isomorphism,
which `ModuleSystemRlimTensor.map_comp_eq_of_resolutions` moves past the family. -/
lemma natTransOfResolutions_app_of_prop {B D : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ⟶ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ e L hL = e K hK ≫ G.map (DerivedCategory.Q.map f))
    (K : CochainComplex B ℤ) (hK : P K) :
    (natTransOfResolutions P hP F G e he).app (DerivedCategory.Q.obj K) = e K hK := by
  rw [natTransOfResolutions_app]
  have h := map_comp_eq_of_resolutions P hP F G e he
    (resolutionComplex P hP (DerivedCategory.Q.obj K)) K
    (resolutionComplex_prop P hP _) hK
    (resolutionIso P hP (DerivedCategory.Q.obj K)).hom
  rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- On a pair of K-flat complexes both derived tensor products are computed by the ordinary
total tensor product, so they agree there. -/
noncomputable def kFlatDerivedTensorIso (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  (canonicalDerivedTensorProduct R).comparison K L hK hL ≪≫
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensorIso K L hL).symm

/-- The K-flat comparison of the two derived tensor products is natural in both variables. -/
private lemma kFlatDerivedTensorIso_naturality
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    ((canonicalDerivedTensorProduct R).tensor.map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫ (kFlatDerivedTensorIso K' L' hK' hL').hom =
      (kFlatDerivedTensorIso K L hK hL).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.map
          (show (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L') from
            (DerivedCategory.Q.map f, DerivedCategory.Q.map g)) := by
  have hc := (canonicalDerivedTensorProduct R).comparison_naturality f g hK hK' hL hL'
  have ht := (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensorIso_naturality
    f g hL hL'
  dsimp only [kFlatDerivedTensorIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_mono ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensorIso
    K' L' hL').hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ht, Iso.inv_hom_id_assoc]
  exact hc

/-- The K-flat comparison of the two derived tensor products is natural in the first
variable. -/
@[reassoc]
private lemma kFlatDerivedTensorIso_naturality_left
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : K ⟶ K') (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) :
    ((canonicalDerivedTensorProduct R).tensor.map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫ (kFlatDerivedTensorIso K' L hK' hL).hom =
      (kFlatDerivedTensorIso K L hK hL).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.map
          (show (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L) from
            (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L))) := by
  simpa using kFlatDerivedTensorIso_naturality f (𝟙 L) hK hK' hL hL

/-- The K-flat comparison of the two derived tensor products is natural in the second
variable. -/
@[reassoc]
private lemma kFlatDerivedTensorIso_naturality_right
    (K : CochainComplex (ModuleCat.{u} R) ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : L ⟶ L') (hK : K.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫ (kFlatDerivedTensorIso K L' hK hL').hom =
      (kFlatDerivedTensorIso K L hK hL).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.map
          (show (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L') from
            (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map g)) := by
  simpa using kFlatDerivedTensorIso_naturality (𝟙 K) g hK hK hL hL'

/-- The comparison of the two derived tensor products in the second variable, descended from
K-flat complexes to all of `D(R)`, with the first variable a K-flat complex. -/
private noncomputable def tensorNatTransRight (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) :
    (canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K) ⟶
      (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).obj
        (DerivedCategory.Q.obj K) :=
  natTransOfResolutions (kFlatProp R) exists_kFlat
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).obj
      (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIso K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIso_naturality_right K g hK hL hL')

/-- The component formula for the second-variable descent. -/
private lemma tensorNatTransRight_app (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (tensorNatTransRight K hK).app X =
      ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K)).map
          (resolutionIso (kFlatProp R) exists_kFlat X).inv ≫
        (kFlatDerivedTensorIso K (resolutionComplex (kFlatProp R) exists_kFlat X) hK
          (resolutionComplex_prop (kFlatProp R) exists_kFlat X)).hom ≫
        ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).obj
            (DerivedCategory.Q.obj K)).map
          (resolutionIso (kFlatProp R) exists_kFlat X).hom :=
  natTransOfResolutions_app (kFlatProp R) exists_kFlat
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).obj
      (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIso K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIso_naturality_right K g hK hL hL') X

/-- The second-variable descent is the K-flat comparison at a K-flat second complex. -/
private lemma tensorNatTransRight_app_kFlat (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    (tensorNatTransRight K hK).app (DerivedCategory.Q.obj L) =
      (kFlatDerivedTensorIso K L hK hL).hom :=
  natTransOfResolutions_app_of_prop (kFlatProp R) exists_kFlat
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K))
    ((curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).obj
      (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatDerivedTensorIso K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatDerivedTensorIso_naturality_right K g hK hL hL') L hL

/-- Every component of the second-variable descent is an isomorphism. -/
private instance tensorNatTransRight_app_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) (X : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((tensorNatTransRight K hK).app X) := by
  rw [tensorNatTransRight_app]
  infer_instance

/-- The second-variable descent is an isomorphism of functors. -/
private instance tensorNatTransRight_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) : IsIso (tensorNatTransRight K hK) :=
  NatIso.isIso_of_isIso_app _

/-- The second-variable descents are natural in chain maps between K-flat first complexes:
checked componentwise, where the resolution isomorphism of the component cancels and leaves the
first-variable K-flat naturality. -/
@[reassoc]
private lemma tensorNatTransRight_naturality {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ K') (hK : K.KFlat) (hK' : K'.KFlat) :
    (canonicalDerivedTensorProduct R).tensor.map (DerivedCategory.Q.map f) ≫
        tensorNatTransRight K' hK' =
      tensorNatTransRight K hK ≫
        (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).map
          (DerivedCategory.Q.map f) := by
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app, tensorNatTransRight_app, tensorNatTransRight_app]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [curry_obj_obj_map, curry_obj_map_app, Prod.mkHom]
  rw [kFlatDerivedTensorIso_naturality_left_assoc _ f hK hK'
    (resolutionComplex_prop (kFlatProp R) exists_kFlat X)]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  simp

/-- The comparison of the two derived tensor products, descended in the first variable too:
a morphism of bifunctors, in curried form. -/
private noncomputable def tensorNatTrans (R : Type u) [CommRing R] :
    (canonicalDerivedTensorProduct R).tensor ⟶
      curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor :=
  natTransOfResolutions (kFlatProp R) exists_kFlat
    (canonicalDerivedTensorProduct R).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor)
    (fun K hK => tensorNatTransRight K hK)
    (fun _K _K' hK hK' f => tensorNatTransRight_naturality f hK hK')

/-- The component formula for the first-variable descent. -/
private lemma tensorNatTrans_app (X : DerivedCategory (ModuleCat.{u} R)) :
    (tensorNatTrans R).app X =
      (canonicalDerivedTensorProduct R).tensor.map
          (resolutionIso (kFlatProp R) exists_kFlat X).inv ≫
        tensorNatTransRight (resolutionComplex (kFlatProp R) exists_kFlat X)
          (resolutionComplex_prop (kFlatProp R) exists_kFlat X) ≫
        (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor).map
          (resolutionIso (kFlatProp R) exists_kFlat X).hom :=
  natTransOfResolutions_app (kFlatProp R) exists_kFlat
    (canonicalDerivedTensorProduct R).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor)
    (fun K hK => tensorNatTransRight K hK)
    (fun _K _K' hK hK' f => tensorNatTransRight_naturality f hK hK') X

/-- The first-variable descent is the second-variable descent at a K-flat first complex. -/
private lemma tensorNatTrans_app_kFlat (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) :
    (tensorNatTrans R).app (DerivedCategory.Q.obj K) = tensorNatTransRight K hK :=
  natTransOfResolutions_app_of_prop (kFlatProp R) exists_kFlat
    (canonicalDerivedTensorProduct R).tensor
    (curry.obj (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor)
    (fun K hK => tensorNatTransRight K hK)
    (fun _K _K' hK hK' f => tensorNatTransRight_naturality f hK hK') K hK

/-- Every component of the first-variable descent is an isomorphism of functors. -/
private instance tensorNatTrans_app_isIso (X : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((tensorNatTrans R).app X) := by
  rw [tensorNatTrans_app]
  infer_instance

/-- The first-variable descent is an isomorphism. -/
private instance tensorNatTrans_isIso : IsIso (tensorNatTrans R) :=
  NatIso.isIso_of_isIso_app _

/-- **The canonical derived tensor product of [stacks 0FNQ] and the tensor half of the
tensor--Hom bundle of [stacks 0A63] agree as bifunctors on `D(R)`.**

`Dualizing.derivedHomAdjunctionTensorIso` identifies the two object by object.  This is the
bifunctorial upgrade: one isomorphism of functors `D(R) × D(R) ⥤ D(R)`, hence natural in both
variables simultaneously.  Its value on a pair of K-flat complexes is the comparison of the two
K-flat characterizations, `Dualizing.derivedHomAdjunctionTensorNatIso_hom_app_kFlat`. -/
@[no_expose] noncomputable def derivedHomAdjunctionTensorNatIso (R : Type u) [CommRing R] :
    uncurry.obj (canonicalDerivedTensorProduct R).tensor ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor :=
  uncurry.mapIso (asIso (tensorNatTrans R)) ≪≫ currying.counitIso.app _

/-- The bifunctorial comparison is the K-flat comparison on a pair of K-flat complexes. -/
lemma derivedHomAdjunctionTensorNatIso_hom_app_kFlat
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (derivedHomAdjunctionTensorNatIso R).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (kFlatDerivedTensorIso K L hK hL).hom := by
  dsimp only [derivedHomAdjunctionTensorNatIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom]
  rw [NatTrans.comp_app]
  simp only [currying_counitIso_hom_app_app, uncurry_map_app]
  rw [tensorNatTrans_app_kFlat K hK, tensorNatTransRight_app_kFlat K L hK hL]
  exact Category.comp_id _

end Dualizing

end
