module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIsoGeneral

/-!
# Any two derived tensor products of [stacks 068I] agree as bifunctors

A derived tensor product on `D(R)` in the sense of [stacks 068I] is recorded by
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`: a bifunctor on the derived category
together with a comparison with the ordinary total tensor product of K-flat representatives,
natural in both representatives, and exactness in each variable.

Any two such data are isomorphic as functors `D(R) ⥤ D(R) ⥤ D(R)`, naturally in both variables at
once. In particular the canonical derived tensor product over `R` itself and the
universe-polymorphic one at the ring's own module universe agree as bifunctors; the latter is
built over `ULift R` and transported along the scalar equivalence, so it is **not**
`CochainComplex.DerivedTensor.DerivedTensorProduct.toGeneral` of the former.

## Main results

* `Dualizing.uniqueDerivedTensorGeneralNatIso` — **the uniqueness statement**: any two derived
  tensor products of [stacks 068I] at one universe are isomorphic as bifunctors.
* `Dualizing.uniqueDerivedTensorGeneralNatIso_app_app_kFlat` — its value at a pair of K-flat
  complexes is the composite of the two data's own K-flat comparisons.
* `Dualizing.derivedHomAdjunctionTensorNatIsoCompare` — the consequence: the tensor of
  `StacksDraft.DerivedHom.derivedHomAdjunction`, the same-universe model of [stacks 0A63], and
  the tensor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` at the ring's own module
  universe agree as bifunctors on the product category.

## Implementation notes

Both data carry a K-flat comparison with the *same* target, the localization of the ordinary
total tensor product, and both comparisons are natural in chain maps between K-flat complexes.
So the two bifunctors are canonically identified on K-flat pairs, by
`Dualizing.kFlatGeneralCompare`, and the identification descends one variable at a time with
`ModuleSystemRlimTensor.natTransOfResolutions`, exactly as in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIso`: that instrument
descends in a single variable and its target category is arbitrary, so the second pass is run
with the target taken to be the functor category `D(R) ⥤ D(R)`.

Working with transformations rather than isomorphisms throughout is what keeps the component
formula `ModuleSystemRlimTensor.natTransOfResolutions_app` available, which is what exhibits
every component as a composite of isomorphisms.

Stating the comparison for two arbitrary data of [stacks 068I], rather than for the two canonical
ones, is what keeps the K-flatness hypotheses and the comparison targets *syntactically* the same
on both sides.  At the ring's own module universe the universe-polymorphic K-flatness predicate
`CochainComplex.DerivedTensor.IsKFlat` and the comparison target
`CochainComplex.DerivedTensor.tensorComplex` agree with the one-universe
`CochainComplex.KFlat` and `K ⊗ L` only up to an unfolding that `rw` and `simp` do not perform,
so a comparison written directly between
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` and
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral` elaborates but cannot be
rewritten in.  The instantiation is done once, at the end, through
`CochainComplex.DerivedTensor.DerivedTensorProduct.toGeneral`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
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

/-- The universe-polymorphic K-flatness of [stacks 068I] as a predicate on cochain complexes,
spelled once so that every appeal to the descent lemmas of `ModuleSystemRlimTensor` uses the same
resolving class. -/
private abbrev isKFlatProp (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ → Prop := fun L => IsKFlat.{u, u} L

/-- Every cochain complex of `R`-modules has a K-flat resolution: [stacks 06Y4], in the shape the
descent lemmas of `ModuleSystemRlimTensor` ask for. -/
private lemma exists_isKFlat (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ) (s : L ⟶ M), isKFlatProp R L ∧ QuasiIso s := by
  obtain ⟨K, f, hK, -, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} M
  exact ⟨K, f, hK, hf⟩

variable (T₁ T₂ : DerivedTensorProductGeneral.{u, u} R)

/-- On a pair of K-flat complexes both derived tensor products are computed by the ordinary total
tensor product, so they agree there. -/
noncomputable def kFlatGeneralCompare (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (hL : IsKFlat.{u, u} L) :
    (T₁.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      (T₂.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) :=
  T₁.comparison K L hK hL ≪≫ (T₂.comparison K L hK hL).symm

/-- Two isomorphisms into a common target, each natural against the same map `m`, compose to an
isomorphism `X ≅ Y` natural against the two source maps. -/
private lemma comp_symm_hom_naturality {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (c₁ : X ≅ Z) (c₁' : X' ≅ Z') (c₂ : Y ≅ Z) (c₂' : Y' ≅ Z') (a : X ⟶ X') (b : Y ⟶ Y')
    (m : Z ⟶ Z') (hc : a ≫ c₁'.hom = c₁.hom ≫ m) (hg : b ≫ c₂'.hom = c₂.hom ≫ m) :
    a ≫ (c₁' ≪≫ c₂'.symm).hom = (c₁ ≪≫ c₂.symm).hom ≫ b := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_mono c₂'.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc, hc]

/-- The K-flat comparison of two derived tensor products is natural in the first variable. -/
@[reassoc]
private lemma kFlatGeneralCompare_naturality_left
    {K K' : CochainComplex (ModuleCat.{u} R) ℤ} (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : K ⟶ K') (hK : IsKFlat.{u, u} K) (hK' : IsKFlat.{u, u} K')
    (hL : IsKFlat.{u, u} L) :
    (T₁.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
          (kFlatGeneralCompare T₁ T₂ K' L hK' hL).hom =
      (kFlatGeneralCompare T₁ T₂ K L hK hL).hom ≫
        (T₂.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) := by
  have hc := T₁.comparison_naturality f (𝟙 L) hK hK' hL hL
  have hg := T₂.comparison_naturality f (𝟙 L) hK hK' hL hL
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hc hg
  exact comp_symm_hom_naturality _ _ _ _ _ _ _ hc hg

/-- The K-flat comparison of two derived tensor products is natural in the second variable. -/
@[reassoc]
private lemma kFlatGeneralCompare_naturality_right
    (K : CochainComplex (ModuleCat.{u} R) ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : L ⟶ L') (hK : IsKFlat.{u, u} K) (hL : IsKFlat.{u, u} L)
    (hL' : IsKFlat.{u, u} L') :
    (T₁.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
          (kFlatGeneralCompare T₁ T₂ K L' hK hL').hom =
      (kFlatGeneralCompare T₁ T₂ K L hK hL).hom ≫
        (T₂.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) := by
  have hc := T₁.comparison_naturality (𝟙 K) g hK hK hL hL'
  have hg := T₂.comparison_naturality (𝟙 K) g hK hK hL hL'
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hc hg
  exact comp_symm_hom_naturality _ _ _ _ _ _ _ hc hg

/-- The comparison in the second variable, descended from K-flat complexes to all of `D(R)`, with
the first variable a K-flat complex. -/
private noncomputable def generalNatTransRight (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) :
    T₁.tensor.obj (DerivedCategory.Q.obj K) ⟶ T₂.tensor.obj (DerivedCategory.Q.obj K) :=
  natTransOfResolutions (isKFlatProp R) exists_isKFlat
    (T₁.tensor.obj (DerivedCategory.Q.obj K)) (T₂.tensor.obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatGeneralCompare T₁ T₂ K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatGeneralCompare_naturality_right T₁ T₂ K g hK hL hL')

/-- The component formula for the second-variable descent. -/
private lemma generalNatTransRight_app (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (X : DerivedCategory (ModuleCat.{u} R)) :
    (generalNatTransRight T₁ T₂ K hK).app X =
      (T₁.tensor.obj (DerivedCategory.Q.obj K)).map
          (resolutionIso (isKFlatProp R) exists_isKFlat X).inv ≫
        (kFlatGeneralCompare T₁ T₂ K (resolutionComplex (isKFlatProp R) exists_isKFlat X) hK
          (resolutionComplex_prop (isKFlatProp R) exists_isKFlat X)).hom ≫
        (T₂.tensor.obj (DerivedCategory.Q.obj K)).map
          (resolutionIso (isKFlatProp R) exists_isKFlat X).hom :=
  natTransOfResolutions_app (isKFlatProp R) exists_isKFlat
    (T₁.tensor.obj (DerivedCategory.Q.obj K)) (T₂.tensor.obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatGeneralCompare T₁ T₂ K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatGeneralCompare_naturality_right T₁ T₂ K g hK hL hL') X

/-- The second-variable descent is the K-flat comparison at a K-flat second complex. -/
private lemma generalNatTransRight_app_kFlat (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (hL : IsKFlat.{u, u} L) :
    (generalNatTransRight T₁ T₂ K hK).app (DerivedCategory.Q.obj L) =
      (kFlatGeneralCompare T₁ T₂ K L hK hL).hom :=
  natTransOfResolutions_app_of_prop (isKFlatProp R) exists_isKFlat
    (T₁.tensor.obj (DerivedCategory.Q.obj K)) (T₂.tensor.obj (DerivedCategory.Q.obj K))
    (fun L hL => (kFlatGeneralCompare T₁ T₂ K L hK hL).hom)
    (fun _L _L' hL hL' g => kFlatGeneralCompare_naturality_right T₁ T₂ K g hK hL hL') L hL

/-- Every component of the second-variable descent is an isomorphism. -/
private instance generalNatTransRight_app_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (X : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((generalNatTransRight T₁ T₂ K hK).app X) := by
  rw [generalNatTransRight_app]
  infer_instance

/-- The second-variable descent is an isomorphism of functors. -/
private instance generalNatTransRight_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) : IsIso (generalNatTransRight T₁ T₂ K hK) :=
  NatIso.isIso_of_isIso_app _

/-- The second-variable descents are natural in chain maps between K-flat first complexes:
checked componentwise, where the resolution isomorphism of the component cancels and leaves the
first-variable K-flat naturality. -/
@[reassoc]
private lemma generalNatTransRight_naturality {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ K') (hK : IsKFlat.{u, u} K) (hK' : IsKFlat.{u, u} K') :
    T₁.tensor.map (DerivedCategory.Q.map f) ≫ generalNatTransRight T₁ T₂ K' hK' =
      generalNatTransRight T₁ T₂ K hK ≫ T₂.tensor.map (DerivedCategory.Q.map f) := by
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app, generalNatTransRight_app,
    generalNatTransRight_app]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  rw [kFlatGeneralCompare_naturality_left_assoc T₁ T₂ _ f hK hK'
    (resolutionComplex_prop (isKFlatProp R) exists_isKFlat X)]
  rw [← NatTrans.naturality]

/-- The comparison of the two derived tensor products, descended in the first variable too: a
morphism of bifunctors. -/
private noncomputable def generalNatTrans : T₁.tensor ⟶ T₂.tensor :=
  natTransOfResolutions (isKFlatProp R) exists_isKFlat T₁.tensor T₂.tensor
    (fun K hK => generalNatTransRight T₁ T₂ K hK)
    (fun _K _K' hK hK' f => generalNatTransRight_naturality T₁ T₂ f hK hK')

/-- The component formula for the first-variable descent. -/
private lemma generalNatTrans_app (X : DerivedCategory (ModuleCat.{u} R)) :
    (generalNatTrans T₁ T₂).app X =
      T₁.tensor.map (resolutionIso (isKFlatProp R) exists_isKFlat X).inv ≫
        generalNatTransRight T₁ T₂ (resolutionComplex (isKFlatProp R) exists_isKFlat X)
          (resolutionComplex_prop (isKFlatProp R) exists_isKFlat X) ≫
        T₂.tensor.map (resolutionIso (isKFlatProp R) exists_isKFlat X).hom :=
  natTransOfResolutions_app (isKFlatProp R) exists_isKFlat T₁.tensor T₂.tensor
    (fun K hK => generalNatTransRight T₁ T₂ K hK)
    (fun _K _K' hK hK' f => generalNatTransRight_naturality T₁ T₂ f hK hK') X

/-- The first-variable descent is the second-variable descent at a K-flat first complex. -/
private lemma generalNatTrans_app_kFlat (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) :
    (generalNatTrans T₁ T₂).app (DerivedCategory.Q.obj K) = generalNatTransRight T₁ T₂ K hK :=
  natTransOfResolutions_app_of_prop (isKFlatProp R) exists_isKFlat T₁.tensor T₂.tensor
    (fun K hK => generalNatTransRight T₁ T₂ K hK)
    (fun _K _K' hK hK' f => generalNatTransRight_naturality T₁ T₂ f hK hK') K hK

/-- Every component of the first-variable descent is an isomorphism of functors. -/
private instance generalNatTrans_app_isIso (X : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((generalNatTrans T₁ T₂).app X) := by
  rw [generalNatTrans_app]
  infer_instance

/-- The first-variable descent is an isomorphism. -/
private instance generalNatTrans_isIso : IsIso (generalNatTrans T₁ T₂) :=
  NatIso.isIso_of_isIso_app _

/-- **Any two derived tensor products of [stacks 068I] agree as bifunctors on `D(R)`.**
`Stacks.Duality.derivedTensorGeneralCompare` and `Dualizing.derivedTensorGeneralObjIso` identify
them object by object, from chosen K-flat resolutions.  This is the bifunctorial upgrade: one
isomorphism of functors `D(R) ⥤ D(R) ⥤ D(R)`, hence natural in both variables simultaneously.
Its value on a pair of K-flat complexes is `Dualizing.kFlatGeneralCompare`, the composite of the
two data's own K-flat comparisons. -/
@[no_expose] noncomputable def uniqueDerivedTensorGeneralNatIso : T₁.tensor ≅ T₂.tensor :=
  asIso (generalNatTrans T₁ T₂)

/-- The bifunctorial comparison is the K-flat comparison on a pair of K-flat complexes. -/
lemma uniqueDerivedTensorGeneralNatIso_app_app_kFlat
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsKFlat.{u, u} K)
    (hL : IsKFlat.{u, u} L) :
    ((uniqueDerivedTensorGeneralNatIso T₁ T₂).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (kFlatGeneralCompare T₁ T₂ K L hK hL).hom := by
  dsimp only [uniqueDerivedTensorGeneralNatIso, asIso_hom]
  rw [generalNatTrans_app_kFlat T₁ T₂ K hK, generalNatTransRight_app_kFlat T₁ T₂ K L hK hL]

/-- The canonical derived tensor product over `R` and the universe-polymorphic one at the ring's
own module universe agree as bifunctors.  The second is transported along the scalar equivalence
from the derived tensor product over `ULift R`, so this is an instance of
`Dualizing.uniqueDerivedTensorGeneralNatIso` and not a definitional identity. -/
@[no_expose] noncomputable def canonicalDerivedTensorGeneralNatIso (R : Type u) [CommRing R] :
    (canonicalDerivedTensorProduct R).tensor ≅
      (canonicalDerivedTensorProductGeneral.{u, u} R).tensor :=
  uniqueDerivedTensorGeneralNatIso (canonicalDerivedTensorProduct R).toGeneral
    (canonicalDerivedTensorProductGeneral.{u, u} R)

/-- **The two spellings of the derived tensor product of [stacks 0A63] at one universe agree as
bifunctors.**  The tensor of `StacksDraft.DerivedHom.derivedHomAdjunction`, the same-universe
model, and the tensor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` at the ring's own
module universe are isomorphic as functors on the product category `D(R) × D(R)`.

The two are connected to the two canonical derived tensor products of [stacks 068I] by
`Dualizing.derivedHomAdjunctionTensorNatIso` and
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`, each natural in both variables, and those
two canonical data are identified by `Dualizing.canonicalDerivedTensorGeneralNatIso`. -/
@[no_expose] noncomputable def derivedHomAdjunctionTensorNatIsoCompare (R : Type u)
    [CommRing R] :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R).tensor :=
  (derivedHomAdjunctionTensorNatIso R).symm ≪≫
    uncurry.mapIso (canonicalDerivedTensorGeneralNatIso R) ≪≫
    derivedHomAdjunctionTensorNatIsoGeneral.{u, u} R

end Dualizing

end
