module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Trifunctor
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.KFlatHomotopyTensor

@[expose] public noncomputable section

/-!
# The derived tensor product

Let `R` be a commutative ring. This file constructs the derived tensor product on the derived
category `D(R)` of complexes of `R`-modules, and establishes its structural properties: it is
exact in each variable, commutative up to a canonical Koszul symmetry, and associative up to a
canonical isomorphism natural in all three variables.

The construction rests on K-flat resolutions. Tensoring an arbitrary complex with a
quasi-isomorphism between K-flat complexes again gives a quasi-isomorphism, so the tensor-total
functor attached to a K-flat complex descends through the localization at quasi-isomorphisms,
and the resulting functor on `D(R)` does not depend on the chosen resolution.

## Main definitions

* `CochainComplex.DerivedTensor.derivedTensorProduct`: the exact endofunctor `- ⊗ˡ[R] M` of the
  derived category, obtained from a K-flat resolution of a representative of `M`.
* `CochainComplex.DerivedTensor.DerivedTensorProduct`: a derived tensor bifunctor on `D(R)`,
  packaged with its comparison with the ordinary total tensor product of K-flat complexes, its
  exactness in both variables and its unit `R[0]`.
* `CochainComplex.DerivedTensor.DerivedTensorProductGeneral`: the same interface with the module
  universe left independent of the universe of `R`, using the bare module tensor bifunctor
  `CochainComplex.DerivedTensor.moduleTensor` in place of a monoidal structure.
* `CochainComplex.DerivedTensor.IsKoszulSwap`: the property of a map `K ⊗ L ⟶ L ⊗ K` of being
  the ordinary braiding times the Koszul sign `(-1) ^ (p * q)` on each homogeneous summand.
* `CochainComplex.DerivedTensor.KoszulBraiding`: a natural symmetry of a derived tensor product
  whose representatives on K-flat complexes are Koszul swaps.
* `CochainComplex.DerivedTensor.SymmetricDerivedTensorProduct`: a derived tensor product together
  with its Koszul symmetry.

## Main results

* `CochainComplex.DerivedTensor.quasiIso_tleftCochain_map`: left tensoring an arbitrary complex
  with a quasi-isomorphism between K-flat complexes preserves the quasi-isomorphism.
* `CochainComplex.DerivedTensor.derivedTensorProduct_commShift`: the derived tensor product with
  a fixed object commutes with the shift functors.
* `CochainComplex.DerivedTensor.derivedTensorProduct_isTriangulated`: the derived tensor product
  with a fixed object is an exact functor of triangulated categories.
* `CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution`: any K-flat
  resolution of any representative computes the derived tensor product, by a natural isomorphism
  uniquely determined by its pullback to the homotopy category.
* `CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct`: the canonical derived
  tensor bifunctor together with its canonical, bifunctorial Koszul symmetry.
* `CochainComplex.DerivedTensor.derivedTensorProduct_associator`: the canonical three-variable
  natural associativity isomorphism for the derived tensor product.
* `CochainComplex.DerivedTensor.derivedAssociator`,
  `CochainComplex.DerivedTensor.derivedAssociatorIso` and
  `CochainComplex.DerivedTensor.derivedAssociatorIso_comparison`: the same associator *named*
  rather than existentially quantified, together with the law on K-flat representatives that
  determines it.  A coherence of some other structure against the associator cannot be stated
  against the existential form, so these are what such a statement has to cite.
* `CochainComplex.DerivedTensor.derivedAssociatorIso_naturality`: naturality of that named
  associator in all three arguments.

## Implementation notes

The endofunctor `derivedTensorProduct M` is obtained by choosing a K-flat resolution of a
representative of `M`, applying the tensor-total functor `Tright` on the homotopy category, and
descending it through the localization at quasi-isomorphisms. The choice is harmless up to
isomorphism by `quasiIso_tleftCochain_map`, and the derived-category universe is left independent
of the module universe, so the construction applies in particular to
`HasDerivedCategory.standard` without identifying distinct localizations.

Mathlib does not currently package the unbounded derived tensor product as a bifunctor on the
derived category. We therefore characterize it by natural comparison isomorphisms with the
ordinary total tensor product on pairs of K-flat complexes, which is what
`DerivedTensorProduct` records; its symmetry is a natural isomorphism of bifunctors, so
functoriality in both complexes is part of its type. The bifunctor itself is built by localizing
the tensor product of the homotopy category along the K-flat objects, which form a triangulated
subcategory on which the quasi-isomorphisms admit left resolutions, hence a localized
equivalence onto `D(R)`.

Canonicality of the associator is expressed by computing it on K-flat representatives: under the
comparison isomorphism it is the standard associator of complexes. Naturality in all three
variables is recorded explicitly.

`derivedTensorProduct_associator` states that content existentially, which is the right form for
the tag but the wrong one for a consumer that has to *name* the associator — for instance to say
that a lax monoidal comparison is compatible with it. The associator it quantifies over is
`derivedAssociator`, which is therefore public; `derivedAssociatorIso` is its component at a
triple of objects, and `derivedAssociatorIso_comparison` is the determining law. Naturality is
naturality of `derivedAssociator` at a triple of morphisms and needs no separate statement.

Throughout, modules live in the universe of `R`. Mathlib provides the monoidal structure on
`ModuleCat` only when the module universe agrees with the universe of `R`, and both
`CochainComplex.KFlat` and `TotalTensorComplex.tright_isTriangulated` are stated under that
restriction, so this is the form in which `Tright` and K-flatness are simultaneously available.
The universe-polymorphic interface `DerivedTensorProductGeneral` sidesteps this by using
`moduleTensor`, which needs no monoidal unit; in the ring's universe it is definitionally the
monoidal product, so `DerivedTensorProduct.toGeneral` preserves the bifunctor and its
comparisons.

## References

* [The Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [The Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [The Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [The Stacks Project, Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ)
-/

open CategoryTheory

universe u v w

open CochainComplex.KFlatHomotopyTensor

namespace CochainComplex.DerivedTensor

/-! ### The canonical symmetric derived tensor bifunctor and its associator -/

section Canonical

open Limits MonoidalCategory Functor

variable {R : Type u} [CommRing R]

/-- The derived category of `R`-modules. -/
public abbrev DObj (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] := DerivedCategory (ModuleCat.{u} R)

/-- A derived tensor product on `D(R)`, characterized by its canonical comparison with the
ordinary total tensor product whenever both complexes are K-flat, exactness in both variables,
and the unit `R[0]`. -/
public structure DerivedTensorProduct (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] where
  /-- The bifunctor `- ⊗_R^L -` on the derived category. -/
  tensor : DObj R ⥤ (DObj R ⥤ DObj R)
  /-- On K-flat representatives, derived tensor product is computed by ordinary total tensor
  product. -/
  comparison (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L)
  /-- The comparison with tensor products of K-flat representatives is natural in both
  variables. -/
  comparison_naturality {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
          (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
          (comparison K' L' hK' hL').hom =
        (comparison K L hK hL).hom ≫
          DerivedCategory.Q.map (HomologicalComplex.tensorHom f g)
  /-- Tensoring in the first variable commutes with shifts. -/
  commShift_left : ∀ L, (tensor.flip.obj L).CommShift ℤ
  /-- Tensoring in the second variable commutes with shifts. -/
  commShift_right : ∀ K, (tensor.obj K).CommShift ℤ
  /-- Tensoring in the first variable is exact. -/
  exact_left : ∀ L, letI := commShift_left L; (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the second variable is exact. -/
  exact_right : ∀ K, letI := commShift_right K; (tensor.obj K).IsTriangulated
  /-- The complex `R[0]` is a right unit for the derived tensor product, naturally in `K`. -/
  rightUnitor :
    tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      𝟭 (DObj R)
  /-- On a K-flat complex, the derived right unit agrees with the ordinary right unitor
  through the K-flat comparison. -/
  rightUnitor_comparison (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (hK : K.KFlat)
      (hUnit : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).KFlat) :
    (comparison K (𝟙_ _) hK hUnit).hom ≫
        DerivedCategory.Q.map (MonoidalCategory.rightUnitor K).hom =
      rightUnitor.hom.app (DerivedCategory.Q.obj K)

attribute [instance] DerivedTensorProduct.commShift_left DerivedTensorProduct.commShift_right
  DerivedTensorProduct.exact_left DerivedTensorProduct.exact_right

/-- The ordinary tensor bifunctor on modules in an arbitrary universe containing `R`.
This does not require a monoidal unit in `ModuleCat`. -/
public def moduleTensor (R : Type u) [CommRing R] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M :=
    { obj := fun N ↦ ModuleCat.of R (TensorProduct R M N)
      map := fun f ↦ ModuleCat.ofHom (f.hom.lTensor M)
      map_id := by intros; ext; rfl
      map_comp := by intros; ext; rfl }
  map f :=
    { app := fun N ↦ ModuleCat.ofHom (f.hom.rTensor N)
      naturality := by intros; ext; rfl }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

/-- The tensor product bifunctor is additive in its first variable. -/
public instance (R : Type u) [CommRing R] : (moduleTensor.{u, v} R).Additive where
  map_add {_ _ f g} := NatTrans.ext <| funext fun L =>
    ModuleCat.hom_ext (LinearMap.rTensor_add L f.hom g.hom)

/-- Tensoring with a fixed module on the left is additive. -/
public instance (M : ModuleCat.{max u v} R) : ((moduleTensor R).obj M).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.lTensor_add M f.hom g.hom)

/-- The total tensor product of complexes, with its usual Koszul differential, in an
independent module universe. -/
@[sga "4 XVII 1.1.10"]
public noncomputable abbrev tensorComplex
    (K L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat.{max u v} R) ℤ :=
  HomologicalComplex.mapBifunctor K L (moduleTensor R) (ComplexShape.up ℤ)

/-- `CochainComplex.KFlat`, under the name used by consumers that state K-flatness against
`CochainComplex.DerivedTensor.moduleTensor` rather than a monoidal product. -/
public abbrev IsKFlat (K : CochainComplex (ModuleCat.{max u v} R) ℤ) : Prop := K.KFlat

/-- A derived tensor bifunctor on modules in an independent universe, characterized by
natural comparison with ordinary total tensor products of K-flat representatives and exactness
in both variables. The comparison uses the actual module tensor product, so this does not
stand for an arbitrary exact bifunctor. -/
public structure DerivedTensorProductGeneral (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{max u v} R)] where
  /-- The derived tensor bifunctor. -/
  tensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R)
  /-- K-flat representatives compute the derived tensor product. -/
  comparison (K L : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (hK : K.KFlat) (hL : L.KFlat) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (tensorComplex K L)
  /-- The comparison is natural in both representatives. -/
  comparison_naturality {K K' L L' : CochainComplex (ModuleCat.{max u v} R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
          (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
          (comparison K' L' hK' hL').hom =
        (comparison K L hK hL).hom ≫
          DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g (moduleTensor R) (ComplexShape.up ℤ))
  /-- Tensoring in the first variable commutes with shifts. -/
  commShift_left : ∀ L, (tensor.flip.obj L).CommShift ℤ
  /-- Tensoring in the second variable commutes with shifts. -/
  commShift_right : ∀ K, (tensor.obj K).CommShift ℤ
  /-- Tensoring in the first variable is exact. -/
  exact_left : ∀ L, letI := commShift_left L; (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the second variable is exact. -/
  exact_right : ∀ K, letI := commShift_right K; (tensor.obj K).IsTriangulated

attribute [instance] DerivedTensorProductGeneral.commShift_left
  DerivedTensorProductGeneral.commShift_right DerivedTensorProductGeneral.exact_left
  DerivedTensorProductGeneral.exact_right

/-- View the existing derived tensor product in the universe-polymorphic interface.
The tensor bifunctor and the comparisons agree definitionally. -/
public def DerivedTensorProduct.toGeneral [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) :
    DerivedTensorProductGeneral.{u, u} R where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  commShift_left := T.commShift_left
  commShift_right := T.commShift_right
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- A morphism `K ⊗ L ⟶ L ⊗ K` is the Koszul swap if, on the summand
`K^p ⊗ L^q`, it is the ordinary braiding multiplied by `(-1) ^ (p * q)`. -/
public def IsKoszulSwap (K L : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⊗ L ⟶ L ⊗ K) :
    Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj K L p q n h ≫ f.f n =
      (p * q).negOnePow •
        ((β_ (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h))

/-- A natural symmetry of a derived tensor product which, under its comparison with the tensor
product of K-flat representatives, is represented by the Koszul swap. -/
public structure KoszulBraiding [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) where
  /-- The symmetry, natural in both derived complexes. -/
  iso : T.tensor ≅ T.tensor.flip
  /-- On K-flat representatives, the symmetry is induced by the signed interchange map. -/
  isKoszul (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    ∃ f : K ⊗ L ⟶ L ⊗ K, IsKoszulSwap K L f ∧
      DerivedCategory.Q.map f =
        (T.comparison K L hK hL).inv ≫
          (iso.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
          (T.comparison L K hL hK).hom

/-- A derived tensor product together with its natural Koszul symmetry. -/
public structure SymmetricDerivedTensorProduct (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] where
  /-- The derived tensor product bifunctor and its K-flat comparison. -/
  tensorProduct : DerivedTensorProduct R
  /-- The natural symmetry, represented by the Koszul swap on K-flat complexes. -/
  braiding : KoszulBraiding tensorProduct

private lemma homotopy_quasiIso_iff_isIso_Qh {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    {X Y : KC R} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) f ↔
      IsIso ((DerivedCategory.Qh (C := ModuleCat.{u} R)).map f) :=
  (DerivedCategory.isIso_Qh_map_iff f).symm

attribute [local instance] homotopyTensorLifting

/-- The tensor product on the homotopy category of complexes of `R`-modules, obtained by
descending the total tensor product of complexes along the homotopy-category quotient. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[no_expose, sga "4 XVII 1.1.6.2" "special case", sga "4 XVII 4.1.6" "special case"]
public noncomputable def homotopyCategoryTensor (R : Type u) [CommRing R] :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
        HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  homotopyTensor R

/-- `CochainComplex.DerivedTensor.homotopyCategoryTensor` lifts the total tensor product of
complexes through the homotopy-category quotient in both variables. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[instance_reducible, no_expose]
public noncomputable def homotopyCategoryTensorLifting (R : Type u) [CommRing R] :
    Localization.Lifting₂
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (homotopyCategoryTensor R) :=
  homotopyTensorLifting R

private noncomputable abbrev kFlatQ (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    (KFlatObjects R).FullSubcategory ⥤ DObj R :=
  (KFlatObjects R).ι ⋙ DerivedCategory.Qh

private lemma kFlatQ_isLocalization (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    (kFlatQ R).IsLocalization (KFlatQuasiIso R) := by
  have := kFlatLocalizer_isLocalizedEquivalence (R := R)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer R) (DerivedCategory.Qh (C := ModuleCat.{u} R))

attribute [local instance] kFlatQ_isLocalization

/-- The K-flat objects of the homotopy category of complexes of `R`-modules. -/
public abbrev kFlatHomotopyObjects (R : Type u) [CommRing R] :
    ObjectProperty (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  fun K => CochainComplex.KFlat K.as

/-- Quasi-isomorphisms between K-flat objects of the homotopy category. -/
public abbrev kFlatHomotopyQuasiIso (R : Type u) [CommRing R] :
    MorphismProperty (kFlatHomotopyObjects R).FullSubcategory :=
  (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
    (kFlatHomotopyObjects R).ι

/-- The functor from K-flat objects of the homotopy category to the derived category.
The derived category is an arbitrary localization of complexes of `R`-modules: the
construction uses only `DerivedCategory.Qh`, which is available at every model. -/
public noncomputable abbrev kFlatHomotopyQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (kFlatHomotopyObjects R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (kFlatHomotopyObjects R).ι ⋙ DerivedCategory.Qh

/-- The derived category of `R`-modules is the localization of the K-flat objects of the
homotopy category at the quasi-isomorphisms, at any model of the derived category. -/
public theorem kFlatHomotopyQ_isLocalization (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (kFlatHomotopyQ.{u, w} R).IsLocalization (kFlatHomotopyQuasiIso R) := by
  have := kFlatLocalizer_isLocalizedEquivalence (R := R)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer R) (DerivedCategory.Qh (C := ModuleCat.{u} R))

private lemma kFlatQ_essSurj (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] : (kFlatQ R).EssSurj :=
  Localization.essSurj (kFlatQ R) (KFlatQuasiIso R)

attribute [local instance] kFlatQ_essSurj

private noncomputable abbrev kFlatTensorToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :=
  ((((Functor.whiskeringLeft₂ (DObj R)).obj (KFlatObjects R).ι).obj
    (KFlatObjects R).ι).obj
      (homotopyTensor R ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Qh (C := ModuleCat.{u} R))))

private lemma kFlatTensorToDerived_inverts {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    MorphismProperty.IsInvertedBy₂ (KFlatQuasiIso R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) := by
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := homotopyTensor_right_preserves_quasiIso L.1 L.2 f.hom hf
  have h₂ := homotopyTensor_right_preserves_quasiIso K'.1 K'.2 g.hom hg
  exact IsIso.comp_isIso' ((homotopy_quasiIso_iff_isIso_Qh _).1 h₁)
    ((NatIso.isIso_map_iff (isoWhiskerRight ((homotopyTensorBraiding R).app K'.1)
      (DerivedCategory.Qh (C := ModuleCat.{u} R))) g.hom).2
        ((homotopy_quasiIso_iff_isIso_Qh _).1 h₂))

private noncomputable def derivedTensor (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] : DObj R ⥤ DObj R ⥤ DObj R :=
  Localization.lift₂ (kFlatTensorToDerived R) kFlatTensorToDerived_inverts
    (kFlatQ R) (kFlatQ R)

@[instance_reducible]
private noncomputable def derivedTensorLifting (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    Localization.Lifting₂ (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) (derivedTensor R) := by
  unfold derivedTensor
  infer_instance

attribute [local instance] derivedTensorLifting

private noncomputable def derivedTensorComparisonIso (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :=
  Localization.Lifting₂.iso (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
    (kFlatTensorToDerived R) (derivedTensor R)

private noncomputable def derivedTensorComparison {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  (((derivedTensor R).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K).symm).app
      (DerivedCategory.Q.obj L)) ≪≫
    ((derivedTensor R).obj ((DerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj K))).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app L).symm ≪≫
    ((derivedTensorComparisonIso R).app
      ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩).app
      ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩ ≪≫
    DerivedCategory.Qh.mapIso (homotopyTensorComparison K L) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app (K ⊗ L)

attribute [local instance] kFlatObjects_isTriangulated

private lemma kFlatQuasiIso_hasLeftCalculusOfFractions (R : Type u) [CommRing R] :
    (KFlatQuasiIso R).HasLeftCalculusOfFractions := by
  have h : KFlatQuasiIso R =
      ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).inverseImage
        (KFlatObjects R).ι).trW := by
    ext X Y f
    change HomotopyCategory.quasiIso _ _ ((KFlatObjects R).ι.map f) ↔ _
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).inverseImage_trW_iff
      (KFlatObjects R).ι f).symm
  rw [h]
  infer_instance

attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions

private lemma kFlatQ_mapArrow_essSurj (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    (kFlatQ R).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (kFlatQ R) (KFlatQuasiIso R)

attribute [local instance] kFlatQ_mapArrow_essSurj

/-- A functor isomorphic to a triangulated functor admits a shift commutation making it
triangulated. -/
private lemma exists_commShift_isTriangulated_of_iso {A B : Type*} [Category* A] [Category* B]
    [HasShift A ℤ] [HasShift B ℤ] [Preadditive A] [Preadditive B] [HasZeroObject A]
    [HasZeroObject B] [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor A n)]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor B n)]
    [Pretriangulated A] [Pretriangulated B]
    {F G : A ⥤ B} (e : F ≅ G) [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ s : G.CommShift ℤ, letI := s; G.IsTriangulated := by
  let := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩

private lemma kFlatTensorToDerived_exact_left {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (K : (KFlatObjects R).FullSubcategory) :
    ∃ s : ((kFlatTensorToDerived R).flip.obj K).CommShift ℤ,
      letI := s; ((kFlatTensorToDerived R).flip.obj K).IsTriangulated := by
  obtain ⟨s, hs⟩ := TotalTensorComplex.tright_isTriangulated K.1.as
  let := s
  have := hs
  let e : (KFlatObjects R).ι ⋙ Tright K.1.as ⋙ DerivedCategory.Qh ≅
      (kFlatTensorToDerived R).flip.obj K :=
    isoWhiskerLeft (KFlatObjects R).ι
      (isoWhiskerRight (homotopyTensorRightIso K.1.as).symm DerivedCategory.Qh)
  exact exists_commShift_isTriangulated_of_iso e

private lemma derivedTensor_exact_left {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (L : DObj R) :
    ∃ s : ((derivedTensor R).flip.obj L).CommShift ℤ,
      letI := s; ((derivedTensor R).flip.obj L).IsTriangulated := by
  let K := (kFlatQ R).objPreimage L
  obtain ⟨s, hs⟩ := kFlatTensorToDerived_exact_left K
  let := s
  have := hs
  let := Localization.Lifting₂.snd (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R)
    (KFlatQuasiIso R) (kFlatTensorToDerived R) (derivedTensor R) K
  let := Functor.commShiftOfLocalization (kFlatQ R) (KFlatQuasiIso R) ℤ
    ((kFlatTensorToDerived R).flip.obj K) ((derivedTensor R).flip.obj ((kFlatQ R).obj K))
  have := Functor.isTriangulated_of_localization (kFlatQ R) (KFlatQuasiIso R)
    ((kFlatTensorToDerived R).flip.obj K) ((derivedTensor R).flip.obj ((kFlatQ R).obj K))
  let e := (derivedTensor R).flip.mapIso ((kFlatQ R).objObjPreimageIso L)
  exact exists_commShift_isTriangulated_of_iso e

private noncomputable def derivedTensorBraiding (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] : derivedTensor R ≅ (derivedTensor R).flip := by
  let e : kFlatTensorToDerived R ≅ (kFlatTensorToDerived R).flip :=
    (((whiskeringLeft₂ (DObj R)).obj (KFlatObjects R).ι).obj (KFlatObjects R).ι).mapIso
      (isoWhiskerRight (homotopyTensorBraiding R)
        ((whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := ModuleCat.{u} R))))
  exact Localization.lift₂NatIso (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
    (kFlatTensorToDerived R) (kFlatTensorToDerived R).flip
    (derivedTensor R) (derivedTensor R).flip e

private lemma derivedTensor_exact_right {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K : DObj R) :
    ∃ s : ((derivedTensor R).obj K).CommShift ℤ,
      letI := s; ((derivedTensor R).obj K).IsTriangulated := by
  obtain ⟨s, hs⟩ := derivedTensor_exact_left K
  let := s
  have := hs
  let e := ((derivedTensorBraiding R).app K).symm
  exact exists_commShift_isTriangulated_of_iso e

private abbrev KFlatComplexes (R : Type u) [CommRing R] : ObjectProperty (C R) :=
  fun K => K.KFlat

private noncomputable abbrev kFlatQuotient (R : Type u) [CommRing R] :
    (KFlatComplexes R).FullSubcategory ⥤ (KFlatObjects R).FullSubcategory :=
  (KFlatObjects R).lift
    ((KFlatComplexes R).ι ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (fun K => K.2)

private noncomputable abbrev kFlatComplexQ (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :=
  (KFlatComplexes R).ι ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R))

private noncomputable def kFlatQuotientCompQIso (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    kFlatQuotient R ⋙ kFlatQ R ≅ kFlatComplexQ R :=
  isoWhiskerLeft (KFlatComplexes R).ι (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))

private noncomputable abbrev complexTensorToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :=
  curriedTensor (C R) ⋙ (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R))

private noncomputable abbrev kFlatComplexTensorToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :=
  (((whiskeringLeft₂ (DObj R)).obj (KFlatComplexes R).ι).obj (KFlatComplexes R).ι).obj
    (complexTensorToDerived R)

private noncomputable def derivedTensorComparisonNatIso (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    (((whiskeringLeft₂ (DObj R)).obj (kFlatComplexQ R)).obj (kFlatComplexQ R)).obj
      (derivedTensor R) ≅ kFlatComplexTensorToDerived R := by
  let q := kFlatQuotientCompQIso R
  let h := Localization.Lifting₂.iso
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (homotopyEquivalences R) (homotopyEquivalences R)
    (curriedTensor (C R) ⋙ (Functor.whiskeringRight _ _ _).obj
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))) (homotopyTensor R)
  exact ((((whiskeringLeft₂ (DObj R)).mapIso q.symm).app (kFlatComplexQ R)).app
      (derivedTensor R)) ≪≫
    ((((whiskeringLeft₂ (DObj R)).obj (kFlatQuotient R ⋙ kFlatQ R)).mapIso q.symm).app
      (derivedTensor R)) ≪≫
    (((whiskeringLeft₂ (DObj R)).obj (kFlatQuotient R)).obj (kFlatQuotient R)).mapIso
      (derivedTensorComparisonIso R) ≪≫
    (((whiskeringLeft₂ (DObj R)).obj (KFlatComplexes R).ι).obj (KFlatComplexes R).ι).mapIso
      (isoWhiskerRight h ((whiskeringRight _ _ _).obj
          (DerivedCategory.Qh (C := ModuleCat.{u} R))) ≪≫
        isoWhiskerLeft (curriedTensor (C R))
          ((whiskeringRight (C R) (C R) (DObj R)).mapIso
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))))

private lemma derivedTensorComparisonNatIso_app {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((derivedTensorComparisonNatIso R).app ⟨K, hK⟩).app ⟨L, hL⟩ =
      derivedTensorComparison K L hK hL := by
  rfl

private lemma derivedTensorComparison_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] {K K' L L' : C R} (f : K ⟶ K') (g : L ⟶ L')
    (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    ((derivedTensor R).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
      (derivedTensorComparison K' L' hK' hL').hom =
    (derivedTensorComparison K L hK hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let f' : (⟨K, hK⟩ : (KFlatComplexes R).FullSubcategory) ⟶ ⟨K', hK'⟩ := ⟨f⟩
  let g' : (⟨L, hL⟩ : (KFlatComplexes R).FullSubcategory) ⟶ ⟨L', hL'⟩ := ⟨g⟩
  have h := (uncurry.map (derivedTensorComparisonNatIso R).hom).naturality
    ((f', g') : (⟨K, hK⟩, ⟨L, hL⟩) ⟶ (⟨K', hK'⟩, ⟨L', hL'⟩))
  simpa [f', g', uncurry_obj_map, tensorHom_def, ← Functor.map_comp,
    ← derivedTensorComparisonNatIso_app] using h

private noncomputable def homotopyTensorRightUnitor (R : Type u) [CommRing R] :
    (homotopyTensor R).flip.obj
      ((HomotopyCategory.quotient _ _).obj (𝟙_ (C R))) ≅ 𝟭 (KC R) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let F := curriedTensor (C R) ⋙ (whiskeringRight _ _ _).obj Q
  letI := Localization.Lifting₂.snd Q Q (homotopyEquivalences R)
    (homotopyEquivalences R) F (homotopyTensor R) (𝟙_ (C R))
  exact Localization.liftNatIso Q (homotopyEquivalences R) (F.flip.obj (𝟙_ (C R))) Q
    _ _ (isoWhiskerRight (MonoidalCategory.rightUnitorNatIso (C R)) Q)

private noncomputable def derivedTensorRightUnitorCore (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    (derivedTensor R).flip.obj ((kFlatQ R).obj
      ⟨(HomotopyCategory.quotient _ _).obj (𝟙_ (C R)), kFlat_unit⟩) ≅ 𝟭 (DObj R) := by
  let U : (KFlatObjects R).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj (𝟙_ (C R)), kFlat_unit⟩
  letI := Localization.Lifting₂.snd (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R)
    (KFlatQuasiIso R) (kFlatTensorToDerived R) (derivedTensor R) U
  exact Localization.liftNatIso (kFlatQ R) (KFlatQuasiIso R)
    ((kFlatTensorToDerived R).flip.obj U) (kFlatQ R) _ _
    (isoWhiskerLeft (KFlatObjects R).ι
      (isoWhiskerRight (homotopyTensorRightUnitor R) DerivedCategory.Qh))

private noncomputable def derivedTensorRightUnitor (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    (derivedTensor R).flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      𝟭 (DObj R) :=
  (derivedTensor R).flip.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app (𝟙_ (C R))).symm ≪≫
    derivedTensorRightUnitorCore R

private lemma homotopyTensorRightUnitor_app {R : Type u} [CommRing R] (K : C R) :
    (homotopyTensorRightUnitor R).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (homotopyTensorComparison K (𝟙_ _)).hom ≫
        (HomotopyCategory.quotient _ _).map (ρ_ K).hom := by
  simp [homotopyTensorRightUnitor, Localization.liftNatIso, homotopyTensorComparison,
    Localization.liftNatTrans_app, Localization.Lifting₂.snd, Localization.Lifting₂.fst]
  rfl

private lemma derivedTensorRightUnitorCore_app {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K : (KFlatObjects R).FullSubcategory) :
    (derivedTensorRightUnitorCore R).hom.app ((kFlatQ R).obj K) =
      ((derivedTensorComparisonIso R).hom.app K).app
          ⟨(HomotopyCategory.quotient _ _).obj (𝟙_ (C R)), kFlat_unit⟩ ≫
        DerivedCategory.Qh.map ((homotopyTensorRightUnitor R).hom.app K.1) := by
  dsimp only [derivedTensorRightUnitorCore, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [derivedTensorComparisonIso]
  rfl

private lemma derivedTensorRightUnitorCore_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K : C R) (hK : K.KFlat) :
    ((derivedTensorComparisonIso R).hom.app
        ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩).app
        ⟨(HomotopyCategory.quotient _ _).obj (𝟙_ (C R)), kFlat_unit⟩ ≫
      DerivedCategory.Qh.map (homotopyTensorComparison K (𝟙_ _)).hom ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app (K ⊗ 𝟙_ _) ≫
      DerivedCategory.Q.map (ρ_ K).hom =
    (derivedTensorRightUnitorCore R).hom.app
      ((kFlatQ R).obj ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K := by
  rw [derivedTensorRightUnitorCore_app, homotopyTensorRightUnitor_app]
  simp [Functor.map_comp, Category.assoc]

private lemma derivedTensorRightUnitor_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K : C R) (hK : K.KFlat)
    (hUnit : (𝟙_ (C R)).KFlat) :
    (derivedTensorComparison K (𝟙_ _) hK hUnit).hom ≫
      DerivedCategory.Q.map (ρ_ K).hom =
        (derivedTensorRightUnitor R).hom.app (DerivedCategory.Q.obj K) := by
  dsimp only [derivedTensorComparison, derivedTensorRightUnitor, Iso.trans_hom,
    NatTrans.comp_app, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, flip_map_app]
  simp only [Category.assoc]
  rw [derivedTensorRightUnitorCore_comparison]
  erw [← ((derivedTensor R).map
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K).inv).naturality_assoc]
  erw [(derivedTensorRightUnitorCore R).hom.naturality_assoc]
  simp

private lemma derivedTensorBraiding_app {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : (KFlatObjects R).FullSubcategory) :
    ((derivedTensorBraiding R).hom.app ((kFlatQ R).obj K)).app ((kFlatQ R).obj L) =
      ((derivedTensorComparisonIso R).hom.app K).app L ≫
        DerivedCategory.Qh.map (((homotopyTensorBraiding R).hom.app K.1).app L.1) ≫
        ((derivedTensorComparisonIso R).inv.app L).app K := by
  dsimp only [derivedTensorBraiding, Localization.lift₂NatIso]
  rw [Localization.lift₂NatTrans_app_app]
  rfl

@[reassoc]
private lemma derivedTensorBraiding_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] {K K' L L' : DObj R} (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor R).map f).app L ≫ ((derivedTensor R).obj K').map g ≫
        ((derivedTensorBraiding R).hom.app K').app L' =
      ((derivedTensorBraiding R).hom.app K).app L ≫
        ((derivedTensor R).map g).app K ≫ ((derivedTensor R).obj L').map f := by
  have h := (uncurry.map (derivedTensorBraiding R).hom).naturality
    ((f, g) : (K, L) ⟶ (K', L'))
  simp only [uncurry_obj_map, uncurry_map_app, Category.assoc,
    flip_obj_obj, flip_obj_map, flip_map_app] at h
  rw [((derivedTensor R).map g).naturality f] at h
  exact h

private lemma derivedTensorComparison_braiding {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((derivedTensorBraiding R).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫ (derivedTensorComparison L K hL hK).hom =
      (derivedTensorComparison K L hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom := by
  dsimp only [derivedTensorComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  erw [← derivedTensorBraiding_naturality_assoc]
  erw [derivedTensorBraiding_app
    ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩
    ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩]
  rw [homotopyTensorBraiding_app]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_app_assoc,
    Iso.map_inv_hom_id_assoc, DerivedCategory.quotientCompQhIso_hom_naturality]
  rfl

/-- **Stacks 0BYI.** The canonical derived tensor product, equipped with its symmetry functorial
in both complexes and represented on K-flat complexes in degrees `p` and `q` by the ordinary
tensor braiding with the sign `(-1) ^ (p * q)`. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[stacks 0BYI, no_expose]
public noncomputable def canonicalSymmetricDerivedTensorProduct
    (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] : SymmetricDerivedTensorProduct R := by
  classical
  let s := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  have hs := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose_spec
  letI := s
  let T : DerivedTensorProduct R :=
    { tensor := derivedTensor R
      comparison := derivedTensorComparison
      comparison_naturality := derivedTensorComparison_naturality
      commShift_left := fun L => (derivedTensor_exact_left L).choose
      commShift_right := fun K => (derivedTensor_exact_right K).choose
      exact_left := fun L => (derivedTensor_exact_left L).choose_spec
      exact_right := fun K => (derivedTensor_exact_right K).choose_spec
      rightUnitor := derivedTensorRightUnitor R
      rightUnitor_comparison := derivedTensorRightUnitor_comparison }
  refine ⟨T, ⟨derivedTensorBraiding R, ?_⟩⟩
  intro K L hK hL
  refine ⟨(β_ K L).hom, hs K L, ?_⟩
  change DerivedCategory.Q.map (β_ K L).hom =
    (derivedTensorComparison K L hK hL).inv ≫
      ((derivedTensorBraiding R).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫ (derivedTensorComparison L K hL hK).hom
  simpa [Category.assoc] using congrArg
    (fun f => (derivedTensorComparison K L hK hL).inv ≫ f)
    (derivedTensorComparison_braiding K L hK hL).symm

/-- The canonical derived tensor product, characterized by its natural comparison with ordinary
tensor products of K-flat complexes. -/
public noncomputable abbrev canonicalDerivedTensorProduct
    (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] : DerivedTensorProduct R :=
  (canonicalSymmetricDerivedTensorProduct R).tensorProduct

/-- The natural Koszul symmetry of the canonical derived tensor product. -/
public noncomputable def derivedTensorProductKoszulBraiding
    (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] : KoszulBraiding (canonicalDerivedTensorProduct R) :=
  (canonicalSymmetricDerivedTensorProduct R).braiding

/-- The canonical derived tensor product bifunctor. -/
public noncomputable abbrev canonicalDerivedTensorProductFunctor (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    DObj R ⥤ (DObj R ⥤ DObj R) :=
  (canonicalDerivedTensorProduct R).tensor

/-- The natural right unit isomorphism for the derived tensor product. -/
public noncomputable def derivedTensorProductRightUnitorIso
    [HasDerivedCategory (ModuleCat.{u} R)] (K : DObj R) :
    ((canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅ K :=
  (canonicalDerivedTensorProduct R).rightUnitor.app K

/-- The canonical isomorphism `K ⊗ᴸ L ≅ L ⊗ᴸ K`, functorial in both derived
complexes. Its K-flat representatives are the signed swaps specified by
`canonicalSymmetricDerivedTensorProduct.braiding.isKoszul`. -/
@[ega "III 6.3.5" "Remark 6.3.5(i)", ega "III 6.7.13" "special case"]
public noncomputable def derivedTensorProductCommIso
    [HasDerivedCategory (ModuleCat.{u} R)] (K L : DObj R) :
    ((canonicalDerivedTensorProductFunctor R).obj K).obj L ≅
      ((canonicalDerivedTensorProductFunctor R).obj L).obj K :=
  ((derivedTensorProductKoszulBraiding R).iso.app K).app L

/-! #### Associativity -/

private lemma kFlatComplexes_isMonoidal (R : Type u) [CommRing R] :
    (KFlatComplexes R).IsMonoidal where
  prop_unit := kFlat_unit
  prop_tensor := CochainComplex.KFlat.tensor R

attribute [local instance] kFlatComplexes_isMonoidal

private abbrev kFlatQuotient₃ (R : Type u) [CommRing R] :=
  (kFlatQuotient R).prod ((kFlatQuotient R).prod (kFlatQuotient R))

set_option backward.isDefEq.respectTransparency false in
private def kFlatQuotient₃WhiskeringFullyFaithful (R : Type u) [CommRing R]
    (E : Type*) [Category* E] :
    ((whiskeringLeft _ _ E).obj (kFlatQuotient₃ R)).FullyFaithful where
  preimage τ :=
    { app := fun X => τ.app
        (⟨X.1.obj.as, X.1.property⟩,
          ⟨X.2.1.obj.as, X.2.1.property⟩, ⟨X.2.2.obj.as, X.2.2.property⟩)
      naturality := by
        intro X Y f
        have h := τ.naturality
          ((⟨f.1.hom.out⟩, ⟨f.2.1.hom.out⟩, ⟨f.2.2.hom.out⟩) :
            (⟨X.1.obj.as, X.1.property⟩,
              ⟨X.2.1.obj.as, X.2.1.property⟩, ⟨X.2.2.obj.as, X.2.2.property⟩) ⟶
            (⟨Y.1.obj.as, Y.1.property⟩,
              ⟨Y.2.1.obj.as, Y.2.1.property⟩, ⟨Y.2.2.obj.as, Y.2.2.property⟩))
        simp only [whiskeringLeft_obj_obj, Functor.comp_map, kFlatQuotient₃,
          Functor.prod_map, kFlatQuotient, ObjectProperty.lift_map,
          ObjectProperty.ι_map, HomotopyCategory.quotient_map_out] at h
        exact h }
  map_preimage τ := rfl
  preimage_map τ := rfl

private abbrev kFlatQ₃ (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] :=
  (kFlatQ R).prod ((kFlatQ R).prod (kFlatQ R))

private abbrev kFlatComplexQ₃ (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] :=
  (kFlatComplexQ R).prod ((kFlatComplexQ R).prod (kFlatComplexQ R))

private def kFlatComplexQ₃WhiskeringFullyFaithful (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (E : Type*) [Category* E] :
    ((whiskeringLeft _ _ E).obj (kFlatComplexQ₃ R)).FullyFaithful := by
  let h := Localization.fullyFaithfulWhiskeringLeft (kFlatQ₃ R)
    ((KFlatQuasiIso R).prod ((KFlatQuasiIso R).prod (KFlatQuasiIso R))) E
  let h' := h.comp (kFlatQuotient₃WhiskeringFullyFaithful R E)
  let e : kFlatQuotient₃ R ⋙ kFlatQ₃ R ≅ kFlatComplexQ₃ R :=
    NatIso.prod (kFlatQuotientCompQIso R)
      (NatIso.prod (kFlatQuotientCompQIso R) (kFlatQuotientCompQIso R))
  exact h'.ofIso ((whiskeringLeft _ _ E).mapIso e)

private abbrev kFlatComplexQuasiIso (R : Type u) [CommRing R] :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
    (KFlatComplexes R).ι

@[instance_reducible]
private def tensorLifting {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) :
    Localization.Lifting₂ (kFlatComplexQ R) (kFlatComplexQ R)
      (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
      (curriedTensor (KFlatComplexes R).FullSubcategory ⋙
        (whiskeringRight _ _ _).obj (kFlatComplexQ R)) T.tensor where
  iso := NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun L => T.comparison K.obj L.obj K.property L.property)
      (by
        intro L L' g
        change _ ≫ _ = _ ≫ DerivedCategory.Q.map
          (HomologicalComplex.tensorHom (𝟙 K.obj) g.hom)
        simpa using T.comparison_naturality (𝟙 K.obj) g.hom
          K.property K.property L.property L'.property))
    (by
      intro K K' f
      ext L
      change _ ≫ _ = _ ≫ DerivedCategory.Q.map
        (HomologicalComplex.tensorHom f.hom (𝟙 L.obj))
      simpa using T.comparison_naturality f.hom (𝟙 L.obj)
        K.property K'.property L.property L.property)

attribute [local instance] tensorLifting

/-- **The canonical associator of a derived tensor product, as a named isomorphism of
trifunctors.**  For a derived tensor product `T` on `D(R)`, the two triple products
`(X ⊗ᴸ Y) ⊗ᴸ Z` and `X ⊗ᴸ (Y ⊗ᴸ Z)`, read as trifunctors `D(R) × D(R) × D(R) ⥤ D(R)`, are
isomorphic.

It is obtained by descent: on K-flat complexes the two trifunctors are the two bracketings of the
ordinary total tensor product, which are isomorphic by `CategoryTheory.curriedAssociatorNatIso`
for the monoidal structure on K-flat complexes, and the triple localization functor
`D(R) × D(R) × D(R)` is full and faithful after whiskering, so that isomorphism has a unique
preimage.  Uniqueness of the preimage is what makes this associator *canonical*: it is determined
by the law `CochainComplex.DerivedTensor.derivedAssociatorIso_comparison` below, which says what
it does on K-flat representatives.

`CochainComplex.DerivedTensor.derivedTensorProduct_associator`, [stacks 0BYJ], is the
existentially quantified form of the same content; this definition and the two laws below are
what a *coherence* of the associator — for instance the compatibility of a monoidal comparison
with it — has to be stated against, since an existential associator cannot be named in such a
statement. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[no_expose]
public def derivedAssociator {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) :
    uncurry₃.obj (bifunctorComp₁₂ T.tensor T.tensor) ≅
      uncurry₃.obj (bifunctorComp₂₃ T.tensor T.tensor) := by
  let L := kFlatComplexQ R
  let W := kFlatComplexQuasiIso R
  let F := curriedTensor (KFlatComplexes R).FullSubcategory
  letI := Localization.Lifting₃.bifunctorComp₁₂ L L L L L W W W W F F T.tensor T.tensor
  letI := Localization.Lifting₃.bifunctorComp₂₃ L L L L L W W W W F F T.tensor T.tensor
  exact (kFlatComplexQ₃WhiskeringFullyFaithful R (DObj R)).preimageIso
    (uncurry₃.mapIso
      (Localization.Lifting₃.iso L L L W W W
          ((postcompose₃.obj L).obj (bifunctorComp₁₂ F F))
          (bifunctorComp₁₂ T.tensor T.tensor) ≪≫
        (postcompose₃.obj L).mapIso (curriedAssociatorNatIso _) ≪≫
        (Localization.Lifting₃.iso L L L W W W
          ((postcompose₃.obj L).obj (bifunctorComp₂₃ F F))
          (bifunctorComp₂₃ T.tensor T.tensor)).symm))

private lemma uncurry₃_map_app
    {A B C E : Type*} [Category* A] [Category* B] [Category* C] [Category* E]
    {F G : A ⥤ B ⥤ C ⥤ E} (τ : F ⟶ G) (X : A) (Y : B) (Z : C) :
    (uncurry₃.map τ).app (X, Y, Z) = ((τ.app X).app Y).app Z := rfl

private lemma uncurry₃_obj_map
    {A B C E : Type*} [Category* A] [Category* B] [Category* C] [Category* E]
    (F : A ⥤ B ⥤ C ⥤ E) {X X' : A} {Y Y' : B} {Z Z' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (uncurry₃.obj F).map ((f, g, h) : (X, Y, Z) ⟶ (X', Y', Z')) =
      (((F.map f).app Y).app Z ≫ ((F.obj X').map g).app Z) ≫
        ((F.obj X').obj Y').map h := rfl

private lemma whiskeringLeft_preimageIso_hom_app
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (L : A ⥤ B) (h : ((whiskeringLeft A B E).obj L).FullyFaithful)
    {F G : B ⥤ E} (e : L ⋙ F ≅ L ⋙ G) (X : A) :
    (h.preimageIso e).hom.app (L.obj X) = e.hom.app X :=
  congrArg (fun τ => τ.app X) (h.map_preimage e.hom)

set_option backward.isDefEq.respectTransparency false in
private lemma derivedAssociator_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R)
    (K L M : C R) (hK : K.KFlat) (hL : L.KFlat) (hM : M.KFlat) :
    (derivedAssociator T).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L, DerivedCategory.Q.obj M) ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (T.comparison L M hL hM).hom ≫
        (T.comparison K (L ⊗ M) hK (CochainComplex.KFlat.tensor R L M hL hM)).hom =
      (T.tensor.map (T.comparison K L hK hL).hom).app (DerivedCategory.Q.obj M) ≫
        (T.comparison (K ⊗ L) M (CochainComplex.KFlat.tensor R K L hK hL) hM).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.associator K L M).hom := by
  dsimp only [derivedAssociator]
  erw [whiskeringLeft_preimageIso_hom_app (kFlatComplexQ₃ R) _ _
    (⟨K, hK⟩, ⟨L, hL⟩, ⟨M, hM⟩)]
  simp only [Functor.mapIso_hom, uncurry₃_map_app]
  dsimp [Localization.Lifting₃.iso, Localization.Lifting₃.bifunctorComp₁₂,
    Localization.Lifting₃.bifunctorComp₂₃, Localization.Lifting₂.iso, tensorLifting,
    bifunctorComp₁₂Functor, bifunctorComp₂₃Functor,
    bifunctorComp₁₂FunctorObj, bifunctorComp₂₃FunctorObj]
  simp only [bifunctorComp₁₂FunctorMap_app_app_app_app,
    whiskeringLeft₂_obj_obj_obj_obj_obj, comp_obj, ObjectProperty.ι_obj,
    whiskeringRight_obj_obj, curriedTensor_obj_obj, ObjectProperty.tensorObj_obj,
    NatIso.ofComponents_hom_app, curriedAssociatorNatIso_hom_app_app_app,
    ObjectProperty.associator_def, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    bifunctorComp₂₃FunctorMap_app_app_app_app, NatIso.ofComponents_inv_app,
    Category.assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- **The canonical associator of a derived tensor product at a triple of objects.**  The
component of `CochainComplex.DerivedTensor.derivedAssociator` at `(X, Y, Z)`:
`(X ⊗ᴸ Y) ⊗ᴸ Z ≅ X ⊗ᴸ (Y ⊗ᴸ Z)`.

This is the named associator that
`CochainComplex.DerivedTensor.derivedTensorProduct_associator`, [stacks 0BYJ], asserts the
existence of.  Naturality in all three arguments is naturality of
`CochainComplex.DerivedTensor.derivedAssociator`, taken at a triple of morphisms; the law that
*determines* it is `CochainComplex.DerivedTensor.derivedAssociatorIso_comparison` — its value on
K-flat representatives, which is the ordinary associator of total tensor products of complexes
read through the comparison of `T` — the triple localization being full and faithful after
whiskering. -/
public abbrev derivedAssociatorIso {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (T : DerivedTensorProduct R)
    (X Y Z : DerivedCategory (ModuleCat.{u} R)) :
    (T.tensor.obj ((T.tensor.obj X).obj Y)).obj Z ≅
      (T.tensor.obj X).obj ((T.tensor.obj Y).obj Z) :=
  (derivedAssociator T).app (X, Y, Z)

/-- **The canonical associator on K-flat representatives is the ordinary associator of total
tensor products.**  The law that determines
`CochainComplex.DerivedTensor.derivedAssociatorIso`: for K-flat `K`, `L`, `M`, transporting the
associator at their images along the comparison isomorphisms of `T` — which identify the derived
tensor products of the images with the images of the total tensor products — gives
`HomologicalComplex.associator K L M`.

This is the compatibility of the canonical associator with the K-flat comparison of `T`, and it is
what a coherence of a monoidal comparison against the derived associator has to be reduced to;
`CochainComplex.DerivedTensor.derivedTensorProduct_associator`, [stacks 0BYJ], is the same
equation with the associator existentially quantified, which is the form no such coherence can be
stated against. -/
public theorem derivedAssociatorIso_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) (K L M : C R) (hK : K.KFlat) (hL : L.KFlat) (hM : M.KFlat) :
    (derivedAssociatorIso T (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
            (DerivedCategory.Q.obj M)).hom ≫
          (T.tensor.obj (DerivedCategory.Q.obj K)).map (T.comparison L M hL hM).hom ≫
          (T.comparison K (L ⊗ M) hK (CochainComplex.KFlat.tensor R L M hL hM)).hom =
        (T.tensor.map (T.comparison K L hK hL).hom).app (DerivedCategory.Q.obj M) ≫
          (T.comparison (K ⊗ L) M (CochainComplex.KFlat.tensor R K L hK hL) hM).hom ≫
          DerivedCategory.Q.map (HomologicalComplex.associator K L M).hom :=
  derivedAssociator_comparison T K L M hK hL hM

/-- **The canonical derived associator is natural in all three arguments.**  For morphisms
`f : K ⟶ K'`, `g : L ⟶ L'` and `h : M ⟶ M'` of `D(R)`, the square relating
`CochainComplex.DerivedTensor.derivedAssociatorIso` at `(K, L, M)` and at `(K', L', M')` through
the two triple products commutes.

This is naturality of `CochainComplex.DerivedTensor.derivedAssociator`, taken at the triple
`(f, g, h)` and with the two triple-product trifunctors evaluated on it.  The same content occurs
inside `CochainComplex.DerivedTensor.derivedTensorProduct_associator`, [stacks 0BYJ], but there
the associator it is stated for is existentially quantified; a coherence of some other structure
against the *named* associator — the compatibility of a monoidal comparison with it, say — needs
the naming, which is what this provides. -/
public theorem derivedAssociatorIso_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (T : DerivedTensorProduct R) {K K' L L' M M' : DObj R}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    (T.tensor.map ((T.tensor.map f).app L ≫ (T.tensor.obj K').map g)).app M ≫
          (T.tensor.obj ((T.tensor.obj K').obj L')).map h ≫
          (derivedAssociatorIso T K' L' M').hom =
      (derivedAssociatorIso T K L M).hom ≫
        (T.tensor.map f).app ((T.tensor.obj L).obj M) ≫
        (T.tensor.obj K').map ((T.tensor.map g).app M ≫ (T.tensor.obj L').map h) := by
  have hn := (derivedAssociator T).hom.naturality
    ((f, g, h) : (K, L, M) ⟶ (K', L', M'))
  rw [uncurry₃_obj_map, uncurry₃_obj_map] at hn
  refine Eq.trans ?_ (Eq.trans hn ?_)
  · rw [Functor.map_comp, NatTrans.comp_app]
    exact (Category.assoc _ _ _).symm
  · rw [Functor.map_comp]
    exact congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0BYJ.** The derived tensor product is associative up to a canonical isomorphism,
functorial in all three complexes. On K-flat representatives this is the standard associator
of tensor products of complexes. -/
@[stacks 0BYJ]
public theorem derivedTensorProduct_associator
    (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] :
    let D := DerivedCategory (ModuleCat.{u} R)
    let C := CochainComplex (ModuleCat.{u} R) ℤ
    let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
    let T := canonicalDerivedTensorProduct R
    ∃ associator : ∀ K L M : D,
          (T.tensor.obj ((T.tensor.obj K).obj L)).obj M ≅
            (T.tensor.obj K).obj ((T.tensor.obj L).obj M),
        (∀ {K K' L L' M M' : D} (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M'),
          (T.tensor.map ((T.tensor.map f).app L ≫ (T.tensor.obj K').map g)).app M ≫
                (T.tensor.obj ((T.tensor.obj K').obj L')).map h ≫
                (associator K' L' M').hom =
            (associator K L M).hom ≫
              (T.tensor.map f).app ((T.tensor.obj L).obj M) ≫
              (T.tensor.obj K').map
                ((T.tensor.map g).app M ≫ (T.tensor.obj L').map h)) ∧
        ∀ (K L M : C) (hK : K.KFlat) (hL : L.KFlat) (hM : M.KFlat),
          let hKL := CochainComplex.KFlat.tensor R K L hK hL
          let hLM := CochainComplex.KFlat.tensor R L M hL hM
          (associator (Q.obj K) (Q.obj L) (Q.obj M)).hom ≫
                (T.tensor.obj (Q.obj K)).map (T.comparison L M hL hM).hom ≫
                (T.comparison K (L ⊗ M) hK hLM).hom =
            (T.tensor.map (T.comparison K L hK hL).hom).app (Q.obj M) ≫
              (T.comparison (K ⊗ L) M hKL hM).hom ≫
              Q.map (HomologicalComplex.associator K L M).hom := by
  dsimp only
  let T := canonicalDerivedTensorProduct R
  refine ⟨fun K L M => (derivedAssociator T).app (K, L, M), ?_, ?_⟩
  · intro K K' L L' M M' f g h
    exact derivedAssociatorIso_naturality T f g h
  · intro K L M hK hL hM
    exact derivedAssociatorIso_comparison T K L M hK hL hM

end Canonical

end CochainComplex.DerivedTensor

end
