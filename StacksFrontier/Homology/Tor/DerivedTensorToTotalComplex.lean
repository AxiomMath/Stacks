module

public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex
public import StacksFrontier.Homology.Tor.ModuleKFlatDescent
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# The canonical map from the derived tensor product to the ordinary total tensor complex

Let `R` be a commutative ring.  `CochainComplex.DerivedTensor.DerivedTensorProduct` of
[Stacks, Tag 0BYI] packages a derived tensor bifunctor on `D(R)` together with its comparison
with the ordinary total tensor complex **on a pair of K-flat complexes** and nothing more.  For
arbitrary complexes `K` and `L` the two objects `QK ⊗^𝐋_R QL` and `Q(Tot(K ⊗_R L))` are no
longer isomorphic, but there is still a canonical morphism between them, natural in both
variables.

## Main definitions

* `CochainComplex.DerivedTensor.ToTotal.tensorPairIso`: **any packaged derived tensor product is
  the K-flat descent of the ordinary total tensor complex**, as an isomorphism of bifunctors on
  `D(R) × D(R)`.
* `CochainComplex.DerivedTensor.ToTotal.modelToTensorNatTrans`: the canonical map for that
  descent, which is `CochainComplex.KFlatBifunctor.toTensor` packaged as a morphism of
  bifunctors on pairs of cochain complexes.
* `CochainComplex.DerivedTensor.ToTotal.derivedToTensorNatTrans`: **the canonical map**
  `QK ⊗^𝐋_R QL ⟶ Q(Tot(K ⊗_R L))` for an arbitrary packaged derived tensor product.
* `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans`: the same for the
  canonical derived tensor product of [Stacks, Tag 064M].

## Main results

* `CochainComplex.DerivedTensor.ToTotal.tensorPairIso_hom_app`: the descended isomorphism at a
  pair of K-flat complexes is the comparison of Tag 0BYI followed by the inverse of
  `CochainComplex.KFlatBifunctor.toTensor`.
* `CochainComplex.DerivedTensor.ToTotal.derivedToTensorNatTrans_app_eq_comparison`: at every
  pair of K-flat complexes the canonical map is the K-flat comparison recorded by the structure.
* `CochainComplex.DerivedTensor.ToTotal.isIso_derivedToTensorNatTrans_app`: it is invertible as
  soon as the right factor is K-flat, with no hypothesis on the left factor.

## Implementation notes

*How the descent goes.*  On a pair of K-flat complexes both bifunctors are computed by the
ordinary total tensor complex: on the packaged side by `DerivedTensorProduct.comparison`, on the
descent side by `toTensor`, which at a K-flat right factor is the one-sided comparison and hence
invertible.  Both comparisons are natural in cochain maps between K-flat complexes, and — this
is what makes the composite natural — their naturality squares have the *same* right-hand edge
`Q(f ⊗ g)`: `toTensor_naturality` is stated with the two one-variable total complexes merged
into `HomologicalComplex.mapBifunctorMap`, which for the tensor bifunctor of modules is
`HomologicalComplex.tensorHom` by `rfl`, and that is the edge
`DerivedTensorProduct.comparison_naturality` uses.  Since `D(R) × D(R)` is the localization of
the pairs of K-flat objects at the quasi-isomorphisms
(`CochainComplex.DerivedTensor.OneSided.kFlatQModulesPair_isLocalization`, i.e. Tag 06Y4 in each
variable), `CategoryTheory.Localization.liftNatIso` extends the comparison to all of
`D(R) × D(R)`.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.KFlatBifunctor
open scoped MonoidalCategory CategoryTheory.Prod

universe u

namespace CochainComplex.DerivedTensor.ToTotal

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- The tensor bifunctor of complexes of `R`-modules, as a bifunctor. -/
abbrev modF (R : Type u) [CommRing R] := MonoidalCategory.curriedTensor (ModuleCat.{u} R)

/-- The existence of K-flat resolutions [Stacks, Tag 06Y4], for the tensor bifunctor of complexes
of `R`-modules. -/
abbrev modRes (R : Type u) [CommRing R] := OneSided.exists_kFlat_quasiIso R

/-- `(x, y) ↦ x ⊗^𝐋_R y` for a packaged derived tensor product, on the product category. -/
abbrev tensorPairOf (T : DerivedTensorProduct R) : DObj R × DObj R ⥤ DObj R :=
  Functor.uncurry.obj T.tensor

/-- `(x, y) ↦ x ⊗^𝐋_R y` for the K-flat descent of the total tensor complex. -/
abbrev tensorPairModel (R : Type u) [CommRing R] : DObj R × DObj R ⥤ DObj R :=
  Functor.uncurry.obj (OneSided.tensorBifunctor R)

/-- `Q` in each of two variables, as a functor on pairs of cochain complexes. -/
abbrev qPair (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ ⥤
      DObj R × DObj R :=
  DerivedCategory.Q.prod DerivedCategory.Q

/-- `Tot(- ⊗_R -)`, the ordinary total tensor complex, as a functor on *pairs* of cochain
complexes. -/
abbrev totalTensorPair (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ ⥤
      CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.uncurry.obj ((modF R).map₂HomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- On a morphism of the product category the total tensor complex is the tensor product of the
two morphisms. -/
theorem totalTensorPair_map {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (totalTensorPair R).map (a ×ₘ b) = HomologicalComplex.tensorHom a b :=
  HomologicalComplex.mapBifunctorMap_eq_map₂_comp (modF R) _ a b

/-- The canonical map of `toTensor` at a pair of K-flat complexes is invertible. -/
theorem isIso_toTensor (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    IsIso (toTensor (modF R) (modRes R) K L) := by
  rw [toTensor_eq_comparisonRight (modF R) (modRes R) K (L := L) hL]
  exact (comparisonRight (modF R) K L hL).isIso_hom

/-- **The right leg at a pair of K-flat complexes.** -/
def rightIso (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    (tensorPairModel R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  @asIso _ _ _ _ (toTensor (modF R) (modRes R) K L) (isIso_toTensor K L hL)

/-- `rightIso` is natural in cochain maps between complexes whose right factors are K-flat. -/
theorem rightIso_naturality {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensorPairModel R).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (rightIso K' L' hL').hom =
      (rightIso K L hL).hom ≫ DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) :=
  (Category.assoc _ _ _).trans (toTensor_naturality (modF R) (modRes R) a b)

/-- The comparison `T.comparison` of a packaged derived tensor product is natural in cochain maps
between K-flat complexes. -/
theorem leftIso_naturality (T : DerivedTensorProduct R)
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensorPairOf T).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (T.comparison K' L' hK' hL').hom =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) :=
  (Category.assoc _ _ _).trans (T.comparison_naturality a b hK hK' hL hL')

/-! ### The comparison at a pair of K-flat complexes -/

/-- **The comparison at a pair of K-flat complexes**: both legs land in `Q(K ⊗_R L)`, so they
compose to an isomorphism between the two derived tensor products there. -/
def modelComparison (T : DerivedTensorProduct R) (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    (tensorPairOf T).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (tensorPairModel R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  T.comparison K L hK hL ≪≫ (rightIso K L hL).symm

/-- The comparison at a pair of K-flat complexes is natural in cochain maps between them. -/
theorem modelComparison_naturality (T : DerivedTensorProduct R)
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ K') (b : L ⟶ L')
    (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensorPairOf T).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (modelComparison T K' L' hK' hL').hom =
      (modelComparison T K L hK hL).hom ≫
        (tensorPairModel R).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) :=
  CategoryTheory.comp_symm_naturality (T.comparison K L hK hL) (rightIso K L hL)
    (T.comparison K' L' hK' hL') (rightIso K' L' hL') _ _ _
    (leftIso_naturality T a b hK hK' hL hL') (rightIso_naturality a b hL hL')

/-! ### Descent along the K-flat localization -/

/-- `OneSided.kFlatQModulesPairIso` is natural, the target morphism being the image of chosen
cochain representatives of the two homotopy classes. -/
theorem kFlatQModulesPairIso_naturality
    {M N : (kFlatObjects (modF R)).FullSubcategory ×
      (kFlatObjects (modF R)).FullSubcategory} (g : M ⟶ N) :
    (OneSided.kFlatQModulesPair R).map g ≫ (OneSided.kFlatQModulesPairIso R N).hom =
      (OneSided.kFlatQModulesPairIso R M).hom ≫
        (DerivedCategory.Q.map g.1.hom.out ×ₘ DerivedCategory.Q.map g.2.hom.out) := by
  have key : ∀ {A B : (kFlatObjects (modF R)).FullSubcategory} (f : A ⟶ B),
      DerivedCategory.Qh.map f.hom ≫ (DerivedCategory.quotientCompQhIso _).hom.app B.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app A.obj.as ≫
          DerivedCategory.Q.map f.hom.out := fun {A B} f => by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality
      (C := ModuleCat.{u} R) f.hom.out
    rw [HomotopyCategory.quotient_map_out] at h
    exact h
  exact Prod.ext (key g.1) (key g.2)

/-- **The comparison at K-flat representatives, as an isomorphism of functors** on pairs of
K-flat objects of the homotopy category. -/
def modelsComparison (T : DerivedTensorProduct R) :
    OneSided.kFlatQModulesPair R ⋙ tensorPairOf T ≅
      OneSided.kFlatQModulesPair R ⋙ tensorPairModel R :=
  NatIso.ofComponents
    (fun M => (tensorPairOf T).mapIso (OneSided.kFlatQModulesPairIso R M) ≪≫
      modelComparison T M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((tensorPairModel R).mapIso (OneSided.kFlatQModulesPairIso R M)).symm)
    (fun {M N} g => by
      refine CategoryTheory.naturality_transport _ _ (OneSided.kFlatQModulesPairIso R M)
        (OneSided.kFlatQModulesPairIso R N)
        (modelComparison T M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (modelComparison T N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((OneSided.kFlatQModulesPair R).map g) _ (kFlatQModulesPairIso_naturality g) ?_
      exact modelComparison_naturality T g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] OneSided.kFlatQModulesPair_isLocalization

/-- **Any two derived tensor products of complexes of `R`-modules agree**: the bifunctor of a
packaged derived tensor product is isomorphic to the K-flat descent of the ordinary total tensor
complex, bifunctorially. -/
def tensorPairIso (T : DerivedTensorProduct R) : tensorPairOf T ≅ tensorPairModel R :=
  Localization.liftNatIso (OneSided.kFlatQModulesPair R) (OneSided.kFlatQuasiIsoModulesPair R)
    _ _ _ _ (modelsComparison T)

/-- The K-flat object of the homotopy category attached to a K-flat complex. -/
abbrev kFlatObj {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : K.KFlat) :
    (kFlatObjects (modF R)).FullSubcategory :=
  ⟨(HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K, hK⟩

/-- **The descended comparison, at a pair of K-flat complexes, is the model comparison.** -/
theorem tensorPairIso_hom_app (T : DerivedTensorProduct R)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (tensorPairIso T).hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (modelComparison T K L hK hL).hom := by
  set M : (kFlatObjects (modF R)).FullSubcategory ×
    (kFlatObjects (modF R)).FullSubcategory := (kFlatObj hK, kFlatObj hL) with hM
  have hcomp : (tensorPairIso T).hom.app ((OneSided.kFlatQModulesPair R).obj M) =
      (modelsComparison T).hom.app M := by
    dsimp only [tensorPairIso, Localization.liftNatIso, Iso.symm_hom]
    rw [Localization.liftNatTrans_app]
    have h₁ : Localization.Lifting.iso (OneSided.kFlatQModulesPair R)
        (OneSided.kFlatQuasiIsoModulesPair R)
        (OneSided.kFlatQModulesPair R ⋙ tensorPairOf T) (tensorPairOf T) = Iso.refl _ := rfl
    have h₂ : Localization.Lifting.iso (OneSided.kFlatQModulesPair R)
        (OneSided.kFlatQuasiIsoModulesPair R)
        (OneSided.kFlatQModulesPair R ⋙ tensorPairModel R) (tensorPairModel R) =
      Iso.refl _ := rfl
    rw [h₁, h₂]
    simp
  have hnat := (tensorPairIso T).hom.naturality (OneSided.kFlatQModulesPairIso R M).hom
  rw [hcomp] at hnat
  have hinv : IsIso ((tensorPairOf T).map (OneSided.kFlatQModulesPairIso R M).hom) :=
    inferInstanceAs (IsIso ((tensorPairOf T).mapIso (OneSided.kFlatQModulesPairIso R M)).hom)
  refine (cancel_epi ((tensorPairOf T).map
    (OneSided.kFlatQModulesPairIso R M).hom)).1 (hnat.trans ?_)
  dsimp only [modelsComparison, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-! ### The canonical map to the ordinary total tensor complex -/

/-- **The canonical map of the K-flat descent to the ordinary total tensor complex**, as a
morphism of bifunctors on pairs of cochain complexes of `R`-modules:

`QK ⊗^𝐋_R QL ⟶ Q(Tot(K ⊗_R L))`,

for arbitrary `K` and `L`.  Its components are `CochainComplex.KFlatBifunctor.toTensor`. -/
def modelToTensorNatTrans (R : Type u) [CommRing R] :
    qPair R ⋙ tensorPairModel R ⟶ totalTensorPair R ⋙ DerivedCategory.Q where
  app KL := toTensor (modF R) (modRes R) KL.1 KL.2
  naturality _ _ g :=
    (Category.assoc _ _ _).trans (toTensor_naturality' (modF R) (modRes R) g.1 g.2)

/-- **The canonical map from a packaged derived tensor product to the ordinary total tensor
complex**, as a morphism of bifunctors on pairs of cochain complexes of `R`-modules:

`QK ⊗^𝐋_R QL ⟶ Q(Tot(K ⊗_R L))`,

for arbitrary `K` and `L`. -/
def derivedToTensorNatTrans (T : DerivedTensorProduct R) :
    qPair R ⋙ tensorPairOf T ⟶ totalTensorPair R ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft (qPair R) (tensorPairIso T).hom ≫ modelToTensorNatTrans R

/-- The canonical map at a pair of complexes, written out. -/
theorem derivedToTensorNatTrans_app (T : DerivedTensorProduct R)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedToTensorNatTrans T).app (K, L) =
      (tensorPairIso T).hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        toTensor (modF R) (modRes R) K L :=
  NatTrans.comp_app _ _ _

/-- **At a pair of K-flat complexes the canonical map is the comparison of [Stacks, Tag 0BYI].** -/
theorem derivedToTensorNatTrans_app_eq_comparison (T : DerivedTensorProduct R)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (derivedToTensorNatTrans T).app (K, L) = (T.comparison K L hK hL).hom := by
  rw [derivedToTensorNatTrans_app T K L, tensorPairIso_hom_app T K L hK hL]
  dsimp only [modelComparison, Iso.trans_hom, Iso.symm_hom]
  show ((T.comparison K L hK hL).hom ≫ (rightIso K L hL).inv) ≫ (rightIso K L hL).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The canonical map at a K-flat right factor is invertible**, for an arbitrary left
factor. -/
theorem isIso_derivedToTensorNatTrans_app (T : DerivedTensorProduct R)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    IsIso ((derivedToTensorNatTrans T).app (K, L)) := by
  have := isIso_toTensor K L hL
  rw [derivedToTensorNatTrans_app T K L]
  infer_instance

/-! ### The canonical derived tensor product of Tag 064M -/

/-- **The canonical map from the derived tensor product of complexes of `R`-modules to the
ordinary total tensor complex.**  The derived tensor product is the canonical one of
[Stacks, Tag 064M]. -/
def canonicalDerivedToTensorNatTrans (R : Type u) [CommRing R] :
    qPair R ⋙
        Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R) ⟶
      totalTensorPair R ⋙ DerivedCategory.Q :=
  derivedToTensorNatTrans (canonicalDerivedTensorProduct R)

/-- At a pair of K-flat complexes the canonical map is the K-flat comparison of
[Stacks, Tag 064M]. -/
theorem canonicalDerivedToTensorNatTrans_app_eq_comparison (R : Type u) [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (canonicalDerivedToTensorNatTrans R).app (K, L) =
      ((canonicalDerivedTensorProduct R).comparison K L hK hL).hom :=
  derivedToTensorNatTrans_app_eq_comparison _ K L hK hL

end CochainComplex.DerivedTensor.ToTotal

end
