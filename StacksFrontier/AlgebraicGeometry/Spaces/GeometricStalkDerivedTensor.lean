module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafifyLocallySmall
public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TriangulatedSubcategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# The geometric stalk of a derived tensor product of algebraic spaces

Let `X` be an algebraic space and `x̄` a geometric point of `X`.  For `E, K ∈ D(𝒪_X)` the
derived geometric stalk of `E ⊗ᴸ K` is the derived tensor product of the stalks over the
geometric stalk ring:

`(E ⊗ᴸ_{𝒪_X} K)_x̄ ≅ E_x̄ ⊗ᴸ_{𝒪_{X,x̄}} K_x̄`,

naturally in `E` and `K`.

## Main definitions

* `AlgebraicGeometry.Space.stalkKFlatObjects`: the complexes of `𝒪_X`-modules which are K-flat
  and whose stalk complex at `x̄` is K-flat, as a triangulated property of `K(𝒪_X)`.
* `AlgebraicGeometry.Space.derivedTensorGeometricStalkIso`: the isomorphism above, as an
  isomorphism of bifunctors `D(𝒪_X) ⥤ D(𝒪_X) ⥤ D(𝒪_{X,x̄})`.

## Main results

* `AlgebraicGeometry.Space.stalkKFlatComplexQ_isLocalization`: `D(𝒪_X)` is the localization of
  those complexes at the quasi-isomorphisms.
* `AlgebraicGeometry.Space.derivedTensorGeometricStalkIso_hom_app_app`: on a pair of such
  complexes the isomorphism is the composite of the K-flat comparisons of Stacks 06YU on both
  sides with the stalk of the total tensor complex (Stacks 03EL at the point of Stacks 04K0).

## Implementation notes

The derived tensor product of `𝒪_X`-modules is
`AlgebraicGeometry.Space.smallEtaleDerivedTensor`, the canonical derived tensor product of
Stacks 06YU on the small étale site, and the one of `𝒪_{X,x̄}`-modules is
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` (Stacks 0BYI).  Both are computed
by the total tensor complex on K-flat complexes.  The isomorphism is therefore assembled on the
complexes which are K-flat with K-flat stalk complex at `x̄`, which resolve every complex
(`AlgebraicGeometry.Space.exists_kFlat_resolution_kFlat_geometricStalks`, via Stacks 06YS), and
descended by `CategoryTheory.Localization.lift₂NatIso`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w d

/- A module imported here brings the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` into scope; it gives `Abelian` for these
categories of modules at a universe join that is never the one used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso` is natural in
the left-hand variable. -/
lemma stalkSheafTensorIso_naturality_left
    {A A' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A ⟶ A')
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.sheafModuleFiberOfCommRing Φ O).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).map f).app B) ≫
        (stalkSheafTensorIso Φ O A' B).hom =
      (stalkSheafTensorIso Φ O A B).hom ≫
        ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).map
          ((Stacks.sheafModuleFiberOfCommRing Φ O).map f)).app
            ((Stacks.sheafModuleFiberOfCommRing Φ O).obj B) :=
  tensorSheafifyIso_naturality_left Φ O (φ := f.val) B.val

end Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, v, w, d} X)

/-- The K-flat comparison of a derived tensor product is natural in the first complex alone. -/
theorem comparison_naturality_left
    {K K' L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ}
    (f : K ⟶ K') (hK : IsKFlat X.O K) (hK' : IsKFlat X.O K') (hL : IsKFlat X.O L) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (T.comparison K' L hK' hL).hom =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f (𝟙 L)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have h := T.comparison_naturality f (𝟙 L) hK hK' hL hL
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- The K-flat comparison of a derived tensor product is natural in the second complex
alone. -/
theorem comparison_naturality_right
    (K : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ)
    {L L' : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ} (g : L ⟶ L')
    (hK : IsKFlat X.O K) (hL : IsKFlat X.O L) (hL' : IsKFlat X.O L') :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (T.comparison K L' hK hL').hom =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 K) g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have h := T.comparison_naturality (𝟙 K) g hK hK hL hL'
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h

end Stacks.SheafOfModules.DerivedTensorProduct

namespace CochainComplex.DerivedTensor.DerivedTensorProduct

/- `CochainComplex.DerivedTensor.DerivedTensorProduct` is stated for the standard derived category
of `R`-modules; the global instance `ModuleCat.hasDerivedCategory` is found first and is not that
one, so it is switched off in this namespace. -/

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] (T : DerivedTensorProduct R)

/-- The K-flat comparison of a derived tensor product over a ring is natural in the first
complex alone, with the total tensor complex written as `Functor.map₂HomologicalComplex`. -/
theorem comparison_naturality_map₂_left {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⟶ K') (hK : K.KFlat) (hK' : K'.KFlat)
    (hL : L.KFlat) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (T.comparison K' L hK' hL).hom =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map ((((curriedTensor (ModuleCat.{u} R)).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app L) := by
  have h := T.comparison_naturality f (𝟙 L) hK hK' hL hL
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- The K-flat comparison of a derived tensor product over a ring is natural in the second
complex alone, with the total tensor complex written as `Functor.map₂HomologicalComplex`. -/
theorem comparison_naturality_map₂_right (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L') (hK : K.KFlat) (hL : L.KFlat)
    (hL' : L'.KFlat) :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (T.comparison K L' hK hL').hom =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map ((((curriedTensor (ModuleCat.{u} R)).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map g) := by
  have h := T.comparison_naturality (𝟙 K) g hK hK hL hL'
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h

end CochainComplex.DerivedTensor.DerivedTensorProduct

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (x : GeometricPoint B S hS X.1)

attribute [local instance] AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

/-- The stalk functor at `x̄` on `𝒪_X`-modules, valued in modules over the geometric stalk ring
(Stacks 04K0, the module-valued fibre of Stacks 04EQ). -/
abbrev geometricStalkModuleFunctor :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      ModuleCat.{u} (geometricStalkRing B S hS x) :=
  Stacks.sheafModuleFiberOfCommRing.{u} (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O

/-- The stalk functor at `x̄` is additive. -/
instance : (geometricStalkModuleFunctor x).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O

/-- The stalk functor at `x̄` preserves finite limits. -/
instance : PreservesFiniteLimits (geometricStalkModuleFunctor x) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O

/-- The stalk functor at `x̄` preserves finite colimits. -/
instance : PreservesFiniteColimits (geometricStalkModuleFunctor x) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O

variable (X) in
/-- The total tensor complex of complexes of `𝒪_X`-modules, Stacks 06YU's
`Stacks.SheafOfModules.Tensor.tensorComplex` on the small étale site. -/
abbrev smallEtaleTensorComplex :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS X.1 X.2).O

/-- **The complexes which are K-flat with K-flat stalk complex at `x̄`**, as a property of the
homotopy category of `𝒪_X`-modules. -/
def stalkKFlatObjects :
    ObjectProperty (HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :=
  Stacks.SheafOfModules.kFlatObjects (smallEtaleRingedTopos B S hS X).O ⊓
    (CochainComplex.KFlatBifunctor.kFlatObjects
        (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))).inverseImage
      ((geometricStalkModuleFunctor x).mapHomotopyCategory (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.Space.stalkKFlatObjects x` is closed under isomorphisms. -/
instance stalkKFlatObjects_isClosedUnderIsomorphisms :
    (stalkKFlatObjects x).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨(Stacks.SheafOfModules.kFlatObjects (smallEtaleRingedTopos B S hS X).O).prop_of_iso e h.1,
      (CochainComplex.KFlatBifunctor.kFlatObjects
        (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))).prop_of_iso
      (((geometricStalkModuleFunctor x).mapHomotopyCategory (ComplexShape.up ℤ)).mapIso e) h.2⟩

/-- `AlgebraicGeometry.Space.stalkKFlatObjects x` is a triangulated subcategory of the homotopy
category. -/
instance stalkKFlatObjects_isTriangulated : (stalkKFlatObjects x).IsTriangulated := by
  have := Stacks.SheafOfModules.kFlatObjects_isTriangulated (smallEtaleRingedTopos B S hS X).O
  have := CochainComplex.KFlatBifunctor.kFlatObjects_isTriangulated
    (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))
  have : ((CochainComplex.KFlatBifunctor.kFlatObjects
        (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))).inverseImage
      ((geometricStalkModuleFunctor x).mapHomotopyCategory
        (ComplexShape.up ℤ))).IsClosedUnderIsomorphisms :=
    inferInstance
  have : ((CochainComplex.KFlatBifunctor.kFlatObjects
        (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))).inverseImage
      ((geometricStalkModuleFunctor x).mapHomotopyCategory (ComplexShape.up ℤ))).IsTriangulated :=
    inferInstance
  exact inferInstanceAs (ObjectProperty.IsTriangulated (_ ⊓ _))

/-- **Resolutions by complexes K-flat with K-flat stalk complex at `x̄`.** Every complex of
`𝒪_X`-modules receives a quasi-isomorphism from such a complex. -/
theorem exists_stalkKFlat_resolution
    (M : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
      (s : P ⟶ M), QuasiIso s ∧
        stalkKFlatObjects x ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) := by
  obtain ⟨P, s, hs, hP, hst⟩ := exists_kFlat_resolution_kFlat_geometricStalks X M
  exact ⟨P, s, hs, hP.1, hst x⟩

/-- The quasi-isomorphisms between objects of `stalkKFlatObjects x`. -/
abbrev stalkKFlatQuasiIso : MorphismProperty (stalkKFlatObjects x).FullSubcategory :=
  (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).inverseImage (stalkKFlatObjects x).ι

/-- The inclusion of `stalkKFlatObjects x`, as a morphism of localizers. -/
def stalkKFlatLocalizer :
    LocalizerMorphism (stalkKFlatQuasiIso x)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ)) where
  functor := (stalkKFlatObjects x).ι
  map _ _ _ hf := hf

/-- The inclusion of `AlgebraicGeometry.Space.stalkKFlatObjects x` induces an equivalence of the
localizations at the quasi-isomorphisms. -/
theorem stalkKFlatLocalizer_isLocalizedEquivalence :
    (stalkKFlatLocalizer x).IsLocalizedEquivalence := by
  have hW := Stacks.SheafOfModules.quasiIso_isSaturated_and_isCompatibleWithTriangulation
    (smallEtaleRingedTopos B S hS X).O
  let _ : (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)).IsCompatibleWithTriangulation := hW.2
  have h := stalkKFlatObjects x
    |>.isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ)) hW.1
  refine h.2.2 fun K => ?_
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨P, s, hs, hP⟩ := exists_stalkKFlat_resolution x M
  exact ⟨{
    X₁ := ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, hP⟩
    w := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s
    hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs }⟩

/-- `D(𝒪_X)` is the localization of `stalkKFlatObjects x` at the quasi-isomorphisms. -/
instance stalkKFlatQ_isLocalization :
    ((stalkKFlatObjects x).ι ⋙ DerivedCategory.Qh).IsLocalization (stalkKFlatQuasiIso x) := by
  have := stalkKFlatLocalizer_isLocalizedEquivalence x
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (stalkKFlatLocalizer x) DerivedCategory.Qh

/-- The complexes of `𝒪_X`-modules which are K-flat with K-flat stalk complex at `x̄`. -/
abbrev stalkKFlatComplexes :
    ObjectProperty
      (CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :=
  ObjectProperty.complexSubcategory (stalkKFlatObjects x)

/-- The functor from `stalkKFlatComplexes x` to `D(𝒪_X)`. -/
abbrev stalkKFlatComplexQ :
    (stalkKFlatComplexes x).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (stalkKFlatComplexes x).ι ⋙ DerivedCategory.Q

/-- The quasi-isomorphisms between complexes of `stalkKFlatComplexes x`. -/
abbrev stalkKFlatComplexQuasiIso : MorphismProperty (stalkKFlatComplexes x).FullSubcategory :=
  (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).inverseImage (stalkKFlatComplexes x).ι

/-- **`D(𝒪_X)` is the localization of the complexes K-flat with K-flat stalk complex at `x̄`**
at the quasi-isomorphisms between them. -/
instance stalkKFlatComplexQ_isLocalization :
    (stalkKFlatComplexQ x).IsLocalization (stalkKFlatComplexQuasiIso x) :=
  ObjectProperty.ι_comp_Q_isLocalization _

/-! ### The stalk of the total tensor complex -/

/-- The stalk functor at `x̄` commutes with the coproducts of the antidiagonals of a total
complex. -/
instance preservesColimitsOfShape_antidiagonal_sheafModuleFiber (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (geometricStalkModuleFunctor x) := by
  have : PreservesColimitsOfSize.{0, 0} (geometricStalkModuleFunctor x) :=
    Stacks.preservesColimits_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  infer_instance

/-- **The stalk at `x̄` of the total tensor complex** of two complexes of `𝒪_X`-modules is the
total tensor complex of their stalk complexes (Stacks 03EL at the point of Stacks 04K0, in each
bidegree), naturally in both complexes. -/
def stalkTensorComplexNatIso :
    smallEtaleTensorComplex X ⋙
      (Functor.whiskeringRight _ _ _).obj
        ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)) ≅
    (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x))).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.transportNatIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O)
    (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x)))
    (geometricStalkModuleFunctor x) (geometricStalkModuleFunctor x) (geometricStalkModuleFunctor x)
    (Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O)
    (fun f N =>
      Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso_naturality_left
        (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O f N)
    (fun M _ _ g =>
      Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso_naturality_right
        (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O M g)

/-! ### The comparison on complexes K-flat with K-flat stalk complex -/

/-- The derived tensor product of `𝒪_X`-modules followed by the derived geometric stalk at `x̄`:
`(E, K) ↦ (E ⊗ᴸ K)_x̄`. -/
abbrev derivedTensorGeometricStalkSource :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x)) :=
  smallEtaleDerivedTensor B S hS X ⋙
    (Functor.whiskeringRight _ _ _).obj (geometricDerivedStalk B S hS x)

/-- The derived geometric stalks at `x̄` followed by the derived tensor product over the
geometric stalk ring: `(E, K) ↦ E_x̄ ⊗ᴸ K_x̄`. -/
abbrev derivedTensorGeometricStalkTarget :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x)) :=
  geometricDerivedStalk B S hS x ⋙
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
      (geometricStalkRing B S hS x)).tensor ⋙
    (Functor.whiskeringLeft _ _ _).obj (geometricDerivedStalk B S hS x)

/-- A bifunctor out of `D(𝒪_X)`, restricted to the complexes K-flat with K-flat stalk complex
at `x̄`. -/
abbrev stalkKFlatRestrict
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x))) :
    (stalkKFlatComplexes x).FullSubcategory ⥤ (stalkKFlatComplexes x).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x)) :=
  (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexQ x)).obj (stalkKFlatComplexQ x)).obj F

/-- The K-flat comparison of Stacks 06YU on the small étale site, followed by the derived
geometric stalk. -/
def derivedTensorGeometricStalkComparison₁ :
    stalkKFlatRestrict x (derivedTensorGeometricStalkSource x) ≅
      (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (smallEtaleTensorComplex X ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q ⋙ geometricDerivedStalk B S hS x)) :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents
      (fun L => (geometricDerivedStalk B S hS x).mapIso
        ((smallEtaleDerivedTensorProduct B S hS X).comparison P.obj L.obj P.property.1
          L.property.1))
      (fun {L L'} g =>
        ((geometricDerivedStalk B S hS x).map_comp _ _).symm.trans
          ((congrArg (geometricDerivedStalk B S hS x).map
            (Stacks.SheafOfModules.DerivedTensorProduct.comparison_naturality_right
              (smallEtaleDerivedTensorProduct B S hS X) P.obj g.hom P.property.1 L.property.1
              L'.property.1)).trans
            ((geometricDerivedStalk B S hS x).map_comp _ _))))
    (fun {P P'} f => by
      ext L
      exact ((geometricDerivedStalk B S hS x).map_comp _ _).symm.trans
        ((congrArg (geometricDerivedStalk B S hS x).map
          (Stacks.SheafOfModules.DerivedTensorProduct.comparison_naturality_left
            (smallEtaleDerivedTensorProduct B S hS X) f.hom P.property.1 P'.property.1
            L.property.1)).trans
          ((geometricDerivedStalk B S hS x).map_comp _ _)))

/-- The derived geometric stalk of a complex is its stalk complex. -/
def derivedTensorGeometricStalkComparison₂ :
    (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (smallEtaleTensorComplex X ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q ⋙ geometricDerivedStalk B S hS x)) ≅
      (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (smallEtaleTensorComplex X ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)) :=
  (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
      (stalkKFlatComplexes x).ι).mapIso
    (Functor.isoWhiskerLeft (smallEtaleTensorComplex X)
      ((Functor.whiskeringRight _ _ _).mapIso
        (geometricStalkModuleFunctor x).mapDerivedCategoryFactors))

/-- The stalk of the total tensor complex, Stacks 03EL in each bidegree. -/
def derivedTensorGeometricStalkComparison₃ :
    (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (smallEtaleTensorComplex X ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)) ≅
      (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ))) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q) :=
  (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
      (stalkKFlatComplexes x).ι).mapIso
    (Functor.isoWhiskerRight (stalkTensorComplexNatIso x)
      ((Functor.whiskeringRight _ _ _).obj DerivedCategory.Q))

/-- The K-flat comparison of Stacks 0BYI over the geometric stalk ring, at the stalk complexes,
which are K-flat. -/
def derivedTensorGeometricStalkComparison₄ :
    (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ))) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q) ≅
      (((Functor.whiskeringLeft₂ _).obj ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
          ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (geometricStalkRing B S hS x)).tensor :=
  (NatIso.ofComponents (F := (((Functor.whiskeringLeft₂ _).obj ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
          ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (geometricStalkRing B S hS x)).tensor)
    (G := (((Functor.whiskeringLeft₂ _).obj (stalkKFlatComplexes x).ι).obj
          (stalkKFlatComplexes x).ι).obj
        (((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (curriedTensor (ModuleCat.{u} (geometricStalkRing B S hS x))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            ((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ))) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q))
    (fun P => NatIso.ofComponents
      (fun L => (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (geometricStalkRing B S hS x)).comparison _ _ P.property.2 L.property.2)
      (fun {L L'} g =>
        CochainComplex.DerivedTensor.DerivedTensorProduct.comparison_naturality_map₂_right
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            (geometricStalkRing B S hS x)) _ _ P.property.2 L.property.2 L'.property.2))
    (fun {P P'} f => by
      ext L
      exact CochainComplex.DerivedTensor.DerivedTensorProduct.comparison_naturality_map₂_left
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (geometricStalkRing B S hS x)) _ _ P.property.2 P'.property.2 L.property.2)).symm

/-- The stalk complexes compute the derived geometric stalks, in both variables. -/
def derivedTensorGeometricStalkComparison₅ :
    (((Functor.whiskeringLeft₂ _).obj ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
          ((stalkKFlatComplexes x).ι ⋙
            (geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)).obj
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (geometricStalkRing B S hS x)).tensor ≅
      stalkKFlatRestrict x (derivedTensorGeometricStalkTarget x) :=
  ((((Functor.whiskeringLeft₂ _).mapIso
      (Functor.isoWhiskerLeft (stalkKFlatComplexes x).ι
        (geometricStalkModuleFunctor x).mapDerivedCategoryFactors.symm)).app _).app _) ≪≫
    ((((Functor.whiskeringLeft₂ _).obj ((stalkKFlatComplexes x).ι ⋙ DerivedCategory.Q ⋙
        geometricDerivedStalk B S hS x)).mapIso
      (Functor.isoWhiskerLeft (stalkKFlatComplexes x).ι
        (geometricStalkModuleFunctor x).mapDerivedCategoryFactors.symm)).app _)

/-- The comparison of the two bifunctors on the complexes K-flat with K-flat stalk complex at
`x̄`. -/
def derivedTensorGeometricStalkRestrictIso :
    stalkKFlatRestrict x (derivedTensorGeometricStalkSource x) ≅
      stalkKFlatRestrict x (derivedTensorGeometricStalkTarget x) :=
  derivedTensorGeometricStalkComparison₁ x ≪≫ derivedTensorGeometricStalkComparison₂ x ≪≫
    derivedTensorGeometricStalkComparison₃ x ≪≫ derivedTensorGeometricStalkComparison₄ x ≪≫
      derivedTensorGeometricStalkComparison₅ x

/-- Restriction to the complexes K-flat with K-flat stalk complex at `x̄`, as a lifting datum. -/
@[instance_reducible]
def stalkKFlatLifting
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x))) :
    Localization.Lifting₂ (stalkKFlatComplexQ x) (stalkKFlatComplexQ x)
      (stalkKFlatComplexQuasiIso x) (stalkKFlatComplexQuasiIso x) (stalkKFlatRestrict x F) F :=
  ⟨Iso.refl _⟩

/-- **The geometric stalk of a derived tensor product.** For an algebraic space `X`, a
geometric point `x̄` of `X` and `E, K ∈ D(𝒪_X)`,

`(E ⊗ᴸ_{𝒪_X} K)_x̄ ≅ E_x̄ ⊗ᴸ_{𝒪_{X,x̄}} K_x̄`,

naturally in `E` and `K`. -/
def derivedTensorGeometricStalkIso :
    derivedTensorGeometricStalkSource x ≅ derivedTensorGeometricStalkTarget x :=
  letI := stalkKFlatLifting x (derivedTensorGeometricStalkSource x)
  letI := stalkKFlatLifting x (derivedTensorGeometricStalkTarget x)
  Localization.lift₂NatIso (stalkKFlatComplexQ x) (stalkKFlatComplexQ x)
    (stalkKFlatComplexQuasiIso x) (stalkKFlatComplexQuasiIso x)
    (stalkKFlatRestrict x (derivedTensorGeometricStalkSource x))
    (stalkKFlatRestrict x (derivedTensorGeometricStalkTarget x))
    (derivedTensorGeometricStalkSource x) (derivedTensorGeometricStalkTarget x)
    (derivedTensorGeometricStalkRestrictIso x)

/-- On a pair of complexes K-flat with K-flat stalk complex at `x̄`, the isomorphism
`derivedTensorGeometricStalkIso` is the composite of the comparisons above. -/
theorem derivedTensorGeometricStalkIso_hom_app_app
    (P L : (stalkKFlatComplexes x).FullSubcategory) :
    ((derivedTensorGeometricStalkIso x).hom.app (DerivedCategory.Q.obj P.obj)).app
        (DerivedCategory.Q.obj L.obj) =
      ((derivedTensorGeometricStalkRestrictIso x).hom.app P).app L := by
  let := stalkKFlatLifting x (derivedTensorGeometricStalkSource x)
  let := stalkKFlatLifting x (derivedTensorGeometricStalkTarget x)
  refine (Localization.lift₂NatTrans_app_app (stalkKFlatComplexQ x) (stalkKFlatComplexQ x)
    (stalkKFlatComplexQuasiIso x) (stalkKFlatComplexQuasiIso x)
    (stalkKFlatRestrict x (derivedTensorGeometricStalkSource x))
    (stalkKFlatRestrict x (derivedTensorGeometricStalkTarget x))
    (derivedTensorGeometricStalkSource x) (derivedTensorGeometricStalkTarget x)
    (derivedTensorGeometricStalkRestrictIso x).hom P L).trans ?_
  exact (Category.id_comp _).trans (Category.comp_id _)

end AlgebraicGeometry.Space

end
