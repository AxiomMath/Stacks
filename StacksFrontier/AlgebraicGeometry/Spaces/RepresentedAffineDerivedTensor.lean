module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapTensorProduct
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DevissageNatTrans

/-!
# The derived tensor product on an affine representable algebraic space

Let `U` be an object of the big fppf site with affine underlying scheme and ring of global
functions `A`, and let `Φ : D(A) ⥤ D(𝒪_{yoneda.obj U})` be the derived associated-module
functor.  Then `Φ(E) ⊗ᴸ Φ(K) ≅ Φ(E ⊗ᴸ_A K)`, naturally in `E` and `K`.

## Main results

* `AlgebraicGeometry.Space.isKFlat_of_geometricStalks`: on any algebraic space, a complex of
  `𝒪`-modules whose stalk complex at every geometric point is K-flat is K-flat (Stacks 0DEN (2)
  at the geometric points).
* `AlgebraicGeometry.Space.isKFlat_representedAffineToposAssociated`: the associated complex of a
  K-flat complex of `A`-modules is K-flat.
* `AlgebraicGeometry.Space.representedAffineDerivedTensorBifunctorIso`: the isomorphism of
  bifunctors `Φ(-) ⊗ᴸ Φ(-) ≅ Φ(- ⊗ᴸ_A -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u


namespace CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The K-flat complexes of `R`-modules. -/
abbrev kFlatModuleComplexes : ObjectProperty (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ObjectProperty.complexSubcategory
    (CochainComplex.KFlatBifunctor.kFlatObjects (curriedTensor (ModuleCat.{u} R)))

/-- The K-flat complexes of `R`-modules, in `D(R)`. -/
abbrev kFlatModuleComplexQ :
    (kFlatModuleComplexes R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (kFlatModuleComplexes R).ι ⋙ DerivedCategory.Q

/-- The quasi-isomorphisms between K-flat complexes of `R`-modules. -/
abbrev kFlatModuleComplexQuasiIso : MorphismProperty (kFlatModuleComplexes R).FullSubcategory :=
  (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).inverseImage (kFlatModuleComplexes R).ι

/-- **`D(R)` is the localization of the K-flat complexes of `R`-modules** at the
quasi-isomorphisms between them (Stacks 06Y4 supplies the resolutions). -/
instance kFlatModuleComplexQ_isLocalization :
    (kFlatModuleComplexQ R).IsLocalization (kFlatModuleComplexQuasiIso R) :=
  ObjectProperty.ι_comp_Q_isLocalization _

end CochainComplex.DerivedTensor

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### K-flatness at the geometric points -/

/-- **K-flatness from the geometric stalks.**  A complex of `𝒪_X`-modules whose stalk complex at
every geometric point is K-flat is K-flat: the geometric points are a conservative family
(Stacks 04K5) and stalks commute with total tensor complexes (Stacks 03EL). -/
theorem isKFlat_of_geometricStalks {X : AlgebraicSpaces B S hS}
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hK : ∀ x : GeometricPoint B S hS X.1,
      CochainComplex.KFlat
        (((geometricStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS X.1 X.2).O K := by
  intro F hF
  refine (Stacks.acyclic_iff_forall_acyclic_sheafModuleFiberOfCommRing
    (smallEtaleRingedTopos B S hS X).O
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2) _).2 fun Φ => ?_
  rcases Φ with ⟨_, ⟨x⟩⟩
  exact HomologicalComplex.Acyclic.of_iso (((stalkTensorComplexNatIso x).app F).app K).symm
    (hK x _ (Stacks.acyclic_map_sheafModuleFiberOfCommRing (smallEtaleRingedTopos B S hS X).O
      (etaleSitePoint B S hS X.1 x X.2) hF))

variable (B S hS) in
/-- **The associated complex of a K-flat complex is K-flat.**  For a K-flat complex `P` of
`A`-modules, the stalk of `P^~` at a geometric point `x̄` is `P ⊗_A 𝒪_{x̄}`, which is K-flat. -/
theorem isKFlat_representedAffineToposAssociated (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hP : P.KFlat) :
    Stacks.SheafOfModules.IsKFlat
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O
      (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  isKFlat_of_geometricStalks (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) _
    fun x => CochainComplex.KFlat.of_iso ((representedAffineComplexStalkIso B S hS U x).app P).symm
      (RingTheory.TorIndependence.kFlat_mapCochainComplex _ P hP)

/-! ### The associated module of a tensor product, in both variables -/

section Tensor

variable (B S hS) (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- At `M = A` the isomorphism `(A ⊗_A N)^~ ≅ A^~ ⊗ N^~` is the left unitor followed by the unit
constraint `N^~ ≅ A^~ ⊗ N^~`. -/
theorem representedAffineAssociatedTensorIso_hom_app_unit
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineAssociatedTensorIso B S hS U N).hom.app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
      (representedAffineAssociated B S hS U).map (λ_ N).hom ≫
        (representedAffineUnitTensorIso B S hS U _).inv := by
  change (representedAffineAssociated B S hS U).map
      ((representedAffineTensorSectionsNatTrans B S hS U N).app _) ≫
    (representedAffineAssociatedAdjunction B S hS U).counit.app _ = _
  rw [representedAffineTensorSectionsNatTrans_app_unit, Functor.map_comp, Category.assoc]
  refine congrArg ((representedAffineAssociated B S hS U).map (λ_ N).hom ≫ ·) ?_
  have h₁ := (representedAffineAssociatedAdjunction B S hS U).counit.naturality
    (representedAffineUnitTensorIso B S hS U ((representedAffineAssociated B S hS U).obj N)).inv
  have h₂ := (representedAffineAssociatedAdjunction B S hS U).left_triangle_components N
  simp only [Functor.comp_map, Functor.id_map] at h₁
  simp only [representedAffineTensorSectionsUnitIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  exact (congrArg ((representedAffineAssociated B S hS U).map
    ((representedAffineAssociatedAdjunction B S hS U).unit.app N) ≫ ·) h₁).trans
      (by rw [← Category.assoc, h₂]; exact Category.id_comp _)

/-- Given `f₁ ≫ l' = l ≫ g` and isomorphisms `u`, `u'` with `t ≫ u'.hom = u.hom ≫ Φ.map g`, the
composites `Φ.map f₁ ≫ Φ.map l' ≫ u'.inv` and `Φ.map l ≫ u.inv ≫ t` agree. -/
theorem map_comp_comp_inv_of_squares {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {a b c d : C} {x y : D} (f₁ : a ⟶ c) (l' : c ⟶ d) (l : a ⟶ b) (g : b ⟶ d)
    (hl : f₁ ≫ l' = l ≫ g) (u : x ≅ Φ.obj b) (u' : y ≅ Φ.obj d) (t : x ⟶ y)
    (hu : t ≫ u'.hom = u.hom ≫ Φ.map g) :
    Φ.map f₁ ≫ Φ.map l' ≫ u'.inv = Φ.map l ≫ u.inv ≫ t := by
  rw [← Category.assoc, ← Φ.map_comp, hl, Φ.map_comp, Category.assoc]
  refine congrArg (Φ.map l ≫ ·) ?_
  rw [Iso.eq_inv_comp, ← reassoc_of% hu, Iso.hom_inv_id, Category.comp_id]

/-- **The isomorphism `(M ⊗_A N)^~ ≅ M^~ ⊗ N^~` is natural in `N`.**  Both composites are natural
in `M` and agree at `M = A`, where the isomorphism is the left unitor followed by the unit
constraint. -/
theorem representedAffineAssociatedTensorIso_hom_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineAssociated B S hS U).map (M ◁ g) ≫
        (representedAffineAssociatedTensorIso B S hS U N').hom.app M =
      (representedAffineAssociatedTensorIso B S hS U N).hom.app M ≫
        ((representedAffineTensor B S hS U).obj ((representedAffineAssociated B S hS U).obj M)).map
          ((representedAffineAssociated B S hS U).map g) := by
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u}
      (tensorRight N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤ _) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have h : Functor.whiskerRight ((tensoringRight _).map g) (representedAffineAssociated B S hS U) ≫
      (representedAffineAssociatedTensorIso B S hS U N').hom =
      (representedAffineAssociatedTensorIso B S hS U N).hom ≫
        Functor.whiskerLeft (representedAffineAssociated B S hS U)
          ((representedAffineTensor B S hS U).flip.map
            ((representedAffineAssociated B S hS U).map g)) := by
    refine Stacks.EilenbergWatts.natTrans_ext_of_app_unit ?_
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      representedAffineAssociatedTensorIso_hom_app_unit,
      representedAffineAssociatedTensorIso_hom_app_unit, Category.assoc]
    exact map_comp_comp_inv_of_squares (representedAffineAssociated B S hS U) _ _ _ g
      (MonoidalCategory.leftUnitor_naturality g) _ _ _
      (representedAffineUnitTensorIso_naturality B S hS U
        ((representedAffineAssociated B S hS U).map g))
  exact NatTrans.congr_app h M

/-! ### The comparison on complexes -/

section ToposSpelling

/-- The tensor product of `𝒪`-modules on `yoneda.obj U`, in the ringed-topos spelling. -/
abbrev representedAffineToposTensor :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⥤
        SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The category of `𝒪`-modules on `yoneda.obj U` has all small colimits. -/
local instance (priority := 100000) hasColimitsOfSize_toposModules_yoneda :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) :=
  inferInstance

/-- The image under the associated-module functor of the tensor bicomplex of two complexes of
`A`-modules has a total complex. -/
instance hasTotal_mapBicomplex_representedAffineToposAssociated
    (K L : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex
      (representedAffineToposAssociated B S hS U)
      ((((curriedTensor (ModuleCat.{u}
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ) := fun _ =>
  ((hasColimitsOfSize_toposModules_yoneda B S hS U).has_colimits_of_shape _).has_colimit _

/-- The associated-module functor preserves coproducts indexed by the antidiagonal
`{(p, q) | p + q = n}`. -/
instance preservesColimitsOfShape_antidiagonal_representedAffineToposAssociated (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (representedAffineToposAssociated B S hS U) := by
  have : PreservesColimitsOfSize.{0, 0} (representedAffineToposAssociated B S hS U) :=
    (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  infer_instance

/-- `(P ⊗_A Q)^~ ≅ P^~ ⊗ Q^~` on complexes, in the ringed-topos spelling. -/
def representedAffineToposTensorComplexNatIso :
    (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)) ≅
    (representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (representedAffineToposTensor B S hS U).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.transportNatIso
    (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (representedAffineToposTensor B S hS U)
    (representedAffineToposAssociated B S hS U) (representedAffineToposAssociated B S hS U)
    (representedAffineToposAssociated B S hS U)
    (fun a b => (representedAffineAssociatedTensorIso B S hS U b).app a)
    (fun f b => (representedAffineAssociatedTensorIso B S hS U b).hom.naturality f)
    (fun a _ _ g => representedAffineAssociatedTensorIso_hom_naturality_right B S hS U a g)

/-- The component of `AlgebraicGeometry.Space.representedAffineToposTensorComplexNatIso`. -/
abbrev representedAffineToposTensorComplexIso
    (P L : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :=
  CochainComplex.KFlatBifunctor.transportComplexIso
    (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (representedAffineToposTensor B S hS U)
    (representedAffineToposAssociated B S hS U) (representedAffineToposAssociated B S hS U)
    (representedAffineToposAssociated B S hS U)
    (fun a b => (representedAffineAssociatedTensorIso B S hS U b).app a)
    (fun f b => (representedAffineAssociatedTensorIso B S hS U b).hom.naturality f)
    (fun a _ _ g => representedAffineAssociatedTensorIso_hom_naturality_right B S hS U a g) P L

/-- The isomorphism `(P ⊗_A L)^~ ≅ P^~ ⊗ L^~` on complexes is natural in `L`. -/
theorem representedAffineToposTensorComplexIso_naturality_right
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ}
    (g : L ⟶ L') :
    ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) g
            (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
            (ComplexShape.up ℤ)) ≫
        (representedAffineToposTensorComplexIso B S hS U P L').hom =
      (representedAffineToposTensorComplexIso B S hS U P L).hom ≫
        HomologicalComplex.mapBifunctorMap
          (𝟙 (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))
          (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) (representedAffineToposTensor B S hS U)
          (ComplexShape.up ℤ) := by
  refine CochainComplex.KFlatBifunctor.transportComplexIso_naturality_right _ _ _ _ _ _ ?_ ?_ P g
  exact fun f b => (representedAffineAssociatedTensorIso B S hS U b).hom.naturality f

/-- The isomorphism `(P ⊗_A L)^~ ≅ P^~ ⊗ L^~` on complexes is natural in `P`. -/
theorem representedAffineToposTensorComplexIso_naturality_left
    {P P' : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ} (f : P ⟶ P')
    (L : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap f (𝟙 L)
            (curriedTensor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
            (ComplexShape.up ℤ)) ≫
        (representedAffineToposTensorComplexIso B S hS U P' L).hom =
      (representedAffineToposTensorComplexIso B S hS U P L).hom ≫
        HomologicalComplex.mapBifunctorMap
          (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)
          (𝟙 (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) (representedAffineToposTensor B S hS U)
          (ComplexShape.up ℤ) := by
  refine CochainComplex.KFlatBifunctor.transportComplexIso_naturality_left _ _ _ _ _ _ ?_ ?_ f L
  exact fun f b => (representedAffineAssociatedTensorIso B S hS U b).hom.naturality f

/-- A functor carries a commutative square with invertible vertical sides to the square of the
inverses. -/
theorem map_inv_naturality {C D : Type*} [Category C] [Category D] (Q : C ⥤ D) {a b a' b' : C}
    (e : a ≅ b) (e' : a' ≅ b') (x : a ⟶ a') (y : b ⟶ b') (h : x ≫ e'.hom = e.hom ≫ y) :
    Q.map y ≫ Q.map e'.inv = Q.map e.inv ≫ Q.map x := by
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-! ### The derived comparison -/

/-- `Φ` on a localized complex is the localization of the associated complex, in the
ringed-topos spelling. -/
def representedAffineToposDerivedFactorsQ :
    DerivedCategory.Q ⋙ representedAffineToposDerivedAssociated B S hS U ≅
      (representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  representedAffineToposDerivedFactors B S hS U ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)

/-- The derived tensor product of the associated objects: `(E, K) ↦ Φ(E) ⊗ᴸ Φ(K)`. -/
abbrev representedAffineDerivedTensorSource :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) :=
  representedAffineToposDerivedAssociated B S hS U ⋙
    smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ ⋙
      (Functor.whiskeringLeft _ _ _).obj (representedAffineToposDerivedAssociated B S hS U)

/-- The associated object of the derived tensor product: `(E, K) ↦ Φ(E ⊗ᴸ_A K)`. -/
abbrev representedAffineDerivedTensorTarget :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) :=
  (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor ⋙
    (Functor.whiskeringRight _ _ _).obj (representedAffineToposDerivedAssociated B S hS U)

/-- A bifunctor out of `D(A)`, restricted to the K-flat complexes. -/
abbrev representedAffineKFlatRestrict
    (F : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))) :
    (CochainComplex.DerivedTensor.kFlatModuleComplexes
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).FullSubcategory ⥤
      (CochainComplex.DerivedTensor.kFlatModuleComplexes
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) :=
  (((Functor.whiskeringLeft₂ _).obj
      (CochainComplex.DerivedTensor.kFlatModuleComplexQ
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).obj
    (CochainComplex.DerivedTensor.kFlatModuleComplexQ
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).obj F

/-- The inclusion of the K-flat complexes of `A`-modules followed by the associated complex. -/
abbrev representedAffineKFlatAssociated :
    (CochainComplex.DerivedTensor.kFlatModuleComplexes
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).FullSubcategory ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ℤ :=
  (CochainComplex.DerivedTensor.kFlatModuleComplexes
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι ⋙
    (representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `Φ` on the K-flat complexes is the localization of the associated complex. -/
def representedAffineDerivedTensorComparison₁ :
    representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorSource B S hS U) ≅
      (((Functor.whiskeringLeft₂ _).obj
          (representedAffineKFlatAssociated B S hS U ⋙ DerivedCategory.Q)).obj
        (representedAffineKFlatAssociated B S hS U ⋙ DerivedCategory.Q)).obj
        (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) :=
  ((((Functor.whiskeringLeft₂ _).mapIso
      (Functor.isoWhiskerLeft (CochainComplex.DerivedTensor.kFlatModuleComplexes
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι
        (representedAffineToposDerivedFactorsQ B S hS U))).app
      ((CochainComplex.DerivedTensor.kFlatModuleComplexQ
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⋙
        representedAffineToposDerivedAssociated B S hS U)).app
      (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ≪≫
    ((((Functor.whiskeringLeft₂ _).obj
        (representedAffineKFlatAssociated B S hS U ⋙ DerivedCategory.Q)).mapIso
      (Functor.isoWhiskerLeft (CochainComplex.DerivedTensor.kFlatModuleComplexes
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι
        (representedAffineToposDerivedFactorsQ B S hS U))).app
      (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))

/-- The K-flat comparison of Stacks 06YU on `yoneda.obj U`, at associated complexes of K-flat
complexes, which are K-flat. -/
def representedAffineDerivedTensorComparison₂ :
    (((Functor.whiskeringLeft₂ _).obj
          (representedAffineKFlatAssociated B S hS U ⋙ DerivedCategory.Q)).obj
        (representedAffineKFlatAssociated B S hS U ⋙ DerivedCategory.Q)).obj
        (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ≅
      (((Functor.whiskeringLeft₂ _).obj (representedAffineKFlatAssociated B S hS U)).obj
          (representedAffineKFlatAssociated B S hS U)).obj
        ((representedAffineToposTensor B S hS U).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q) :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents
      (fun L => (smallEtaleDerivedTensorProduct B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).comparison
        ((representedAffineKFlatAssociated B S hS U).obj P)
        ((representedAffineKFlatAssociated B S hS U).obj L)
        (isKFlat_representedAffineToposAssociated B S hS U P.obj P.property)
        (isKFlat_representedAffineToposAssociated B S hS U L.obj L.property))
      (fun {L L'} g =>
        Stacks.SheafOfModules.DerivedTensorProduct.comparison_naturality_right
          (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          _ ((representedAffineKFlatAssociated B S hS U).map g)
          (isKFlat_representedAffineToposAssociated B S hS U P.obj P.property)
          (isKFlat_representedAffineToposAssociated B S hS U L.obj L.property)
          (isKFlat_representedAffineToposAssociated B S hS U L'.obj L'.property)))
    (fun {P P'} f => by
      ext L
      exact Stacks.SheafOfModules.DerivedTensorProduct.comparison_naturality_left
        (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        ((representedAffineKFlatAssociated B S hS U).map f)
        (isKFlat_representedAffineToposAssociated B S hS U P.obj P.property)
        (isKFlat_representedAffineToposAssociated B S hS U P'.obj P'.property)
        (isKFlat_representedAffineToposAssociated B S hS U L.obj L.property))

/-- The associated complex of the total tensor complex, `(P ⊗_A Q)^~ ≅ P^~ ⊗ Q^~`. -/
def representedAffineDerivedTensorComparison₃ :
    (((Functor.whiskeringLeft₂ _).obj (representedAffineKFlatAssociated B S hS U)).obj
          (representedAffineKFlatAssociated B S hS U)).obj
        ((representedAffineToposTensor B S hS U).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q) ≅
      (((Functor.whiskeringLeft₂ _).obj (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        ((curriedTensor (ModuleCat.{u}
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)) :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents
      (fun L => DerivedCategory.Q.mapIso
        (representedAffineToposTensorComplexIso B S hS U P.obj L.obj).symm)
      (fun {L L'} g => map_inv_naturality DerivedCategory.Q _ _ _ _
        (representedAffineToposTensorComplexIso_naturality_right B S hS U P.obj g.hom)))
    (fun {P P'} f => by
      ext L
      exact map_inv_naturality DerivedCategory.Q _ _ _ _
        (representedAffineToposTensorComplexIso_naturality_left B S hS U f.hom L.obj))

/-- The localization of the associated complex is `Φ` of the localization. -/
def representedAffineDerivedTensorComparison₄ :
    (((Functor.whiskeringLeft₂ _).obj (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        ((curriedTensor (ModuleCat.{u}
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((representedAffineToposAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              DerivedCategory.Q)) ≅
      (((Functor.whiskeringLeft₂ _).obj (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        ((curriedTensor (ModuleCat.{u}
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q ⋙ representedAffineToposDerivedAssociated B S hS U)) :=
  (((Functor.whiskeringLeft₂ _).obj (CochainComplex.DerivedTensor.kFlatModuleComplexes
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
    (CochainComplex.DerivedTensor.kFlatModuleComplexes
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).mapIso
    (Functor.isoWhiskerLeft ((curriedTensor (ModuleCat.{u}
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      ((Functor.whiskeringRight _ _ _).mapIso
        (representedAffineToposDerivedFactorsQ B S hS U).symm))

/-- The K-flat comparison over `A`, followed by `Φ`. -/
def representedAffineDerivedTensorComparison₅ :
    (((Functor.whiskeringLeft₂ _).obj (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        (CochainComplex.DerivedTensor.kFlatModuleComplexes
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).ι).obj
        ((curriedTensor (ModuleCat.{u}
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (DerivedCategory.Q ⋙ representedAffineToposDerivedAssociated B S hS U)) ≅
      representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorTarget B S hS U) :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents
      (fun L => (representedAffineToposDerivedAssociated B S hS U).mapIso
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).comparison _ _
          P.property L.property).symm)
      (fun {L L'} g => map_inv_naturality (representedAffineToposDerivedAssociated B S hS U) _ _ _ _
        (CochainComplex.DerivedTensor.DerivedTensorProduct.comparison_naturality_map₂_right
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ g.hom
          P.property L.property L'.property)))
    (fun {P P'} f => by
      ext L
      exact map_inv_naturality (representedAffineToposDerivedAssociated B S hS U) _ _ _ _
        (CochainComplex.DerivedTensor.DerivedTensorProduct.comparison_naturality_map₂_left
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ f.hom
          P.property P'.property L.property))

/-- The comparison of the two bifunctors on the K-flat complexes of `A`-modules. -/
def representedAffineDerivedTensorRestrictIso :
    representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorSource B S hS U) ≅
      representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorTarget B S hS U) :=
  representedAffineDerivedTensorComparison₁ B S hS U ≪≫
    representedAffineDerivedTensorComparison₂ B S hS U ≪≫
    representedAffineDerivedTensorComparison₃ B S hS U ≪≫
    representedAffineDerivedTensorComparison₄ B S hS U ≪≫
    representedAffineDerivedTensorComparison₅ B S hS U

/-- Restriction to the K-flat complexes of `A`-modules, as a lifting datum. -/
@[instance_reducible]
def representedAffineKFlatLifting
    (F : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
        DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))) :
    Localization.Lifting₂
      (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
      (representedAffineKFlatRestrict B S hS U F) F :=
  ⟨Iso.refl _⟩

/-- **The derived tensor product on an affine representable algebraic space.**  For `E, K ∈ D(A)`,

`Φ(E) ⊗ᴸ_{𝒪} Φ(K) ≅ Φ(E ⊗ᴸ_A K)`,

naturally in `E` and `K`, where `Φ : D(A) ⥤ D(𝒪_{yoneda.obj U})` is the derived
associated-module functor. -/
def representedAffineDerivedTensorBifunctorIso :
    representedAffineDerivedTensorSource B S hS U ≅ representedAffineDerivedTensorTarget B S hS U :=
  letI := representedAffineKFlatLifting B S hS U (representedAffineDerivedTensorSource B S hS U)
  letI := representedAffineKFlatLifting B S hS U (representedAffineDerivedTensorTarget B S hS U)
  Localization.lift₂NatIso
    (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorSource B S hS U))
    (representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorTarget B S hS U))
    (representedAffineDerivedTensorSource B S hS U) (representedAffineDerivedTensorTarget B S hS U)
    (representedAffineDerivedTensorRestrictIso B S hS U)

/-- On a pair of K-flat complexes the isomorphism is the composite of the comparisons. -/
theorem representedAffineDerivedTensorBifunctorIso_hom_app_app
    (P L : (CochainComplex.DerivedTensor.kFlatModuleComplexes
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).FullSubcategory) :
    ((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
        (DerivedCategory.Q.obj P.obj)).app
        (DerivedCategory.Q.obj L.obj) =
      ((representedAffineDerivedTensorRestrictIso B S hS U).hom.app P).app L := by
  let := representedAffineKFlatLifting B S hS U (representedAffineDerivedTensorSource B S hS U)
  let := representedAffineKFlatLifting B S hS U (representedAffineDerivedTensorTarget B S hS U)
  refine (Localization.lift₂NatTrans_app_app
    (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (CochainComplex.DerivedTensor.kFlatModuleComplexQuasiIso
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorSource B S hS U))
    (representedAffineKFlatRestrict B S hS U (representedAffineDerivedTensorTarget B S hS U))
    (representedAffineDerivedTensorSource B S hS U) (representedAffineDerivedTensorTarget B S hS U)
    (representedAffineDerivedTensorRestrictIso B S hS U).hom P L).trans ?_
  exact (Category.id_comp _).trans (Category.comp_id _)

end ToposSpelling

end Tensor

end AlgebraicGeometry.Space

end
