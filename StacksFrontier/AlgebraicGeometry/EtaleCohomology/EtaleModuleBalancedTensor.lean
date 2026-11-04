module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber
public import StacksFrontier.Homology.Perfect.BalancedTensorFree
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Tensoring étale sheaves of modules with a bounded complex of finite free right modules

Let `X` be a scheme and `Λ` a ring, not necessarily commutative. For a right `Λ`-module `N`
and a sheaf `F` of left `Λ`-modules on Mathlib's small étale site of `X`, the sheaf of abelian
groups `N ⊗_Λ F` is the sheafification of the presheaf `U ↦ N ⊗_Λ F(U)`, the balanced tensor
product `StacksDraft.Perfect.balancedTensorFunctor` taken sectionwise. This is a bifunctor,
additive in both variables, and for a complex `R` of right `Λ`-modules and a complex `F` of
sheaves of `Λ`-modules it has a total complex `Tot(R ⊗_Λ F)`, a complex of sheaves of
`ℤ`-modules.

This file records the four properties of that total complex which the trace formula uses, when
`R` is a strictly bounded complex of finite free right `Λ`-modules.

* **Stalks.** At every point of the site, in particular at every geometric point, the stalk of
  `Tot(R ⊗_Λ F)` is `Tot(R ⊗_Λ F_s)`, the total complex of the module-level balanced tensor
  product with the stalk complex. This holds for an arbitrary `R`.
* **Direct image.** For a morphism `π : X ⟶ Y`, `π_* Tot(R ⊗_Λ F) ≅ Tot(R ⊗_Λ π_* F)`. The
  point is that for a finite free `N` the presheaf `U ↦ N ⊗_Λ F(U)` is already a sheaf, being a
  finite power of the underlying abelian sheaf of `F`, so that sheafification does nothing and
  the construction commutes with precomposition of sections.
* **Acyclicity.** If every term of `I` is injective, every term of `Tot(R ⊗_Λ I)` is acyclic for
  `π_*`: it is a finite product of copies of the underlying abelian sheaves of injectives.
* **Quasi-isomorphisms.** A quasi-isomorphism `F ⟶ G` of arbitrary, unbounded, complexes
  induces a quasi-isomorphism `Tot(R ⊗_Λ F) ⟶ Tot(R ⊗_Λ G)`. This is checked on stalks, where it
  is `StacksDraft.Perfect.quasiIso_mapBifunctorMap_balancedTensorFunctor`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleBalancedTensor`: the bifunctor `(N, F) ↦ N ⊗_Λ F`.
* `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotal`: the total complex `Tot(R ⊗_Λ F)`, and
  `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotalMap` its functoriality in `F`.
* `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotalStalkIso`: its stalks.
* `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotalDirectImageIso`: its direct images.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotalStalkIso_hom_naturality`: the stalk
  isomorphism is natural in `F`.
* `Stacks.EtaleCohomology.rightAcyclic_etaleModuleBalancedTensorTotal_X`: the terms of
  `Tot(R ⊗_Λ I)` are acyclic for direct image when `I` is a complex of injectives.
* `Stacks.EtaleCohomology.quasiIso_etaleModuleBalancedTensorTotalMap`: `Tot(R ⊗_Λ -)` preserves
  quasi-isomorphisms.
* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleSheafFiber_map`,
  `Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleSheafFiber` and
  `Stacks.EtaleCohomology.quasiIso_of_forall_quasiIso_etaleModuleSheafFiber`: isomorphisms, zero
  objects and quasi-isomorphisms of sheaves of modules on Mathlib's small étale site are detected
  at the geometric points.
* `Stacks.EtaleCohomology.etaleModuleSheafFiberHomologyIso`: the stalk of a homology sheaf is the
  homology of the stalk complex.
* `Stacks.EtaleCohomology.isZero_homology_etaleModuleBalancedTensorTotal_iff`: a homology sheaf
  of `Tot(R ⊗_Λ F)` vanishes exactly when the corresponding homology of `Tot(R ⊗_Λ F_s)` vanishes
  at every geometric point `s`.

## Implementation notes

The stalk comparison is `CategoryTheory.Functor.mapBifunctorTotalIso`, the stalk functor
preserving all coproducts. Direct image does not preserve infinite coproducts, so the direct
image comparison is `HomologicalComplex₂.TotalMap.totalIsoOfFinite`: on each antidiagonal only
the finitely many terms indexed by the degrees of `R` are nonzero, and finite coproducts are
preserved by every additive functor. The comparison of the bicomplexes is the sheafification of the
unit of sheafification, which is invertible on the terms because the presheaf `U ↦ R^q ⊗_Λ F^p(U)`
is a sheaf.

The geometric points of `X` are points of the site relative to the universe `u`, whereas the
coefficients live in `ModuleCat.{u + 1}`; the conservativity statements go through the
universe lifts of the points (`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale_ulift`),
whose fibre functors are those of the points
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftNatIso`).

The stalk statements are made for the fibre functor `(Scheme.pointSmallEtale s.hom).sheafFiber`
of a geometric point `s`, which is what `Stacks.EtaleCohomology.etaleModuleStalk` unfolds to for
an object of a big étale site; `etaleModuleBalancedTensorTotalEtaleModuleStalkIso` restates the
stalk isomorphism in that form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StacksDraft.Perfect

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local instance] balancedTensorFunctor_additive balancedTensorFunctor_isLeftAdjoint
  HasDerivedCategory.standard moduleCat_hasLimitsOfSize etaleModules_ab5OfSize

/-! ### The tensor bifunctor on sheaves -/

section Bifunctor

variable (Λ : Type) [Ring Λ] (X : Scheme.{u})

/-- **Tensoring a sheaf of left `Λ`-modules with a right `Λ`-module**: `(N, F) ↦ N ⊗_Λ F`, the
sheafification of the presheaf of abelian groups `U ↦ N ⊗_Λ F(U)`. -/
def etaleModuleBalancedTensor :
    ModuleCat.{u + 1} (MulOpposite Λ) ⥤ EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} ℤ X :=
  balancedTensorFunctor Λ ⋙ Functor.whiskeringRight X.Etaleᵒᵖ _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) ⋙
    (Functor.whiskeringRight _ _ _).obj (presheafToSheaf _ _)

/-- Tensoring with a fixed right module is `Sheaf.composeAndSheafify` of the module-level
balanced tensor product. -/
theorem etaleModuleBalancedTensor_obj (N : ModuleCat.{u + 1} (MulOpposite Λ)) :
    (etaleModuleBalancedTensor Λ X).obj N =
      Sheaf.composeAndSheafify X.smallEtaleTopology ((balancedTensorFunctor Λ).obj N) :=
  rfl

/-- The value `N ⊗_Λ F` is the sheafification of the presheaf `U ↦ N ⊗_Λ F(U)`. -/
theorem etaleModuleBalancedTensor_obj_obj (N : ModuleCat.{u + 1} (MulOpposite Λ))
    (F : EtaleModules.{u, 0} Λ X) :
    ((etaleModuleBalancedTensor Λ X).obj N).obj F =
      (presheafToSheaf _ _).obj (F.obj ⋙ (balancedTensorFunctor Λ).obj N) :=
  rfl

/-- Tensoring with a fixed right module is additive. -/
instance etaleModuleBalancedTensor_obj_additive (N : ModuleCat.{u + 1} (MulOpposite Λ)) :
    ((etaleModuleBalancedTensor Λ X).obj N).Additive := by
  dsimp [etaleModuleBalancedTensor]
  infer_instance

/-- The tensor bifunctor is additive in the right module. -/
instance etaleModuleBalancedTensor_additive : (etaleModuleBalancedTensor Λ X).Additive := by
  dsimp [etaleModuleBalancedTensor]
  infer_instance

end Bifunctor

/-! ### Tensoring with a finite free module does not need sheafification -/

section Fan

variable {Λ : Type} [Ring Λ] {C : Type*} [Category* C]

/-- The projection `(ι → M) ⟶ M` onto the `i`-th coordinate, as a natural transformation from
`StacksDraft.Perfect.balancedTensorFreeModel` to the underlying abelian group. -/
def balancedTensorFreeModelProj (ι : Type v) (i : ι) :
    balancedTensorFreeModel Λ ι ⟶ ModuleCat.restrictScalars.{v} (Int.castRingHom Λ) where
  app M := ModuleCat.ofHom (X := (balancedTensorFreeModel Λ ι).obj M)
    (Y := (ModuleCat.restrictScalars.{v} (Int.castRingHom Λ)).obj M)
    (intLinearMapOfAddHom (Pi.evalAddMonoidHom (fun _ : ι => (M : Type v)) i))

/-- For a presheaf `P` of `Λ`-modules, the presheaf `U ↦ (ι → P(U))` with its coordinate
projections, as a fan over `ι` copies of the underlying presheaf of abelian groups of `P`. -/
def presheafBalancedTensorFreeFan (ι : Type v) (P : Cᵒᵖ ⥤ ModuleCat.{v} Λ) :
    Fan (fun _ : ι => P ⋙ ModuleCat.restrictScalars.{v} (Int.castRingHom Λ)) :=
  Fan.mk (P ⋙ balancedTensorFreeModel Λ ι)
    (fun i => Functor.whiskerLeft P (balancedTensorFreeModelProj ι i))

/-- The map into `U ↦ (ι → P(U))` induced by a fan over `ι` copies of the underlying presheaf of
abelian groups of `P`. -/
def presheafBalancedTensorFreeFanLift (ι : Type v) (P : Cᵒᵖ ⥤ ModuleCat.{v} Λ)
    (t : Fan (fun _ : ι => P ⋙ ModuleCat.restrictScalars.{v} (Int.castRingHom Λ))) :
    t.pt ⟶ P ⋙ balancedTensorFreeModel Λ ι where
  app U := ModuleCat.ofHom (X := t.pt.obj U) (Y := (balancedTensorFreeModel Λ ι).obj (P.obj U))
    (intLinearMapOfAddHom (AddMonoidHom.mk' (fun x i => (t.proj i).app U x)
      (fun x y => funext fun _ => map_add _ x y)))
  naturality U V f := by
    ext x
    funext i
    exact ConcreteCategory.congr_hom ((t.proj i).naturality f) x

/-- The presheaf `U ↦ (ι → P(U))` is the product of `ι` copies of the underlying presheaf of
abelian groups of `P`. -/
def isLimitPresheafBalancedTensorFreeFan (ι : Type v) (P : Cᵒᵖ ⥤ ModuleCat.{v} Λ) :
    IsLimit (presheafBalancedTensorFreeFan ι P) :=
  Fan.IsLimit.mk _ (presheafBalancedTensorFreeFanLift ι P)
    (fun t i => by ext U x; rfl)
    (fun t m hm => by
      ext U x
      funext i
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm i) U) x)

end Fan

section Free

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}

/-- For a sheaf `G` of `Λ`-modules, the presheaf `U ↦ (ι → G(U))` is a sheaf, being a product of
copies of the underlying sheaf of abelian groups of `G`. -/
theorem isSheaf_comp_balancedTensorFreeModel (ι : Type (u + 1)) (G : EtaleModules.{u, 0} Λ X) :
    Presheaf.IsSheaf X.smallEtaleTopology (G.obj ⋙ balancedTensorFreeModel Λ ι) :=
  ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf X.smallEtaleTopology)
    (isLimitPresheafBalancedTensorFreeFan ι G.obj)
    (fun _ => ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj G).property)

/-- **For a finite free right module `N`, the presheaf `U ↦ N ⊗_Λ G(U)` is already a sheaf**: it
is isomorphic to `U ↦ (ι → G(U))` for a basis of `N` indexed by `ι`. -/
theorem isSheaf_comp_balancedTensorFunctor_obj (N : ModuleCat.{u + 1} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N]
    (G : EtaleModules.{u, 0} Λ X) :
    Presheaf.IsSheaf X.smallEtaleTopology (G.obj ⋙ (balancedTensorFunctor Λ).obj N) :=
  (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft G.obj
    (balancedTensorFreeIso (Module.Free.chooseBasis (MulOpposite Λ) N)))).2
    (isSheaf_comp_balancedTensorFreeModel _ G)

/-- The sheaf `U ↦ (ι → G(U))` with its coordinate projections, as a fan over `ι` copies of the
underlying sheaf of abelian groups of `G`. -/
def etaleModuleBalancedTensorFreeFan (ι : Type (u + 1)) (G : EtaleModules.{u, 0} Λ X) :
    Fan (fun _ : ι => (etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj G) :=
  Fan.mk ⟨G.obj ⋙ balancedTensorFreeModel Λ ι, isSheaf_comp_balancedTensorFreeModel ι G⟩
    (fun i => ⟨Functor.whiskerLeft G.obj (balancedTensorFreeModelProj ι i)⟩)

/-- The sheaf `U ↦ (ι → G(U))` is the product of `ι` copies of the underlying sheaf of abelian
groups of `G`, limits of sheaves being computed on presheaves. -/
def isLimitEtaleModuleBalancedTensorFreeFan (ι : Type (u + 1)) (G : EtaleModules.{u, 0} Λ X) :
    IsLimit (etaleModuleBalancedTensorFreeFan ι G) :=
  isLimitOfIsLimitFanMkObj (sheafToPresheaf _ _) _ _
    (isLimitPresheafBalancedTensorFreeFan ι G.obj)

/-- For a finite free right module `N` with a basis indexed by `ι`, the sheaf `N ⊗_Λ G` is the
sheaf `U ↦ (ι → G(U))`, a finite power of the underlying sheaf of abelian groups of `G`. -/
def etaleModuleBalancedTensorFreeSheafIso (N : ModuleCat.{u + 1} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N]
    (G : EtaleModules.{u, 0} Λ X) :
    ((etaleModuleBalancedTensor Λ X).obj N).obj G ≅
      (etaleModuleBalancedTensorFreeFan (Module.Free.ChooseBasisIndex (MulOpposite Λ) N) G).pt :=
  (sheafificationIso ⟨_, isSheaf_comp_balancedTensorFunctor_obj N G⟩).symm ≪≫
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (Functor.isoWhiskerLeft G.obj
      (balancedTensorFreeIso (Module.Free.chooseBasis (MulOpposite Λ) N)))

end Free

/-! ### The comparison with direct image -/

section DirectImage

variable {Λ : Type} [Ring Λ] {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- For a presheaf `P` of abelian groups on `X`, the restriction of the unit `P ⟶ a(P)` of
sheafification along the base change functor of `π`: a map from the presheaf of sections of `P`
over `X ×_Y -` to the direct image of `a(P)`. -/
def etaleModulePresheafDirectImageUnit :
    (Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} ℤ)).obj (smallEtaleBaseChange π).op ⟶
      presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} ℤ) ⋙
        etaleModuleDirectImage.{u, 0} ℤ π ⋙ sheafToPresheaf Y.smallEtaleTopology _ where
  app P := Functor.whiskerLeft (smallEtaleBaseChange π).op (toSheafify X.smallEtaleTopology P)
  naturality P P' f := by
    apply NatTrans.ext
    funext V
    exact NatTrans.congr_app (toSheafify_naturality X.smallEtaleTopology f) _

/-- The comparison `a_Y(P(X ×_Y -)) ⟶ π_* a_X(P)` between sheafifying after and before
restricting sections along the base change functor of `π`, adjoint to
`Stacks.EtaleCohomology.etaleModulePresheafDirectImageUnit`. -/
def etaleModuleSheafifyDirectImageComparison :
    (Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} ℤ)).obj (smallEtaleBaseChange π).op ⋙
        presheafToSheaf Y.smallEtaleTopology _ ⟶
      presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} ℤ) ⋙
        etaleModuleDirectImage.{u, 0} ℤ π :=
  Functor.whiskerRight (etaleModulePresheafDirectImageUnit π) (presheafToSheaf _ _) ≫
    Functor.whiskerLeft (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} ℤ) ⋙
      etaleModuleDirectImage.{u, 0} ℤ π) (sheafificationAdjunction Y.smallEtaleTopology _).counit

/-- On a presheaf which is already a sheaf, sheafifying commutes with direct image. -/
theorem isIso_etaleModuleSheafifyDirectImageComparison_app
    (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (hP : Presheaf.IsSheaf X.smallEtaleTopology P) :
    IsIso ((etaleModuleSheafifyDirectImageComparison π).app P) := by
  have : IsIso (toSheafify X.smallEtaleTopology P) := isIso_toSheafify _ hP
  have : IsIso ((etaleModulePresheafDirectImageUnit π).app P) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft (smallEtaleBaseChange π).op
      (toSheafify X.smallEtaleTopology P))
  dsimp [etaleModuleSheafifyDirectImageComparison]
  infer_instance

variable {π}

/-- The comparison `N ⊗_Λ π_* G ⟶ π_*(N ⊗_Λ G)`. -/
def etaleModuleBalancedTensorDirectImageComparison (N : ModuleCat.{u + 1} (MulOpposite Λ))
    (G : EtaleModules.{u, 0} Λ X) :
    ((etaleModuleBalancedTensor Λ Y).obj N).obj ((etaleModuleDirectImage.{u, 0} Λ π).obj G) ⟶
      (etaleModuleDirectImage.{u, 0} ℤ π).obj (((etaleModuleBalancedTensor Λ X).obj N).obj G) :=
  (etaleModuleSheafifyDirectImageComparison π).app (G.obj ⋙ (balancedTensorFunctor Λ).obj N)

/-- The comparison `N ⊗_Λ π_* G ⟶ π_*(N ⊗_Λ G)` is natural in `N`. -/
theorem etaleModuleBalancedTensorDirectImageComparison_naturality_left
    {N N' : ModuleCat.{u + 1} (MulOpposite Λ)} (f : N ⟶ N') (G : EtaleModules.{u, 0} Λ X) :
    ((etaleModuleBalancedTensor Λ Y).map f).app ((etaleModuleDirectImage.{u, 0} Λ π).obj G) ≫
        etaleModuleBalancedTensorDirectImageComparison N' G =
      etaleModuleBalancedTensorDirectImageComparison N G ≫
        (etaleModuleDirectImage.{u, 0} ℤ π).map (((etaleModuleBalancedTensor Λ X).map f).app G) :=
  (etaleModuleSheafifyDirectImageComparison π).naturality
    (Functor.whiskerLeft G.obj ((balancedTensorFunctor Λ).map f))

/-- The comparison `N ⊗_Λ π_* G ⟶ π_*(N ⊗_Λ G)` is natural in `G`. -/
theorem etaleModuleBalancedTensorDirectImageComparison_naturality_right
    (N : ModuleCat.{u + 1} (MulOpposite Λ)) {G G' : EtaleModules.{u, 0} Λ X} (g : G ⟶ G') :
    ((etaleModuleBalancedTensor Λ Y).obj N).map ((etaleModuleDirectImage.{u, 0} Λ π).map g) ≫
        etaleModuleBalancedTensorDirectImageComparison N G' =
      etaleModuleBalancedTensorDirectImageComparison N G ≫
        (etaleModuleDirectImage.{u, 0} ℤ π).map (((etaleModuleBalancedTensor Λ X).obj N).map g) :=
  (etaleModuleSheafifyDirectImageComparison π).naturality
    (Functor.whiskerRight g.hom ((balancedTensorFunctor Λ).obj N))

/-- **Tensoring with a finite free right module commutes with direct image**: for such an `N`,
the comparison `N ⊗_Λ π_* G ⟶ π_*(N ⊗_Λ G)` is an isomorphism, because the presheaf
`U ↦ N ⊗_Λ G(U)` is already a sheaf. -/
instance isIso_etaleModuleBalancedTensorDirectImageComparison
    (N : ModuleCat.{u + 1} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N]
    (G : EtaleModules.{u, 0} Λ X) :
    IsIso (etaleModuleBalancedTensorDirectImageComparison (π := π) N G) :=
  isIso_etaleModuleSheafifyDirectImageComparison_app π _
    (isSheaf_comp_balancedTensorFunctor_obj N G)

end DirectImage

/-! ### The total complex -/

section Total

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}
  (R : CochainComplex (ModuleCat.{u + 1} (MulOpposite Λ)) ℤ)

/-- **The total complex `Tot(R ⊗_Λ F)`** of the double complex `(q, p) ↦ R^q ⊗_Λ F^p`, for a
complex `R` of right `Λ`-modules and a complex `F` of sheaves of left `Λ`-modules on the small
étale site of `X`; it is a complex of sheaves of abelian groups. -/
def etaleModuleBalancedTensorTotal (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :
    CochainComplex (EtaleModules.{u, 0} ℤ X) ℤ :=
  HomologicalComplex.mapBifunctor R F (etaleModuleBalancedTensor Λ X) (ComplexShape.up ℤ)

/-- The map `Tot(R ⊗_Λ F) ⟶ Tot(R ⊗_Λ G)` induced by a map of complexes `F ⟶ G`. -/
def etaleModuleBalancedTensorTotalMap {F G : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ}
    (φ : F ⟶ G) : etaleModuleBalancedTensorTotal R F ⟶ etaleModuleBalancedTensorTotal R G :=
  HomologicalComplex.mapBifunctorMap (𝟙 R) φ _ _

/-- `Tot(R ⊗_Λ -)` as a functor on complexes of sheaves of `Λ`-modules. -/
def etaleModuleBalancedTensorTotalFunctor :
    CochainComplex (EtaleModules.{u, 0} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} ℤ X) ℤ :=
  ((etaleModuleBalancedTensor Λ X).map₂HomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj R

/-- The functor `Tot(R ⊗_Λ -)` is `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotal` on
objects. -/
theorem etaleModuleBalancedTensorTotalFunctor_obj
    (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :
    (etaleModuleBalancedTensorTotalFunctor R).obj F = etaleModuleBalancedTensorTotal R F :=
  rfl

/-- The functor `Tot(R ⊗_Λ -)` is `Stacks.EtaleCohomology.etaleModuleBalancedTensorTotalMap` on
morphisms. -/
theorem etaleModuleBalancedTensorTotalFunctor_map
    {F G : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ} (φ : F ⟶ G) :
    (etaleModuleBalancedTensorTotalFunctor R).map φ = etaleModuleBalancedTensorTotalMap R φ :=
  rfl

/-- Tensoring with a zero module gives zero. -/
theorem isZero_etaleModuleBalancedTensor_obj_obj {N : ModuleCat.{u + 1} (MulOpposite Λ)}
    (hN : IsZero N) (G : EtaleModules.{u, 0} Λ X) :
    IsZero (((etaleModuleBalancedTensor Λ X).obj N).obj G) :=
  ((etaleModuleBalancedTensor Λ X).map_isZero hN).obj G

/-- For `R` strictly concentrated in degrees `[a, b]`, tensoring with a nonzero `R^q` forces
`q ∈ [a, b]`. -/
private theorem mem_Icc_of_not_isZero_etaleModuleBalancedTensor_obj_obj (a b : ℤ)
    [R.IsStrictlyGE a] [R.IsStrictlyLE b] {q : ℤ} {G : EtaleModules.{u, 0} Λ X}
    (h : ¬ IsZero (((etaleModuleBalancedTensor Λ X).obj (R.X q)).obj G)) : q ∈ Set.Icc a b := by
  by_contra hq
  refine h (isZero_etaleModuleBalancedTensor_obj_obj ?_ G)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hq
  exact hq.elim (fun h => R.isZero_of_isStrictlyGE a q h)
    (fun h => R.isZero_of_isStrictlyLE b q h)

/-- For `R` strictly bounded, each antidiagonal of the double complex `(q, p) ↦ R^q ⊗_Λ F^p`
has only finitely many nonzero terms. -/
theorem finite_nonzero_etaleModuleBalancedTensorBicomplex (a b : ℤ) [R.IsStrictlyGE a]
    [R.IsStrictlyLE b] (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (n : ℤ) :
    Finite {j // ¬ IsZero (((((etaleModuleBalancedTensor Λ X).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj R).obj F).toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n j)} := by
  refine Finite.of_injective (β := Set.Icc a b) (fun j => ⟨j.1.1.1, ?_⟩) ?_
  · exact mem_Icc_of_not_isZero_etaleModuleBalancedTensor_obj_obj R a b j.2
  · rintro ⟨⟨⟨q, p⟩, hqp⟩, hj⟩ ⟨⟨⟨q', p'⟩, hqp'⟩, hj'⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at h hqp hqp' ⊢
    have h1 : q + p = n := hqp
    have h2 : q' + p' = n := hqp'
    ext <;> simp <;> omega

/-! #### Direct image -/

section DirectImage

variable {Y : Scheme.{u}} (π : X ⟶ Y) (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)

/-- For `R` strictly bounded, the double complex `(q, p) ↦ R^q ⊗_Λ F^p` has only finitely many
nonzero terms in each total degree. -/
theorem finite_support_etaleModuleBalancedTensorBicomplex (a b : ℤ) [R.IsStrictlyGE a]
    [R.IsStrictlyLE b] (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq =
        n ∧ ¬ IsZero ((((((etaleModuleBalancedTensor Λ X).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj R).obj F).X pq.1).X pq.2)}.Finite := by
  refine ((Set.finite_Icc a b).image (fun q => (q, n - q))).subset ?_
  rintro ⟨q, p⟩ ⟨hqp, hnz⟩
  refine ⟨q, mem_Icc_of_not_isZero_etaleModuleBalancedTensor_obj_obj R a b hnz, ?_⟩
  have h1 : q + p = n := hqp
  simp only [Prod.mk.injEq, true_and]
  omega

/-- The comparison of the double complexes `(q, p) ↦ R^q ⊗_Λ π_* F^p` and
`(q, p) ↦ π_*(R^q ⊗_Λ F^p)`, an isomorphism when the terms of `R` are finite free. -/
def etaleModuleBalancedTensorDirectImageBicomplexIso
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)] :
    ((((etaleModuleBalancedTensor Λ Y).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj R).obj
        (((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex _).obj F)) ≅
      HomologicalComplex₂.mapBicomplex (etaleModuleDirectImage.{u, 0} ℤ π)
        ((((etaleModuleBalancedTensor Λ X).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj R).obj F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => HomologicalComplex.Hom.isoOfComponents
      (fun p => @asIso _ _ _ _
        (etaleModuleBalancedTensorDirectImageComparison (π := π) (R.X q) (F.X p))
        (isIso_etaleModuleBalancedTensorDirectImageComparison (R.X q) (F.X p)))
      (fun p p' _ => (etaleModuleBalancedTensorDirectImageComparison_naturality_right (π := π)
        (R.X q) (F.d p p')).symm))
    (fun q q' _ => HomologicalComplex.hom_ext _ _ (fun p =>
      (etaleModuleBalancedTensorDirectImageComparison_naturality_left (π := π)
        (R.d q q') (F.X p)).symm))

/-- **Direct image commutes with tensoring with a bounded complex of finite free modules**:
`π_* Tot(R ⊗_Λ F) ≅ Tot(R ⊗_Λ π_* F)` for `R` strictly bounded with finite free terms and `F`
an arbitrary complex. -/
def etaleModuleBalancedTensorTotalDirectImageIso (a b : ℤ) [R.IsStrictlyGE a] [R.IsStrictlyLE b]
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)] :
    ((etaleModuleDirectImage.{u, 0} ℤ π).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (etaleModuleBalancedTensorTotal R F) ≅
      etaleModuleBalancedTensorTotal R
        (((etaleModuleDirectImage.{u, 0} Λ π).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) :=
  (HomologicalComplex₂.TotalMap.totalIsoOfFinite (etaleModuleDirectImage.{u, 0} ℤ π) _
      (finite_support_etaleModuleBalancedTensorBicomplex R F a b)).symm ≪≫
    HomologicalComplex₂.total.mapIso (etaleModuleBalancedTensorDirectImageBicomplexIso R π F).symm
      (ComplexShape.up ℤ)

end DirectImage

/-! #### Acyclicity for direct image -/

section Acyclic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A coproduct with finitely many nonzero terms of right acyclic objects is right acyclic**,
for an additive left exact functor out of an abelian category with enough injectives: it is a
finite product of those terms. -/
theorem rightAcyclic_of_isColimit_cofan_of_finite_nonzero {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (Φ : C ⥤ D) [Φ.Additive] [EnoughInjectives C] [PreservesFiniteLimits Φ] {J : Type}
    {M : J → C} [Finite {j // ¬ IsZero (M j)}] {c : Cofan M} (hc : IsColimit c)
    (hM : ∀ j, Φ.rightAcyclic (M j)) : Φ.rightAcyclic c.pt := by
  let S : Set J := {j | ¬ IsZero (M j)}
  have : Finite S := ‹Finite {j // ¬ IsZero (M j)}›
  let g := fun j : S => M j.1
  have := Abelian.hasFiniteBiproducts (C := C)
  have hc' := StacksDraft.TotalComplexQuasiIso.isColimitRestrictCofan c hc S
    (fun j h => by_contra fun h' => h h')
  let e : c.pt ≅ ∏ᶜ g :=
    hc'.coconePointUniqueUpToIso (biproduct.isColimit g) ≪≫ biproduct.isoProduct g
  exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso Φ e.symm
    (Stacks.RightAcyclicProduct.rightAcyclic_pi Φ g (fun j => hM j.1))

variable {Y : Scheme.{u}} (π : X ⟶ Y)

/-- For a finite free right module `N` and an injective sheaf `I` of `Λ`-modules, `N ⊗_Λ I` is
acyclic for direct image: it is a finite power of the underlying sheaf of abelian groups of `I`,
which is acyclic everywhere. -/
theorem rightAcyclic_etaleModuleBalancedTensor_obj_obj (N : ModuleCat.{u + 1} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N]
    (I : EtaleModules.{u, 0} Λ X) [Injective I] :
    (etaleModuleDirectImage.{u, 0} ℤ π).rightAcyclic
      (((etaleModuleBalancedTensor Λ X).obj N).obj I) := by
  have : (etaleModuleDirectImage.{u, 0} ℤ π).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, 0} ℤ π).isRightAdjoint
  refine Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
    (etaleModuleBalancedTensorFreeSheafIso N I).symm ?_
  exact Stacks.RightAcyclicProduct.rightAcyclic_of_isLimit_fan _
    (isLimitEtaleModuleBalancedTensorFreeFan _ I)
    (fun _ => rightAcyclic_directImage_of_isAcyclicEverywhere π _
      (isAcyclicEverywhere_restrictScalars' (Int.castRingHom Λ) I))

/-- **The terms of `Tot(R ⊗_Λ I)` are acyclic for direct image** when `R` is a strictly bounded
complex of finite free right `Λ`-modules and every term of `I` is injective. -/
theorem rightAcyclic_etaleModuleBalancedTensorTotal_X (a b : ℤ) [R.IsStrictlyGE a]
    [R.IsStrictlyLE b]
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)]
    (I : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) [∀ p, Injective (I.X p)] (n : ℤ) :
    (etaleModuleDirectImage.{u, 0} ℤ π).rightAcyclic
      ((etaleModuleBalancedTensorTotal R I).X n) := by
  have : (etaleModuleDirectImage.{u, 0} ℤ π).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, 0} ℤ π).isRightAdjoint
  have := finite_nonzero_etaleModuleBalancedTensorBicomplex R a b I n
  exact rightAcyclic_of_isColimit_cofan_of_finite_nonzero _
    (GradedObject.isColimitCofanMapObj _ _ n)
    (fun j => rightAcyclic_etaleModuleBalancedTensor_obj_obj π (R.X j.1.1) (I.X j.1.2))

end Acyclic

/-! #### Stalks -/

section Stalk

variable (Φ : GrothendieckTopology.Point.{u} X.smallEtaleTopology)

/-- The fibre functor of a point of the small étale site is additive on sheaves of modules,
being left exact. -/
instance etaleModuleSheafFiber_additive (Λ' : Type) [Ring Λ'] :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The comparison `Φ.presheafFiberCompIso` between taking fibres before and after applying a
functor preserving filtered colimits is natural in that functor. -/
theorem etaleSheafFiber_presheafFiberCompIso_hom_naturality {A B : Type*} [Category* A]
    [Category* B] [HasColimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} B] {T T' : A ⥤ B}
    [PreservesFilteredColimitsOfSize.{u, u} T] [PreservesFilteredColimitsOfSize.{u, u} T']
    (α : T ⟶ T') (P : X.Etaleᵒᵖ ⥤ A) :
    Φ.presheafFiber.map (Functor.whiskerLeft P α) ≫ (Φ.presheafFiberCompIso T').hom.app P =
      (Φ.presheafFiberCompIso T).hom.app P ≫ α.app (Φ.presheafFiber.obj P) := by
  apply Φ.presheafFiber_hom_ext
  intro V x
  rw [Φ.toPresheafFiber_naturality_assoc, Φ.toPresheafFiber_presheafFiberCompIso_hom_app,
    Φ.toPresheafFiber_presheafFiberCompIso_hom_app_assoc]
  exact (α.naturality _).symm

/-- Pasting two commutative squares side by side. -/
private theorem comp_comp_eq_of_comp_eq_of_comp_eq {C : Type*} [Category* C]
    {S T U V W Z : C} {a : S ⟶ T} {b : T ⟶ U} {c : S ⟶ V} {d : V ⟶ U} {e : U ⟶ Z} {f : V ⟶ W}
    {g : W ⟶ Z} (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = f ≫ g) : a ≫ b ≫ e = (c ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **The stalk of `N ⊗_Λ G` is `N ⊗_Λ G_Φ`**: stalks are insensitive to sheafification, and
the balanced tensor product with `N` commutes with the filtered colimit computing the stalk. -/
def etaleModuleBalancedTensorStalkIso (N : ModuleCat.{u + 1} (MulOpposite Λ))
    (G : EtaleModules.{u, 0} Λ X) :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).obj (((etaleModuleBalancedTensor Λ X).obj N).obj G) ≅
      ((balancedTensorFunctor Λ).obj N).obj ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :=
  (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} ℤ)).app
      (G.obj ⋙ (balancedTensorFunctor Λ).obj N) ≪≫
    (Φ.presheafFiberCompIso ((balancedTensorFunctor Λ).obj N)).app G.obj

/-- The stalk comparison for `N ⊗_Λ G` is natural in `N`. -/
theorem etaleModuleBalancedTensorStalkIso_naturality_left
    {N N' : ModuleCat.{u + 1} (MulOpposite Λ)} (f : N ⟶ N') (G : EtaleModules.{u, 0} Λ X) :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).map (((etaleModuleBalancedTensor Λ X).map f).app G) ≫
        (etaleModuleBalancedTensorStalkIso Φ N' G).hom =
      (etaleModuleBalancedTensorStalkIso Φ N G).hom ≫
        ((balancedTensorFunctor Λ).map f).app
          ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) := by
  have h₁ := (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} ℤ)).hom.naturality
    (Functor.whiskerLeft G.obj ((balancedTensorFunctor Λ).map f))
  have h₂ := etaleSheafFiber_presheafFiberCompIso_hom_naturality Φ
    ((balancedTensorFunctor Λ).map f) G.obj
  dsimp only [etaleModuleBalancedTensorStalkIso, Iso.trans_hom, Iso.app_hom]
  exact comp_comp_eq_of_comp_eq_of_comp_eq h₁ h₂

/-- The stalk comparison for `N ⊗_Λ G` is natural in `G`. -/
theorem etaleModuleBalancedTensorStalkIso_naturality_right
    (N : ModuleCat.{u + 1} (MulOpposite Λ)) {G G' : EtaleModules.{u, 0} Λ X} (g : G ⟶ G') :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).map (((etaleModuleBalancedTensor Λ X).obj N).map g) ≫
        (etaleModuleBalancedTensorStalkIso Φ N G').hom =
      (etaleModuleBalancedTensorStalkIso Φ N G).hom ≫
        ((balancedTensorFunctor Λ).obj N).map
          ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).map g) := by
  have h₁ := (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} ℤ)).hom.naturality
    (Functor.whiskerRight g.hom ((balancedTensorFunctor Λ).obj N))
  have h₂ := (Φ.presheafFiberCompIso ((balancedTensorFunctor Λ).obj N)).hom.naturality g.hom
  dsimp only [etaleModuleBalancedTensorStalkIso, Iso.trans_hom, Iso.app_hom]
  exact comp_comp_eq_of_comp_eq_of_comp_eq h₁ h₂

/-- **The stalk of `Tot(R ⊗_Λ F)` is `Tot(R ⊗_Λ F_Φ)`**, the total complex of the module-level
balanced tensor product of `R` with the stalk complex of `F`, at every point `Φ` of the small
étale site, in particular at every geometric point. -/
def etaleModuleBalancedTensorTotalStalkIso (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :
    ((Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (etaleModuleBalancedTensorTotal R F) ≅
      HomologicalComplex.mapBifunctor R
        (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
        (balancedTensorFunctor Λ) (ComplexShape.up ℤ) :=
  Functor.mapBifunctorTotalIso (etaleModuleBalancedTensor Λ X) (balancedTensorFunctor Λ) (𝟭 _)
    (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)) (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ))
    (etaleModuleBalancedTensorStalkIso Φ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)
    (fun f G => etaleModuleBalancedTensorStalkIso_naturality_left Φ f G)
    (fun N _ _ g => etaleModuleBalancedTensorStalkIso_naturality_right Φ N g) R F

/-- The stalk isomorphism of `Tot(R ⊗_Λ F)` is natural in `F`. -/
theorem etaleModuleBalancedTensorTotalStalkIso_hom_naturality
    {F G : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ} (φ : F ⟶ G) :
    ((Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (etaleModuleBalancedTensorTotalMap R φ) ≫
        (etaleModuleBalancedTensorTotalStalkIso R Φ G).hom =
      (etaleModuleBalancedTensorTotalStalkIso R Φ F).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 R)
          (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)
          (balancedTensorFunctor Λ) (ComplexShape.up ℤ) := by
  have := Functor.mapBifunctorTotalIso_hom_naturality (etaleModuleBalancedTensor Λ X)
    (balancedTensorFunctor Λ) (𝟭 _)
    (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)) (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ))
    (etaleModuleBalancedTensorStalkIso Φ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (c := ComplexShape.up ℤ)
    (fun f G => etaleModuleBalancedTensorStalkIso_naturality_left Φ f G)
    (fun N _ _ g => etaleModuleBalancedTensorStalkIso_naturality_right Φ N g) R R F G (𝟙 R) φ
  rwa [CategoryTheory.Functor.map_id] at this

/-- The stalk isomorphism of `Tot(R ⊗_Λ F)` at a geometric point `s` of an object `X` of a big
étale site, stated with the étale stalk functors `Stacks.EtaleCohomology.etaleModuleStalk`. -/
def etaleModuleBalancedTensorTotalEtaleModuleStalkIso (B : BigEtaleSite.{u}) (X' : B.Scheme)
    (s : GeometricPoint X'.obj) (F : CochainComplex (EtaleModules.{u, 0} Λ X'.obj) ℤ) :
    ((etaleModuleStalk.{u, 0} B X' ℤ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (etaleModuleBalancedTensorTotal R F) ≅
      HomologicalComplex.mapBifunctor R
        (((etaleModuleStalk.{u, 0} B X' Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
        (balancedTensorFunctor Λ) (ComplexShape.up ℤ) :=
  etaleModuleBalancedTensorTotalStalkIso R (Scheme.pointSmallEtale s.hom) F

end Stalk

end Total

/-! ### Detecting isomorphisms, zero objects and quasi-isomorphisms at geometric points -/

section Conservative

variable {Λ' : Type} [Ring Λ'] {X : Scheme.{u}}

/-- **A morphism of sheaves of modules on Mathlib's small étale site is an isomorphism as soon as
it is one on the stalks at all geometric points.** -/
theorem isIso_of_forall_isIso_etaleModuleSheafFiber_map {F G : EtaleModules.{u, 0} Λ' X}
    (f : F ⟶ G)
    (h : ∀ s : GeometricPoint X,
      IsIso ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ') |>.map f)) :
    IsIso f := by
  let _ : PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ'
  let _ : PreservesFilteredColimits (forget (ModuleCat.{u + 1} Λ')) :=
    comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat)
      (forget AddCommGrpCat)
  have _ : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ') :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have hcov : ⋃ x : X, Set.range (GeometricPoint.ofPoint X x).hom = Set.univ :=
    Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.2 ⟨x, default, GeometricPoint.ofPoint_liesOver X x⟩
  have hP := Scheme.isConservative_pointSmallEtale_ulift.{0, u}
    (fun x : X => (GeometricPoint.ofPoint X x).hom) hcov
  have happ : ∀ q : (ObjectProperty.ofObj (fun x : X =>
      (Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).ulift.{u + 1})).FullSubcategory,
      IsIso (q.obj.sheafFiber.map f) := by
    rintro ⟨_, ⟨x⟩⟩
    exact (NatIso.isIso_map_iff (GrothendieckTopology.Point.sheafFiberUliftNatIso _ _) f).2 (h _)
  exact (hP.jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ')).isIso f

/-- **A sheaf of modules on Mathlib's small étale site whose stalks at all geometric points
vanish is zero.** -/
theorem isZero_of_forall_isZero_etaleModuleSheafFiber (F : EtaleModules.{u, 0} Λ' X)
    (h : ∀ s : GeometricPoint X,
      IsZero ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ') |>.obj F)) :
    IsZero F := by
  have hiso : IsIso (0 : F ⟶ F) :=
    isIso_of_forall_isIso_etaleModuleSheafFiber_map 0 (fun s => by
      rw [Functor.map_zero, (h s).eq_of_src 0 (𝟙 _)]
      infer_instance)
  rw [IsZero.iff_id_eq_zero]
  simpa using (IsIso.inv_hom_id (0 : F ⟶ F)).symm

/-- **The stalk of a homology sheaf is the homology of the stalk complex**, the fibre functor of
a point of the small étale site being exact. -/
def etaleModuleSheafFiberHomologyIso (Φ : GrothendieckTopology.Point.{u} X.smallEtaleTopology)
    (K : CochainComplex (EtaleModules.{u, 0} Λ' X) ℤ) (n : ℤ) :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).obj (K.homology n) ≅
      (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K).homology n :=
  ((K.sc n).mapHomologyIso (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ'))).symm

/-- **A morphism of complexes of sheaves of modules on Mathlib's small étale site is a
quasi-isomorphism as soon as it is one on the stalks at all geometric points.** -/
theorem quasiIso_of_forall_quasiIso_etaleModuleSheafFiber
    {K L : CochainComplex (EtaleModules.{u, 0} Λ' X) ℤ} (φ : K ⟶ L)
    (h : ∀ s : GeometricPoint X, QuasiIso
      (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ')).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_of_forall_isIso_etaleModuleSheafFiber_map _ (fun s => ?_)
  let Φ := Scheme.pointSmallEtale s.hom
  have h₁ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map φ)
    (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ'))
  have h₂ : IsIso (HomologicalComplex.homologyMap
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).mapHomologicalComplex (ComplexShape.up ℤ)
        |>.map φ) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((h s).quasiIsoAt n)
  let e : Arrow.mk (HomologicalComplex.homologyMap
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).mapHomologicalComplex (ComplexShape.up ℤ)
        |>.map φ) n) ≅
      Arrow.mk ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')).map
        (HomologicalComplex.homologyMap φ n)) :=
    Arrow.isoMk ((K.sc n).mapHomologyIso (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ')))
      ((L.sc n).mapHomologyIso (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ'))) h₁.symm
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h₂

end Conservative

/-! ### Quasi-isomorphism invariance and homology -/

section QuasiIso

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}
  (R : CochainComplex (ModuleCat.{u + 1} (MulOpposite Λ)) ℤ)

/-- **`Tot(R ⊗_Λ -)` preserves quasi-isomorphisms** when `R` is a strictly bounded complex of
finite free right `Λ`-modules: a quasi-isomorphism `F ⟶ G` of arbitrary, unbounded, complexes of
sheaves of `Λ`-modules induces a quasi-isomorphism `Tot(R ⊗_Λ F) ⟶ Tot(R ⊗_Λ G)`. It is checked
at the geometric points, where it is the module-level statement
`StacksDraft.Perfect.quasiIso_mapBifunctorMap_balancedTensorFunctor`. -/
theorem quasiIso_etaleModuleBalancedTensorTotalMap (a b : ℤ) [R.IsStrictlyGE a]
    [R.IsStrictlyLE b]
    [∀ q, Module.Free (MulOpposite Λ) (R.X q)] [∀ q, Module.Finite (MulOpposite Λ) (R.X q)]
    {F G : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ} (f : F ⟶ G) [QuasiIso f] :
    QuasiIso (etaleModuleBalancedTensorTotalMap R f) := by
  refine quasiIso_of_forall_quasiIso_etaleModuleSheafFiber _ (fun s => ?_)
  let Φ := Scheme.pointSmallEtale s.hom
  let e : Arrow.mk (((Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (etaleModuleBalancedTensorTotalMap R f)) ≅
      Arrow.mk (HomologicalComplex.mapBifunctorMap (𝟙 R)
        (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)
        (balancedTensorFunctor Λ) (ComplexShape.up ℤ)) :=
    Arrow.isoMk (etaleModuleBalancedTensorTotalStalkIso R Φ F)
      (etaleModuleBalancedTensorTotalStalkIso R Φ G)
      (etaleModuleBalancedTensorTotalStalkIso_hom_naturality R Φ f).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2
    (quasiIso_mapBifunctorMap_balancedTensorFunctor Λ R a b _)

/-- The stalk of the `n`-th homology sheaf of `Tot(R ⊗_Λ F)` is the `n`-th homology of
`Tot(R ⊗_Λ F_Φ)`. -/
def etaleModuleBalancedTensorTotalStalkHomologyIso
    (Φ : GrothendieckTopology.Point.{u} X.smallEtaleTopology)
    (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (n : ℤ) :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} ℤ)).obj
        ((etaleModuleBalancedTensorTotal R F).homology n) ≅
      (HomologicalComplex.mapBifunctor R
        (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
        (balancedTensorFunctor Λ) (ComplexShape.up ℤ)).homology n :=
  etaleModuleSheafFiberHomologyIso Φ _ n ≪≫
    HomologicalComplex.homologyMapIso (etaleModuleBalancedTensorTotalStalkIso R Φ F) n

/-- **A homology sheaf of `Tot(R ⊗_Λ F)` vanishes exactly when the corresponding homology of
`Tot(R ⊗_Λ F_s)` vanishes at every geometric point `s`.** -/
theorem isZero_homology_etaleModuleBalancedTensorTotal_iff
    (F : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (n : ℤ) :
    IsZero ((etaleModuleBalancedTensorTotal R F).homology n) ↔
      ∀ s : GeometricPoint X, IsZero ((HomologicalComplex.mapBifunctor R
        ((((Scheme.pointSmallEtale s.hom).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            (balancedTensorFunctor Λ) (ComplexShape.up ℤ)).homology n) :=
  ⟨fun h s => ((Scheme.pointSmallEtale s.hom).sheafFiber.map_isZero h).of_iso
      (etaleModuleBalancedTensorTotalStalkHomologyIso R _ F n).symm,
    fun h => isZero_of_forall_isZero_etaleModuleSheafFiber _ fun s =>
      (h s).of_iso (etaleModuleBalancedTensorTotalStalkHomologyIso R _ F n)⟩

end QuasiIso

end Stacks.EtaleCohomology

end
