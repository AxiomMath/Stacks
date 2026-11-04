module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsCentral
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DevissageNatTrans

/-!
# Stacks 07A4 on affine representables, against the associated module

Let `g : U' ⟶ U` be a morphism of objects of the big fppf site with affine underlying schemes, with
map of rings of global functions `A ⟶ A'`. The isomorphism of Stacks 07A4 for `g`, the affine
base change isomorphism `Lg^* Φ_A ≅ Φ_{A'}(- ⊗ᴸ_A A')` and the isomorphisms
`Φ(-) ⊗ᴸ Φ(-) ≅ Φ(- ⊗ᴸ -)` are compatible with the base change isomorphism of Stacks 068I, up to a
unit of `A'`.

## Main results

* `ModuleCat.ExtendScalars.exists_bifunctor_app_eq_smul`: a natural endomorphism of
  `(M, N) ↦ (A' ⊗_A M) ⊗_{A'} (A' ⊗_A N)` is multiplication by an element of `A'`.
* `AlgebraicGeometry.Space.exists_representedAffinePullbackTensorHom_eq`: the two module-level
  isomorphisms `g^*((M ⊗ N)^~) ≅ ((A' ⊗_A M) ⊗_{A'} (A' ⊗_A N))^~` differ by multiplication by
  an element of `A'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace ModuleCat.ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- `(B ⊗_A M) ⊗_B (B ⊗_A N)`, as a bifunctor in the `A`-modules `M` and `N`. -/
abbrev tensorBifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} A ⥤ ModuleCat.{u} B :=
  ModuleCat.extendScalars.{u, u, u} f ⋙ curriedTensor (ModuleCat.{u} B) ⋙
    (Functor.whiskeringLeft _ _ _).obj (ModuleCat.extendScalars.{u, u, u} f)

/-- `(B ⊗_A A) ⊗_B (B ⊗_A N) ≅ B ⊗_A N`, naturally in `N`. -/
def tensorBifunctorUnitIso (N : ModuleCat.{u} A) :
    ((tensorBifunctor f).obj (ModuleCat.of A A)).obj N ≅ (ModuleCat.extendScalars f).obj N :=
  Functor.Monoidal.μIso (ModuleCat.extendScalars.{u, u, u} f) (ModuleCat.of A A) N ≪≫
    (ModuleCat.extendScalars.{u, u, u} f).mapIso (λ_ N)

/-- `tensorBifunctorUnitIso` is natural in `N`. -/
theorem tensorBifunctorUnitIso_naturality {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    ((tensorBifunctor f).obj (ModuleCat.of A A)).map g ≫ (tensorBifunctorUnitIso f N').hom =
      (tensorBifunctorUnitIso f N).hom ≫ (ModuleCat.extendScalars f).map g := by
  simp only [tensorBifunctorUnitIso, Iso.trans_hom, Functor.Monoidal.μIso_hom,
    Functor.mapIso_hom]
  change ((ModuleCat.extendScalars f).obj (ModuleCat.of A A) ◁
      (ModuleCat.extendScalars f).map g) ≫ _ ≫ _ = _
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_right, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (_ ≫ ·) (congrArg (ModuleCat.extendScalars f).map
    (MonoidalCategory.leftUnitor_naturality g))

/-- For fixed `N`, the functor `M ↦ (B ⊗_A M) ⊗_B (B ⊗_A N)` preserves colimits. -/
instance preservesColimitsOfSize_tensorBifunctor_flip_obj (N : ModuleCat.{u} A) :
    PreservesColimitsOfSize.{u, u} ((tensorBifunctor f).flip.obj N) := by
  have : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u}
      (tensorRight ((ModuleCat.extendScalars.{u, u, u} f).obj N) : ModuleCat.{u} B ⥤ _) :=
    preservesColimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight ((ModuleCat.extendScalars.{u, u, u} f).obj N))
  exact preservesColimits_of_natIso (F := ModuleCat.extendScalars.{u, u, u} f ⋙
      tensorRight ((ModuleCat.extendScalars.{u, u, u} f).obj N))
    (G := (tensorBifunctor f).flip.obj N) (NatIso.ofComponents (fun _ => Iso.refl _)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))

/-- A natural endomorphism of `(M, N) ↦ (B ⊗_A M) ⊗_B (B ⊗_A N)` is multiplication by an
element of `B`. -/
theorem exists_bifunctor_app_eq_smul (δ : tensorBifunctor f ⟶ tensorBifunctor f) :
    ∃ c : B, ∀ M N, (δ.app M).app N = c • 𝟙 _ := by
  let e := NatIso.ofComponents (tensorBifunctorUnitIso f) (tensorBifunctorUnitIso_naturality f)
  let ζ : ModuleCat.extendScalars.{u, u, u} f ⟶ ModuleCat.extendScalars.{u, u, u} f :=
    e.inv ≫ δ.app (ModuleCat.of A A) ≫ e.hom
  obtain ⟨c, hc⟩ := natTrans_app_eq_smul (P := (⊤ : ObjectProperty (ModuleCat.{u} A)))
    trivial (Functor.whiskerLeft (⊤ : ObjectProperty _).ι ζ)
  have hA : ∀ N, (δ.app (ModuleCat.of A A)).app N = c • 𝟙 _ := fun N => by
    have h := hc ⟨N, trivial⟩
    change (tensorBifunctorUnitIso f N).inv ≫ (δ.app (ModuleCat.of A A)).app N ≫
      (tensorBifunctorUnitIso f N).hom = _ at h
    rwa [Iso.inv_comp_eq, ← Iso.eq_comp_inv, Linear.comp_smul, Category.comp_id,
      Linear.smul_comp, Iso.hom_inv_id] at h
  refine ⟨c, fun M N => ?_⟩
  let δN : (tensorBifunctor f).flip.obj N ⟶ (tensorBifunctor f).flip.obj N :=
    { app := fun M => (δ.app M).app N
      naturality := fun M M' φ => NatTrans.congr_app (δ.naturality φ) N }
  have h : δN = c • 𝟙 _ := Stacks.EilenbergWatts.natTrans_ext_of_app_unit
    ((hA N).trans (NatTrans.app_smul _ c (𝟙 _)).symm)
  exact (NatTrans.congr_app h M).trans (NatTrans.app_smul M c (𝟙 _))

end ModuleCat.ExtendScalars

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/-- Pasting five commutative squares. -/
theorem paste_five_squares {C : Type*} [Category C] {x₀ x₁ x₂ x₃ x₄ x₅ y₀ y₁ y₂ y₃ y₄ y₅ : C}
    (a₀ : x₀ ⟶ y₀) (a₁ : x₁ ⟶ y₁) (a₂ : x₂ ⟶ y₂) (a₃ : x₃ ⟶ y₃) (a₄ : x₄ ⟶ y₄) (a₅ : x₅ ⟶ y₅)
    (p₁ : x₀ ⟶ x₁) (p₂ : x₁ ⟶ x₂) (p₃ : x₂ ⟶ x₃) (p₄ : x₃ ⟶ x₄) (p₅ : x₄ ⟶ x₅)
    (q₁ : y₀ ⟶ y₁) (q₂ : y₁ ⟶ y₂) (q₃ : y₂ ⟶ y₃) (q₄ : y₃ ⟶ y₄) (q₅ : y₄ ⟶ y₅)
    (s₁ : a₀ ≫ q₁ = p₁ ≫ a₁) (s₂ : a₁ ≫ q₂ = p₂ ≫ a₂) (s₃ : a₂ ≫ q₃ = p₃ ≫ a₃)
    (s₄ : a₃ ≫ q₄ = p₄ ≫ a₄) (s₅ : a₄ ≫ q₅ = p₅ ≫ a₅) :
    a₀ ≫ q₁ ≫ q₂ ≫ q₃ ≫ q₄ ≫ q₅ = (p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅) ≫ a₅ := by
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, reassoc_of% s₄, s₅]
  simp only [Category.assoc]

/-- Pasting four commutative squares. -/
theorem paste_four_squares {C : Type*} [Category C] {x₀ x₁ x₂ x₃ x₄ y₀ y₁ y₂ y₃ y₄ : C}
    (a₀ : x₀ ⟶ y₀) (a₁ : x₁ ⟶ y₁) (a₂ : x₂ ⟶ y₂) (a₃ : x₃ ⟶ y₃) (a₄ : x₄ ⟶ y₄)
    (p₁ : x₀ ⟶ x₁) (p₂ : x₁ ⟶ x₂) (p₃ : x₂ ⟶ x₃) (p₄ : x₃ ⟶ x₄)
    (q₁ : y₀ ⟶ y₁) (q₂ : y₁ ⟶ y₂) (q₃ : y₂ ⟶ y₃) (q₄ : y₃ ⟶ y₄)
    (s₁ : a₀ ≫ q₁ = p₁ ≫ a₁) (s₂ : a₁ ≫ q₂ = p₂ ≫ a₂) (s₃ : a₂ ≫ q₃ = p₃ ≫ a₃)
    (s₄ : a₃ ≫ q₄ = p₄ ≫ a₄) :
    a₀ ≫ q₁ ≫ q₂ ≫ q₃ ≫ q₄ = (p₁ ≫ p₂ ≫ p₃ ≫ p₄) ≫ a₄ := by
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, s₄]
  simp only [Category.assoc]

/-- Pasting two commutative squares. -/
theorem paste_two_squares {C : Type*} [Category C] {x₀ x₁ x₂ y₀ y₁ y₂ : C}
    (a₀ : x₀ ⟶ y₀) (a₁ : x₁ ⟶ y₁) (a₂ : x₂ ⟶ y₂) (p₁ : x₀ ⟶ x₁) (p₂ : x₁ ⟶ x₂)
    (q₁ : y₀ ⟶ y₁) (q₂ : y₁ ⟶ y₂) (s₁ : a₀ ≫ q₁ = p₁ ≫ a₁) (s₂ : a₁ ≫ q₂ = p₂ ≫ a₂) :
    a₀ ≫ q₁ ≫ q₂ = (p₁ ≫ p₂) ≫ a₂ := by
  rw [reassoc_of% s₁, s₂, Category.assoc]

/-- A commutative square with invertible horizontal sides gives one with their inverses. -/
theorem square_inv {C : Type*} [Category C] {a b a' b' : C} (e : a ≅ b) (e' : a' ≅ b')
    (x : a ⟶ a') (y : b ⟶ b') (h : x ≫ e'.hom = e.hom ≫ y) : y ≫ e'.inv = e.inv ≫ x := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Conjugating by isomorphisms preserves a pair of naturality squares. -/
theorem inv_comp_naturality {C : Type*} [Category C] {x y x' y' : C} (a : x ⟶ x') (b : y ⟶ y')
    (E : x ⟶ y) (E' : x' ⟶ y') [IsIso E] [IsIso E'] (T : x ⟶ y) (T' : x' ⟶ y')
    (hE : a ≫ E' = E ≫ b) (hT : a ≫ T' = T ≫ b) : b ≫ inv E' ≫ T' = (inv E ≫ T) ≫ b := by
  rw [Category.assoc, IsIso.eq_inv_comp, ← reassoc_of% hE, IsIso.hom_inv_id_assoc, hT]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ToposTensor

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- `(M ⊗_A N)^~ ≅ M^~ ⊗ N^~`, in the ringed-topos spelling. -/
def representedAffineToposTensorIso
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineToposAssociated B S hS U).obj (M ⊗ N) ≅
      ((representedAffineToposTensor B S hS U).obj
        ((representedAffineToposAssociated B S hS U).obj M)).obj
        ((representedAffineToposAssociated B S hS U).obj N) :=
  (representedAffineAssociatedTensorIso B S hS U N).app M

/-- `representedAffineToposTensorIso` is natural in the second module. -/
theorem representedAffineToposTensorIso_hom_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineToposAssociated B S hS U).map (M ◁ g) ≫
        (representedAffineToposTensorIso B S hS U M N').hom =
      (representedAffineToposTensorIso B S hS U M N).hom ≫
        ((representedAffineToposTensor B S hS U).obj
          ((representedAffineToposAssociated B S hS U).obj M)).map
          ((representedAffineToposAssociated B S hS U).map g) :=
  representedAffineAssociatedTensorIso_hom_naturality_right B S hS U M g

/-- `representedAffineToposTensorIso` is natural in the first module. -/
theorem representedAffineToposTensorIso_hom_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineToposAssociated B S hS U).map (f ▷ N) ≫
        (representedAffineToposTensorIso B S hS U M' N).hom =
      (representedAffineToposTensorIso B S hS U M N).hom ≫
        ((representedAffineToposTensor B S hS U).map
          ((representedAffineToposAssociated B S hS U).map f)).app
          ((representedAffineToposAssociated B S hS U).obj N) :=
  (representedAffineAssociatedTensorIso B S hS U N).hom.naturality f

end ToposTensor

section ModuleLevel

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)

/-- Pullback of modules along the morphism of small étale ringed topoi of `g`. -/
abbrev representedAffineModulePullback :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS _)
    (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom

/-- The isomorphism `g^*(N^~) ≅ (A' ⊗_A N)^~` is natural in `N`. -/
theorem representedAffineToposPullbackIso_hom_naturality
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (g : N ⟶ N') :
    (representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map g) ≫
        (representedAffineToposPullbackIso B S hS g₀).hom.app N' =
      (representedAffineToposPullbackIso B S hS g₀).hom.app N ≫
        (representedAffineToposAssociated B S hS U').map
          ((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).map g) :=
  (representedAffineToposPullbackIso B S hS g₀).hom.naturality g

/-- Stacks 03EL for `g` at associated modules, in the curried spelling. -/
def representedAffinePullbackTensorStep
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).obj
      (((representedAffineToposTensor B S hS U).obj
      ((representedAffineToposAssociated B S hS U).obj M)).obj
      ((representedAffineToposAssociated B S hS U).obj N)) ⟶
      ((representedAffineToposTensor B S hS U').obj
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj M))).obj
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj N)) :=
  (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom).hom.app
        ((representedAffineToposAssociated B S hS U).obj M,
        (representedAffineToposAssociated B S hS U).obj N)

/-- `g^*M^~ ⊗ g^*N^~ ⟶ (A' ⊗ M)^~ ⊗ (A' ⊗ N)^~`. -/
def representedAffinePullbackTensorFactors
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineToposTensor B S hS U').obj
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj M))).obj
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj N)) ⟶
      ((representedAffineToposTensor B S hS U').obj
        ((representedAffineToposAssociated B S hS U').obj
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj
        M))).obj ((representedAffineToposAssociated B S hS U').obj
        ((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).obj N)) :=
  ((representedAffineToposTensor B S hS U').map
      ((representedAffineToposPullbackIso B S hS g₀).hom.app M)).app
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj N)) ≫
      ((representedAffineToposTensor B S hS U').obj
      ((representedAffineToposAssociated B S hS U').obj
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj
      M))).map ((representedAffineToposPullbackIso B S hS g₀).hom.app N)

/-- `g^*((M ⊗ N)^~) ≅ g^*(M^~ ⊗ N^~) ≅ g^*M^~ ⊗ g^*N^~ ≅ (A' ⊗ M)^~ ⊗ (A' ⊗ N)^~
≅ ((A' ⊗ M) ⊗ (A' ⊗ N))^~`, through the tensor product of the pullbacks (Stacks 03EL). -/
def representedAffinePullbackTensorHom
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj (M ⊗ N)) ⟶
      (representedAffineToposAssociated B S hS U').obj
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ⊗
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N) :=
  (representedAffineModulePullback B S hS g₀).map
      (representedAffineToposTensorIso B S hS U M N).hom ≫
    representedAffinePullbackTensorStep B S hS g₀ M N ≫
    representedAffinePullbackTensorFactors B S hS g₀ M N ≫
    (representedAffineToposTensorIso B S hS U'
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M)
      ((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).obj N)).inv

/-- `g^*((M ⊗ N)^~) ≅ (A' ⊗ (M ⊗ N))^~ ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))^~`, through the extension of
scalars of the tensor product (Stacks 068I). -/
def representedAffinePullbackExtensionHom
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).obj
        ((representedAffineToposAssociated B S hS U).obj (M ⊗ N)) ⟶
      (representedAffineToposAssociated B S hS U').obj
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ⊗
          (ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).obj N) :=
  (representedAffineToposPullbackIso B S hS g₀).hom.app (M ⊗ N) ≫
    (representedAffineToposAssociated B S hS U').map
      (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom) M N)

/-- `representedAffinePullbackExtensionHom` is an isomorphism. -/
instance isIso_representedAffinePullbackExtensionHom
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    IsIso (representedAffinePullbackExtensionHom B S hS g₀ M N) := by
  unfold representedAffinePullbackExtensionHom
  infer_instance

/-- `representedAffinePullbackExtensionHom` is natural in the second module. -/
theorem representedAffinePullbackExtensionHom_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map (M ◁ g)) ≫
        representedAffinePullbackExtensionHom B S hS g₀ M N' =
      representedAffinePullbackExtensionHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map
          ((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).obj M ◁
            (ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g₀).hom).map g) :=
  paste_two_squares _ _ _ _ _ _ _
    (representedAffineToposPullbackIso_hom_naturality B S hS g₀ (M ◁ g)) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (Functor.OplaxMonoidal.δ_natural_right _ _ _).symm)

/-- `representedAffinePullbackExtensionHom` is natural in the first module. -/
theorem representedAffinePullbackExtensionHom_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map (f ▷ N)) ≫
        representedAffinePullbackExtensionHom B S hS g₀ M' N =
      representedAffinePullbackExtensionHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map
          ((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀).hom).map f ▷
            (ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g₀).hom).obj N) :=
  paste_two_squares _ _ _ _ _ _ _
    (representedAffineToposPullbackIso_hom_naturality B S hS g₀ (f ▷ N)) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (Functor.OplaxMonoidal.δ_natural_left _ _ _).symm)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- The isomorphism `g^*(M^~ ⊗ N^~) ≅ g^*M^~ ⊗ g^*N^~` is natural in `N`. -/
theorem representedAffinePullbackTensorIso_naturality_snd
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineModulePullback B S hS g₀).map
        (((representedAffineToposTensor B S hS U).obj
          ((representedAffineToposAssociated B S hS U).obj M)).map
          ((representedAffineToposAssociated B S hS U).map g)) ≫
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom).hom.app
        (((representedAffineToposAssociated B S hS U).obj M),
        (representedAffineToposAssociated B S hS U).obj N') =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom).hom.app
        (((representedAffineToposAssociated B S hS U).obj M),
        (representedAffineToposAssociated B S hS U).obj N) ≫
        ((representedAffineToposTensor B S hS U').obj
          ((representedAffineModulePullback B S hS g₀).obj
            ((representedAffineToposAssociated B S hS U).obj M))).map
          ((representedAffineModulePullback B S hS g₀).map
            ((representedAffineToposAssociated B S hS U).map g)) :=
  Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_snd
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀)).toModulesHom
    ((representedAffineToposAssociated B S hS U).obj M)
    ((representedAffineToposAssociated B S hS U).map g)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- The isomorphism `g^*(M^~ ⊗ N^~) ≅ g^*M^~ ⊗ g^*N^~` is natural in `M`. -/
theorem representedAffinePullbackTensorIso_naturality_fst
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).map
        (((representedAffineToposTensor B S hS U).map
          ((representedAffineToposAssociated B S hS U).map f)).app
            ((representedAffineToposAssociated B S hS U).obj N)) ≫
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom).hom.app
        ((representedAffineToposAssociated B S hS U).obj M',
        ((representedAffineToposAssociated B S hS U).obj N)) =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g₀)).toModulesHom).hom.app
        (((representedAffineToposAssociated B S hS U).obj M),
        ((representedAffineToposAssociated B S hS U).obj N)) ≫
        ((representedAffineToposTensor B S hS U').map
          ((representedAffineModulePullback B S hS g₀).map
          ((representedAffineToposAssociated B S hS U).map f))).app
          ((representedAffineModulePullback B S hS g₀).obj
          ((representedAffineToposAssociated B S hS U).obj N)) :=
  Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g₀)).toModulesHom
    ((representedAffineToposAssociated B S hS U).map f)
      ((representedAffineToposAssociated B S hS U).obj N)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- `representedAffinePullbackTensorStep` is natural in the second module. -/
theorem representedAffinePullbackTensorStep_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineModulePullback B S hS g₀).map
      (((representedAffineToposTensor B S hS U).obj
      ((representedAffineToposAssociated B S hS U).obj M)).map
      ((representedAffineToposAssociated B S hS U).map g)) ≫
      representedAffinePullbackTensorStep B S hS g₀ M N' =
      representedAffinePullbackTensorStep B S hS g₀ M N ≫
        ((representedAffineToposTensor B S hS U').obj
        ((representedAffineModulePullback B S hS g₀).obj
        ((representedAffineToposAssociated B S hS U).obj M))).map
        ((representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map g)) :=
  representedAffinePullbackTensorIso_naturality_snd B S hS g₀ M g

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- `representedAffinePullbackTensorStep` is natural in the first module. -/
theorem representedAffinePullbackTensorStep_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).map
      (((representedAffineToposTensor B S hS U).map
      ((representedAffineToposAssociated B S hS U).map f)).app
      ((representedAffineToposAssociated B S hS U).obj N)) ≫
      representedAffinePullbackTensorStep B S hS g₀ M' N =
      representedAffinePullbackTensorStep B S hS g₀ M N ≫
        ((representedAffineToposTensor B S hS U').map
        ((representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map f))).app
        ((representedAffineModulePullback B S hS g₀).obj
        ((representedAffineToposAssociated B S hS U).obj N)) :=
  representedAffinePullbackTensorIso_naturality_fst B S hS g₀ f N

/-- `representedAffinePullbackTensorFactors` is natural in the second module. -/
theorem representedAffinePullbackTensorFactors_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    ((representedAffineToposTensor B S hS U').obj
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj M))).map
      ((representedAffineModulePullback B S hS g₀).map
      ((representedAffineToposAssociated B S hS U).map g)) ≫
      representedAffinePullbackTensorFactors B S hS g₀ M N' =
      representedAffinePullbackTensorFactors B S hS g₀ M N ≫
        ((representedAffineToposTensor B S hS U').obj
        ((representedAffineToposAssociated B S hS U').obj
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj
        M))).map ((representedAffineToposAssociated B S hS U').map
        ((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).map g)) := by
  unfold representedAffinePullbackTensorFactors
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, Category.assoc]
  simp only [Functor.comp_obj]
  rw [← Functor.map_comp, ← Functor.map_comp, representedAffineToposPullbackIso_hom_naturality]

/-- `representedAffinePullbackTensorFactors` is natural in the first module. -/
theorem representedAffinePullbackTensorFactors_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineToposTensor B S hS U').map
      ((representedAffineModulePullback B S hS g₀).map
      ((representedAffineToposAssociated B S hS U).map f))).app
      ((representedAffineModulePullback B S hS g₀).obj
      ((representedAffineToposAssociated B S hS U).obj N)) ≫
      representedAffinePullbackTensorFactors B S hS g₀ M' N =
      representedAffinePullbackTensorFactors B S hS g₀ M N ≫
        ((representedAffineToposTensor B S hS U').map
        ((representedAffineToposAssociated B S hS U').map
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map
        f))).app ((representedAffineToposAssociated B S hS U').obj
        ((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).obj N)) := by
  unfold representedAffinePullbackTensorFactors
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
    representedAffineToposPullbackIso_hom_naturality, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Category.assoc, NatTrans.naturality]

/-- `representedAffinePullbackTensorHom` is natural in the second module. -/
theorem representedAffinePullbackTensorHom_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    (representedAffineModulePullback B S hS g₀).map
      ((representedAffineToposAssociated B S hS U).map (M ◁ g)) ≫
      representedAffinePullbackTensorHom B S hS g₀ M N' =
      representedAffinePullbackTensorHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ◁
        (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).map g) := by
  unfold representedAffinePullbackTensorHom
  exact paste_four_squares _ _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      representedAffineToposTensorIso_hom_naturality_right])
    (representedAffinePullbackTensorStep_naturality_right B S hS g₀ M g)
    (representedAffinePullbackTensorFactors_naturality_right B S hS g₀ M g)
    (square_inv _ _ _ _ (representedAffineToposTensorIso_hom_naturality_right B S hS U'
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M)
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map g)))

/-- `representedAffinePullbackTensorHom` is natural in the first module. -/
theorem representedAffinePullbackTensorHom_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineModulePullback B S hS g₀).map
      ((representedAffineToposAssociated B S hS U).map (f ▷ N)) ≫
      representedAffinePullbackTensorHom B S hS g₀ M' N =
      representedAffinePullbackTensorHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map f ▷
        (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).obj N) := by
  unfold representedAffinePullbackTensorHom
  exact paste_four_squares _ _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      representedAffineToposTensorIso_hom_naturality_left])
    (representedAffinePullbackTensorStep_naturality_left B S hS g₀ f N)
    (representedAffinePullbackTensorFactors_naturality_left B S hS g₀ f N)
    (square_inv _ _ _ _ (representedAffineToposTensorIso_hom_naturality_left B S hS U'
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map f)
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N)))

/-- The ratio of the two comparisons, as an endomorphism of `(A' ⊗ M) ⊗ (A' ⊗ N)`. -/
def representedAffinePullbackTensorRatio
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ⊗
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N ⟶
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ⊗
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N :=
  (representedAffineToposAssociatedFullyFaithful B S hS U').preimage
    (inv (representedAffinePullbackExtensionHom B S hS g₀ M N) ≫
      representedAffinePullbackTensorHom B S hS g₀ M N)

/-- The associated module of `representedAffinePullbackTensorRatio` is the composite of the
inverse of `representedAffinePullbackExtensionHom` with `representedAffinePullbackTensorHom`. -/
theorem map_representedAffinePullbackTensorRatio
    (M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineToposAssociated B S hS U').map
        (representedAffinePullbackTensorRatio B S hS g₀ M N) =
      inv (representedAffinePullbackExtensionHom B S hS g₀ M N) ≫
        representedAffinePullbackTensorHom B S hS g₀ M N :=
  (representedAffineToposAssociatedFullyFaithful B S hS U').map_preimage _

/-- A pair of compatible morphisms commuting with the two comparisons also commutes with their
ratio. -/
private theorem representedAffinePullbackTensorRatio_comp_eq
    {M N M' N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (h : M ⊗ N ⟶ M' ⊗ N')
    (a : (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ⊗
        (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N ⟶
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M' ⊗
        (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N')
    (hE : (representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map h) ≫
        representedAffinePullbackExtensionHom B S hS g₀ M' N' =
      representedAffinePullbackExtensionHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map a)
    (hT : (representedAffineModulePullback B S hS g₀).map
        ((representedAffineToposAssociated B S hS U).map h) ≫
        representedAffinePullbackTensorHom B S hS g₀ M' N' =
      representedAffinePullbackTensorHom B S hS g₀ M N ≫
        (representedAffineToposAssociated B S hS U').map a) :
    a ≫ representedAffinePullbackTensorRatio B S hS g₀ M' N' =
      representedAffinePullbackTensorRatio B S hS g₀ M N ≫ a :=
  (representedAffineToposAssociatedFullyFaithful B S hS U').map_injective (by
    rw [Functor.map_comp, Functor.map_comp, map_representedAffinePullbackTensorRatio,
      map_representedAffinePullbackTensorRatio]
    exact inv_comp_naturality _ _ _ _ _ _ hE hT)

/-- `representedAffinePullbackTensorRatio` is natural in the second module. -/
theorem representedAffinePullbackTensorRatio_naturality_right
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    {N N' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (g : N ⟶ N') :
    ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ◁
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map g) ≫
      representedAffinePullbackTensorRatio B S hS g₀ M N' =
      representedAffinePullbackTensorRatio B S hS g₀ M N ≫
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj M ◁
        (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).map g) :=
  representedAffinePullbackTensorRatio_comp_eq B S hS g₀ _ _
    (representedAffinePullbackExtensionHom_naturality_right B S hS g₀ M g)
    (representedAffinePullbackTensorHom_naturality_right B S hS g₀ M g)

/-- `representedAffinePullbackTensorRatio` is natural in the first module. -/
theorem representedAffinePullbackTensorRatio_naturality_left
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (f : M ⟶ M') (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map f ▷
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).obj N) ≫
      representedAffinePullbackTensorRatio B S hS g₀ M' N =
      representedAffinePullbackTensorRatio B S hS g₀ M N ≫
        ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map f ▷
        (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).obj N) :=
  representedAffinePullbackTensorRatio_comp_eq B S hS g₀ _ _
    (representedAffinePullbackExtensionHom_naturality_left B S hS g₀ f N)
    (representedAffinePullbackTensorHom_naturality_left B S hS g₀ f N)

/-- The ratio, as a natural endomorphism of `(M, N) ↦ (A' ⊗ M) ⊗ (A' ⊗ N)`. -/
def representedAffinePullbackTensorRatioNatTrans :
    ModuleCat.ExtendScalars.tensorBifunctor (representedAffineCommRingCatHom B S hS g₀).hom ⟶
      ModuleCat.ExtendScalars.tensorBifunctor (representedAffineCommRingCatHom B S hS g₀).hom where
  app M :=
    { app := fun N => representedAffinePullbackTensorRatio B S hS g₀ M N
      naturality := fun _ _ g =>
        representedAffinePullbackTensorRatio_naturality_right B S hS g₀ M g }
  naturality _ _ f := NatTrans.ext (funext fun N =>
    representedAffinePullbackTensorRatio_naturality_left B S hS g₀ f N)

/-- The two comparisons `g^*((M ⊗ N)^~) ≅ ((A' ⊗ M) ⊗ (A' ⊗ N))^~` differ by multiplication by
an element of `A'`, independent of `M` and `N`. -/
theorem exists_representedAffinePullbackTensorHom_eq :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤),
      ∀ M N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
      representedAffinePullbackTensorHom B S hS g₀ M N =
        representedAffinePullbackExtensionHom B S hS g₀ M N ≫
          (representedAffineToposAssociated B S hS U').map (c • 𝟙 _) := by
  obtain ⟨c, hc⟩ := ModuleCat.ExtendScalars.exists_bifunctor_app_eq_smul _
    (representedAffinePullbackTensorRatioNatTrans B S hS g₀)
  refine ⟨c, fun M N => ?_⟩
  have h := map_representedAffinePullbackTensorRatio B S hS g₀ M N
  rw [show representedAffinePullbackTensorRatio B S hS g₀ M N = c • 𝟙 _ from hc M N] at h
  rw [h, IsIso.hom_inv_id_assoc]

end ModuleLevel

end AlgebraicGeometry.Space

end
