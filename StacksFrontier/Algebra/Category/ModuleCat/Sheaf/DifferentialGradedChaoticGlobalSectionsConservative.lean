module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticGlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDistinguished
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck

/-!
# Derived global sections on a chaotic site detect isomorphisms through their kernel

Let `C` be a small category with the chaotic topology, `R` a commutative ring and `ℬ` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. This file reduces
the statement that the derived global sections functor `RΓ : D(ℬ, d) ⥤ D(R)` reflects
isomorphisms between objects of `QC(ℬ, d)` to the statement that it has no nonzero object of
`QC(ℬ, d)` in its kernel.

The reduction runs through the cone of a homomorphism of graded injective K-injective modules, so
two facts about cones are proved on the way: the cone of a homomorphism of graded injective
K-injective modules is again graded injective and K-injective, and the global sections of a cone
are the mapping cone of the global sections.

## Main definitions

* `SheafOfModules.GradedModule.shiftEquivalence`: the degree shift of right graded modules, as an
  equivalence of categories.
* `SheafOfModules.DifferentialGradedModule.forgetShiftIso`: the underlying graded module of the
  chosen shift of a right differential graded module is the degree shift by one of its underlying
  graded module.
* `Stacks.ChaoticSite.dgGlobalSectionsConeIso`: the global sections of the cone of `f` are the
  mapping cone of the global sections of `f`.

## Main results

* `SheafOfModules.GradedModule.injective_shift`: a degree shift of an injective right graded
  module is injective.
* `SheafOfModules.DifferentialGradedModule.gradedInjective_cone` and
  `SheafOfModules.DifferentialGradedModule.isKInjective_cone`: the cone of a homomorphism of graded
  injective (resp. K-injective) right differential graded modules is graded injective
  (resp. K-injective); `isDGInjective_cone` combines the two.
* `SheafOfModules.DifferentialGradedModule.isIso_toDerivedCategory_map_iff_isZero_cone`: a
  homomorphism becomes an isomorphism of `D(A, d)` exactly when its cone becomes zero there.
* `Stacks.ChaoticSite.acyclic_dgGlobalSections_cone_iff`: the global sections of the cone of `f`
  are acyclic exactly when the global sections of `f` are a quasi-isomorphism.
* `Stacks.ChaoticSite.derivedGlobalSections_map_of_isDGInjective` and
  `Stacks.ChaoticSite.isIso_derivedGlobalSections_map_iff`: on a homomorphism `f` of graded
  injective K-injective modules, `RΓ` is the class of `Γ(f)`, so it is an isomorphism exactly when
  `Γ(f)` is a quasi-isomorphism.
* `Stacks.ChaoticSite.isZero_derivedGlobalSections_cone`: for such an `f` with `Γ(f)` a
  quasi-isomorphism, `RΓ` of the cone of `f` vanishes.
* `Stacks.ChaoticSite.qc_cone`: the cone of a homomorphism between modules in `QC(ℬ, d)` is in
  `QC(ℬ, d)`.
* `Stacks.ChaoticSite.isIso_of_isIso_derivedGlobalSections_map_of_kernel`: **if no nonzero object
  of `QC(ℬ, d)` has zero derived global sections, then a morphism of `QC(ℬ, d)` whose derived
  global sections are an isomorphism is an isomorphism.**

## Implementation notes

The underlying graded module of a cone splits as the target plus the shifted source
(`SheafOfModules.DifferentialGradedModule.ConePackage.gradedSplitting`), and an object of a
preadditive category that is split in this way between two injective objects is injective: an
extension is assembled from the extensions of its two coordinates. The shifted source is
injective because the degree shift is an equivalence of the category of right graded modules.

K-injectivity of the cone is the exactness of `Hom(N, -)` on the distinguished triangle
`L ⟶ C(f) ⟶ K[1]` of `K(Mod(A, d))`, for `N` acyclic.

## References

* [Stacks Project, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)
* [Stacks Project, Tag 0FSU](https://stacks.math.columbia.edu/tag/0FSU)
* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t a m v u w

namespace SheafOfModules

/-! ### The degree shift of right graded modules is an equivalence -/

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (B : GradedAlgebra.{t, a} R)

/-- The degree shift by `k`, as an endofunctor of the category of right graded modules. -/
def degreeShiftFunctor (k : ℤ) : GradedModule.{t, a, m} B ⥤ GradedModule.{t, a, m} B where
  obj M := M.shift k
  map φ := shiftHom φ k
  map_id M := shiftHom_id M k
  map_comp φ ψ := shiftHom_comp φ ψ k

variable {B}

/-- Two opposite degree shifts of a right graded module cancel. -/
def shiftShiftIso (M : GradedModule.{t, a, m} B) (k l : ℤ) (h : k + l = 0) :
    (M.shift k).shift l ≅ M where
  hom :=
    { app n := degCastHom M.piece (show n + l + k = n by omega)
      map_smul n i U x y := by
        simp only [degCastHom_val_app, shift_smul, castHom_shift_piece, Cofree.smul_castHom_left,
          Cofree.castHom_castHom] }
  inv :=
    { app n := degCastHom M.piece (show n = n + l + k by omega)
      map_smul n i U x y := by
        simp only [degCastHom_val_app, shift_smul, castHom_shift_piece, Cofree.smul_castHom_left,
          Cofree.castHom_castHom] }
  hom_inv_id := Hom.ext fun n =>
    (degCastHom_comp_degCastHom M.piece _ _).trans (degCastHom_eq_id M.piece _)
  inv_hom_id := Hom.ext fun n =>
    (degCastHom_comp_degCastHom M.piece _ _).trans (degCastHom_eq_id M.piece _)

variable (B) in
/-- Composing two opposite degree shifts is the identity functor. -/
def degreeShiftFunctorCompIso (k l : ℤ) (h : k + l = 0) :
    degreeShiftFunctor.{t, a, m} B k ⋙ degreeShiftFunctor B l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => shiftShiftIso M k l h) fun {M N} φ => Hom.ext fun n =>
    (degCastHom_comp_app φ (show n + l + k = n by omega)).symm

variable (B) in
/-- **The degree shift by `k` is an equivalence of the category of right graded modules**, with
inverse the degree shift by `-k`. -/
def shiftEquivalence (k : ℤ) : GradedModule.{t, a, m} B ≌ GradedModule.{t, a, m} B :=
  CategoryTheory.Equivalence.mk (degreeShiftFunctor B k) (degreeShiftFunctor B (-k))
    (degreeShiftFunctorCompIso B k (-k) (by omega)).symm
    (degreeShiftFunctorCompIso B (-k) k (by omega))

/-- **A degree shift of an injective right graded module is injective.** -/
theorem injective_shift (M : GradedModule.{t, a, m} B) [Injective M] (k : ℤ) :
    Injective (M.shift k) :=
  ((shiftEquivalence B k).map_injective_iff M).2 inferInstance

end GradedModule

namespace DifferentialGradedModule

/-! ### Graded injectivity of cones -/

section GradedInjective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- The identification of the pieces of the chosen shift of `K` with the pieces of `K` one
degree up, as a homomorphism of right graded modules. -/
def forgetShiftHom (K : DifferentialGradedModule.{t, a, m} A) :
    (forgetToGradedModule A).obj (shift K) ⟶ ((forgetToGradedModule A).obj K).shift 1 where
  app n := ((shiftPackage K).xIso n).hom
  map_smul n i U x y := (shiftPackage K).xIso_mul n i U x y

/-- **The underlying graded module of the chosen shift of `K` is the degree shift by one of the
underlying graded module of `K`.** -/
def forgetShiftIso (K : DifferentialGradedModule.{t, a, m} A) :
    (forgetToGradedModule A).obj (shift K) ≅ ((forgetToGradedModule A).obj K).shift 1 :=
  haveI : IsIso (forgetShiftHom K) := GradedModule.isIso_of_componentwise _ fun n => by
    change IsIso ((shiftPackage K).xIso n).hom
    infer_instance
  asIso (forgetShiftHom K)

/-- The chosen shift of a graded injective right differential graded module is graded
injective. -/
theorem gradedInjective_shift {K : DifferentialGradedModule.{t, a, m} A} (hK : GradedInjective K) :
    GradedInjective (shift K) :=
  have : Injective ((forgetToGradedModule A).obj K) := hK
  Injective.of_iso (forgetShiftIso K).symm (GradedModule.injective_shift _ 1)

/-- The middle term of a graded-split sequence of right differential graded modules whose outer
terms have injective underlying graded modules has injective underlying graded module: an
extension is assembled from the extensions of its two coordinates. -/
theorem injective_of_gradedSplitting {K L M : DifferentialGradedModule.{t, a, m} A}
    {f : K ⟶ L} {g : L ⟶ M} (S : GradedSplitting f g)
    (hK : Injective (GradedModule.ofDifferentialGraded K))
    (hM : Injective (GradedModule.ofDifferentialGraded M)) :
    Injective (GradedModule.ofDifferentialGraded L) := by
  refine ⟨fun {P Q} h i _ => ?_⟩
  obtain ⟨a, ha⟩ := hK.factors (h ≫ S.r) i
  obtain ⟨b, hb⟩ := hM.factors (h ≫ GradedModule.ofDifferentialGradedMap g) i
  refine ⟨a ≫ GradedModule.ofDifferentialGradedMap f + b ≫ S.s, ?_⟩
  rw [Preadditive.comp_add, ← Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
    Category.assoc, ← Preadditive.comp_add, S.id, Category.comp_id]

/-- **The cone of a homomorphism of graded injective right differential graded modules is graded
injective**: after forgetting the differentials it is split between the target and the shifted
source. -/
theorem gradedInjective_cone {I I' : DifferentialGradedModule.{t, a, m} A} (f : I ⟶ I')
    (hI : GradedInjective I) (hI' : GradedInjective I') :
    GradedInjective (conePackage f).cone :=
  injective_of_gradedSplitting (conePackage f).gradedSplitting hI' (gradedInjective_shift hI)

end GradedInjective

/-! ### K-injectivity of cones -/

section KInjective

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **The cone of a homomorphism of K-injective right differential graded modules is
K-injective**: for `N` acyclic, `Hom(N, -)` is exact on the distinguished triangle
`L ⟶ C(f) ⟶ K[1]` of `K(Mod(A, d))`, whose outer terms receive no nonzero morphism from `N`. -/
theorem isKInjective_cone {I I' : DifferentialGradedModule.{u, v, w} A} (f : I ⟶ I')
    (hI : IsKInjective I) (hI' : IsKInjective I') : IsKInjective (conePackage f).cone := by
  intro N hN
  have key : ∀ g : (HomotopyCategory.quotient A).obj N ⟶
      (HomotopyCategory.quotient A).obj (conePackage f).cone, g = 0 := by
    intro g
    have h₂ : g ≫ (coneRotatedTriangle f).mor₂ = 0 := (isKInjective_shift hI N hN).elim _ _
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ (coneRotatedTriangle_distinguished f) g h₂
    have hk0 : k = 0 := (hI' N hN).elim k 0
    rw [hk, hk0]
    exact zero_comp
  exact ⟨fun g g' => (key g).trans (key g').symm⟩

/-- **The cone of a homomorphism of graded injective K-injective right differential graded modules
is graded injective and K-injective.** -/
theorem isDGInjective_cone {I I' : DifferentialGradedModule.{u, v, w} A} (f : I ⟶ I')
    (hI : IsDGInjective I) (hI' : IsDGInjective I') : IsDGInjective (conePackage f).cone :=
  ⟨gradedInjective_cone f hI.1 hI'.1, isKInjective_cone f hI.2 hI'.2⟩

end KInjective

/-! ### Isomorphisms of the derived category and cones -/

section Derived

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A homomorphism of right differential graded modules becomes an isomorphism of `D(A, d)`
exactly when its cone becomes zero there**: the image of the cone triangle is distinguished, and
its third arrow is the translate of the image of the homomorphism. -/
theorem isIso_toDerivedCategory_map_iff_isZero_cone {I I' : DifferentialGradedModule.{u, v, w} A}
    (f : I ⟶ I') :
    IsIso ((toDerivedCategory.{u, v, w} A).map ((HomotopyCategory.quotient A).map f)) ↔
      IsZero ((toDerivedCategory.{u, v, w} A).obj
        ((HomotopyCategory.quotient A).obj (conePackage f).cone)) := by
  set Q := toDerivedCategory.{u, v, w} A
  set g := (HomotopyCategory.quotient A).map f
  have hT := Q.map_distinguished _ (coneRotatedTriangle_distinguished f)
  have h₃ := Triangle.isZero₂_iff_isIso₃ _ hT
  change IsZero (Q.obj ((HomotopyCategory.quotient A).obj (conePackage f).cone)) ↔
    IsIso (Q.map (eqToHom (HomotopyCategory.shiftFunctor_obj A I).symm ≫ g⟦(1 : ℤ)⟧') ≫
      (Q.commShiftIso (1 : ℤ)).hom.app _) at h₃
  rw [h₃, isIso_comp_right_iff, Q.map_comp, eqToHom_map, isIso_comp_left_iff,
    ← isIso_iff_of_reflects_iso (Q.map g) (shiftFunctor _ (1 : ℤ))]
  exact (NatIso.isIso_map_iff (Q.commShiftIso (1 : ℤ)) g).symm

end Derived

end DifferentialGradedModule

end SheafOfModules

/-! ### The global sections of a cone, and the reduction to the kernel -/

namespace Stacks.ChaoticSite

open Stacks.PresheafOfModules _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [SmallCategory C] (R : Type u) [CommRing R]
  (ℬ : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R))

/-- **The global sections of the cone of `f` are the mapping cone of the global sections of
`f`**: the cone's complex is the mapping cone of `f`, and the additive functor `Γ` commutes with
mapping cones. -/
def dgGlobalSectionsConeIso {I I' : DifferentialGradedModule.{u, u, u} ℬ} (f : I ⟶ I') :
    (dgGlobalSections R ℬ).obj (conePackage f).cone ≅
      CochainComplex.mappingCone ((dgGlobalSections R ℬ).map f) :=
  eqToIso (congrArg ((globalSections R).mapHomologicalComplex _).obj
      (conePackage f).cone_complex) ≪≫
    CochainComplex.mappingCone.mapHomologicalComplexIso f.toHomologicalComplex (globalSections R)

/-- **The global sections of the cone of `f` are acyclic exactly when the global sections of `f`
are a quasi-isomorphism.** -/
theorem acyclic_dgGlobalSections_cone_iff {I I' : DifferentialGradedModule.{u, u, u} ℬ}
    (f : I ⟶ I') :
    ((dgGlobalSections R ℬ).obj (conePackage f).cone).Acyclic ↔
      QuasiIso ((dgGlobalSections R ℬ).map f) := by
  rw [← CochainComplex.mappingCone.acyclic_iff_quasiIso]
  exact ⟨fun h n => (h n).of_iso (dgGlobalSectionsConeIso R ℬ f),
    fun h n => (h n).of_iso (dgGlobalSectionsConeIso R ℬ f).symm⟩

/-- On a homomorphism of graded injective K-injective modules, the derived global sections are
the class of the global sections of that homomorphism, read through the identifications of their
values. -/
theorem derivedGlobalSections_map_of_isDGInjective {I I' : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) (hI' : IsDGInjective I') (f : I ⟶ I') :
    (derivedGlobalSections R ℬ).map ((toDerivedCategory.{u, u, u} ℬ).map
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).map f)) =
      eqToHom (derivedGlobalSections_obj_of_isDGInjective R ℬ hI) ≫
        DerivedCategory.Qh.map ((_root_.HomotopyCategory.quotient _ _).map
          ((dgGlobalSections R ℬ).map f)) ≫
        eqToHom (derivedGlobalSections_obj_of_isDGInjective R ℬ hI').symm :=
  rigidRightDerivedExtension_map_of_isDGInjective.{u, u, u} (X := constRingedSite C R) (A := ℬ)
    (derivedGlobalSectionsAux R ℬ) hI hI' f

/-- **On a homomorphism of graded injective K-injective modules, the derived global sections are
an isomorphism exactly when the global sections are a quasi-isomorphism.** -/
theorem isIso_derivedGlobalSections_map_iff {I I' : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) (hI' : IsDGInjective I') (f : I ⟶ I') :
    IsIso ((derivedGlobalSections R ℬ).map ((toDerivedCategory.{u, u, u} ℬ).map
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).map f))) ↔
      QuasiIso ((dgGlobalSections R ℬ).map f) := by
  rw [derivedGlobalSections_map_of_isDGInjective R ℬ hI hI' f, isIso_comp_left_iff,
    isIso_comp_right_iff, ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _

/-- **The derived global sections of the cone of a homomorphism of graded injective K-injective
modules vanish when the global sections of the homomorphism are a quasi-isomorphism**: the cone is
graded injective and K-injective, so its derived global sections are the class of its global
sections, which are the mapping cone of a quasi-isomorphism. -/
theorem isZero_derivedGlobalSections_cone {I I' : DifferentialGradedModule.{u, u, u} ℬ}
    (hI : IsDGInjective I) (hI' : IsDGInjective I') (f : I ⟶ I')
    (hf : QuasiIso ((dgGlobalSections R ℬ).map f)) :
    IsZero ((derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj (conePackage f).cone))) := by
  refine IsZero.of_iso ?_ (eqToIso (derivedGlobalSections_obj_of_isDGInjective R ℬ
      (isDGInjective_cone (X := constRingedSite C R) f hI hI')) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso (dgGlobalSectionsConeIso R ℬ f))
  exact (Triangle.isZero₃_iff_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished ((dgGlobalSections R ℬ).map f))).2
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hf)

/-- Every object of `D(ℬ, d)` is isomorphic to the image of a graded injective K-injective
module (Tag 0FT0). -/
theorem exists_isDGInjective_iso (Z : derivedCategory.{u, u, u} ℬ) :
    ∃ I : DifferentialGradedModule.{u, u, u} ℬ, IsDGInjective I ∧
      Nonempty (Z ≅ (toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)) := by
  obtain ⟨I, s, hs, hKI, hGI⟩ := exists_quasiIso_isDGInjective (X := constRingedSite C R) ℬ
    ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj (derivedCategoryModule ℬ Z))
  exact ⟨_, ⟨hGI, hKI⟩,
    ⟨@asIso _ _ _ _ _ ((quasiIsomorphisms.{u, u, u} ℬ).Q_inverts s hs)⟩⟩

/-- A morphism of `D(ℬ, d)` into the image of a graded injective K-injective module, out of the
image of a module, is the class of a homomorphism of modules (Tag 0FT8). -/
theorem exists_toDerivedCategory_map_eq {I I' : DifferentialGradedModule.{u, u, u} ℬ}
    (hI' : IsDGInjective I')
    (φ : (toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I) ⟶
      (toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I')) :
    ∃ f : I ⟶ I', (toDerivedCategory.{u, u, u} ℬ).map
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).map f) = φ := by
  obtain ⟨g, hg⟩ := (bijective_toDerivedCategory_map (X := constRingedSite C R)
    (hasKInjectiveResolutions_dg.{u, u, u} (X := constRingedSite C R) ℬ)
    ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I) hI'.2 hI'.1).2 φ
  obtain ⟨f⟩ := g
  exact ⟨f, hg⟩

/-- The cone of a homomorphism of right differential graded `ℬ`-modules whose source and target
lie in `QC(ℬ, d)` lies in `QC(ℬ, d)`, a triangulated subcategory (Tag 0GZA). -/
theorem qc_cone {I I' : DifferentialGradedModule.{u, u, u} ℬ} (f : I ⟶ I')
    (hI : Chaotic.QC ℬ ((toDerivedCategory.{u, u, u} ℬ).obj
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)))
    (hI' : Chaotic.QC ℬ ((toDerivedCategory.{u, u, u} ℬ).obj
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I'))) :
    Chaotic.QC ℬ ((toDerivedCategory.{u, u, u} ℬ).obj
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj (conePackage f).cone)) := by
  have hT := (toDerivedCategory.{u, u, u} ℬ).map_distinguished _
    (coneRotatedTriangle_distinguished (X := constRingedSite C R) f)
  refine ObjectProperty.ext_of_isTriangulatedClosed₂ (Chaotic.QC ℬ) _ hT hI' ?_
  change Chaotic.QC ℬ ((toDerivedCategory.{u, u, u} ℬ).obj
    ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj (shift I)))
  refine ObjectProperty.prop_of_iso _
    ((((toDerivedCategory.{u, u, u} ℬ).commShiftIso (1 : ℤ)).app
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj I)).symm ≪≫
      eqToIso (congrArg (toDerivedCategory.{u, u, u} ℬ).obj
        (HomotopyCategory.shiftFunctor_obj (X := constRingedSite C R) ℬ I))) ?_
  exact (Chaotic.QC ℬ).le_shift (1 : ℤ) _ hI

/-- **The reduction of the conservativity of the derived global sections on `QC(ℬ, d)` to its
kernel.** If no nonzero object of `QC(ℬ, d)` has zero derived global sections, then a morphism
`φ : M ⟶ N` of `QC(ℬ, d)` whose derived global sections are an isomorphism is an isomorphism.

Replace `M` and `N` by graded injective K-injective modules `I` and `I'`; then `φ` is the class of
a homomorphism `f : I ⟶ I'` (Tag 0FT8). Its global sections are a quasi-isomorphism, so the
derived global sections of the cone of `f`, which is graded injective and K-injective, vanish. The
cone lies in the triangulated subcategory `QC(ℬ, d)` along with `I` and `I'`, so it vanishes by
hypothesis, and `f` becomes an isomorphism of `D(ℬ, d)`. -/
theorem isIso_of_isIso_derivedGlobalSections_map_of_kernel
    (hker : ∀ M : derivedCategory.{u, u, u} ℬ, Chaotic.QC ℬ M →
      IsZero ((derivedGlobalSections R ℬ).obj M) → IsZero M)
    {M N : derivedCategory.{u, u, u} ℬ} (hM : Chaotic.QC ℬ M) (hN : Chaotic.QC ℬ N)
    (φ : M ⟶ N) (hφ : IsIso ((derivedGlobalSections R ℬ).map φ)) : IsIso φ := by
  obtain ⟨I, hI, ⟨eM⟩⟩ := exists_isDGInjective_iso R ℬ M
  obtain ⟨I', hI', ⟨eN⟩⟩ := exists_isDGInjective_iso R ℬ N
  obtain ⟨f, hf⟩ := exists_toDerivedCategory_map_eq R ℬ hI' (eM.inv ≫ φ ≫ eN.hom)
  have hφ' : IsIso ((derivedGlobalSections R ℬ).map ((toDerivedCategory.{u, u, u} ℬ).map
      ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).map f))) := by
    rw [hf, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hzero := isZero_derivedGlobalSections_cone R ℬ hI hI' f
    ((isIso_derivedGlobalSections_map_iff R ℬ hI hI' f).1 hφ')
  have hQC := qc_cone R ℬ f (ObjectProperty.prop_of_iso _ eM hM)
    (ObjectProperty.prop_of_iso _ eN hN)
  have hiso := (isIso_toDerivedCategory_map_iff_isZero_cone (X := constRingedSite C R) f).2
    (hker _ hQC hzero)
  have hiso' : IsIso (eM.inv ≫ φ ≫ eN.hom) := by
    rw [← hf]
    exact hiso
  have hφeq : φ = eM.hom ≫ (eM.inv ≫ φ ≫ eN.hom) ≫ eN.inv := by simp
  rw [hφeq]
  infer_instance

end Stacks.ChaoticSite
