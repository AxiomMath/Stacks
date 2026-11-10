module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Cohomology over an affine base

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S` affine and
let `F` be a quasi-coherent `𝒪_X`-module. The cohomology of `F` is the module of global sections
of its higher direct image, `H ᵖ(X, F) = H ⁰(S, R ᵖ f_* F)`.

Both sides are modules over `Γ(S, ⊤)`: the left-hand side is `H ᵖ(X, F)`, a `Γ(X, ⊤)`-module,
with its scalars restricted along `Γ(S, ⊤) ⟶ Γ(X, ⊤)`, and the right-hand side is the module of
global sections of the higher direct image. The statement is an isomorphism of functors on the
full subcategory of quasi-coherent modules.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat`: the `ℤ`-indexed and the
  `ℕ`-indexed higher right derived functors agree in natural-number degrees.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.rightDerivedCompIso`: an exact functor may be
  pulled out of a right derived functor.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.rightDerivedIsoOfNatIso`: a natural isomorphism
  of additive functors induces one of their right derived functors.

## Main results

* `cohomologyIsoGlobalSectionsRightDerivedPushforward`, in the same namespace: the natural
  isomorphism `H ᵖ(X, F) ≅ H ⁰(S, R ᵖ f_* F)` of `Γ(S, ⊤)`-modules for quasi-coherent `F`, when
  `f` is quasi-compact and quasi-separated and the target is affine.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-! ### Global sections of sheaves of modules on a scheme -/

/-- Global sections of sheaves of modules on a scheme is left exact. -/
instance moduleGlobalSections_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleGlobalSections X) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _

/-! ### Comparisons of right derived functors -/

/-- For an additive functor out of an abelian category with enough injectives, the degree-`n`
value of the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` at a natural number `n` is the
degree-`n` value of the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`. -/
def derivedPlusIsoNat {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (G : C ⥤ D) [G.Additive] (A : C) (n : ℕ) :
    (G.rightDerivedPlus (n : ℤ)).obj A ≅ (G.rightDerived n).obj A :=
  ((Stacks.DerivedIndexing.rightDerivedIso G n).app A).symm

/-- If `G` preserves homology then `G(R ⁿF(A)) ≅ R ⁿ(F ⋙ G)(A)`. -/
def rightDerivedCompIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [G.PreservesHomology] (A : C) (n : ℕ) :
    G.obj ((F.rightDerived n).obj A) ≅ ((F ⋙ G).rightDerived n).obj A :=
  ((CategoryTheory.Functor.rightDerivedCompIso F G n).app A).symm

/-- A natural isomorphism of additive functors induces one of their right derived functors. -/
def rightDerivedIsoOfNatIso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n :=
  CategoryTheory.Functor.rightDerivedIsoOfNatIso e n

/-- If `G` preserves the left homology in degree `n` of `F` applied to the chosen injective
resolution of every `E.obj X`, then `E ⋙ R ⁿF ⋙ G ≅ E ⋙ R ⁿ(F ⋙ G)`. -/
private def rightDerivedCompositionNatIso
    {D A B C : Type*} [Category* D] [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasInjectiveResolutions A]
    (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (n : ℕ)
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n)) :
    E ⋙ F.rightDerived n ⋙ G ≅ E ⋙ (F ⋙ G).rightDerived n := by
  let K (X : D) := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj (E.obj X)).as
  have hK : ∀ X, G.PreservesLeftHomologyOf ((K X).sc n) := fun X => by
    simpa [K, injectiveResolutions, HomotopyCategory.quotient_obj_as] using h X
  refine NatIso.ofComponents
    (fun X => by
      letI := hK X
      unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
        HomotopyCategory.homologyFunctor
      exact ((K X).sc n).mapHomologyIso G |>.symm) ?_
  intro X Y φ
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
    ((injectiveResolutions A).map (E.map φ))
  let _ := hK X
  let _ := hK Y
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_map]
  rw [← hg]
  unfold HomotopyCategory.homologyFunctor
  dsimp [Functor.comp_map, Functor.mapHomotopyCategory, HomologicalComplex.homologyFunctor]
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) n).map
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

/-! ### Right acyclic objects -/

section Acyclic

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

omit [HasDerivedCategory C] in
/-- The right derived functor of an additive functor out of a category with enough injectives is
everywhere defined. -/
private lemma hasRightDerivedFunctor_mapHomotopyCategoryPlus (G : C ⥤ D) [G.Additive] :
    (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
  have := (HomotopyCategory.Plus.localizerMorphism_derives
    (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).hasPointwiseRightDerivedFunctor
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_mapHomotopyCategoryPlus

/-- Right acyclicity in Mathlib's `ℕ`-indexing: a left exact additive functor is acyclic at `A`
exactly when all its positive-degree right derived functors vanish at `A`. -/
private lemma rightAcyclic_iff_forall_pos_isZero (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] (A : C) :
    G.rightAcyclic A ↔ ∀ n : ℕ, 0 < n → IsZero ((G.rightDerived n).obj A) := by
  rw [(G.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus A).2 inferInstance]
  refine ⟨fun h n hn => (h n (by omega)).of_iso (derivedPlusIsoNat G A n).symm, fun h i hi => ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact (h n (by omega)).of_iso (derivedPlusIsoNat G A n)

/-- Right acyclicity is invariant under isomorphism. -/
private lemma rightAcyclic_of_iso (G : C ⥤ D) [G.Additive] {A B : C} (e : A ≅ B)
    (h : G.rightAcyclic A) : G.rightAcyclic B :=
  (G.rightAcyclic).prop_of_iso e h

end Acyclic

/-! ### Global sections over an affine base -/

/-- A module whose underlying abelian group is zero is zero. -/
private lemma isZero_of_isZero_forget₂ {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  exact congrArg (fun φ ↦ AddCommGrpCat.Hom.hom φ x) ((IsZero.iff_id_eq_zero _).1 h)

attribute [local instance] hasRightDerivedFunctor_mapHomotopyCategoryPlus

/-- A quasi-coherent module on an affine scheme is right acyclic for global sections. -/
private lemma rightAcyclic_moduleGlobalSections_of_isAffine (S : Scheme.{u}) [IsAffine S]
    (F : S.Modules) [F.IsQuasicoherent] : (moduleGlobalSections S).rightAcyclic F := by
  refine (rightAcyclic_iff_forall_pos_isZero (moduleGlobalSections S) F).2 fun n hn => ?_
  have hcoh : IsZero (((moduleGlobalSections S ⋙
      forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).rightDerived n).obj F) := by
    change IsZero (Hgroup S.ringCatSheaf ⊤ n F)
    exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S F ⊤
      (isAffineOpen_top S) n hn
  exact isZero_of_isZero_forget₂ _ (hcoh.of_iso
    (rightDerivedCompIso (moduleGlobalSections S) _ F n))

/-! ### The comparison -/

/-- Global sections of a pushforward are global sections of the module itself, with the scalars
restricted along `Γ(S, ⊤) ⟶ Γ(X, ⊤)`; the identification is the identity on sections. -/
private def pushforwardCompModuleGlobalSectionsIso {X S : Scheme.{u}} (f : X ⟶ S) :
    moduleGlobalSections X ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      Scheme.Modules.pushforward f ⋙ moduleGlobalSections S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The `n`-th right derived functor of global sections on `X`, followed by restriction of scalars
along `Γ(S, ⊤) ⟶ Γ(X, ⊤)`, is the `n`-th right derived functor of global sections of the
pushforward along `f`. -/
private def rightDerivedModuleGlobalSectionsIso {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    (moduleGlobalSections X).rightDerived n ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      (Scheme.Modules.pushforward f ⋙ moduleGlobalSections S).rightDerived n :=
  haveI : (ModuleCat.restrictScalars f.appTop.hom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (CategoryTheory.Functor.rightDerivedCompIso (moduleGlobalSections X)
      (ModuleCat.restrictScalars f.appTop.hom) n).symm ≪≫
    rightDerivedIsoOfNatIso (pushforwardCompModuleGlobalSectionsIso f) n

/-- The quasi-coherent modules on a scheme, included into `AlgebraicGeometry.Scheme.Modules`. -/
private abbrev qcohInclusion (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- Over an affine base, global sections preserve the left homology in degree `n` of the
pushforward of the chosen injective resolution of a quasi-coherent module. -/
private lemma preservesLeftHomologyOf_moduleGlobalSections {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S] (n : ℕ)
    (A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (moduleGlobalSections S).PreservesLeftHomologyOf
      ((((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution ((qcohInclusion X).obj A)).cocomplex).sc n) := by
  let F := (qcohInclusion X).obj A
  let _ : F.IsQuasicoherent := A.property
  let I := injectiveResolution F
  let K : CochainComplex S.Modules ℕ :=
    ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hX : ∀ i, (moduleGlobalSections S).rightAcyclic (K.X i) := fun i =>
    Stacks.SchemeCohomology.rightAcyclic_schemePushforward_obj f ⊤ (I.cocomplex.X i) (I.injective i)
  have hH : ∀ i, (moduleGlobalSections S).rightAcyclic (K.homology i) := by
    intro i
    let _ : (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
      isQuasicoherent_rightDerived f F i
    exact rightAcyclic_of_iso (moduleGlobalSections S)
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) i)
      (rightAcyclic_moduleGlobalSections_of_isAffine S
        (((Scheme.Modules.pushforward f).rightDerived i).obj F))
  exact ((moduleGlobalSections S).rightAcyclic_cycles_and_preservesLeftHomologyOf_sc
    K hX hH n).2

/-- For `f` quasi-compact and quasi-separated with `S` affine, on the quasi-coherent modules,
cohomology in a natural-number degree `n`, with scalars restricted to `Γ(S, ⊤)`, is the global
sections of the degree-`n` higher direct image. -/
private def affineBaseRightDerivedIso {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] (n : ℕ) :
    qcohInclusion X ⋙
        (moduleGlobalSections X).rightDerived n ⋙ ModuleCat.restrictScalars f.appTop.hom ≅
      qcohInclusion X ⋙
        (Scheme.Modules.pushforward f).rightDerived n ⋙ moduleGlobalSections S :=
  Functor.isoWhiskerLeft (qcohInclusion X) (rightDerivedModuleGlobalSectionsIso f n) ≪≫
    (rightDerivedCompositionNatIso (qcohInclusion X) (Scheme.Modules.pushforward f)
      (moduleGlobalSections S) n (preservesLeftHomologyOf_moduleGlobalSections f n)).symm

/-- For a quasi-compact and quasi-separated morphism `f : X ⟶ S` of
schemes with `S` affine, the cohomology of a quasi-coherent module on `X` is naturally
isomorphic, as a module over `Γ(S, ⊤)`, to the module of global sections of its higher direct
image: `H ᵖ(X, F) = H ⁰(S, R ᵖ f_* F)`. -/
@[no_expose]
def cohomologyIsoGlobalSectionsRightDerivedPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S] (q : ℤ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (moduleGlobalSections X).rightDerivedPlus q ⋙
        ModuleCat.restrictScalars f.appTop.hom ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
      (Scheme.Modules.pushforward f).rightDerivedPlus q ⋙
        moduleGlobalSections S := by
  let Q := qcohInclusion X
  by_cases hq : 0 ≤ q
  · rw [← Int.toNat_of_nonneg hq]
    exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q
          (Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections X) q.toNat).symm)
          (ModuleCat.restrictScalars f.appTop.hom) ≪≫
        affineBaseRightDerivedIso f q.toNat ≪≫
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q
        (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q.toNat).symm)
        (moduleGlobalSections S)).symm
  · refine NatIso.ofComponents (fun A => ?_) ?_
    · exact IsZero.iso
        ((ModuleCat.restrictScalars f.appTop.hom).map_isZero
          (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
            (moduleGlobalSections X) (Q.obj A) q (by omega)))
        ((moduleGlobalSections S).map_isZero
          (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
            (Scheme.Modules.pushforward f) (Q.obj A) q (by omega)))
    · intro A B g
      exact ((moduleGlobalSections S).map_isZero
        (CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
          (Scheme.Modules.pushforward f) (Q.obj B) q (by omega))).eq_of_tgt _ _

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
