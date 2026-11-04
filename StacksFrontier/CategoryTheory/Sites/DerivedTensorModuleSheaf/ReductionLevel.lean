module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle

/-!
# Derived reductions of a K-flat complex at a fixed level

Let `(C, J)` be a site, `f : Λ →+* S` a homomorphism of commutative rings and `P` a K-flat
complex of sheaves of `Λ`-modules. For a sheaf `N` of `S`-modules, the cohomology sheaves of
`P ⊗_Λ^L N` (with `N` read over `Λ` and placed in degree zero) are those of
`(S ⊗_Λ P) ⊗_S^L N`, read over `Λ`, naturally in `N`. This is the projection formula, made
natural in the coefficients: it is what identifies the reductions of `P` modulo all ideals
containing a fixed ideal with the reductions of a single complex over the quotient ring.

## Main definitions

* `Stacks.ModuleSheaf.homologyDerivedTensorSingleRestrictScalarsIso`: the natural isomorphism
  `Hⁿ(P ⊗_Λ^L N[0]) ≅ Hⁿ((S ⊗_Λ P) ⊗_S^L N[0])` of functors of the sheaf `N` of `S`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe t t' t'' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ S : Type w} [CommRing Λ] [CommRing S] [UnivLE.{max u v, w}] (f : Λ →+* S)
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))]

/-- **The projection formula on cohomology, natural in the coefficients.** For a K-flat complex
`P` of sheaves of `Λ`-modules whose extension of scalars `S ⊗_Λ P` is again K-flat, and every
`n`, the functor `N ↦ Hⁿ(P ⊗_Λ^L N[0])` on sheaves of `S`-modules (with `N` read over `Λ`) is
the functor `N ↦ Hⁿ((S ⊗_Λ P) ⊗_S^L N[0])` read over `Λ`. -/
def homologyDerivedTensorSingleRestrictScalarsIso
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (hP' : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} S)))
      (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) (n : ℤ) :
    restrictScalars J f ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P) ⋙
          DerivedCategory.homologyFunctor _ n ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        tensorLeft (DerivedCategory.Q.obj
          (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⋙
          DerivedCategory.homologyFunctor _ n) ⋙ restrictScalars J f :=
  Functor.isoWhiskerLeft (restrictScalars J f)
      (Functor.isoWhiskerRight (derivedTensorSingleIso hP)
          (DerivedCategory.homologyFunctor _ n) ≪≫
        Functor.isoWhiskerLeft (rowFunctor _ P)
          (DerivedCategory.homologyFunctorFactors _ n)) ≪≫
    Functor.isoWhiskerRight
      (mapRowFunctorIso (extendScalars J f ⋙ curriedTensor (Sheaf J (ModuleCat.{w} S)))
        (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))
        (extendScalarsTensorRestrictScalarsIso f) P).symm
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n) ≪≫
    Functor.isoWhiskerLeft (rowFunctor _ P)
      ((restrictScalars J f).mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
          (rowFunctor (curriedTensor (Sheaf J (ModuleCat.{w} S)))
            (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (DerivedCategory.homologyFunctorFactors _ n).symm ≪≫
        Functor.isoWhiskerRight (derivedTensorSingleIso hP').symm
          (DerivedCategory.homologyFunctor _ n))
      (restrictScalars J f)

section Sections

variable {A : Type w} [CommRing A] (g : A →+* S) (φ : Λ →+* A) (hgφ : g.comp φ = f)
  [HasDerivedCategory.{t''} (Sheaf J (ModuleCat.{w} A))] (U : C)

/-- Sections over `U` commute with restriction of scalars. -/
def restrictScalarsCompSheafSectionsIso :
    restrictScalars J f ⋙ (sheafSections J (ModuleCat.{w} Λ)).obj (op U) ≅
      (sheafSections J (ModuleCat.{w} S)).obj (op U) ⋙ ModuleCat.restrictScalars.{w} f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

include hgφ in
/-- **The sections of the reductions at one level, as functors of the coefficients.** Let
`φ : Λ → A` and `g : A → S` be ring maps with `g ∘ φ = f`, let `P` be a K-flat complex of
sheaves of `Λ`-modules representing `K'`, and `W` a K-flat complex of sheaves of `A`-modules,
such that `S ⊗_Λ P` and `S ⊗_A W` are isomorphic in `D(C, S)` and again K-flat. Then the two
functors on `S`-modules
`M ↦ Γ(U, H⁰(K' ⊗_Λ^L \underline{M}))` and `M ↦ Γ(U, H⁰(W ⊗_A^L \underline{M}))`, the second
read over `Λ`, are isomorphic. -/
def reductionLevelSectionsIso {K' : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (eP : DerivedCategory.Q.obj P ≅ K')
    (hP : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (hP' : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} S)))
      (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    {W : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ}
    (hW : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} A))) W)
    (hW' : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} S)))
      (((extendScalars J g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
    (ψ : DerivedCategory.Q.obj
        (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((extendScalars J g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) :
    ModuleCat.restrictScalars.{w} f ⋙ constantSheaf J (ModuleCat.{w} Λ) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K' ⋙
          DerivedCategory.homologyFunctor _ 0 ⋙ (sheafSections J (ModuleCat.{w} Λ)).obj (op U) ≅
      ModuleCat.restrictScalars.{w} g ⋙ constantSheaf J (ModuleCat.{w} A) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft (DerivedCategory.Q.obj W) ⋙
          DerivedCategory.homologyFunctor _ 0 ⋙ (sheafSections J (ModuleCat.{w} A)).obj (op U) ⋙
            ModuleCat.restrictScalars.{w} φ :=
  let cS := constantSheaf J (ModuleCat.{w} S)
  let sgS := HomologicalComplex.single (Sheaf J (ModuleCat.{w} S)) (ComplexShape.up ℤ) 0 ⋙
    DerivedCategory.Q
  let HS := DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} S)) 0
  let HΛ := DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) 0
  let HA := DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} A)) 0
  let ΓΛ := (sheafSections J (ModuleCat.{w} Λ)).obj (op U)
  let ΓA := (sheafSections J (ModuleCat.{w} A)).obj (op U)
  let ΓS := (sheafSections J (ModuleCat.{w} S)).obj (op U)
  let Wg := ((extendScalars J g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W
  Functor.isoWhiskerRight (restrictScalarsConstantSheafIso J f).symm
      (DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K' ⋙ HΛ ⋙ ΓΛ) ≪≫
    Functor.isoWhiskerLeft (cS ⋙ restrictScalars J f)
      (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0)
          (tensorLeft K' ⋙ HΛ ⋙ ΓΛ) ≪≫
        Functor.isoWhiskerLeft (HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q) (Functor.isoWhiskerRight ((curriedTensor _).mapIso eP.symm)
            (HΛ ⋙ ΓΛ))) ≪≫
    Functor.isoWhiskerLeft cS
      (Functor.isoWhiskerRight (homologyDerivedTensorSingleRestrictScalarsIso f hP hP' 0) ΓΛ) ≪≫
    Functor.isoWhiskerLeft (cS ⋙ sgS)
      (Functor.isoWhiskerRight ((curriedTensor _).mapIso ψ) (HS ⋙ restrictScalars J f ⋙ ΓΛ)) ≪≫
    Functor.isoWhiskerLeft (cS ⋙ sgS ⋙ tensorLeft (DerivedCategory.Q.obj Wg) ⋙ HS)
      (restrictScalarsCompSheafSectionsIso f U ≪≫
        Functor.isoWhiskerLeft ΓS (ModuleCat.restrictScalarsComp'.{w} φ g f hgφ.symm) ≪≫
        Functor.isoWhiskerRight (restrictScalarsCompSheafSectionsIso g U).symm
          (ModuleCat.restrictScalars.{w} φ)) ≪≫
    Functor.isoWhiskerLeft cS
      (Functor.isoWhiskerRight (homologyDerivedTensorSingleRestrictScalarsIso g hW hW' 0).symm
        (ΓA ⋙ ModuleCat.restrictScalars.{w} φ)) ≪≫
    Functor.isoWhiskerRight (restrictScalarsConstantSheafIso J g)
      ((HomologicalComplex.single (Sheaf J (ModuleCat.{w} A)) (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q) ⋙ tensorLeft (DerivedCategory.Q.obj W) ⋙ HA ⋙ ΓA ⋙
        ModuleCat.restrictScalars.{w} φ) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars.{w} g ⋙ constantSheaf J (ModuleCat.{w} A))
      (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0).symm
        (tensorLeft (DerivedCategory.Q.obj W) ⋙ HA ⋙ ΓA ⋙ ModuleCat.restrictScalars.{w} φ))

end Sections

end Stacks.ModuleSheaf

end
