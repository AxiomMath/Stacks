module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemLevelwise
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Fiber
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionLevel
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.QuotientRestrictScalars

/-!
# Mittag-Leffler for sections of derived reductions through an adic model

Let `(C, J)` be a site, `Λ` a commutative ring, `I ⊆ Λ` a finitely generated ideal and
`A = Λ^∧` the `I`-adic completion, with `J = IA`. Let `K'` be represented by a K-flat complex
`P` of sheaves of `Λ`-modules and let `W` be a K-flat complex of sheaves of `A`-modules such
that for every `n ≥ 1` the reductions `Λ/Iⁿ ⊗_Λ P` and `Λ/Iⁿ ⊗_A W` are isomorphic in
`D(C, Λ/Iⁿ)`, by isomorphisms which need not be compatible as `n` varies. Then the inverse
system `n ↦ Γ(U, H⁰(K' ⊗_Λ^L \underline{Λ/Iⁿ}))` satisfies the Mittag-Leffler condition as soon
as `j ↦ Γ(U, H⁰(W ⊗_A^L \underline{A/Jʲ}))` does.

## Main results

* `Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel`: the system
  `n ↦ Γ(U, H⁰(K' ⊗_Λ^L \underline{Λ/Iⁿ}))` is Mittag-Leffler when the corresponding system of
  an adic model `W` is.
* `Stacks.ModuleSheaf.constantComplexReductionSectionsIso`: the sections of the reductions of a
  constant complex `\underline{F}` are the sections of the constant sheaves on the cohomology
  of the termwise reductions of `F`.
* `Stacks.ModuleSheaf.nonempty_iso_extendScalars_sheafFiber`: if `S ⊗_Λ^L P` is constant with
  value `E`, then `E ≅ S ⊗_Λ P_Φ` for the fibre `P_Φ` of `P` at any point `Φ`.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe t t' t'' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}] (I : Ideal Λ)
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [∀ n : ℕ, HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (Λ ⧸ I ^ n)))]
  [HasDerivedCategory.{t''} (Sheaf J (ModuleCat.{w} (AdicCompletion I Λ)))]

/-- **Mittag-Leffler for sections of derived reductions through an adic model.** Let `P` be a
K-flat complex of sheaves of `Λ`-modules representing `K'` and `W` a K-flat complex of sheaves
of modules over the `I`-adic completion `A` of `Λ`, `I` finitely generated, such that all their
reductions `Λ/Iⁿ⁺¹ ⊗ P` and `Λ/Iⁿ⁺¹ ⊗_A W` are K-flat and isomorphic in `D(C, Λ/Iⁿ⁺¹)`. If the
system `j ↦ Γ(U, H⁰(W ⊗_A^L \underline{A/(IA)ʲ}))` is Mittag-Leffler, so is the system
`n ↦ Γ(U, H⁰(K' ⊗_Λ^L \underline{Λ/Iⁿ}))`. -/
theorem isMittagLefflerCategorical_reductionSections_of_adicModel (hI : I.FG) (U : C)
    {K' : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (eP : DerivedCategory.Q.obj P ≅ K')
    (hP : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (hP' : ∀ n : ℕ, KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))))
      (((extendScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    {W : CochainComplex (Sheaf J (ModuleCat.{w} (AdicCompletion I Λ))) ℤ}
    (hW : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} (AdicCompletion I Λ)))) W)
    (hW' : ∀ n : ℕ, KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))))
      (((extendScalars J (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj W))
    (ψ : ∀ n : ℕ, DerivedCategory.Q.obj
        (((extendScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((extendScalars J (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj W))
    (hG : IsMittagLefflerCategorical
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (AdicCompletion I Λ)
          (I.map (algebraMap Λ (AdicCompletion I Λ)))
          (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)) ⋙
        constantSheaf J (ModuleCat.{w} (AdicCompletion I Λ)) ⋙
          DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft (DerivedCategory.Q.obj W) ⋙
            DerivedCategory.homologyFunctor _ 0 ⋙
              (sheafSections J (ModuleCat.{w} (AdicCompletion I Λ))).obj (op U) ⋙
                ModuleCat.restrictScalars.{w} (algebraMap Λ (AdicCompletion I Λ)))) :
    IsMittagLefflerCategorical
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I (ModuleCat.of Λ Λ) ⋙
        constantSheaf J (ModuleCat.{w} Λ) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          tensorLeft K' ⋙ DerivedCategory.homologyFunctor _ 0 ⋙
            (sheafSections J (ModuleCat.{w} Λ)).obj (op U)) := by
  refine IsMittagLefflerCategorical.of_forall_le_iso hG fun n => ?_
  have hgφ : (AdicCompletion.evalₐ I (n + 1)).toRingHom.comp
      (algebraMap Λ (AdicCompletion I Λ)) = Ideal.Quotient.mk (I ^ (n + 1)) :=
    (AdicCompletion.evalₐ I (n + 1)).comp_algebraMap
  have hmap : (I.map (algebraMap Λ (AdicCompletion I Λ))).map
      (AdicCompletion.evalₐ I (n + 1)).toRingHom = I.map (Ideal.Quotient.mk (I ^ (n + 1))) := by
    rw [Ideal.map_map, hgφ]
  have hker : RingHom.ker (AdicCompletion.evalₐ I (n + 1)).toRingHom ≤
      I.map (algebraMap Λ (AdicCompletion I Λ)) ^ (n + 1) := by
    rw [AdicCompletion.ker_evalₐ I hI (n + 1)]
  obtain ⟨e, he⟩ := exists_le_iso_comp_of_iso
    (reductionLevelSectionsIso (Ideal.Quotient.mk (I ^ (n + 1)))
      (AdicCompletion.evalₐ I (n + 1)).toRingHom (algebraMap Λ (AdicCompletion I Λ)) hgφ U eP hP
      (hP' n) hW (hW' n) (ψ n)) (n + 1)
    (fun j hj => AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso
      (Ideal.Quotient.mk (I ^ (n + 1))) Ideal.Quotient.mk_surjective I _ rfl j
      (by rw [Ideal.mk_ker]; exact Ideal.pow_le_pow_right hj))
    (fun i j hij hjn =>
      AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso_naturality _ _ _ _ _ hij _ _)
    (fun j hj => AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso
      (AdicCompletion.evalₐ I (n + 1)).toRingHom (AdicCompletion.surjective_evalₐ I (n + 1)) _ _
      hmap j (hker.trans (Ideal.pow_le_pow_right hj)))
    (fun i j hij hjn =>
      AlgebraicGeometry.ProEtale.adicQuotientRestrictScalarsIso_naturality _ _ _ _ _ hij _ _)
  exact ⟨fun j hj => e j (hj.trans n.le_succ), fun i j hij hjn => he i j hij (hjn.trans n.le_succ)⟩

section ConstantModel

variable {A : Type w} [CommRing A] [HasDerivedCategory.{t''} (Sheaf J (ModuleCat.{w} A))]

/-- The constant sheaf functor turns the tensor product of modules into the tensor product of
sheaves, as an isomorphism of curried bifunctors. -/
def constantSheafTensorIso :
    letI := constantSheafMonoidal J A
    curriedTensor (ModuleCat.{w} A) ⋙
        (Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} A)) ≅
      constantSheaf J (ModuleCat.{w} A) ⋙ curriedTensor (Sheaf J (ModuleCat.{w} A)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (constantSheaf J (ModuleCat.{w} A)) :=
  letI := constantSheafMonoidal J A
  NatIso.ofComponents (fun X => NatIso.ofComponents
      (fun M => (Functor.Monoidal.μIso (constantSheaf J (ModuleCat.{w} A)) X M).symm)
      (fun g => by simp))
    (fun f => by
      ext M
      simp)

/-- **Sections of the derived reductions of a constant complex.** For a complex `F` of
`A`-modules whose constant complex `\underline{F}` is K-flat, the functor
`M ↦ Γ(U, H⁰(\underline{F} ⊗_A^L \underline{M}))` is `M ↦ Γ(U, \underline{H⁰(F ⊗_A M)})`, the
tensor product being taken termwise. -/
def constantComplexReductionSectionsIso (F : CochainComplex (ModuleCat.{w} A) ℤ)
    (hW : KFlatLeft (curriedTensor (Sheaf J (ModuleCat.{w} A)))
      (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
    (U : C) :
    constantSheaf J (ModuleCat.{w} A) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        tensorLeft (DerivedCategory.Q.obj
          (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) ⋙
          DerivedCategory.homologyFunctor _ 0 ⋙ (sheafSections J (ModuleCat.{w} A)).obj (op U) ≅
      rowFunctor (curriedTensor (ModuleCat.{w} A)) F ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0 ⋙
          constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj (op U) :=
  let c := constantSheaf J (ModuleCat.{w} A)
  let W := (c.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let Γ := (sheafSections J (ModuleCat.{w} A)).obj (op U)
  Functor.isoWhiskerLeft c
      (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0)
          (tensorLeft (DerivedCategory.Q.obj W) ⋙ DerivedCategory.homologyFunctor _ 0 ⋙ Γ) ≪≫
        Functor.isoWhiskerRight (derivedTensorSingleIso hW)
          (DerivedCategory.homologyFunctor _ 0 ⋙ Γ) ≪≫
        Functor.isoWhiskerLeft (rowFunctor _ W)
          (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ 0) Γ)) ≪≫
    Functor.isoWhiskerRight
      (mapRowFunctorIso (curriedTensor (ModuleCat.{w} A))
        (curriedTensor (Sheaf J (ModuleCat.{w} A))) (constantSheafTensorIso (J := J)) F).symm
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0 ⋙ Γ) ≪≫
    Functor.isoWhiskerLeft (rowFunctor (curriedTensor (ModuleCat.{w} A)) F)
      (Functor.isoWhiskerRight (c.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) 0) Γ)

end ConstantModel

section Fiber

variable [LocallySmall.{w} C] (Φ : J.Point.{w}) {S : Type w} [CommRing S]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))] [HasDerivedCategory.{t''} (ModuleCat.{w} S)]

/-- **A complex of constant sheaves is recovered from its fibre.** If a complex `P` of sheaves of
`S`-modules is isomorphic in `D(C, S)` to the constant complex `\underline{E}` of an object `E` of
`D(S)`, then `E` is isomorphic to the fibre of `P` at any point of the site. -/
theorem nonempty_iso_sheafFiber_of_iso_constantSheaf
    (P : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ) (E : DerivedCategory (ModuleCat.{w} S))
    (e : DerivedCategory.Q.obj P ≅
      (constantSheaf J (ModuleCat.{w} S)).mapDerivedCategory.obj E) :
    Nonempty (E ≅ DerivedCategory.Q.obj
      (((moduleSheafFiber S Φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  let c := constantSheaf J (ModuleCat.{w} S)
  let St := moduleSheafFiber S Φ
  have : PreservesFiniteColimits c := by unfold c constantSheaf; infer_instance
  have : PreservesFiniteLimits c := preservesFiniteLimits_constantSheaf J S
  have : c.Additive := Functor.additive_of_preserves_binary_products _
  let X := DerivedCategory.Q.objPreimage E
  let eX : DerivedCategory.Q.obj X ≅ E := DerivedCategory.Q.objObjPreimageIso E
  exact ⟨eX.symm ≪≫
    DerivedCategory.Q.mapIso (((Functor.mapHomologicalComplexIdIso _ _).app X).symm ≪≫
      (NatIso.mapHomologicalComplex (CategoryTheory.Sites.constantSheafFiberNatIso Φ).symm
        (ComplexShape.up ℤ)).app X ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (c ⋙ St)) (ComplexShape.up ℤ)).app
        X).symm) ≪≫
    (St.mapDerivedCategoryFactors.app _).symm ≪≫
    St.mapDerivedCategory.mapIso ((c.mapDerivedCategoryFactors.app X).symm ≪≫
      c.mapDerivedCategory.mapIso eX ≪≫ e.symm) ≪≫
    St.mapDerivedCategoryFactors.app P⟩

/-- **The coefficients of a constant derived extension of scalars are the extension of scalars
of the fibre.** Let `P` be a K-flat complex of sheaves of `Λ`-modules and `f : Λ → S` a ring map.
If `S ⊗_Λ^L P` is isomorphic in `D(C, S)` to the constant complex `\underline{E}`, then `E` is
isomorphic in `D(S)` to `S ⊗_Λ P_Φ`, the termwise extension of scalars of the fibre of `P` at any
point `Φ` of the site. -/
theorem nonempty_iso_extendScalars_sheafFiber {Λ : Type w} [CommRing Λ]
    [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] (f : Λ →+* S)
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (E : DerivedCategory (ModuleCat.{w} S))
    (e : (derivedExtendScalars J f).obj (DerivedCategory.Q.obj P) ≅
      (constantSheaf J (ModuleCat.{w} S)).mapDerivedCategory.obj E) :
    Nonempty (E ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{w, w, w} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((moduleSheafFiber Λ Φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by
  have : (ModuleCat.extendScalars.{w, w, w} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{w} f).left_adjoint_additive
  obtain ⟨e'⟩ := nonempty_iso_sheafFiber_of_iso_constantSheaf Φ _ E
    ((derivedExtendScalarsObjIso J f hP).symm ≪≫ e)
  exact ⟨e' ≪≫ DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P ≪≫
      (NatIso.mapHomologicalComplex (sheafFiberExtendScalarsIso Φ f) (ComplexShape.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app P).symm)⟩

end Fiber

end Stacks.ModuleSheaf

end
