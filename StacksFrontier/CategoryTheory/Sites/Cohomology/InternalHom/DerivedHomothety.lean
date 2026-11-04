module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingOnModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UncurryingOfMorphisms

/-!
# The homothety map `𝒪 ⟶ R𝓗om(K, K)` on a ringed site

For an object `K` of `D(𝒪)` the homothety map `𝒪 ⟶ R𝓗om(K, K)` is the morphism corresponding to
the left unit constraint `𝒪 ⊗^L K ≅ K` under the tensor–Hom bijection of Stacks 08J8.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedHomothety`: the homothety map.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedHomothety_iff_of_isIso`: the homothety is invertible
  exactly when some morphism `𝒪 ⟶ R𝓗om(K, K)` with invertible transpose is.
* `AlgebraicGeometry.RingedSite.derivedHomothety_naturality`: the homothety is natural for
  isomorphisms of `K`.
* `AlgebraicGeometry.RingedSite.isIso_derivedHomothety_Q_iff`: on representatives, the homothety
  of `Q B` is invertible exactly when a morphism of complexes `𝒪 ⟶ SheafHom(B, I)` whose
  uncurrying is a quasi-isomorphism is one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The left unit constraint `𝒪 ⊗^L K ≅ K` of Stacks 0FPT, at the derived tensor product of
Stacks 08J8. -/
def derivedLeftUnitor (K : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj K ⟶ K :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
      (derivedTensorProductDatumOfSite X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))
      K).hom

/-- The left unit constraint `derivedLeftUnitor X K` is an isomorphism. -/
instance (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedLeftUnitor X K) :=
  inferInstanceAs (IsIso (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
      (derivedTensorProductDatumOfSite X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))
      K).hom)

/-- **The homothety map** `𝒪 ⟶ R𝓗om(K, K)` on a ringed site: the morphism corresponding to the
left unit constraint `𝒪 ⊗^L K ≅ K` under the tensor–Hom bijection of Stacks 08J8. -/
def derivedHomothety (K : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      ((derivedSheafHomBifunctor X).obj (op K)).obj K :=
  (derivedCurryHomEquiv X _ K K).symm (derivedLeftUnitor X K)

/-- The transpose of the homothety map is the left unit constraint. -/
theorem derivedCurryHomEquiv_derivedHomothety
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedCurryHomEquiv X ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) K K
      (derivedHomothety X K) = derivedLeftUnitor X K := by
  rw [derivedHomothety, AddEquiv.apply_symm_apply]

/-- **The homothety map differs from any morphism `𝒪 ⟶ R𝓗om(K, K)` with invertible transpose
by an automorphism of `R𝓗om(K, K)`**, the one induced by an automorphism of `K`. -/
theorem derivedHomothety_eq_comp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (s : ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
          ((derivedSheafHomBifunctor X).obj (op K)).obj K)
    (hs : IsIso (derivedCurryHomEquiv X _ K K s)) :
    derivedHomothety X K = s ≫ ((derivedSheafHomBifunctor X).obj (op K)).map
      (inv (derivedCurryHomEquiv X _ K K s) ≫ derivedLeftUnitor X K) := by
  apply (derivedCurryHomEquiv X _ K K).injective
  rw [derivedCurryHomEquiv_derivedHomothety, derivedCurryHomEquiv_naturality_target,
    IsIso.hom_inv_id_assoc]

/-- **The homothety map is invertible exactly when any morphism `𝒪 ⟶ R𝓗om(K, K)` with
invertible transpose is.** Both differ by the automorphism of `R𝓗om(K, K)` induced by an
automorphism of `K`. -/
theorem isIso_derivedHomothety_iff_of_isIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (s : ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      ((derivedSheafHomBifunctor X).obj (op K)).obj K)
    (hs : IsIso (derivedCurryHomEquiv X _ K K s)) :
    IsIso (derivedHomothety X K) ↔ IsIso s := by
  rw [derivedHomothety_eq_comp X K s hs]
  exact isIso_comp_right_iff s _

/-- The left unit constraint is natural. -/
theorem derivedLeftUnitor_naturality {K K' : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : K ⟶ K') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map a ≫
        derivedLeftUnitor X K' = derivedLeftUnitor X K ≫ a :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_naturality X
    (derivedTensorProductDatumOfSite X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)) a

/-- **The homothety map is natural for isomorphisms**: for `e : K ≅ K'` the homothety of `K'` is
that of `K` followed by `R𝓗om(e⁻¹, e)`. -/
theorem derivedHomothety_naturality {K K' : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ≅ K') :
    derivedHomothety X K' = derivedHomothety X K ≫
      (((derivedSheafHomBifunctor X).map e.inv.op).app K ≫
        ((derivedSheafHomBifunctor X).obj (op K')).map e.hom) := by
  apply (derivedCurryHomEquiv X ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) K' K').injective
  rw [derivedCurryHomEquiv_comp_map_of_id X
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) K K' K K' e.inv e.hom,
    derivedCurryHomEquiv_derivedHomothety, derivedCurryHomEquiv_derivedHomothety,
    ← Category.assoc, derivedLeftUnitor_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The homothety map of `K` is invertible exactly when that of an isomorphic object is. -/
theorem isIso_derivedHomothety_iff_of_iso
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ≅ K') :
    IsIso (derivedHomothety X K) ↔ IsIso (derivedHomothety X K') := by
  rw [derivedHomothety_naturality X e]
  exact (isIso_comp_right_iff _ _).symm

/-- **The homothety map on representatives.** Let `B` be a K-flat complex, `q : B ⟶ I` a
quasi-isomorphism into a K-injective complex, `f : 𝒪 ⟶ SheafHom(B, I)` a morphism of complexes
and `g : Tot(𝒪 ⊗ B) ⟶ I` a quasi-isomorphism corresponding to `f` under the currying
isomorphism of Stacks 0A90 on global sections. Then the homothety of `Q B` is invertible exactly
when `f` is a quasi-isomorphism. -/
theorem exists_derivedHomothety_Q_eq
    (B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] (q : B ⟶ I) [QuasiIso q]
    (hT : Stacks.SheafOfModules.IsKFlat X.O
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((HomologicalComplex.single (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B))
    (f : ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
          (sheafHomComplex X B I).obj)
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
        ((HomologicalComplex.single (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B ⟶ I)
    [QuasiIso g]
    (hfg : HomologicalComplex.homologyMap
        (globalSectionsComplexMap X (sheafHomTensorCurryIso X
            ((HomologicalComplex.single (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) B I).hom) 0
          (globalHomologyClass X ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                  (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (sheafHomComplex X B I).obj f) =
      globalHomologyClass X _ I g) :
    ∃ (a : ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅ DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (b : DerivedCategory.Q.obj (sheafHomComplex X B I).obj ≅
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj B)),
      derivedHomothety X (DerivedCategory.Q.obj B) = a.hom ≫ DerivedCategory.Q.map f ≫ b.hom := by
  have hg := derivedCurryHomEquiv_model X ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) B I
    (Stacks.SheafOfModules.isKFlat_single_unit X.O) hB hT f g hfg
  have hn := derivedCurryHomEquiv_comp_map X (DerivedCategory.Q.obj
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj I)
    (DerivedCategory.Q.obj B)
    ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
    (𝟙 (DerivedCategory.Q.obj B))
    (inv (DerivedCategory.Q.map q))
    (DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X B I).inv)
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 inferInstance
  let s := ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom ≫
        (DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X B I).inv) ≫
          ((derivedSheafHomBifunctor X).map (𝟙 (DerivedCategory.Q.obj B)).op).app _ ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).map
              (inv (DerivedCategory.Q.map q))
  have hs : IsIso (derivedCurryHomEquiv X _ (DerivedCategory.Q.obj B)
      (DerivedCategory.Q.obj B) s) := by
    simp only [s]; rw [hn, hg]; infer_instance
  refine ⟨(DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
          (derivedSheafHomComparison X B I).symm ≪≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).mapIso
        (asIso (inv (DerivedCategory.Q.map q))) ≪≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).mapIso
        (asIso (inv (derivedCurryHomEquiv X _ (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj B) s) ≫ derivedLeftUnitor X _)), ?_⟩
  rw [derivedHomothety_eq_comp X _ _ hs]
  simp only [s, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.assoc, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]

/-- The left unit constraint `Tot(𝒪[0] ⊗ B) ≅ B` of total tensor complexes. -/
def tensorComplexLeftUnitIso (B : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
        ((HomologicalComplex.single (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B ≅ B :=
  Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) B ≪≫
    Stacks.SheafOfModules.tensorComplexUnitIso X.O B

/-- **The homothety map on representatives, as a currying.** For a K-flat complex `B`, a
K-injective complex `I` and a quasi-isomorphism `g : Tot(𝒪[0] ⊗ B) ⟶ I`, the homothety map of
`Q B` is the class of the currying `𝒪[0] ⟶ SheafHom(B, I)` of `g`, up to isomorphisms of source
and target. -/
theorem exists_derivedHomothety_Q_eq_curryMap
    (B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective]
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B ⟶ I)
    [QuasiIso g] :
    ∃ (a : ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅ DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (b : DerivedCategory.Q.obj (sheafHomComplex X B I).obj ≅
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj B)),
      derivedHomothety X (DerivedCategory.Q.obj B) =
        a.hom ≫ DerivedCategory.Q.map (curryMap X g) ≫ b.hom := by
  have hT : Stacks.SheafOfModules.IsKFlat X.O
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((HomologicalComplex.single (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B) := fun F hF i =>
    (hB F hF i).of_iso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).mapIso
      (tensorComplexLeftUnitIso X B)).symm
  have hfg := homologyMap_globalHomologyClass_uncurryMap X (curryMap X g)
  rw [uncurryMap_curryMap] at hfg
  exact exists_derivedHomothety_Q_eq X B I hB ((tensorComplexLeftUnitIso X B).inv ≫ g) hT _ _ hfg

/-- **The homothety map on representatives.** For a K-flat complex `B`, a K-injective complex
`I` and a quasi-isomorphism `g : Tot(𝒪[0] ⊗ B) ⟶ I`, the homothety map of `Q B` is invertible
exactly when the currying `𝒪[0] ⟶ SheafHom(B, I)` of `g` is a quasi-isomorphism. -/
theorem isIso_derivedHomothety_Q_iff
    (B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective]
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj B ⟶ I)
    [QuasiIso g] :
    IsIso (derivedHomothety X (DerivedCategory.Q.obj B)) ↔ QuasiIso (curryMap X g) := by
  obtain ⟨a, b, hb⟩ := exists_derivedHomothety_Q_eq_curryMap X B I hB g
  rw [hb, isIso_comp_left_iff, isIso_comp_right_iff, DerivedCategory.isIso_Q_map_iff_quasiIso]

section Transport

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} Y.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- The bijection `Hom(K, L) ≅ Hom(F K, F L)` obtained by reading `Hom(K, L)` as
`Hom(𝒪, R𝓗om(K, L))`, applying `F` and reading back through `F 𝒪 ≅ 𝒪` and
`F R𝓗om(K, L) ≅ R𝓗om(F K, F L)`. -/
def derivedHomothetyTransportEquiv
    (F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hF : F.FullyFaithful) (K L : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ε : F.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (σ : F.obj (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj (op (F.obj K))).obj (F.obj L)) :
    (K ⟶ L) ≃ (F.obj K ⟶ F.obj L) :=
  ((asIso (derivedLeftUnitor X K)).symm.homCongr (Iso.refl L)).trans <|
    (derivedCurryHomEquiv X _ K L).symm.toEquiv.trans <| hF.homEquiv.trans <|
      (ε.homCongr σ).trans <| (derivedCurryHomEquiv Y _ (F.obj K) (F.obj L)).toEquiv.trans <|
        (asIso (derivedLeftUnitor Y (F.obj K))).homCongr (Iso.refl (F.obj L))

/-- `derivedHomothetyTransportEquiv` sends `g : K ⟶ L` to the composite of the inverse of the
left unit constraint of `F K` with the transpose under `derivedCurryHomEquiv` of
`ε.inv ≫ F.map h ≫ σ.hom`, where `h : 𝒪 ⟶ R𝓗om(K, L)` corresponds to the composite of the left
unit constraint of `K` with `g`. -/
lemma derivedHomothetyTransportEquiv_apply
    (F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hF : F.FullyFaithful) (K L : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ε : F.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (σ : F.obj (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj (op (F.obj K))).obj (F.obj L)) (g : K ⟶ L) :
    derivedHomothetyTransportEquiv X Y F hF K L ε σ g =
      inv (derivedLeftUnitor Y (F.obj K)) ≫ derivedCurryHomEquiv Y _ (F.obj K) (F.obj L)
        (ε.inv ≫ F.map ((derivedCurryHomEquiv X _ K L).symm (derivedLeftUnitor X K ≫ g)) ≫
          σ.hom) := by
  simp [derivedHomothetyTransportEquiv, Iso.homCongr_apply]

/-- **The homothety map is invariant under a fully faithful functor commuting with `𝒪` and
with `R𝓗om(K, -)`.** Let `F : D(𝒪_X) ⥤ D(𝒪_Y)` be fully faithful, `F 𝒪_X ≅ 𝒪_Y`, and
`F R𝓗om(K, L) ≅ R𝓗om(F K, F L)` natural in `L`. Then `F` of the homothety map of `K` is
invertible exactly when the homothety map of `F K` is. No compatibility of the given
isomorphisms with the tensor–Hom bijection is needed. -/
theorem isIso_map_derivedHomothety_iff
    (F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hF : F.FullyFaithful) (K : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ε : F.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (σ : ∀ L, F.obj (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj (op (F.obj K))).obj (F.obj L))
    (hσ : ∀ {L L' : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (a : L ⟶ L'),
      F.map (((derivedSheafHomBifunctor X).obj (op K)).map a) ≫ (σ L').hom =
        (σ L).hom ≫ ((derivedSheafHomBifunctor Y).obj (op (F.obj K))).map (F.map a)) :
    IsIso (F.map (derivedHomothety X K)) ↔ IsIso (derivedHomothety Y (F.obj K)) := by
  let T := fun L => derivedHomothetyTransportEquiv X Y F hF K L ε (σ L)
  -- naturality of `T` in the target
  have hT : ∀ {L L' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : K ⟶ L)
      (a : L ⟶ L'), T L' (g ≫ a) = T L g ≫ F.map a := by
    intro L L' g a
    have h1 := derivedCurryHomEquiv_symm_naturality_target X a (derivedLeftUnitor X K ≫ g)
    rw [Category.assoc] at h1
    simp only [T, derivedHomothetyTransportEquiv_apply, h1, Functor.map_comp, Category.assoc, hσ]
    rw [← derivedCurryHomEquiv_naturality_target]
    simp only [Category.assoc]
  obtain ⟨θ, hθ₀⟩ : ∃ θ : K ⟶ K, F.map θ = T K (𝟙 K) := ⟨_, hF.map_preimage _⟩
  have hθ : ∀ {L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : K ⟶ L),
      T L g = F.map (θ ≫ g) := by
    intro L g
    rw [Functor.map_comp, hθ₀, ← hT, Category.id_comp]
  have hθiso : IsIso θ := by
    obtain ⟨g, hg⟩ := (T K).surjective (F.map (𝟙 K))
    rw [hθ] at hg
    have h1 : θ ≫ g = 𝟙 K := hF.map_injective hg
    refine ⟨g, h1, ?_⟩
    apply (T K).injective
    rw [hθ, hθ, ← Category.assoc θ g θ, h1, Category.id_comp, Category.comp_id]
  have hmain : ε.inv ≫ F.map (derivedHomothety X K) ≫ (σ K).hom =
      derivedHomothety Y (F.obj K) ≫
        ((derivedSheafHomBifunctor Y).obj (op (F.obj K))).map (F.map θ) := by
    apply (derivedCurryHomEquiv Y _ (F.obj K) (F.obj K)).injective
    rw [derivedCurryHomEquiv_naturality_target, derivedCurryHomEquiv_derivedHomothety]
    have h2 := hθ (𝟙 K)
    simp only [T, derivedHomothetyTransportEquiv_apply, Category.comp_id] at h2
    rw [IsIso.inv_comp_eq] at h2
    convert h2 using 3
    rw [derivedHomothety]
  rw [← isIso_comp_right_iff (derivedHomothety Y (F.obj K))
    (((derivedSheafHomBifunctor Y).obj (op (F.obj K))).map (F.map θ)), ← hmain,
    isIso_comp_left_iff, isIso_comp_right_iff]

end Transport

end AlgebraicGeometry.RingedSite

end
