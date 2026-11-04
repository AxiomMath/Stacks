module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionSquareProof
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# Derived base change on cohomology

Let `ψ : R ⟶ A` be a homomorphism of rings with commutative underlying rings, `M` in `D(R)`, `N`
in `D(A)` and `r : M ⟶ Res N` a morphism into derived restriction of scalars, with adjoint
transpose `c : M ⊗^L_R A ⟶ N` under `- ⊗^L_R A ⊣ Res` (Stacks 0GMT).  On degree-`q` cohomology
`r` gives an `R`-linear map `H^q(M) ⟶ H^q(N)`, whose adjoint transpose is an `A`-linear map
`H^q(M) ⊗_R A ⟶ H^q(N)`.  This file factors that map as

`H^q(M) ⊗_R A ⟶ H^q(M ⊗^L_R A) ⟶ H^q(N)`,

the second map being `H^q(c)` and the first, `baseChangeHomologyComparison ψ M q`, depending on
`M` alone. So whenever the first map is invertible, as it is when `ψ` is flat, `c` is a
quasi-isomorphism exactly when every `H^q(M) ⊗_R A ⟶ H^q(N)` is bijective.

## Main definitions

* `baseChangeHomologyComparison`: the map `H^q(M) ⊗_R A ⟶ H^q(M ⊗^L_R A)`.

## Main results

* `homEquiv_symm_homology_eq`: the factorization displayed above.
* `isIso_homEquiv_symm_of_isIso_homology`: if the first map is invertible and every
  `H^q(M) ⊗_R A ⟶ H^q(N)` is, then `c` is an isomorphism.
* `isIso_baseChangeHomologyComparison_of_flat`: for flat `ψ` the first map is an isomorphism.

## References

* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.CartesianObjects (commRingOfComm)
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

universe r t

namespace Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits


section Exact

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  {E : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜} [E.Additive] [G.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- For an adjunction `E ⊣ G` of exact functors and a short complex `S`, the adjoint transpose
`E(H(S)) ⟶ H(S.map E)` of the homology of the unit, read through the comparison
`H((S.map E).map G) ≅ G(H(S.map E))`, is an isomorphism: it is the inverse comparison
`E(H(S)) ≅ H(S.map E)`, up to the comparison for the identity functor. -/
theorem isIso_homEquiv_symm_homologyMap_unit (adj : E ⊣ G) (S : ShortComplex 𝒜) :
    IsIso ((adj.homEquiv _ _).symm
      (ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫ ((S.map E).mapHomologyIso G).hom)) := by
  have h : ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫ ((S.map E).mapHomologyIso G).hom =
      (S.mapHomologyIso (𝟭 𝒜)).hom ≫ adj.unit.app S.homology ≫
        G.map (S.mapHomologyIso E).inv := by
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc]
    congr 2
    rw [Iso.inv_comp_eq, ← Stacks.Homology.mapHomologyIso_comp_hom E G S, Category.assoc,
      ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
  rw [h, Adjunction.homEquiv_naturality_left_symm]
  have e : (adj.homEquiv _ _).symm (adj.unit.app S.homology ≫ G.map (S.mapHomologyIso E).inv) =
      (S.mapHomologyIso E).inv := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality]
    simp
  rw [e]
  infer_instance

end Exact

/-- Naturality of `Stacks.Homology.derivedHomologyIso` in the object of the derived category. -/
private theorem homologyFunctor_map_comp_derivedHomologyIso_hom_app
    {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
    [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ] (E : 𝒜 ⥤ ℬ) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] {X Y : DerivedCategory 𝒜}
    (g : X ⟶ Y) (q : ℤ) :
    (DerivedCategory.homologyFunctor ℬ q).map (E.mapDerivedCategory.map g) ≫
        (Stacks.Homology.derivedHomologyIso E q).hom.app Y =
      (Stacks.Homology.derivedHomologyIso E q).hom.app X ≫
        E.map ((DerivedCategory.homologyFunctor 𝒜 q).map g) :=
  (Stacks.Homology.derivedHomologyIso E q).hom.naturality g

variable {R A : RingCat.{r}} (ψ : R ⟶ A) (hR : ∀ x y : R, x * y = y * x)
  (hA : ∀ x y : A, x * y = y * x)

/-- The extension–restriction adjunction of modules along `ψ`, at the module universe of
`dBaseChange`, for the commutative ring structures given by `hR` and `hA`. -/
abbrev moduleBaseChangeAdj :
    letI := commRingOfComm R hR
    letI := commRingOfComm A hA
    ModuleCat.extendScalars.{r, r, max t r} ψ.hom ⊣ ModuleCat.restrictScalars.{max t r} ψ.hom :=
  letI := commRingOfComm R hR
  letI := commRingOfComm A hA
  ModuleCat.extendRestrictScalarsAdj.{max t r} ψ.hom

/-- **The comparison `H^q(M) ⊗_R A ⟶ H^q(M ⊗^L_R A)`**: the adjoint transpose of the cohomology
of the unit `M ⟶ Res (M ⊗^L_R A)` of `- ⊗^L_R A ⊣ Res`. -/
def baseChangeHomologyComparison (M : DerivedCategory (ModuleCat.{max t r} R)) (q : ℤ) :
    letI := commRingOfComm R hR
    letI := commRingOfComm A hA
    (ModuleCat.extendScalars.{r, r, max t r} ψ.hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj M) ⟶
      (DerivedCategory.homologyFunctor _ q).obj ((dBaseChange.{r, t} ψ hR hA).obj M) :=
  ((moduleBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ q).map ((dBaseChangeAdj.{r, t} ψ hR hA).unit.app M) ≫
      (Stacks.Homology.derivedHomologyIso (ModuleCat.restrictScalars.{max t r} ψ.hom) q).hom.app
        ((dBaseChange.{r, t} ψ hR hA).obj M))

/-- **The cohomology of a derived base change map.** For `f : M ⟶ Res N`, the adjoint transpose
`H^q(M) ⊗_R A ⟶ H^q(N)` of `H^q(f)` is `baseChangeHomologyComparison` followed by `H^q` of the
adjoint transpose `M ⊗^L_R A ⟶ N` of `f`. -/
theorem homEquiv_symm_homology_eq (M : DerivedCategory (ModuleCat.{max t r} R))
    (N : DerivedCategory (ModuleCat.{max t r} A)) (f : M ⟶ (dRestrictScalars.{r, max t r} ψ).obj N)
    (q : ℤ) :
    ((moduleBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm
        ((DerivedCategory.homologyFunctor _ q).map f ≫
          (Stacks.Homology.derivedHomologyIso (ModuleCat.restrictScalars.{max t r} ψ.hom) q).hom.app
            N) =
      baseChangeHomologyComparison.{r, t} ψ hR hA M q ≫
        (DerivedCategory.homologyFunctor _ q).map
          (((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm f) := by
  have hf : f = (dBaseChangeAdj.{r, t} ψ hR hA).unit.app M ≫
      (dRestrictScalars.{r, max t r} ψ).map
        (((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm f) :=
    (((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv M N).apply_symm_apply f).symm.trans
      ((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv_unit M N _)
  conv_lhs => rw [hf]
  have hn := homologyFunctor_map_comp_derivedHomologyIso_hom_app
    (ModuleCat.restrictScalars.{max t r} ψ.hom)
    (((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm f) q
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **The criterion.** If `baseChangeHomologyComparison ψ M q` is invertible for every `q` (for
example because `ψ` is flat) and, for every `q`, the adjoint transpose `H^q(M) ⊗_R A ⟶ H^q(N)` of
`H^q(f)` is invertible, then the adjoint transpose `M ⊗^L_R A ⟶ N` of `f` is an isomorphism. -/
theorem isIso_homEquiv_symm_of_isIso_homology (M : DerivedCategory (ModuleCat.{max t r} R))
    (N : DerivedCategory (ModuleCat.{max t r} A)) (f : M ⟶ (dRestrictScalars.{r, max t r} ψ).obj N)
    (hM : ∀ q, IsIso (baseChangeHomologyComparison.{r, t} ψ hR hA M q))
    (hf : ∀ q, IsIso (((moduleBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm
        ((DerivedCategory.homologyFunctor _ q).map f ≫
          (Stacks.Homology.derivedHomologyIso (ModuleCat.restrictScalars.{max t r} ψ.hom) q).hom.app
            N))) :
    IsIso (((dBaseChangeAdj.{r, t} ψ hR hA).homEquiv _ _).symm f) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have := hf q
  rw [homEquiv_symm_homology_eq] at this
  exact IsIso.of_isIso_comp_left (baseChangeHomologyComparison.{r, t} ψ hR hA M q) _


/-- `baseChangeHomologyComparison` is natural in the object of `D(R)`. -/
theorem baseChangeHomologyComparison_naturality {M M' : DerivedCategory (ModuleCat.{max t r} R)}
    (e : M ⟶ M') (q : ℤ) :
    letI := commRingOfComm R hR
    letI := commRingOfComm A hA
    (ModuleCat.extendScalars.{r, r, max t r} ψ.hom).map
        ((DerivedCategory.homologyFunctor _ q).map e) ≫
        baseChangeHomologyComparison.{r, t} ψ hR hA M' q =
      baseChangeHomologyComparison.{r, t} ψ hR hA M q ≫
        (DerivedCategory.homologyFunctor _ q).map ((dBaseChange.{r, t} ψ hR hA).map e) := by
  let := commRingOfComm R hR
  let := commRingOfComm A hA
  simp only [baseChangeHomologyComparison]
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hη := (dBaseChangeAdj.{r, t} ψ hR hA).unit.naturality e
  have hd := homologyFunctor_map_comp_derivedHomologyIso_hom_app
    (ModuleCat.restrictScalars.{max t r} ψ.hom) ((dBaseChange.{r, t} ψ hR hA).map e) q
  simp only [Functor.comp_map, Functor.id_map] at hη
  rw [← Functor.map_comp_assoc, hη, Functor.map_comp_assoc, hd]
  rfl

/-- **Flat base change commutes with cohomology.** For a flat ring map `ψ`, the comparison
`H^q(M) ⊗_R A ⟶ H^q(M ⊗^L_R A)` is an isomorphism for every `M` in `D(R)` and every `q`. -/
theorem isIso_baseChangeHomologyComparison_of_flat
    (hψ : letI := commRingOfComm R hR; letI := commRingOfComm A hA; ψ.hom.Flat)
    (M : DerivedCategory (ModuleCat.{max t r} R)) (q : ℤ) :
    IsIso (baseChangeHomologyComparison.{r, t} ψ hR hA M q) := by
  let := commRingOfComm R hR
  let := commRingOfComm A hA
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{r, r, max t r} ψ.hom) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hψ
  have : PreservesFiniteColimits (ModuleCat.extendScalars.{r, r, max t r} ψ.hom) := by
    have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{r, r, max t r} ψ.hom) :=
      (moduleBaseChangeAdj.{r, t} ψ hR hA).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  suffices hQ : ∀ X : CochainComplex (ModuleCat.{max t r} R) ℤ,
      IsIso (baseChangeHomologyComparison.{r, t} ψ hR hA (DerivedCategory.Q.obj X) q) by
    have e := DerivedCategory.Q.objObjPreimageIso M
    have hn := baseChangeHomologyComparison_naturality.{r, t} ψ hR hA e.hom q
    have := hQ (DerivedCategory.Q.objPreimage M)
    have h2 : IsIso ((ModuleCat.extendScalars.{r, r, max t r} ψ.hom).map
        ((DerivedCategory.homologyFunctor _ q).map e.hom) ≫
        baseChangeHomologyComparison.{r, t} ψ hR hA M q) := by
      rw [hn]; infer_instance
    exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars.{r, r, max t r} ψ.hom).map
        ((DerivedCategory.homologyFunctor _ q).map e.hom)) _
  intro X
  have : (ModuleCat.extendScalars.{r, r, max t r} ψ.hom).Additive :=
    (moduleBaseChangeAdj.{r, t} ψ hR hA).left_adjoint_additive
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{r, r, t} ψ.hom
  let cmp : DerivedCategory.Q ⋙ T.functor ⟶
      (ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q := T.comparison
  have : Functor.IsLeftDerivedFunctor T.functor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{max t r} R) (ComplexShape.up ℤ)) :=
    T.isLeftDerived
  have hc : IsIso cmp := Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
      (Functor.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso _ _)
  have hu := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{r,
    r, t} ψ.hom T.functor cmp X
  let E := ModuleCat.extendScalars.{r, r, max t r} ψ.hom
  let G := ModuleCat.restrictScalars.{max t r} ψ.hom
  let adj₀ := moduleBaseChangeAdj.{r, t} ψ hR hA
  let c : (dBaseChange.{r, t} ψ hR hA).obj (DerivedCategory.Q.obj X) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) := cmp.app X
  have hcX : IsIso c := NatIso.isIso_app_of_isIso cmp X
  have key : baseChangeHomologyComparison.{r, t} ψ hR hA (DerivedCategory.Q.obj X) q ≫
      (DerivedCategory.homologyFunctor _ q).map c =
      E.map ((DerivedCategory.homologyFunctorFactors _ q).hom.app X) ≫
        (adj₀.homEquiv _ _).symm
          ((HomologicalComplex.homologyFunctor _ _ q).map
              ((adj₀.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫
            (Stacks.Homology.exactHomologyIso G q).hom.app ((E.mapHomologicalComplex _).obj X)) ≫
        (DerivedCategory.homologyFunctorFactors _ q).inv.app
          ((E.mapHomologicalComplex _).obj X) := by
    simp only [baseChangeHomologyComparison]
    rw [← Adjunction.homEquiv_naturality_right_symm]
    conv_rhs => rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm]
    congr 1
    have hd := homologyFunctor_map_comp_derivedHomologyIso_hom_app G c q
    have hf := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max t r} R) q).hom.naturality
      ((adj₀.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X)
    have hQ := Stacks.Cohomology.HypercohomologyEdge.derivedHomologyIso_hom_app_Q G q
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
    simp only [Functor.comp_map] at hf
    have hu' : (dBaseChangeAdj.{r, t} ψ hR hA).unit.app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategory.map c =
        DerivedCategory.Q.map ((adj₀.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫
          G.mapDerivedCategoryFactors.inv.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
      hu
    show ((DerivedCategory.homologyFunctor _ q).map
          ((dBaseChangeAdj.{r, t} ψ hR hA).unit.app (DerivedCategory.Q.obj X)) ≫
        (Stacks.Homology.derivedHomologyIso G q).hom.app
          ((dBaseChange.{r, t} ψ hR hA).obj (DerivedCategory.Q.obj X))) ≫
        G.map ((DerivedCategory.homologyFunctor _ q).map c) = _
    rw [Category.assoc, ← hd, ← Functor.map_comp_assoc, hu', hQ, Functor.map_comp_assoc,
      ← (DerivedCategory.homologyFunctor _ q).map_comp_assoc
        (G.mapDerivedCategoryFactors.inv.app _), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hf]
    simp only [Category.assoc]
    rfl
  have hZ : IsIso ((adj₀.homEquiv _ _).symm
      ((HomologicalComplex.homologyFunctor _ _ q).map
          ((adj₀.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫
        (Stacks.Homology.exactHomologyIso G q).hom.app ((E.mapHomologicalComplex _).obj X))) :=
    isIso_homEquiv_symm_homologyMap_unit adj₀ (X.sc q)
  have h2 : IsIso (baseChangeHomologyComparison.{r, t} ψ hR hA (DerivedCategory.Q.obj X) q ≫
      (DerivedCategory.homologyFunctor _ q).map c) := by
    rw [key]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hZ inferInstance)
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor _ q).map c)

end Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange
