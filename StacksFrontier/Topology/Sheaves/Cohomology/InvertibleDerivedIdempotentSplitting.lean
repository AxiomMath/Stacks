module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotents
public import StacksFrontier.Homology.DerivedCategory.IdempotentSplitting

/-!
# Splitting an object of `D(𝒪_X)` along global idempotents

Let `(X, 𝒪_X)` be a ringed space, `K` a complex of `𝒪_X`-modules and `(e_n)_{n ∈ ℤ}` a family of
orthogonal idempotents of `Γ(X, 𝒪_X)` such that `e_n` acts on the cohomology sheaf `H^k(K)` as the
identity when `k = n` and as zero otherwise. Then `K ≅ ⨁_n H^n(K)[-n]` in `D(𝒪_X)`. If moreover the
family is locally finite and complete, and each `H^n(K)` is invertible over the factor `e_n 𝒪_X`,
then `K` satisfies clause (2) of Stacks 0FPG.

## Main results

* `Stacks.Cohomology.InvertibleDerived.smulHom`: multiplication by a global section of `𝒪_X`.
* `Stacks.Cohomology.InvertibleDerived.nonempty_Q_obj_iso_sigma_single`: the splitting
  `K ≅ ⨁_n H^n(K)[-n]`.
* `Stacks.Cohomology.InvertibleDerived.hasInvertibleModuleDecomposition_of_idempotents`: clause (2)
  of Stacks 0FPG from such a family of idempotents.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-! ### Multiplication by a global section -/

section SMul

variable (s : X.presheaf.obj (op ⊤))

/-- Multiplication by the restriction of a global section `s` to `U` commutes with the action of
`𝒪_X(U)` on sections of an `𝒪_X`-module. -/
public theorem smul_smul_comm (U : (Opens X.carrier)ᵒᵖ) {F : Mod X.sheaf}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) (m : F.val.obj U) :
    ringSec (U := U) (globalRes s U.unop) • (r • m) =
      r • ringSec (U := U) (globalRes s U.unop) • m :=
  (mul_smul (ringSec (U := U) (globalRes s U.unop)) r m).symm.trans
    ((congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U => a • m)
      (mul_comm (G := ↑(X.presheaf.obj U)) (globalRes s U.unop) r)).trans
      (mul_smul r (ringSec (U := U) (globalRes s U.unop)) m))

/-- **Multiplication by a global section** `s` of `𝒪_X`, as an endomorphism of an `𝒪_X`-module. -/
public def smulHom (F : Mod X.sheaf) : F ⟶ F :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun m => ringSec (U := U) (globalRes s U.unop) • m
          map_add' := fun m m' => smul_add _ m m'
          map_smul' := fun r m => smul_smul_comm s U r m }
     naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun m =>
        ((F.val.map_smul f (ringSec (U := U) (globalRes s U.unop)) m).trans
          (congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj V =>
            a • F.val.map f m) (map_globalRes s f))).symm) }⟩

/-- On sections over `U`, `smulHom s F` is multiplication by the restriction of `s` to `U`. -/
public theorem smulHom_app (F : Mod X.sheaf) (U : (Opens X.carrier)ᵒᵖ) (m : F.val.obj U) :
    (smulHom s F).val.app U m = ringSec (U := U) (globalRes s U.unop) • m := rfl

/-- Multiplication by a global section commutes with every morphism of `𝒪_X`-modules. -/
@[reassoc]
public theorem smulHom_naturality {F G : Mod X.sheaf} (φ : F ⟶ G) :
    φ ≫ smulHom s G = smulHom s F ≫ φ := by
  ext U m
  exact ((φ.val.app U).hom.map_smul _ m).symm

/-- Multiplying by `s` and then by `t` is multiplying by `t * s`. -/
public theorem smulHom_comp (t : X.presheaf.obj (op ⊤)) (F : Mod X.sheaf) :
    smulHom s F ≫ smulHom t F = smulHom (t * s) F := by
  ext U m
  exact ((mul_smul (ringSec (U := U) (globalRes t U.unop)) (ringSec (U := U) (globalRes s U.unop))
    m).symm.trans
    (congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U => a • m)
      (globalRes_mul t s U.unop).symm))

/-- Multiplication by a global section, as an endomorphism of the identity functor of the
category of `𝒪_X`-modules. -/
public def smulNatTrans : 𝟭 (Mod X.sheaf) ⟶ 𝟭 (Mod X.sheaf) where
  app F := smulHom s F
  naturality _ _ φ := smulHom_naturality s φ

/-- The component of `smulNatTrans s` at `F` is `smulHom s F`. -/
public theorem smulNatTrans_app (F : Mod X.sheaf) : (smulNatTrans s).app F = smulHom s F := rfl

/-- Multiplication by `s` followed by multiplication by `t` is multiplication by `t * s`, as
endomorphisms of the identity functor. -/
public theorem smulNatTrans_comp (t : X.presheaf.obj (op ⊤)) :
    smulNatTrans s ≫ smulNatTrans t = smulNatTrans (t * s) :=
  NatTrans.ext (funext fun F => smulHom_comp s t F)

end SMul

/-! ### Clause (2) of Stacks 0FPG from global idempotents -/

section Decomposition

variable (L : LocallyFiniteIdempotents X) {K : CochainComplex (Mod X.sheaf) ℤ}

/-- Multiplication by the idempotent `e_n` is an idempotent endomorphism of the identity
functor. -/
public theorem smulNatTrans_idem (n : ℤ) :
    smulNatTrans (L.e n) ≫ smulNatTrans (L.e n) = smulNatTrans (L.e n) := by
  rw [smulNatTrans_comp, (L.idem n).eq]

variable {L} (hK : ActsOnHomology (fun n => smulNatTrans (L.e n)) K)

include hK in
/-- `e_n` acts as the identity on `H^n(K)`. -/
public theorem actsAsOne_homology (n : ℤ) : L.ActsAsOne n (K.homology n) := by
  intro U m
  have h := hK n n
  rw [if_pos rfl, smulNatTrans_app] at h
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.val.app U) h) m

/-- **Clause (2) of Stacks 0FPG from global idempotents.** Let `(e_n)` be a locally finite
complete family of orthogonal idempotents of `Γ(X, 𝒪_X)` such that `e_n` acts on `H^k(K)` as the
identity for `k = n` and as zero otherwise, and such that each `H^n(K)` is an invertible module
over the factor `e_n 𝒪_X`. Then `K` admits the decomposition of clause (2) of Stacks 0FPG, with
`𝒪_n = e_n 𝒪_X` and `ℋ^n = H^n(K)`. -/
public theorem hasInvertibleModuleDecomposition_of_idempotents
    [HasDerivedCategory.{d} (Mod X.sheaf)]
    (hinv : ∀ n, Stacks.SheafOfModules.Tensor.IsInvertibleModule (L.factor n)
      (LocallyFiniteIdempotents.factorModule (actsAsOne_homology hK n))) :
    HasInvertibleModuleDecomposition X (DerivedCategory.Q.obj K) := by
  let _i1 : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let _i2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := Mod X.sheaf)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts _ _
  let _i3 : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.sheaf)) :=
    preservesColimitsOfShape_discrete_shrink.{u} _ _
  let _i4 : HasExactColimitsOfShape (Discrete (ULift.{u} ℤ)) (Mod X.sheaf) := inferInstance
  let _i5 : HasExactColimitsOfShape (Discrete ℤ) (Mod X.sheaf) :=
    HasExactColimitsOfShape.of_domain_equivalence _ (Discrete.equivalence Equiv.ulift)
  obtain ⟨e⟩ := nonempty_Q_obj_iso_sigma_single (smulNatTrans_idem L) hK
  exact ⟨L.productDecomposition, fun n => LocallyFiniteIdempotents.factorModule
      (actsAsOne_homology hK n), hinv,
    ⟨e ≪≫ Sigma.mapIso fun n => (DerivedCategory.singleFunctor _ n).mapIso
      (LocallyFiniteIdempotents.toOXModFactorModuleIso (actsAsOne_homology hK n)).symm⟩⟩

end Decomposition

end Stacks.Cohomology.InvertibleDerived

end
