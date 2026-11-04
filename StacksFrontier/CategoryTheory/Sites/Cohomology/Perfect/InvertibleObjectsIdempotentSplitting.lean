module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsIdempotents
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting

/-!
# Splitting an object of `D(O)` along global idempotents of a ringed site

Let `(C, O)` be a ringed site, `K` a complex of `O`-modules and `(e_n)_{n ∈ ℤ}` a locally finite
complete family of orthogonal idempotents of `Γ(C, O)` such that `e_n` acts on the cohomology
sheaf `H^k(K)` as the identity when `k = n` and as zero otherwise. If each `H^n(K)` is invertible
over the factor `e_n O`, then `K` satisfies clause (2) of Stacks 0FPY, with `O_n = e_n O` and
`ℋ^n = H^n(K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.smulHom`: multiplication by a global section of
  `O`, as an endomorphism of an `O`-module.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.smulNatTrans`: the same, as an endomorphism of
  the identity functor of the category of `O`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.hasInvertibleModuleDecomposition_of_idempotents`:
  clause (2) of Stacks 0FPY from such a family of idempotents.

## Implementation notes

The splitting `K ≅ ⨁_n H^n(K)[-n]` itself is the category-theoretic
`Stacks.Cohomology.InvertibleDerived.nonempty_Q_obj_iso_sigma_single`, which only needs the
idempotents as endomorphisms of the identity functor of an abelian category with exact countable
coproducts.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

open Stacks.Cohomology.InvertibleDerived (ActsOnHomology nonempty_Q_obj_iso_sigma_single)

variable {X : RingedSite.{u, u, u}}

/-! ### Multiplication by a global section -/

section SMul

variable (s : GlobalSection X)

/-- Multiplication by a global section `s` of `O` commutes with the action of every local section
of `O` on an `O`-module. -/
theorem smul_smul_comm (U : X.Cᵒᵖ) {F : Mod X.O}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (m : F.val.obj U) :
    ringSec (s.val U) • (r • m) = r • ringSec (s.val U) • m :=
  (mul_smul (ringSec (s.val U)) r m).symm.trans
    ((congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U => a • m)
      (mul_comm (G := (X.O.obj.obj U : Type u)) (s.val U) r)).trans
      (mul_smul r (ringSec (s.val U)) m))

/-- **Multiplication by a global section** `s` of `O`, as an endomorphism of an `O`-module. -/
def smulHom (F : Mod X.O) : F ⟶ F :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun m => ringSec (s.val U) • m
          map_add' := fun m m' => smul_add _ m m'
          map_smul' := fun r m => smul_smul_comm s U r m }
     naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun m =>
        ((F.val.map_smul f (ringSec (s.val U)) m).trans
          (congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V =>
            a • F.val.map f m) (s.map_val f))).symm) }⟩

/-- On sections over `U`, `smulHom s F` is multiplication by the restriction of `s` to `U`. -/
theorem smulHom_app (F : Mod X.O) (U : X.Cᵒᵖ) (m : F.val.obj U) :
    (smulHom s F).val.app U m = ringSec (s.val U) • m := rfl

/-- Multiplication by a global section commutes with every morphism of `O`-modules. -/
@[reassoc]
theorem smulHom_naturality {F G : Mod X.O} (φ : F ⟶ G) :
    φ ≫ smulHom s G = smulHom s F ≫ φ := by
  ext U m
  exact ((φ.val.app U).hom.map_smul _ m).symm

/-- Multiplication by `s` followed by multiplication by `t` is multiplication by `t * s`. -/
theorem smulHom_comp (t : GlobalSection X) (F : Mod X.O) :
    smulHom s F ≫ smulHom t F = smulHom (t * s) F := by
  ext U m
  exact (mul_smul (ringSec (t.val U)) (ringSec (s.val U)) m).symm

/-- Multiplication by a global section, as an endomorphism of the identity functor of the
category of `O`-modules. -/
def smulNatTrans : 𝟭 (Mod X.O) ⟶ 𝟭 (Mod X.O) where
  app F := smulHom s F
  naturality _ _ φ := smulHom_naturality s φ

/-- The component of `smulNatTrans s` at `F` is `smulHom s F`. -/
theorem smulNatTrans_app (F : Mod X.O) : (smulNatTrans s).app F = smulHom s F := rfl

/-- Composing `smulNatTrans s` with `smulNatTrans t` gives `smulNatTrans (t * s)`. -/
theorem smulNatTrans_comp (t : GlobalSection X) :
    smulNatTrans s ≫ smulNatTrans t = smulNatTrans (t * s) :=
  NatTrans.ext (funext fun F => smulHom_comp s t F)

end SMul

/-! ### Clause (2) of Stacks 0FPY from global idempotents -/

section Decomposition

variable (E : LocallyFiniteIdempotents X) {K : CochainComplex (Mod X.O) ℤ}

/-- Multiplication by the idempotent `e_n` is an idempotent endomorphism of the identity functor
of the category of `O`-modules. -/
theorem smulNatTrans_idem (n : ℤ) :
    smulNatTrans (E.e n) ≫ smulNatTrans (E.e n) = smulNatTrans (E.e n) := by
  rw [smulNatTrans_comp]
  congr 1
  exact GlobalSection.ext fun U => (E.idem n U).eq

variable {E} (hK : ActsOnHomology (fun n => smulNatTrans (E.e n)) K)

include hK in
/-- `e_n` acts as the identity on `H^n(K)`. -/
theorem actsAsOne_homology (n : ℤ) : E.ActsAsOne n (K.homology n) := by
  intro U m
  have h := hK n n
  rw [if_pos rfl, smulNatTrans_app] at h
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.val.app U) h) m

/-- **Clause (2) of Stacks 0FPY from global idempotents.** Let `(e_n)` be a locally finite
complete family of orthogonal idempotents of `Γ(C, O)` such that `e_n` acts on `H^k(K)` as the
identity for `k = n` and as zero otherwise, and such that each `H^n(K)` is an invertible module
over the factor `e_n O`. Then `K` admits the decomposition of clause (2) of Stacks 0FPY, with
`O_n = e_n O` and `ℋ^n = H^n(K)`. -/
theorem hasInvertibleModuleDecomposition_of_idempotents
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (hinv : ∀ n, Stacks.SheafOfModules.Tensor.IsInvertibleModule (E.factor n)
      (LocallyFiniteIdempotents.factorModule (actsAsOne_homology hK n))) :
    HasInvertibleModuleDecomposition X (DerivedCategory.Q.obj K) := by
  let _i1 : HasCoproducts.{u} (DerivedCategory (Mod X.O)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let _i2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := Mod X.O)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts _ _
  let _i3 : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.O)) :=
    preservesColimitsOfShape_discrete_shrink.{u} _ _
  let _i4 : HasExactColimitsOfShape (Discrete (ULift.{u} ℤ)) (Mod X.O) := inferInstance
  let _i5 : HasExactColimitsOfShape (Discrete ℤ) (Mod X.O) :=
    HasExactColimitsOfShape.of_domain_equivalence _ (Discrete.equivalence Equiv.ulift)
  obtain ⟨e⟩ := nonempty_Q_obj_iso_sigma_single (smulNatTrans_idem E) hK
  obtain ⟨e'⟩ := iso_coproduct_zeroDifferentialComplex X E.productDecomposition
    (fun n => LocallyFiniteIdempotents.factorModule (actsAsOne_homology hK n))
  exact ⟨E.productDecomposition, fun n => LocallyFiniteIdempotents.factorModule
      (actsAsOne_homology hK n), hinv,
    ⟨e ≪≫ (Sigma.mapIso fun n => (DerivedCategory.singleFunctor _ n).mapIso
      (LocallyFiniteIdempotents.toOModFactorModuleIso (actsAsOne_homology hK n)).symm) ≪≫ e'⟩⟩

end Decomposition

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
