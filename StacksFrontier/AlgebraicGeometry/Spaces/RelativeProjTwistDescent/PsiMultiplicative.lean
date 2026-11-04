module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescended
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraUnit
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegMultiplicative
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleFromPair
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap

/-!
# `ψ` of Stacks 084D on the scheme of a base change is multiplicative

In Situation 0849 let `V ×_X P` be the base change of the relative Proj `P = Proj_X(𝒜)` to a
scheme point `v : V ⟶ X`, whose scheme is `Proj_V(v^*𝒜)`.  The map `ψ` of Stacks 01NR at that
point, in its adjoint form `π_V^*(v^*𝒜)_n ⟶ 𝒪(n)`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHom`), is the comparison of the
inverse images along `V ×_X P ⟶ Proj_V(v^*𝒜) ⟶ V` followed by the inverse image of the transpose
of the homogeneous-section map, and that transpose is a homomorphism of sheaves of graded algebras.
This file records the resulting compatibility of `ψ` with the multiplications, read through the
comparison of Stacks 01CD (03EL on schemes), at free variables: it is the scheme-level input of the
statement of Stacks 084D that `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` is a homomorphism of graded
algebras.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposePullbackHom`: the transpose of
  the homogeneous-section map of Stacks 01NR, as a homomorphism out of the inverse image
  `Stacks.RingedSpace.pullbackGradedAlgebra` of the graded algebra.

## Main results

* `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_hom`: a composite of
  comparisons of inverse images along `fh = k ≫ h` and of the inverse image of a homomorphism of
  sheaves of graded algebras carries the pulled-back multiplication to the multiplication.
* `AlgebraicGeometry.Space.pullbackTensorIso_inv_comp_map_mulSheaf_comp_psi`: **the transpose of
  Tag 01NR's `ψ`, read on a scheme through `fh = k ≫ π`, carries the pulled-back multiplication of
  `𝒜` to the multiplication of the twists**; at `k` the identification of the scheme of
  `V ×_X P` with `Proj_V(v^*𝒜)` its components are
  `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHom`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (situationAlgebra)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData

variable {S : Scheme.{u}} {A : RelativeProjBridge.SheafGradedAlgebra.{u} S} (D : TwistData A)

/-- The multiplication of the inverse image `Stacks.RingedSpace.pullbackGradedAlgebra` along the
structure morphism is that of the monoidal pullback
`Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra`: both are the inverse comparison of Stacks
01CD followed by the pullback of the multiplication of `𝒜`. -/
theorem mulSheaf_pullbackGradedAlgebra_toBase (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (Stacks.RingedSpace.pullbackGradedAlgebra
        (relativeProj A).toBase.toLRSHom.toShHom (situationAlgebra A)) i j =
      SheafOfModules.GradedAlgebra.mulSheaf (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (RelativeProjQcohSheaf.ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
        (RelativeProjQcohSheaf.isSheafStruct S)) i j :=
  (Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra _ (situationAlgebra A) i j).trans
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra
      (relativeProj A).toBase (situationAlgebra A) i j).symm

/-- **The transpose of the homogeneous-section map of Stacks 01NR, as a homomorphism of sheaves
of graded algebras out of `Stacks.RingedSpace.pullbackGradedAlgebra`**: its components are
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTranspose`, and it preserves products
of homogeneous local sections because the two inverse images have the same multiplication
(`…TwistData.mulSheaf_pullbackGradedAlgebra_toBase`). -/
def psiTransposePullbackHom :
    Stacks.RingedSpace.pullbackGradedAlgebra (relativeProj A).toBase.toLRSHom.toShHom
        (situationAlgebra A) ⟶ D.algebra where
  app := D.psiTranspose
  map_mul i j U x y := by
    have hm : ((Stacks.RingedSpace.pullbackGradedAlgebra (relativeProj A).toBase.toLRSHom.toShHom
          (situationAlgebra A)).mul i j).app U x y =
        ((Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
          (RelativeProjQcohSheaf.ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
          (RelativeProjQcohSheaf.isSheafStruct S)).mul i j).app U x y :=
      ((SheafOfModules.GradedAlgebra.mulSheaf_unit
          (Stacks.RingedSpace.pullbackGradedAlgebra (relativeProj A).toBase.toLRSHom.toShHom
            (situationAlgebra A)) i j U x y).symm.trans (by
          rw [mulSheaf_pullbackGradedAlgebra_toBase]
          rfl)).trans
        (SheafOfModules.GradedAlgebra.mulSheaf_unit
          (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
            (RelativeProjQcohSheaf.ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
            (RelativeProjQcohSheaf.isSheafStruct S)) i j U x y)
    rw [hm]
    exact D.psiTranspose_map_mul i j U x y

end Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData

namespace AlgebraicGeometry.Space

/-- Three images of a functor followed by a morphism are the image of the composite followed by
it; stated on variables, so that it applies up to definitional equality of the spellings. -/
private theorem map_comp_map_comp_map_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₁ X₂ X₃ X₄ : C} {Y : D} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (m : F.obj X₄ ⟶ Y) :
    F.map a ≫ F.map b ≫ F.map c ≫ m = F.map (a ≫ b ≫ c) ≫ m := by
  simp only [Functor.map_comp, Category.assoc]

/-- **A composite of comparisons of inverse images and of the inverse image of a homomorphism of
sheaves of graded algebras carries the pulled-back multiplication to the multiplication**: for
`fh = k ≫ h` and a homomorphism `φ : h^*G ⟶ D` of sheaves of graded algebras, the family
`fh^*G_n ≅ k^*h^*G_n ⟶ k^*D_n` carries the multiplication of `G`, pulled back along `fh` and read
through the comparison of Stacks 01CD, to the multiplication of `k^*D`. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_hom {W P' S' : Scheme.{u}}
    (fh : W ⟶ S') (k : W ⟶ P') (h : P' ⟶ S') (e : fh = k ≫ h)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf S'.toRingedSpace))
    (D' : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra P')
    (φ : Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS h G ⟶ D')
    (ψ' : ∀ n, (Scheme.Modules.pullback fh).obj (G.piece n) ⟶
      (Scheme.Modules.pullback k).obj (D'.piece n))
    (hψ' : ψ' = fun n => (Scheme.Modules.pullbackCongr e).hom.app (G.piece n) ≫
      (Scheme.Modules.pullbackComp k h).inv.app (G.piece n) ≫
        (Scheme.Modules.pullback k).map (φ.app n)) (i j : ℤ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso fh (G.piece i) (G.piece j)).inv ≫
        (Scheme.Modules.pullback fh).map (SheafOfModules.GradedAlgebra.mulSheaf G i j) ≫
        ψ' (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((ψ' i, ψ' j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k D') i j := by
  subst hψ'
  subst e
  have h0 := Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra (k ≫ h).toLRSHom.toShHom G i j
  have h1 := mulSheaf_comp_tensorSheafMap_of_hom
    (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G
      (rfl : k ≫ h = k ≫ h)).hom i j
  have h2 := mulSheaf_comp_tensorSheafMap_of_hom
    (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G k h).inv i j
  have h3 := mulSheaf_comp_tensorSheafMap_of_hom
    (Stacks.RingedSpace.pullbackGradedAlgebraMap k.toLRSHom.toShHom φ) i j
  have k1 : (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (k ≫ h) (G.piece i)
      (G.piece j)).inv ≫
        (Scheme.Modules.pullback (k ≫ h)).map (SheafOfModules.GradedAlgebra.mulSheaf G i j) =
      SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS (k ≫ h) G) i j := by
    rw [h0]
    rfl
  beta_reduce
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _) k1)).trans ?_
  refine ((reassoc_of% h1) _).trans ?_
  refine (congrArg (fun z => _ ≫ z) ((reassoc_of% h2) _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z) h3).trans ?_
  refine (map_comp_map_comp_map_comp_eq _ _ _ _ _).trans ?_
  rfl

/-- **The transpose of Tag 01NR's `ψ`, read on a scheme `W` through `fh = k ≫ π`, carries the
pulled-back multiplication to the multiplication of the twists**: for a quasi-coherent graded
algebra `𝒜` on `S'`, twists `D` of `Proj_{S'}(𝒜)`, `k : W ⟶ Proj_{S'}(𝒜)` and `fh = k ≫ π`, the
family `fh^*𝒜_n ≅ k^*π^*𝒜_n ⟶ k^*𝒪(n)` (`n ≥ 0`) of transposes of `ψ` carries the multiplication of
`𝒜`, pulled back along `fh` and read through Stacks 01CD, to the multiplication of `k^*⨁ 𝒪(n)`. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_psi {S' W : Scheme.{u}}
    {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.{u} S'}
    (D : Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData A) (fh : W ⟶ S')
    (k : W ⟶ (relativeProj A).scheme) (e : fh = k ≫ (relativeProj A).toBase)
    (χ : ∀ n : ℕ, (Scheme.Modules.pullback fh).obj (A.piece (n : ℤ)) ⟶
      (Scheme.Modules.pullback k).obj (D.algebra.piece (n : ℤ)))
    (hχ : ∀ n, χ n = (Scheme.Modules.pullbackCongr e).hom.app _ ≫
      (Scheme.Modules.pullbackComp k (relativeProj A).toBase).inv.app _ ≫
      (Scheme.Modules.pullback k).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
          (D.ψ n))) (i j : ℕ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso fh (A.piece (i : ℤ))
        (A.piece (j : ℤ))).inv ≫
        (Scheme.Modules.pullback fh).map
          (SheafOfModules.GradedAlgebra.mulSheaf (situationAlgebra A) (i : ℤ) (j : ℤ)) ≫
        χ (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((χ i, χ j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS k D.algebra)
          (i : ℤ) (j : ℤ) := by
  obtain rfl : χ = _ := funext hχ
  exact pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_hom fh k (relativeProj A).toBase e
    (situationAlgebra A) D.algebra D.psiTransposePullbackHom _ rfl (i : ℤ) (j : ℤ)

/-- **Tag 01NR's `ψ` in adjoint form along a factorization carries the pulled-back multiplication
to the multiplication of the twists**: for `f = ι ≫ π`, the morphisms
`AlgebraicGeometry.Space.pullbackAdjointPsi A ι f hf n : f^*A_n ⟶ ι^*𝒪(n)` carry the multiplication
of `A`, pulled back along `f` and read through Stacks 01CD, to the multiplication of
`ι^*⨁ 𝒪(n)`. -/
theorem pullbackTensorIso_inv_comp_pullbackAdjointPsi {X Y : Scheme.{u}}
    (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.{u} Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase)
    (i j : ℕ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f (A.piece (i : ℤ))
        (A.piece (j : ℤ))).inv ≫
        (Scheme.Modules.pullback f).map
          (SheafOfModules.GradedAlgebra.mulSheaf (situationAlgebra A) (i : ℤ) (j : ℤ)) ≫
        pullbackAdjointPsi A ι f hf (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((pullbackAdjointPsi A ι f hf i, pullbackAdjointPsi A ι f hf j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS ι
            (Tag07ZGTwist.twistAlgebra A))
          (i : ℤ) (j : ℤ) :=
  pullbackTensorIso_inv_comp_map_mulSheaf_comp_psi (GluedTwistAlgebra.twistDataOfGradedAlgebra A)
    f ι hf (pullbackAdjointPsi A ι f hf) (fun _ => rfl) i j

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **`ψ` on the scheme of `V ×_X P` carries the pulled-back multiplication of `v^*𝒜` to the
multiplication of the twists** (the scheme-level input of Stacks 084D): the inverse comparison of
Stacks 01CD, followed by the pullback along `V ×_X P ⟶ V` of the multiplication of `v^*𝒜` and by
`ψ_{i+j}` (`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`, which is
`AlgebraicGeometry.Space.pullbackAdjointPsi` at the point `v` by definition), is `ψ_i ⊗ ψ_j`
followed by the multiplication `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of the twists on `V ×_X P`. -/
theorem pullbackTensorIso_inv_comp_psiChartSchemeHomOfAdjoint
    (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1) (i j : ℕ) :
    type_of% (pullbackTensorIso_inv_comp_pullbackAdjointPsi (s.shrink.pointAlgebra V v)
      (s.toRelativeProj V v) (s.fibreToBase V v) (s.fibreToBase_eq V v) i j) :=
  pullbackTensorIso_inv_comp_pullbackAdjointPsi (s.shrink.pointAlgebra V v) (s.toRelativeProj V v)
    (s.fibreToBase V v) (s.fibreToBase_eq V v) i j

end RelativeProjSituation

end AlgebraicGeometry.Space

end
