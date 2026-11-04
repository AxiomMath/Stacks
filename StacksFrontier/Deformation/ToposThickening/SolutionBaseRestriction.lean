module

public import StacksFrontier.Deformation.ToposThickening.ObstructionBaseClassCoefficient

/-!
# Restricting a solution along a map of base thickenings

Let `S` and `T` be square-zero extension problems of ringed topoi (Tag 08UF) over the same
morphism `f : X ⟶ B`, with thickened bases `O_{B'_S}` and `O_{B'_T}`. Take a map
`φ : O_{B'_S} ⟶ O_{B'_T}` over `O_B`, a map of ideals `ι : f⁻¹J_S ⟶ f⁻¹J_T` compatible with
`f⁻¹φ`, and a map of target modules `k : G_S ⟶ G_T` with `c_T ∘ ι = k ∘ c_S`. A solution `O'` of
`T` is a square-zero extension of `O` by `G_T` over `f⁻¹O_{B'_T}`. Read over `f⁻¹O_{B'_S}` through
`f⁻¹φ`, it is a solution of `S.mapTarget k`, the problem `S` with target `G_T` and prescribed map
`c_S ≫ k`.

## Main definitions

* `RingedToposExtensionProblem.CompatibleFirstOrderThickening.restrictBase`:
  the restricted solution.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

namespace CompatibleFirstOrderThickening

variable {S T : RingedToposExtensionProblem X B} (hf : S.f = T.f)

include hf in
/-- **A solution of `T`, read over the thickened base of `S`**, is a solution of
`S.mapTarget k`. The data are:

* `φ : O_{B'_S} ⟶ O_{B'_T}` over `O_B`;
* a map of ideals `ι` compatible with `f⁻¹φ`;
* `k : G_S ⟶ G_T` with `c_T ∘ ι = k ∘ c_S`.

The extension, its reduction and its kernel are those of the solution of `T`. The base map is
`f⁻¹φ` followed by that of the solution. -/
public def restrictBase (φ : S.baseExtension ⟶ T.baseExtension)
    (hφ : φ ≫ T.baseReduction = S.baseReduction)
    (k : S.G ⟶ T.G) (ι : ∀ U : X.Cᵒᵖ, S.I.val.obj U → T.I.val.obj U)
    (hι : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
      ((inverseImageCommRingFunctor S.f.toToposHom).map φ).hom.app U
          (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
            S.idealInclusion.val.app U a) =
        hf ▸ (show ((inverseImageCommRingFunctor T.f.toToposHom).obj T.baseExtension).obj.obj U from
          T.idealInclusion.val.app U (ι U a)))
    (hk : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
      (show T.G.val.obj U from T.c.val.app U (ι U a)) =
        k.val.app U (show S.G.val.obj U from S.c.val.app U a))
    (P : T.CompatibleFirstOrderThickening) :
    (S.mapTarget k).CompatibleFirstOrderThickening := by
  obtain ⟨fS, baseS, redS, lsS, sqS, IS, GS, inclS, cS, zS, uS⟩ := S
  obtain ⟨fT, baseT, redT, lsT, sqT, IT, GT, inclT, cT, zT, uT⟩ := T
  dsimp only at hf
  subst hf
  exact
    { extension := P.extension
      reduction := P.reduction
      locallySurjective := P.locallySurjective
      squareZero := P.squareZero
      baseMap := (inverseImageCommRingFunctor fS.toToposHom).map φ ≫ P.baseMap
      baseMap_reduction := (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) P.baseMap_reduction).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ fS.fSharpInverseImage) ((Functor.map_comp _ _ _).symm.trans
            (congrArg (inverseImageCommRingFunctor fS.toToposHom).map hφ)))))
      kernelInclusion := P.kernelInclusion
      kernelZero := P.kernelZero
      kernelUniversal := P.kernelUniversal
      baseMap_ideal := fun U a => by
        change P.baseMap.hom.app U
            (((inverseImageCommRingFunctor fS.toToposHom).map φ).hom.app U
              (inclS.val.app U a)) = _
        rw [hι U a]
        refine (P.baseMap_ideal U (ι U a)).trans ?_
        exact congrArg (fun g => (show P.extension.obj.obj U from P.kernelInclusion.val.app U g))
          (hk U a) }

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
