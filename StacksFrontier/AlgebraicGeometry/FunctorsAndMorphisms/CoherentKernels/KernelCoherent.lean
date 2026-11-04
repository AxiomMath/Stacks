module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.FiniteSupportVanishing
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.DiagonalSurjection
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient

/-!
# The kernel of a coherence-preserving exact functor is coherent

Let `k` be a field and let `X` and `Y` be schemes of finite type over `k` with `X` separated. A
quasi-coherent kernel `𝒦` on `X ×_k Y` satisfying the two conditions of [Stacks, Tag 0FZH] is
coherent as soon as `F_𝒦(𝒪_X)` is: by [Stacks, Tag 0FZJ] it is a quotient of
`𝒪_X ⊠ F_𝒦(𝒪_X)`, which is coherent on the Noetherian scheme `X ×_k Y`. This is the coherence
step of the proof of [Stacks, Tag 0FZN].

## Main results

* `AlgebraicGeometry.CoherentKernels.isCoherent_of_integralTransformExactKernel`.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
* [Stacks Project, Tag 0FZJ](https://stacks.math.columbia.edu/tag/0FZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CoherentKernels

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **The kernel of [Stacks, Tag 0FZH] is coherent when its integral transform sends `𝒪_X` to a
coherent module.** It is a quotient of `𝒪_X ⊠ F_𝒦(𝒪_X)` by [Stacks, Tag 0FZJ], and that external
tensor product of coherent modules is coherent on the locally Noetherian scheme `X ×_k Y`. -/
theorem isCoherent_of_integralTransformExactKernel
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom]
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : integralTransformExactKernel k X Y K)
    (hO : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      ((quasicoherentIntegralTransform k X Y K).obj
        ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
            X.left⟩).obj.IsCoherent) :
    K.obj.IsCoherent := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom Y.hom ≫ X.hom)
  obtain ⟨e, he⟩ := exists_epi_externalTensorProduct_unit k X Y K hK
  have hO' : (SheafOfModules.unit X.left.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have h₁ : ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj
      (SheafOfModules.unit X.left.ringCatSheaf)).IsCoherent :=
    isCoherent_pullback _ _
  have h₂ : ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).obj
      ((quasicoherentIntegralTransform k X Y K).obj
        ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
            X.left⟩).obj).IsCoherent :=
    @isCoherent_pullback _ _ _ _ _ hO
  have hE := @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent
    (pullback X.hom Y.hom).toRingedSpace _ _ h₁ h₂
  have : K.obj.IsQuasicoherent := K.property
  have : (externalTensorProduct X.hom Y.hom (SheafOfModules.unit X.left.ringCatSheaf)
      ((quasicoherentIntegralTransform k X Y K).obj
        ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
            X.left⟩).obj).IsFiniteType := hE.isFiniteType
  have : K.obj.IsFiniteType := Scheme.Modules.isFiniteType_of_epi e
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    K.obj

end AlgebraicGeometry.CoherentKernels

end
