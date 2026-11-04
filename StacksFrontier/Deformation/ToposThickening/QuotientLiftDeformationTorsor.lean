module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftDeformation

/-!
# The lifts of a quotient form a torsor as soon as there is one (Stacks 0CZV)

In the setting of `StacksFrontier/Deformation/ToposThickening/QuotientLiftDeformation.lean`, this
file names the group `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)` and the action `𝒦' ↦ 𝒦'_φ` of the remark of
Stacks 0CZV, and shows that the lifts of the quotient form a principal homogeneous space under
that group as soon as one lift exists, without passing through the obstruction of Stacks 0CZU.

## Main results

* `Deformation.ToposThickening.quotientLiftGroup`: the group `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)`.
* `Deformation.ToposThickening.quotientLiftDeformation`: the lift `𝒦'_φ`.
* `Deformation.ToposThickening.exists_addTorsor_quotientLift_of_nonempty`: the lifts form a
  principal homogeneous space under `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)` once one lift exists.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section QuotientLiftDeformation

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (K : Subobject ((pullbackModules i.toRingedToposModulesHom).obj F'))

attribute [local instance] epi_quotientLiftCanonicalMap

/-- **The group `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)` of Stacks 0CZV**, under which the lifts of the quotient
`ℱ ⟶ 𝒬 = ℱ/𝒦` form a principal homogeneous space. -/
abbrev quotientLiftGroup : Type _ :=
  (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
    (baseIdealTensor t f ht).obj (cokernel K.arrow)

include comm in
/-- **The lift `𝒦'_φ` of the remark of Stacks 0CZV**: for a lift `𝒦'` of the quotient and
`φ : 𝒦 ⟶ 𝒬 ⊗ f^*𝒥`, the subsheaf of the sections `s` of `ℱ'` whose image in `ℱ` is a section `k`
of `𝒦` and whose image in `ℱ'/𝒦'` is `φ(k)`, read through the inclusion `𝒬 ⊗ f^*𝒥 ⊂ ℱ'/𝒦'`. It is
the value of the action of
`Deformation.ToposThickening.exists_addTorsor_quotientLift_of_nonempty`: the kernel of
`π⁻¹(𝒦) ⟶ ℱ'/𝒦'`, `s ↦ (s mod 𝒦') - φ(π(s))`
(`Deformation.ToposThickening.extensionDeformation`). -/
noncomputable def quotientLiftDeformation
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    {K' : Subobject F'} (hK' : IsQuotientLift i f' F' K K')
    (φ : quotientLiftGroup i t f ht F' K) : Subobject F' :=
  extensionDeformation (S := quotientLiftPreimageShortComplex i hi F' K)
    (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftPreimageι i F' K) K'
    (factors_of_isQuotientLift i t f f' hi ht comm F' K hstrict hflat hK')
    (i.pushforwardModules.map φ)

include comm in
/-- **The lifts of a quotient form a principal homogeneous space under `Hom_O(𝒦, 𝒬 ⊗ f^*𝒥)`, as
soon as there is one**, with the action `𝒦' ↦ 𝒦'_φ` of the remark of Stacks 0CZV
(`Deformation.ToposThickening.quotientLiftDeformation`). By Remark 0CZU a lift exists exactly when
the obstruction vanishes; see `Deformation.ToposThickening.exists_addTorsor_quotientLift`. -/
theorem exists_addTorsor_quotientLift_of_nonempty
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hQ : IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (cokernel K.arrow)))
    (hne : Nonempty {K' : Subobject F' // IsQuotientLift i f' F' K K'}) :
    ∃ T : AddTorsor (quotientLiftGroup i t f ht F' K)
        {K' : Subobject F' // IsQuotientLift i f' F' K K'},
      ∀ (φ : quotientLiftGroup i t f ht F' K)
        (K' : {K' : Subobject F' // IsQuotientLift i f' F' K K'}),
        (T.vadd φ K').val =
          quotientLiftDeformation i t f f' hi ht comm F' K hstrict hflat K'.property φ := by
  have := epi_quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K
  have hS := quotientLiftPreimageShortComplex_shortExact i hi F' K
  obtain ⟨T, hT⟩ := exists_addTorsor_extensionKernelIn
    (S := quotientLiftPreimageShortComplex i hi F' K)
    (c := quotientLiftCanonicalMap i t f f' hi ht comm F' hstrict hflat K)
    (quotientLiftPreimageι i F' K) hS
    (pushforwardModulesHomAddEquiv i hi
      (K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((baseIdealTensor t f ht).obj (cokernel K.arrow)))
    (IsQuotientLift i f' F' K)
    (isQuotientLift_extensionKernelIn i t f f' hi ht comm F' K hstrict hflat hQ)
    (fun _ hK' => exists_extensionKernelIn_eq_of_isQuotientLift i t f f' hi ht comm F' K
      hstrict hflat hK') hne
  exact ⟨T, fun φ K' => hT φ K' _⟩

end QuotientLiftDeformation

end Deformation.ToposThickening

end
