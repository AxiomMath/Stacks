module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExteriorAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardSheafifyLocallyBijective

/-!
# The pushforward of an exterior algebra along a continuous functor of sites

Let `Φ : Cs ⥤ Ct` be a continuous functor of sites and `A` an exterior algebra of a sheaf of
modules `M` over `Ct`. If pushforward along `Φ` commutes with the sheafification of the
sectionwise exterior powers of `M`, that is, if the comparison
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom` is invertible at each of
them, then the pushforward `Φ_*A` is an exterior algebra of `Φ_*M`. The hypothesis holds when `Φ`
is cocontinuous (`Stacks.SheafOfModules.PushforwardSheafification.isIso_pushforwardSheafifyHom`).

## Main definitions

* `SheafOfModules.ContinuousPushforward.pushforwardGen`: the degree-one generator of `Φ_*A`.
* `SheafOfModules.ContinuousPushforward.sectionwiseExtPowPushforwardIso`: the sheafified
  sectionwise exterior power of `Φ_*M` over `Cs` is the pushforward of the one of `M` over `Ct`,
  given the invertibility of the sheafification comparison.
* `SheafOfModules.ContinuousPushforward.exteriorPushforwardIso`: the degreewise isomorphism
  between `Φ_*A` and any exterior algebra of `Φ_*M`.

## Main results

* `SheafOfModules.ContinuousPushforward.exteriorDescSq_pushforward_app`: the comparison
  homomorphism over the source site is the pushforward of the one over the target site.
* `SheafOfModules.ContinuousPushforward.isExteriorAlgebra_pushforward`: the pushforward of an
  exterior algebra of `M` is an exterior algebra of `Φ_*M`, for any continuous `Φ` along which
  the sheafification comparison of every sectionwise exterior power of `M` is invertible.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules
  Stacks.SheafOfModules.PushforwardSheafification

universe w t a v u v' u'

namespace SheafOfModules.ContinuousPushforward

section Pushforward

open _root_.SheafOfModules.GradedAlgebra

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (Φ : Cs ⥤ Ct)
  [Φ.IsContinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat Jt Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp)) (gen : M ⟶ A.piece 1)
  (hgen : GradedAlgebra.SquareZero gen)

/-- The degree-one generator pushed forward along `Φ`. -/
noncomputable def pushforwardGen :
    (sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M ⟶
      (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).piece 1 :=
  (sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).map gen

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}] in
include hgen in
/-- The pushforward of a square-zero degree-one generator is square-zero. -/
theorem squareZero_pushforwardGen :
    GradedAlgebra.SquareZero (pushforwardGen.{w} Js Φ M A gen) :=
  fun V x => hgen (Φ.op.obj V) x

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}] in
/-- Pushforward of a presheaf of modules along `Φ`, in the two spellings used by
`PresheafOfModules.extPowPushforwardIso` and by
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom`, is the same
functor. -/
theorem sitePushforward_eq_presheafPushforwardFunctor :
    sitePushforward Φ (O := Osharp.obj) =
      presheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp) := rfl

/-- Pushforward along `Φ` in the two spellings, as an isomorphism. It is the identity: the two
functors are equal (`sitePushforward_eq_presheafPushforwardFunctor`). -/
noncomputable def pushforwardRestrictIso (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj) :
    (sitePushforward Φ (O := Osharp.obj)).obj P ≅
      (presheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj P := Iso.refl _

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}] in
/-- `SheafOfModules.ContinuousPushforward.pushforwardRestrictIso` is the identity on sections. -/
theorem pushforwardRestrictIso_hom_apply (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj)
    (V : Csᵒᵖ) (z : ((sitePushforward Φ (O := Osharp.obj)).obj P).obj V) :
    Hom.app (pushforwardRestrictIso.{w} Js Φ (Osharp := Osharp) P).hom V z = z := rfl

/-- The isomorphism between the presheaf of sectionwise exterior powers of the pushforward of
`M` and the pushforward, along `presheafPushforwardFunctor`, of the presheaf of sectionwise
exterior powers of `M`. -/
noncomputable def extPowPushforwardPresheafIso (n : ℕ) :=
  (extPowPushforwardIso (O := Osharp.obj) Φ n M.val).symm ≪≫
    pushforwardRestrictIso.{w} Js Φ (Osharp := Osharp) (extPow n M.val)

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}] in
/-- `extPowPushforwardPresheafIso` is the identity on sections. -/
theorem extPowPushforwardPresheafIso_hom_apply (n : ℕ) (V : Csᵒᵖ)
    (z : (extPow (O := Φ.op ⋙ Osharp.obj) n
      ((sitePushforward Φ (O := Osharp.obj)).obj M.val)).obj V) :
    Hom.app (extPowPushforwardPresheafIso.{w} Js Φ M n).hom V z =
      Hom.app (extPowPushforwardIso (O := Osharp.obj) Φ n M.val).inv V z := rfl

/-- Pushforward along `Φ` commutes with the sheafified sectionwise exterior power in degree `n`,
as soon as the comparison `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom`
of the sheafification of the pushforward with the pushforward of the sheafification is
invertible at the `n`-th sectionwise exterior power of `M`. -/
noncomputable def sectionwiseExtPowPushforwardIso (n : ℕ)
    [IsIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))] :=
  (PresheafOfModules.sheafification.{w}
        (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)).mapIso
      (extPowPushforwardPresheafIso.{w} Js Φ M n) ≪≫
    asIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `sectionwiseExtPowPushforwardIso` acts on sections as the composite of its two legs. -/
theorem sectionwiseExtPowPushforwardIso_hom_val_app (n : ℕ)
    [IsIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))] (V : Csᵒᵖ)
    (x : ((PresheafOfModules.sheafification.{w}
      (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)).obj
        (extPow (O := Φ.op ⋙ Osharp.obj) n
          ((sitePushforward Φ (O := Osharp.obj)).obj M.val))).val.obj V) :
    (sectionwiseExtPowPushforwardIso.{w} Js Φ M n).hom.val.app V x =
      (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val)).val.app V
        (((PresheafOfModules.sheafification.{w}
              (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)).map
            (extPowPushforwardPresheafIso.{w} Js Φ M n).hom).val.app V x) := rfl

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison morphism `pushforwardSheafifyHom` carries the image of a local section over
`V` under the sheafification unit over `Cs` to the image of the same section over `Φ V` under the
sheafification unit over `Ct`. -/
theorem pushforwardSheafifyHom_sheafifyUnit (P : PresheafOfModules.{w} (toRingCat Jt Osharp).obj)
    (V : Csᵒᵖ)
    (y : ((presheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj P).obj V) :
    (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) P).val.app V
        (Hom.app (sheafifyUnit (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
          ((presheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj P)) V y) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat Jt Osharp).obj) P) (Φ.op.obj V) y :=
  sheafificationHomEquiv_symm_app
    (R₀ := (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
    (Rs := pushforwardRingSheaf Js Φ (toRingCat Jt Osharp))
    (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
    (P := (presheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj P)
    (T := (sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj
      ((PresheafOfModules.sheafification.{w} (𝟙 (toRingCat Jt Osharp).obj)).obj P))
    (pushforwardUnit.{w} Js Φ (toRingCat Jt Osharp) P) V y

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `sectionwiseExtPowPushforwardIso` carries the unit-image of a local section of the
sectionwise exterior power over an object `V` of the source site to the unit-image of the
corresponding section over `Φ V`. -/
theorem sectionwiseExtPowPushforwardIso_hom_sheafifyUnit (n : ℕ)
    [IsIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))] (V : Csᵒᵖ)
    (z : (extPow (O := Φ.op ⋙ Osharp.obj) n
      ((sitePushforward Φ (O := Osharp.obj)).obj M.val)).obj V) :
    (sectionwiseExtPowPushforwardIso.{w} Js Φ M n).hom.val.app V
        (Hom.app (sheafifyUnit (𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
          (extPow (O := Φ.op ⋙ Osharp.obj) n
            ((sitePushforward Φ (O := Osharp.obj)).obj M.val))) V z) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat Jt Osharp).obj) (extPow n M.val)) (Φ.op.obj V)
        (Hom.app (extPowPushforwardPresheafIso.{w} Js Φ M n).hom V z) := by
  refine Eq.trans (sectionwiseExtPowPushforwardIso_hom_val_app.{w} Js Φ M n V _) ?_
  refine Eq.trans (congrArg (fun t =>
    (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val)).val.app V t)
    (PresheafOfModules.unit_naturality_apply
      (R₀ := (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
      (R := pushforwardRingSheaf Js Φ (toRingCat Jt Osharp))
      (α := 𝟙 (pushforwardRingSheaf Js Φ (toRingCat Jt Osharp)).obj)
      (extPowPushforwardPresheafIso.{w} Js Φ M n).hom V z)) ?_
  exact pushforwardSheafifyHom_sheafifyUnit.{w} Js Φ (extPow n M.val) V
    (Hom.app (extPowPushforwardPresheafIso.{w} Js Φ M n).hom V z)

omit [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}] in
/-- The ordered product of degree-one sections in the pushed-forward graded algebra is the
ordered product in `A` over the image of the object under `Φ`. -/
theorem homogeneousProd_pushforward (V : Csᵒᵖ) (n : ℕ)
    (z : Fin n → ((GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).piece 1).val.obj V) :
    Stacks.GradedAlgebra.homogeneousProd.{v, u, w, w}
        (O := (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp)).obj)
        (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).toPresheafGradedAlgebra V n z =
      Stacks.GradedAlgebra.homogeneousProd.{v', u', w, w} (O := Osharp.obj)
        A.toPresheafGradedAlgebra (Φ.op.obj V) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg (fun y => (A.mul (n : ℤ) 1).app (Φ.op.obj V) y
        (z (Fin.last n))) (ih fun i => z i.castSucc)

include hgen in
/-- In every degree `n` at which the sheafification comparison of the sectionwise exterior power
is invertible, the comparison homomorphism `exteriorDescSq` over the source site is
`sectionwiseExtPowPushforwardIso` followed by the pushforward of the comparison homomorphism
over the target site. -/
theorem exteriorDescSq_pushforward_app (n : ℕ)
    [IsIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))] :
    (exteriorDescSq (J := Js)
        (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ
          (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M)
        (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A) (pushforwardGen.{w} Js Φ M A gen)
        (squareZero_pushforwardGen.{w} Js Φ M A gen hgen)).app (n : ℤ) =
      (sectionwiseExtPowPushforwardIso.{w} Js Φ M n).hom ≫
        (sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).map
          ((exteriorDescSq M A gen hgen).app (n : ℤ)) := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ?_)
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  have hL := exteriorDescSq_sheafifyUnit_ιMulti (J := Js)
    (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp))
    ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M)
    (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A) (pushforwardGen.{w} Js Φ M A gen)
    (squareZero_pushforwardGen.{w} Js Φ M A gen hgen) n V s
  have hR := sectionwiseExtPowPushforwardIso_hom_sheafifyUnit.{w} Js Φ M n V
    (exteriorPower.ιMulti _ n s)
  have hR2 := exteriorDescSq_sheafifyUnit_ιMulti M A gen hgen n (Φ.op.obj V) s
  refine Eq.trans hL (Eq.symm ?_)
  refine Eq.trans (congrArg (fun z =>
    ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).map
      ((exteriorDescSq M A gen hgen).app (n : ℤ))).val.app V z) hR) ?_
  exact Eq.trans hR2 (homogeneousProd_pushforward.{w} Js Φ A V n _).symm

end Pushforward

section PushforwardUniversal

open _root_.SheafOfModules.GradedAlgebra

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (Φ : Cs ⥤ Ct)
  [Φ.IsContinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (toRingCat Jt Osharp))
  (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen)
  [∀ n : ℕ, IsIso (pushforwardSheafifyHom.{w} Js Φ (toRingCat Jt Osharp) (extPow n M.val))]

include hA in
/-- The comparison homomorphism `exteriorDescSq` over the source site is invertible in every
degree, when the sheafification comparison of every sectionwise exterior power of `M` is
invertible. -/
theorem isIso_exteriorDescSq_pushforward_app (n : ℤ) :
    IsIso ((exteriorDescSq (J := Js)
      (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M)
        (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A) (pushforwardGen.{w} Js Φ M A gen)
        (squareZero_pushforwardGen.{w} Js Φ M A gen hA.1)).app n) := by
  by_cases hn : n < 0
  · refine Limits.IsZero.isIso ?_ ?_ _
    · rw [Limits.IsZero.iff_id_eq_zero]
      ext V x
      exact sectionwiseExteriorAlgebra_piece_eq_zero_of_neg Js
        (𝟙 (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ
          (Osharp := Osharp)).obj)
        ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M).val hn V x
    · rw [Limits.IsZero.iff_id_eq_zero]
      ext V y
      exact exteriorPiece_eq_zero_of_neg M A gen hA hn (Φ.op.obj V) y
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hn)
    have he : (exteriorDescSq M A gen hA.1).app (m : ℤ) =
        (exteriorPieceIso M A gen hA (m : ℤ)).hom := rfl
    rw [exteriorDescSq_pushforward_app.{w} Js Φ M A gen hA.1 m, he]
    exact IsIso.comp_isIso' (Iso.isIso_hom _)
      (((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).mapIso
        (exteriorPieceIso M A gen hA (m : ℤ))).isIso_hom)

include hA in
/-- The pushforward of an exterior algebra `A` of `M` along a continuous functor of sites `Φ` is
an exterior algebra of the pushforward of `M`, on the pushed-forward generator, as soon as the
comparison `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom` is
invertible at every sectionwise exterior power of `M`. -/
theorem isExteriorAlgebra_pushforward :
    GradedAlgebra.IsExteriorAlgebra (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A)
      (pushforwardGen.{w} Js Φ M A gen) := by
  set e := sheafifySectionsIso (J := Js)
    (Osharp := _root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp))
    ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M)
  have huniv := GradedAlgebra.IsExteriorAlgebra.of_desc_isIso
    (isExteriorAlgebra_sectionwiseExteriorAlgebra Js
      (𝟙 (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp)).obj)
      ((sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M).val)
    (e.hom ≫ pushforwardGen.{w} Js Φ M A gen)
    (GradedAlgebra.squareZero_comp _ (squareZero_pushforwardGen.{w} Js Φ M A gen hA.1))
    (fun n => isIso_exteriorDescSq_pushforward_app.{w} Js Φ M A gen hA n)
  have h2 := GradedAlgebra.IsExteriorAlgebra.comp_iso huniv e.inv e.isIso_inv
  rwa [show e.inv ≫ e.hom ≫ pushforwardGen.{w} Js Φ M A gen = _ from
    Iso.inv_hom_id_assoc _ _] at h2

variable (B : GradedAlgebra.{w, w} (toRingCat Js
    (_root_.Stacks.SheafOfModules.pushforwardCommRingSheaf Js Φ (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js Φ (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : GradedAlgebra.IsExteriorAlgebra B gen')

/-- The degree-`n` isomorphism between the pushforward of an exterior algebra `A` of `M` and an
exterior algebra `B` of the pushforward of `M`, given by their universal properties. -/
noncomputable def exteriorPushforwardIso (n : ℤ) :
    (GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).piece n ≅ B.piece n :=
  GradedAlgebra.IsUniversal.pieceIso
    (isExteriorAlgebra_pushforward.{w} Js Φ M A gen hA).isUniversal hB.isUniversal n

/-- The comparison of exterior algebras along a pushforward carries one generator to the
other. -/
theorem exteriorPushforwardIso_generator :
    pushforwardGen.{w} Js Φ M A gen ≫
        (exteriorPushforwardIso.{w} Js Φ M A gen hA B gen' hB 1).hom = gen' :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of exterior algebras along a pushforward is multiplicative on homogeneous
local sections. -/
theorem exteriorPushforwardIso_mul (i j : ℤ) (V : Csᵒᵖ)
    (x : ((GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).piece i).val.obj V)
    (y : ((GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).piece j).val.obj V) :
    (exteriorPushforwardIso.{w} Js Φ M A gen hA B gen' hB (i + j)).hom.val.app V
        (((GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).mul i j).app V x y) =
      (B.mul i j).app V
        ((exteriorPushforwardIso.{w} Js Φ M A gen hA B gen' hB i).hom.val.app V x)
        ((exteriorPushforwardIso.{w} Js Φ M A gen hA B gen' hB j).hom.val.app V y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j V x y

/-- The comparison of exterior algebras along a pushforward carries the unit to the unit. -/
theorem exteriorPushforwardIso_one (V : Csᵒᵖ) :
    (exteriorPushforwardIso.{w} Js Φ M A gen hA B gen' hB 0).hom.val.app V
        ((GradedAlgebra.pushforwardAlg.{w, w} Js Φ A).one.eval V) = B.one.eval V :=
  GradedAlgebra.IsUniversal.pieceIso_one _ _ V

end PushforwardUniversal

end SheafOfModules.ContinuousPushforward

end
