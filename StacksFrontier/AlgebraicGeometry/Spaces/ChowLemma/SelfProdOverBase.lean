module

public import StacksFrontier.AlgebraicGeometry.Spaces.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FinProductPeel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization

/-!
# The self-product over an algebraic space inside the product over the base

Let `X` be an algebraic space over `S` whose structure morphism is separated, and let `U` be an
object of the spaces-étale site of `X`. The `n`-fold self-product `U ×_X ⋯ ×_X U` is formed over
`X`; the proof of Stacks 089J has to put it inside a product formed over the *base*, and the
whole argument turns on that comparison being an immersion.

This file proves it, by induction on the number of factors. One factor peels off as a fibre
product by `Stacks.FinProd.isLimitBinaryFanPiSucc`, the passage from a fibre product over `X` to
one over the base is the *magic diagram* of Stacks 03KN, which is a closed immersion exactly
because `X` is separated over the base, and the remaining factors are handled by the induction
hypothesis, base-changed along one projection.

The statement is proved with a family of morphisms `k i` out of `U` built into it, so that the
comparison lands in a product of *other* objects — in Stacks 089J the `n` copies of a projective
compactification of the chart, into which the chart is an open immersion. Carrying them along is
free and avoids a second induction identifying a product of immersions as an immersion.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.selfProdTail`: the morphism of the spaces-étale site of
  `X` forgetting the zeroth factor of a self-product.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isPullback_selfProdSucc`: **the `(n+1)`-fold self-product
  over `X` is the fibre product over `X` of the chart with the `n`-fold self-product**, as a
  cartesian square of presheaves with the zeroth projection and
  `AlgebraicGeometry.Space.SpacesEtale.selfProdTail` as its legs.
* `AlgebraicGeometry.Space.SpacesEtale.exists_isImmersion_selfProdOverBase`: **the comparison of
  the self-product over `X` with a product over the base is an immersion**, given a family of
  immersions out of the chart.

## What is and is not proved

Nothing here carries a Stacks attribute. The magic diagram is Stacks 03KN, carried by
`AlgebraicGeometry.Space.isClosedImmersion_mapDesc`; base change and composition of immersions
are Stacks 02YW and 02YV, carried in
`StacksFrontier/AlgebraicGeometry/Spaces/ImmersionBaseChange.lean`; what is added is the induction
on the number of factors which combines them.

The comparison morphism is produced as the content of an existence statement rather than as a
definition: its construction passes through the comparison isomorphisms of two cartesian
squares, which are chosen, and nothing downstream needs a formula for it — only that it is an
immersion and what its components are.

The dual statement, that the comparison is a *closed* immersion when the morphisms `k i` are,
is not proved; only the immersion form is, that being what Stacks 089J consumes through Stacks
01RG.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The morphism of the spaces-étale site of `X` forgetting the zeroth factor of a finite
self-product.** -/
def selfProdTail (U : SpacesEtale B S hS X) (n : ℕ) :
    selfProd B S hS X U (n + 1) ⟶ selfProd B S hS X U n :=
  Stacks.FinProd.piTail fun _ : Fin (n + 1) ↦ U

/-- Composing `AlgebraicGeometry.Space.SpacesEtale.selfProdTail` with the `i`-th projection is
the `(i + 1)`-st projection. -/
@[simp]
theorem selfProdTail_comp_π (U : SpacesEtale B S hS X) (n : ℕ) (i : Fin n) :
    selfProdTail B S hS X U n ≫ Pi.π (fun _ : Fin n ↦ U) i =
      Pi.π (fun _ : Fin (n + 1) ↦ U) i.succ :=
  Stacks.FinProd.piTail_comp_π (fun _ : Fin (n + 1) ↦ U) i

/-- **The `(n + 1)`-fold self-product of an object of the spaces-étale site of `X` is the binary
product of that object with the `n`-fold self-product**, the two legs being the zeroth projection
and `AlgebraicGeometry.Space.SpacesEtale.selfProdTail`. -/
def isLimitBinaryFanSelfProdSucc (U : SpacesEtale B S hS X) (n : ℕ) :
    IsLimit (BinaryFan.mk (Pi.π (fun _ : Fin (n + 1) ↦ U) 0) (selfProdTail B S hS X U n)) :=
  Stacks.FinProd.isLimitBinaryFanPiSucc fun _ : Fin (n + 1) ↦ U

/-- **The `(n + 1)`-fold self-product over `X` is the fibre product over `X` of the object with
its `n`-fold self-product.** Binary products in the spaces-étale site of `X` are fibre products
over `X`, because the final object of that site is the identity of `X`; the inclusion into the
algebraic spaces over `S` preserves fibre products, and a cartesian square of algebraic spaces is
cartesian as a square of presheaves. -/
theorem isPullback_selfProdSucc (U : SpacesEtale B S hS X) (n : ℕ) :
    IsPullback ((toSpaces B S hS X).map (Pi.π (fun _ : Fin (n + 1) ↦ U) 0)).hom
      ((toSpaces B S hS X).map (selfProdTail B S hS X U n)).hom
      U.obj.hom.hom (selfProd B S hS X U n).obj.hom.hom := by
  have h0 := IsPullback.of_is_product' (isLimitBinaryFanSelfProdSucc B S hS X U n)
    (final_isTerminal B S hS X)
  rw [show (final_isTerminal B S hS X).from U = toFinal B S hS U from
        (final_isTerminal B S hS X).hom_ext _ _,
    show (final_isTerminal B S hS X).from (selfProd B S hS X U n) =
        toFinal B S hS (selfProd B S hS X U n) from
      (final_isTerminal B S hS X).hom_ext _ _] at h0
  exact AlgebraicSpaces.isPullback_hom B S hS (h0.map (toSpaces B S hS X))

/-- **The comparison of the self-product over `X` with a product over the base is an
immersion.** Let `X` be an algebraic space over `S` whose structure morphism `X ⟶ T` to the
terminal presheaf is separated, let `U` be an object of the spaces-étale site of `X`, and let
`k i : U ⟶ 𝒴 i` be immersions into `n + 1` further algebraic spaces over `S`. Then the morphism
from the `(n + 1)`-fold self-product `U ×_X ⋯ ×_X U` into the product `𝒴 0 ×_T ⋯ ×_T 𝒴 n` over
the base whose `i`-th component is the `i`-th projection followed by `k i` is an immersion.

The induction peels one factor off both products. On the left the peeled form is a fibre product
over `X` and on the right one over the base, so the step is the magic diagram of Stacks 03KN —
a closed immersion because `X ⟶ T` is separated — followed by the base change of the comparison
for `n` factors along a projection. In Stacks 089J the `𝒴 i` are the `n + 1` copies of a
projective compactification of the chart `U`, and the `k i` are the open immersion of the chart
into it. -/
theorem exists_isImmersion_selfProdOverBase {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsTerminal T) (hsep : IsSeparated B S hS (hT.from X.obj))
    (U : SpacesEtale B S hS X) :
    ∀ (n : ℕ) (𝒴 : Fin (n + 1) → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (k : ∀ i, (underlying B S hS X U).obj ⟶ 𝒴 i), (∀ i, IsImmersion B S hS (k i)) →
      ∃ φ : (underlying B S hS X (selfProd B S hS X U (n + 1))).obj ⟶ ∏ᶜ 𝒴,
        IsImmersion B S hS φ ∧
          ∀ i, φ ≫ Pi.π 𝒴 i =
            ((toSpaces B S hS X).map (Pi.π (fun _ : Fin (n + 1) ↦ U) i)).hom ≫ k i := by
  intro n
  induction n with
  | zero =>
      intro 𝒴 k hk
      refine ⟨Pi.lift fun i ↦ ((toSpaces B S hS X).map (Pi.π (fun _ : Fin 1 ↦ U) i)).hom ≫ k i,
        ?_, fun i ↦ Pi.lift_comp_π _ i⟩
      have ha : IsIso ((toSpaces B S hS X).map (Pi.π (fun _ : Fin 1 ↦ U) 0)).hom := by
        rw [← ObjectProperty.ι_map]
        infer_instance
      have hπ : IsIso (Pi.π 𝒴 0) := Stacks.FinProd.isIso_pi_π_fin_one 𝒴
      have hval : (Pi.lift fun i ↦
            ((toSpaces B S hS X).map (Pi.π (fun _ : Fin 1 ↦ U) i)).hom ≫ k i) =
          (((toSpaces B S hS X).map (Pi.π (fun _ : Fin 1 ↦ U) 0)).hom ≫ k 0) ≫
            inv (Pi.π 𝒴 0) :=
        (IsIso.eq_comp_inv _).2 (Pi.lift_comp_π _ 0)
      rw [hval]
      refine isImmersion_comp B S hS _ _ (isImmersion_comp B S hS _ _ ?_ (hk 0)) ?_
      · exact isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _)
      · exact isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _)
  | succ n ih =>
      intro 𝒴 k hk
      obtain ⟨φ, hφ, hφc⟩ := ih (fun i : Fin (n + 1) ↦ 𝒴 i.succ) (fun i ↦ k i.succ)
        fun i ↦ hk i.succ
      have sq := isPullback_selfProdSucc B S hS X U (n + 1)
      have e₁ : U.obj.hom.hom ≫ hT.from X.obj = k 0 ≫ hT.from (𝒴 0) := hT.hom_ext _ _
      have e₂ : (selfProd B S hS X U (n + 1)).obj.hom.hom ≫ hT.from X.obj =
          φ ≫ hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ) := hT.hom_ext _ _
      have sqP := IsPullback.of_is_product' (Stacks.FinProd.isLimitBinaryFanPiSucc 𝒴) hT
      have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
        (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u})
          (BigFppfOver.toScheme B S hS))
      have hcomp : (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
        have : MorphismProperty.IsStableUnderComposition
            (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
          MorphismProperty.IsMultiplicative.toIsStableUnderComposition
        MorphismProperty.IsStableUnderComposition.inverseImage
          (P := (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}))
          (BigFppfOver.toScheme B S hS)
      have hem := MorphismProperty.pullbackMap
        (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsImmersion.{u}) (BigFppfOver.toScheme B S hS)))
        (f := U.obj.hom.hom ≫ hT.from X.obj)
        (g := (selfProd B S hS X U (n + 1)).obj.hom.hom ≫ hT.from X.obj)
        (f' := hT.from (𝒴 0)) (g' := hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ))
        (i₁ := k 0) (i₂ := φ) (hk 0) hφ e₁ e₂
      refine ⟨sq.isoPullback.hom ≫ pullback.mapDesc U.obj.hom.hom
          (selfProd B S hS X U (n + 1)).obj.hom.hom (hT.from X.obj) ≫
        pullback.map (U.obj.hom.hom ≫ hT.from X.obj)
          ((selfProd B S hS X U (n + 1)).obj.hom.hom ≫ hT.from X.obj) (hT.from (𝒴 0))
          (hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ)) (k 0) φ (𝟙 T)
          ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₂) ≫
        sqP.isoPullback.inv, ?_, fun j ↦ ?_⟩
      · refine isImmersion_comp B S hS _ _
          (isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _)) ?_
        refine isImmersion_comp B S hS _ _
          (isImmersion_of_isClosedImmersion B S hS (isClosedImmersion_mapDesc B S hS _ _ _ hsep))
          ?_
        exact isImmersion_comp B S hS _ _ hem
          (isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _))
      · have hfst : sqP.isoPullback.inv ≫ Pi.π 𝒴 0 =
            pullback.fst (hT.from (𝒴 0)) (hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ)) :=
          (Iso.inv_comp_eq _).2 sqP.isoPullback_hom_fst.symm
        have hsnd : sqP.isoPullback.inv ≫ Stacks.FinProd.piTail 𝒴 =
            pullback.snd (hT.from (𝒴 0)) (hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ)) :=
          (Iso.inv_comp_eq _).2 sqP.isoPullback_hom_snd.symm
        induction j using Fin.cases with
        | zero =>
            rw [Category.assoc, Category.assoc, Category.assoc, hfst, pullback.lift_fst,
              pullback.lift_fst_assoc, Category.comp_id, ← Category.assoc,
              sq.isoPullback_hom_fst]
        | succ i =>
            have hsnd2 : sqP.isoPullback.inv ≫ Pi.π 𝒴 i.succ =
                pullback.snd (hT.from (𝒴 0)) (hT.from (∏ᶜ fun i : Fin (n + 1) ↦ 𝒴 i.succ)) ≫
                  Pi.π (fun i : Fin (n + 1) ↦ 𝒴 i.succ) i := by
              rw [← Stacks.FinProd.piTail_comp_π 𝒴 i, ← Category.assoc, hsnd]
            rw [Category.assoc, Category.assoc, Category.assoc, hsnd2,
              pullback.lift_snd_assoc, Category.assoc, hφc i, pullback.lift_snd_assoc,
              Category.comp_id, ← Category.assoc, sq.isoPullback_hom_snd, ← Category.assoc,
              ← hom_toSpaces_map_comp, selfProdTail_comp_π]

end AlgebraicGeometry.Space.SpacesEtale

end
