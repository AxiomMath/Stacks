module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveObstructionAtTranslation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityConverse
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityCriterionProof

/-!
# Stacks 07YM

Let `S` be a locally Noetherian scheme, `𝒳` a category fibred in groupoids over the big fppf
site of `S` satisfying (RS\*), `U = Spec A` affine of finite type over `S` mapping into an
affine open `Spec Λ ⊆ S`, `x` an object of `𝒳` over `U`, and `ξ : E ⟶ NL_{A/Λ}` a morphism of
`D⁻(A)` satisfying conditions (i) and (ii) of the tag. Then at a finite type point `u₀ ∈ U`
with residue field `k`, `x` is versal at `u₀` as soon as `ξ` induces a surjection
`H^{-1}(E ⊗ᴸ_A k) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A k)` and an injection
`H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)`, and conversely when `u₀` is a closed point.

This file states the tag once and proves it.

## Main results

* `Deformation.Artin.naiveVersalityCriterion` — **Stacks 07YM.** The predicate
  `Deformation.Artin.NaiveVersalityCriterion`, which [Stacks, Tag 07YN] and
  [Stacks, Tag 07YU] consume as a hypothesis, holds.

## Implementation notes

The two directions are `Deformation.Artin.isVersalAt_of_derivedFibreHomologyMap_conditions`
and `Deformation.Artin.derivedFibreHomologyMap_conditions_of_isVersalAt`, both stated in raw
variables — a ring `Λ`, a ring `A`, a structure morphism `Spec A ⟶ S` factored through an
affine open `Spec Λ ⟶ S` — and the translation from the `Deformation.Artin.ChartedObject` and
`Deformation.Artin.NaiveObstructionAt` vocabulary of the predicate is
`StacksFrontier.Deformation.Artin.Obstruction.NaiveObstructionAtTranslation`: hypothesis (i)
becomes `Deformation.Artin.NaiveObstructionAt.nonempty_underFiber_iff_comp_eq_zero`,
hypothesis (ii) becomes `Deformation.Artin.NaiveObstructionAt.exists_tangentEquiv`, and the
dictionary of the charted object is a family of `rfl`s. In particular the versality witness
`Deformation.Artin.ChartedObject.overScheme_eq` needs no transport: it and the raw-variable
witness are two proofs of the same `Prop`.

`NaiveVersalityCriterion` is a bare predicate over the data `hp hRS P hΩ E ξ` and carries
neither `IsLocallyNoetherian S` nor `Algebra.FiniteType c.ring P.ring` nor the boundedness of
`E`; the tag requires all three, so they are hypotheses of the theorem. They are the source's
own hypotheses and nothing else is assumed: `IsNoetherianRing c.ring` follows from the first
through `c.immersion` being an open immersion, `IsNoetherianRing P.ring` from the second, and
`Mono c.immersion` from the open immersion.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

universe u v w

section Tag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
variable (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
variable (P : ChartedObject B S hS p c) [Algebra.FiniteType c.ring P.ring]
variable (hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring))))
variable (E : DerivedCategory (ModuleCat.{u} P.ring))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} P.ring)).minus E)
  (ξ : E ⟶ P.naiveCotangent)

include hE in
/-- **Stacks 07YM.** Let `S` be a locally Noetherian scheme, let `𝒳` be a category fibred in
groupoids over the big fppf site of `S` satisfying (RS\*), let `U = Spec A` be affine of finite
type over `S` mapping into an affine open `Spec Λ ⊆ S`, let `x` be an object of `𝒳` over `U`,
and let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` such that

1. for every deformation situation `(x, A' → A)` the object `x` lifts to `Spec A'` exactly
   when `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` is zero, and
2. there is an isomorphism of functors `T_x(−) ⟶ Ext⁰_A(E, −)` carrying the canonical element
   to `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`.

Let `u₀ ∈ U` be a finite type point with residue field `k`. Then `x` is versal at `u₀` as soon
as `ξ` induces a surjection `H^{-1}(E ⊗ᴸ_A k) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A k)` and an injection
`H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)`; and conversely, if `u₀` is a closed point at which `x`
is versal, then `ξ` induces such a surjection and such an injection.

Both directions are stated at once, as the predicate
`Deformation.Artin.NaiveVersalityCriterion` which [Stacks, Tag 07YN] and [Stacks, Tag 07YU]
consume as a hypothesis. -/
@[stacks 07YM]
public theorem naiveVersalityCriterion : NaiveVersalityCriterion hp hRS P hΩ E ξ := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of c.ring)) :=
    isLocallyNoetherian_of_isOpenImmersion c.immersion
  have : IsNoetherianRing c.ring :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of c.ring)).mp inferInstance
  have : IsNoetherianRing P.ring := Algebra.FiniteType.isNoetherianRing c.ring P.ring
  intro data u hu
  obtain ⟨teq, hteqnat, hteqcan⟩ := data.exists_tangentEquiv
  refine ⟨fun h => ?_, fun hclosed hversal => ?_⟩
  · exact isVersalAt_of_derivedFibreHomologyMap_conditions c.ring P.ring B S hS
      P.obj.alg.toScheme P.obj.alg.mem c.immersion P.factorization p P.point P.obj.obj.2
      hp hRS hΩ E hE ξ
      (fun _ _ _ _ _ D hq hchart => data.nonempty_underFiber_iff_comp_eq_zero D hq hchart)
      teq hteqnat hteqcan u hu h.1 h.2
  · exact derivedFibreHomologyMap_conditions_of_isVersalAt c.ring P.ring B S hS
      P.obj.alg.toScheme P.obj.alg.mem c.immersion P.factorization p P.point P.obj.obj.2
      hp hRS hΩ E hE ξ teq hteqnat hteqcan u hclosed
      (fun _ _ _ _ _ D hq hchart hkill =>
        (data.nonempty_underFiber_iff_comp_eq_zero D hq hchart).mpr hkill)
      hversal

include hE in
/-- **Stacks 07YN**, with the versality criterion of Stacks 07YM discharged rather than assumed.

`Deformation.Artin.exists_isOpen_isVersalAt_of_naiveObstructionAt` takes that criterion as a
hypothesis, and must: it lives in a module this one imports, while the criterion is proved here,
so it cannot apply it without a cycle. This is the same statement with the hypothesis supplied by
`Deformation.Artin.naiveVersalityCriterion`, so the tag sits on a declaration that grants
nothing. -/
@[stacks 07YN]
public theorem isOpenVersalityAt_of_naiveObstructionAt
    (data : NaiveObstructionAt hp hRS P hΩ E ξ)
    (hFinite : ∀ n : ℤ,
      Module.Finite P.ring ((DerivedCategory.homologyFunctor (ModuleCat.{u} P.ring) n).obj E))
    (u₀ : Spec (.of P.ring)) (hu₀ : IsClosed ({u₀} : Set (Spec (.of P.ring))))
    (hversal : IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u₀ P.point
      P.overScheme_eq) :
    ∃ V : Set (Spec (.of P.ring)), IsOpen V ∧ u₀ ∈ V ∧
      ∀ u ∈ V, IsFiniteTypePoint u →
        IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u P.point
          P.overScheme_eq :=
  exists_isOpen_isVersalAt_of_naiveObstructionAt (hE := hE) (data := data) (hFinite := hFinite)
    (hcriterion := naiveVersalityCriterion hp hRS P hΩ E hE ξ)
    (u₀ := u₀) (hu₀ := hu₀) (hversal := hversal)

end Tag

end Deformation.Artin

end
