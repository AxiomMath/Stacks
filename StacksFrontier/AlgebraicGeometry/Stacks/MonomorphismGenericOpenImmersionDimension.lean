module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismGenericOpenImmersionTransport

/-!
# The dimension computation of Stacks 0DS2: the displayed equation (0DS3) of its proof

In the proof of Stacks 0DS2, `m : 𝒯 ⟶ 𝒳` is a locally-of-finite-type monomorphism of algebraic
stacks, `𝒳` is Jacobson, pseudo-catenary and locally Noetherian, `|𝒯|` is irreducible of
dimension `d` and `𝒳` is reduced of dimension at most `d`. A smooth `f : U ⟶ 𝒳` from a scheme is
base changed to `f' : U' = 𝒯 ×_𝒳 U ⟶ 𝒯`, and for `u' ∈ |U'|` above `u ∈ |U|` the source displays

`dim_{u'}(U') = dim_{u'}(U'_{f'(u')}) + dim_{f'(u')}(𝒯)`
`            ≥ dim_u(U_{f(u)}) + dim_{f(u)}(𝒳) = dim_u(U)`,

the middle comparison coming from `dim_{u'}(U'_{f'(u')}) = dim_u(U_{f(u)})` (**Stacks 0DRN**) and
`dim_{f'(u')}(𝒯) = d ≥ dim_{f(u)}(𝒳)` (**Stacks 0DRX** and the hypotheses), the two outer
equalities being the dimension formula at the smooth charts `U' ⟶ 𝒯` and `U ⟶ 𝒳`
(**Stacks 0DRP**, which for a source representable by an algebraic space is **Stacks 0DRI**).

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_twoFibreProduct_eq_add_ge_add_eq`: the whole
  displayed equation (0DS3) of the proof of Stacks 0DS2, with `U` an algebraic space and `U'`
  the 2-fibre product `𝒯 ×_𝒳 U` of **Stacks 04T2** itself.

## Implementation notes

All dimensions are those of **Stacks 0AFN** and all relative dimensions those of
**Stacks 0DRL**, of the algebraic stacks `U'` (the apex of the square) and `U` (the algebraic
stack of the algebraic space). These agree with the dimensions of **Stacks 04N5** of
representing algebraic spaces
(`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_zero_of_representing`), which is
how `AlgebraicGeometry.Stack.dimensionAtPoint_le_dimensionAtPoint_representingMap` reads the
resulting inequality on the representing algebraic spaces. Keeping them in the extended integers
lets the chain be stated literally, with no casts between the two value types.

The Jacobson, pseudo-catenary and locally Noetherian conditions on `𝒯` that Stacks 0DRX needs
are derived from those on `𝒳` by
`AlgebraicGeometry.Stack.AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType`, **Stacks 0DRW**
and **Stacks 06R6**; the local Noetherianity of `U` and of `U'`, and the local finite type and
smoothness of `f'` (**Stacks 075W**), are derived in the statement itself. Neither the
monomorphism condition on `m` nor the reducedness of `𝒳` enters this computation, so neither is
assumed; nor is surjectivity of `f`.

## References

* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
* [Stacks Project, Tag 0DS3](https://stacks.math.columbia.edu/tag/0DS3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The displayed equation (0DS3) of the proof of Stacks 0DS2.** Let `m : 𝒯 ⟶ 𝒳` be a
locally-of-finite-type 1-morphism of algebraic stacks over `S`, with `𝒳` Jacobson,
pseudo-catenary and locally Noetherian, with `|𝒯|` irreducible and `𝒯` of dimension `d`
(Stacks 0AFP), and with `𝒳` of dimension at most `d`. Let `f : U ⟶ 𝒳` be a smooth 1-morphism
from (the algebraic stack of) an algebraic space, let `Q` be a 2-fibre product of `m` and `f`
(Stacks 04T2) with apex `U' = 𝒯 ×_𝒳 U` and projections `f' = Q.fst : U' ⟶ 𝒯` and
`Q.snd : U' ⟶ U`, and let `u'` be a point of `U'` with image `u` in `U`. Then

* `dim_{u'}(U') = dim_{u'}(U'_{f'(u')}) + dim_{f'(u')}(𝒯)` (Stacks 0DRP at `f'`);
* `dim_{u'}(U'_{f'(u')}) = dim_u(U_{f(u)})` (Stacks 0DRN);
* `dim_{f'(u')}(𝒯) = d` and `dim_{f(u)}(𝒳) ≤ d` (Stacks 0DRX and the hypotheses);
* `dim_u(U_{f(u)}) + dim_{f(u)}(𝒳) ≤ dim_{u'}(U'_{f'(u')}) + dim_{f'(u')}(𝒯)`;
* `dim_u(U_{f(u)}) + dim_{f(u)}(𝒳) = dim_u(U)` (Stacks 0DRP at `f`);
* hence `dim_u(U) ≤ dim_{u'}(U')`.

Dimensions are those of Stacks 0AFN and relative dimensions those of Stacks 0DRL. The
local-finite-type, smoothness and local-Noetherianity witnesses these need are derived in the
statement from the hypotheses (Stacks 06MH, 075W, 06R6). -/
theorem dimensionAtPoint_twoFibreProduct_eq_add_ge_add_eq (m : 𝒯 ⟶ 𝒳)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ)
    (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt))
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hfsm : AlgebraicStacks.IsSmooth B S hS f)
    (Q : Bicategory.TwoCommSq m f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (u' : points B S hS Q.pt.val.val Q.pt.val.property) :
    -- `dim_{u'}(U') = dim_{u'}(U'_{f'(u')}) + dim_{f'(u')}(𝒯)`
    dimensionAtPoint B S hS Q.pt
        (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
            (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
            h𝒳N)) u' =
        relativeStackDimensionAt.{u, w} B S hS Q.fst
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
              (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
              (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
                (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
              (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
                h𝒳N))
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
              h𝒳N) u' +
          dimensionAtPoint B S hS 𝒯
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
              h𝒳N)
            (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom u') ∧
    -- `dim_{u'}(U'_{f'(u')}) = dim_u(U_{f(u)})`
      relativeStackDimensionAt.{u, w} B S hS Q.fst
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
            (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
              (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
              h𝒳N))
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
            h𝒳N) u' =
        relativeStackDimensionAt.{u, w} B S hS f
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm)
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm) h𝒳N) h𝒳N
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') ∧
    -- `dim_{f'(u')}(𝒯) = d`
      dimensionAtPoint B S hS 𝒯
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N)
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom u') =
        ((d : ℤ) : EInt) ∧
    -- `d ≥ dim_{f(u)}(𝒳)`
      dimensionAtPoint B S hS 𝒳 h𝒳N
          (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property f.hom.hom
            (pointsMap B S hS Q.pt.val.val Q.pt.val.property
              (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')) ≤
        ((d : ℤ) : EInt) ∧
    -- `dim_u(U_{f(u)}) + dim_{f(u)}(𝒳) ≤ dim_{u'}(U'_{f'(u')}) + dim_{f'(u')}(𝒯)`
      relativeStackDimensionAt.{u, w} B S hS f
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm)
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm) h𝒳N) h𝒳N
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') +
        dimensionAtPoint B S hS 𝒳 h𝒳N
          (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property f.hom.hom
            (pointsMap B S hS Q.pt.val.val Q.pt.val.property
              (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')) ≤
      relativeStackDimensionAt.{u, w} B S hS Q.fst
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
            (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
              (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
              h𝒳N))
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
            h𝒳N) u' +
        dimensionAtPoint B S hS 𝒯
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N)
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom u') ∧
    -- `dim_u(U_{f(u)}) + dim_{f(u)}(𝒳) = dim_u(U)`
      relativeStackDimensionAt.{u, w} B S hS f
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm)
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm) h𝒳N) h𝒳N
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') +
        dimensionAtPoint B S hS 𝒳 h𝒳N
          (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property f.hom.hom
            (pointsMap B S hS Q.pt.val.val Q.pt.val.property
              (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')) =
        dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU)
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm) h𝒳N)
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') ∧
    -- `dim_u(U) ≤ dim_{u'}(U')`
      dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU)
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm) h𝒳N)
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') ≤
        dimensionAtPoint B S hS Q.pt
          (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
            (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst
              (AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm))
            (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft
              h𝒳N)) u' := by
  classical
  -- the derived witnesses
  have h𝒯N : IsLocallyNoetherianStack.{u, w} B S hS 𝒯 :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N
  have hfft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hfsm
  have h𝒰N : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS f hfft h𝒳N
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS f m Q hQ hfsm
  have hfstft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst hfstSmooth
  have hQN : IsLocallyNoetherianStack.{u, w} B S hS Q.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst hfstft h𝒯N
  -- the three properties of `𝒯` that Stacks 0DRX needs
  have h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯 :=
    AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType B S hS m hft h𝒳Jacobson
  have h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯 :=
    isPseudoCatenary_of_isLocallyOfFiniteType B S hS m hft h𝒳Catenary
  -- Stacks 0DRP at the two smooth charts, and Stacks 0DRN comparing the relative dimensions
  have hQP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS Q.fst
    hfstSmooth hfstft hQN h𝒯N u'
  have hfP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS f hfsm hfft
    h𝒰N h𝒳N (pointsMap B S hS Q.pt.val.val Q.pt.val.property
      (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')
  have hDRN := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS m f Q hQ
    hfft hfstft hQN h𝒰N h𝒯N h𝒳N u'
  -- Stacks 0DRX: the dimension of `𝒯` is `d` at every point
  have hconst := isConstant_dimensionAtPoint_of_irreducibleSpace B S hS 𝒯 h𝒯N h𝒯Jacobson
    h𝒯Catenary h𝒯Irreducible
  have h𝒯val : dimensionAtPoint B S hS 𝒯 h𝒯N
      (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom u') =
      ((d : ℤ) : EInt) :=
    (dimension_eq_dimensionAtPoint_of_isConstant B S hS 𝒯 h𝒯N hconst _).symm.trans h𝒯dim
  have h𝒳val : dimensionAtPoint B S hS 𝒳 h𝒳N
      (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property f.hom.hom
        (pointsMap B S hS Q.pt.val.val Q.pt.val.property
          (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')) ≤
      ((d : ℤ) : EInt) :=
    le_trans (le_iSup (fun x => dimensionAtPoint B S hS 𝒳 h𝒳N x) _) h𝒳dim
  -- the common relative dimension is an integer, so it can be added to an inequality
  obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast B S hS f hfft h𝒰N h𝒳N
    (pointsMap B S hS Q.pt.val.val Q.pt.val.property
      (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')
  have hmid : relativeStackDimensionAt.{u, w} B S hS f hfft h𝒰N h𝒳N
        (pointsMap B S hS Q.pt.val.val Q.pt.val.property
          (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u') +
      dimensionAtPoint B S hS 𝒳 h𝒳N
        (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
          (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property f.hom.hom
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom u')) ≤
      relativeStackDimensionAt.{u, w} B S hS Q.fst hfstft hQN h𝒯N u' +
        dimensionAtPoint B S hS 𝒯 h𝒯N
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom u') := by
    rw [hDRN, hc, h𝒯val, add_comm, add_comm (((c : ℤ) : EInt))]
    exact add_intCast_le_add_intCast_of_le c h𝒳val
  have hfirst := hQP.trans (add_comm _ _)
  have hlast := (add_comm _ _).trans hfP.symm
  exact ⟨hfirst, hDRN, h𝒯val, h𝒳val, hmid, hlast,
    hlast.symm.le.trans (hmid.trans_eq hfirst.symm)⟩

end AlgebraicGeometry.Stack

end
