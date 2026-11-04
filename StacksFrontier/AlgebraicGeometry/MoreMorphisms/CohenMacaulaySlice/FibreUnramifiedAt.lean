module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreQuasiFiniteAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.LocalRing.MinimalGenerators
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.QuasiFiniteSlice

/-!
# The fibre ideal of a slice cut by a minimal generating sequence of the fibre

Let `f : X ⟶ S` be a morphism of schemes, let `x : X`, and let `h₁, …, h_r` be elements of
`𝒪_{X, x}` whose images in the local ring `𝒪_{X_{f x}, x}` of the fibre **generate its maximal
ideal**.  Let `ι : Z ⟶ X` be a preimmersion through `x` on which all the `h_i` vanish.  Then

> `𝔪_{f x} · 𝒪_{Z, z} = 𝔪_z`

at the point `z` of `Z` above `x`.  Equivalently, by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, the local ring of the fibre of `ι ≫ f` at `z`
is the residue field `κ(z)`.

This is the source's computation
`𝒪_{T, v} = 𝒪_{V, v} / (φ(f₁), …, φ(f_d)) = κ(v)` in the proof of the structure theorem
**Stacks 06N3**, and it is the first of the two clauses by which **Stacks 02GF** recognizes
unramifiedness at a point;  the second, finite separability of `κ(z)/κ(f z)`, is a statement
about residue fields alone and is untouched here.

The hypothesis that the images *generate* the maximal ideal is what distinguishes this from the
quasi-finiteness datum of
`Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk`, which asks only that they
form a regular sequence of length the dimension of the fibre stalk and therefore only makes the
fibre stalk of the slice zero-dimensional.  A zero-dimensional local ring need not be a field,
so that datum cannot be upgraded to this one;  the generating hypothesis has to be arranged when
the slicing sequence is chosen, which is what
`AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_fiberStalk_of_smooth`
does.

## Main results

* `Stacks.AlgebraicGeometry.map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk`:
  the fibre ideal of the slice is the whole maximal ideal.
* `Stacks.AlgebraicGeometry.isField_fiberStalk_comp_of_ofList_eq_maximalIdeal_fiberStalk`: the
  same statement read on the scheme-theoretic fibre — its local ring at `z` is a field.

## Implementation notes

The whole argument is the commutative algebra of
`IsLocalRing.map_eq_maximalIdeal_of_ofList_quotient_eq_maximalIdeal`:  the ideals
`(h₁, …, h_r) + 𝔪_{f x}𝒪_{X, x}` and `𝔪_x` have the same image in
`𝒪_{X, x} / 𝔪_{f x}𝒪_{X, x}` and both contain `𝔪_{f x}𝒪_{X, x}`, so they agree, and the
surjection `𝒪_{X, x} → 𝒪_{Z, z}` of a preimmersion kills the first summand while carrying `𝔪_x`
onto `𝔪_z`.

What the geometry contributes is only the translation of the hypothesis from the fibre stalk to
that quotient, which is `AlgebraicGeometry.quotientStalkEquivFiberStalk_mk` together with
`Stacks.AlgebraicGeometry.stalkCongr_hom_eq_cast`;  no comparison of the two *fibres* is needed,
and in particular none of the pullback bookkeeping that
`Stacks.AlgebraicGeometry.quasiFiniteAt_comp_of_isRegular_fiberStalk` runs through
`AlgebraicGeometry.fiberMapOfSourceHom`.

No `@[stacks]` attribute is claimed: **Stacks 02GF** is registered on
`AlgebraicGeometry.unramifiedAt_tfae`, and this is one clause of it for one morphism, not the
tag.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

variable {X S Z : Scheme.{u}}

/-- **The fibre ideal of a slice cut by a minimal generating sequence of the fibre is the whole
maximal ideal.**  Let `f : X ⟶ S`, let `ι : Z ⟶ X` be a preimmersion with `ι z = x`, and let
`h₁, …, h_r` be elements of `𝒪_{X, x}` which vanish in `𝒪_{Z, z}` and whose images in the local
ring of the fibre `X_{f x}` at `x` **generate its maximal ideal**.  Then
`𝔪_{f x} 𝒪_{Z, z} = 𝔪_z`.

This is the source's `𝒪_{T, v} = 𝒪_{V, v}/(φ(f₁), …, φ(f_d)) = κ(v)` in the proof of
**Stacks 06N3**, and the first clause of the characterization of unramifiedness at a point in
**Stacks 02GF**. -/
theorem map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk
    (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S) (z : Z) (x : X) (hx : ι z = x)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (hzero : ∀ k, (ι.stalkMap z).hom (hx.symm ▸ h k) = 0)
    (hgen : Ideal.ofList
        (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ h k))
      = maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    Ideal.map ((ι ≫ f).stalkMap z).hom (maximalIdeal (S.presheaf.stalk ((ι ≫ f) z)))
      = maximalIdeal (Z.presheaf.stalk z) := by
  classical
  subst hx
  -- the fibre stalk as the quotient of `𝒪_{X, ι z}` by the extended maximal ideal of the base
  have : IsLocalRing ((X.presheaf.stalk (ι z)) ⧸
      Ideal.map (f.stalkMap (ι z)).hom
        (maximalIdeal (S.presheaf.stalk (f (ι z))))) :=
    (quotientStalkEquivFiberStalk f (ι z)).symm.isLocalRing
  -- the hypothesis, read on that quotient
  have hmk : ∀ k, quotientStalkEquivFiberStalk f (ι z)
        (Ideal.Quotient.mk
          (Ideal.map (f.stalkMap (ι z)).hom
            (maximalIdeal (S.presheaf.stalk (f (ι z))))) (h k))
      = ((f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z))).hom
          ((f.fiberι_asFiber (ι z)).symm ▸ h k) := by
    intro k
    rw [quotientStalkEquivFiberStalk_mk, stalkCongr_hom_eq_cast]
  have hgenQ : Ideal.ofList
        (List.ofFn fun k => Ideal.Quotient.mk
          (Ideal.map (f.stalkMap (ι z)).hom
            (maximalIdeal (S.presheaf.stalk (f (ι z))))) (h k))
      = maximalIdeal ((X.presheaf.stalk (ι z)) ⧸
          Ideal.map (f.stalkMap (ι z)).hom
            (maximalIdeal (S.presheaf.stalk (f (ι z))))) := by
    have h1 := congrArg
      (Ideal.map (quotientStalkEquivFiberStalk f (ι z)).symm.toRingHom) hgen
    rw [Ideal.map_ofList, List.map_ofFn,
      IsLocalRing.map_maximalIdeal_of_surjective
        (quotientStalkEquivFiberStalk f (ι z)).symm.toRingHom
        (quotientStalkEquivFiberStalk f (ι z)).symm.surjective] at h1
    simp only [Function.comp_def] at h1
    refine Eq.trans (congrArg Ideal.ofList (congrArg List.ofFn (funext fun k => ?_))) h1
    rw [← hmk k]
    simp
  -- the composite stalk map factors through the extended ideal
  have hfac : Ideal.map ((ι ≫ f).stalkMap z).hom
        (maximalIdeal (S.presheaf.stalk ((ι ≫ f) z)))
      = Ideal.map (ι.stalkMap z).hom
        (Ideal.map (f.stalkMap (ι z)).hom
          (maximalIdeal (S.presheaf.stalk (f (ι z))))) := by
    rw [Ideal.map_map]
    refine congrArg (fun φ => Ideal.map φ
      (maximalIdeal (S.presheaf.stalk (f (ι z))))) ?_
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  rw [hfac]
  exact IsLocalRing.map_eq_maximalIdeal_of_ofList_quotient_eq_maximalIdeal _
    (IsLocalRing.map_maximalIdeal_le _) h (ι.stalkMap z).hom
    (ι.stalkMap_surjective z) hzero hgenQ

/-- **The local ring of the fibre of a slice cut by a minimal generating sequence of the fibre is
a field**, namely the residue field `κ(z)`.  This is the source's `𝒪_{T, v} = κ(v)` in the proof
of **Stacks 06N3**, read on the scheme-theoretic fibre rather than as an equality of ideals.

It is `Stacks.AlgebraicGeometry.map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk`
transported by `AlgebraicGeometry.quotientStalkEquivFiberStalk`, which presents the fibre stalk
as `𝒪_{Z, z} / 𝔪_{(ι ≫ f) z} 𝒪_{Z, z}`. -/
theorem isField_fiberStalk_comp_of_ofList_eq_maximalIdeal_fiberStalk
    (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S) (z : Z) (x : X) (hx : ι z = x)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (hzero : ∀ k, (ι.stalkMap z).hom (hx.symm ▸ h k) = 0)
    (hgen : Ideal.ofList
        (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ h k))
      = maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    IsField (((ι ≫ f).fiber ((ι ≫ f) z)).presheaf.stalk ((ι ≫ f).asFiber z)) :=
  ((Ideal.quotEquivOfEq
      (map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk
        ι f z x hx h hzero hgen).symm).trans
    (quotientStalkEquivFiberStalk (ι ≫ f) z)).symm.isField
      (Field.toIsField (IsLocalRing.ResidueField (Z.presheaf.stalk z)))

end Stacks.AlgebraicGeometry

end
