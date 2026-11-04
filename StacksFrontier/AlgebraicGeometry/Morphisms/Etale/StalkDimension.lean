module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Étale morphisms preserve the dimension of local rings and the transcendence degree of points

Let `g : V' ⟶ V` be an étale morphism of schemes, `v' ∈ V'` a point and `v = g(v')`. Then:

* the residue field extension `κ(v) ⟶ κ(v')` is finite separable, so for every morphism
  `V ⟶ S`, with `s` the image of `v`, the transcendence degrees
  `trdeg_{κ(s)} κ(v')` and `trdeg_{κ(s)} κ(v)` agree;
* if `V` is locally Noetherian, the local rings have the same dimension,
  `dim 𝒪_{V', v'} = dim 𝒪_{V, v}`.

The second is the dimension formula for a flat local homomorphism of Noetherian local rings
`R ⟶ S` (Stacks 00ON): `dim S = dim R + dim S/𝔪_R S`. For an unramified local homomorphism
`𝔪_R S = 𝔪_S`, so the closed fibre is a field and has dimension `0`. Together the two equalities
give `trdeg_{κ(s)} κ(v') + 2 dim 𝒪_{V', v'} = trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v}`, which is the
invariance of the bound `d_V` of Stacks 0DC6 under étale maps.

## Main results

* `ringKrullDim_eq_of_flat_of_map_maximalIdeal`: a flat local homomorphism `R ⟶ S` of Noetherian
  local rings with `𝔪_R S = 𝔪_S` has `dim S = dim R`.
* `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_of_formallyUnramified`: a flat, formally
  unramified morphism locally of finite type into a locally Noetherian scheme (for instance an
  étale one) preserves the dimension of local rings.
* `AlgebraicGeometry.Scheme.Hom.trdeg_residueField_eq_of_formallyUnramified`: a formally
  unramified morphism locally of finite type (for instance an étale one) preserves the
  transcendence degree of residue fields over any base.

## Implementation notes

The two equalities are stated separately rather than as the single combined equality: the
transcendence degree is a cardinal and the Krull dimension an element of `WithBot ℕ∞`, and the
separate equalities are the stronger statement. The hypotheses are those the proofs use: étale is
flat, formally unramified and locally of finite type, and the Noetherian hypothesis is needed on
`V` only (it then holds on `V'`).

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public section

open IsLocalRing CategoryTheory

/-- **Stacks 00ON, for an unramified closed fibre.** A flat local homomorphism `R ⟶ S` of
Noetherian local rings with `𝔪_R S = 𝔪_S` does not change the Krull dimension: the closed fibre
`S/𝔪_R S` is a field, of dimension `0`. -/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  have : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal S)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at key
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, key]

namespace AlgebraicGeometry.Scheme.Hom

/-- **Étale morphisms preserve the dimension of local rings.** Let `g : V' ⟶ V` be flat, formally
unramified and locally of finite type (for instance étale), with `V` locally Noetherian. Then
`dim 𝒪_{V', v'} = dim 𝒪_{V, g(v')}` for every `v' ∈ V'`. -/
theorem ringKrullDim_stalk_eq_of_formallyUnramified {V' V : Scheme} (g : V' ⟶ V) [Flat g]
    [FormallyUnramified g] [LocallyOfFiniteType g] [IsLocallyNoetherian V] (v' : V') :
    ringKrullDim (V'.presheaf.stalk v') = ringKrullDim (V.presheaf.stalk (g.base v')) := by
  have : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian g
  let := (g.stalkMap v').hom.toAlgebra
  have : IsLocalHom (algebraMap (V.presheaf.stalk (g.base v')) (V'.presheaf.stalk v')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap v').hom)
  have : Module.Flat (V.presheaf.stalk (g.base v')) (V'.presheaf.stalk v') :=
    Flat.stalkMap g v'
  have : Algebra.FormallyUnramified (V.presheaf.stalk (g.base v')) (V'.presheaf.stalk v') :=
    FormallyUnramified.stalkMap g v'
  have : Algebra.EssFiniteType (V.presheaf.stalk (g.base v')) (V'.presheaf.stalk v') :=
    LocallyOfFiniteType.stalkMap g v'
  exact ringKrullDim_eq_of_flat_of_map_maximalIdeal Algebra.FormallyUnramified.map_maximalIdeal

/-- **Étale morphisms preserve transcendence degrees of points.** Let `g : V' ⟶ V` be formally
unramified and locally of finite type (for instance étale) and `f : V ⟶ S` any morphism. For
`v' ∈ V'`, with `v = g(v')` and `s = f(v)`, the residue field `κ(v')` is a finite separable
extension of `κ(v)`, so `trdeg_{κ(s)} κ(v') = trdeg_{κ(s)} κ(v)`; here `κ(v')` is a
`κ(s)`-algebra through `κ(s) ⟶ κ(v) ⟶ κ(v')`. -/
theorem trdeg_residueField_eq_of_formallyUnramified {S V' V : Scheme} (f : V ⟶ S) (g : V' ⟶ V)
    [FormallyUnramified g] [LocallyOfFiniteType g] (v' : V') :
    letI := (f.residueFieldMap (g.base v')).hom.toAlgebra
    letI := ((g.residueFieldMap v').hom.comp (f.residueFieldMap (g.base v')).hom).toAlgebra
    Algebra.trdeg (S.residueField (f.base (g.base v'))) (V'.residueField v') =
      Algebra.trdeg (S.residueField (f.base (g.base v'))) (V.residueField (g.base v')) := by
  let := (f.residueFieldMap (g.base v')).hom.toAlgebra
  let := ((g.residueFieldMap v').hom.comp (f.residueFieldMap (g.base v')).hom).toAlgebra
  let := (g.residueFieldMap v').hom.toAlgebra
  have : IsScalarTower (S.residueField (f.base (g.base v'))) (V.residueField (g.base v'))
      (V'.residueField v') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := trdeg_add_eq (S.residueField (f.base (g.base v'))) (V.residueField (g.base v'))
    (A := V'.residueField v')
  rw [trdeg_eq_zero (R := V.residueField (g.base v')), add_zero] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Hom

end
