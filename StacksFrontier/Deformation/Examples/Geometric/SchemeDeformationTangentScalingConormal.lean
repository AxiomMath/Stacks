module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSelfMapIdealScaling
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationTangentSelfMapGroup

/-!
# The coordinate scaling of a first-order deformation, on the conormal sheaf

Let `X` be a scheme over a field `k` and `P` a choice of pushforwards for a point of its
deformation category. The scalar action of `c : k` on the `Inf` term of the sequence of
[Stacks Project, Tag 0E3V] is transport along `Deformation.tangentScaling`, the self-map `ε ↦ cε`
of the dual numbers under the base, and the morphism of total spaces that transport is taken
along is

`σ_c := (P.map (Deformation.tangentScaling c)).map`,

a self-arrow of the chosen first-order pushforward. This file computes what `σ_c` does to the
conormal sheaf of the special fibre: it is **multiplication by `c`**.

The computation has two halves, and the geometric one is already done. The general statement
`Deformation.Examples.conormalSelfMap_eq_smul` says that a self-arrow `φ` of a first-order
deformation whose base component scales a generator `t` of the maximal ideal of the base by
`c : A` induces multiplication by the residue of `c` on the conormal sections. What remains is to
produce that base datum for `Deformation.tangentScaling`, which is a computation in the dual
numbers and is what this file does.

## The transport along the equality of base objects

The base object of the chosen pushforward is *equal* to the dual numbers under the point's base —
that equality is the second component of `Deformation.ChosenPushforwardsAt.obj` — but it is not
that object syntactically, so `Deformation.tangentScaling` cannot be read on it directly. What
`CategoryTheory.IsHomLift.fac'` gives is a factorisation of the base component of `P.map` through
`eqToHom` of that equality, and `Deformation.Examples.exists_generator_of_eq` moves the base datum
across it by substituting the equality away. So the dual-number computation is performed once, at
the dual numbers themselves, and transported.

## Main results

* `Deformation.Examples.dualNumbersEquiv_snd`: the dual-number coordinate reads the infinitesimal
  component as `ULift.down` of it, the companion of `Deformation.dualNumbersEquiv_fst`.
* `Deformation.Examples.apply_eq_mul_of_fst_snd`: an element of a ring isomorphic to the dual
  numbers whose residue coordinate vanishes and whose infinitesimal coordinate is `c` is `c` times
  `ε`.
* `Deformation.Examples.exists_generator_of_eq`: transport of the base datum along an equality of
  objects of `𝒞_Λ`.
* `Deformation.Examples.exists_tangentScaling_base_generator`: **the base datum for
  `Deformation.tangentScaling`** — a generator of the maximal ideal of the base of the chosen
  first-order pushforward which the base component of `P.map (tangentScaling c)` multiplies by an
  element of residue `c`.
* `Deformation.Examples.conormalSelfMap_tangentScaling_eq_smul`: **the endomorphism of the
  conormal sections of the special fibre induced by `σ_c` is multiplication by `c`.**

## Implementation notes

The dual-number computation is done in `DualNumber k` rather than in the carrier of the object of
`𝒞_Λ`. The carrier *is* `TrivSqZeroExt k (ULift k)`, and the two readings of a coordinate,
`TrivSqZeroExt.fst` and `TrivSqZeroExt.snd`, apply to it directly — that is how
`Deformation.tangentScaling_right_hom_fst` and `Deformation.tangentScaling_right_hom_snd` are
stated. Its *ring structure*, however, is the one recorded in the object, which does not reduce to
`TrivSqZeroExt`'s at the transparency a `rw` of `TrivSqZeroExt.snd_mul` needs. So every product is
formed after transporting along `Deformation.dualNumbersEquiv`, where the type is a plain
`TrivSqZeroExt` and the multiplication lemmas apply; the transport is a ring isomorphism, so one
application of injectivity brings the conclusion back.

The square-zero hypothesis on the defining ideal is carried rather than discharged, as in
`Deformation.Examples.conormalSelfMap_eq_smul` and
`Deformation.Examples.ker_specialMap_pow_two_eq_bot`: it is a condition on the base object alone,
and `Deformation.Examples.maximalIdeal_artinianDualNumbers_sq_eq_bot` discharges it for the
dual-number object.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [local instance] deformationSpecialMap_isClosedImmersion

/-! ### The dual-number coordinate on the infinitesimal component -/

/-- **The dual-number coordinate of `𝒞_Λ` reads the infinitesimal component as `ULift.down` of
it.** `Deformation.dualNumbersEquiv` is the inverse of the lift `k[ε] ⟶ k[ε]` of
`Deformation.dualNumbersUp`, which is `ULift.up` on the infinitesimal component, so its inverse is
`ULift.down` there. This is the companion of `Deformation.dualNumbersEquiv_fst`. -/
theorem dualNumbersEquiv_snd (z : Deformation.artinianDualNumbers.{u, u, u} Λ k) :
    TrivSqZeroExt.snd (Deformation.dualNumbersEquiv.{u, u, u} (Λ := Λ) (k := k) z) =
      ULift.down (TrivSqZeroExt.snd z) :=
  congrArg (fun y : Deformation.artinianDualNumbers.{u, u, u} Λ k =>
      ULift.down (TrivSqZeroExt.snd y))
    ((AlgEquiv.ofBijective (Deformation.dualNumbersUp.{u, u, u} (Λ := Λ) (k := k))
      Deformation.dualNumbersUp_bijective.{u, u, u}).apply_symm_apply z)

/-- **An element of a ring isomorphic to the dual numbers with vanishing residue coordinate and
infinitesimal coordinate `c` is `c` times `ε`.** Both sides are determined by their two
coordinates, so the statement is `TrivSqZeroExt.ext` after transporting along the isomorphism;
the point of stating it for a ring isomorphism is that the product is then formed in
`DualNumber k`, where the coordinate formulae for a product apply. -/
theorem apply_eq_mul_of_fst_snd {B : Type u} [CommRing B] (e : B ≃+* DualNumber k)
    (c : k) {y w : B} (hy : e y = DualNumber.eps (R := k))
    (hfst : TrivSqZeroExt.fst (e w) = 0) (hsnd : TrivSqZeroExt.snd (e w) = c) :
    w = e.symm (TrivSqZeroExt.inl c) * y := by
  refine e.injective ?_
  rw [map_mul, e.apply_symm_apply, hy]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfst, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, DualNumber.fst_eps, mul_zero]
  · rw [hsnd, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      DualNumber.fst_eps, DualNumber.snd_eps, smul_eq_mul, mul_one, MulOpposite.op_zero,
      zero_smul, add_zero]

/-! ### Transport of the base datum along an equality of base objects -/

/-- **The base datum of a scaling self-map, transported along an equality of objects of `𝒞_Λ`.**
The datum is a generator of the maximal ideal, an element of residue `c`, and the equation saying
that the self-map multiplies the generator by that element; the transport substitutes the equality
away, after which the two `eqToHom`s are the identity. -/
theorem exists_generator_of_eq {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B) (g : B ⟶ B)
    (c : k) {t₀ c₀ : (B : Type u)}
    (ht₀ : IsLocalRing.maximalIdeal (B : Type u) = Ideal.span {t₀})
    (hres : Deformation.Artin.residueMap B c₀ = c) (hg : g.hom t₀ = c₀ * t₀) :
    ∃ t c' : (A : Type u),
      IsLocalRing.maximalIdeal (A : Type u) = Ideal.span {t} ∧
        Deformation.Artin.residueMap A c' = c ∧
        (eqToHom h ≫ g ≫ eqToHom h.symm).hom t = c' * t := by
  subst h
  refine ⟨t₀, c₀, ht₀, hres, ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact hg

/-! ### The base datum for the coordinate scaling -/

variable {X : Over (Spec (CommRingCat.of k))}

/-- **The base datum of `Deformation.tangentScaling` at the chosen first-order pushforward.**
There is a generator `t` of the maximal ideal of the base of the chosen first-order pushforward
and an element of residue `c` by which the base component of `P.map (tangentScaling c)` multiplies
it.

At the dual numbers themselves the generator is `ε`, the element is `c`, and the equation is the
coordinate computation `Deformation.tangentScaling_right_hom_fst` and
`Deformation.tangentScaling_right_hom_snd`: the scaling fixes the residue coordinate and
multiplies the infinitesimal one by `c`. The base object of the pushforward is only *equal* to the
dual numbers, so `CategoryTheory.IsHomLift.fac'` factors the base component through the `eqToHom`
of that equality and `Deformation.Examples.exists_generator_of_eq` carries the datum across. -/
theorem exists_tangentScaling_base_generator
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) (c : k) :
    ∃ t c' : ((firstOrderPushforward P).base : Type u),
      IsLocalRing.maximalIdeal ((firstOrderPushforward P).base : Type u) = Ideal.span {t} ∧
        Deformation.Artin.residueMap (firstOrderPushforward P).base c' = c ∧
        (P.map (tangentScaling
            (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
            (x := x₀) c)).base.hom t = c' * t := by
  let := residueAlgebra (x₀.base)
  set σ := tangentScaling (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
    (x := x₀) c
  set e : (dualNumbersUnder (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
        (x := x₀)).right ≃+* DualNumber k :=
    (Deformation.dualNumbersEquiv.{u, u, u} (Λ := (x₀.base : Type u)) (k := k)).toRingEquiv
      with he
  have hfst_e : ∀ v, TrivSqZeroExt.fst (e v) = TrivSqZeroExt.fst v := fun v =>
    Deformation.dualNumbersEquiv_fst.{u, u, u} (Λ := (x₀.base : Type u)) (k := k) v
  have hsnd_e : ∀ v, TrivSqZeroExt.snd (e v) = ULift.down (TrivSqZeroExt.snd v) := fun v =>
    dualNumbersEquiv_snd (Λ := (x₀.base : Type u)) (k := k) v
  have hfst : ∀ z, TrivSqZeroExt.fst (e.symm z) = TrivSqZeroExt.fst z := fun z => by
    rw [← hfst_e, e.apply_symm_apply]
  have hsnd : ∀ z, ULift.down (TrivSqZeroExt.snd (e.symm z)) = TrivSqZeroExt.snd z := fun z => by
    rw [← hsnd_e, e.apply_symm_apply]
  have hmul : σ.right.hom (e.symm DualNumber.eps) =
      e.symm (TrivSqZeroExt.inl c) * e.symm DualNumber.eps := by
    refine apply_eq_mul_of_fst_snd e c (e.apply_symm_apply _) ?_ ?_
    · rw [hfst_e, tangentScaling_right_hom_fst, hfst, DualNumber.fst_eps]
    · rw [hsnd_e, tangentScaling_right_hom_snd]
      change c * ULift.down (TrivSqZeroExt.snd (e.symm DualNumber.eps)) = _
      rw [hsnd, DualNumber.snd_eps, mul_one]
  have hres : Deformation.Artin.residueMap
      (dualNumbersUnder (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
        (x := x₀)).right (e.symm (TrivSqZeroExt.inl c)) = c := by
    change TrivSqZeroExt.fst (e.symm (TrivSqZeroExt.inl c)) = c
    rw [hfst, TrivSqZeroExt.fst_inl]
  have hbase : (P.map σ).base = eqToHom (P.obj (dualNumbersUnder
        (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀))).2 ≫
      σ.right ≫ eqToHom (P.obj (dualNumbersUnder
        (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀))).2.symm :=
    CategoryTheory.IsHomLift.fac'
      (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (f := σ.right) (φ := P.map σ)
  rw [hbase]
  exact exists_generator_of_eq _ _ c (maximalIdeal_eq_span_of_dualNumberRingEquiv e) hres hmul

/-! ### The coordinate scaling on the conormal sections -/

/-- **The endomorphism of the conormal sections of the special fibre induced by the coordinate
scaling is multiplication by the scalar.** For `c : k`, the self-arrow
`P.map (Deformation.tangentScaling c)` of the chosen first-order pushforward — the morphism of
total spaces the scalar action of the `Inf` term of [Stacks Project, Tag 0E3V] transports
along — induces on the conormal sections of the special fibre multiplication by the function `c`
determines on `X`.

This is `Deformation.Examples.conormalSelfMap_eq_smul` with its base datum supplied by
`Deformation.Examples.exists_tangentScaling_base_generator`. -/
theorem conormalSelfMap_tangentScaling_eq_smul
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀)
    (hsq : (firstOrderPushforward P).specialMap.ker ^ 2 = ⊥) (c : k)
    (V : (firstOrderPushforward P).scheme.Opens)
    (s : Γ(Stacks.Thickenings.conormalModules (firstOrderPushforward P).specialMap,
      (firstOrderPushforward P).specialMap ⁻¹ᵁ V)) :
    Stacks.Thickenings.conormalSelfMap hsq
        (P.map (tangentScaling
          (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
          (x := x₀) c)).special_compat V s =
      baseSection X.hom c ((firstOrderPushforward P).specialMap ⁻¹ᵁ V) • s := by
  obtain ⟨t, c', ht, hres, hb⟩ := exists_tangentScaling_base_generator P c
  rw [conormalSelfMap_eq_smul hsq _ ht hb V s, hres]

end Deformation.Examples

end
