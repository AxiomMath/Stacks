module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullbackCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# The functoriality of the Laurent algebra in its invertible module is natural in the base

Let `T` be a scheme and `L`, `L'` invertible `𝒪_T`-modules.
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentCongr.lean` builds from an
isomorphism `e : L ≅ L'` the degreewise comparison
`...LaurentCongr.congrIso e n : L^{⊗ n} ≅ (L')^{⊗ n}` of the integral tensor powers of Tag 01CU,
as data with a successor law. This file proves the two laws of that comparison that no file of
this directory had: it is **functorial in the module** and it is **natural in the base scheme**.

## The two laws

* `...LaurentCongr.congrIso_trans`: `congrIso (e₁ ≪≫ e₂) n = congrIso e₁ n ≪≫ congrIso e₂ n`.
* `...LaurentCongr.congrIso_laurentPullback`: for `k : T' ⟶ T` the square

      k^*(L^{⊗ n}) ──k^*(congrIso e n)──> k^*((L')^{⊗ n})
            │                                   │
            │ the comparison along k             │ the comparison along k
            v                                   v
      (k^*L)^{⊗ n} ──congrIso (k^*e) n──> (k^*L')^{⊗ n}

  commutes, the horizontal below it being the comparison attached to the inverse image of `e`.

Neither can be read off the degree-zero and degree-one values: `congrIso` is a two-sided
recursion on `ℤ` and the only equations available about it are `...LaurentCongr.congrIso_zero`
and the successor law `...LaurentCongr.congrIso_succIso`. So each law is the same two-sided
induction as `...LaurentCongr.congrIso_mul` and `...LaurentComposition.pieceIso_comp`: upwards by
the successor laws, downwards by cancelling a whiskering by an invertible module, which is
faithful.

## What they were missing from

`...RelativeProjQcohSheaf.laurentPullbackCongrIso` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentPullbackCongr.lean` is the chart
comparison `g^*(L^{⊗ i}) ≅ (L')^{⊗ i}` along which a glueing argument for the functor `F_d` of
Section 01NS transports the map `ψ` of a quadruple. Comparing two charts over a common
refinement needs its **composition law**, and that law has two halves. One is the composition law
`...RelativeProjQcohSheaf.laurentPullback_comp` of the comparison of the integral tensor powers.
The other is the pair above: the chart comparison is `...RelativeProjQcohSheaf.laurentPullback`
followed by `congrIso`, so moving an inverse image across it moves an inverse image across
`congrIso` — which is the naturality in the base — and then composes two comparisons attached to
two different isomorphisms of invertible modules — which is the functoriality in the module.
Three modules of this directory record the absence of the first:
`...RelativeProjQcohSheaf.LaurentPullbackCongr`, `...RelativeProjQcohSheaf.QuadrupleChartGlue`
and `...RelativeProjQcohSheaf.ZariskiAmalgamation`.

## Main definitions

* `...LaurentCongr.pullbackCongrIso`: the inverse image of an isomorphism of invertible modules,
  ascribed at the `...LaurentPullback.pullbackModule` spelling so that instance search sees both
  modules as inverse images and hence finds their invertibility.
* `...RelativeProjQcohSheaf.compCongrIso`: the identification `(k ≫ a)^*L ≅ k^*(L')` that a
  glueing argument has over a refinement of a chart, where it holds the chart module of the
  chart and no third module.

## Main results

* `...LaurentCongr.congrIso_trans_hom` and `...LaurentCongr.congrIso_trans`: **the comparison is
  functorial in the invertible module.**
* `...LaurentCongr.congrIso_refl_hom` and `...LaurentCongr.congrIso_refl`: the comparison
  attached to the identity is the identity.
* `...LaurentCongr.congrIso_symm`: consequently the comparison attached to `e.symm` **is** the
  inverse of the one attached to `e`. The implementation notes of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentAlgebraCongr.lean` record that this
  identification was a further induction nothing had needed.
* `...LaurentCongr.congrIso_laurentPullback`: **the comparison is natural in the base scheme**,
  at the `...RelativeProjQcohSheaf.laurentPullback` spelling of the comparison of the integral
  tensor powers that the map `ψ` of a quadruple is written with.
* `...RelativeProjQcohSheaf.laurentPullbackCongrIso_comp`: **the composition law for the chart
  comparison** — the inverse image along `k` of the chart comparison along `a`, followed by the
  chart comparison along `k`, is the chart comparison along `k ≫ a`, through the contraction of
  the iterated inverse image. The relation between the three identifications of the invertible
  modules is a hypothesis rather than a choice, so the law applies to whichever composite a
  glueing argument has produced.
* `...RelativeProjQcohSheaf.laurentPullbackCongrIso_pullback`: that law at the identification
  `...RelativeProjQcohSheaf.compCongrIso`, which is the form a glueing argument meets it in — and
  where the third chart comparison collapses to the comparison of the integral tensor powers by
  `...LaurentCongr.congrIso_refl_hom`.

## Implementation notes

Each induction is split into a left-hand and a right-hand lemma, both cut down to the degree-`n`
statement whiskered by the module the recursion lowers the degree against, exactly as
`...LaurentComposition.compCompat_lhs` and `compCompat_rhs` are. That is what lets the downward
step cancel the two isomorphisms and then appeal to the faithfulness of the whiskering.

In degree zero the three Laurent algebras involved have the structure sheaf as their degree-zero
piece *on the nose*, so an identity morphism of one is an identity morphism of another by `rfl`
and not syntactically; a goal mentioning two of them is not type-correct at `implicit`
transparency and `rw` refuses it, reporting a missing pattern rather than the cause. Every
degree-zero step below is therefore a term built from `Eq.trans` and `congrArg`, which is the cure
this directory prescribes.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### The comparison is functorial in the invertible module -/

/-- Two-sided induction on `ℤ` out of `0`, from the upward and the downward step. -/
private theorem int_induction_two_sided {p : ℤ → Prop} (h0 : p 0) (hsucc : ∀ n, p n → p (n + 1))
    (hpred : ∀ n, p (n + 1) → p n) (n : ℤ) : p n := by
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hsucc i ih
  | pred i ih => exact hpred _ (by rwa [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring])

/-- Whiskering on the right by an invertible module is faithful. -/
private theorem eq_of_whiskerRight_eq {T : Scheme.{u}}
    {X Y P : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) P]
    {f g : X ⟶ Y} (h : f ▷ P = g ▷ P) : f = g := by
  refine ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj P).map_injective ?_
  exact (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) f P).trans
    (h.trans (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) g P).symm)

section Trans

variable {T : Scheme.{u}}
  {M N P : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) N]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) P]
  (e₁ : M ≅ N) (e₂ : N ≅ P)

/-- **The composition law in degree `n`**: composing the comparisons attached to `e₁` and to `e₂`
is the comparison attached to their composite. -/
abbrev TransCompat (n : ℤ) : Prop :=
  (congrIso e₁ n).hom ≫ (congrIso e₂ n).hom = (congrIso (e₁ ≪≫ e₂) n).hom

/-- **The composition law in degree `0`**, where all three comparisons are the identity of the
structure sheaf. -/
theorem transCompat_zero : TransCompat e₁ e₂ 0 :=
  have h₁ : (congrIso e₁ 0).hom = CategoryStruct.id ((laurent M).piece 0) :=
    congrArg Iso.hom (congrIso_zero e₁)
  have h₂ : (congrIso e₂ 0).hom = CategoryStruct.id ((laurent N).piece 0) :=
    congrArg Iso.hom (congrIso_zero e₂)
  have h₃ : (congrIso (e₁ ≪≫ e₂) 0).hom = CategoryStruct.id ((laurent M).piece 0) :=
    congrArg Iso.hom (congrIso_zero (e₁ ≪≫ e₂))
  (congrArg (fun z => z ≫ (congrIso e₂ 0).hom) h₁).trans
    ((Category.id_comp ((congrIso e₂ 0).hom)).trans (h₂.trans h₃.symm))

/-- **The left-hand side of the degree-`(n + 1)` law**, cut down by the successor comparison to
its degree-`n` counterpart whiskered by `P`. The inputs are the successor law of the comparison
for `e₁` and for `e₂` and the exchange law for whiskerings. -/
theorem transCompat_lhs (n : ℤ) :
    (succIso M n).hom ≫ ((congrIso e₁ (n + 1)).hom ≫ (congrIso e₂ (n + 1)).hom) =
      ((laurent M).piece n ◁ (e₁.hom ≫ e₂.hom)) ≫
        (((congrIso e₁ n).hom ≫ (congrIso e₂ n).hom) ▷ P) ≫ (succIso P n).hom := by
  rw [← Category.assoc, congrIso_succIso]
  simp only [Category.assoc]
  rw [congrIso_succIso e₂ n, ← whisker_exchange_assoc (congrIso e₁ n).hom e₂.hom]
  simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
    Category.assoc]

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) N] in
/-- **The right-hand side of the degree-`(n + 1)` law**, cut down the same way. This is the
successor law of the comparison attached to the composite. -/
theorem transCompat_rhs (n : ℤ) :
    (succIso M n).hom ≫ (congrIso (e₁ ≪≫ e₂) (n + 1)).hom =
      ((laurent M).piece n ◁ (e₁.hom ≫ e₂.hom)) ≫
        ((congrIso (e₁ ≪≫ e₂) n).hom ▷ P) ≫ (succIso P n).hom := by
  rw [congrIso_succIso (e₁ ≪≫ e₂) n]
  rfl

/-- **The inductive step, upwards**: the law in degree `n` gives it in degree `n + 1`. -/
theorem transCompat_succ {n : ℤ} (h : TransCompat e₁ e₂ n) : TransCompat e₁ e₂ (n + 1) := by
  refine (Iso.cancel_iso_hom_left (succIso M n) _ _).mp ?_
  rw [transCompat_lhs, transCompat_rhs, h]

/-- **The inductive step, downwards**: the law in degree `n + 1` gives it in degree `n`. This is
the direction that reaches the negative degrees, and it is where the invertibility of `P` is
used: the two sides in degree `n` become equal after tensoring on the right by `P`, and tensoring
by an invertible module is an equivalence, hence faithful. -/
theorem transCompat_of_succ {n : ℤ} (h : TransCompat e₁ e₂ (n + 1)) : TransCompat e₁ e₂ n := by
  have h2 : (succIso M n).hom ≫ ((congrIso e₁ (n + 1)).hom ≫ (congrIso e₂ (n + 1)).hom) =
      (succIso M n).hom ≫ (congrIso (e₁ ≪≫ e₂) (n + 1)).hom :=
    congrArg (fun z => (succIso M n).hom ≫ z) h
  rw [transCompat_lhs, transCompat_rhs] at h2
  have h3 := (Iso.cancel_iso_hom_left
    (MonoidalCategory.whiskerLeftIso ((laurent M).piece n) (e₁ ≪≫ e₂)) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_right _ _ (succIso P n)).mp h3
  exact eq_of_whiskerRight_eq h4

/-- **The degreewise comparison of the integral tensor powers is functorial in the invertible
module**: the comparison attached to a composite of two isomorphisms is the composite of the two
comparisons, in **every** integral degree.

The induction is two-sided out of degree `0`: upwards by `transCompat_succ`, downwards by
`transCompat_of_succ`. -/
theorem congrIso_trans_hom (n : ℤ) :
    (congrIso e₁ n).hom ≫ (congrIso e₂ n).hom = (congrIso (e₁ ≪≫ e₂) n).hom := by
  exact int_induction_two_sided (p := TransCompat e₁ e₂) (transCompat_zero e₁ e₂)
    (fun _ => transCompat_succ e₁ e₂) (fun _ => transCompat_of_succ e₁ e₂) n

/-- `...LaurentCongr.congrIso_trans_hom` read as an equality of isomorphisms. -/
theorem congrIso_trans (n : ℤ) :
    congrIso (e₁ ≪≫ e₂) n = congrIso e₁ n ≪≫ congrIso e₂ n :=
  Iso.ext (congrIso_trans_hom e₁ e₂ n).symm

end Trans

section Refl

variable {T : Scheme.{u}}
  (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]

/-- **The identity law in degree `n`**: the comparison attached to the identity of `M` is the
identity of the degree-`n` piece. -/
abbrev ReflCompat (n : ℤ) : Prop :=
  (congrIso (Iso.refl M) n).hom = CategoryStruct.id ((laurent M).piece n)

/-- **The identity law in degree `0`**, which is `...LaurentCongr.congrIso_zero`. -/
theorem reflCompat_zero : ReflCompat M 0 :=
  congrArg Iso.hom (congrIso_zero (Iso.refl M))

/-- **The left-hand side of the degree-`(n + 1)` identity law**, cut down by the successor
comparison: the comparison attached to the identity whiskers the degree-`n` one by `M`. -/
theorem reflCompat_lhs (n : ℤ) :
    (succIso M n).hom ≫ (congrIso (Iso.refl M) (n + 1)).hom =
      ((congrIso (Iso.refl M) n).hom ▷ M) ≫ (succIso M n).hom := by
  rw [congrIso_succIso, Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **The right-hand side of the degree-`(n + 1)` identity law**, cut down the same way. -/
theorem reflCompat_rhs (n : ℤ) :
    (succIso M n).hom ≫ CategoryStruct.id ((laurent M).piece (n + 1)) =
      (CategoryStruct.id ((laurent M).piece n) ▷ M) ≫ (succIso M n).hom := by
  rw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]

/-- **The inductive step, upwards**: the identity law in degree `n` gives it in degree `n + 1`. -/
theorem reflCompat_succ {n : ℤ} (h : ReflCompat M n) : ReflCompat M (n + 1) := by
  refine (Iso.cancel_iso_hom_left (succIso M n) _ _).mp ?_
  rw [reflCompat_lhs, reflCompat_rhs, h]

/-- **The inductive step, downwards**: the identity law in degree `n + 1` gives it in degree `n`,
by the faithfulness of tensoring on the right by the invertible module `M`. -/
theorem reflCompat_of_succ {n : ℤ} (h : ReflCompat M (n + 1)) : ReflCompat M n := by
  have h2 : (succIso M n).hom ≫ (congrIso (Iso.refl M) (n + 1)).hom =
      (succIso M n).hom ≫ CategoryStruct.id ((laurent M).piece (n + 1)) :=
    congrArg (fun z => (succIso M n).hom ≫ z) h
  rw [reflCompat_lhs, reflCompat_rhs] at h2
  have h3 := (Iso.cancel_iso_hom_right _ _ (succIso M n)).mp h2
  exact eq_of_whiskerRight_eq h3

/-- **The comparison attached to the identity is the identity**, in every integral degree. The
induction is the two-sided one of `...LaurentCongr.congrIso_trans_hom`. -/
theorem congrIso_refl_hom (n : ℤ) :
    (congrIso (Iso.refl M) n).hom = CategoryStruct.id ((laurent M).piece n) := by
  exact int_induction_two_sided (p := ReflCompat M) (reflCompat_zero M)
    (fun _ => reflCompat_succ M) (fun _ => reflCompat_of_succ M) n

/-- `...LaurentCongr.congrIso_refl_hom` read as an equality of isomorphisms. -/
theorem congrIso_refl (n : ℤ) : congrIso (Iso.refl M) n = Iso.refl ((laurent M).piece n) :=
  Iso.ext (congrIso_refl_hom M n)

end Refl

section Symm

variable {T : Scheme.{u}}
  {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) N]

/-- **The comparison attached to `e.symm` is the inverse of the comparison attached to `e`.** The
comparison attached to `e.symm` is a second recursion on the degree, and the implementation notes
of `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentAlgebraCongr.lean` record that
identifying the two was a further induction nothing had needed. It is
`...LaurentCongr.congrIso_trans_hom` and `...LaurentCongr.congrIso_refl_hom` together. -/
theorem congrIso_symm_hom (e : M ≅ N) (n : ℤ) :
    (congrIso e.symm n).hom = (congrIso e n).inv := by
  have h := congrIso_trans_hom e.symm e n
  rw [Iso.symm_self_id, congrIso_refl_hom] at h
  exact ((Iso.eq_comp_inv (congrIso e n)).mpr h).trans (Category.id_comp _)

/-- `...LaurentCongr.congrIso_symm_hom` read as an equality of isomorphisms. -/
theorem congrIso_symm (e : M ≅ N) (n : ℤ) : congrIso e.symm n = (congrIso e n).symm :=
  Iso.ext (congrIso_symm_hom e n)

end Symm

/-! ### The comparison is natural in the base scheme -/

section Naturality

variable {T' T : Scheme.{u}} (k : T' ⟶ T)
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
  (e : L ≅ L')

/-- **The inverse image of an isomorphism of invertible modules**, with its source and target
ascribed at the `...LaurentPullback.pullbackModule` spelling rather than as values of a functor.
The ascription is what lets instance search see the two modules as inverse images, and hence find
their invertibility. -/
abbrev pullbackCongrIso : pullbackModule k L ≅ pullbackModule k L' :=
  (pullbackFunctor (ringedSpaceHom k)).mapIso e

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L'] in
/-- The inverse image of an isomorphism acts on morphisms as the inverse image of its forward
component. -/
theorem pullbackCongrIso_hom :
    (pullbackCongrIso k e).hom = (pullbackFunctor (ringedSpaceHom k)).map e.hom :=
  rfl

/-- **The naturality square in degree `n`**: taking the inverse image of the comparison attached
to `e` and then comparing the integral tensor powers along `k` agrees with comparing along `k`
and then applying the comparison attached to the inverse image of `e`. -/
abbrev NatCompat (n : ℤ) : Prop :=
  (pullbackFunctor (ringedSpaceHom k)).map (congrIso e n).hom ≫ laurentPullback k L' n =
    laurentPullback k L n ≫ (congrIso (pullbackCongrIso k e) n).hom

/-- **The naturality square in degree `0`.** Both comparisons attached to an isomorphism are the
identity there, and both comparisons of the integral tensor powers are the structure-sheaf
comparison of Tag 01CD (`...RelativeProjQcohSheaf.laurentPullback_zero`). -/
theorem natCompat_zero : NatCompat k e 0 :=
  have hz : laurentPullback k L' 0 = laurentPullback k L 0 :=
    (laurentPullback_zero k L').trans (laurentPullback_zero k L).symm
  have hmap : (pullbackFunctor (ringedSpaceHom k)).map (congrIso e 0).hom =
      CategoryStruct.id ((pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 0)) :=
    CategoryTheory.Functor.map_id _ _
  have hcg : (congrIso (pullbackCongrIso k e) 0).hom =
      CategoryStruct.id ((laurent (pullbackModule k L)).piece 0) :=
    congrArg Iso.hom (congrIso_zero (pullbackCongrIso k e))
  have hl : (pullbackFunctor (ringedSpaceHom k)).map (congrIso e 0).hom ≫
      laurentPullback k L' 0 = laurentPullback k L' 0 :=
    (congrArg (fun z => z ≫ laurentPullback k L' 0) hmap).trans
      (Category.id_comp (laurentPullback k L' 0))
  have hr : laurentPullback k L 0 ≫ (congrIso (pullbackCongrIso k e) 0).hom =
      laurentPullback k L 0 :=
    (congrArg (fun z => laurentPullback k L 0 ≫ z) hcg).trans
      (Category.comp_id (laurentPullback k L 0))
  hl.trans (hz.trans hr.symm)

/-- **The left-hand side of the degree-`(n + 1)` square**, cut down by the successor comparison
to its degree-`n` counterpart whiskered by `k^*L`. The inputs are the successor law of
`...LaurentCongr.congrIso`, the successor law
`...RelativeProjQcohSheaf.laurentPullback_succIso` of the comparison of the integral tensor
powers and the naturality of the comparison of Tag 01CD in each variable. -/
theorem natCompat_lhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        ((pullbackFunctor (ringedSpaceHom k)).map (congrIso e (n + 1)).hom ≫
          laurentPullback k L' (n + 1)) =
      pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L ≫
        (((pullbackFunctor (ringedSpaceHom k)).map (congrIso e n).hom ≫
            laurentPullback k L' n) ▷ pullbackModule k L) ≫
          ((laurent (pullbackModule k L')).piece n ◁
              (pullbackFunctor (ringedSpaceHom k)).map e.hom) ≫
            (succIso (pullbackModule k L') n).hom := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, congrIso_succIso,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [laurentPullback_succIso k L' n,
    reassoc_of% (pullbackTensorComparison_naturality_left (ringedSpaceHom k)
      (B := L') (congrIso e n).hom),
    reassoc_of% (pullbackTensorComparison_naturality_right (ringedSpaceHom k)
      (A := (laurent L).piece n) e.hom)]
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight]
  rw [whisker_exchange_assoc ((pullbackFunctor (ringedSpaceHom k)).map (congrIso e n).hom)
      ((pullbackFunctor (ringedSpaceHom k)).map e.hom),
    whisker_exchange_assoc (laurentPullback k L' n)
      ((pullbackFunctor (ringedSpaceHom k)).map e.hom)]

/-- **The right-hand side of the degree-`(n + 1)` square**, cut down the same way. The inputs are
the successor law of the comparison of the integral tensor powers along `k` and the successor law
of the comparison attached to the inverse image of `e`. -/
theorem natCompat_rhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        (laurentPullback k L (n + 1) ≫ (congrIso (pullbackCongrIso k e) (n + 1)).hom) =
      pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L ≫
        ((laurentPullback k L n ≫ (congrIso (pullbackCongrIso k e) n).hom) ▷
            pullbackModule k L) ≫
          ((laurent (pullbackModule k L')).piece n ◁
              (pullbackFunctor (ringedSpaceHom k)).map e.hom) ≫
            (succIso (pullbackModule k L') n).hom := by
  rw [← Category.assoc, laurentPullback_succIso k L n]
  simp only [Category.assoc]
  rw [congrIso_succIso (pullbackCongrIso k e) n, pullbackCongrIso_hom]
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight]
  rw [whisker_exchange_assoc (congrIso (pullbackCongrIso k e) n).hom
    ((pullbackFunctor (ringedSpaceHom k)).map e.hom)]

/-- **The inductive step, upwards**: the square in degree `n` gives it in degree `n + 1`. -/
theorem natCompat_succ {n : ℤ} (h : NatCompat k e n) : NatCompat k e (n + 1) := by
  refine (Iso.cancel_iso_hom_left
    ((pullbackFunctor (ringedSpaceHom k)).mapIso (succIso L n)) _ _).mp ?_
  change (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ _ =
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ _
  rw [natCompat_lhs, natCompat_rhs, h]

/-- **The inductive step, downwards**: the square in degree `n + 1` gives it in degree `n`. This
is the direction that reaches the negative degrees, and it is where the invertibility of `k^*L`
is used: the two sides in degree `n` become equal after tensoring on the right by that module,
and tensoring by an invertible module is an equivalence, hence faithful. -/
theorem natCompat_of_succ {n : ℤ} (h : NatCompat k e (n + 1)) : NatCompat k e n := by
  have h2 : (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        ((pullbackFunctor (ringedSpaceHom k)).map (congrIso e (n + 1)).hom ≫
          laurentPullback k L' (n + 1)) =
      (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        (laurentPullback k L (n + 1) ≫ (congrIso (pullbackCongrIso k e) (n + 1)).hom) :=
    congrArg (fun z => (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ z) h
  rw [natCompat_lhs, natCompat_rhs] at h2
  have h3 := (Iso.cancel_iso_hom_left (asIso (pullbackTensorComparison (ringedSpaceHom k)
    ((laurent L).piece n) L)) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_right _ _
    (MonoidalCategory.whiskerLeftIso ((laurent (pullbackModule k L')).piece n)
        (pullbackCongrIso k e) ≪≫
      succIso (pullbackModule k L') n)).mp h3
  exact eq_of_whiskerRight_eq h4

/-- **The degreewise comparison of the integral tensor powers induced by an isomorphism of
invertible modules is natural in the base scheme**, in **every** integral degree: the inverse
image along `k : T' ⟶ T` of the comparison attached to `e : L ≅ L'`, read through the comparison
of the integral tensor powers along `k`, is the comparison attached to the inverse image of `e`.

This is the law whose absence `...RelativeProjQcohSheaf.LaurentPullbackCongr`,
`...RelativeProjQcohSheaf.QuadrupleChartGlue` and `...RelativeProjQcohSheaf.ZariskiAmalgamation`
each record. The induction is two-sided out of degree `0`: upwards by `natCompat_succ`, downwards
by `natCompat_of_succ`. -/
theorem congrIso_laurentPullback (n : ℤ) : NatCompat k e n := by
  exact int_induction_two_sided (p := NatCompat k e) (natCompat_zero k e)
    (fun _ => natCompat_succ k e) (fun _ => natCompat_of_succ k e) n

end Naturality

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **The composition law for the chart comparison
`...RelativeProjQcohSheaf.laurentPullbackCongrIso`**: for `a : V ⟶ T` and `k : W ⟶ V`, the
inverse image along `k` of the chart comparison along `a`, followed by the chart comparison along
`k`, is the chart comparison along `k ≫ a`, read through the contraction
`...LaurentComposition.compCmp` of the iterated inverse image.

The three identifications of the invertible modules — `e : a^*L ≅ L'`, `c : k^*L' ≅ L''` and
`e'' : (k ≫ a)^*L ≅ L''` — are related by the hypothesis `he` rather than by a choice, so the law
applies to whichever composite a glueing argument has produced.

The inputs are the composition law `...RelativeProjQcohSheaf.laurentPullback_comp` of the
comparison of the integral tensor powers and the two laws of `...LaurentCongr.congrIso` proved
above: its naturality in the base scheme (`...LaurentCongr.congrIso_laurentPullback`) and its
functoriality in the invertible module (`...LaurentCongr.congrIso_trans_hom`). This is the law a
glueing argument needs in order to compare two charts over a common refinement. -/
theorem laurentPullbackCongrIso_comp {W V T : Scheme.{u}} (a : V ⟶ T) (k : W ⟶ V)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V.toRingedSpace.presheaf (isSheafStruct V) L']
    {L'' : SheafOfModules.{u} (structureRingSheaf W.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible W.toRingedSpace.presheaf (isSheafStruct W) L'']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (c : (pullbackFunctor (ringedSpaceHom k)).obj L' ≅ L'')
    (e'' : (pullbackFunctor (ringedSpaceHom (k ≫ a))).obj L ≅ L'')
    (he : (compCmp k a L).hom ≫ e''.hom =
      (pullbackFunctor (ringedSpaceHom k)).map e.hom ≫ c.hom)
    (i : ℤ) :
    (compCmp k a ((laurent L).piece i)).hom ≫
        (laurentPullbackCongrIso (k ≫ a) L e'' i).hom =
      (pullbackFunctor (ringedSpaceHom k)).map (laurentPullbackCongrIso a L e i).hom ≫
        (laurentPullbackCongrIso k L' c i).hom := by
  have hiso : compCmp k a L ≪≫ e'' = pullbackCongrIso k e ≪≫ c := Iso.ext he
  have htrans : (congrIso (compCmp k a L) i).hom ≫ (congrIso e'' i).hom =
      (congrIso (pullbackCongrIso k e) i).hom ≫ (congrIso c i).hom :=
    (congrIso_trans_hom (compCmp k a L) e'' i).trans
      ((congrArg (fun z => (congrIso z i).hom) hiso).trans
        (congrIso_trans_hom (pullbackCongrIso k e) c i).symm)
  have hnat := congrIso_laurentPullback k e i
  have hcomp := laurentPullback_comp a k L i
  simp only [laurentPullbackCongrIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, ← htrans, reassoc_of% hcomp]

/-- **The identification of the inverse image of a chart module that the composition law for the
chart comparison is taken at**: `(k ≫ a)^*L ≅ k^*(L')`, the contraction of the iterated inverse
image read backwards followed by the inverse image of the given identification `e : a^*L ≅ L'`.
This is the identification a glueing argument has over a refinement of a chart: it holds the
chart module of the member, not a third module on the refinement. -/
abbrev compCongrIso {W V T : Scheme.{u}} (a : V ⟶ T) (k : W ⟶ V)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L') :
    (pullbackFunctor (ringedSpaceHom (k ≫ a))).obj L ≅
      (pullbackFunctor (ringedSpaceHom k)).obj L' :=
  (compCmp k a L).symm ≪≫ (pullbackFunctor (ringedSpaceHom k)).mapIso e

/-- **The chart comparison moves across a refinement of a chart**: the inverse image along `k` of
the chart comparison along `a`, followed by the comparison of the integral tensor powers along
`k`, is the chart comparison along `k ≫ a` taken at the identification
`...RelativeProjQcohSheaf.compCongrIso`.

This is `...RelativeProjQcohSheaf.laurentPullbackCongrIso_comp` with the third invertible module
taken to be the inverse image of the second and the third identification the identity, where the
functoriality `...LaurentCongr.congrIso_refl_hom` of the comparison collapses the chart comparison
along `k` to the comparison of the integral tensor powers. It is the form in which a glueing
argument for the functor `F_d` of Section 01NS meets the law: over a refinement of a chart it
holds the chart module of that chart and nothing else. -/
theorem laurentPullbackCongrIso_pullback {W V T : Scheme.{u}} (a : V ⟶ T) (k : W ⟶ V)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V.toRingedSpace.presheaf (isSheafStruct V) L']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L') (i : ℤ) :
    (compCmp k a ((laurent L).piece i)).hom ≫
        (laurentPullbackCongrIso (k ≫ a) L (compCongrIso a k L e) i).hom =
      (pullbackFunctor (ringedSpaceHom k)).map (laurentPullbackCongrIso a L e i).hom ≫
        laurentPullback k L' i := by
  have hrefl : (laurentPullbackCongrIso k L' (Iso.refl
      ((pullbackFunctor (ringedSpaceHom k)).obj L')) i).hom = laurentPullback k L' i :=
    (congrArg (fun z => laurentPullback k L' i ≫ z)
        (congrIso_refl_hom ((pullbackFunctor (ringedSpaceHom k)).obj L') i)).trans
      (Category.comp_id _)
  have he : (compCmp k a L).hom ≫ (compCongrIso a k L e).hom =
      (pullbackFunctor (ringedSpaceHom k)).map e.hom ≫
        (Iso.refl ((pullbackFunctor (ringedSpaceHom k)).obj L')).hom :=
    (Iso.hom_inv_id_assoc (compCmp k a L) _).trans (Category.comp_id _).symm
  exact (laurentPullbackCongrIso_comp a k L e
    (Iso.refl ((pullbackFunctor (ringedSpaceHom k)).obj L')) (compCongrIso a k L e) he i).trans
    (congrArg (fun z => (pullbackFunctor (ringedSpaceHom k)).map
      (laurentPullbackCongrIso a L e i).hom ≫ z) hrefl)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
