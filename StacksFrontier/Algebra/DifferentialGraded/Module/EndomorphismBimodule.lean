module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyEndomorphism
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismDGA
import StacksCore.Tactic.EgaSgaAttribute

/-! # A differential graded module as a bimodule over its own endomorphism algebra

Let `(B, d)` be a differential graded algebra over a commutative ring `R` and let `Q` be a right
differential graded `B`-module. Its endomorphism differential graded algebra
`E = End(Q) = Hom_{Mod^{dg}_{(B,d)}}(Q, Q)` of Tag 09LE acts on `Q` on the left, tautologically:
a degree-`n` element of `E` *is* a degree-`n` homogeneous right `B`-linear endomorphism of `Q`,
so it acts by evaluation. That action is right `B`-linear by construction, so it makes `Q` a
differential graded `(E, B)`-bimodule in the sense of Tag 0FQJ.

This is the bimodule the converse direction of [Stacks, Tag 09S8] and the proof of
[Stacks, Tag 09SA] use: there one has a compact generator `P` of `D(B, d)`, replaces it by a
property-(P) resolution `Q`, and views `Q` as an `(End(Q), B)`-bimodule in order to apply
[Stacks, Tag 09S7].

## Main definitions

* `DifferentialGradedModule.homogeneousMapToCochain` and
  `DifferentialGradedModule.homogeneousMapToCochainₗ`: a homogeneous right `B`-linear map of
  degree `n`, read as a degree-`n` cochain of the underlying complexes, `R`-linearly in the map.
* `DifferentialGradedModule.endomorphismLeftAction`: the tautological left differential graded
  action of `End(Q)` on the complex underlying `Q`.
* `DifferentialGradedModule.endomorphismBimoduleStructure`: that action as a compatible left
  action on the right differential graded `B`-module `Q`, i.e. a
  `DifferentialGradedModule.BimoduleStructure`.
* `DifferentialGraded.Bimodule.endomorphism`: `Q` as a differential graded
  `(End(Q), B)`-bimodule.

## Main results

* `DifferentialGradedModule.homogeneousMapToCochain_id`,
  `DifferentialGradedModule.homogeneousMapToCochain_comp` and
  `DifferentialGradedModule.homogeneousMapToCochain_d`: the passage to cochains carries the
  identity to the identity cochain, a composite to the composite cochain and the Hom differential
  to the graded commutator differential `δ`. These three are exactly the laws of a left
  differential graded action, which is why the action below is a composite of linear maps with no
  further data.
* `DifferentialGraded.Bimodule.endomorphism_leftMultiplication`: left multiplication by a
  homogeneous element of `End(Q)` on the bimodule is that element, under the identification
  `DifferentialGradedModule.endomorphismAlgebraHom` of `End(Q)^n` with the degree-`n` homogeneous
  right `B`-linear endomorphisms of `Q`.

## Implementation notes

*Why a cochain translation is needed at all.* A `DifferentialGradedModule.BimoduleStructure` on
`Q` is a `DifferentialGradedAlgebra.LeftAction` on `Q.toCochainComplex` — a family of cochains of
the underlying complex of `R`-modules — together with the assertion that each of those cochains
is induced by a homogeneous right `B`-linear map
(`DifferentialGradedModule.IsRightLinearCochain`). The degree-`n` part of `End(Q)` is a
homogeneous right `B`-linear map already, so the content of the construction is purely the
translation between the two presentations of such a map, and the three laws above.

*Universes.* The left action lives on `Q.toCochainComplex`, a complex of `ModuleCat.{u} R`, so a
`BimoduleStructure` forces the module universe of `Q` to be the base-ring universe `u`; the
algebra universe of `B` stays free. This matches the single-universe convention of Tag 09JJ used
throughout this chapter.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) for differential graded
  bimodules and [Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI) for the criterion that a
  left action is a bimodule structure,
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the endomorphism algebra and
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC) for the differential graded category of
  differential graded modules.
* [Stacks Project, Tag 09S9](https://stacks.math.columbia.edu/tag/09S9) and
  [Tag 09SA](https://stacks.math.columbia.edu/tag/09SA) for the use made of this bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, v} R)

/-! ### Homogeneous right-linear maps as cochains -/

/-- A degree-`n` homogeneous right `B`-linear map `L → M`, read as a degree-`n` cochain of the
cochain complexes of `R`-modules underlying `L` and `M`: its component from degree `p` to degree
`q = p + n` is the map itself, which lands in the right piece by homogeneity. -/
def homogeneousMapToCochain {L M : DifferentialGradedModule.{u, v, w} B} {n : ℤ}
    (f : HomogeneousMap B L M n) :
    Cochain L.toCochainComplex M.toCochainComplex n :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom
    { toFun := fun x => (⟨f.1 x, hpq ▸ f.2.1 p x x.property⟩ : M.grading q)
      map_add' := fun _ _ => Subtype.ext (f.1.map_add _ _)
      map_smul' := fun r _ => Subtype.ext (f.1.map_smul r _) }

/-- Every component of the cochain attached to a homogeneous map is that map. -/
theorem homogeneousMapToCochain_v {L M : DifferentialGradedModule.{u, v, w} B} {n : ℤ}
    (f : HomogeneousMap B L M n) (p q : ℤ) (hpq : p + n = q) (x : L.grading p) :
    ((show M.grading q from (homogeneousMapToCochain B f).v p q hpq x) : M.M) = f.1 x :=
  rfl

/-- The cochain attached to a homogeneous map is induced by that map, so it is a right `B`-linear
cochain in the sense of `DifferentialGradedModule.IsRightLinearCochain`. -/
theorem isRightLinearCochain_homogeneousMapToCochain
    (Q : DifferentialGradedModule.{u, v, w} B) {n : ℤ} (f : HomogeneousMap B Q Q n) :
    IsRightLinearCochain B Q (homogeneousMapToCochain B f) :=
  ⟨f, fun p x => homogeneousMapToCochain_v B f p (p + n) rfl x⟩

/-- Reading a homogeneous right `B`-linear map as a cochain is `R`-linear in the map. -/
def homogeneousMapToCochainₗ (L M : DifferentialGradedModule.{u, v, w} B) (n : ℤ) :
    HomogeneousMap B L M n →ₗ[R] Cochain L.toCochainComplex M.toCochainComplex n where
  toFun := homogeneousMapToCochain B
  map_add' f g := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.add_v]
    ext x
    rfl
  map_smul' r f := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.smul_v]
    ext x
    rfl

/-- The `R`-linear map `homogeneousMapToCochainₗ` sends a homogeneous map to its cochain. -/
@[simp] theorem homogeneousMapToCochainₗ_apply {L M : DifferentialGradedModule.{u, v, w} B}
    {n : ℤ} (f : HomogeneousMap B L M n) :
    homogeneousMapToCochainₗ B L M n f = homogeneousMapToCochain B f :=
  rfl

/-- **The identity homogeneous map is the identity cochain.** -/
theorem homogeneousMapToCochain_id (L : DifferentialGradedModule.{u, v, w} B) :
    homogeneousMapToCochain B (homogeneousMapId B L) = Cochain.ofHom (𝟙 L.toCochainComplex) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p := by omega
  rw [Cochain.ofHom_v]
  rfl

/-- **A composite of homogeneous maps is the composite cochain.** Composition of homogeneous maps
is written with the outer map first and composition of cochains with the inner one first, which
is why the two arguments are exchanged. -/
theorem homogeneousMapToCochain_comp {L M N : DifferentialGradedModule.{u, v, w} B} {m n k : ℤ}
    (h : m + n = k) (g : HomogeneousMap B M N m) (f : HomogeneousMap B L M n) :
    homogeneousMapToCochain B (homogeneousMapComp B h g f) =
      (homogeneousMapToCochain B f).comp (homogeneousMapToCochain B g) (by omega) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.comp_v _ _ (show n + m = k by omega) p (p + n) q rfl (by omega)]
  rfl

/-- **The Hom differential of homogeneous maps is the graded commutator differential of
cochains.** -/
theorem homogeneousMapToCochain_d {L M : DifferentialGradedModule.{u, v, w} B} {n : ℤ}
    (f : HomogeneousMap B L M n) :
    homogeneousMapToCochain B (homogeneousMapDifferential B f) =
      δ n (n + 1) (homogeneousMapToCochain B f) := by
  have hd {N : DifferentialGradedModule.{u, v, w} B} (i j : ℤ) (hij : i + 1 = j)
      (y : N.grading i) :
      ((show N.grading j from N.toCochainComplex.d i j y) : N.M) = N.d y := by
    subst j
    rw [toCochainComplex_d]
    rfl
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v n (n + 1) rfl _ p q hpq (p + n) (p + 1) (by omega) rfl, toCochainComplex_d]
  ext x
  let x' : L.grading p := x
  apply Subtype.ext
  show M.d (f.1 (x' : L.M)) - DifferentialGraded.gradedSign R n • f.1 (L.d (x' : L.M)) =
    ((show M.grading q from M.toCochainComplex.d (p + n) q
      ⟨f.1 (x' : L.M), f.2.1 p (x' : L.M) x'.property⟩) : M.M) +
      ((n + 1).negOnePow : ℤ) • f.1 (L.d (x' : L.M))
  rw [hd (p + n) q (by omega), Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.val_neg,
    neg_smul, sub_eq_add_neg, ← Int.cast_smul_eq_zsmul R, Int.coe_negOnePow R n]
  rfl

/-! ### The tautological left action of the endomorphism algebra -/

variable (Q : DifferentialGradedModule.{u, v, u} B)

/-- **The tautological left action of `End(Q)` on `Q`.** A degree-`n` element of the endomorphism
differential graded algebra of `Q` is a degree-`n` homogeneous right `B`-linear endomorphism of
`Q`; it acts on the complex underlying `Q` by the corresponding cochain. The three laws of a left
differential graded action are the three identifications
`DifferentialGradedModule.endomorphismAlgebraHom_one`,
`DifferentialGradedModule.endomorphismAlgebraHom_mul` and
`DifferentialGradedModule.endomorphismAlgebraHom_d` of Tag 09LE, together with
`DifferentialGradedModule.homogeneousMapToCochain_id`,
`DifferentialGradedModule.homogeneousMapToCochain_comp` and
`DifferentialGradedModule.homogeneousMapToCochain_d`. -/
def endomorphismLeftAction : (endomorphismDGA B Q).LeftAction Q.toCochainComplex where
  action n := (homogeneousMapToCochainₗ B Q Q n).comp (endomorphismAlgebraHom B Q n).toLinearMap
  map_one := by
    obtain ⟨e, he, hid⟩ := endomorphismAlgebraHom_one B Q
    have he' : (⟨1, SetLike.one_mem_graded (endomorphismDGA B Q).grading⟩ :
        (endomorphismDGA B Q).grading 0) = e := Subtype.ext he.symm
    change homogeneousMapToCochain B (endomorphismAlgebraHom B Q 0 _) = _
    rw [he', hid]
    exact homogeneousMapToCochain_id B Q
  map_mul n m a b := by
    obtain ⟨c, hc, hcomp⟩ := endomorphismAlgebraHom_mul B Q n m (n + m) rfl a b
    have hc' : (⟨(a : (endomorphismDGA B Q).A) * (b : (endomorphismDGA B Q).A),
        SetLike.mul_mem_graded a.property b.property⟩ :
          (endomorphismDGA B Q).grading (n + m)) = c := Subtype.ext hc.symm
    change homogeneousMapToCochain B (endomorphismAlgebraHom B Q (n + m) _) = _
    rw [hc', hcomp]
    exact homogeneousMapToCochain_comp B rfl _ _
  map_d n a := by
    change homogeneousMapToCochain B (endomorphismAlgebraHom B Q (n + 1) _) = _
    rw [endomorphismAlgebraHom_d B Q n a]
    exact homogeneousMapToCochain_d B _

/-- The cochain through which a homogeneous element of `End(Q)` acts is that element, read as a
homogeneous right `B`-linear endomorphism of `Q`. -/
theorem endomorphismLeftAction_action (n : ℤ) (a : (endomorphismDGA B Q).grading n) :
    (endomorphismLeftAction B Q).action n a =
      homogeneousMapToCochain B (endomorphismAlgebraHom B Q n a) :=
  rfl

/-- **The tautological left action of `End(Q)` makes `Q` a differential graded
`(End(Q), B)`-bimodule structure.** Every homogeneous element of `End(Q)` acts by a right
`B`-linear cochain, since it *is* a homogeneous right `B`-linear map; by Tag 0FQI that is exactly
what makes the left action a bimodule structure on the fixed right `B`-module `Q`. -/
def endomorphismBimoduleStructure : BimoduleStructure (endomorphismDGA B Q) B Q :=
  ⟨endomorphismLeftAction B Q, fun n a =>
    isRightLinearCochain_homogeneousMapToCochain B Q (endomorphismAlgebraHom B Q n a)⟩

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, v} R)
  (Q : DifferentialGradedModule.{u, v, u} B)

/-- **A right differential graded `B`-module `Q` as a differential graded
`(End(Q), B)`-bimodule**, for `End(Q)` its endomorphism differential graded algebra of Tag 09LE.
The right module is `Q` itself and the left action is the tautological one of
`DifferentialGradedModule.endomorphismLeftAction`.

Marked `implicit_reducible` so that `(endomorphism B Q).rightModule` is recognised as `Q` by the
type checks that run below default transparency; every statement about this bimodule is a
statement about `Q`. -/
@[implicit_reducible]
def endomorphism : Bimodule (endomorphismDGA B Q) B where
  rightModule := Q
  leftAction := endomorphismBimoduleStructure B Q

/-- The right module of the bimodule `DifferentialGraded.Bimodule.endomorphism B Q` is `Q`. -/
@[simp] theorem endomorphism_rightModule : (endomorphism B Q).rightModule = Q := rfl

/-- **Left multiplication on the tautological bimodule is evaluation.** Left multiplication by a
homogeneous element `a` of `End(Q)` on the bimodule of `DifferentialGraded.Bimodule.endomorphism`
is `a` itself, read through `DifferentialGradedModule.endomorphismAlgebraHom` as a homogeneous
right `B`-linear endomorphism of `Q`.

`DifferentialGraded.Bimodule.leftMultiplication` is extracted from an existence statement, so it
is only computable on homogeneous elements; an arbitrary element is decomposed into its
homogeneous components. -/
theorem endomorphism_leftMultiplication (n : ℤ) (a : (endomorphismDGA B Q).grading n) :
    (endomorphism B Q).leftMultiplication n a = endomorphismAlgebraHom B Q n a := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn
    (endomorphism B Q).rightModule.grading with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | @homogeneous p x =>
    rw [leftMultiplication_apply (endomorphism B Q) n p a x]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The cohomology-endomorphism comparison of the tautological bimodule -/

/-- The differential of `End(Q)` applied to the element corresponding to a homogeneous map `c`
corresponds to the Hom differential of `c`. -/
private theorem endomorphismAlgebraHom_d_symm (k : ℤ) (c : HomogeneousMap B Q Q k) :
    endomorphismAlgebraHom B Q (k + 1)
        ⟨(endomorphismDGA B Q).d ((endomorphismAlgebraHom B Q k).symm c),
          (endomorphismDGA B Q).d_mem k _ ((endomorphismAlgebraHom B Q k).symm c).property⟩ =
      homogeneousMapDifferential B c := by
  rw [endomorphismAlgebraHom_d, LinearEquiv.apply_symm_apply]

/-- **Every homomorphism `Q ⟶ Q[k]` is the action of a degree-`k` cocycle of `End(Q)`.** A
homomorphism into the shift is the same thing as a closed degree-`k` homogeneous right `B`-linear
endomorphism of `Q` (`DifferentialGradedModule`
`.homogeneousMapDifferential_eq_zero_iff_exists_hom_shift`), and such an endomorphism is a
degree-`k` cocycle of `End(Q)` because the differential of `End(Q)` is the Hom differential
(`DifferentialGradedModule.endomorphismAlgebraHom_d`). -/
theorem surjective_cocycleAction (k : ℤ) :
    Function.Surjective ((endomorphism B Q).cocycleAction k) := by
  intro F
  let g : HomogeneousMap B Q Q k :=
    ⟨F.toFun, by
      rw [mem_homogeneousMapSubmodule]
      exact ⟨fun i x hx => by
          simpa only [endomorphism_rightModule, shift_grading] using F.map_grading i x hx,
        fun a x => F.map_smul x a⟩⟩
  have hg : homogeneousMapDifferential B g = 0 :=
    (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift B Q Q k g).mpr ⟨F, rfl⟩
  let a := (endomorphismAlgebraHom B Q k).symm g
  have ha : (endomorphismDGA B Q).d a = 0 := by
    have hz : (⟨(endomorphismDGA B Q).d a, (endomorphismDGA B Q).d_mem k a a.property⟩ :
        (endomorphismDGA B Q).grading (k + 1)) = 0 :=
      (endomorphismAlgebraHom B Q (k + 1)).injective
        ((endomorphismAlgebraHom_d_symm B Q k g).trans (hg.trans (map_zero _).symm))
    exact congrArg Subtype.val hz
  refine ⟨⟨a, ha⟩, ?_⟩
  apply DifferentialGradedModule.Hom.ext
  rw [cocycleAction_toFun, endomorphism_leftMultiplication]
  exact congrArg Subtype.val ((endomorphismAlgebraHom B Q k).apply_symm_apply g)

/-- A degree-`k` homogeneous element of `End(Q)` whose action is the Hom differential of a
degree-`(k - 1)` homogeneous map is a coboundary of `End(Q)`.

This is the injectivity half of the comparison below, in the form the Hom differential delivers
it: the identification `DifferentialGradedModule.endomorphismAlgebraHom_d` of the differential of
`End(Q)` with the Hom differential is stated in degree `(k - 1) + 1`, so the degree is first
normalised to that shape. -/
private theorem exists_d_eq_of_homogeneousMapDifferential (k : ℤ)
    (a b : (endomorphismDGA B Q).grading k) (c : HomogeneousMap B Q Q (k - 1))
    (hc : (homogeneousMapDifferential B c).1 =
      (endomorphismAlgebraHom B Q k a).1 - (endomorphismAlgebraHom B Q k b).1) :
    ∃ c' : (endomorphismDGA B Q).grading (k - 1),
      (a : (endomorphismDGA B Q).A) - b = (endomorphismDGA B Q).d c' := by
  generalize hk : k - 1 = l at c hc ⊢
  obtain rfl : k = l + 1 := by omega
  refine ⟨(endomorphismAlgebraHom B Q l).symm c, ?_⟩
  have he : endomorphismAlgebraHom B Q (l + 1) (a - b) =
      endomorphismAlgebraHom B Q (l + 1)
        ⟨(endomorphismDGA B Q).d ((endomorphismAlgebraHom B Q l).symm c),
          (endomorphismDGA B Q).d_mem l _
            ((endomorphismAlgebraHom B Q l).symm c).property⟩ := by
    rw [endomorphismAlgebraHom_d_symm, map_sub]
    exact Subtype.ext hc.symm
  exact congrArg Subtype.val ((endomorphismAlgebraHom B Q (l + 1)).injective he)

end DifferentialGraded.Bimodule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)
  (Q : DifferentialGradedModule.{u, u, u} B)

/-- **Hypothesis (3) of [Stacks, Tag 09S7] holds for the tautological bimodule of a module with
property (P).** For `Q` a right differential graded `B`-module with property (P) and
`E = End(Q)` its endomorphism differential graded algebra, the canonical map
$$H^k(E) \longrightarrow \Hom_{D(B, d)}(Q, Q[k])$$
of `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every
`k ∈ ℤ`.

Both halves factor through the same two steps. Property (P) makes localization bijective on
morphisms out of `Q` (`DifferentialGradedModule.bijective_q_map_of_propertyP`, [Stacks, Tag
09KY]), so `Hom_{D(B, d)}(Q, Q[k])` is `Hom_{K(B, d)}(Q, Q[k])`; and the degree-`k` part of `E`
*is* the degree-`k` homogeneous right `B`-linear endomorphisms of `Q`, with the differential of
`E` the Hom differential, so degree-`k` cocycles of `E` are exactly the homomorphisms `Q ⟶ Q[k]`
(`DifferentialGraded.Bimodule.surjective_cocycleAction`) and coboundaries are exactly the
null-homotopic ones
(`DifferentialGradedModule.toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential`).

Neither hypothesis of [Stacks, Tag 09SA] is used: this holds for every `Q` with property (P). -/
@[sga "5 IIIB 5.7" "special case"]
theorem bijective_cohomologyEndomorphismComparison_endomorphism
    (hQ : Nonempty (PropertyPFiltration Q)) (k : ℤ) :
    Function.Bijective ((endomorphism B Q).cohomologyEndomorphismComparison k) := by
  refine ⟨fun x y hxy => ?_, fun f => ?_⟩
  · induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rw [cohomologyEndomorphismComparison_mk, cohomologyEndomorphismComparison_mk,
      Functor.comp_map, Functor.comp_map] at hxy
    obtain ⟨c, hc⟩ := (toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential B
      ((endomorphism B Q).cocycleAction_toFun k a)
      ((endomorphism B Q).cocycleAction_toFun k b)).1
        ((bijective_q_map_of_propertyP hQ (Q.shift k)).injective hxy)
    rw [endomorphism_leftMultiplication, endomorphism_leftMultiplication] at hc
    exact Quotient.sound (exists_d_eq_of_homogeneousMapDifferential B Q k a.1 b.1 c hc)
  · obtain ⟨g, hg⟩ := (bijective_q_map_of_propertyP hQ (Q.shift k)).surjective f
    obtain ⟨a, ha⟩ := surjective_cocycleAction B Q k ((toHomotopyCategory B).preimage g)
    refine ⟨Quotient.mk _ a, ?_⟩
    rw [cohomologyEndomorphismComparison_mk, Functor.comp_map, ha, Functor.map_preimage, hg]

end DifferentialGraded.Bimodule

end
