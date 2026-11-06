module

import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.DifferentialOperator.Defs
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.ENatToNat
public import Mathlib.Algebra.Category.CommAlgCat.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.CategoryTheory.Limits.Filtered
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan
import StacksFrontier.RingTheory.Cotangent.H1BaseChange

/-!
# Étale and formally étale ring maps: first properties

A ring map `R → S` is *formally étale* (`Algebra.FormallyEtale`) when along every square-zero
extension `A → A ⧸ I` of `R`-algebras each `R`-algebra map `S → A ⧸ I` lifts to `S → A` in exactly
one way, and *étale* (`Algebra.Etale`) when it is moreover of finite presentation. This file
collects the first properties of the two notions: the comparison between them, stability of formal
étaleness under localization and under filtered colimits, what étaleness says pointwise on fibres
and about the shape of a presentation, the behaviour of étaleness under localization at a prime,
under flat base change and along a square-zero thickening.

It was split from `StacksFrontier.RingTheory.Etale.Basic`, which re-exports it together with
`StacksFrontier.RingTheory.Etale.Basic.DiagonalIdeal` (powers of the diagonal ideal) and
`StacksFrontier.RingTheory.Etale.Basic.PrincipalParts` (modules of principal parts) under a formally
étale extension.

## Main results

* `Algebra.formallyEtale_iff_etale`: a finitely presented algebra is étale if and only if it is
  formally étale.
* `Algebra.FormallyEtale.colimit`: a filtered colimit of formally étale algebras is formally
  étale.
* `RingHom.Etale.quasiFinite`: an étale ring map is quasi-finite.
* `Algebra.exists_isIdempotentElem_isLocalizationAway_of_surjective`: a surjective flat ring map of
  finite presentation is a localization at an idempotent.
* `RingHom.Etale.of_comp`: a map of `R`-algebras out of a formally unramified `R`-algebra of finite
  type whose composite with the structure map is étale is itself étale; in particular a map between
  two étale `R`-algebras is étale.
* `Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal`: a finitely presented algebra whose local
  homomorphism `R_p → S_q` is flat, for which `p S_q` is the maximal ideal of `S_q`, and whose
  residue field extension `κ(q)/κ(p)` is finite separable, is étale at `q`.
* `Algebra.etaleLocus_eq_of_isPushout`: for `S'` the base change of `S` along a flat ring map
  `R → R'`, the étale locus of `S'` over `R'` is the inverse image of the étale locus of `S` over
  `R` under `PrimeSpectrum.comap (algebraMap S S')`.
* `Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange`: a square-zero thickening `A' → A` and a
  thickening `B' → B` of an étale `A`-algebra whose ideal is the base change of the ideal of
  `A' → A` give an étale `A'`-algebra `B'`.

## Implementation notes

A directed system of algebras is a functor `F : ι ⥤ CommAlgCat R` out of a nonempty directed
preorder, which is a filtered category, so `colimit F` is the directed colimit.

In `RingHom.Etale.of_comp` the hypothesis that `R → S` be étale is weakened to formal
unramifiedness and finite type, and the weakening is strict: for `R = ℤ`, `S = ℤ × ℤ ⧸ 2`,
`T = ℤ` and `g` the first projection, `f` is formally unramified and of finite type but not étale,
while `g ∘ f = id` is étale and so is `g`.

"Étale at `q`" is `Algebra.IsEtaleAt R q`, formal étaleness of the stalk; under finite presentation
it is the existence of a `g ∉ q` with `R → S_g` étale (`Algebra.exists_etale_of_isEtaleAt`,
`Algebra.basicOpen_subset_etaleLocus_iff_etale`). In
`Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal` the local homomorphism `R_p → S_q` is the
`algebraMap` of the instances `[Algebra (Localization.AtPrime p) (Localization.AtPrime q)]` and
`[Localization.AtPrime.IsLiesOverAlgebra p q]`, and flatness is assumed of `R_p → S_q` only. The
finiteness of `κ(q)/κ(p)` follows from the remaining hypotheses.

`Algebra.etaleLocus_eq_of_isPushout` is stated for `Algebra.etaleLocus R S`, the set of primes `q`
with `Localization.AtPrime q` formally étale over `R`, and needs no finite presentation
hypothesis; the base change is the abstract `Algebra.IsPushout R S R' S'`.

In `Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange` the condition `J = I ⊗_A B` is spelled as
`IsBaseChange B' f` for the map `f : I → J` induced by `A' → B'`, that is, as bijectivity of the
canonical `B' ⊗[A'] I → J`. Tensoring over `A'` avoids the `A`-module structure on `I`, which
exists only because `I ^ 2 = ⊥`, and asks for the same thing: either condition gives `J = I B'`,
hence `B' ⧸ I B' ≅ B`, and then `B' ⊗[A'] I ≅ (B' ⧸ I B') ⊗[A] I ≅ B ⊗[A] I` compatibly with the
two maps to `J`. The condition `J ^ 2 = ⊥` follows from `I ^ 2 = ⊥` and `J = I B'`.

## References

* [StacksProject 00S4](https://stacks.math.columbia.edu/tag/00S4)
* [StacksProject 00TF](https://stacks.math.columbia.edu/tag/00TF)
* [StacksProject 00TG](https://stacks.math.columbia.edu/tag/00TG)
* [StacksProject 00U2](https://stacks.math.columbia.edu/tag/00U2)
* [StacksProject 00U5](https://stacks.math.columbia.edu/tag/00U5)
* [StacksProject 00U6](https://stacks.math.columbia.edu/tag/00U6)
* [StacksProject 00U7](https://stacks.math.columbia.edu/tag/00U7)
* [StacksProject 00U8](https://stacks.math.columbia.edu/tag/00U8)
* [StacksProject 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [StacksProject 00UR](https://stacks.math.columbia.edu/tag/00UR)
* [StacksProject 031N](https://stacks.math.columbia.edu/tag/031N)
* [StacksProject 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [StacksProject 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [StacksProject 04EG](https://stacks.math.columbia.edu/tag/04EG)
* [StacksProject 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [StacksProject 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public section

open scoped TensorProduct

/-! ### Formally étale ring maps -/

/-- A finitely presented algebra is étale if and only if it is formally étale. -/
@[stacks 00UR, ega "IV 17.3.2" "(ii), étale case", ega "IV 17.3.1" "étale case, ring maps"]
theorem Algebra.formallyEtale_iff_etale
    (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hfp : Algebra.FinitePresentation R S) :
    Algebra.FormallyEtale R S ↔ Algebra.Etale R S :=
  ⟨fun hf => ⟨hf, hfp⟩, fun h => h.1⟩

add_to_stacks 04EG "For a multiplicative subset `M ⊆ R` the ring map `R → M⁻¹R` is formally
  étale, stated for an arbitrary ring `Rₘ` realising the localization rather than for a chosen
  model." Algebra.FormallyEtale.of_isLocalization
add_to_ega "0 19.10.3" Algebra.FormallyEtale.of_isLocalization

open CategoryTheory Limits in
/-- Two `R`-algebra maps out of a colimit of `R`-algebras agree as soon as their composites with
the structure maps `F.obj i → colim F` agree. -/
private lemma algHom_colimit_ext {R : Type} [CommRing R] {ι : Type} [Category ι]
    {F : ι ⥤ CommAlgCat.{0} R} [HasColimit F] {B : Type} [CommRing B] [Algebra R B]
    {g₁ g₂ : (colimit F : CommAlgCat R) →ₐ[R] B}
    (h : ∀ i : ι, g₁.comp (colimit.ι F i).hom = g₂.comp (colimit.ι F i).hom) : g₁ = g₂ := by
  have h' : CommAlgCat.ofHom g₁ = CommAlgCat.ofHom g₂ :=
    colimit.hom_ext fun i => CommAlgCat.hom_ext (h i)
  exact congrArg CommAlgCat.Hom.hom h'

open CategoryTheory Limits in
/-- Let `R` be a commutative ring and let `ι` be a directed set, a nonempty preorder in which
every pair has an upper bound. Let `F : ι ⥤ CommAlgCat R` be a directed system of `R`-algebras
over `ι`, the family `S_i = F.obj i` with the transition maps encoded by functoriality. If every
`S_i` is formally étale over `R`, then the colimit `S = colim_i S_i` is formally étale over
`R`. -/
@[stacks 031N]
theorem Algebra.FormallyEtale.colimit
    (R : Type) [CommRing R]
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (F : ι ⥤ CommAlgCat.{0} R)
    (h : ∀ i : ι, Algebra.FormallyEtale R (F.obj i)) :
    Algebra.FormallyEtale R (colimit F : CommAlgCat R) := by
  rw [Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth]
  constructor
  · rw [Algebra.FormallyUnramified.iff_comp_injective]
    intro B _ _ I hI g₁ g₂ hg
    refine algHom_colimit_ext fun i => ?_
    apply Algebra.FormallyUnramified.lift_unique I ⟨2, by rw [hI]; rfl⟩
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hg]
  · rw [Algebra.FormallySmooth.iff_comp_surjective]
    intro B _ _ I hI g
    have hnil : IsNilpotent I := ⟨2, by rw [hI]; rfl⟩
    choose f hf using fun i =>
      Algebra.FormallySmooth.exists_lift (A := F.obj i) I hnil (g.comp (colimit.ι F i).hom)
    have compat : ∀ {i j : ι} (hij : i ≤ j),
        (f j).comp (F.map (homOfLE hij)).hom = f i := by
      intro i j hij
      apply Algebra.FormallyUnramified.lift_unique (A := F.obj i) I hnil
      have hw : (colimit.ι F j).hom.comp (F.map (homOfLE hij)).hom = (colimit.ι F i).hom :=
        congrArg CommAlgCat.Hom.hom (colimit.w F (homOfLE hij))
      rw [← AlgHom.comp_assoc, hf j, hf i, AlgHom.comp_assoc, hw]
    let c : Cocone F :=
      { pt := CommAlgCat.of R B
        ι :=
          { app := fun i => CommAlgCat.ofHom (f i)
            naturality := by
              intro i j φ
              apply CommAlgCat.hom_ext
              simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, Functor.const_obj_obj,
                Functor.const_obj_map, CommAlgCat.hom_id, AlgHom.id_comp]
              have : φ = homOfLE (leOfHom φ) := Subsingleton.elim _ _
              rw [this]
              exact compat (leOfHom φ) } }
    refine ⟨(colimit.desc F c).hom, algHom_colimit_ext fun i => ?_⟩
    have hd : (colimit.desc F c).hom.comp (colimit.ι F i).hom = f i :=
      congrArg CommAlgCat.Hom.hom (colimit.ι_desc c i)
    rw [AlgHom.comp_assoc, hd]
    exact hf i

/-! ### Étale ring maps -/

/-- An étale ring map is quasi-finite: every fibre `κ(P) ⊗ S` is a finite `κ(P)`-algebra. -/
@[stacks 00U5]
theorem RingHom.Etale.quasiFinite
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) :
    f.QuasiFinite := by
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.Etale R S := hf
  refine ⟨fun P _ => ?_⟩
  have : Algebra.Etale P.ResidueField (P.Fiber S) := Algebra.Etale.baseChange R S P.ResidueField
  exact Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber S)

add_to_stacks 00U9 "An étale algebra is standard smooth of relative dimension `0`, that is, it
  admits a presentation with as many equations as variables whose Jacobian determinant is
  invertible. Mathlib proves the equivalence, of which the tag is the forward implication."
  Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero
add_to_sga "1 II 1.3" "clause (i), special case"
  Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

add_to_stacks 03PC "jacobian"
  Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

/-- A surjective, flat, finitely presented ring map `R → S` exhibits `S` as the localization of
`R` at an idempotent `e`: the kernel of `algebraMap R S` is the ideal `(1 - e)`, and `S` is the
localization of `R` away from `e`. -/
@[stacks 00U8]
theorem Algebra.exists_isIdempotentElem_isLocalizationAway_of_surjective
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S))
    [Module.Flat R S] [Algebra.FinitePresentation R S] :
    ∃ e : R, IsIdempotentElem e ∧
      RingHom.ker (algebraMap R S) = Ideal.span {1 - e} ∧
      IsLocalization.Away e S := by
  have hfg : (RingHom.ker (algebraMap R S)).FG := by
    simpa using Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R S) hsurj
  have : Module.FinitePresentation R S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap R S) hsurj hfg
  have : Module.Projective R S := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Algebra.linearMap R S) LinearMap.id hsurj
  set e : R := s (1 : S) with he
  have hme : algebraMap R S e = 1 := by
    rw [he]; simpa [Algebra.linearMap_apply] using LinearMap.congr_fun hs 1
  have key : ∀ x ∈ RingHom.ker (algebraMap R S), x * e = 0 := fun x hx => by
    have hsx : s (algebraMap R S x) = x * e := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, ← he, smul_eq_mul]
    rw [RingHom.mem_ker.mp hx, map_zero] at hsx
    exact hsx.symm
  have h1e : 1 - e ∈ RingHom.ker (algebraMap R S) := by simp [RingHom.mem_ker, hme]
  have hidem : IsIdempotentElem e := by
    show e * e = e
    linear_combination -key (1 - e) h1e
  have hker : RingHom.ker (algebraMap R S) = Ideal.span {1 - e} :=
    le_antisymm (fun x hx => Ideal.mem_span_singleton.mpr ⟨x, by linear_combination key x hx⟩)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1e))
  exact ⟨e, hidem, hker, IsLocalization.away_of_isIdempotentElem hidem hker hsurj⟩

/-! ### A map between étale algebras is étale -/

/-- A ring map is étale if and only if it is formally étale and of finite presentation, the
`RingHom` counterpart of `Algebra.etale_iff`. -/
@[sga "3 VIIB 1.6"]
private lemma RingHom.etale_iff_formallyEtale_and_finitePresentation {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) : f.Etale ↔ f.FormallyEtale ∧ f.FinitePresentation :=
  let := f.toAlgebra
  Algebra.etale_iff R S

/-- Let `f : R →+* S` and `g : S →+* T` be ring maps, so that `g` is a map of `R`-algebras for the
`R`-algebra structure `g ∘ f` on `T`. If `f` is formally unramified and of finite type and `g ∘ f`
is étale, then `g` is étale. In particular a map between two étale `R`-algebras is étale. -/
@[stacks 00U7 "Stated for ring maps and their composite rather than for a tower of algebras: the
source quantifies over `R`-algebra maps `S → T`, for which `RingHom.Etale` is the predicate, and
the sibling `RingHom.FormallyEtale.of_comp` is stated that way. The hypothesis that `R → S` be
étale is weakened to the two properties the mathematics uses, formal unramifiedness and finite
type; see the module docstring for a witness that the generalization is strict."]
theorem RingHom.Etale.of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.FormallyUnramified) (hf' : f.FiniteType)
    (h : (g.comp f).Etale) : g.Etale := by
  rw [RingHom.etale_iff_formallyEtale_and_finitePresentation] at h ⊢
  exact ⟨RingHom.FormallyEtale.of_comp hf h.1,
    RingHom.FinitePresentation.of_comp_finiteType f h.2 hf'⟩

/-! ### A local criterion for étaleness at a prime -/

section LocalCriterion

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]
  [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]

/-- Let `R → S` be of finite presentation and let `q` be a prime of `S` lying over `p`. If
`R_p → S_q` is flat and the fibre `κ(p) ⊗_{R_p} S_q` is formally smooth over `κ(p)`, then
`R_p → S_q` is formally smooth.

This is `Algebra.IsSmoothAt.of_formallySmooth_fiber` with flatness and smoothness of the fibre
assumed at `q` only. -/
private lemma formallySmooth_localization_of_formallySmooth_fiber
    [Algebra.FormallySmooth p.ResidueField
      (p.ResidueField ⊗[Localization.AtPrime p] Localization.AtPrime q)] :
    Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q) := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
      (M := Algebra.algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.IsPushout R Rp S Sp :=
    .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
  have : Algebra.FinitePresentation Rp Sp := .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid _ q.primeCompl)

include p in
/-- A finitely presented algebra that is unramified at a prime `q` lying over `p` and whose local
homomorphism `R_p → S_q` is flat is étale at `q`. -/
private lemma isEtaleAt_of_isUnramifiedAt_of_flat [Algebra.IsUnramifiedAt R q] :
    Algebra.IsEtaleAt R q :=
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars R _ _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  have : Algebra.FormallyEtale p.ResidueField
      (p.ResidueField ⊗[Localization.AtPrime p] Localization.AtPrime q) :=
    .of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q) :=
    formallySmooth_localization_of_formallySmooth_fiber p q
  have : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_formallyUnramified_and_formallySmooth
  Algebra.FormallyEtale.comp R (Localization.AtPrime p) _

end LocalCriterion

/-- Let `R → S` be a ring map and let `q` be a prime of `S` lying over a prime `p` of `R`. If (1)
`R → S` is of finite presentation, (2) `R_p → S_q` is flat, (3) `p S_q` is the maximal ideal of the
local ring `S_q`, and (4) the field extension `κ(q)/κ(p)` is finite separable, then `R → S` is
étale at `q`. -/
@[nolint unusedArguments,
  stacks 00U6 "\"Étale at `q`\" is `Algebra.IsEtaleAt R q`, which under
hypothesis (1) is the source's Definition 00U1 (`Algebra.exists_etale_of_isEtaleAt` in one
direction, `Algebra.basicOpen_subset_etaleLocus_iff_etale` in the other). Hypothesis (3) is
recorded as `p S_q = m_{S_q}`; the source's `p S_q = q S_q` follows by
`Localization.AtPrime.map_eq_maximalIdeal`. The finiteness half of (4) is stated because the
source states it, and is implied by the rest; see the module docstring.",
  ega "IV 18.2.3" "a') ⇒ a)", sga "1 IX 1.2" "converse direction"]
theorem Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    [Module.Finite p.ResidueField q.ResidueField]
    [Algebra.IsSeparable p.ResidueField q.ResidueField]
    (h : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q :=
  have : Algebra.IsUnramifiedAt R q := (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr ⟨‹_›, h⟩
  isEtaleAt_of_isUnramifiedAt_of_flat p q

/-! ### The étale locus and flat base change -/

/-- A module vanishes at a prime `p` exactly when some — equivalently any — model `Mₚ` of its
localization at `p` is trivial. -/
private lemma notMem_support_iff_of_isLocalizedModule {A M Mₚ : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup Mₚ] [Module A Mₚ] (p : PrimeSpectrum A)
    (f : M →ₗ[A] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f] :
    p ∉ Module.support A M ↔ Subsingleton Mₚ :=
  Module.notMem_support_iff.trans (IsLocalizedModule.iso _ f).subsingleton_congr

/-- **The support of a base change along a flat ring map.** Let `A → B` be flat and let the
`B`-module `N` be the base change `B ⊗[A] M` of an `A`-module `M`. Then `Supp_B(N)` is the inverse
image of `Supp_A(M)` under `Spec(B) → Spec(A)`. -/
private lemma support_eq_preimage_comap_of_flat {A B M N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (e : B ⊗[A] M ≃ₗ[B] N) :
    Module.support B N = PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.support A M := by
  rw [← e.support_eq]
  ext P
  rw [Set.mem_preimage, ← not_iff_not]
  set p := PrimeSpectrum.comap (algebraMap A B) P
  have : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal P.asIdeal
  set Ap := Localization.AtPrime p.asIdeal
  set Bp := Localization.AtPrime P.asIdeal
  have : Module.FaithfullyFlat Ap Bp := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have eN : Bp ⊗[B] (B ⊗[A] M) ≃ₗ[Bp] Bp ⊗[Ap] (Ap ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B Bp Bp M ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap Bp Bp M).symm
  rw [notMem_support_iff_of_isLocalizedModule P (TensorProduct.mk B Bp _ 1),
    notMem_support_iff_of_isLocalizedModule p (TensorProduct.mk A Ap M 1),
    eN.subsingleton_congr]
  exact ⟨fun _ => Module.FaithfullyFlat.lTensor_reflects_triviality Ap Bp _,
    fun _ => inferInstance⟩


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Stacks.Cotangent.H1BaseChange in
/-- Let `R → S` be a ring map, let `R → R'` be flat and let `S'` be the base change of `S` along
`R → R'`. Then the set of primes of `S'` where `R' → S'` is étale is the inverse image, under
`Spec S' → Spec S`, of the set of primes of `S` where `R → S` is étale. -/
@[stacks 00U2 "(5). Stated for `Algebra.etaleLocus`, hence without the tag's hypothesis that
`R → S` be of finite presentation, which neither the conclusion nor the proof uses; with that
hypothesis the two loci are the tag's. The base change is the abstract `Algebra.IsPushout`. See
the module docstring, which also records where in Mathlib the other ten items live."]
theorem Algebra.etaleLocus_eq_of_isPushout
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Module.Flat R R'] :
    Algebra.etaleLocus R' S' =
      PrimeSpectrum.comap (algebraMap S S') ⁻¹' Algebra.etaleLocus R S := by
  have : Algebra.IsPushout R R' S S' := .symm inferInstance
  have : Module.Flat S S' :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R S R' S').toLinearEquiv.symm
  simp only [Algebra.etaleLocus_eq_compl_support, Set.preimage_inter, Set.preimage_compl,
    support_eq_preimage_comap_of_flat (KaehlerDifferential.tensorKaehlerEquiv R R' S S'),
    support_eq_preimage_comap_of_flat (isBaseChange_h1Cotangent_map R S R' S').equiv]

/-! ### Étaleness of a square-zero thickening whose ideal is a base change -/

/-! #### The canonical map `M ⊗[R] I → M` of an ideal -/

/-- The canonical `M`-linear map `M ⊗[R] I → M` attached to an ideal `I` of `R` and an
`R`-algebra `M`: the base change along `R → M` of the inclusion `I → R`. It sends `m ⊗ₜ x` to
`m * x`, its range is `I M` (`range_subtypeBaseChange`), and it is natural in `M`
(`map_subtypeBaseChange`). -/
private noncomputable def subtypeBaseChange {R : Type*} [CommSemiring R] (M : Type*)
    [CommSemiring M] [Algebra R M] (I : Ideal R) : M ⊗[R] ↥I →ₗ[M] M :=
  (Algebra.linearMap R M ∘ₗ I.subtype).liftBaseChange M

private lemma subtypeBaseChange_tmul {R : Type*} [CommSemiring R] (M : Type*) [CommSemiring M]
    [Algebra R M] (I : Ideal R) (m : M) (x : ↥I) :
    subtypeBaseChange M I (m ⊗ₜ x) = m * algebraMap R M (x : R) := by
  simp [subtypeBaseChange]

private lemma range_subtypeBaseChange {R : Type*} [CommSemiring R] (M : Type*) [CommSemiring M]
    [Algebra R M] (I : Ideal R) :
    LinearMap.range (subtypeBaseChange M I) = I.map (algebraMap R M) := by
  rw [subtypeBaseChange, LinearMap.range_liftBaseChange, LinearMap.range_comp,
    Submodule.range_subtype, Ideal.map, Submodule.map_coe]
  rfl

/-- Every element of `I M` is the image of an element of `M ⊗[R] I`. -/
private lemma exists_subtypeBaseChange_eq {R : Type*} [CommSemiring R] {M : Type*} [CommSemiring M]
    [Algebra R M] {I : Ideal R} {y : M} (hy : y ∈ I.map (algebraMap R M)) :
    ∃ s, subtypeBaseChange M I s = y := by
  rwa [← LinearMap.mem_range, range_subtypeBaseChange]

/-- Naturality of `M ⊗[R] I → M` in the `R`-algebra `M`. -/
private lemma map_subtypeBaseChange {R C M : Type*} [CommSemiring R] [CommSemiring C]
    [CommSemiring M] [Algebra R C] [Algebra R M] (I : Ideal R) (φ : C →ₐ[R] M) (s : C ⊗[R] ↥I) :
    φ (subtypeBaseChange C I s) = subtypeBaseChange M I (LinearMap.rTensor ↥I φ.toLinearMap s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp [subtypeBaseChange_tmul, AlgHom.commutes]
  | add s t hs ht => simp [hs, ht]

/-! #### Two consequences of a square-zero ideal -/

/-- A square-zero ideal annihilates itself. -/
private lemma mul_eq_zero_of_sq_eq_bot {R : Type*} [CommRing R] {J : Ideal R} (hJ : J ^ 2 = ⊥)
    {a b : R} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  simpa [hJ, ← pow_two] using Ideal.mul_mem_mul ha hb

/-- An element of `I C` tensored with an element of `I` vanishes in `C ⊗[A'] I`, when
`I ^ 2 = ⊥`. -/
private lemma tmul_eq_zero_of_mem_map {A' C : Type*} [CommRing A'] [CommRing C] [Algebra A' C]
    {I : Ideal A'} (hI : I ^ 2 = ⊥) {y : C} (hy : y ∈ I.map (algebraMap A' C)) (x : ↥I) :
    (y ⊗ₜ[A'] x : C ⊗[A'] ↥I) = 0 := by
  obtain ⟨s, rfl⟩ := exists_subtypeBaseChange_eq hy
  clear hy
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
      have h0 : (a : A') • x = 0 :=
        Subtype.ext (by simpa using mul_eq_zero_of_sq_eq_bot hI a.2 x.2)
      rw [subtypeBaseChange_tmul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, h0,
        TensorProduct.tmul_zero]
  | add s t hs ht => rw [map_add, TensorProduct.add_tmul, hs, ht, add_zero]

/-! #### A lift modulo a square-zero base-generated ideal is an isomorphism -/

/-- If every element of `B'` agrees modulo `I B'` with an element of the image of an
`A'`-algebra map `φ : C → B'`, and `I B'` has square zero, then `φ` is surjective. -/
private theorem surjective_of_sub_mem_of_sq_eq_bot {A' C B' : Type*} [CommRing A'] [CommRing C]
    [CommRing B'] [Algebra A' C] [Algebra A' B'] (I : Ideal A') (φ : C →ₐ[A'] B')
    (hmod : ∀ b : B', ∃ c, b - φ c ∈ I.map (algebraMap A' B'))
    (h2 : I.map (algebraMap A' B') ^ 2 = ⊥) : Function.Surjective φ := by
  have key : ∀ s : B' ⊗[A'] ↥I, ∃ c, φ c = subtypeBaseChange B' I s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b x =>
        obtain ⟨c, hc⟩ := hmod b
        have h0 : algebraMap A' B' (x : A') * (φ c - b) = 0 :=
          mul_eq_zero_of_sq_eq_bot h2 (Ideal.mem_map_of_mem _ x.2) (by simpa using neg_mem hc)
        refine ⟨(x : A') • c, ?_⟩
        rw [subtypeBaseChange_tmul, map_smul, Algebra.smul_def, mul_comm b, ← sub_eq_zero,
          ← mul_sub]
        exact h0
    | add s t hs ht =>
        obtain ⟨c, hc⟩ := hs
        obtain ⟨d, hd⟩ := ht
        exact ⟨c + d, by rw [map_add, hc, hd, map_add]⟩
  intro b
  obtain ⟨c, hc⟩ := hmod b
  obtain ⟨s, hs⟩ := exists_subtypeBaseChange_eq hc
  obtain ⟨d, hd⟩ := key s
  exact ⟨c + d, by rw [map_add, hd, hs, add_sub_cancel]⟩

/-- If `φ` is a surjection of modules whose kernel is annihilated by `N` in the sense that
`y ⊗ₜ x` vanishes for `y ∈ ker φ`, then `φ ⊗ N` is injective. -/
private lemma rTensor_injective_of_tmul_eq_zero {R C M N : Type*} [CommRing R] [AddCommGroup C]
    [Module R C] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : C →ₗ[R] M)
    (hφ : Function.Surjective φ)
    (h : ∀ y ∈ LinearMap.ker φ, ∀ x : N, (y ⊗ₜ[R] x : C ⊗[R] N) = 0) :
    Function.Injective (LinearMap.rTensor N φ) := by
  rw [← LinearMap.ker_eq_bot, (rTensor_exact N (LinearMap.exact_subtype_ker_map φ)
    (by simpa using hφ)).linearMap_ker_eq, LinearMap.range_eq_bot]
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y x => rw [LinearMap.rTensor_tmul]; exact h _ y.2 x
  | add s t hs ht => simp [hs, ht]

/-- Let `I` be a square-zero ideal of `A'` and let `φ : C → B'` be a surjection of `A'`-algebras
whose kernel is contained in `I C`. If the canonical map `B' ⊗[A'] I → B'` is injective, then `φ`
is injective. -/
private theorem injective_of_ker_le_map_of_sq_eq_bot {A' C B' : Type*} [CommRing A'] [CommRing C]
    [CommRing B'] [Algebra A' C] [Algebra A' B'] (I : Ideal A') (hI : I ^ 2 = ⊥) (φ : C →ₐ[A'] B')
    (hφ : Function.Surjective φ) (hker : ∀ c, φ c = 0 → c ∈ I.map (algebraMap A' C))
    (hinj : Function.Injective (subtypeBaseChange B' I)) : Function.Injective φ := by
  have hrT : Function.Injective (LinearMap.rTensor ↥I (φ.toLinearMap : C →ₗ[A'] B')) :=
    rTensor_injective_of_tmul_eq_zero _ hφ fun y hy x =>
      tmul_eq_zero_of_mem_map hI (hker _ (LinearMap.mem_ker.mp hy)) x
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨s, rfl⟩ := exists_subtypeBaseChange_eq (hker c hc)
  have h1 : LinearMap.rTensor ↥I (φ.toLinearMap : C →ₗ[A'] B') s = 0 := by
    refine hinj ?_
    rw [← map_subtypeBaseChange, hc, map_zero]
  rw [hrT (h1.trans (map_zero _).symm), map_zero]

/-! #### Étaleness of the thickening -/

/-- `Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange`, with the two ideals `I = ker (A' → A)` and
`J = ker (B' → B)` given as data pinned by `hIdef` and `hJdef`. -/
private theorem etale_of_sq_eq_bot_of_isBaseChange
    {A' A B' B : Type*} [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A' A] [Algebra A' B'] [Algebra A' B] [Algebra A B] [Algebra B' B]
    [IsScalarTower A' A B] [IsScalarTower A' B' B] [Algebra.Etale A B]
    (I : Ideal A') (J : Ideal B') (hIdef : I = RingHom.ker (algebraMap A' A))
    (hJdef : J = RingHom.ker (algebraMap B' B))
    (hA : Function.Surjective (algebraMap A' A)) (hB : Function.Surjective (algebraMap B' B))
    (hI : I ^ 2 = ⊥) (f : ↥I →ₗ[A'] ↥J)
    (hf : ∀ x, (f x : B') = algebraMap A' B' (x : A')) (hbc : IsBaseChange B' f) :
    Algebra.Etale A' B' := by
  have hbij : Function.Bijective (f.liftBaseChange B') := hbc
  have hfJ : J.subtype ∘ₗ f.liftBaseChange B' = subtypeBaseChange B' I := by
    rw [LinearMap.liftBaseChange_comp]
    exact congrArg (LinearMap.liftBaseChange B') (LinearMap.ext hf)
  have hJmap : J = I.map (algebraMap A' B') := by
    rw [← range_subtypeBaseChange B' I, ← hfJ, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hbij.2, Submodule.map_top, Submodule.range_subtype]
  have hJ2 : I.map (algebraMap A' B') ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have hinjB : Function.Injective (subtypeBaseChange B' I) := by
    rw [← hfJ]
    exact Subtype.val_injective.comp hbij.1
  obtain ⟨C, _, _, hCet, ψ, hψs, hψk⟩ := etale_lift_along_surjection A' A B hA
  have hgker : RingHom.ker (algebraMap B' B) = I.map (algebraMap A' B') := by rw [← hJmap, hJdef]
  have hnil : IsNilpotent (RingHom.ker (IsScalarTower.toAlgHom A' B' B : B' →+* B)) :=
    ⟨2, show RingHom.ker (algebraMap B' B) ^ 2 = 0 by rw [hgker, hJ2, Ideal.zero_eq_bot]⟩
  let φ : C →ₐ[A'] B' :=
    Algebra.FormallySmooth.liftOfSurjective ψ (IsScalarTower.toAlgHom A' B' B) hB hnil
  have hφ : ∀ c, algebraMap B' B (φ c) = ψ c :=
    Algebra.FormallySmooth.liftOfSurjective_apply ψ (IsScalarTower.toAlgHom A' B' B) hB hnil
  have hmod : ∀ b : B', ∃ c, b - φ c ∈ I.map (algebraMap A' B') := by
    intro b
    obtain ⟨c, hc⟩ := hψs (algebraMap B' B b)
    exact ⟨c, by rw [← hgker, RingHom.mem_ker, map_sub, hφ c, hc, sub_self]⟩
  have hker : ∀ c, φ c = 0 → c ∈ I.map (algebraMap A' C) := fun c hc => by
    rw [hIdef, ← hψk, RingHom.mem_ker]
    show ψ c = 0
    rw [← hφ c, hc, map_zero]
  have hsurj : Function.Surjective φ := surjective_of_sub_mem_of_sq_eq_bot I φ hmod hJ2
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ
    ⟨injective_of_ker_le_map_of_sq_eq_bot I hI φ hsurj hker hinjB, hsurj⟩)

/-- Let `A' → A` and `B' → B` be surjective ring maps forming a commutative square with `A' → B'`
and `A → B`, and write `I = ker (A' → A)`, `J = ker (B' → B)`. If `I` has square zero, `A → B` is
étale, and `J` is the base change of `I` along `A' → B'` (`J = I ⊗_A B`), then `A' → B'` is étale.
-/
@[stacks 05YT "The source's `J = I ⊗_A B` is spelled as bijectivity of the canonical map
`B' ⊗[A'] I → J`, i.e. as `IsBaseChange B' f` for the map `f : I → J` induced by `A' → B'`;
tensoring over `A'` rather than `A` avoids the `A`-module structure on `I`, which is unavailable
to typeclass inference, and asks for the same thing (see the module docstring). The source's
hypothesis `J ^ 2 = ⊥` is dropped: it follows from `hI` and the surjectivity half of `hbc`."]
theorem Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange
    {A' A B' B : Type*} [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A' A] [Algebra A' B'] [Algebra A' B] [Algebra A B] [Algebra B' B]
    [IsScalarTower A' A B] [IsScalarTower A' B' B] [Algebra.Etale A B]
    (hA : Function.Surjective (algebraMap A' A)) (hB : Function.Surjective (algebraMap B' B))
    (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (f : RingHom.ker (algebraMap A' A) →ₗ[A'] RingHom.ker (algebraMap B' B))
    (hf : ∀ x, (f x : B') = algebraMap A' B' (x : A')) (hbc : IsBaseChange B' f) :
    Algebra.Etale A' B' :=
  etale_of_sq_eq_bot_of_isBaseChange _ _ rfl rfl hA hB hI f hf hbc

end
