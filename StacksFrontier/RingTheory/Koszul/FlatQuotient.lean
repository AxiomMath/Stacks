module

public import StacksFrontier.RingTheory.Koszul.H1BaseChange
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan

@[expose] public section

/-!
# Koszul homology under base change when the quotient is flat

Let `A → B` and `A → A'` be ring maps, let `f₁, …, fᵣ` be elements of `B`, and suppose that
`B / (f₁, …, fᵣ)` is flat over `A`. Then both quasi-regularity and H₁-regularity of the sequence
are preserved by its image in `B ⊗[A] A'`.

Two lifting statements along a locally nilpotent ideal follow. Let `R → S` be flat of finite
presentation, let `I ⊆ R` be locally nilpotent, and let `f₁, …, fᵣ` be elements of `S` whose
images in `S / IS` are quasi-regular. If `(S / IS) / (f₁, …, fᵣ)` is flat (resp. smooth) over
`R / I`, then `S / (f₁, …, fᵣ)` is flat (resp. smooth) over `R`.

## Main results

* `Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat`: quasi-regular and
  H₁-regular sequences remain so after arbitrary base change when their quotient is flat over
  the base.
* `Koszul.flat_quotient_span_of_isQuasiRegular_of_locallyNilpotent`: flatness of the quotient
  by a sequence lifts across a locally nilpotent ideal when the reduced sequence is
  quasi-regular.
* `Koszul.smooth_quotient_span_of_isQuasiRegular_of_locallyNilpotent`: smoothness of the
  quotient by a sequence lifts across a locally nilpotent ideal when the reduced sequence is
  quasi-regular.

## Implementation notes

The sequence is represented by `f : Fin r → B`. Quasi-regularity uses the corresponding list
`List.ofFn f`, while H₁-regularity uses `f` directly. Its image in the tensor-product algebra is
the canonical sequence `KoszulH1.fp f`, and its generated ideal is
`Ideal.span (Set.range f)`.

The quasi-regular half is proved by exhibiting the whole comparison square
`Source → Target` for `f` and for `KoszulH1.fp f` as a base change along `A → A'`: flatness of
`B / (f₁, …, fᵣ)` propagates to flatness of every graded piece `Tcomp B f n` and hence of
`B ⧸ JpowM B f n`, which is what makes the submodule and quotient comparison maps base changes.
Bijectivity then transfers along the square. The H₁-regular half instead reduces to
`KoszulH1.cmp_surjective` (Tag 063Q): surjectivity of the canonical map on first Koszul homology
carries vanishing across the base change.

The two lifting statements are local on `Spec S`: after localizing at a maximal ideal of `S` one
reduces, via the local flatness criterion of Tag 0470, to regularity of the sequence on the
closed fibre, where Tag 09CC turns the quasi-regularity supplied by Tag 0CEP into regularity.
The smooth statement then feeds the flat one into the fibrewise criterion for smoothness.

The finite sequence is represented by `f : Fin r → S`. The extended ideal `IS` is
`I.map (algebraMap R S)`, and both quotients use their canonical algebra structures. Local
nilpotence of `I` is expressed by the inclusion `I ≤ nilradical R`.

## References

* [The Stacks Project, Tag 0CEP](https://stacks.math.columbia.edu/tag/0CEP)
* [The Stacks Project, Tag 0CEQ](https://stacks.math.columbia.edu/tag/0CEQ)
* [The Stacks Project, Tag 0CER](https://stacks.math.columbia.edu/tag/0CER)
-/

open scoped TensorProduct

namespace Koszul

open RingTheory.Sequence TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {r : ℕ} (f : Fin r → B)

/-! ### Flatness of the graded pieces of the quasi-regularity comparison -/

private lemma flat_qrMbar (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f))) :
    Module.Flat A (qrMbar B f) := by
  let e : qrMbar B f ≃ₗ[B] B ⧸ Jid f :=
    Submodule.quotEquivOfEq _ _ (by simp [Jid])
  have : Module.Flat A (B ⧸ Jid f) := hflat
  exact Module.Flat.of_linearEquiv (e.restrictScalars A)

private lemma flat_Source (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f))) :
    Module.Flat A (Source B f) := by
  have : Module.Flat A (qrMbar B f) := flat_qrMbar f hflat
  have hi : Module.Flat A ((Fin r →₀ ℕ) →₀ qrMbar B f) :=
    Module.Flat.of_linearEquiv (finsuppLEquivDirectSum A (qrMbar B f) (Fin r →₀ ℕ))
  exact Module.Flat.of_linearEquiv ((srcFinsuppEquiv B f).restrictScalars A)

private lemma flat_Target (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) :
    Module.Flat A (Target B f) := by
  have := flat_Source f hflat
  let e : Source B f ≃ₗ[qrRbar f] Target B f :=
    LinearEquiv.ofBijective (quasiRegularCanonicalMap (M := B) f) hf
  exact Module.Flat.of_linearEquiv (e.symm.restrictScalars A)

private lemma flat_Tcomp (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) (n : ℕ) :
    Module.Flat A (Tcomp B f n) := by
  have := flat_Target f hflat hf
  exact (Module.Flat.directSum_iff).mp inferInstance n

private lemma flat_quotient_of_flat_subquotient
    (P Q : Submodule B B) (hQP : Q ≤ P)
    (hsub : Module.Flat A (P ⧸ Submodule.comap P.subtype Q))
    (hquot : Module.Flat A (B ⧸ P)) :
    Module.Flat A (B ⧸ Q) := by
  let I : (P ⧸ Submodule.comap P.subtype Q) →ₗ[B] B ⧸ Q :=
    Submodule.mapQ _ _ P.subtype fun _ hx => hx
  let G : (B ⧸ Q) →ₗ[B] B ⧸ P := Submodule.factor hQP
  have hI : Function.Injective I := by
    rw [← LinearMap.ker_eq_bot]
    change I.ker = ⊥
    rw [show I.ker = (Submodule.comap P.subtype Q).map
        (Submodule.comap P.subtype Q).mkQ from Submodule.ker_mapQ _ _ _ _]
    exact Submodule.mkQ_map_self _
  have hG : Function.Surjective G := Submodule.factor_surjective hQP
  have hIG : Function.Exact I G := by
    rw [LinearMap.exact_iff, show G.ker = (Submodule.comap (LinearMap.id : B →ₗ[B] B) P).map Q.mkQ
        from Submodule.ker_mapQ _ _ _ _]
    rw [show I = (Submodule.comap P.subtype Q).mapQ Q P.subtype _ from rfl,
      Submodule.range_mapQ, Submodule.range_subtype]
    simp
  exact flat_of_flat_of_flat (I.restrictScalars A) (G.restrictScalars A) hI hIG hG

private lemma flat_quotient_powers (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) (n : ℕ) :
    Module.Flat A (B ⧸ JpowM B f n) := by
  induction n with
  | zero =>
      have hzero : JpowM B f 0 = ⊤ := by simp [JpowM]
      rw [hzero]
      infer_instance
  | succ n ih =>
      have hQP : JpowM B f (n + 1) ≤ JpowM B f n := by
        unfold JpowM
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n) (I := Jid f))
      exact flat_quotient_of_flat_subquotient (JpowM B f n) (JpowM B f (n+1)) hQP
        (flat_Tcomp f hflat hf n) ih

/-! ### The base-change comparison maps -/

variable {A' : Type*} [CommRing A'] [Algebra A A']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private noncomputable def tensorComm : A' ⊗[A] B ≃ₗ[A'] B ⊗[A] A' :=
  (Algebra.TensorProduct.commRight A A' B).toLinearEquiv

private theorem bc_isBaseChange :
    IsBaseChange A' (KoszulH1.inclLeft (A := A) (B := B) (A' := A')).toLinearMap := by
  apply IsBaseChange.of_equiv (tensorComm (A := A) (B := B) (A' := A'))
  intro b
  simp [tensorComm, KoszulH1.inclLeft]

private theorem map_equiv_baseChange
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module A' N] [IsScalarTower A A' N] {bc : M →ₗ[A] N}
    (hbc : IsBaseChange A' bc) (P : Submodule A M) :
    Submodule.map (hbc.equiv : A' ⊗[A] M →ₗ[A'] N) (P.baseChange A') =
      Submodule.span A' (bc '' P) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
  refine congrArg _ (Set.image_congr' fun x => ?_)
  simp

private theorem isBaseChange_of_submodule_of_flat_quotient
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module A' N] [IsScalarTower A A' N] {bc : M →ₗ[A] N}
    (hbc : IsBaseChange A' bc) (P : Submodule A M) (P' : Submodule A' N)
    (hP' : P' = Submodule.span A' (bc '' P))
    (hflat : Module.Flat A (M ⧸ P)) (g : P →ₗ[A] P')
    (hg : ∀ x : P, ((g x : N)) = bc (x : M)) : IsBaseChange A' g := by
  have hinj : Function.Injective (P.toBaseChange A') := by
    have hlin : Function.Injective (LinearMap.lTensor A' P.subtype) :=
      LinearMap.lTensor_injective_of_exact_of_flat P.mkQ P.mkQ_surjective P.subtype
        P.subtype_injective (LinearMap.exact_subtype_mkQ P) A'
    intro x y hxy
    exact hlin (congrArg Subtype.val hxy)
  let eP : A' ⊗[A] P ≃ₗ[A'] P.baseChange A' :=
    LinearEquiv.ofBijective (P.toBaseChange A') ⟨hinj, P.toBaseChange_surjective A'⟩
  have hmap : Submodule.map (hbc.equiv : A' ⊗[A] M →ₗ[A'] N) (P.baseChange A') = P' :=
    (map_equiv_baseChange hbc P).trans hP'.symm
  refine IsBaseChange.of_equiv
    (eP.trans ((Submodule.equivMapOfInjective _ hbc.equiv.injective _).trans
      (LinearEquiv.ofEq _ _ hmap))) ?_
  intro x
  apply Subtype.ext
  change (hbc.equiv : A' ⊗[A] M →ₗ[A'] N)
    (((P.toBaseChange A') (1 ⊗ₜ[A] x) : P.baseChange A') : A' ⊗[A] M) = (g x : N)
  rw [Submodule.coe_toBaseChange_tmul]
  simpa using (hg x).symm

private theorem isBaseChange_of_quotient
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module A' N] [IsScalarTower A A' N] {bc : M →ₗ[A] N}
    (hbc : IsBaseChange A' bc) (P : Submodule A M) (P' : Submodule A' N)
    (hP' : P' = Submodule.span A' (bc '' P))
    (g : (M ⧸ P) →ₗ[A] (N ⧸ P'))
    (hg : ∀ x : M, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (bc x)) :
    IsBaseChange A' g := by
  refine IsBaseChange.of_equiv
    ((AlgebraTensorModule.tensorQuotientEquiv A' A A' P).trans
      (Submodule.Quotient.equiv _ P' hbc.equiv
        (by
          have hbase : P.baseChange A' =
              LinearMap.range
                (AlgebraTensorModule.lTensor A' A' (P.subtype.restrictScalars A)) := rfl
          rw [← hbase]
          exact (map_equiv_baseChange hbc P).trans hP'.symm))) ?_
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H m =>
      rw [LinearEquiv.trans_apply, AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, hg]
      change Submodule.Quotient.mk ((hbc.equiv : A' ⊗[A] M →ₗ[A'] N) (1 ⊗ₜ[A] m)) = _
      simp

/-- Base-change statement for the map on quotients by a `B`-submodule and a `B ⊗[A] A'`-submodule
induced by a base change `bc`. -/
private theorem isBaseChange_of_quotient_of_module
    {M N : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N] [Module A N] [Module A' N] [IsScalarTower A A' N]
    [Module (B ⊗[A] A') N] [IsScalarTower A' (B ⊗[A] A') N] [IsScalarTower A (B ⊗[A] A') N]
    {bc : M →ₗ[A] N}
    (hbc : IsBaseChange A' bc) (P : Submodule B M) (P' : Submodule (B ⊗[A] A') N)
    (hP' : P'.restrictScalars A' = Submodule.span A' (bc '' P))
    (g : (M ⧸ P) →ₗ[A] (N ⧸ P'))
    (hg : ∀ x : M, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (bc x)) :
    IsBaseChange A' g := by
  let g0 : (M ⧸ P.restrictScalars A) →ₗ[A] (N ⧸ P'.restrictScalars A') :=
    Submodule.liftQ _ ((P'.restrictScalars A').mkQ.restrictScalars A ∘ₗ bc) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP']
      exact Submodule.subset_span ⟨x, hx, rfl⟩)
  have hbc0 : IsBaseChange A' g0 :=
    isBaseChange_of_quotient hbc (P.restrictScalars A) (P'.restrictScalars A') hP' g0 fun x =>
      Submodule.liftQ_apply _ _ x
  let e := Submodule.Quotient.restrictScalarsEquiv A P
  let e' := Submodule.Quotient.restrictScalarsEquiv A' P'
  apply (IsBaseChange.iff_of_equiv_comm e e' ?_).mp hbc0
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H y => exact (hg y).trans rfl

/-! ### The ideal powers `JpowM` under base change -/

private theorem fpow_fp (f : Fin r → B) (e : Fin r →₀ ℕ) :
    KoszulH1.inclLeft (A := A) (A' := A') (fpow f e) =
      fpow (KoszulH1.fp (A := A) (A' := A') f) e := by
  simp [fpow, KoszulH1.fp, map_prod]

private theorem map_fpow_mul (f : Fin r → B) (e : Fin r →₀ ℕ) (b : B) :
    (KoszulH1.inclLeft (A := A) (A' := A')) (fpow f e * b) =
      fpow (KoszulH1.fp (A := A) (A' := A') f) e *
        KoszulH1.inclLeft (A := A) (A' := A') b := by
  rw [map_mul, fpow_fp]

private theorem map_mem_JpowM (f : Fin r → B) (n : ℕ) (b : B)
    (hb : b ∈ JpowM B f n) :
    (KoszulH1.inclLeft (A := A) (A' := A')) b ∈
      JpowM (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n := by
  rw [JpowM_eq_span] at hb
  induction hb using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨e, m, he, rfl⟩ := hy
      subst he
      change (KoszulH1.inclLeft (A := A) (A' := A')) (fpow f e * m) ∈ _
      rw [map_fpow_mul]
      exact fpow_smul_mem _ e _
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | smul b a _ ha =>
      change (KoszulH1.inclLeft (A := A) (A' := A')) (b * a) ∈ _
      rw [map_mul]
      exact Submodule.smul_mem _ _ ha

private theorem mul_mem_span_image_JpowM (f : Fin r → B) (n : ℕ) (c x : B ⊗[A] A')
    (hx : x ∈ Submodule.span A' ((KoszulH1.inclLeft (A := A) (A' := A')).toLinearMap ''
      (JpowM B f n : Set B))) :
    c * x ∈ Submodule.span A' ((KoszulH1.inclLeft (A := A) (A' := A')).toLinearMap ''
      (JpowM B f n : Set B)) := by
  have hc : c ∈ Submodule.span A'
      (Set.range (KoszulH1.inclLeft (A := A) (A' := A') (B := B)).toLinearMap) := by
    rw [IsBaseChange.span_range_eq_top (bc_isBaseChange (A := A) (B := B) (A' := A'))]
    trivial
  induction hc using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨i, hi, rfl⟩ := hy
          change KoszulH1.inclLeft (A := A) (A' := A') b *
            KoszulH1.inclLeft (A := A) (A' := A') i ∈ _
          rw [← map_mul]
          exact Submodule.subset_span ⟨b * i, (JpowM B f n).smul_mem b hi, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
          rw [mul_add]
          exact Submodule.add_mem _ ha hb
      | smul a' a _ ha =>
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ _ ha
  | zero => simp
  | add a b _ _ ha hb =>
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  | smul a' a _ ha =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ ha

private theorem span_image_JpowM (f : Fin r → B) (n : ℕ) :
    Submodule.span A' ((KoszulH1.inclLeft (A := A) (A' := A')).toLinearMap ''
      (JpowM B f n : Set B)) =
      (JpowM (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n).restrictScalars A' := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    exact map_mem_JpowM (A := A) (A' := A') f n x hx
  · intro x hx
    rw [JpowM_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨e, y', he, rfl⟩ := hy
        subst he
        rw [smul_eq_mul, mul_comm]
        exact mul_mem_span_image_JpowM f _ y' _ (Submodule.subset_span
          ⟨fpow f e, by simpa using fpow_smul_mem f e (1 : B), fpow_fp f e⟩)
    | zero => simp
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha => exact mul_mem_span_image_JpowM f n c a ha

private noncomputable def JpowMRestrictB (f : Fin r → B) (n : ℕ) :
    JpowM B f n →ₗ[B]
      JpowM (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n where
  toFun x := ⟨KoszulH1.inclLeft (A := A) (A' := A') x.1,
    map_mem_JpowM (A := A) (A' := A') f n x.1 x.2⟩
  map_add' x y := Subtype.ext (by simp [KoszulH1.inclLeft, TensorProduct.add_tmul])
  map_smul' b x := Subtype.ext (by simp [Algebra.smul_def, KoszulH1.inclLeft, map_mul])

private noncomputable def JpowMRestrict (f : Fin r → B) (n : ℕ) :
    JpowM B f n →ₗ[A]
      JpowM (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n :=
  (JpowMRestrictB (A := A) (A' := A') f n).restrictScalars A

private theorem isBaseChange_JpowMRestrict (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) (n : ℕ) :
    IsBaseChange A' (JpowMRestrict (A := A) (A' := A') f n) := by
  let bc := (KoszulH1.inclLeft (A := A) (A' := A') (B := B)).toLinearMap
  have hbc : IsBaseChange A' bc := bc_isBaseChange (A := A) (B := B) (A' := A')
  let P := (JpowM B f n).restrictScalars A
  let P' := (JpowM (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n).restrictScalars A'
  have hflatP : Module.Flat A (B ⧸ P) := by
    have : Module.Flat A (B ⧸ JpowM B f n) := flat_quotient_powers f hflat hf n
    exact Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv A _)
  exact isBaseChange_of_submodule_of_flat_quotient hbc P P'
    (span_image_JpowM (A := A) (A' := A') f n).symm hflatP
    (JpowMRestrict (A := A) (A' := A') f n) (fun _ => rfl)

private theorem span_image_Tsub (f : Fin r → B) (n : ℕ) :
    (Tsub (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n).restrictScalars A' =
      Submodule.span A' ((JpowMRestrict (A := A) (A' := A') f n) ''
        ((Tsub B f n).restrictScalars A : Set (JpowM B f n))) := by
  let g := KoszulH1.fp (A := A) (A' := A') f
  let R := JpowMRestrict (A := A) (A' := A') f n
  let P := JpowM (B ⊗[A] A') g n
  let Q := JpowM (B ⊗[A] A') g (n+1)
  have hleft : Submodule.map (P.subtype.restrictScalars A')
      ((Tsub (B ⊗[A] A') g n).restrictScalars A') = Q.restrictScalars A' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, JpowM_succ_le g n hy⟩, hy, rfl⟩
  apply Submodule.map_injective_of_injective (f := P.subtype.restrictScalars A') P.injective_subtype
  rw [hleft, Submodule.map_span]
  convert (span_image_JpowM (A := A) (A' := A') f (n+1)).symm using 1
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z.1, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨R ⟨z, JpowM_succ_le f n hz⟩, ?_, rfl⟩
    exact ⟨⟨z, JpowM_succ_le f n hz⟩, hz, rfl⟩

private noncomputable def tgtMapComp (f : Fin r → B) (n : ℕ) :
    Tcomp B f n →ₗ[A] Tcomp (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n :=
  let Q' := Tsub (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n
  let g := Submodule.mapQ (Tsub B f n) (Q'.restrictScalars B)
    (JpowMRestrictB (A := A) (A' := A') f n)
    (by
      intro x hx
      exact map_mem_JpowM (A := A) (A' := A') f (n+1) x.1 hx)
  ((Submodule.Quotient.restrictScalarsEquiv B Q').restrictScalars A).toLinearMap ∘ₗ
    g.restrictScalars A

private theorem tgtMapComp_mk (f : Fin r → B) (n : ℕ) (x : JpowM B f n) :
    tgtMapComp (A := A) (A' := A') f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (JpowMRestrict (A := A) (A' := A') f n x) :=
  rfl

private theorem isBaseChange_tgtMapComp (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) (n : ℕ) :
    IsBaseChange A' (tgtMapComp (A := A) (A' := A') f n) :=
  isBaseChange_of_quotient_of_module
    (isBaseChange_JpowMRestrict (A := A) (A' := A') f hflat hf n) _ _
    (span_image_Tsub (A := A) (A' := A') f n) _ fun _ => rfl

/-! ### The degree-one quotient `qrMbar` under base change -/

private theorem map_mem_Jid_smul_top (f : Fin r → B) (b : B)
    (hb : b ∈ Jid f • (⊤ : Submodule B B)) :
    KoszulH1.inclLeft (A := A) (A' := A') b ∈
      Jid (KoszulH1.fp (A := A) (A' := A') f) •
        (⊤ : Submodule (B ⊗[A] A') (B ⊗[A] A')) := by
  rw [← JpowM_one (KoszulH1.fp (A := A) (A' := A') f)]
  exact map_mem_JpowM (A := A) (A' := A') f 1 b (by rwa [JpowM_one])

private theorem span_image_Jid_smul_top (f : Fin r → B) :
    (Jid (KoszulH1.fp (A := A) (A' := A') f) •
      (⊤ : Submodule (B ⊗[A] A') (B ⊗[A] A'))).restrictScalars A' =
      Submodule.span A' ((KoszulH1.inclLeft (A := A) (A' := A')).toLinearMap ''
        (((Jid f • (⊤ : Submodule B B)) : Submodule B B) : Set B)) := by
  simpa only [JpowM_one] using
    (span_image_JpowM (A := A) (A' := A') f 1).symm

private noncomputable def barMap (f : Fin r → B) :
    qrMbar B f →ₗ[A]
      qrMbar (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) :=
  let P := Jid f • (⊤ : Submodule B B)
  let P' := Jid (KoszulH1.fp (A := A) (A' := A') f) •
    (⊤ : Submodule (B ⊗[A] A') (B ⊗[A] A'))
  let g : (B ⧸ P) →ₗ[B] ((B ⊗[A] A') ⧸ P'.restrictScalars B) :=
    Submodule.mapQ P (P'.restrictScalars B)
      (Algebra.linearMap B (B ⊗[A] A'))
      (by intro b hb; exact map_mem_Jid_smul_top (A := A) (A' := A') f b hb)
  ((Submodule.Quotient.restrictScalarsEquiv B P').restrictScalars A).toLinearMap ∘ₗ
    g.restrictScalars A

private theorem barMap_mk (f : Fin r → B) (b : B) :
    barMap (A := A) (A' := A') f (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (KoszulH1.inclLeft (A := A) (A' := A') b) :=
  rfl

private theorem isBaseChange_barMap (f : Fin r → B) :
    IsBaseChange A' (barMap (A := A) (A' := A') f) :=
  isBaseChange_of_quotient_of_module (bc_isBaseChange (A := A) (B := B) (A' := A')) _ _
    (span_image_Jid_smul_top (A := A) (A' := A') f) _ fun _ => rfl

/-! ### The comparison square for the quasi-regularity map -/

private noncomputable def srcMap (f : Fin r → B) :
    Source B f →ₗ[A] Source (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) :=
  (((srcFinsuppEquiv (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f)).restrictScalars
        A).symm).toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (barMap (A := A) (A' := A') f) ∘ₗ
    ((srcFinsuppEquiv B f).restrictScalars A).toLinearMap

private theorem srcMap_srcMono (f : Fin r → B) (e : Fin r →₀ ℕ) (b : B) :
    srcMap (A := A) (A' := A') f (srcMono f e b) =
      srcMono (KoszulH1.fp (A := A) (A' := A') f) e
        (KoszulH1.inclLeft (A := A) (A' := A') b) := by
  simp only [srcMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_symm_apply, LinearEquiv.restrictScalars_apply,
    srcFinsuppEquiv_srcMono, mapRange_linearMap_single, barMap_mk]
  rw [← srcFinsuppEquiv_srcMono (KoszulH1.fp (A := A) (A' := A') f) e
    (KoszulH1.inclLeft (A := A) (A' := A') b), LinearEquiv.symm_apply_apply]

private theorem isBaseChange_srcMap (f : Fin r → B) :
    IsBaseChange A' (srcMap (A := A) (A' := A') f) := by
  refine
    (IsBaseChange.iff_of_equiv_comm ((srcFinsuppEquiv B f).restrictScalars A).symm
          ((srcFinsuppEquiv (B ⊗[A] A')
            (KoszulH1.fp (A := A) (A' := A') f)).restrictScalars A').symm
          ?_).1
      (IsBaseChange.finsuppPow _ (isBaseChange_barMap (A := A) (A' := A') f))
  refine LinearMap.ext fun y => ?_
  simp only [srcMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_symm_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.apply_symm_apply]

private noncomputable def tgtMap (f : Fin r → B) :
    Target B f →ₗ[A] Target (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) :=
  DirectSum.lmap fun n => tgtMapComp (A := A) (A' := A') f n

private theorem isBaseChange_tgtMap (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Function.Bijective (quasiRegularCanonicalMap (M := B) f)) :
    IsBaseChange A' (tgtMap (A := A) (A' := A') f) :=
  IsBaseChange.directSum fun n => isBaseChange_tgtMapComp (A := A) (A' := A') f hflat hf n

private theorem tgtMap_imgTargetLin (f : Fin r → B) (e : Fin r →₀ ℕ) (b : B) :
    tgtMap (A := A) (A' := A') f (imgTargetLin f e b) =
      imgTargetLin (KoszulH1.fp (A := A) (A' := A') f) e
        (KoszulH1.inclLeft (A := A) (A' := A') b) := by
  simp only [imgTargetLin, imgClassLin, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, tgtMap]
  change (DirectSum.lmap (fun n => tgtMapComp (A := A) (A' := A') f n))
      ((DirectSum.lof A ℕ (fun n => Tcomp B f n) (qrMdeg e))
        (Submodule.Quotient.mk ((fpowSmulRestrict f e) b))) =
    (DirectSum.lof A ℕ
      (fun n => Tcomp (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f) n)
      (qrMdeg e))
      (Submodule.Quotient.mk ((fpowSmulRestrict
        (KoszulH1.fp (A := A) (A' := A') f) e)
        (KoszulH1.inclLeft (A := A) (A' := A') b)))
  rw [DirectSum.lmap_lof, tgtMapComp_mk]
  have hm : KoszulH1.inclLeft (A := A) (A' := A') (fpow f e • b) =
      fpow (KoszulH1.fp (A := A) (A' := A') f) e •
        KoszulH1.inclLeft (A := A) (A' := A') b := by
    simpa only [smul_eq_mul] using map_fpow_mul (A := A) (A' := A') f e b
  exact congrArg _ (congrArg _ (Subtype.ext hm))

private theorem quasiRegularCanonicalMap_srcMap (f : Fin r → B) (x : Source B f) :
    quasiRegularCanonicalMap (M := B ⊗[A] A')
      (KoszulH1.fp (A := A) (A' := A') f)
      (srcMap (A := A) (A' := A') f x) =
    tgtMap (A := A) (A' := A') f (quasiRegularCanonicalMap (M := B) f x) := by
  obtain ⟨y, rfl⟩ := (srcFinsuppEquiv B f).symm.surjective x
  induction y using Finsupp.induction_linear with
  | zero => simp
  | single e mb =>
      induction mb using Submodule.Quotient.induction_on with
      | H b =>
          have hs :
              (srcFinsuppEquiv B f).symm
                (Finsupp.single e (Submodule.Quotient.mk b)) = srcMono f e b := by
            rw [← srcFinsuppEquiv_srcMono f e b, LinearEquiv.symm_apply_apply]
          rw [hs, srcMap_srcMono, canonicalMap_srcMono, canonicalMap_srcMono,
            tgtMap_imgTargetLin]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem bijective_of_isBaseChange_square
    {M N M' N' : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    [AddCommGroup N'] [Module A N'] [Module A' N'] [IsScalarTower A A' N']
    {u : M →ₗ[A] M'} {v : N →ₗ[A] N'}
    (hu : IsBaseChange A' u) (hv : IsBaseChange A' v)
    (φ : M →ₗ[A] N) (hφ : Function.Bijective φ) (φ' : M' →ₗ[A'] N')
    (hcomm : ∀ x, φ' (u x) = v (φ x)) :
    Function.Bijective φ' := by
  have hkey : φ' = hv.equiv.toLinearMap ∘ₗ φ.baseChange A' ∘ₗ hu.equiv.symm.toLinearMap := by
    apply hu.algHom_ext
    intro m
    have hm : hu.equiv.symm (u m) = 1 ⊗ₜ[A] m := by
      apply hu.equiv.injective
      simp [hu.equiv_tmul]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      hm, LinearMap.baseChange_tmul, hv.equiv_tmul, one_smul]
    exact hcomm m
  rw [hkey]
  exact (hv.equiv.bijective.comp
    (LinearEquiv.baseChange A A' M N (LinearEquiv.ofBijective φ hφ)).bijective).comp
    hu.equiv.symm.bijective

/-! ### The two halves of Tag 0CEP -/

private theorem quasiRegular_baseChange_of_quotient_flat
    (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : IsQuasiRegular B (List.ofFn f)) :
    IsQuasiRegular (B ⊗[A] A')
      (List.ofFn (KoszulH1.fp (A := A) (A' := A') f)) := by
  have hφ : Function.Bijective (quasiRegularCanonicalMap (M := B) f) := by
    change Function.Bijective (quasiRegularCanonicalMap (M := B)
      (fun i : Fin (List.ofFn f).length => (List.ofFn f)[i])) at hf
    exact (bijective_quasiRegularCanonicalMap_congr (by simp) f _
      (fun i => by simpa using List.get_ofFn f i)).mp hf
  have hφ' : Function.Bijective
      (quasiRegularCanonicalMap (M := B ⊗[A] A')
        (KoszulH1.fp (A := A) (A' := A') f)) :=
    bijective_of_isBaseChange_square
      (M := Source B f) (N := Target B f)
      (M' := Source (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f))
      (N' := Target (B ⊗[A] A') (KoszulH1.fp (A := A) (A' := A') f))
      (u := srcMap (A := A) (A' := A') f)
      (v := tgtMap (A := A) (A' := A') f)
      (isBaseChange_srcMap (A := A) (A' := A') f)
      (isBaseChange_tgtMap (A := A) (A' := A') f hflat hφ)
      ((quasiRegularCanonicalMap (M := B) f).restrictScalars A) hφ
      ((quasiRegularCanonicalMap (M := B ⊗[A] A')
        (KoszulH1.fp (A := A) (A' := A') f)).restrictScalars A')
      (quasiRegularCanonicalMap_srcMap (A := A) (A' := A') f)
  change Function.Bijective (quasiRegularCanonicalMap (M := B ⊗[A] A')
    (fun i : Fin (List.ofFn (KoszulH1.fp (A := A) (A' := A') f)).length =>
      (List.ofFn (KoszulH1.fp (A := A) (A' := A') f))[i]))
  exact (bijective_quasiRegularCanonicalMap_congr
    (by simp) (KoszulH1.fp (A := A) (A' := A') f) _
    (fun i => by simpa using
      List.get_ofFn (KoszulH1.fp (A := A) (A' := A') f) i)).mpr hφ'

private theorem h1Regular_baseChange_of_quotient_flat
    {A B A' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [Algebra A A'] {r : ℕ} (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (hf : Koszul.IsH1Regular f) :
    Koszul.IsH1Regular (KoszulH1.fp (A := A) (A' := A') f) := by
  change CategoryTheory.Limits.IsZero ((Koszul.seqComplex f).homology 1) at hf
  change CategoryTheory.Limits.IsZero
    ((Koszul.seqComplex (KoszulH1.fp (A := A) (A' := A') f)).homology 1)
  rw [ModuleCat.isZero_iff_subsingleton] at hf ⊢
  have : Subsingleton (KoszulH1.H1 f) :=
    ⟨fun _ _ => (Koszul.h1ConcreteIso f).injective (hf.elim _ _)⟩
  have htarget : Subsingleton (KoszulH1.H1 (KoszulH1.fp (A := A) (A' := A') f)) :=
    (KoszulH1.cmp_surjective f hflat).subsingleton
  let e := Koszul.h1ConcreteIso (KoszulH1.fp (A := A) (A' := A') f)
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  exact congrArg e (htarget.elim x' y')

/-! ### Tag 0CEP -/

/-- **Stacks Project, Tag 0CEP.** Suppose that `B / (f₁, …, fᵣ)` is flat over `A`. If `f` is
quasi-regular, then its image in `B ⊗[A] A'` is quasi-regular; if `f` is H₁-regular, then its
image is H₁-regular. -/
@[stacks 0CEP]
public theorem quasiRegular_and_h1Regular_baseChange_of_quotient_flat
    {A B A' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [Algebra A A'] {r : ℕ} (f : Fin r → B)
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f))) :
    (IsQuasiRegular B (List.ofFn f) →
      IsQuasiRegular (B ⊗[A] A')
        (List.ofFn (KoszulH1.fp (A := A) (A' := A') f))) ∧
    (Koszul.IsH1Regular f →
      Koszul.IsH1Regular (KoszulH1.fp (A := A) (A' := A') f)) :=
  ⟨quasiRegular_baseChange_of_quotient_flat f hflat,
    h1Regular_baseChange_of_quotient_flat f hflat⟩

/-! ### Reduction to the local fibres -/

section LocallyNilpotent

universe u v

private lemma flat_quotient_of_flat_localizations
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S)
    (h : ∀ (Q : Ideal S) [Q.IsMaximal],
      Module.Flat R ((Localization.AtPrime Q) ⧸ J.map (algebraMap S (Localization.AtPrime Q)))) :
    Module.Flat R (S ⧸ J) := by
  let N (Q : Ideal S) [Q.IsMaximal] :=
    (Localization.AtPrime Q) ⧸ J.localized' (Localization.AtPrime Q) Q.primeCompl
      (Algebra.linearMap S (Localization.AtPrime Q))
  apply Module.flat_of_isLocalized_maximal (R := R) S (S ⧸ J) N
    (fun Q hQ => by
      let : Q.IsMaximal := hQ
      exact J.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
        (Algebra.linearMap S (Localization.AtPrime Q)))
  intro Q hQ
  have he : J.localized' (Localization.AtPrime Q) Q.primeCompl
      (Algebra.linearMap S (Localization.AtPrime Q)) =
        J.map (algebraMap S (Localization.AtPrime Q)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  change Module.Flat R (_ ⧸ _)
  rw [he]
  exact h Q

/-- For an ideal `I` of `R` and an `R ⧸ I`-algebra `K`, the isomorphism of `R ⧸ I`-algebras
`(S ⧸ I S) ⊗[R ⧸ I] K ≃ K ⊗[R] S`. -/
public noncomputable def quotientBaseChangeEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (K : Type*) [CommRing K] [Algebra R K] [Algebra (R ⧸ I) K]
    [IsScalarTower R (R ⧸ I) K] :
    ((S ⧸ I.map (algebraMap R S)) ⊗[R ⧸ I] K) ≃ₐ[R ⧸ I] K ⊗[R] S :=
  (Algebra.TensorProduct.comm (R ⧸ I) _ _).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := R ⧸ I) (A₁ := K))
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I)).trans
      (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) (R ⧸ I) K S))

/-- `quotientBaseChangeEquiv I K` sends `[s] ⊗ₜ k` to `k ⊗ₜ s`. -/
public lemma quotientBaseChangeEquiv_tmul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (K : Type*) [CommRing K] [Algebra R K] [Algebra (R ⧸ I) K]
    [IsScalarTower R (R ⧸ I) K] (s : S) (k : K) :
    quotientBaseChangeEquiv I K ((Ideal.Quotient.mk _ s) ⊗ₜ k) = k ⊗ₜ[R] s := by
  simp [quotientBaseChangeEquiv]

/-- Quasi-regularity of a sequence is inherited by the image of the sequence under a flat ring
map. -/
public lemma isQuasiRegular_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    {l : List R} (hl : IsQuasiRegular R l) : IsQuasiRegular S (l.map φ) := by
  let := φ.toAlgebra
  have : Module.Flat R S := hφ
  exact hl.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

/-- Let `S → T` be flat, `I` an ideal of `R` and `K` an `R ⧸ I`-algebra. If the images of
`f₁, …, fᵣ` form a quasi-regular sequence in `S ⧸ I S` with flat quotient over `R ⧸ I`, then the
elements `1 ⊗ fᵢ` form a quasi-regular sequence in `K ⊗[R] T`. -/
public lemma isQuasiRegular_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T] (I : Ideal R) (K : Type*) [CommRing K] [Algebra R K]
    [Algebra (R ⧸ I) K] [IsScalarTower R (R ⧸ I) K]
    {r : ℕ} (f : Fin r → S)
    (hqr : IsQuasiRegular (S ⧸ I.map (algebraMap R S))
      (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
    (hflat : Module.Flat (R ⧸ I)
      ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))) :
    IsQuasiRegular (K ⊗[R] T) (List.ofFn (fun i ↦ (1 : K) ⊗ₜ[R] algebraMap S T (f i))) := by
  have h := (quasiRegular_and_h1Regular_baseChange_of_quotient_flat
    (A' := K) _ hflat).1 hqr
  let e := quotientBaseChangeEquiv (S := S) I K
  have h' := isQuasiRegular_map_of_flat e.toRingHom
    (RingHom.Flat.of_bijective e.bijective) h
  let g : K ⊗[R] S →ₐ[K] K ⊗[R] T :=
    Algebra.TensorProduct.lTensor K (IsScalarTower.toAlgHom R S T)
  have hg : g.Flat := (show (IsScalarTower.toAlgHom R S T).Flat from
    (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat S T›)).lTensor K
  have h'' := isQuasiRegular_map_of_flat g.toRingHom hg h'
  simpa [List.map_ofFn, Function.comp_def, KoszulH1.fp, KoszulH1.inclLeft,
    e, g, quotientBaseChangeEquiv_tmul] using h''

/-- The fibre of an `R`-algebra `T` over an ideal `m` of a localization `P` of `R` is the base
change of `P ⧸ m` along `R → T`. -/
public noncomputable def localizationFiberEquiv
    {R P T : Type*} [CommRing R] [CommRing P] [CommRing T]
    [Algebra R P] [Algebra R T] [Algebra P T] [IsScalarTower R P T]
    (U : Submonoid R) [IsLocalization U P] (m : Ideal P) :
    (T ⧸ m.map (algebraMap P T)) ≃+* (P ⧸ m) ⊗[R] T :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T m).toRingEquiv.trans
    (IsLocalization.algebraTensorEquiv U P (P ⧸ m) T).toRingEquiv

/-- `localizationFiberEquiv` sends the class of `t` to `1 ⊗ t`. -/
public lemma localizationFiberEquiv_mk
    {R P T : Type*} [CommRing R] [CommRing P] [CommRing T]
    [Algebra R P] [Algebra R T] [Algebra P T] [IsScalarTower R P T]
    (U : Submonoid R) [IsLocalization U P] (m : Ideal P) (t : T) :
    localizationFiberEquiv (T := T) U m (Ideal.Quotient.mk _ t) = 1 ⊗ₜ[R] t := rfl

/-- The inverse of `localizationFiberEquiv` sends `1 ⊗ t` to the class of `t`. -/
public lemma localizationFiberEquiv_symm_tmul_one
    {R P T : Type*} [CommRing R] [CommRing P] [CommRing T]
    [Algebra R P] [Algebra R T] [Algebra P T] [IsScalarTower R P T]
    (U : Submonoid R) [IsLocalization U P] (m : Ideal P) (t : T) :
    (localizationFiberEquiv (T := T) U m).symm (1 ⊗ₜ[R] t) = Ideal.Quotient.mk _ t :=
  (localizationFiberEquiv (T := T) U m).symm_apply_apply (Ideal.Quotient.mk _ t)

/-- A sequence of `S` that is quasi-regular modulo an ideal `I` of `R`, with flat quotient, has
regular image in the closed fibre of a local `R`-algebra `T` over a localization `P` of `R`.

This is the local half of the proof of tags 0CEQ and 0CER: by tag 0CEP the image of the sequence
is quasi-regular in the fibre, the fibre is Noetherian local, and tag 061S turns quasi-regularity
in a Noetherian local ring into regularity. -/
public lemma isRegular_fiber
    {R S P T : Type*} [CommRing R] [CommRing S] [CommRing P] [CommRing T]
    [Algebra R S] [Algebra R P] [Algebra R T] [Algebra P T] [Algebra S T]
    [IsScalarTower R S T] [IsScalarTower R P T]
    [IsLocalRing P] [IsLocalRing T] [IsLocalHom (algebraMap P T)]
    [Module.Flat S T] [Algebra.EssFiniteType R T]
    (U : Submonoid R) [IsLocalization U P]
    (I : Ideal R) (hI : I ≤ (IsLocalRing.maximalIdeal P).comap (algebraMap R P))
    {r : ℕ} (f : Fin r → S) (hf : ∀ i, algebraMap S T (f i) ∈ IsLocalRing.maximalIdeal T)
    (hqr : IsQuasiRegular (S ⧸ I.map (algebraMap R S))
      (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
    (hflat : Module.Flat (R ⧸ I)
      ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))) :
    IsRegular (T ⧸ (IsLocalRing.maximalIdeal P).map (algebraMap P T))
      (List.ofFn (fun i ↦ algebraMap S T (f i))) := by
  let m := IsLocalRing.maximalIdeal P
  let K := P ⧸ m
  let D := T ⧸ m.map (algebraMap P T)
  let : Field K := Ideal.Quotient.field m
  let : Algebra (R ⧸ I) K := Ideal.Quotient.algebraQuotientOfLEComap hI
  have : IsScalarTower R (R ⧸ I) K := .of_algebraMap_eq fun _ ↦ rfl
  have h := isQuasiRegular_baseChange (T := T) I K f hqr hflat
  let e := localizationFiberEquiv (T := T) U m
  have h' := isQuasiRegular_map_of_flat e.symm.toRingHom
    (RingHom.Flat.of_bijective e.symm.bijective) h
  have hqrD : IsQuasiRegular D (List.ofFn (fun i ↦ Ideal.Quotient.mk (m.map (algebraMap P T))
      (algebraMap S T (f i)))) := by
    rw [List.map_ofFn] at h'
    change IsQuasiRegular D (List.ofFn (fun i ↦
      e.symm ((1 : K) ⊗ₜ[R] algebraMap S T (f i)))) at h'
    simpa only [e, localizationFiberEquiv_symm_tmul_one] using h'
  have : IsNoetherianRing (K ⊗[R] T) := Algebra.EssFiniteType.isNoetherianRing K _
  have : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap P T)).ne
  have : IsLocalRing D := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (m.map (algebraMap P T))) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (m.map (algebraMap P T))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmem : ∀ i, Ideal.Quotient.mk (m.map (algebraMap P T))
      (algebraMap S T (f i)) ∈ IsLocalRing.maximalIdeal D := by
    intro i
    exact IsLocalRing.map_maximalIdeal_le (Ideal.Quotient.mk (m.map (algebraMap P T)))
      (Ideal.mem_map_of_mem _ (hf i))
  have hreg := ((Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae
    (M := D) _ hmem).2.out 4 1).mp hqrD
  have hc := (AddEquiv.refl D).isRegular_congr (R := T) (S := D)
    (as := List.ofFn (fun i ↦ algebraMap S T (f i)))
    (bs := (List.ofFn (fun i ↦ algebraMap S T (f i))).map (algebraMap T D))
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun t _ x ↦ by
        change t • x = algebraMap T D t • x
        exact (algebraMap_smul D t x).symm)))
  have hlist : (List.ofFn (fun i ↦ algebraMap S T (f i))).map (algebraMap T D) =
      List.ofFn (fun i ↦ Ideal.Quotient.mk (m.map (algebraMap P T))
        (algebraMap S T (f i))) := by
    rw [List.map_ofFn]
    rfl
  refine hc.mpr ?_
  rw [hlist]
  exact hreg

/-- A localization of a localization of an algebra of finite presentation is essentially of
finite presentation over the corresponding localization of the base. -/
public lemma essentiallyOfFinitePresentation_localization
    {R P : Type u} {S T : Type v} [CommRing R] [CommRing P] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R P] [Algebra R T] [Algebra P T] [Algebra S T]
    [IsScalarTower R S T] [IsScalarTower R P T] [Algebra.FinitePresentation R S]
    (M : Submonoid R) (N : Submonoid S) [IsLocalization M P] [IsLocalization N T]
    (hMN : Algebra.algebraMapSubmonoid S M ≤ N) :
    (algebraMap P T).EssentiallyOfFinitePresentation := by
  rw [RingHom.EssentiallyOfFinitePresentation, toAlgebra_algebraMap]
  let A := P ⊗[R] S
  let ψ : A →ₐ[P] T := Algebra.TensorProduct.lift (Algebra.ofId P T)
    (IsScalarTower.toAlgHom R S T) (fun _ _ ↦ Commute.all _ _)
  let : Algebra A T := ψ.toRingHom.toAlgebra
  let : Algebra S A := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower S A T := .of_algebraMap_eq fun s ↦ by
    change algebraMap S T s = ψ (1 ⊗ₜ[R] s)
    change algebraMap S T s = algebraMap P T 1 * algebraMap S T s
    simp
  have : IsScalarTower P A T := .of_algebraMap_eq fun p ↦ by
    change algebraMap P T p = ψ (p ⊗ₜ[R] 1)
    change algebraMap P T p = algebraMap P T p * algebraMap S T 1
    simp
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) A := inferInstance
  have : IsLocalization (N.map (algebraMap S A)) T :=
    IsLocalization.isLocalization_of_submonoid_le A T _ N hMN
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    N.map (algebraMap S A), inferInstance⟩

/-! ### Tag 0CEQ -/

/-- **Stacks Project, Tag 0CEQ.** A flat, finitely presented algebra remains flat after quotienting
by lifts of a quasi-regular sequence whose reduced quotient is flat. -/
@[stacks 0CEQ]
public theorem flat_quotient_span_of_isQuasiRegular_of_locallyNilpotent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (I : Ideal R) (hI : I ≤ nilradical R) {r : ℕ} (f : Fin r → S)
    (hqr : IsQuasiRegular (S ⧸ I.map (algebraMap R S))
      (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
    (hflat : Module.Flat (R ⧸ I)
      ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦
          Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))) :
    Module.Flat R (S ⧸ Ideal.span (Set.range f)) := by
  classical
  apply flat_quotient_of_flat_localizations
  intro Q hQ
  let T := Localization.AtPrime Q
  by_cases hf : ∀ i, f i ∈ Q
  · let p := Q.comap (algebraMap R S)
    have : p.IsPrime := Ideal.comap_isPrime _ _
    have : Q.LiesOver p := ⟨rfl⟩
    let P := Localization.AtPrime p
    let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p Q
    have : IsLocalHom (algebraMap P T) :=
      Localization.isLocalHom_localRingHom p Q (algebraMap R S) rfl
    have : Module.Flat P T :=
      (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
    have hI' : I ≤ (IsLocalRing.maximalIdeal P).comap (algebraMap R P) :=
      hI.trans (nilradical_le_prime _)
    have hreg := isRegular_fiber (P := P) (T := T) p.primeCompl I hI' f
      (fun i ↦ (IsLocalization.AtPrime.to_map_mem_maximal_iff T Q (f i)).mpr (hf i))
      hqr hflat
    have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
      essentiallyOfFinitePresentation_localization (S := S) p.primeCompl Q.primeCompl
        (by rintro _ ⟨x, hx, rfl⟩; exact hx)
    have hreg' : IsRegular
        (T ⧸ ((IsLocalRing.maximalIdeal P).map (algebraMap P T) • (⊤ : Submodule T T)))
        (List.ofFn (fun i ↦ algebraMap S T (f i))) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hreg
    have ht := (Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
      (R := P) (S := T) (M := T) hess _ hreg').2 r
    have he : Ideal.ofList ((List.ofFn (fun i ↦ algebraMap S T (f i))).take r) •
        (⊤ : Submodule T T) = (Ideal.span (Set.range f)).map (algebraMap S T) := by
      rw [List.take_of_length_le (by simp), Ideal.smul_eq_mul, Ideal.mul_top,
        Ideal.ofList_ofFn, Ideal.map_span, ← Set.range_comp]
      rfl
    rw [he] at ht
    have : Module.Flat P (T ⧸ (Ideal.span (Set.range f)).map (algebraMap S T)) := ht
    exact Module.Flat.trans R P _
  · obtain ⟨i, hi⟩ := not_forall.mp hf
    have he : (Ideal.span (Set.range f)).map (algebraMap S T) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i)))
        (IsLocalization.map_units T (⟨f i, hi⟩ : Q.primeCompl))
    have : Subsingleton (T ⧸ (Ideal.span (Set.range f)).map (algebraMap S T)) :=
      Ideal.Quotient.subsingleton_iff.mpr he
    exact inferInstance

/-! ### Tag 0CER -/

/-- Quotienting `S ⧸ I S` by the image of `f` is the base change to `R ⧸ I` of `S ⧸ (f)`. -/
private noncomputable def quotientSpanQuotientMapEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) {r : ℕ}
    (f : Fin r → S) :
    ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
      ≃ₐ[R ⧸ I] TensorProduct R (R ⧸ I) (S ⧸ Ideal.span (Set.range f)) :=
  have hL : Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))) =
      (Ideal.span (Set.range f)).map (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hK : (I.map (algebraMap R S)).map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) =
      I.map (algebraMap R (S ⧸ Ideal.span (Set.range f))) := by
    calc
      _ = I.map ((Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toRingHom.comp
          (algebraMap R S)) := Ideal.map_map _ _
      _ = _ := by congr 1
  (AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (((Ideal.quotientEquivAlgOfEq R hL).trans
      (DoubleQuot.quotQuotEquivCommₐ R _ _)).trans (Ideal.quotientEquivAlgOfEq R hK))).trans
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (S ⧸ Ideal.span (Set.range f)) I)

/-- **Stacks Project, Tag 0CER.** A flat, finitely presented algebra remains smooth after
quotienting by lifts of a quasi-regular sequence whose reduced quotient is smooth. -/
@[stacks 0CER]
public theorem smooth_quotient_span_of_isQuasiRegular_of_locallyNilpotent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (I : Ideal R) (hI : I ≤ nilradical R) {r : ℕ} (f : Fin r → S)
    (hqr : IsQuasiRegular (S ⧸ I.map (algebraMap R S))
      (List.ofFn (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))
    (hsmooth : Algebra.Smooth (R ⧸ I)
      ((S ⧸ I.map (algebraMap R S)) ⧸
        Ideal.span (Set.range (fun i ↦
          Ideal.Quotient.mk (I.map (algebraMap R S)) (f i))))) :
    Algebra.Smooth R (S ⧸ Ideal.span (Set.range f)) := by
  have : Module.Flat R (S ⧸ Ideal.span (Set.range f)) :=
    flat_quotient_span_of_isQuasiRegular_of_locallyNilpotent I hI f hqr inferInstance
  have : Algebra.FinitePresentation R (S ⧸ Ideal.span (Set.range f)) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range f))
  apply Algebra.Smooth.of_formallySmooth_fiber
  intro p hp
  have hpI : I ≤ p := hI.trans (nilradical_le_prime p)
  let φ : R ⧸ I →+* p.ResidueField :=
    Ideal.Quotient.lift I (algebraMap R p.ResidueField) (fun x hx ↦ by
      rw [← RingHom.mem_ker]
      exact (Ideal.ker_algebraMap_residueField p).symm ▸ hpI hx)
  let : Algebra (R ⧸ I) p.ResidueField := φ.toAlgebra
  have : IsScalarTower R (R ⧸ I) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let J : Ideal S := Ideal.span (Set.range f)
  let K : Ideal S := I.map (algebraMap R S)
  let L : Ideal (S ⧸ K) := Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk K (f i)))
  let e : ((S ⧸ K) ⧸ L) ≃ₐ[R ⧸ I] TensorProduct R (R ⧸ I) (S ⧸ J) :=
    quotientSpanQuotientMapEquiv I f
  have : Algebra.Smooth (R ⧸ I) ((S ⧸ K) ⧸ L) := by
    simpa [K, L] using hsmooth
  have : Algebra.Smooth p.ResidueField
      (TensorProduct (R ⧸ I) p.ResidueField ((S ⧸ K) ⧸ L)) :=
    Algebra.Smooth.baseChange (R ⧸ I) ((S ⧸ K) ⧸ L) p.ResidueField
  let ee : TensorProduct (R ⧸ I) p.ResidueField ((S ⧸ K) ⧸ L) ≃ₐ[p.ResidueField]
      (p.Fiber (S ⧸ J)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl) e).trans
      (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) p.ResidueField p.ResidueField (S ⧸ J))
  have hee : Algebra.FormallySmooth p.ResidueField (p.Fiber (S ⧸ J)) :=
    Algebra.FormallySmooth.of_equiv
      (A := TensorProduct (R ⧸ I) p.ResidueField ((S ⧸ K) ⧸ L)) ee
  simpa [J] using hee

end LocallyNilpotent

end Koszul
