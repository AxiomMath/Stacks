module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationAgreementOverAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.PowerTorsionOfCompletion
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The equalizer of two formal morphisms out of a completion, cut out by torsion functions

Let `V` be an affine object of the big fppf site of `S` with Noetherian ring of global sections
`A`, let `Z = V(I)`, and let `x₁, x₂ : V_{/Z} ⟶ W` be morphisms of fppf sheaves whose equalizer
`E_W ⟶ V_{/Z}` is a closed immersion. Over the thickening `Spec (A / Iⁿ)` the equalizer is a
closed subscheme cut out by an ideal `J n ⊇ Iⁿ`, and the `J n` can be chosen with
`J n = J (n + 1) ⊔ Iⁿ`. If moreover some proper `p : Y ⟶ V` through which `V ∖ Z ⟶ V` lifts has
`Y_{/Z} ⟶ V_{/Z}` factoring through `E_W`, then the formal functions `x ∈ Â` vanishing on `E_W`
(those with `n`-th component in the image of `J n` for every `n`) are killed by a power of `I`:
on `Y ×_V Spec Â` such an `x` vanishes, since it vanishes on the completion along the inverse
image of `Z` and the inverse image of `Z` meets every closed subset
(`AlgebraicGeometry.Space.eq_of_completion_eq_of_closed_meets`); and for `a ∈ I` the basic open
`D(a) ⊆ Spec Â` lifts to `Y ×_V Spec Â`. Finitely many such `x` generate the ideal, and they come
from `I`-power torsion elements of `A`
(`AdicCompletion.exists_algebraMap_eq_of_pow_smul_eq_zero`). Hence `E_W` is cut out, over every
thickening, by a finite set of `I`-power torsion elements of `A`.

This is the algebraic core of the injectivity half of the proof of Stacks 0GI5. The source
quotes Lemma 0GHE at this point, which needs the equalizer `E'` of the two witnesses to be
proper over `V`; that fails for non-separated `X'`. Here only the properness of one witness is
used, after it has been related to the other one by a morphism at a finite stage.

## Main results

* `AlgebraicGeometry.Space.exists_ideals_of_isClosedImmersion_equalizer`: the ideals `J n`.
* `AdicCompletion.exists_forall_evalₐ_mem_of_eq_sup_pow`: lifting through a system of ideals
  with surjective transitions.
* `AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_isProper`: formal functions vanishing on the
  equalizer are `I`-power torsion.
* `AlgebraicGeometry.Space.exists_finset_torsion_iff_of_isProper`: the equalizer is cut out by
  finitely many `I`-power torsion elements of `A`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AdicCompletion

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- A sequence of ideals `J n` with `J n = J (n + 1) ⊔ Iⁿ` is decreasing. -/
theorem antitone_of_eq_sup_pow {J : ℕ → Ideal A} (hJ : ∀ n, J n = J (n + 1) ⊔ I ^ n) :
    Antitone J :=
  antitone_nat_of_succ_le fun n => (hJ n).symm ▸ le_sup_left

/-- **Lifting through a system of ideals with surjective transitions.** If `J n = J (n + 1) ⊔ Iⁿ`
for all `n`, every element of `J n` is, modulo `Iⁿ`, the `n`-th component of an element of the
`I`-adic completion all of whose components lie in the images of the `J m`. -/
theorem exists_forall_evalₐ_mem_of_eq_sup_pow {J : ℕ → Ideal A}
    (hJ : ∀ n, J n = J (n + 1) ⊔ I ^ n) {n : ℕ} {a : A} (ha : a ∈ J n) :
    ∃ x : AdicCompletion I A, (∀ m, evalₐ I m x ∈ (J m).map (Ideal.Quotient.mk (I ^ m))) ∧
      evalₐ I n x = Ideal.Quotient.mk (I ^ n) a := by
  have step : ∀ k (c : J (n + k)), ∃ c' : J (n + k + 1), (c : A) - c' ∈ I ^ (n + k) := by
    intro k c
    have hc : (c : A) ∈ J (n + k + 1) ⊔ I ^ (n + k) := hJ (n + k) ▸ c.2
    rw [Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, hyz⟩ := hc
    exact ⟨⟨y, hy⟩, by rwa [← hyz, add_sub_cancel_left]⟩
  choose next hnext using step
  let g : (k : ℕ) → J (n + k) := fun k =>
    Nat.rec (motive := fun k => ↥(J (n + k))) ⟨a, ha⟩ (fun k c => next k c) k
  have hg : ∀ k, (g k : A) - g (k + 1) ∈ I ^ (n + k) := fun k => hnext k (g k)
  let f : AdicCauchySequence I A := AdicCauchySequence.mk I A (fun k => (g k : A)) (fun k => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (by omega) (hg k))
  refine ⟨mk I A f, fun m => ?_, ?_⟩
  · rw [evalₐ_mk]
    exact Ideal.mem_map_of_mem _ (antitone_of_eq_sup_pow hJ (by omega : m ≤ n + m) (g m).2)
  · rw [evalₐ_mk, Ideal.Quotient.eq]
    have h0 : ∀ d, (g 0 : A) - g d ∈ I ^ n := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [show (g 0 : A) - g (d + 1) = ((g 0 : A) - g d) + ((g d : A) - g (d + 1)) by ring]
        exact add_mem ih (Ideal.pow_le_pow_right (by omega) (hg d))
    rw [← neg_mem_iff, neg_sub]
    exact h0 n


/-- A ring map out of the `I`-adic completion killing the image of `Iⁿ` kills every element whose
`n`-th component vanishes. -/
theorem map_eq_zero_of_evalₐ_eq_zero [IsNoetherianRing A] {R : Type*} [CommRing R]
    (ψ : AdicCompletion I A →+* R)
    {n : ℕ} (hψ : ∀ a ∈ I ^ n, ψ (algebraMap A (AdicCompletion I A) a) = 0)
    {x : AdicCompletion I A} (hx : evalₐ I n x = 0) : ψ x = 0 := by
  have hle : I ^ n ≤ I ^ n • (⊤ : Ideal A) := by rw [smul_eq_mul, Ideal.mul_top]
  have hx' : x ∈ LinearMap.ker (eval I A n) := by
    rw [LinearMap.mem_ker, ← factor_evalₐ_eq_eval I x hle, hx, _root_.map_zero]
  rw [← pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I)] at hx'
  refine Submodule.smul_induction_on hx' (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · rw [Algebra.smul_def, _root_.map_mul, hψ a ha, zero_mul]
  · rw [_root_.map_add, hy, hz, add_zero]

/-- The `n`-th component of the image of `c : A` in the `I`-adic completion is the class of `c`. -/
private theorem evalₐ_algebraMap_eq_mk (n : ℕ) (c : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) c) = Ideal.Quotient.mk (I ^ n) c := by
  rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

/-- A ring map out of the `I`-adic completion killing the image of `Iⁿ` takes the same value on
two elements with the same `n`-th component. -/
theorem map_eq_map_algebraMap_of_evalₐ_eq [IsNoetherianRing A] {R : Type*} [CommRing R]
    (ψ : AdicCompletion I A →+* R) {n : ℕ}
    (hψ : ∀ a ∈ I ^ n, ψ (algebraMap A (AdicCompletion I A) a) = 0)
    {x : AdicCompletion I A} {c : A} (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    ψ x = ψ (algebraMap A (AdicCompletion I A) c) := by
  rw [← sub_eq_zero, ← _root_.map_sub]
  refine map_eq_zero_of_evalₐ_eq_zero ψ hψ ?_
  rw [_root_.map_sub, hx, evalₐ_algebraMap_eq_mk, sub_self]

end AdicCompletion

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism from an affine scheme mapping into the zero locus of a finitely generated ideal
kills a power of it on global sections. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_pow_le_ker_appTop {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Y) (K : Ideal Γ(Y, ⊤)) (hK : K.FG)
    (h : ∀ x, f x ∈ Y.zeroLocus (K : Set Γ(Y, ⊤))) :
    ∃ n, K ^ n ≤ RingHom.ker f.appTop.hom := by
  have h1 : X.zeroLocus (f.appTop.hom '' (K : Set Γ(Y, ⊤))) = Set.univ :=
    (Scheme.preimage_zeroLocus f _).symm.trans (Set.eq_univ_of_forall h)
  have h2 : PrimeSpectrum.zeroLocus (f.appTop.hom '' (K : Set Γ(Y, ⊤))) = Set.univ := by
    rw [← X.isoSpec_inv_preimage_zeroLocus, h1]
    rfl
  rw [PrimeSpectrum.zeroLocus_eq_univ_iff] at h2
  refine Ideal.exists_pow_le_of_le_radical_of_fg (fun a ha => ?_) hK
  obtain ⟨k, hk⟩ := h2 ⟨a, ha, rfl⟩
  exact ⟨k, by rw [RingHom.mem_ker, map_pow, hk]⟩

section Quotient

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- On global sections, `Spec (Γ(X) ⧸ K) ⟶ Spec Γ(X) ≅ X` sends `a` to the class of `a`. -/
theorem _root_.AlgebraicGeometry.Scheme.appTop_specMap_mk_comp_isoSpec_inv_apply (X : Scheme.{u})
    [IsAffine X] (K : Ideal Γ(X, ⊤)) (a : Γ(X, ⊤)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.isoSpec.inv).appTop a =
      (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ K))).inv (Ideal.Quotient.mk K a) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Stacks.RelativeSpec.isoSpec_inv_appTop,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- On global sections, `Spec R ⟶ Spec Γ(X) ≅ X` induced by `f : Γ(X) →+* R` sends `a` to `f a`. -/
theorem _root_.AlgebraicGeometry.Scheme.appTop_specMap_comp_isoSpec_inv_apply (X : Scheme.{u})
    [IsAffine X] {R : Type u} [CommRing R] (f : Γ(X, ⊤) →+* R) (a : Γ(X, ⊤)) :
    (Spec.map (CommRingCat.ofHom f) ≫ X.isoSpec.inv).appTop a =
      (Scheme.ΓSpecIso (.of R)).inv (f a) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Stacks.RelativeSpec.isoSpec_inv_appTop,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The kernel of the map on global sections of `Spec (Γ(X) ⧸ K) ⟶ X` is `K`. -/
theorem _root_.AlgebraicGeometry.Scheme.ker_appTop_specMap_mk_comp_isoSpec_inv (X : Scheme.{u})
    [IsAffine X] (K : Ideal Γ(X, ⊤)) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫
      X.isoSpec.inv).appTop.hom = K := by
  ext a
  rw [RingHom.mem_ker, Scheme.appTop_specMap_mk_comp_isoSpec_inv_apply,
    ← Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have := congrArg (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ K))).hom.hom h
  rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The map on global sections of `Spec (Γ(X) ⧸ K) ⟶ X` is surjective. -/
theorem _root_.AlgebraicGeometry.Scheme.surjective_appTop_specMap_mk_comp_isoSpec_inv
    (X : Scheme.{u}) [IsAffine X] (K : Ideal Γ(X, ⊤)) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫
      X.isoSpec.inv).appTop.hom := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ K))).hom.hom y)
  refine ⟨a, ?_⟩
  rw [Scheme.appTop_specMap_mk_comp_isoSpec_inv_apply, ha, ← CommRingCat.comp_apply,
    Iso.hom_inv_id, CommRingCat.id_apply]

/-- The kernel of the map on global sections of `Spec (A / Kⁿ) ⟶ V` is `Kⁿ`. -/
theorem ker_appTop_adicCompletionQuotientObjHom (n : ℕ) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map
      (adicCompletionQuotientObjHom B S hS V K n)).appTop.hom = K ^ n :=
  Scheme.ker_appTop_specMap_mk_comp_isoSpec_inv _ (K ^ n)

/-- The map on global sections of `Spec (A / Kⁿ) ⟶ V` is surjective. -/
theorem surjective_appTop_adicCompletionQuotientObjHom (n : ℕ) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map
      (adicCompletionQuotientObjHom B S hS V K n)).appTop.hom :=
  Scheme.surjective_appTop_specMap_mk_comp_isoSpec_inv _ (K ^ n)

/-- The morphism of schemes underlying `Spec (A / Kⁿ) ⟶ V` is a closed immersion. -/
instance isClosedImmersion_adicCompletionQuotientObjHom (n : ℕ) :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (adicCompletionQuotientObjHom B S hS V K n)) := by
  change AlgebraicGeometry.IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ n))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
  infer_instance

/-- A morphism into `V` factors through `Spec (A / Kⁿ)` exactly when it kills `Kⁿ` on global
sections. -/
theorem exists_comp_adicCompletionQuotientObjHom_iff {T : BigFppfOver B S hS} (t : T ⟶ V)
    (n : ℕ) :
    (∃ t' : T ⟶ adicCompletionQuotientObj B S hS V K n,
        t' ≫ adicCompletionQuotientObjHom B S hS V K n = t) ↔
      K ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom := by
  rw [FormalSpace.exists_comp_eq_iff_ker_le, ker_appTop_adicCompletionQuotientObjHom]

/-- A morphism factoring through `Spec (A / Iⁿ)` has point-set image in `V(I)`. -/
theorem hasImageIn_of_comp_adicCompletionQuotientObjHom
    {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    {Z : Set (points B S hS (yoneda.obj V))}
    (hTI : ∀ x, x ∈ Z ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {n : ℕ} {T : BigFppfOver B S hS} (t' : T ⟶ adicCompletionQuotientObj B S hS V I n) :
    HasImageIn B S hS (yoneda.obj V) Z T (t' ≫ adicCompletionQuotientObjHom B S hS V I n) :=
  (completionSubfunctor B S hS (yoneda.obj V) Z).map t'.op
    (hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI n)

end Quotient

/-! ### The ideals of the equalizer over the thickenings -/

section Criterion

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (points B S hS (yoneda.obj V))}
  (hTI : ∀ x, x ∈ Z ↔ pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  {W : FormalSpace.FppfSheaf B S hS} (x₁ x₂ : completionSheaf B S hS (yoneda.obj V) Z ⟶ W)

include hTI in
/-- **The equalizer over the `n`-th thickening is cut out by an ideal.** If the equalizer of
`x₁, x₂ : V_{/Z} ⟶ W` is a closed immersion, then for each `n` there is an ideal `J ⊇ Iⁿ` of `A`
such that a morphism `t : T ⟶ V` killing `Iⁿ` equalizes `x₁` and `x₂` exactly when it kills
`J`. -/
theorem exists_ideal_iff_of_isClosedImmersion_equalizer
    (hE : FormalSpace.IsClosedImmersion B S hS (equalizer.ι x₁ x₂)) (n : ℕ) :
    ∃ J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤), I ^ n ≤ J ∧
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (ht : HasImageIn B S hS (yoneda.obj V) Z T t),
        I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
        (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
            x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
          J ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom) := by
  let Q := adicCompletionQuotientObj B S hS V I n
  let q := adicCompletionQuotientObjHom B S hS V I n
  have hq := hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI n
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Q) :=
    inferInstanceAs (IsAffine (Spec _))
  let ξ : uliftYoneda.{u + 1}.obj Q ⟶ (completionSheaf B S hS (yoneda.obj V) Z).obj :=
    uliftYonedaEquiv.symm (FormalSpace.presheafSection B S hS q hq)
  obtain ⟨R, r, hr, hrep⟩ :=
    FormalSpace.exists_isClosedImmersion_represents_equalizer x₁ x₂ hE Q ξ
  have hker : ∀ {T' : BigFppfOver B S hS} (u : T' ⟶ Q) (a),
      a ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map (u ≫ q)).appTop.hom ↔
        ((BigFppfOver.toScheme B S hS).map u).appTop.hom
          (((BigFppfOver.toScheme B S hS).map q).appTop.hom a) = 0 := fun u a => by
    rw [RingHom.mem_ker, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  refine ⟨RingHom.ker ((BigFppfOver.toScheme B S hS).map (r ≫ q)).appTop.hom, fun a ha => ?_, ?_⟩
  · have h0 : ((BigFppfOver.toScheme B S hS).map q).appTop.hom a = 0 := by
      rwa [← RingHom.mem_ker, ker_appTop_adicCompletionQuotientObjHom]
    rw [hker, h0, map_zero]
  intro T t ht htI
  obtain ⟨t', rfl⟩ := (exists_comp_adicCompletionQuotientObjHom_iff V I t n).mpr htI
  have hsec : ∀ y : completionSheaf B S hS (yoneda.obj V) Z ⟶ W,
      y.hom.app (op T) (FormalSpace.presheafSection B S hS (t' ≫ q) ht) =
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map t' ≫ ξ ≫ y.hom) := by
    intro y
    rw [← Category.assoc, uliftYonedaEquiv_comp]
    congr 1
    have e : uliftYoneda.{u + 1}.map t' ≫ ξ = uliftYonedaEquiv.symm
        ((completionSheaf B S hS (yoneda.obj V) Z).obj.map t'.op
          (FormalSpace.presheafSection B S hS q hq)) :=
      (uliftYonedaEquiv_symm_map t'.op _).symm
    rw [e, Equiv.apply_symm_apply]
    have ht' : HasImageIn B S hS (yoneda.obj V) Z T ((yoneda.obj V).map t'.op q) := by
      rwa [yoneda_obj_map, Quiver.Hom.unop_op]
    rw [FormalSpace.presheafSection_map (F := yoneda.obj V) (TF := Z) B S hS t' q hq ht']
    congr 1
  rw [hsec, hsec, uliftYonedaEquiv.injective.eq_iff, ← hrep T t',
    FormalSpace.exists_comp_eq_iff_ker_le]
  refine ⟨fun h a ha => (hker t' a).mpr (h ((hker r a).mp ha)), fun h b hb => ?_⟩
  obtain ⟨a, rfl⟩ := surjective_appTop_adicCompletionQuotientObjHom V I n b
  exact (hker t' a).mp (h ((hker r a).mpr hb))

include hTI in
/-- A morphism into `V` killing a power of `I` has point-set image in `Z = V(I)`. -/
theorem hasImageIn_of_pow_le_ker {T : BigFppfOver B S hS} (t : T ⟶ V) {n : ℕ}
    (h : I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom) :
    HasImageIn B S hS (yoneda.obj V) Z T t := by
  obtain ⟨t', rfl⟩ := (exists_comp_adicCompletionQuotientObjHom_iff V I t n).mpr h
  exact hasImageIn_of_comp_adicCompletionQuotientObjHom V hTI t'

include hTI in
/-- **The ideals of the equalizer over the thickenings form a system with surjective
transitions**: they can be chosen with `J n = J (n + 1) ⊔ Iⁿ`. -/
theorem exists_ideals_of_isClosedImmersion_equalizer
    (hE : FormalSpace.IsClosedImmersion B S hS (equalizer.ι x₁ x₂)) :
    ∃ J : ℕ → Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      (∀ n, I ^ n ≤ J n ∧
        ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (ht : HasImageIn B S hS (yoneda.obj V) Z T t),
          I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
          (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
              x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
            J n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom)) ∧
      ∀ n, J n = J (n + 1) ⊔ I ^ n := by
  choose J hJ₀ hJ using fun n => exists_ideal_iff_of_isClosedImmersion_equalizer hTI x₁ x₂ hE n
  refine ⟨J, fun n => ⟨hJ₀ n, hJ n⟩, fun n => ?_⟩
  have himg : ∀ (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (m : ℕ), I ^ m ≤ K →
      HasImageIn B S hS (yoneda.obj V) Z (adicCompletionQuotientObj B S hS V K 1)
        (adicCompletionQuotientObjHom B S hS V K 1) :=
    fun K m hm => hasImageIn_of_pow_le_ker hTI _ (n := m)
      (by rwa [ker_appTop_adicCompletionQuotientObjHom, pow_one])
  have test : ∀ (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (m : ℕ) (hm : I ^ m ≤ K),
      (x₁.hom.app (op (adicCompletionQuotientObj B S hS V K 1)) (FormalSpace.presheafSection B S hS
          (adicCompletionQuotientObjHom B S hS V K 1) (himg K m hm)) =
        x₂.hom.app (op (adicCompletionQuotientObj B S hS V K 1)) (FormalSpace.presheafSection B S hS
          (adicCompletionQuotientObjHom B S hS V K 1) (himg K m hm)) ↔
        J m ≤ K) := fun K m hm =>
    (hJ m _ (adicCompletionQuotientObjHom B S hS V K 1) (himg K m hm)
      (by rwa [ker_appTop_adicCompletionQuotientObjHom, pow_one])).trans
      (by rw [ker_appTop_adicCompletionQuotientObjHom, pow_one])
  have hle : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
  apply le_antisymm
  · have hK : I ^ n ≤ J (n + 1) ⊔ I ^ n := le_sup_right
    exact (test _ n hK).mp ((test _ (n + 1) (hle.trans hK)).mpr le_sup_left)
  · refine sup_le ?_ (hJ₀ n)
    exact (test _ (n + 1) (hle.trans (hJ₀ n))).mp ((test _ n (hJ₀ n)).mpr le_rfl)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
include hTI in
/-- A morphism `T ⟶ V` with point-set image in `Z = V(I)` maps every point of `T` into the zero
locus of `I`. -/
theorem toScheme_map_mem_zeroLocus_of_hasImageIn {T : BigFppfOver B S hS} {s : T ⟶ V}
    (hs : HasImageIn B S hS (yoneda.obj V) Z T s) (y : (BigFppfOver.toScheme B S hS).obj T) :
    (BigFppfOver.toScheme B S hS).map s y ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := by
  have hz : yonedaEquiv.symm s = yoneda.map s := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  rw [hasImageIn_iff_range_subset, hz] at hs
  have h := hs ⟨(schemePointsHomeomorph B S hS T).symm y, rfl⟩
  rwa [hTI, pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply,
    Homeomorph.apply_symm_apply] at h

include hTI in
/-- **Formal functions vanishing on the equalizer vanish on points of it.** Let `J n` be the
ideals cutting out the equalizer of `x₁, x₂` over the thickenings, and let `x ∈ Â` have all its
components in the images of the `J m`. For an affine `T` and `g : T ⟶ Spec Â` whose composite
with `Spec Â ⟶ V` equalizes `x₁` and `x₂`, the pullback of `x` to `T` vanishes. -/
theorem appTop_eq_zero_of_forall_evalₐ_mem
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {J : ℕ → Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hJ : ∀ n (T : BigFppfOver B S hS) (t : T ⟶ V)
      (ht : HasImageIn B S hS (yoneda.obj V) Z T t),
        I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
        (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
            x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
          J n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom))
    {x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hx : ∀ m, AdicCompletion.evalₐ I m x ∈ (J m).map (Ideal.Quotient.mk (I ^ m)))
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (g : T ⟶ adicCompletionObj B S hS V I)
    (hg : HasImageIn B S hS (yoneda.obj V) Z T (g ≫ adicCompletionObjHom B S hS V I))
    (heq : x₁.hom.app (op T) (FormalSpace.presheafSection B S hS _ hg) =
      x₂.hom.app (op T) (FormalSpace.presheafSection B S hS _ hg)) :
    ((BigFppfOver.toScheme B S hS).map g).appTop
      ((Scheme.ΓSpecIso (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv
        x) = 0 := by
  let s := g ≫ adicCompletionObjHom B S hS V I
  obtain ⟨n, hn⟩ := Scheme.exists_pow_le_ker_appTop ((BigFppfOver.toScheme B S hS).map s) I
    (Ideal.fg_of_isNoetherianRing I) (toScheme_map_mem_zeroLocus_of_hasImageIn hTI hg)
  have hJn := (hJ n T s hg hn).mp heq
  obtain ⟨c, hc, hcx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hx n)
  let ψ : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((Scheme.ΓSpecIso (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv ≫
      ((BigFppfOver.toScheme B S hS).map g).appTop).hom
  have hψ : ∀ a, ψ (algebraMap _ _ a) = ((BigFppfOver.toScheme B S hS).map s).appTop a := by
    intro a
    have e : ((BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I)).appTop a =
        (Scheme.ΓSpecIso (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv
          (algebraMap _ _ a) :=
      Scheme.appTop_specMap_comp_isoSpec_inv_apply _ _ a
    show _ = ((BigFppfOver.toScheme B S hS).map (g ≫ adicCompletionObjHom B S hS V I)).appTop a
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e]
    rfl
  show ψ x = 0
  rw [AdicCompletion.map_eq_map_algebraMap_of_evalₐ_eq ψ (n := n)
    (fun a ha => (hψ a).trans (RingHom.mem_ker.mp (hn ha))) hcx.symm, hψ]
  exact hJn hc

end Criterion

/-! ### Functions as morphisms to the affine line -/

/-- The ring map on global sections of `Spec R ⟶ Spec Γ(X) ≅ X`. -/
theorem _root_.AlgebraicGeometry.Scheme.appTop_specMap_comp_isoSpec_inv (X : Scheme.{u})
    [IsAffine X] {R : CommRingCat.{u}} (f : Γ(X, ⊤) ⟶ R) :
    (Spec.map f ≫ X.isoSpec.inv).appTop = f ≫ (Scheme.ΓSpecIso R).inv := by
  rw [Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop,
    Scheme.ΓSpecIso_inv_naturality]

/-- On global sections, `Spec.map φ` sends the function `x` on `Spec R` to the function `φ x` on
`Spec R'`. -/
theorem _root_.AlgebraicGeometry.Scheme.appTop_specMap_ΓSpecIso_inv_apply
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (x : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso R').inv (φ x) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- Two evaluations `A[X] ⟶ R` at `c` and at `0`, composed with a morphism `h : Y ⟶ Spec R`,
agree exactly when `h` kills `c` on global sections. -/
theorem _root_.AlgebraicGeometry.Scheme.comp_specMap_eval₂_eq_iff {Y : Scheme.{u}}
    {R : CommRingCat.{u}} {A : Type u} [CommRing A] (f : A →+* R) (h : Y ⟶ Spec R) (c : R) :
    h ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f c)) =
        h ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f 0)) ↔
      h.appTop ((Scheme.ΓSpecIso R).inv c) = 0 := by
  have key : ∀ (d : R) (P : Polynomial A),
      (h ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f d))).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv P) =
        h.appTop ((Scheme.ΓSpecIso R).inv (Polynomial.eval₂ f d P)) := by
    intro d P
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.appTop_specMap_ΓSpecIso_inv_apply]
    rfl
  refine ⟨fun e => ?_, fun hc => ?_⟩
  · simpa only [key, Polynomial.eval₂_X, map_zero] using
      congrArg (fun k => (Scheme.Hom.appTop k).hom
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv Polynomial.X)) e
  refine ext_of_isAffine ?_
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (Polynomial A))).inv]
  ext1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    show (h ≫ _).appTop ((Scheme.ΓSpecIso (.of (Polynomial A))).inv _) =
      (h ≫ _).appTop ((Scheme.ΓSpecIso (.of (Polynomial A))).inv _)
    rw [key, key, Polynomial.eval₂_C, Polynomial.eval₂_C]
  · simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    show (h ≫ _).appTop ((Scheme.ΓSpecIso (.of (Polynomial A))).inv _) =
      (h ≫ _).appTop ((Scheme.ΓSpecIso (.of (Polynomial A))).inv _)
    rw [key, key, Polynomial.eval₂_X, Polynomial.eval₂_X, hc, map_zero, map_zero]

/-- The evaluation at `c` of `A[X]` in an `A`-algebra `R` is a section of `Spec R ⟶ Spec A`
over `Spec A`. -/
theorem _root_.AlgebraicGeometry.specMap_eval₂RingHom_comp_specMap_C {A R : Type u}
    [CommRing A] [CommRing R] [Algebra A R] (c : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap A R) c)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Polynomial.eval₂RingHom_comp_C]

section AffineLine

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- The affine line `Spec A[X]` over an affine object `V` of the site with `A = Γ(V)`, structured
over `S` through `V`. -/
noncomputable def affineLineObj : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (Polynomial Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (contains_spec_globalSections B S hS V))
    (Spec.map (CommRingCat.ofHom Polynomial.C) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom)

/-- The function `c` on `Spec Â`, as a morphism `Spec Â ⟶ Spec A[X]` over `V`. -/
noncomputable def adicCompletionObjToAffineLine
    (c : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    adicCompletionObj B S hS V I ⟶ affineLineObj V :=
  BigFppfOver.homMk B S hS _ _
    (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) c))) (by
    refine (?_ : Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) c)) ≫
        ((Spec.map (CommRingCat.ofHom Polynomial.C) ≫
          ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv) ≫ B.inclusion.map V.hom) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom)
    rw [Category.assoc, ← Category.assoc, specMap_eval₂RingHom_comp_specMap_C])

/-- The morphism of schemes underlying `adicCompletionObjToAffineLine V I c` is
`Spec Â ⟶ Spec A[X]` given by evaluation at `c`. -/
theorem toScheme_map_adicCompletionObjToAffineLine
    (c : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (BigFppfOver.toScheme B S hS).map (adicCompletionObjToAffineLine V I c) =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) c)) := rfl

/-- Composed with a morphism `g` into `Spec Â`, the functions `c` and `0` agree exactly when they
agree on the underlying morphism of schemes. -/
theorem comp_adicCompletionObjToAffineLine_eq_iff {T : BigFppfOver B S hS}
    (g : T ⟶ adicCompletionObj B S hS V I)
    (c : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    g ≫ adicCompletionObjToAffineLine V I c = g ≫ adicCompletionObjToAffineLine V I 0 ↔
      (BigFppfOver.toScheme B S hS).map g ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) c)) =
      (BigFppfOver.toScheme B S hS).map g ≫ Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) 0)) := by
  refine ⟨fun h => ?_, fun h => (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  · have := congrArg (BigFppfOver.toScheme B S hS).map h
    rwa [Functor.map_comp, Functor.map_comp] at this
  · rwa [Functor.map_comp, Functor.map_comp]

end AffineLine


/-! ### Torsion of the formal functions vanishing on the equalizer -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ContractionLimitEqualizerTorsion :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ContractionLimitEqualizerTorsion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Torsion

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (points B S hS (yoneda.obj V))}
  (hTI : ∀ x, x ∈ Z ↔ pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  {W : FormalSpace.FppfSheaf B S hS} (x₁ x₂ : completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
  {J : ℕ → Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  (hJ : ∀ n (T : BigFppfOver B S hS) (t : T ⟶ V)
    (ht : HasImageIn B S hS (yoneda.obj V) Z T t),
      I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
      (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
          x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
        J n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom))
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (p : Y ⟶ yoneda.obj V) (hp : IsProper B S hS p)
  (hYx : completionSheafMap B S hS p Z ≫ x₁ = completionSheafMap B S hS p Z ≫ x₂)

include hTI hJ hY hp hYx in
/-- **A formal function vanishing on the equalizer vanishes on `Y ×_V Spec Â`**, for `Y ⟶ V`
proper with `Y_{/Z} ⟶ V_{/Z}` factoring through the equalizer: the two morphisms
`Y ×_V Spec Â ⟶ Spec A[X]` given by `x` and by `0` agree. They agree on the completion along the
inverse image of `Z` (`appTop_eq_zero_of_forall_evalₐ_mem` on an affine cover of each section), so
they agree by `AlgebraicGeometry.Space.eq_of_completion_eq_of_closed_meets`, the inverse image of
`Z` meeting every nonempty closed subset since `Y ×_V Spec Â ⟶ Spec Â` is proper and `IÂ` lies
in the Jacobson radical. -/
theorem pullback_fst_comp_adicCompletionObjToAffineLine_eq
    {x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hx : ∀ m, AdicCompletion.evalₐ I m x ∈ (J m).map (Ideal.Quotient.mk (I ^ m))) :
    pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p ≫
        yoneda.map (adicCompletionObjToAffineLine V I x) =
      pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p ≫
        yoneda.map (adicCompletionObjToAffineLine V I 0) := by
  have hXh : IsAlgebraicSpace B S hS (yoneda.obj (adicCompletionObj B S hS V I)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hŶ : IsAlgebraicSpace B S hS
      (pullback (yoneda.map (adicCompletionObjHom B S hS V I)) p) :=
    isAlgebraicSpace_pullback B S hS _ p hXh hY hV
  have hpr : IsProper B S hS (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p) :=
    isProper_pullback_fst B S hS hY hV hXh p _ hp
  -- `Y` is locally Noetherian
  have hXhnoeth : HasEtaleLocalProperty B S hS (yoneda.obj (adicCompletionObj B S hS V I))
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_of_representable B S hS _ (fun V : Scheme.{u} => IsLocallyNoetherian V)
      (adicCompletionObj B S hS V I) (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian
        (Spec (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))))
  have hYnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hŶ hXh _
    (IsProper.isFiniteType B S hS hpr).1 hXhnoeth
  -- `Z` is closed
  have hTclosed : IsClosed Z := by
    rw [isClosed_pointTopology_yoneda_iff_isClosed_image]
    convert Scheme.zeroLocus_isClosed ((BigFppfOver.toScheme B S hS).obj V)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) using 1
    ext y
    obtain ⟨x, rfl⟩ := surjective_pointsToScheme B S hS V y
    rw [(injective_pointsToScheme B S hS V).mem_set_image, hTI]
  -- the closed subset `T_Y` of `|Y|`
  have hTYclosed : IsClosed (pointsMap B S hS _
      (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) p) ⁻¹'
        (pointsMap B S hS Y p ⁻¹' Z)) :=
    (hTclosed.preimage (continuous_pointsMap B S hS p)).preimage (continuous_pointsMap B S hS _)
  -- `T_Y` meets every nonempty closed subset of `|Y|`
  have hclosed : IsClosedMap (pointsMap B S hS _
      (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p)) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS _
      ((IsProper.universallyClosed B S hS hpr) _ hXh (𝟙 _))
  have hmeets : ∀ C : Set (points B S hS (pullback (yoneda.map
      (adicCompletionObjHom B S hS V I)) p)), IsClosed C → C.Nonempty →
      (C ∩ pointsMap B S hS _ (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) p) ⁻¹'
        (pointsMap B S hS Y p ⁻¹' Z)).Nonempty := by
    intro C hC hCne
    have hK := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS
      (adicCompletionObj B S hS V I) _).mp (hclosed C hC)
    have hK' : IsClosed (pointsToScheme B S hS (adicCompletionObj B S hS V I) ''
        (pointsMap B S hS _ (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p) ''
          C) : Set (PrimeSpectrum
            (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) := hK
    obtain ⟨c₀, hc₀⟩ := hCne
    obtain ⟨M, hMK, hMcl⟩ := hK'.exists_closed_singleton
      ⟨_, ⟨_, ⟨c₀, hc₀, rfl⟩, rfl⟩⟩
    have hMmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal M).mp hMcl
    obtain ⟨_, ⟨c, hc, rfl⟩, hcM⟩ := hMK
    refine ⟨c, hc, ?_⟩
    have hIM : I ≤ Ideal.comap (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) M.asIdeal := by
      have := AdicCompletion.isAdicComplete_self I (Ideal.fg_of_isNoetherianRing I)
      exact Ideal.map_le_iff_le_comap.mp
        ((IsAdicComplete.le_jacobson_bot _).trans (sInf_le ⟨bot_le, hMmax⟩))
    have hmem : (BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I) M ∈
        ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
          (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :=
      (Set.ext_iff.mp (Scheme.isoSpec_inv_preimage_zeroLocus _
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) M)).mpr hIM
    show pointsMap B S hS Y p (pointsMap B S hS _ (pullback.snd _ p) c) ∈ Z
    rw [← Function.comp_apply (f := pointsMap B S hS Y p), ← pointsMap_comp,
      ← pullback.condition, pointsMap_comp, Function.comp_apply, hTI,
      pointsToScheme_pointsMap_yoneda, hcM]
    exact hmem
  -- the two composites agree on the completion along the inverse image of `Z`
  have hcompletion :
      (completionSubfunctor B S hS _ (pointsMap B S hS _
        (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) p) ⁻¹'
          (pointsMap B S hS Y p ⁻¹' Z))).ι ≫
        Functor.whiskerRight (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p ≫
          yoneda.map (adicCompletionObjToAffineLine V I x)) uliftFunctor.{u + 1} =
      (completionSubfunctor B S hS _ (pointsMap B S hS _
        (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) p) ⁻¹'
          (pointsMap B S hS Y p ⁻¹' Z))).ι ≫
        Functor.whiskerRight (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p ≫
          yoneda.map (adicCompletionObjToAffineLine V I 0)) uliftFunctor.{u + 1} := by
    ext Zo s
    obtain ⟨Zo⟩ := Zo
    obtain ⟨⟨y⟩, hy⟩ := s
    show ULift.up ((pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p).app (op Zo) y ≫
        adicCompletionObjToAffineLine V I x) =
      ULift.up ((pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p).app (op Zo) y ≫
        adicCompletionObjToAffineLine V I 0)
    congr 1
    let g := (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) p).app (op Zo) y
    let w := (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) p).app (op Zo) y
    have hw : HasImageIn B S hS Y (pointsMap B S hS Y p ⁻¹' Z) Zo w :=
      (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS _ _ Zo y).mp hy
    have hcond : g ≫ adicCompletionObjHom B S hS V I = p.app (op Zo) w :=
      congrArg (fun α => α.app (op Zo) y)
        (pullback.condition (f := yoneda.map (adicCompletionObjHom B S hS V I)) (g := p))
    rw [comp_adicCompletionObjToAffineLine_eq_iff]
    refine Scheme.Cover.hom_ext ((BigFppfOver.toScheme B S hS).obj Zo).affineCover _ _
      fun i => ?_
    let Ui : BigFppfOver B S hS := BigFppfOver.mk B S hS
      (B.contains_of_mono (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i) Zo.left.2)
      (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i ≫ B.inclusion.map Zo.hom)
    let ui : Ui ⟶ Zo :=
      Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i))
        (by apply ObjectProperty.hom_ext; rfl)
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Ui) :=
      inferInstanceAs (IsAffine (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.X i))
    suffices hzero : (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i ≫
        (BigFppfOver.toScheme B S hS).map g).appTop ((Scheme.ΓSpecIso
          (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv x) = 0 by
      have key := (Scheme.comp_specMap_eval₂_eq_iff
        (R := .of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
        (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i ≫
          (BigFppfOver.toScheme B S hS).map g) x).mpr hzero
      exact (Category.assoc _ _ _).symm.trans (key.trans (Category.assoc _ _ _))
    have e : ((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f i ≫
        (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map (ui ≫ g) := by
      rw [Functor.map_comp]
      rfl
    rw [e]
    let w' := Y.map ui.op w
    have hw' : HasImageIn B S hS Y (pointsMap B S hS Y p ⁻¹' Z) Ui w' :=
      (completionSubfunctor B S hS Y _).map ui.op hw
    have hpw' : HasImageIn B S hS (yoneda.obj V) Z Ui (p.app (op Ui) w') :=
      (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS p Z Ui w').mp hw'
    have hgw : (ui ≫ g) ≫ adicCompletionObjHom B S hS V I = p.app (op Ui) w' := by
      rw [Category.assoc, hcond]
      exact (NatTrans.naturality_apply p ui.op w).symm
    have hg' : HasImageIn B S hS (yoneda.obj V) Z Ui
        ((ui ≫ g) ≫ adicCompletionObjHom B S hS V I) := hgw ▸ hpw'
    refine appTop_eq_zero_of_forall_evalₐ_mem hTI x₁ x₂ hJ hx (ui ≫ g) hg' ?_
    have h1 : x₁.hom.app (op Ui) ((completionSheafMap B S hS p Z).hom.app (op Ui)
          (FormalSpace.presheafSection B S hS w' hw')) =
        x₂.hom.app (op Ui) ((completionSheafMap B S hS p Z).hom.app (op Ui)
          (FormalSpace.presheafSection B S hS w' hw')) :=
      congrArg (fun φ => φ.hom.app (op Ui) (FormalSpace.presheafSection B S hS w' hw')) hYx
    rw [FormalSpace.completionSheafMap_presheafSection B S hS p Z w' hw' hpw'] at h1
    have hc : FormalSpace.presheafSection B S hS _ hg' =
        FormalSpace.presheafSection B S hS (p.app (op Ui) w') hpw' := by
      have : ∀ {a b : (yoneda.obj V).obj (op Ui)} (hab : a = b)
          (ha : HasImageIn B S hS (yoneda.obj V) Z Ui a)
          (hb : HasImageIn B S hS (yoneda.obj V) Z Ui b),
          FormalSpace.presheafSection B S hS a ha = FormalSpace.presheafSection B S hS b hb := by
        intro a b hab ha hb
        subst hab
        rfl
      exact this hgw hg' hpw'
    rw [hc]
    exact h1
  exact eq_of_completion_eq_of_closed_meets B S hS hŶ (isAlgebraicSpace_yoneda B S hS _) hYnoeth
    hTYclosed hmeets _ _ hcompletion

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
include hTI in
/-- A morphism into `V` avoiding `V(I)` pointwise is a section of `V ∖ Z`. -/
theorem mem_openSubspaceOfPoints_compl_of_forall_not_mem {U : BigFppfOver B S hS} (t : U ⟶ V)
    (h : ∀ z, (BigFppfOver.toScheme B S hS).map t z ∉
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    t ∈ (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj (op U) := by
  rw [mem_openSubspaceOfPoints_iff]
  rintro _ ⟨w, rfl⟩
  obtain ⟨z, rfl⟩ := (schemePointsHomeomorph B S hS U).symm.surjective w
  have hy : yonedaEquiv.symm t = yoneda.map t := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  show _ ∉ Z
  rw [hy, schemePointsHomeomorph_symm_naturality]
  intro hz
  rw [hTI, ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply] at hz
  exact h z hz

include hTI hJ hY hp hYx in
/-- **Formal functions vanishing on the equalizer are `I`-power torsion** (the step of the proof of
Stacks 0GI5 replacing Lemma 0GHE): if `Y ⟶ V` is proper, an isomorphism over `V ∖ Z` (in the
weak form that `V ∖ Z ⟶ V` lifts to `Y`), and `Y_{/Z} ⟶ V_{/Z}` factors through the equalizer
of `x₁, x₂`, then every `x ∈ Â` all of whose components lie in the images of the ideals `J m`
cutting out the equalizer is killed by a power of `I`. For `a ∈ I` the basic open `D(a)` of
`Spec Â` maps into `V ∖ Z`, hence lifts to `Y ×_V Spec Â`, on which `x` vanishes
(`pullback_fst_comp_adicCompletionObjToAffineLine_eq`), so `x` vanishes in `Â_a`. -/
theorem exists_pow_smul_eq_zero_of_isProper
    (j : (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ Y)
    (hj : j ≫ p = (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι)
    {x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hx : ∀ m, AdicCompletion.evalₐ I m x ∈ (J m).map (Ideal.Quotient.mk (I ^ m))) :
    ∃ N, ∀ a ∈ I ^ N, a • x = 0 := by
  have key := pullback_fst_comp_adicCompletionObjToAffineLine_eq hTI x₁ x₂ hJ hY p hp hYx hx
  -- every element of `I` kills `x` after raising to a power
  have hpow : ∀ a ∈ I, ∃ k : ℕ, a ^ k • x = 0 := by
    intro a ha
    let f := algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a
    let Ra := Localization.Away f
    have hRa : B.Contains (Spec (.of Ra)) :=
      Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        (Submonoid.powers f) Ra
        (B.contains_spec_adicCompletion (contains_spec_globalSections B S hS V) I)
    let Da : BigFppfOver B S hS := BigFppfOver.mk B S hS hRa
      (Spec.map (CommRingCat.ofHom (algebraMap _ Ra)) ≫
        B.inclusion.map (adicCompletionObj B S hS V I).hom)
    let ιa : Da ⟶ adicCompletionObj B S hS V I :=
      Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap _ Ra))))
        (by apply ObjectProperty.hom_ext; rfl)
    let κ := adicCompletionObjHom B S hS V I
    -- the ring map of `D(a) ⟶ Spec Â` on global sections
    have hιa : ∀ c, ((BigFppfOver.toScheme B S hS).map ιa).appTop
        ((Scheme.ΓSpecIso (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv
          c) = (Scheme.ΓSpecIso (.of Ra)).inv (algebraMap _ Ra c) := fun c =>
      Scheme.appTop_specMap_ΓSpecIso_inv_apply (CommRingCat.ofHom (algebraMap _ Ra)) c
    have hκ : ∀ b, ((BigFppfOver.toScheme B S hS).map κ).appTop b =
        (Scheme.ΓSpecIso (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).inv
          (algebraMap _ _ b) := fun b =>
      Scheme.appTop_specMap_comp_isoSpec_inv_apply _ _ b
    -- `D(a)` maps into `V ∖ Z`
    have hunit : IsUnit (((BigFppfOver.toScheme B S hS).map (ιa ≫ κ)).appTop a) := by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hκ, hιa]
      exact (IsLocalization.Away.algebraMap_isUnit f).map _
    have hDa : ∀ (U : BigFppfOver B S hS) (t : U ⟶ Da),
        t ≫ ιa ≫ κ ∈ (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj (op U) := by
      intro U t
      refine mem_openSubspaceOfPoints_compl_of_forall_not_mem hTI _ fun z hz => ?_
      rw [Functor.map_comp, Scheme.Hom.comp_apply] at hz
      have hz' := (Set.ext_iff.mp (Scheme.preimage_zeroLocus
        ((BigFppfOver.toScheme B S hS).map (ιa ≫ κ))
          (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
        ((BigFppfOver.toScheme B S hS).map t z)).mp hz
      rw [Scheme.mem_zeroLocus_iff] at hz'
      have hb : ((BigFppfOver.toScheme B S hS).obj Da).basicOpen
          (((BigFppfOver.toScheme B S hS).map (ιa ≫ κ)).app ⊤ a) = ⊤ :=
        Scheme.basicOpen_of_isUnit _ hunit
      exact hz' _ ⟨a, ha, rfl⟩ (by rw [hb]; trivial)
    let ℓ : yoneda.obj Da ⟶ (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor :=
      Subfunctor.lift (yoneda.map (ιa ≫ κ)) (by
        rintro ⟨U⟩ _ ⟨t, rfl⟩
        exact hDa U t)
    let sa : yoneda.obj Da ⟶ pullback (yoneda.map κ) p :=
      pullback.lift (yoneda.map ιa) (ℓ ≫ j) (by
        rw [Category.assoc, hj, Subfunctor.lift_ι, Functor.map_comp])
    have h1 := congrArg (sa ≫ ·) key
    rw [← Category.assoc, ← Category.assoc, pullback.lift_fst, ← Functor.map_comp,
      ← Functor.map_comp] at h1
    have h2 := (comp_adicCompletionObjToAffineLine_eq_iff V I ιa x).mp (yoneda.map_injective h1)
    have h2' : Spec.map (CommRingCat.ofHom (algebraMap _ Ra)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) x)) =
      Spec.map (CommRingCat.ofHom (algebraMap _ Ra)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) 0)) := h2
    rw [← Spec.map_comp, ← Spec.map_comp] at h2'
    have h4 : algebraMap _ Ra x = 0 := by
      have := congrArg (fun φ => φ.hom Polynomial.X) (Spec.map_injective h2')
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_zero] at this
      exact this
    obtain ⟨⟨m, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Ra x).mp h4
    exact ⟨k, by rw [Algebra.smul_def, map_pow]; exact hk⟩
  -- a finitely generated ideal in the radical of the annihilator has a power in it
  let K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    LinearMap.ker (LinearMap.toSpanSingleton _ _ x)
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := I) (J := K)
    (fun a ha => by
      obtain ⟨k, hk⟩ := hpow a ha
      exact ⟨k, hk⟩) (Ideal.fg_of_isNoetherianRing I)
  exact ⟨N, fun _ ha => hN ha⟩

end Torsion

/-! ### The equalizer is cut out by finitely many torsion functions -/

section Assembly

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (points B S hS (yoneda.obj V))}

/-- **The equalizer of two formal morphisms out of `V_{/Z}`, when a closed immersion through
which a proper modification factors, is cut out by finitely many `I`-power torsion functions.**
Let `V` be affine with Noetherian ring `A`, `Z = V(I)`, and `x₁, x₂ : V_{/Z} ⟶ W` with closed
equalizer. Let `p : Y ⟶ V` be proper, with a lift `j` of `V ∖ Z ⟶ V`, such that `x₁` and `x₂`
agree on `Y_{/Z}`. Then there is a finite set `s ⊆ A` of elements each killed by a power of `I`
such that a morphism `t : T ⟶ V` killing a power `Iⁿ` equalizes `x₁` and `x₂` exactly when it
kills `s`. This is the algebraic core of the injectivity half of Stacks 0GI5: its source quotes
Lemma 0GHE here, which needs properness of the equalizer `E'`, and this lemma replaces it by the
properness of a witness. -/
theorem exists_finset_torsion_iff_of_isProper
    (hTI : ∀ x, x ∈ Z ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    {W : FormalSpace.FppfSheaf B S hS} (x₁ x₂ : completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (hE : FormalSpace.IsClosedImmersion B S hS (equalizer.ι x₁ x₂))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj V) (hp : IsProper B S hS p)
    (j : (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ Y)
    (hj : j ≫ p = (openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι)
    (hYx : completionSheafMap B S hS p Z ≫ x₁ = completionSheafMap B S hS p Z ≫ x₂) :
    ∃ s : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      (∀ a ∈ s, ∃ N, ∀ b ∈ I ^ N, b * a = 0) ∧
      ∀ (n : ℕ) (T : BigFppfOver B S hS) (t : T ⟶ V)
        (ht : HasImageIn B S hS (yoneda.obj V) Z T t),
        I ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
        (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
            x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
          ∀ a ∈ s, ((BigFppfOver.toScheme B S hS).map t).appTop a = 0) := by
  classical
  obtain ⟨J, hJ, hJsup⟩ := exists_ideals_of_isClosedImmersion_equalizer hTI x₁ x₂ hE
  let Â := AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  -- the ideal of formal functions vanishing on the equalizer
  let Jh : Ideal Â := ⨅ m, Ideal.comap (AdicCompletion.evalₐ I m).toRingHom
    ((J m).map (Ideal.Quotient.mk (I ^ m)))
  have hmem : ∀ y : Â, y ∈ Jh ↔
      ∀ m, AdicCompletion.evalₐ I m y ∈ (J m).map (Ideal.Quotient.mk (I ^ m)) := by
    intro y
    simp only [Jh, Ideal.mem_iInf, Ideal.mem_comap]
    rfl
  obtain ⟨gens, hgens⟩ := (inferInstance : IsNoetherianRing Â).noetherian Jh
  have hgJ : ∀ g : gens, (g : Â) ∈ Jh := fun g => hgens ▸ Submodule.subset_span g.2
  -- each generator comes from a torsion element of `A`
  have htors : ∀ g : gens, ∃ a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      (∃ N, ∀ b ∈ I ^ N, b * a = 0) ∧ algebraMap _ Â a = g := by
    intro g
    obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_isProper hTI x₁ x₂ (fun n => (hJ n).2) hY p hp hYx
      j hj ((hmem _).mp (hgJ g))
    obtain ⟨a, ha, hga⟩ := AdicCompletion.exists_algebraMap_eq_of_pow_smul_eq_zero I hN
    exact ⟨a, ⟨N, ha⟩, hga⟩
  choose a ha hga using htors
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hx
    exact ha g
  intro n T t ht htI
  rw [(hJ n).2 T t ht htI]
  constructor
  · intro hle x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hx
    apply hle
    have h1 := (hmem _).mp (hgJ g) n
    rw [← hga g, AdicCompletion.evalₐ_algebraMap_eq_mk] at h1
    exact (Ideal.mem_quotient_iff_mem (hJ n).1).mp h1
  · intro hs b hb
    obtain ⟨y, hy, hyb⟩ := AdicCompletion.exists_forall_evalₐ_mem_of_eq_sup_pow hJsup hb
    have hyJ : y ∈ Jh := (hmem y).mpr hy
    -- `y` is a combination of the generators, so `b` lies in `span s + Iⁿ`
    have hspan : y ∈ Ideal.span ((algebraMap _ Â) ''
        (↑(Finset.univ.image a) : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) := by
      rw [← hgens] at hyJ
      refine Submodule.span_le.mpr (fun g hg => ?_) hyJ
      exact Submodule.subset_span ⟨a ⟨g, hg⟩, by simp, hga ⟨g, hg⟩⟩
    have hmap := Ideal.mem_map_of_mem (AdicCompletion.evalₐ I n).toRingHom hspan
    rw [Ideal.map_span, ← Set.image_comp] at hmap
    have hcomp : (AdicCompletion.evalₐ I n).toRingHom ∘ (algebraMap _ Â) =
        Ideal.Quotient.mk (I ^ n) :=
      funext (AdicCompletion.evalₐ_algebraMap_eq_mk n)
    rw [hcomp, ← Ideal.map_span] at hmap
    change AdicCompletion.evalₐ I n y ∈ _ at hmap
    rw [hyb, Ideal.mem_quotient_iff_mem_sup] at hmap
    exact sup_le (Submodule.span_le.mpr fun x hx => hs x hx) htI hmap

end Assembly

end AlgebraicGeometry.Space

end
