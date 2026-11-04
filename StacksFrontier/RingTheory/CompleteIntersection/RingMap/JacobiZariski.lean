module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public meta import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Koszul.Descent
public import StacksFrontier.RingTheory.NaiveCotangent.Colimit
public import StacksFrontier.RingTheory.Regular.Ideal
import StacksFrontier.RingTheory.Flat.IdealMapLiftBaseChange

@[expose] public section

/-!
# The cotangent complex of a local complete intersection

Let `A → B → C` be ring maps, let `α : A[x_s] → B` and `β : B[y_t] → C` be presentations, and
let `β.comp α : A[x_s, y_t] → C` be the induced presentation of `C` over `A`. Write `I` for the
kernel of `α` and `K` for the kernel of `β.comp α`. There is a canonical map
`C ⊗_B (I / I²) → K / K²` between the conormal modules of `α` and of `β.comp α`. This file proves
that this map is injective in two situations: when `B → C` is a local complete intersection, and
when `B → C` is a filtered colimit of local complete intersection homomorphisms.

Together with the canonical commutative diagram of conormal modules and Kähler differentials,
injectivity puts a zero at the left of both its exact rows. Consequently the Jacobi--Zariski
sequence extends to the exact sequence
`0 → H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) →
C ⊗_B Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`.

## Main results

* `RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection` proves injectivity of
  the canonical conormal map when `B → C` is a local complete intersection.
* `RingHom.cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection`
  proves injectivity of the canonical conormal map when `B → C` is a filtered colimit of local
  complete intersection homomorphisms.

## Implementation notes

Presentations are represented by `Algebra.Generators`. The source and target of the displayed
map are respectively `C ⊗_B (I / I²)` and `K / K²`. The remaining parts of the canonical diagram
are `Algebra.Generators.Cotangent.exact`,
`Algebra.Generators.CotangentSpace.map_toComp_injective`, and the naturality lemmas for the
cotangent-complex differentials. Exactness of the resulting Jacobi--Zariski sequence is supplied
at its presentation-dependent left node by
`Algebra.Generators.Cotangent.map_ker_baseChange_cotangentComplex` (Stacks tag 00S2), and at its
four right nodes by Mathlib's Jacobi--Zariski exactness lemmas. Thus the injectivity proved here
is precisely the sole additional assertion in the source's diagram and seven-term sequence.

Both proofs reduce injectivity to the ideal-theoretic identity `I' ∩ K² = I' K`, where `I'` is
the image of `I` in `A[x_s, y_t]`: this is `cotangentMap_liftBaseChange_injective_of_flat`, which
compares the conormal base change along a flat presentation map with the conormal module of the
bigger presentation. The identity itself comes from
`Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal` (Stacks tag 07CX) together with faithfully
flat descent of regularity (Stacks tag 068N).

For the local complete intersection case, the first presentation may have an arbitrary variable
type; only the second presentation is finite, as required by the hypothesis.

For the colimit case, a system of ring maps is represented by `RingMapSystemUnbundled` over a
nonempty directed preorder, as in the source's cited Lemma 07BQ. Ring equivalences from its two
`Ring.DirectLimit` rings to `B` and `C`, together with a commuting square, identify its induced
map with `B → C`. This expresses the source's colimit on elements even when the index universe is
independent of the ring universes. An arbitrary categorical colimit in `CommRingCat` would not do
so without a smallness condition. Filtered diagrams can be reindexed by directed preorders. The
universes of `A`, `B`, `C`, both variable types, the index type, and the stage rings are
independent; the system bundle uses a common universe for its source and target rings, and
systems whose two families start in different universes can be lifted to their maximum. Unlike
the local complete intersection case, the presentation of `C` over `B` may have an arbitrary
variable type, since a filtered colimit need not be of finite type. The reduction to the stages
is carried out by pulling the system back along the presentation `A[x_s] → B`, which produces a
system of ring maps whose colimit source is `A[x_s]` itself.

## References

* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4)
* [Stacks Project, Tag 07D5](https://stacks.math.columbia.edu/tag/07D5)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2)
* [Stacks Project, Tag 07BQ](https://stacks.math.columbia.edu/tag/07BQ)
-/

namespace RingHom

universe w w' u₁ u₂ u₃ u₄ u₅

open Algebra TensorProduct MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

/-! ### Conormal modules along a flat map of presentations -/

private theorem cotangentMk_liftBaseChange_injective
    {D C : Type*} [CommRing D] [CommRing C] [Algebra D C]
    (E : Extension D C) (I : Ideal E.Ring) (hIJ : I ≤ E.ker)
    (hsq : I ⊓ E.ker ^ 2 = I * E.ker) :
    Function.Injective
      ((Extension.Cotangent.mk ∘ₗ Submodule.inclusion hIJ).liftBaseChange C) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, rfl⟩ := TensorProduct.mk_surjective E.Ring I C E.algebraMap_surjective x
  change (Extension.Cotangent.mk ∘ₗ Submodule.inclusion hIJ).liftBaseChange C
    (1 ⊗ₜ[E.Ring] i) = 0 at hx
  have hiSq : (i : E.Ring) ∈ E.ker ^ 2 := by
    simpa only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, one_smul,
      Extension.Cotangent.mk_eq_zero_iff, Submodule.inclusion_apply] using hx
  have hiIJ : (i : E.Ring) ∈ I * E.ker := by
    rw [← hsq]
    exact ⟨i.2, hiSq⟩
  rw [Ideal.mul_comm] at hiIJ
  refine Submodule.smul_induction_on' (p := fun z (hz : z ∈ E.ker * I) ↦
    (1 : C) ⊗ₜ[E.Ring] (⟨z, Ideal.mul_le_right hz⟩ : I) = 0) (hx := hiIJ) ?_ ?_
  · intro a ha b hb
    trans (a • (1 : C)) ⊗ₜ[E.Ring] (⟨b, hb⟩ : I)
    · rw [smul_tmul]; rfl
    · have ha0 : algebraMap E.Ring C a = 0 := ha
      simp [Algebra.smul_def, ha0]
  · intro a ha b hb ha' hb'
    convert congrArg₂ (· + ·) ha' hb' using 1
    · rw [← tmul_add]; rfl
    · simp

private theorem cotangentMap_liftBaseChange_injective_of_flat
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Extension R S) (Q : Extension R T) (f : P.Hom Q)
    [Algebra P.Ring Q.Ring] [Module.Flat P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (hsq : P.ker.map f.toRingHom ⊓ Q.ker ^ 2 = P.ker.map f.toRingHom * Q.ker) :
    Function.Injective ((Extension.Cotangent.map f).liftBaseChange T) := by
  let := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r ↦ halg ▸ (f.algebraMap_toRingHom r).symm
  let I := P.ker.map (algebraMap P.Ring Q.Ring)
  have hIQ : I ≤ Q.ker := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show algebraMap Q.Ring T (algebraMap P.Ring Q.Ring x) = 0
    rw [halg, f.algebraMap_toRingHom]
    rw [show algebraMap P.Ring S x = 0 from hx, map_zero]
  let eI := LinearEquiv.ofBijective _ (idealMap_liftBaseChange_bijective (S := Q.Ring) P.ker)
  let eP := (AlgebraTensorModule.cancelBaseChange P.Ring S T T P.ker).symm ≪≫ₗ
    LinearEquiv.baseChange S T _ _ P.cotangentEquiv
  let eQ := (AlgebraTensorModule.cancelBaseChange P.Ring Q.Ring T T P.ker).symm ≪≫ₗ
    LinearEquiv.baseChange Q.Ring T _ _ eI
  let g := (Extension.Cotangent.mk ∘ₗ Submodule.inclusion hIQ).liftBaseChange T
  have hg : Function.Injective g := cotangentMk_liftBaseChange_injective Q I hIQ
    (by simpa only [I, halg] using hsq)
  have hcomm : ((Extension.Cotangent.map f).liftBaseChange T) ∘ₗ eP.toLinearMap =
      g ∘ₗ eQ.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul t x =>
      dsimp only [I] at *
      simp only [eP, eQ, eI, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearEquiv.baseChange_tmul, Extension.contangentEquiv_tmul,
        one_smul, LinearMap.liftBaseChange_tmul, Extension.Cotangent.map_mk,
        LinearEquiv.ofBijective_apply]
      show t • Extension.Cotangent.mk (P := Q) _ = t • Extension.Cotangent.mk (P := Q) _
      congr 2
      apply Subtype.ext
      simp [Algebra.idealMap_apply_coe, halg, Extension.Hom.toAlgHom_apply]
  intro x y hxy
  obtain ⟨x, rfl⟩ := eP.surjective x
  obtain ⟨y, rfl⟩ := eP.surjective y
  apply congrArg eP
  apply eQ.injective
  apply hg
  show (g ∘ₗ eQ.toLinearMap) x = (g ∘ₗ eQ.toLinearMap) y
  rw [← hcomm]
  exact hxy

private theorem flat_rename_inr {R : Type*} [CommRing R] (ι κ : Type*) :
    let := (MvPolynomial.rename (R := R) (Sum.inr : κ → ι ⊕ κ)).toAlgebra
    Module.Flat (MvPolynomial κ R) (MvPolynomial (ι ⊕ κ) R) := by
  let := (MvPolynomial.rename (R := R) (Sum.inr : κ → ι ⊕ κ)).toAlgebra
  let e : MvPolynomial (ι ⊕ κ) R ≃ₐ[MvPolynomial κ R] MvPolynomial ι (MvPolynomial κ R) :=
    { __ := (MvPolynomial.sumAlgEquiv R ι κ).toRingEquiv
      commutes' := fun x ↦ congrArg (fun g : MvPolynomial κ R →ₐ[R]
          MvPolynomial ι (MvPolynomial κ R) ↦ g x)
        (MvPolynomial.sumAlgEquiv_comp_rename_inr R ι κ) }
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

private theorem inf_sq_eq_mul_of_surjective
    {D E F : Type*} [CommRing D] [CommRing E] [CommRing F]
    (q : D →+* E) (hq : Function.Surjective q) (p : E →+* F)
    (hp : Ideal.IsH1Regular (RingHom.ker p)) :
    RingHom.ker q ⊓ RingHom.ker (p.comp q) ^ 2 =
      RingHom.ker q * RingHom.ker (p.comp q) := by
  have hle : RingHom.ker q ≤ RingHom.ker (p.comp q) := by
    intro x hx
    show p (q x) = 0
    rw [show q x = 0 from hx, map_zero]
  apply Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal _ _ hle
  let e := q.quotientKerEquivOfSurjective hq
  apply (Koszul.regular_ideals_of_faithfullyFlat e.toRingHom
    (RingHom.FaithfullyFlat.of_bijective e.bijective) _).2.1
  have he : e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker q)) = q := by
    ext x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hq x
  rw [Ideal.map_map, he]
  have hk : Ideal.map q (RingHom.ker (p.comp q)) = RingHom.ker p := by
    show Ideal.map q ((RingHom.ker p).comap q) = _
    exact Ideal.map_comap_of_surjective q hq _
  rwa [hk]

/-- The canonical conormal map along `β.toComp α` is injective once `I ∩ K² = I K`. -/
private theorem cotangentMap_toComp_injective_of_inf_sq
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {C : Type*} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {S T : Type*} (α : Generators A B S) (β : Generators B C T)
    (hsq : α.ker.map (β.toComp α).toAlgHom ⊓ (β.comp α).ker ^ 2 =
      α.ker.map (β.toComp α).toAlgHom * (β.comp α).ker) :
    Function.Injective
      ((Extension.Cotangent.map (β.toComp α).toExtensionHom).liftBaseChange C) := by
  let : Algebra α.toExtension.Ring (β.comp α).toExtension.Ring :=
    (β.toComp α).toExtensionHom.toRingHom.toAlgebra
  have : Module.Flat α.toExtension.Ring (β.comp α).toExtension.Ring := by
    show @Module.Flat _ _ _ _ (β.toComp α).toAlgHom.toAlgebra.toModule
    rw [Generators.toComp_toAlgHom]
    exact flat_rename_inr T S
  exact cotangentMap_liftBaseChange_injective_of_flat α.toExtension (β.comp α).toExtension
    (β.toComp α).toExtensionHom rfl hsq

/-! ## Tag 07D4

Injectivity of the canonical conormal map for a local complete intersection.
-/

/-- Let `A → B → C` be ring maps, let `α : A[x_s] → B` and
`β : B[y₁, ..., yₘ] → C` be presentations, and write `K` for the kernel of the induced
presentation `β.comp α : A[x_s, y_t] → C`. If `B → C` is a local complete intersection, then
the canonical map `C ⊗_B (I / I²) → K / K²` is injective. Together with the canonical exact
conormal/differential diagram and the Jacobi--Zariski exactness lemmas, this gives the exact
sequence
`0 → H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) →
C ⊗_B Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`. -/
@[stacks 07D4]
public theorem cotangentMap_toComp_injective_of_isLocalCompleteIntersection
    {A : Type u₁} {B : Type u₂} [CommRing A] [CommRing B] [Algebra A B]
    {C : Type u₃} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {S : Type w} {m : ℕ} (α : Generators A B S) (β : Generators B C (Fin m))
    (h : RingHom.IsLocalCompleteIntersection (algebraMap B C)) :
    Function.Injective
      ((Extension.Cotangent.map (β.toComp α).toExtensionHom).liftBaseChange C) := by
  have hβ : Ideal.IsKoszulRegular β.ker := by
    rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
    obtain ⟨_, n, p, hp, hreg⟩ := h
    rw [Generators.ker_eq_ker_aeval_val]
    exact RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial p hp hreg
      (MvPolynomial.aeval β.val) β.aeval_val_surjective
  have hsq : α.ker.map (β.toComp α).toAlgHom ⊓ (β.comp α).ker ^ 2 =
      α.ker.map (β.toComp α).toAlgHom * (β.comp α).ker := by
    rw [Generators.map_toComp_ker]
    have hK : (β.comp α).ker = RingHom.ker ((algebraMap β.Ring C).comp
        (β.ofComp α).toAlgHom.toRingHom) := by
      ext x
      simp [Generators.ker_eq_ker_aeval_val]
      rfl
    rw [hK]
    exact inf_sq_eq_mul_of_surjective (β.ofComp α).toAlgHom.toRingHom
      (Generators.toAlgHom_ofComp_surjective β α) (algebraMap β.Ring C) hβ.isH1Regular
  exact cotangentMap_toComp_injective_of_inf_sq α β hsq

/-! ## Tag 07D5

Injectivity of the canonical conormal map for a filtered colimit of local complete
intersection homomorphisms.
-/

private theorem sub_mem_mul_of_mem_map
    {D E : Type*} [CommRing D] [CommRing E]
    (c : D →+* E) (I : Ideal D) (K : Ideal E) (f : E →+* E)
    (hf : f.comp c = c) (hK : ∀ x, x - f x ∈ K)
    {x : E} (hx : x ∈ I.map c) : x - f x ∈ I.map c * K := by
  change x ∈ Ideal.span (c '' (I : Set D)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have hfa : f (c a) = c a := DFunLike.congr_fun hf a
    simp [hfa]
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hx' hy'
  | smul a x hx hx' =>
    show a * x - f (a * x) ∈ _
    have h₂ : (a - f a) * x ∈ I.map c * K := by
      have hxI : x ∈ I.map c := hx
      simpa only [mul_comm] using (Ideal.mul_mem_mul hxI (hK a))
    have h₃ : f a * (x - f x) ∈ I.map c * K := Ideal.mul_mem_left _ _ hx'
    have he : a * x - f (a * x) = (a - f a) * x + f a * (x - f x) := by
      rw [map_mul]
      ring
    rw [he]
    exact Ideal.add_mem _ h₂ h₃

private theorem polynomial_inf_sq_eq_mul_of_surjective_presentations
    {D S U T : Type*} [CommRing D] [CommRing S]
    (Ibase : Ideal D) (p₀ : MvPolynomial U D →+* S) (a : MvPolynomial T D →+* S)
    (hp₀ : Function.Surjective p₀) (ha : Function.Surjective a)
    (hcomp : a.comp C = p₀.comp C) (hI : Ibase ≤ RingHom.ker (a.comp C))
    (hsq₀ : Ibase.map C ⊓ RingHom.ker p₀ ^ 2 = Ibase.map C * RingHom.ker p₀) :
    Ibase.map C ⊓ RingHom.ker a ^ 2 = Ibase.map C * RingHom.ker a := by
  classical
  let l : MvPolynomial T D →+* MvPolynomial U D :=
    eval₂Hom C (fun t ↦ (hp₀ (a (X t))).choose)
  let r : MvPolynomial U D →+* MvPolynomial T D :=
    eval₂Hom C (fun i ↦ (ha (p₀ (X i))).choose)
  have hlC : l.comp C = C := by ext; simp [l]
  have hrC : r.comp C = C := by ext; simp [r]
  have hl : p₀.comp l = a := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simpa [l] using (DFunLike.congr_fun hcomp x).symm
    · intro t
      simpa [l] using (hp₀ (a (X t))).choose_spec
  have hr : a.comp r = p₀ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simpa [r] using DFunLike.congr_fun hcomp x
    · intro i
      simpa [r] using (ha (p₀ (X i))).choose_spec
  let I : Ideal (MvPolynomial T D) := Ibase.map C
  let I₀ : Ideal (MvPolynomial U D) := Ibase.map C
  let K := RingHom.ker a
  let K₀ := RingHom.ker p₀
  have hsq : I₀ ⊓ K₀ ^ 2 = I₀ * K₀ := hsq₀
  have hlI : I.map l = I₀ := by simp only [I, I₀, Ideal.map_map, hlC]
  have hrI : I₀.map r = I := by simp only [I, I₀, Ideal.map_map, hrC]
  have hlK : K.map l ≤ K₀ := Ideal.map_le_iff_le_comap.2 fun x hx ↦ by
    show p₀ (l x) = 0
    rwa [← RingHom.comp_apply, hl]
  have hrK : K₀.map r ≤ K := Ideal.map_le_iff_le_comap.2 fun x hx ↦ by
    show a (r x) = 0
    rwa [← RingHom.comp_apply, hr]
  show I ⊓ K ^ 2 = I * K
  apply le_antisymm
  · rintro x ⟨hxI, hxK⟩
    have hlxI : l x ∈ I₀ := hlI ▸ Ideal.mem_map_of_mem l hxI
    have hlxK : l x ∈ K₀ ^ 2 := by
      apply pow_le_pow_left' hlK
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem l hxK
    have hlx : l x ∈ I₀ * K₀ := hsq ▸ ⟨hlxI, hlxK⟩
    have hrx : r (l x) ∈ I * K := by
      apply Ideal.mul_mono le_rfl hrK
      rw [← hrI, ← Ideal.map_mul]
      exact Ideal.mem_map_of_mem r hlx
    have hdiff : x - r (l x) ∈ I * K := by
      apply sub_mem_mul_of_mem_map C Ibase K (r.comp l) _ _ hxI
      · rw [RingHom.comp_assoc, hlC, hrC]
      · intro y
        show a (y - r (l y)) = 0
        rw [map_sub, ← RingHom.comp_apply a r, hr,
          ← RingHom.comp_apply p₀ l, hl, sub_self]
    simpa only [sub_add_cancel] using Ideal.add_mem _ hdiff hrx
  · refine le_inf Ideal.mul_le_left ?_
    rw [sq]
    exact Ideal.mul_mono (Ideal.map_le_iff_le_comap.2 fun _ hx ↦ hI hx) le_rfl

private theorem polynomial_inf_sq_eq_mul_of_isLocalCompleteIntersection
    {D R S T : Type*} [CommRing D] [CommRing R] [CommRing S]
    (q : D →+* R) (hq : Function.Surjective q) (g : R →+* S)
    (h : RingHom.IsLocalCompleteIntersection g) (v : T → S)
    (hv : Function.Surjective (eval₂Hom (g.comp q) v)) :
    (RingHom.ker q).map C ⊓ RingHom.ker (eval₂Hom (g.comp q) v) ^ 2 =
      (RingHom.ker q).map C * RingHom.ker (eval₂Hom (g.comp q) v) := by
  let := g.toAlgebra
  obtain ⟨_, n, p, hp, hreg⟩ := h
  let p₀ : MvPolynomial (Fin n) D →+* S := p.toRingHom.comp (map q)
  have hp₀ : Function.Surjective p₀ := hp.comp (map_surjective q hq)
  apply polynomial_inf_sq_eq_mul_of_surjective_presentations (RingHom.ker q) p₀
    (eval₂Hom (g.comp q) v) hp₀ hv
  · ext x
    simp [p₀, ← RingHom.algebraMap_toAlgebra g]
  · intro x hx
    simp [show q x = 0 from hx]
  · simpa only [p₀, ker_map] using
      inf_sq_eq_mul_of_surjective (map (σ := Fin n) q) (map_surjective q hq)
        p.toRingHom hreg.isH1Regular

section PolynomialColimit

variable {J : Type*} [Preorder J] (sys : RingMapSystemUnbundled J)

private abbrev polynomialTransition {i j : J} (hij : i ≤ j) :
    MvPolynomial (sys.S i) (sys.R i) →+* MvPolynomial (sys.S j) (sys.R j) :=
  (rename (sys.fS hij)).toRingHom.comp (map (sys.fR hij))

private abbrev polynomialCocone (i : J) :
    MvPolynomial (sys.S i) (sys.R i) →+* MvPolynomial sys.Sinf sys.Rinf :=
  (rename (sys.toSinf i)).toRingHom.comp (map (sys.toRinf i))

private theorem polynomialCocone_comp {i j : J} (hij : i ≤ j) :
    (polynomialCocone sys j).comp (polynomialTransition sys hij) =
      polynomialCocone sys i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [polynomialCocone, polynomialTransition, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_C, rename_C]
    exact congrArg C (Ring.DirectLimit.of_f hij r)
  · intro s
    simp only [polynomialCocone, polynomialTransition, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_X, rename_X]
    exact congrArg X (Ring.DirectLimit.of_f hij s)

private theorem polynomialCocone_surjective [IsDirectedOrder J] [Nonempty J]
    (x : MvPolynomial sys.Sinf sys.Rinf) :
    ∃ i p, polynomialCocone sys i p = x := by
  obtain ⟨i, _, p, hp⟩ := sys.polyColim_surj (Classical.arbitrary J) x
  exact ⟨i, p, by rwa [sys.homIinf_apply] at hp⟩

private theorem polynomialCocone_ker_sq [IsDirectedOrder J] [Nonempty J]
    (i : J) (p : MvPolynomial (sys.S i) (sys.R i))
    (hp : polynomialCocone sys i p ∈
      RingHom.ker (eval₂Hom sys.gInf _root_.id) ^ 2) :
    ∃ (j : J) (hij : i ≤ j), polynomialTransition sys hij p ∈
      RingHom.ker (eval₂Hom (sys.g j) _root_.id) ^ 2 := by
  have hp' : (sys.homIinf i).toExtensionHom.toAlgHom p ∈ sys.NLinf.ker ^ 2 := by
    rwa [sys.homIinf_apply]
  obtain ⟨j, hij, hj⟩ := sys.kerSq_descends i p hp'
  exact ⟨j, hij, by rwa [sys.transHom_apply] at hj⟩

private theorem polynomialCocone_ker_le (i : J) :
    (RingHom.ker (eval₂Hom (sys.g i) _root_.id)).map (polynomialCocone sys i) ≤
      RingHom.ker (eval₂Hom sys.gInf _root_.id) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have he := sys.aeval_homIinf i x
  rw [sys.homIinf_apply] at he
  change eval₂Hom sys.gInf _root_.id (polynomialCocone sys i x) =
    sys.toSinf i (eval₂Hom (sys.g i) _root_.id x) at he
  show eval₂Hom sys.gInf _root_.id (polynomialCocone sys i x) = 0
  rw [he, show eval₂Hom (sys.g i) _root_.id x = 0 from hx, map_zero]

private def polynomialEquiv {D E : Type*} [CommRing D] [CommRing E]
    (eD : sys.Rinf ≃+* D) (eE : sys.Sinf ≃+* E) :
    MvPolynomial sys.Sinf sys.Rinf ≃+* MvPolynomial E D :=
  (mapEquiv _ eD).trans (renameEquiv D eE.toEquiv).toRingEquiv

private theorem polynomialEquiv_C {D E : Type*} [CommRing D] [CommRing E]
    (eD : sys.Rinf ≃+* D) (eE : sys.Sinf ≃+* E) (r : sys.Rinf) :
    polynomialEquiv sys eD eE (C r) = C (eD r) := by
  simp [polynomialEquiv]

private theorem polynomialEquiv_X {D E : Type*} [CommRing D] [CommRing E]
    (eD : sys.Rinf ≃+* D) (eE : sys.Sinf ≃+* E) (s : sys.Sinf) :
    polynomialEquiv sys eD eE (X s) = X (eE s) := by
  simp [polynomialEquiv]

private theorem polynomialEquiv_eval {D E : Type*} [CommRing D] [CommRing E]
    (eD : sys.Rinf ≃+* D) (eE : sys.Sinf ≃+* E) (g : D →+* E)
    (hcomm : eE.toRingHom.comp sys.gInf = g.comp eD.toRingHom) :
    (eval₂Hom g _root_.id).comp (polynomialEquiv sys eD eE).toRingHom =
      eE.toRingHom.comp (eval₂Hom sys.gInf _root_.id) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, polynomialEquiv_C, eval₂Hom_C]
    exact (DFunLike.congr_fun hcomm r).symm
  · intro s
    simp [polynomialEquiv_X]

private theorem polynomialEquiv_ker {D E : Type*} [CommRing D] [CommRing E]
    (eD : sys.Rinf ≃+* D) (eE : sys.Sinf ≃+* E) (g : D →+* E)
    (hcomm : eE.toRingHom.comp sys.gInf = g.comp eD.toRingHom) :
    (RingHom.ker (eval₂Hom sys.gInf _root_.id)).map (polynomialEquiv sys eD eE).toRingHom =
      RingHom.ker (eval₂Hom g _root_.id) := by
  have he : (RingHom.ker (eval₂Hom g _root_.id)).comap
      (polynomialEquiv sys eD eE).toRingHom =
      RingHom.ker (eval₂Hom sys.gInf _root_.id) := by
    ext x
    show eval₂Hom g _root_.id (polynomialEquiv sys eD eE x) = 0 ↔
      eval₂Hom sys.gInf _root_.id x = 0
    have hc := DFunLike.congr_fun (polynomialEquiv_eval sys eD eE g hcomm) x
    change eval₂Hom g _root_.id (polynomialEquiv sys eD eE x) =
      eE (eval₂Hom sys.gInf _root_.id x) at hc
    rw [hc, map_eq_zero_iff _ eE.injective]
  rw [← he]
  exact Ideal.map_comap_of_surjective (polynomialEquiv sys eD eE).toRingHom
    (polynomialEquiv sys eD eE).surjective _

end PolynomialColimit

section Pullback

universe uD uB uJ u

variable {D : Type uD} {B : Type uB} [CommRing D] [CommRing B]
  {J : Type uJ} [Preorder J] (sys : RingMapSystemUnbundled.{u} J)
  (eB : sys.Rinf ≃+* B) (q : D →+* B)

private abbrev sourcePullback (i : J) : Subring (D × sys.R i) :=
  (q.comp (RingHom.fst D (sys.R i))).eqLocus
    ((eB.toRingHom.comp (sys.toRinf i)).comp (RingHom.snd D (sys.R i)))

private def sourcePullbackMap {i j : J} (hij : i ≤ j) :
    sourcePullback sys eB q i →+* sourcePullback sys eB q j where
  toFun x := ⟨(x.1.1, sys.fR hij x.1.2), by
    change q x.1.1 = eB (sys.toRinf j (sys.fR hij x.1.2))
    rw [show sys.toRinf j (sys.fR hij x.1.2) = sys.toRinf i x.1.2 from
      Ring.DirectLimit.of_f hij x.1.2]
    exact x.2⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private def pullbackSystem : RingMapSystemUnbundled.{max uD u} J where
  R i := sourcePullback sys eB q i
  S i := ULift.{uD} (sys.S i)
  commRingR _ := inferInstance
  commRingS _ := inferInstance
  fR := fun {_ _} h ↦ sourcePullbackMap sys eB q h
  fS := fun {_ _} h ↦
    ULift.ringEquiv.symm.toRingHom.comp ((sys.fS h).comp ULift.ringEquiv.toRingHom)
  fR_id i x := by ext <;> simp [sourcePullbackMap, sys.fR_id]
  fR_comp := fun {_ _ _} hij hjk x ↦ by ext <;> simp [sourcePullbackMap, sys.fR_comp]
  fS_id i x := by ext; exact sys.fS_id i x.down
  fS_comp := fun {_ _ _} hij hjk x ↦ by ext; exact sys.fS_comp hij hjk x.down
  g i := ULift.ringEquiv.symm.toRingHom.comp
    ((sys.g i).comp ((RingHom.snd D (sys.R i)).comp (sourcePullback sys eB q i).subtype))
  square := fun {_ _} hij x ↦ by ext; exact sys.square hij x.1.2

private def pullbackToSource (i : J) : (pullbackSystem sys eB q).R i →+* D :=
  (RingHom.fst D (sys.R i)).comp (sourcePullback sys eB q i).subtype

private def pullbackToStage (i : J) : (pullbackSystem sys eB q).R i →+* sys.R i :=
  (RingHom.snd D (sys.R i)).comp (sourcePullback sys eB q i).subtype

private theorem pullbackToStage_surjective (hq : Function.Surjective q) (i : J) :
    Function.Surjective (pullbackToStage sys eB q i) := by
  intro r
  obtain ⟨d, hd⟩ := hq (eB (sys.toRinf i r))
  exact ⟨⟨(d, r), hd⟩, rfl⟩

private def pullbackSourceHom : (pullbackSystem sys eB q).Rinf →+* D :=
  Ring.DirectLimit.lift _ _ D (pullbackToSource sys eB q)
    (fun _ _ _ _ ↦ rfl)

private theorem pullbackSourceHom_of (i : J) (x : (pullbackSystem sys eB q).R i) :
    pullbackSourceHom sys eB q ((pullbackSystem sys eB q).toRinf i x) = x.1.1 :=
  Ring.DirectLimit.lift_of ..

private theorem pullbackSourceHom_bijective [IsDirectedOrder J] [Nonempty J] :
    Function.Bijective (pullbackSourceHom sys eB q) := by
  have : DirectedSystem sys.R (fun _ _ h ↦ sys.fR h) :=
    ⟨sys.fR_id, fun _ _ _ hij hjk x ↦ sys.fR_comp hij hjk x⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of (G := (pullbackSystem sys eB q).R) x
    have hfst : x.1.1 = 0 := by
      change pullbackSourceHom sys eB q ((pullbackSystem sys eB q).toRinf i x) = 0 at hx
      rwa [pullbackSourceHom_of] at hx
    have hsnd : sys.toRinf i x.1.2 = 0 := by
      apply eB.injective
      rw [map_zero, ← show q x.1.1 = eB (sys.toRinf i x.1.2) from x.2, hfst, map_zero]
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (f' := fun _ _ h ↦ sys.fR h) hsnd
    have hz : (pullbackSystem sys eB q).fR hij x = 0 := by
      apply Subtype.ext
      exact Prod.ext hfst hj
    rw [← Ring.DirectLimit.of_f hij x, hz, map_zero]
  · intro d
    obtain ⟨i, r, hr⟩ := Ring.DirectLimit.exists_of (G := sys.R) (eB.symm (q d))
    have hd : q d = eB (sys.toRinf i r) := by
      change sys.toRinf i r = eB.symm (q d) at hr
      rw [hr, eB.apply_symm_apply]
    exact ⟨(pullbackSystem sys eB q).toRinf i ⟨(d, r), hd⟩,
      pullbackSourceHom_of sys eB q i _⟩

private def pullbackSourceEquiv [IsDirectedOrder J] [Nonempty J] :
    (pullbackSystem sys eB q).Rinf ≃+* D :=
  RingEquiv.ofBijective (pullbackSourceHom sys eB q)
    (pullbackSourceHom_bijective sys eB q)

private def pullbackTargetEquiv :
    (pullbackSystem sys eB q).Sinf ≃+* sys.Sinf :=
  Ring.DirectLimit.congr (fun _ ↦ ULift.ringEquiv)
    (fun _ _ _ ↦ rfl)

private theorem pullbackTargetEquiv_of (i : J) (x : (pullbackSystem sys eB q).S i) :
    pullbackTargetEquiv sys eB q ((pullbackSystem sys eB q).toSinf i x) =
      sys.toSinf i x.down := Ring.DirectLimit.congr_apply_of ..

variable [IsDirectedOrder J] [Nonempty J]
variable {E : Type*} [CommRing E] (eE : sys.Sinf ≃+* E) (g : B →+* E)

private theorem pullback_comm
    (hcomm : eE.toRingHom.comp sys.gInf = g.comp eB.toRingHom) :
    ((pullbackTargetEquiv sys eB q).trans eE).toRingHom.comp
        (pullbackSystem sys eB q).gInf =
      (g.comp q).comp (pullbackSourceEquiv sys eB q).toRingHom := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  show eE (pullbackTargetEquiv sys eB q
      ((pullbackSystem sys eB q).gInf ((pullbackSystem sys eB q).toRinf i x))) =
    g (q (pullbackSourceHom sys eB q ((pullbackSystem sys eB q).toRinf i x)))
  rw [← RingMapSystemUnbundled.toSinf_g, pullbackTargetEquiv_of, pullbackSourceHom_of]
  show eE (sys.toSinf i (sys.g i x.1.2)) = g (q x.1.1)
  rw [sys.toSinf_g]
  have hc := DFunLike.congr_fun hcomm (sys.toRinf i x.1.2)
  change eE (sys.gInf (sys.toRinf i x.1.2)) = g (eB (sys.toRinf i x.1.2)) at hc
  rw [hc, ← show q x.1.1 = eB (sys.toRinf i x.1.2) from x.2]

private abbrev pullbackPolynomial (i : J) :
    MvPolynomial ((pullbackSystem sys eB q).S i) ((pullbackSystem sys eB q).R i) →+*
      MvPolynomial E D :=
  (polynomialEquiv (pullbackSystem sys eB q) (pullbackSourceEquiv sys eB q)
    ((pullbackTargetEquiv sys eB q).trans eE)).toRingHom.comp
      (polynomialCocone (pullbackSystem sys eB q) i)

private theorem pullbackPolynomial_C (i : J) (x : (pullbackSystem sys eB q).R i) :
    pullbackPolynomial sys eB q eE i (C x) = C x.1.1 := by
  show polynomialEquiv _ _ _ (polynomialCocone _ i (C x)) = _
  simp only [polynomialCocone, RingHom.comp_apply, map_C, rename_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, polynomialEquiv_C]
  exact congrArg C (pullbackSourceHom_of sys eB q i x)

private theorem pullbackPolynomial_X (i : J) (x : (pullbackSystem sys eB q).S i) :
    pullbackPolynomial sys eB q eE i (X x) = X (eE (sys.toSinf i x.down)) := by
  show polynomialEquiv _ _ _ (polynomialCocone _ i (X x)) = _
  simp only [polynomialCocone, RingHom.comp_apply, map_X, rename_X,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, polynomialEquiv_X,
    RingEquiv.trans_apply, pullbackTargetEquiv_of]

private theorem pullbackPolynomial_comp {i j : J} (hij : i ≤ j)
    (p : MvPolynomial ((pullbackSystem sys eB q).S i) ((pullbackSystem sys eB q).R i)) :
    pullbackPolynomial sys eB q eE j (polynomialTransition (pullbackSystem sys eB q) hij p) =
      pullbackPolynomial sys eB q eE i p := by
  rw [pullbackPolynomial, ← RingHom.comp_apply, RingHom.comp_assoc, polynomialCocone_comp]

private abbrev pullbackIdeal (i : J) :
    Ideal (MvPolynomial ((pullbackSystem sys eB q).S i) ((pullbackSystem sys eB q).R i)) :=
  (RingHom.ker (pullbackToStage sys eB q i)).map C

private theorem pullbackIdeal_map_le (i : J) :
    (pullbackIdeal sys eB q i).map (pullbackPolynomial sys eB q eE i) ≤
      (RingHom.ker q).map (C (σ := E)) := by
  rw [pullbackIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro x hx
  show pullbackPolynomial sys eB q eE i (C x) ∈ (RingHom.ker q).map C
  rw [pullbackPolynomial_C]
  apply Ideal.mem_map_of_mem
  show q x.1.1 = 0
  have hx : x.1.2 = 0 := hx
  rw [show q x.1.1 = eB (sys.toRinf i x.1.2) from x.2, hx, map_zero, map_zero]

omit [IsDirectedOrder J] [Nonempty J] in
private theorem pullbackIdeal_transition_le {i j : J} (hij : i ≤ j) :
    (pullbackIdeal sys eB q i).map (polynomialTransition (pullbackSystem sys eB q) hij) ≤
      pullbackIdeal sys eB q j := by
  rw [pullbackIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro x hx
  show polynomialTransition (pullbackSystem sys eB q) hij (C x) ∈ pullbackIdeal sys eB q j
  simp only [polynomialTransition, RingHom.comp_apply, map_C, rename_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  apply Ideal.mem_map_of_mem
  show sys.fR hij x.1.2 = 0
  rw [show x.1.2 = 0 from hx, map_zero]

private theorem pullbackIdeal_surjective {x : MvPolynomial E D}
    (hx : x ∈ (RingHom.ker q).map C) :
    ∃ i p, p ∈ pullbackIdeal sys eB q i ∧ pullbackPolynomial sys eB q eE i p = x := by
  classical
  have hs : ∀ x : MvPolynomial E D, ∃ i p, pullbackPolynomial sys eB q eE i p = x := by
    intro x
    let e := polynomialEquiv (pullbackSystem sys eB q) (pullbackSourceEquiv sys eB q)
      ((pullbackTargetEquiv sys eB q).trans eE)
    obtain ⟨i, p, hp⟩ := polynomialCocone_surjective (pullbackSystem sys eB q) (e.symm x)
    refine ⟨i, p, ?_⟩
    show e (polynomialCocone _ i p) = x
    rw [hp, e.apply_symm_apply]
  change x ∈ Ideal.span (C '' (RingHom.ker q : Set D)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    let i : J := Classical.arbitrary J
    let d' : (pullbackSystem sys eB q).R i := ⟨(d, 0), by simpa using hd⟩
    refine ⟨i, C d', Ideal.mem_map_of_mem C (show d' ∈ RingHom.ker
      (pullbackToStage sys eB q i) from rfl), pullbackPolynomial_C sys eB q eE i d'⟩
  | zero => exact ⟨Classical.arbitrary J, 0, Ideal.zero_mem _, map_zero _⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨i, p, hp, hpx⟩ := hx'
    obtain ⟨j, r, hr, hry⟩ := hy'
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, polynomialTransition _ hik p + polynomialTransition _ hjk r,
      Ideal.add_mem _
        (pullbackIdeal_transition_le sys eB q hik (Ideal.mem_map_of_mem _ hp))
        (pullbackIdeal_transition_le sys eB q hjk (Ideal.mem_map_of_mem _ hr)), ?_⟩
    rw [map_add, pullbackPolynomial_comp sys eB q eE hik p,
      pullbackPolynomial_comp sys eB q eE hjk r, hpx, hry]
  | smul a x hx hx' =>
    obtain ⟨i, p, hp, hpx⟩ := hx'
    obtain ⟨j, r, hra⟩ := hs a
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, polynomialTransition _ hjk r * polynomialTransition _ hik p,
      Ideal.mul_mem_left _ _
        (pullbackIdeal_transition_le sys eB q hik (Ideal.mem_map_of_mem _ hp)), ?_⟩
    show pullbackPolynomial sys eB q eE k (_ * _) = a * x
    rw [map_mul, pullbackPolynomial_comp sys eB q eE hjk r,
      pullbackPolynomial_comp sys eB q eE hik p, hra, hpx]

omit [IsDirectedOrder J] [Nonempty J] in
private theorem pullbackIdeal_inf_sq (hq : Function.Surjective q)
    (h : ∀ i : J, RingHom.IsLocalCompleteIntersection (sys.g i)) (i : J) :
    pullbackIdeal sys eB q i ⊓
        RingHom.ker (eval₂Hom ((pullbackSystem sys eB q).g i) _root_.id) ^ 2 =
      pullbackIdeal sys eB q i *
        RingHom.ker (eval₂Hom ((pullbackSystem sys eB q).g i) _root_.id) := by
  let p := eval₂Hom ((sys.g i).comp (pullbackToStage sys eB q i)) ULift.down
  have he : ULift.ringEquiv.toRingHom.comp
      (eval₂Hom ((pullbackSystem sys eB q).g i) _root_.id) = p := by
    apply MvPolynomial.ringHom_ext <;> intro x
    · simp [p, pullbackSystem, pullbackToStage]
    · simp [p, pullbackSystem]; rfl
  have hk : RingHom.ker (eval₂Hom ((pullbackSystem sys eB q).g i) _root_.id) =
      RingHom.ker p := by
    rw [← he, RingHom.ker_comp_of_injective _ ULift.down_injective]
  rw [hk]
  exact polynomial_inf_sq_eq_mul_of_isLocalCompleteIntersection
    (pullbackToStage sys eB q i) (pullbackToStage_surjective sys eB q hq i)
    (sys.g i) (h i) ULift.down (fun x ↦ ⟨X (ULift.up x), by simp⟩)

private theorem canonical_polynomial_inf_sq_eq_mul (hq : Function.Surjective q)
    (hcomm : eE.toRingHom.comp sys.gInf = g.comp eB.toRingHom)
    (h : ∀ i : J, RingHom.IsLocalCompleteIntersection (sys.g i)) :
    (RingHom.ker q).map (C (σ := E)) ⊓ RingHom.ker (eval₂Hom (g.comp q) _root_.id) ^ 2 =
      (RingHom.ker q).map C * RingHom.ker (eval₂Hom (g.comp q) _root_.id) := by
  let ps := pullbackSystem sys eB q
  let e := polynomialEquiv ps (pullbackSourceEquiv sys eB q)
    ((pullbackTargetEquiv sys eB q).trans eE)
  let K := RingHom.ker (eval₂Hom (g.comp q) _root_.id)
  let Kinf := RingHom.ker (eval₂Hom ps.gInf _root_.id)
  have heK : Kinf.map e.toRingHom = K := polynomialEquiv_ker ps _ _ _
    (pullback_comm sys eB q eE g hcomm)
  have hK : ∀ i, (RingHom.ker (eval₂Hom (ps.g i) _root_.id)).map
      (pullbackPolynomial sys eB q eE i) ≤ K := by
    intro i
    show Ideal.map (e.toRingHom.comp (polynomialCocone ps i)) _ ≤ K
    rw [← Ideal.map_map, ← heK]
    exact Ideal.map_mono (polynomialCocone_ker_le ps i)
  apply le_antisymm
  · rintro x ⟨hxI, hxK⟩
    obtain ⟨i, p, hpI, hpx⟩ := pullbackIdeal_surjective sys eB q eE hxI
    have hpK : polynomialCocone ps i p ∈ Kinf ^ 2 := by
      have hm : e (polynomialCocone ps i p) ∈ (Kinf ^ 2).map e.toRingHom := by
        rw [Ideal.map_pow, heK]
        show pullbackPolynomial sys eB q eE i p ∈ K ^ 2
        rwa [hpx]
      have : polynomialCocone ps i p ∈ ((Kinf ^ 2).map e.toRingHom).comap e.toRingHom := hm
      rwa [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at this
    obtain ⟨j, hij, hj⟩ := polynomialCocone_ker_sq ps i p hpK
    have hpj : polynomialTransition ps hij p ∈ pullbackIdeal sys eB q j :=
      pullbackIdeal_transition_le sys eB q hij (Ideal.mem_map_of_mem _ hpI)
    have hpIK : polynomialTransition ps hij p ∈ pullbackIdeal sys eB q j *
        RingHom.ker (eval₂Hom (ps.g j) _root_.id) := by
      rw [← pullbackIdeal_inf_sq sys eB q hq h j]
      exact ⟨hpj, hj⟩
    have hm := Ideal.mem_map_of_mem (pullbackPolynomial sys eB q eE j) hpIK
    rw [Ideal.map_mul] at hm
    have hm' := Ideal.mul_mono (pullbackIdeal_map_le sys eB q eE j) (hK j) hm
    rwa [pullbackPolynomial_comp sys eB q eE hij p, hpx] at hm'
  · refine le_inf Ideal.mul_le_left ?_
    rw [sq]
    apply Ideal.mul_mono _ le_rfl
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show eval₂Hom (g.comp q) _root_.id (C x) = 0
    simp [show q x = 0 from hx]

end Pullback

/-- Let `A → B → C` be ring maps and suppose that `B → C` is exhibited as a filtered
colimit of local complete intersection homomorphisms, with `eB`, `eC`, and `hcomm` identifying
the directed system's colimit map with `B → C`. For presentations `α : A[x_s] → B`
and `β : B[y_t] → C`, the canonical map
`C ⊗_B (I / I²) → K / K²` from the conormal module of `α` to that of the induced
presentation `β.comp α` is injective. -/
@[stacks 07D5]
public theorem cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection
    {A : Type u₁} {B : Type u₂} [CommRing A] [CommRing B] [Algebra A B]
    {C : Type u₃} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {S : Type w} {T : Type w'} (α : Generators A B S) (β : Generators B C T)
    {J : Type u₄} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (sys : RingMapSystemUnbundled.{u₅} J)
    (eB : sys.Rinf ≃+* B) (eC : sys.Sinf ≃+* C)
    (hcomm : eC.toRingHom.comp sys.gInf = (algebraMap B C).comp eB.toRingHom)
    (h : ∀ i : J, RingHom.IsLocalCompleteIntersection (sys.g i)) :
    Function.Injective
      ((Extension.Cotangent.map (β.toComp α).toExtensionHom).liftBaseChange C) := by
  let q := algebraMap α.Ring B
  let g := algebraMap B C
  let e : (β.comp α).Ring ≃+* MvPolynomial T α.Ring := (sumAlgEquiv A T S).toRingEquiv
  let a := (algebraMap (β.comp α).Ring C).comp e.symm.toRingHom
  let f := (β.toComp α).toAlgHom.toRingHom
  have he : e.toRingHom.comp f = MvPolynomial.C := by
    show (sumAlgEquiv A T S).toAlgHom.toRingHom.comp
      (β.toComp α).toAlgHom.toRingHom = _
    rw [Generators.toComp_toAlgHom]
    exact congrArg AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr A T S)
  have he' : e.symm.toRingHom.comp MvPolynomial.C = f := RingHom.ext fun x ↦
    e.injective <| (e.apply_symm_apply _).trans (DFunLike.congr_fun he x).symm
  have haC : a.comp MvPolynomial.C = g.comp q := by
    dsimp only [a]
    rw [RingHom.comp_assoc, he']
    exact RingHom.ext fun x ↦ (β.toComp α).toExtensionHom.algebraMap_toRingHom x
  have hsq : (RingHom.ker q).map MvPolynomial.C ⊓ RingHom.ker a ^ 2 =
      (RingHom.ker q).map MvPolynomial.C * RingHom.ker a := by
    apply polynomial_inf_sq_eq_mul_of_surjective_presentations (RingHom.ker q)
      (eval₂Hom (g.comp q) _root_.id) a (fun x ↦ ⟨X x, by simp⟩)
      ((β.comp α).algebraMap_surjective.comp e.symm.surjective)
    · simpa only [eval₂Hom_comp_C] using haC
    · rw [haC]
      intro x hx
      show g (q x) = 0
      rw [show q x = 0 from hx, map_zero]
    · exact canonical_polynomial_inf_sq_eq_mul sys eB q eC g
        α.algebraMap_surjective hcomm h
  have hI : (α.ker.map f).map e.toRingHom = (RingHom.ker q).map MvPolynomial.C := by
    rw [Ideal.map_map, he]
    rfl
  have hK : (β.comp α).ker.map e.toRingHom = RingHom.ker a := by
    have hk : (RingHom.ker a).comap e.toRingHom = (β.comp α).ker := by
      ext x
      show algebraMap (β.comp α).Ring C (e.symm (e x)) = 0 ↔
        algebraMap (β.comp α).Ring C x = 0
      rw [e.symm_apply_apply]
    rw [← hk]
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _
  have hIK : α.ker.map f ≤ (β.comp α).ker := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show algebraMap (β.comp α).Ring C (f x) = 0
    have hf := (β.toComp α).toExtensionHom.algebraMap_toRingHom x
    change algebraMap (β.comp α).Ring C (f x) =
      algebraMap B C (algebraMap α.Ring B x) at hf
    rw [hf, show algebraMap α.Ring B x = 0 from hx, map_zero]
  have hsq' : α.ker.map f ⊓ (β.comp α).ker ^ 2 =
      α.ker.map f * (β.comp α).ker := by
    apply le_antisymm
    · rintro x ⟨hxI, hxK⟩
      have hx : e x ∈ ((α.ker.map f).map e.toRingHom) * ((β.comp α).ker.map e.toRingHom) := by
        rw [hI, hK, ← hsq]
        constructor
        · rw [← hI]
          exact Ideal.mem_map_of_mem e.toRingHom hxI
        · rw [← hK, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem e.toRingHom hxK
      rw [← Ideal.map_mul] at hx
      have hx' : x ∈
        (Ideal.map e.toRingHom (α.ker.map f * (β.comp α).ker)).comap e.toRingHom := hx
      rwa [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hx'
    · exact le_inf Ideal.mul_le_left (by simpa only [sq] using Ideal.mul_mono hIK le_rfl)
  exact cotangentMap_toComp_injective_of_inf_sq α β hsq'

end

end RingHom

end
