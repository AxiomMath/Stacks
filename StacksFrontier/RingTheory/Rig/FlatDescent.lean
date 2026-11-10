module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Algebra.Ring.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.Units
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Flat
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
import StacksFrontier.RingTheory.Flat.FaithfullyFlatComp

/-!
# Faithfully flat descent of rig-flatness

Consider a commutative square of adic homomorphisms of topological finite type between Noetherian
weakly admissible topological rings
```
B ---β--> B'
↑         ↑
φ         φ'
|         |
A ---α--> A'
```
If `α` is flat and `β` is faithfully flat, then rig-flatness of `φ'` forces rig-flatness of `φ`.

The proof localizes the square at a topologically nilpotent `f : A` and completes, which produces
the analogous square of completed principal localizations; the horizontal maps of that square are
still flat resp. faithfully flat, because both flatness and faithful flatness are preserved by
`IsLocalization.Away.map` and by the induced map of adic completions.  Rig-flatness of `φ'` then
gives flatness of the right-hand vertical leg after inverting the relevant element, and ordinary
faithfully flat descent of flatness in a commutative square gives flatness of the left-hand leg.

## Main results

* `Rig.RingHom.isRigFlat_of_faithfullyFlat` — descent of rig-flatness in such a square.

The completion-comparison infrastructure the proof builds is shared with the ascent lemma of
Stacks 0GGS, so the following are public:

* `Rig.flat_mapAdicCompletion_of_eq` — the induced map of adic completions along a flat algebra
  map out of a Noetherian ring is flat.
* `Rig.flat_awayMap` — the induced map of principal localizations of a flat map is flat.
* `Rig.denseRange_algebraMap_adicCompletion` — a ring is dense in its adic completion.
* `Rig.isTopologicallyOfFiniteType_awayMap` — topological finite type passes to principal
  localizations.

## Implementation notes

The four maps of the square are explicit ring homomorphisms rather than `algebraMap`s, and the
ambient hypotheses of the source — weak admissibility, Noetherianity, adicness, topological finite
type and continuity — are carried as hypotheses, matching the shape of `Rig.RingHom.IsRigFlat`.
Commutativity is an equality of ring homomorphisms.

The completed principal localizations of the four corners are `AdicCompletion`s of
`Localization.Away`, topologized by the adic topology of the extended ideal, exactly as in the
definition of `Rig.RingHom.IsRigFlat`; the maps between them come from
`Stacks.Nagata.PthRootDescent.mapAdicCompletion`.

## References

* [Stacks Project, Tag 0GGT](https://stacks.math.columbia.edu/tag/0GGT)
-/

@[expose] public section

namespace Rig

open TensorProduct

universe u v

/-! ### Faithfully flat descent of flatness in a commutative square -/

/-- In a commutative square of rings with flat lower edge, faithfully flat right edge and flat
far vertical leg, the near vertical leg is flat.

Taking the lower edge to be the identity gives flat descent along the second factor of a
composite, `Rig.flat_of_faithfullyFlat_comp`. -/
theorem flat_of_faithfullyFlat_square
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (f : A →+* B) (α : A →+* A') (β : B →+* B') (g : A' →+* B')
    (hcomm : β.comp f = g.comp α) (hα : α.Flat) (hβ : β.FaithfullyFlat)
    (hg : g.Flat) : f.Flat := by
  let : Algebra A B := f.toAlgebra
  let : Algebra A A' := α.toAlgebra
  let : Algebra B B' := β.toAlgebra
  let : Algebra A' B' := g.toAlgebra
  let : Algebra A B' := (β.comp f).toAlgebra
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.FaithfullyFlat B B' := RingHom.faithfullyFlat_algebraMap_iff.mp hβ
  have hmap : (β.comp f).Flat := by
    rw [hcomm]
    exact hα.comp hg
  let : Module.Flat A B' := RingHom.flat_algebraMap_iff.mp hmap
  let e : (B' ⊗[B] B) ≃ₗ[A] B' :=
    LinearEquiv.restrictScalars A
      ((TensorProduct.comm B B' B).trans (Algebra.TensorProduct.lid B B').toLinearEquiv)
  exact RingHom.flat_algebraMap_iff.mpr <|
    (Module.Flat.tensorProduct_iff_of_faithfullyFlat
      (R := A) (S := B) (S' := B') (M := B)).mp (Module.Flat.of_linearEquiv e)

/-! ### Comparing module and ring adic completions -/

/-- Restricting scalars of `(I.map (algebraMap R S)) ^ n • ⊤` to `R` gives `I ^ n • ⊤`. -/
private theorem restrictScalars_map_pow_smul_top
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S] (n : ℕ) :
    (((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)).restrictScalars R) =
      I ^ n • (⊤ : Submodule R S) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- The `n`-th stage of the module-theoretic `I`-adic completion of an `R`-algebra `S` agrees with
the `n`-th stage of its ring-theoretic completion along the extension of `I`. -/
private noncomputable def quotPowSMulEquivQuotPow
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S] (n : ℕ) :
    (S ⧸ I ^ n • (⊤ : Submodule R S)) ≃ₗ[R]
      S ⧸ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)) := by
  exact (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top I n).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R
      ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)))

private theorem quotPowSMulEquivQuotPow_mk
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S] (n : ℕ) (x : S) :
    quotPowSMulEquivQuotPow I n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  change (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top I n).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv R
        ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)))
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]

private theorem quotPowSMulEquivQuotPow_transitionMap
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S] {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ I ^ n • (⊤ : Submodule R S)) :
    quotPowSMulEquivQuotPow I m (AdicCompletion.transitionMap I S h x) =
      AdicCompletion.transitionMap (I.map (algebraMap R S)) S h
        (quotPowSMulEquivQuotPow I n x) := by
  induction x using Quotient.inductionOn' with
  | _ x =>
      simp only [AdicCompletion.transitionMap, Submodule.factorPow]
      change quotPowSMulEquivQuotPow I m (Submodule.Quotient.mk x) =
        Submodule.factor (Submodule.pow_smul_top_le (I.map (algebraMap R S)) S h)
          (quotPowSMulEquivQuotPow I n (Submodule.Quotient.mk x))
      rw [quotPowSMulEquivQuotPow_mk, quotPowSMulEquivQuotPow_mk]
      exact (Submodule.factor_mk
        (Submodule.pow_smul_top_le (I.map (algebraMap R S)) S h) x).symm

/-- The module-theoretic `I`-adic completion of an `R`-algebra `S` is `R`-linearly isomorphic to
the ring-theoretic adic completion of `S` along the extension of `I`. -/
private noncomputable def adicCompletionRestrictEquiv
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S] :
    AdicCompletion I S ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n => quotPowSMulEquivQuotPow I n (x.val n), by
    intro m n h
    rw [← quotPowSMulEquivQuotPow_transitionMap I h, x.property h]⟩
  invFun x := ⟨fun n => (quotPowSMulEquivQuotPow I n).symm (x.val n), by
    intro m n h
    apply (quotPowSMulEquivQuotPow I m).injective
    rw [quotPowSMulEquivQuotPow_transitionMap I h]
    simp [x.property h]⟩
  left_inv x := AdicCompletion.ext fun n ↦ (quotPowSMulEquivQuotPow I n).symm_apply_apply (x.val n)
  right_inv x := AdicCompletion.ext fun n ↦ (quotPowSMulEquivQuotPow I n).apply_symm_apply (x.val n)
  map_add' x y := AdicCompletion.ext fun n ↦
    (quotPowSMulEquivQuotPow I n).map_add (x.val n) (y.val n)
  map_smul' r x := AdicCompletion.ext fun n ↦ (quotPowSMulEquivQuotPow I n).map_smul r (x.val n)

/-- Upgrading `Rig.adicCompletionRestrictEquiv` to a semilinear isomorphism over the completion of
the base, once the map of completions induced by `algebraMap R S` is known to be the structure
map. -/
private noncomputable def adicCompletionRestrictEquivOverCompletion
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    [Algebra R S] [IsScalarTower R S S]
    (fhat : AdicCompletion I R →+* AdicCompletion (I.map (algebraMap R S)) S)
    [Algebra (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S)]
    (hfhat : algebraMap (AdicCompletion I R)
      (AdicCompletion (I.map (algebraMap R S)) S) = fhat)
    (hfhat_eval : ∀ n a,
      AdicCompletion.evalₐ (I.map (algebraMap R S)) n (fhat a) =
        Ideal.quotientMap ((I.map (algebraMap R S)) ^ n) (algebraMap R S)
          (Ideal.map_le_iff_le_comap.mp (show
            Ideal.map (algebraMap R S) (I ^ n) ≤ (I.map (algebraMap R S)) ^ n by
              rw [Ideal.map_pow]))
          (AdicCompletion.evalₐ I n a)) :
    AdicCompletion I S ≃ₗ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  let J : Ideal S := I.map (algebraMap R S)
  let e := adicCompletionRestrictEquiv (R := R) (S := S) I
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro a x
  conv_rhs => rw [Algebra.smul_def, hfhat]
  apply AdicCompletion.ext
  intro n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  have ha_val : a.val n = Submodule.Quotient.mk r :=
    AdicCompletion.val_eq_mk I n a r hr.symm
  have hfa_eval := hfhat_eval n a
  rw [hr.symm, Ideal.quotientMap_mk] at hfa_eval
  have hfhat_val : (fhat a).val n = Submodule.Quotient.mk (algebraMap R S r) :=
    AdicCompletion.val_eq_mk (I.map (algebraMap R S)) n (fhat a) (algebraMap R S r) hfa_eval
  change quotPowSMulEquivQuotPow I n ((a • x).val n) = (fhat a * e x).val n
  rw [AdicCompletion.smul_eval, AdicCompletion.val_mul, ha_val, hfhat_val]
  have hmul (y : S ⧸ (J ^ n • (⊤ : Submodule S S))) :
      (Submodule.Quotient.mk (algebraMap R S r) : S ⧸ (J ^ n • (⊤ : Submodule S S))) * y =
        r • y := by
    induction y using Quotient.inductionOn' with
    | _ y =>
        change Submodule.Quotient.mk ((algebraMap R S r) * y) = _
        simp [Algebra.smul_def, Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk''_eq_mk]
  have hscalar :
      (Submodule.Quotient.mk r : R ⧸ (I ^ n • (⊤ : Submodule R R))) • x.val n = r • x.val n := by
    induction x.val n using Quotient.inductionOn' with
    | _ y => rfl
  have hex : (e x).val n = quotPowSMulEquivQuotPow I n (x.val n) := rfl
  rw [hmul, hex, hscalar]
  exact (quotPowSMulEquivQuotPow I n).map_smul r (x.val n)

/-! ### Flatness and faithful flatness of induced maps of adic completions -/

/-- The map of adic completions induced by a flat algebra map out of a Noetherian ring is flat. -/
private theorem flat_mapAdicCompletion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [IsScalarTower R S S]
    (I : Ideal R) (hflat : (algebraMap R S).Flat) :
    (Stacks.Nagata.PthRootDescent.mapAdicCompletion I (I.map (algebraMap R S)) le_rfl).Flat := by
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  have hflatQ : Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
    let : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := Module.Flat.baseChange R (R ⧸ I) S
    exact Module.Flat.of_linearEquiv
      ((TensorProduct.quotTensorEquivQuotSMul S I).extendScalarsOfSurjective
        (S := R ⧸ I) Ideal.Quotient.mk_surjective).symm
  have htor := by
    let : Module.Flat (ULift.{v} R) (ULift.{u} S) :=
      Module.Flat.ulift_left_iff.mpr inferInstance
    exact isZero_Tor_one_of_flat (ModuleCat.of (ULift.{v} R) (ULift.{u} S))
      (ModuleCat.of (ULift.{v} R) (ULift.{v} (R ⧸ I)))
  have hmodule :=
    (AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient I I.fg_of_isNoetherianRing
      inferInstance hflatQ htor).2
  let fhat := Stacks.Nagata.PthRootDescent.mapAdicCompletion I (I.map (algebraMap R S)) (le_refl _)
  let : Algebra (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) :=
    fhat.toAlgebra
  let : IsScalarTower (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S)
      (AdicCompletion (I.map (algebraMap R S)) S) := IsScalarTower.of_algebraMap_eq' rfl
  let e := adicCompletionRestrictEquivOverCompletion I fhat rfl
    (fun n a => Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion le_rfl n a)
  let : Module.Flat (AdicCompletion I R) (AdicCompletion I S) := hmodule
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_linearEquiv e.symm)

/-- The adic completion of a ring modulo the extension of the defining ideal is the original
quotient. -/
private noncomputable def adicCompletionQuotientEquiv
    {R : Type*} [CommRing R] (I : Ideal R) (hIFG : I.FG) :
    AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_evalOneₐ_eq_map I hIFG).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))

private theorem adicCompletionQuotientEquiv_mk
    {R : Type*} [CommRing R] (I : Ideal R) (hIFG : I.FG) (x : AdicCompletion I R) :
    adicCompletionQuotientEquiv I hIFG (Ideal.Quotient.mk _ x) = AdicCompletion.evalOneₐ I x := by
  change RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
    (Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom) x) = _
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

private theorem evalOneₐ_mapAdicCompletion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (J : Ideal S) (hmap : I.map (algebraMap R S) ≤ J) (x : AdicCompletion I R) :
    AdicCompletion.evalOneₐ J (Stacks.Nagata.PthRootDescent.mapAdicCompletion I J hmap x) =
      Ideal.quotientMap J (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hmap)
        (AdicCompletion.evalOneₐ I x) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 x)
  rw [← AdicCompletion.factorₐ_evalₐ_one, Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion hmap]
  conv_rhs => rw [← AdicCompletion.factorₐ_evalₐ_one]
  rw [← hr]
  change Ideal.Quotient.factor (show J ^ 1 ≤ J by simp)
      (Ideal.quotientMap (J ^ 1) (algebraMap R S)
        (Ideal.map_le_iff_le_comap.mp (by
          simpa only [pow_one, Ideal.map_pow] using hmap))
        (Ideal.Quotient.mk (I ^ 1) r)) =
    Ideal.quotientMap J (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hmap)
      (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) (Ideal.Quotient.mk (I ^ 1) r))
  rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.quotientMap_mk]

/-- A flat ring homomorphism whose reduction modulo an ideal contained in the Jacobson radical is
faithfully flat is itself faithfully flat. -/
private theorem faithfullyFlat_of_flat_of_quotient
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I.map f ≤ J)
    (hIjac : I ≤ Ring.jacobson R) (hflat : f.Flat)
    (hquot : (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)).FaithfullyFlat) :
    f.FaithfullyFlat := by
  let : Algebra R S := f.toAlgebra
  change Module.FaithfullyFlat R S
  rw [Module.faithfullyFlat_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mp hflat, ?_⟩
  intro m hm
  have hIm : I ≤ m := hIjac.trans (Ring.jacobson_le_of_isMaximal m)
  let qR := Ideal.Quotient.mk I
  let mbar : Ideal (R ⧸ I) := m.map qR
  have hmbar_ne : mbar ≠ ⊤ := by
    intro htop
    have hc := Ideal.comap_map_of_surjective qR Ideal.Quotient.mk_surjective m
    rw [show Ideal.map qR m = ⊤ from htop, Ideal.comap_top] at hc
    have hc' : I ⊔ m = ⊤ := by
      simpa only [qR, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm] using hc.symm
    exact hm.ne_top ((sup_eq_right.mpr hIm).symm.trans hc')
  have hmbar : mbar.IsMaximal :=
    Or.resolve_left
      (Ideal.map_eq_top_or_isMaximal_of_surjective qR Ideal.Quotient.mk_surjective hm) hmbar_ne
  intro htop
  have hmapm : Ideal.map f m = ⊤ := by
    have hmap : Ideal.map (algebraMap R S) m = ⊤ :=
      (Submodule.restrictScalars_eq_top_iff R S _).mp (by simpa [Ideal.smul_top_eq_map] using htop)
    simpa [RingHom.algebraMap_toAlgebra f] using hmap
  have hcomp : (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)).comp qR =
      (Ideal.Quotient.mk J).comp f := by
    ext x
    simp [qR, Ideal.quotientMap]
  have hmapbar :
      Ideal.map (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)) mbar = ⊤ := by
    rw [show mbar = Ideal.map qR m from rfl, Ideal.map_map, hcomp, ← Ideal.map_map, hmapm,
      Ideal.map_top]
  let : Algebra (R ⧸ I) (S ⧸ J) :=
    (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)).toAlgebra
  have hbad := hquot.submodule_ne_top hmbar
  rw [Ideal.smul_top_eq_map] at hbad
  exact hbad ((Submodule.restrictScalars_eq_top_iff (R ⧸ I) (S ⧸ J) _).mpr hmapbar)

/-- The map of adic completions induced by a faithfully flat algebra map out of a Noetherian ring
is faithfully flat. -/
private theorem faithfullyFlat_mapAdicCompletion
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [IsScalarTower R S S] (I : Ideal R)
    (hff : (algebraMap R S).FaithfullyFlat) :
    (Stacks.Nagata.PthRootDescent.mapAdicCompletion I (I.map (algebraMap R S))
      le_rfl).FaithfullyFlat := by
  let J : Ideal S := I.map (algebraMap R S)
  let Ihat : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R))
  let Jhat : Ideal (AdicCompletion J S) := J.map (algebraMap S (AdicCompletion J S))
  let fhat := Stacks.Nagata.PthRootDescent.mapAdicCompletion I J (le_refl _)
  let : Algebra (AdicCompletion I R) (AdicCompletion J S) := fhat.toAlgebra
  let : IsScalarTower (AdicCompletion I R) (AdicCompletion J S) (AdicCompletion J S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hflat : fhat.Flat := flat_mapAdicCompletion I hff.flat
  have hcomp_of : fhat.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp (algebraMap R S) := by
    ext x
    simp [fhat, Stacks.Nagata.PthRootDescent.mapAdicCompletion_of]
  have hmap : Ihat.map fhat ≤ Jhat := by
    change (I.map (algebraMap R (AdicCompletion I R))).map fhat ≤
      J.map (algebraMap S (AdicCompletion J S))
    rw [Ideal.map_map, hcomp_of, Ideal.map_map]
  let eR := adicCompletionQuotientEquiv I I.fg_of_isNoetherianRing
  let eS := adicCompletionQuotientEquiv J (I.fg_of_isNoetherianRing.map _)
  let q : R ⧸ I →+* S ⧸ J :=
    Ideal.quotientMap J (algebraMap R S)
      (Ideal.map_le_iff_le_comap.mp (show Ideal.map (algebraMap R S) I ≤ J from le_rfl))
  let : Algebra (R ⧸ I) (S ⧸ J) := q.toAlgebra
  have hq : q.FaithfullyFlat := by
    have hq0 : Module.FaithfullyFlat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
      let : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.mp hff
      let : Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := inferInstance
      exact Module.FaithfullyFlat.of_linearEquiv (R := R ⧸ I) (M := (R ⧸ I) ⊗[R] S)
        (N := S ⧸ (I • (⊤ : Submodule R S)))
        ((TensorProduct.quotTensorEquivQuotSMul S I).extendScalarsOfSurjective
          (S := R ⧸ I) Ideal.Quotient.mk_surjective).symm
    have hsub : I • (⊤ : Submodule R S) = Submodule.restrictScalars R J := by
      rw [Ideal.smul_top_eq_map]
    let eN : (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R] S ⧸ J :=
      (Submodule.quotEquivOfEq _ _ hsub).trans
        (Submodule.Quotient.restrictScalarsEquiv (R := S) (M := S) R J)
    let eQ : (S ⧸ J) ≃ₗ[R ⧸ I] (S ⧸ (I • (⊤ : Submodule R S))) :=
      { toFun := eN.symm
        invFun := eN
        left_inv := eN.apply_symm_apply
        right_inv := eN.symm_apply_apply
        map_add' := eN.symm.map_add
        map_smul' := by
          intro c x
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
          simpa [RingHom.algebraMap_toAlgebra, q, Ideal.quotientMap_mk, Algebra.smul_def] using
            eN.symm.map_smul r x }
    change Module.FaithfullyFlat (R ⧸ I) (S ⧸ J)
    exact Module.FaithfullyFlat.of_linearEquiv (R := R ⧸ I)
      (M := S ⧸ (I • (⊤ : Submodule R S))) (N := S ⧸ J) eQ
  have heq : eS.toRingHom.comp (Ideal.quotientMap Jhat fhat
      (Ideal.map_le_iff_le_comap.mp hmap)) = q.comp eR.toRingHom := by
    ext x
    change adicCompletionQuotientEquiv J (I.fg_of_isNoetherianRing.map _)
        (Ideal.Quotient.mk Jhat (fhat x)) =
      q (adicCompletionQuotientEquiv I I.fg_of_isNoetherianRing (Ideal.Quotient.mk Ihat x))
    rw [adicCompletionQuotientEquiv_mk, adicCompletionQuotientEquiv_mk]
    exact evalOneₐ_mapAdicCompletion I J le_rfl x
  have hqhat :
      (Ideal.quotientMap Jhat fhat (Ideal.map_le_iff_le_comap.mp hmap)).FaithfullyFlat := by
    have hqhat_eq : Ideal.quotientMap Jhat fhat (Ideal.map_le_iff_le_comap.mp hmap) =
        eS.symm.toRingHom.comp (q.comp eR.toRingHom) := by
      ext x
      exact eS.injective (by
        simpa [RingHom.comp_apply] using DFunLike.congr_fun heq (Ideal.Quotient.mk Ihat x))
    rw [hqhat_eq]
    have heR : (eR.toRingHom).FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective eR.bijective
    have heS : (eS.symm.toRingHom).FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective eS.symm.bijective
    exact RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.comp heR hq) heS
  have hIjac : Ihat ≤ Ring.jacobson (AdicCompletion I R) := by
    simpa only [Ideal.jacobson_bot] using
      (AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot
        I).2.2.2.1
  exact faithfullyFlat_of_flat_of_quotient fhat Ihat Jhat hmap hIjac hflat hqhat

/-- The map of adic completions induced by a flat algebra map out of a Noetherian ring is flat,
stated for an ideal of the target equal to the extension of the ideal of the source. -/
public theorem flat_mapAdicCompletion_of_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [IsScalarTower R S S]
    (I : Ideal R) (J : Ideal S) (hIJ : I.map (algebraMap R S) = J)
    (hflat : (algebraMap R S).Flat) :
    (Stacks.Nagata.PthRootDescent.mapAdicCompletion I J (le_of_eq hIJ)).Flat := by
  subst J
  exact flat_mapAdicCompletion I hflat

private theorem faithfullyFlat_mapAdicCompletion_of_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [IsScalarTower R S S]
    (I : Ideal R) (J : Ideal S) (hIJ : I.map (algebraMap R S) = J)
    (hff : (algebraMap R S).FaithfullyFlat) :
    (Stacks.Nagata.PthRootDescent.mapAdicCompletion I J (le_of_eq hIJ)).FaithfullyFlat := by
  subst J
  exact faithfullyFlat_mapAdicCompletion I hff

/-! ### Adicness, continuity and topological finite type of the completed maps -/

private theorem isAdic_adicTopology {R : Type*} [CommRing R] (I : Ideal R) :
    @IsAdic R _ I.adicTopology I := rfl

/-- The map of adic completions induced by a ring homomorphism carrying `I` onto `J` is adic for
the adic topologies of the extended ideals. -/
private theorem isAdic_mapAdicCompletion
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map f = J) :
    letI : Algebra R S := f.toAlgebra
    letI : TopologicalSpace (AdicCompletion I R) :=
      (I.map (algebraMap R (AdicCompletion I R))).adicTopology
    letI : TopologicalSpace (AdicCompletion J S) :=
      (J.map (algebraMap S (AdicCompletion J S))).adicTopology
    RingHom.IsAdic (Stacks.Nagata.PthRootDescent.mapAdicCompletion I J (le_of_eq hIJ)) := by
  let : Algebra R S := f.toAlgebra
  let fhat := Stacks.Nagata.PthRootDescent.mapAdicCompletion I J (le_of_eq hIJ)
  let Ihat : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R))
  let Jhat : Ideal (AdicCompletion J S) := J.map (algebraMap S (AdicCompletion J S))
  let : TopologicalSpace (AdicCompletion I R) := Ihat.adicTopology
  let : TopologicalSpace (AdicCompletion J S) := Jhat.adicTopology
  have hcomp : fhat.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp (algebraMap R S) :=
    RingHom.ext fun x => Stacks.Nagata.PthRootDescent.mapAdicCompletion_of (le_of_eq hIJ) x
  have halg : I.map (algebraMap R S) = J := by
    rwa [RingHom.algebraMap_toAlgebra f]
  have hmap : Ihat.map fhat = Jhat := by
    dsimp only [Ihat, Jhat]
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, halg]
  exact ⟨Ihat, isAdic_adicTopology Ihat, hmap.symm ▸ isAdic_adicTopology Jhat⟩

/-- Extending an ideal along the two sides of a commuting square of ring homomorphisms gives the
same ideal. -/
private theorem map_map_eq_map_map
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (a : R →+* R') (b : S →+* S') (g : R' →+* S') (h : g.comp a = b.comp f)
    (I : Ideal R) : (I.map a).map g = (I.map f).map b := by
  rw [Ideal.map_map, Ideal.map_map, h]

/-- A ring has dense image in its adic completion along a finitely generated ideal. -/
public theorem denseRange_algebraMap_adicCompletion
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) :
    letI : TopologicalSpace (AdicCompletion I R) :=
      (I.map (algebraMap R (AdicCompletion I R))).adicTopology
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  let C := AdicCompletion I R
  let Ihat : Ideal C := I.map (algebraMap R C)
  let : TopologicalSpace C := Ihat.adicTopology
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  rw [mem_closure_iff_nhds_basis (Ihat.hasBasis_nhds_adic x)]
  intro n _
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R R))
    (AdicCompletion.eval I R n x)
  refine ⟨algebraMap R C r, ⟨r, rfl⟩, algebraMap R C r - x, ?_, by simp⟩
  have hpow : ((Ihat ^ n : Ideal C) : Set C) =
      ((I ^ n • (⊤ : Submodule R C) : Submodule R C) : Set C) := by
    dsimp only [Ihat]
    rw [← Ideal.map_pow, Ideal.smul_top_eq_map, Submodule.coe_restrictScalars]
  rw [hpow, AdicCompletion.pow_smul_top_eq_ker_eval hI]
  refine LinearMap.mem_ker.mpr ?_
  change AdicCompletion.eval I R n (AdicCompletion.of I R r - x) = 0
  rw [map_sub, AdicCompletion.eval_of]
  change (Submodule.Quotient.mk r : R ⧸ I ^ n • (⊤ : Submodule R R)) -
    AdicCompletion.eval I R n x = 0
  rw [hr]
  simp

/-- Topological finite type is inherited by the map of principal localizations induced by a
topologically finite type homomorphism. -/
public theorem isTopologicallyOfFiniteType_awayMap
    {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (I : Ideal B) (hI : IsAdic I) (a : A) :
    letI : TopologicalSpace (Localization.Away (φ a)) :=
      (I.map (algebraMap B (Localization.Away (φ a)))).adicTopology
    TopologicalRing.IsTopologicallyOfFiniteType
      (IsLocalization.Away.map (Localization.Away a) (Localization.Away (φ a)) φ a) := by
  obtain ⟨n, F, hFC, hFdense⟩ := hφ
  let L := Localization.Away a
  let S := Localization.Away (φ a)
  let : CommRing L := inferInstanceAs (CommRing (Localization.Away a))
  let : CommRing S := inferInstanceAs (CommRing (Localization.Away (φ a)))
  let J : Ideal S := I.map (algebraMap B S)
  let ψ : L →+* S := IsLocalization.Away.map L S φ a
  let g : B →+* S := algebraMap B S
  let c : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) L := MvPolynomial.map (algebraMap A L)
  let G : MvPolynomial (Fin n) L →+* S :=
    MvPolynomial.eval₂Hom ψ (fun i => g (F (MvPolynomial.X i)))
  let : TopologicalSpace S := J.adicTopology
  let : IsTopologicalRing S := J.ringFilterBasis.isTopologicalRing
  refine ⟨n, G, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, G, MvPolynomial.eval₂Hom_C]
    rfl
  · have hψx : ∀ x, ψ (algebraMap A L x) = g (φ x) := fun x => by
      simp [ψ, g, IsLocalization.Away.map, IsLocalization.map_eq]
    have hGF : G.comp c = g.comp F := by
      apply MvPolynomial.ringHom_ext
      · intro x
        change G (c (MvPolynomial.C x)) = g (F (MvPolynomial.C x))
        simp only [G, c, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
        rw [hψx]
        exact congrArg g (DFunLike.congr_fun hFC x).symm
      · intro i
        simp [G, c, g]
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.mpr
    intro y
    rw [mem_closure_iff_nhds_basis (J.hasBasis_nhds_adic y)]
    intro k _
    obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (φ a)) y
    obtain ⟨d, hd⟩ := m.property
    have hcl : b ∈ closure (Set.range F) := hFdense b
    rw [mem_closure_iff_nhds_basis (hI.hasBasis_nhds b)] at hcl
    obtain ⟨z, hzrange, hzb⟩ := hcl k trivial
    obtain ⟨p, hpz⟩ := hzrange
    have hzb' : F p ∈ (fun z => b + z) '' ((I ^ k : Ideal B) : Set B) := by
      simpa [hpz] using hzb
    obtain ⟨v, hv, hpv⟩ := hzb'
    have hdiff : F p - b ∈ (I ^ k : Ideal B) := by
      rw [← hpv]
      simpa using hv
    have hmap : g (F p - b) ∈ (J ^ k : Ideal S) := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap B S) hdiff
    let dA : L := algebraMap A L a
    let dB : S := algebraMap B S (φ a)
    have hdA : IsUnit dA := IsLocalization.map_units L ⟨a, Submonoid.mem_powers a⟩
    have hden : algebraMap B S (m : B) = dB ^ d := by
      simpa [dB, map_pow] using (congrArg (algebraMap B S) hd).symm
    have hψbase : ψ dA = dB := hψx a
    have hdAPow : IsUnit (dA ^ d) := hdA.pow d
    have hmUnit : IsUnit (algebraMap B S (m : B)) := IsLocalization.map_units S m
    have hψden : ψ (dA ^ d) = algebraMap B S (m : B) := by
      rw [map_pow, hψbase, hden.symm]
    have hunit : Units.map ψ.toMonoidHom hdAPow.unit = hmUnit.unit := Units.ext hψden
    let u : L := (hdAPow.unit⁻¹ : Lˣ)
    have hu : ψ u = (hmUnit.unit⁻¹ : Sˣ) :=
      (Units.coe_map ψ.toMonoidHom hdAPow.unit⁻¹).symm.trans
        (congrArg Units.val (by rw [map_inv, hunit]))
    have happrox : G (MvPolynomial.C u * c p) - y ∈ (J ^ k : Ideal S) := by
      have hGp : G (c p) = g (F p) := DFunLike.congr_fun hGF p
      rw [map_mul, MvPolynomial.eval₂Hom_C, hGp, hu]
      have hhm : y = g b * (hmUnit.unit⁻¹ : Sˣ) := by
        rw [← hm, mul_assoc, hmUnit.mul_val_inv, mul_one]
      rw [hhm]
      have hmul : (g (F p) - g b) * (hmUnit.unit⁻¹ : Sˣ) ∈ J ^ k :=
        Ideal.mul_mem_right _ _ (by simpa only [map_sub] using hmap)
      convert hmul using 1
      ring
    exact ⟨G (MvPolynomial.C u * c p), ⟨MvPolynomial.C u * c p, rfl⟩,
      ⟨G (MvPolynomial.C u * c p) - y, happrox, by simp⟩⟩

/-- Topological finite type passes to a map of adic completions compatible with the structure
maps. -/
private theorem isTopologicallyOfFiniteType_completion
    {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace S]
    (I : Ideal R) (J : Ideal S) (hJ : J.FG) (hJadic : IsAdic J)
    (f : R →+* S) (fhat : AdicCompletion I R →+* AdicCompletion J S)
    (hcomm : fhat.comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f)
    (hf : TopologicalRing.IsTopologicallyOfFiniteType f) :
    letI : TopologicalSpace (AdicCompletion J S) :=
      (J.map (algebraMap S (AdicCompletion J S))).adicTopology
    TopologicalRing.IsTopologicallyOfFiniteType fhat := by
  obtain ⟨n, F, hFC, hFdense⟩ := hf
  let Jhat : Ideal (AdicCompletion J S) := J.map (algebraMap S (AdicCompletion J S))
  let : TopologicalSpace (AdicCompletion J S) := Jhat.adicTopology
  let : Algebra (AdicCompletion I R) (AdicCompletion J S) := fhat.toAlgebra
  let c : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) (AdicCompletion I R) :=
    MvPolynomial.map (algebraMap R (AdicCompletion I R))
  let g : S →+* AdicCompletion J S := algebraMap S (AdicCompletion J S)
  let Fhat : MvPolynomial (Fin n) (AdicCompletion I R) →+* AdicCompletion J S :=
    MvPolynomial.eval₂Hom (algebraMap (AdicCompletion I R) (AdicCompletion J S))
      (fun i => g (F (MvPolynomial.X i)))
  refine ⟨n, Fhat, RingHom.ext fun a => ?_, ?_⟩
  · simp only [RingHom.comp_apply, Fhat, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra]
  · have hpoly : DenseRange (g ∘ F) :=
      (denseRange_algebraMap_adicCompletion J hJ).comp hFdense (by
        rw [hJadic]
        exact (RingHom.continuous_adic_iff g J Jhat).2
          ⟨1, le_rfl, fun x hx => Ideal.mem_map_of_mem g (by simpa only [pow_one] using hx)⟩)
    have hcomp : Fhat.comp c = g.comp F := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => by simp [Fhat, c, g])
      simp only [RingHom.comp_apply, Fhat, c, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C,
        RingHom.algebraMap_toAlgebra]
      exact (DFunLike.congr_fun hcomm a).trans (congrArg g (DFunLike.congr_fun hFC a).symm)
    exact (show DenseRange (Fhat ∘ c) from by
      simpa only [RingHom.coe_comp] using (hcomp ▸ hpoly : DenseRange ⇑(Fhat.comp c))).of_comp

/-! ### Flatness and faithful flatness of maps of principal localizations -/

/-- The map of principal localizations of `f` at `r` is, up to the equivalences induced by
`ULift.ringEquiv`, the map of principal localizations of the `ULift`ed homomorphism. -/
private theorem exists_ulift_awayMap_comp
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (Rloc Sloc : Type*) [CommRing Rloc] [CommRing Sloc] [Algebra R Rloc] [Algebra S Sloc]
    [IsLocalization.Away r Rloc] [IsLocalization.Away (f r) Sloc] :
    ∃ (eR : Localization.Away (ULift.up (α := R) r) ≃+* Rloc)
      (eS : Localization.Away ((RingHom.ulift f : ULift.{max u v} R →+* ULift.{max u v} S)
        (ULift.up r)) ≃+* Sloc),
      eS.toRingHom.comp (IsLocalization.Away.map (Localization.Away (ULift.up (α := R) r))
        (Localization.Away ((RingHom.ulift f : ULift.{max u v} R →+* ULift.{max u v} S)
          (ULift.up r))) (RingHom.ulift f : ULift.{max u v} R →+* ULift.{max u v} S)
          (ULift.up r)) =
        (IsLocalization.Away.map Rloc Sloc f r).comp eR.toRingHom := by
  let fU : ULift.{max u v} R →+* ULift.{max u v} S := RingHom.ulift f
  let rU := ULift.up (α := R) r
  have hR : (Submonoid.powers rU).map (ULift.ringEquiv : ULift.{max u v} R ≃+* R).toMonoidHom =
      Submonoid.powers r := by
    rw [Submonoid.map_powers]; rfl
  have hS : (Submonoid.powers (fU rU)).map
      (ULift.ringEquiv : ULift.{max u v} S ≃+* S).toMonoidHom = Submonoid.powers (f r) := by
    rw [Submonoid.map_powers]; rfl
  let eR : Localization.Away rU ≃+* Rloc :=
    IsLocalization.ringEquivOfRingEquiv _ _ (ULift.ringEquiv : ULift.{max u v} R ≃+* R) hR
  let eS : Localization.Away (fU rU) ≃+* Sloc :=
    IsLocalization.ringEquivOfRingEquiv _ _ (ULift.ringEquiv : ULift.{max u v} S ≃+* S) hS
  let gU := IsLocalization.Away.map (Localization.Away rU) (Localization.Away (fU rU)) fU rU
  let g := IsLocalization.Away.map Rloc Sloc f r
  refine ⟨eR, eS, ?_⟩
  refine IsLocalization.ringHom_ext (Submonoid.powers rU) (RingHom.ext fun x => ?_)
  have h₁ : gU (algebraMap _ (Localization.Away rU) x) =
      algebraMap _ (Localization.Away (fU rU)) (fU x) :=
    IsLocalization.map_eq _ x
  have h₄ : g (algebraMap R Rloc (ULift.ringEquiv x)) =
      algebraMap S Sloc (f (ULift.ringEquiv x)) :=
    IsLocalization.map_eq _ (ULift.ringEquiv x)
  calc eS (gU (algebraMap _ (Localization.Away rU) x)) =
        eS (algebraMap _ (Localization.Away (fU rU)) (fU x)) := congrArg eS h₁
    _ = algebraMap S Sloc (ULift.ringEquiv (fU x)) :=
      IsLocalization.ringEquivOfRingEquiv_eq hS (fU x)
    _ = algebraMap S Sloc (f (ULift.ringEquiv x)) := rfl
    _ = g (algebraMap R Rloc (ULift.ringEquiv x)) := h₄.symm
    _ = g (eR (algebraMap _ (Localization.Away rU) x)) :=
      congrArg g (IsLocalization.ringEquivOfRingEquiv_eq hR x).symm

/-- The map of principal localizations induced by a flat ring homomorphism is flat. -/
public theorem flat_awayMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (r : R) (hf : f.Flat) :
    (IsLocalization.Away.map (Localization.Away r) (Localization.Away (f r)) f r).Flat := by
  obtain ⟨eR, eS, hcomp⟩ :=
    exists_ulift_awayMap_comp f r (Localization.Away r) (Localization.Away (f r))
  let fU : ULift.{max u v} R →+* ULift.{max u v} S := RingHom.ulift f
  let rU := ULift.up (α := R) r
  have hgU : (IsLocalization.Away.map (Localization.Away rU) (Localization.Away (fU rU))
      fU rU).Flat :=
    RingHom.IsStableUnderBaseChange.isLocalization_map RingHom.Flat.isStableUnderBaseChange
      (Submonoid.powers rU) fU (RingHom.Flat.ulift_iff.mpr hf)
  have hcompFlat := hgU.comp (RingHom.Flat.of_bijective (f := eS.toRingHom) eS.bijective)
  rw [hcomp] at hcompFlat
  exact (RingHom.Flat.comp_iff_of_bijective_right eR.bijective).mp hcompFlat

/-- The map of principal localizations induced by a faithfully flat ring homomorphism is
faithfully flat. -/
private theorem faithfullyFlat_awayMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (Rloc : Type u) (Sloc : Type v) [CommRing Rloc] [CommRing Sloc]
    [Algebra R Rloc] [Algebra S Sloc] [IsLocalization.Away r Rloc]
    [IsLocalization.Away (f r) Sloc] (hf : f.FaithfullyFlat) :
    (IsLocalization.Away.map Rloc Sloc f r).FaithfullyFlat := by
  obtain ⟨eR, eS, hcomp⟩ := exists_ulift_awayMap_comp f r Rloc Sloc
  let fU : ULift.{max u v} R →+* ULift.{max u v} S := RingHom.ulift f
  let rU := ULift.up (α := R) r
  let g := IsLocalization.Away.map Rloc Sloc f r
  have hfU : fU.FaithfullyFlat := by
    have hRe : (ULift.ringEquiv : ULift.{max u v} R ≃+* R).toRingHom.FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective ULift.ringEquiv.bijective
    have hSe : (ULift.ringEquiv : ULift.{max u v} S ≃+* S).symm.toRingHom.FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective ULift.ringEquiv.symm.bijective
    exact RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.comp hRe hf) hSe
  have hgU : (IsLocalization.Away.map (Localization.Away rU) (Localization.Away (fU rU))
      fU rU).FaithfullyFlat :=
    RingHom.IsStableUnderBaseChange.isLocalization_map
      RingHom.FaithfullyFlat.isStableUnderBaseChange (Submonoid.powers rU) fU hfU
  have hcompFF := hgU.comp (RingHom.FaithfullyFlat.of_bijective (f := eS.toRingHom) eS.bijective)
  rw [hcomp] at hcompFF
  have hfinal := RingHom.FaithfullyFlat.comp
    (RingHom.FaithfullyFlat.of_bijective (f := eR.symm.toRingHom) eR.symm.bijective) hcompFF
  rwa [show (g.comp eR.toRingHom).comp eR.symm.toRingHom = g from by ext x; simp] at hfinal

/-! ### The descent lemma -/

namespace RingHom

/-- **Stacks 0GGT.** Rig-flatness descends in a commutative square of adic homomorphisms of
topological finite type between Noetherian weakly admissible rings whose lower horizontal map is
flat and whose upper horizontal map is faithfully flat: if `φ'` is rig-flat, so is `φ`. -/
@[stacks 0GGT]
public theorem isRigFlat_of_faithfullyFlat
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [IsNoetherianRing A] [IsNoetherianRing A'] [IsNoetherianRing B] [IsNoetherianRing B']
    (_hA : TopologicalRing.IsWeaklyAdmissible A) (_hA' : TopologicalRing.IsWeaklyAdmissible A')
    (_hB : TopologicalRing.IsWeaklyAdmissible B) (_hB' : TopologicalRing.IsWeaklyAdmissible B')
    (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (hcomm : β.comp φ = φ'.comp α)
    (_hφ_cont : Continuous φ) (_hα_cont : Continuous α)
    (_hβ_cont : Continuous β) (_hφ'_cont : Continuous φ')
    (hφ_adic : _root_.RingHom.IsAdic φ) (hα_adic : _root_.RingHom.IsAdic α)
    (_hβ_adic : _root_.RingHom.IsAdic β) (hφ'_adic : _root_.RingHom.IsAdic φ')
    (hφ_ft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (_hα_ft : TopologicalRing.IsTopologicallyOfFiniteType α)
    (_hβ_ft : TopologicalRing.IsTopologicallyOfFiniteType β)
    (_hφ'_ft : TopologicalRing.IsTopologicallyOfFiniteType φ')
    (hα_flat : α.Flat) (hβ_ff : β.FaithfullyFlat)
    (hφ'_rigFlat : Rig.RingHom.IsRigFlat φ') :
    Rig.RingHom.IsRigFlat φ := by
  obtain ⟨-, -, hφ'_local⟩ := hφ'_rigFlat
  refine ⟨hφ_adic, hφ_ft, ?_⟩
  intro I hI hIφ f
  have hIα : IsAdic (I.map α) := _root_.RingHom.isAdic_map_of_isAdic α hα_adic hI
  obtain ⟨-, -, hφhat'_flat⟩ := hφ'_local (I.map α) hIα
    (_root_.RingHom.isAdic_map_of_isAdic φ' hφ'_adic hIα) (α f)
  let A₀ := Localization.Away f
  let A₁ := Localization.Away (α f)
  let B₀ := Localization.Away (φ f)
  let B₁ := Localization.Away (φ' (α f))
  let I₀ : Ideal A₀ := I.map (algebraMap A A₀)
  let I₁ : Ideal A₁ := (I.map α).map (algebraMap A' A₁)
  let J₀ : Ideal B₀ := (I.map φ).map (algebraMap B B₀)
  let J₁ : Ideal B₁ := ((I.map α).map φ').map (algebraMap B' B₁)
  have hden : β (φ f) = φ' (α f) := DFunLike.congr_fun hcomm f
  let : IsLocalization.Away (β (φ f)) B₁ := by
    rw [hden]; infer_instance
  let α₀₁ : A₀ →+* A₁ := IsLocalization.Away.map A₀ A₁ α f
  let φ₀ : A₀ →+* B₀ := IsLocalization.Away.map A₀ B₀ φ f
  let β₀₁ : B₀ →+* B₁ := IsLocalization.Away.map B₀ B₁ β (φ f)
  let φ₁ : A₁ →+* B₁ := IsLocalization.Away.map A₁ B₁ φ' (α f)
  have hα₀₁base : α₀₁.comp (algebraMap A A₀) = (algebraMap A' A₁).comp α := by
    ext x; simp [α₀₁, IsLocalization.Away.map]
  have hφ₀base : φ₀.comp (algebraMap A A₀) = (algebraMap B B₀).comp φ := by
    ext x; simp [φ₀, IsLocalization.Away.map]
  have hβ₀₁base : β₀₁.comp (algebraMap B B₀) = (algebraMap B' B₁).comp β := by
    ext x; simp [β₀₁, IsLocalization.Away.map]
  have hφ₁base : φ₁.comp (algebraMap A' A₁) = (algebraMap B' B₁).comp φ' := by
    ext x; simp [φ₁, IsLocalization.Away.map]
  have hloc_comm : β₀₁.comp φ₀ = φ₁.comp α₀₁ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc _ _ β₀₁, hφ₀base, ← RingHom.comp_assoc _ _ β₀₁, hβ₀₁base,
      RingHom.comp_assoc _ _ (algebraMap B' B₁), hcomm, RingHom.comp_assoc _ _ φ₁, hα₀₁base,
      ← RingHom.comp_assoc _ _ φ₁, hφ₁base, RingHom.comp_assoc]
  have hI₀₁ : I₀.map α₀₁ = I₁ := map_map_eq_map_map α _ _ _ hα₀₁base I
  have hI₀φ : I₀.map φ₀ = J₀ := map_map_eq_map_map φ _ _ _ hφ₀base I
  have hJ₀₁ : J₀.map β₀₁ = J₁ := by
    rw [map_map_eq_map_map β _ _ _ hβ₀₁base, Ideal.map_map φ β, hcomm, ← Ideal.map_map]
  have hI₁φ : I₁.map φ₁ = J₁ := map_map_eq_map_map φ' _ _ _ hφ₁base (I.map α)
  let C₀ := AdicCompletion I₀ A₀
  let C₁ := AdicCompletion I₁ A₁
  let D₀ := AdicCompletion J₀ B₀
  let D₁ := AdicCompletion J₁ B₁
  let I₀hat : Ideal C₀ := I₀.map (algebraMap A₀ C₀)
  let I₁hat : Ideal C₁ := I₁.map (algebraMap A₁ C₁)
  let J₀hat : Ideal D₀ := J₀.map (algebraMap B₀ D₀)
  let J₁hat : Ideal D₁ := J₁.map (algebraMap B₁ D₁)
  let : TopologicalSpace C₀ := I₀hat.adicTopology
  let : TopologicalSpace C₁ := I₁hat.adicTopology
  let : TopologicalSpace D₀ := J₀hat.adicTopology
  let : TopologicalSpace D₁ := J₁hat.adicTopology
  let : IsTopologicalRing C₀ := I₀hat.ringFilterBasis.isTopologicalRing
  let : IsTopologicalRing C₁ := I₁hat.ringFilterBasis.isTopologicalRing
  let : IsTopologicalRing D₀ := J₀hat.ringFilterBasis.isTopologicalRing
  let : IsTopologicalRing D₁ := J₁hat.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C₀ C₀ := I₀hat.isLinearTopology
  let : IsLinearTopology C₁ C₁ := I₁hat.isLinearTopology
  let : IsLinearTopology D₀ D₀ := J₀hat.isLinearTopology
  let : IsLinearTopology D₁ D₁ := J₁hat.isLinearTopology
  let : Algebra A₀ A₁ := α₀₁.toAlgebra
  let : Algebra A₀ B₀ := φ₀.toAlgebra
  let : Algebra B₀ B₁ := β₀₁.toAlgebra
  let : Algebra A₁ B₁ := φ₁.toAlgebra
  let αhat : C₀ →+* C₁ := Stacks.Nagata.PthRootDescent.mapAdicCompletion I₀ I₁ (le_of_eq hI₀₁)
  let φhat : C₀ →+* D₀ := Stacks.Nagata.PthRootDescent.mapAdicCompletion I₀ J₀ (le_of_eq hI₀φ)
  let βhat : D₀ →+* D₁ := Stacks.Nagata.PthRootDescent.mapAdicCompletion J₀ J₁ (le_of_eq hJ₀₁)
  let φhat' : C₁ →+* D₁ := Stacks.Nagata.PthRootDescent.mapAdicCompletion I₁ J₁ (le_of_eq hI₁φ)
  have hαhat_adic : _root_.RingHom.IsAdic αhat := isAdic_mapAdicCompletion α₀₁ I₀ I₁ hI₀₁
  have hαhat_flat : αhat.Flat :=
    flat_mapAdicCompletion_of_eq I₀ I₁ hI₀₁ (flat_awayMap α f hα_flat)
  have hβhat_ff : βhat.FaithfullyFlat :=
    faithfullyFlat_mapAdicCompletion_of_eq J₀ J₁ hJ₀₁
      (faithfullyFlat_awayMap β (φ f) B₀ B₁ hβ_ff)
  have hφhat_adic : _root_.RingHom.IsAdic φhat := isAdic_mapAdicCompletion φ₀ I₀ J₀ hI₀φ
  let : TopologicalSpace A₀ := I₀.adicTopology
  let : TopologicalSpace B₀ := J₀.adicTopology
  have hφhat_ft : TopologicalRing.IsTopologicallyOfFiniteType φhat :=
    isTopologicallyOfFiniteType_completion I₀ J₀ J₀.fg_of_isNoetherianRing
      (isAdic_adicTopology J₀) φ₀ φhat
      (RingHom.ext fun a => Stacks.Nagata.PthRootDescent.mapAdicCompletion_of (le_of_eq hI₀φ) a)
      (isTopologicallyOfFiniteType_awayMap φ hφ_ft (I.map φ) hIφ f)
  have hhat_comm : βhat.comp φhat = φhat'.comp αhat := by
    refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I₀ n x)
    dsimp only [βhat, φhat, φhat', αhat, RingHom.comp_apply]
    rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion,
      Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion,
      Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion,
        Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion, ← ha]
    simp only [Ideal.quotientMap_mk]
    exact congrArg (Ideal.Quotient.mk (J₁ ^ n)) (DFunLike.congr_fun hloc_comm a)
  refine ⟨hφhat_adic, hφhat_ft, ?_⟩
  intro x hx
  have hright := hφhat'_flat (αhat x)
    (IsTopologicallyNilpotent.map (continuous_of_isAdic αhat hαhat_adic) hx)
  refine flat_of_faithfullyFlat_square
    ((algebraMap D₀ (Localization.Away (φhat x))).comp φhat) αhat
    (IsLocalization.Away.map (Localization.Away (φhat x))
      (Localization.Away (βhat (φhat x))) βhat (φhat x))
    ((algebraMap D₁ (Localization.Away (βhat (φhat x)))).comp φhat') ?_ hαhat_flat
    (faithfullyFlat_awayMap βhat (φhat x) (Localization.Away (φhat x))
      (Localization.Away (βhat (φhat x))) hβhat_ff) ?_
  · refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]
    exact congrArg (algebraMap D₁ (Localization.Away (βhat (φhat x))))
      (DFunLike.congr_fun hhat_comm y)
  · rw [show βhat (φhat x) = φhat' (αhat x) from DFunLike.congr_fun hhat_comm x,
      show φhat' = Rig.RingHom.completedAwayMap φ' (I.map α) (α f) from rfl]
    exact hright

end RingHom

end Rig

end
