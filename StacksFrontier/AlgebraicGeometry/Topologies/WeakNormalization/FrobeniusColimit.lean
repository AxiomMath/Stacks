module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AbsolutelyWeaklyNormalPerfect
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.RingCharacterization
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Frobenius colimit is the absolute weak normalization

Let `p` be a prime number and `A` an algebra over `ZMod p`. The colimit of the sequence
`A → A → A → ⋯` whose every transition map is the Frobenius endomorphism is canonically the
absolute weak normalization of `A`.

## Main definitions

* `Algebra.frobeniusEndomorphism` is the Frobenius endomorphism of an algebra over `ZMod p`,
  defined also when the algebra is trivial.
* `Algebra.frobeniusDiagram` is the sequential diagram of commutative rings all of whose
  transition maps are Frobenius.

## Main results

* `Algebra.existsUnique_frobeniusColimit_iso_absoluteWeakNormalization`: the colimit of that
  diagram is isomorphic to `Algebra.AbsoluteWeakNormalization A` by a unique isomorphism
  compatible with the canonical maps out of `A`.

## References

* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EVV](https://stacks.math.columbia.edu/tag/0EVV)
* [Stacks Project, Tag 0BRA](https://stacks.math.columbia.edu/tag/0BRA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Algebra

/-! ### The Frobenius sequence -/

/-- The Frobenius endomorphism of an algebra over `ZMod p`, taking `p`-th powers. It is defined
for the trivial algebra too, where `CharP A p` fails. -/
@[ega "0 21.1.4"]
def frobeniusEndomorphism (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]
    [Algebra (ZMod p) A] : A →+* A := by
  classical
  by_cases h : Nontrivial A
  · have _ : Nontrivial A := h
    have _ : CharP A p := charP_of_injective_ringHom (algebraMap (ZMod p) A).injective p
    exact frobenius A p
  · have _ : Subsingleton A := not_nontrivial_iff_subsingleton.mp h
    exact { toFun := fun a => a ^ p
            map_one' := by subsingleton
            map_mul' := by intros; subsingleton
            map_zero' := by subsingleton
            map_add' := by intros; subsingleton }

/-- The Frobenius endomorphism is the `p`-th power map. -/
@[ega "0 21.1.4"]
theorem frobeniusEndomorphism_apply (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]
    [Algebra (ZMod p) A] (a : A) : frobeniusEndomorphism p A a = a ^ p := by
  classical
  by_cases h : Nontrivial A
  · have _ : Nontrivial A := h
    have _ : CharP A p := charP_of_injective_ringHom (algebraMap (ZMod p) A).injective p
    simp [frobeniusEndomorphism, h, frobenius_def]
  · simp [frobeniusEndomorphism, h]

/-- The sequential diagram `A → A → ⋯` of commutative rings with all transition maps given by
the Frobenius endomorphism. -/
def frobeniusDiagram (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (X := fun _ => CommRingCat.of A)
    fun _ => CommRingCat.ofHom (frobeniusEndomorphism p A)

variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A]

/-- The cocone on the Frobenius diagram whose leg at `n` is the colimit leg at `n + 1`. -/
private def frobeniusShiftCocone : Cocone (frobeniusDiagram p A) where
  pt := colimit (frobeniusDiagram p A)
  ι :=
    { app := fun n => colimit.ι (frobeniusDiagram p A) (Nat.succ n)
      naturality := fun _ _ f =>
        colimit.w (frobeniusDiagram p A) (homOfLE (Nat.succ_le_succ (leOfHom f))) }

/-- The forgetful functor to types preserves the colimit of the Frobenius diagram. -/
theorem frobeniusDiagram_forget_preservesColimit :
    PreservesColimit (frobeniusDiagram p A) (forget CommRingCat.{u}) := by
  let D := frobeniusDiagram p A
  let c := CommRingCat.FilteredColimits.colimitCocone.{0, u} D
  have hc : IsColimit c := CommRingCat.FilteredColimits.colimitCoconeIsColimit.{0, u} D
  have hcF : IsColimit ((forget CommRingCat.{u}).mapCocone c) := by
    change IsColimit (Types.TypeMax.colimitCocone (D ⋙ forget CommRingCat.{u}))
    exact Types.TypeMax.colimitCoconeIsColimit (D ⋙ forget CommRingCat.{u})
  exact preservesColimit_of_preserves_colimit_cocone hc hcF

/-- Each successive transition map of the Frobenius diagram is the Frobenius endomorphism. -/
private theorem frobeniusDiagram_map_succ (n : ℕ) :
    (frobeniusDiagram p A).map (homOfLE (Nat.le_succ n)) =
      CommRingCat.ofHom (frobeniusEndomorphism p A) := by
  change (Functor.ofSequence (X := fun _ => CommRingCat.of A)
    fun _ => CommRingCat.ofHom (frobeniusEndomorphism p A)).map _ = _
  rw [Functor.ofSequence_map_homOfLE_succ]

/-- Moving along one step of the Frobenius diagram raises the representative to the `p`-th
power. -/
private theorem frobeniusColimit_ι_succ (n : ℕ) (a : A) :
    colimit.ι (frobeniusDiagram p A) n a =
      colimit.ι (frobeniusDiagram p A) (Nat.succ n) (a ^ p) := by
  let D := frobeniusDiagram p A
  have h := colimit.w D (homOfLE (Nat.le_succ n))
  rw [frobeniusDiagram_map_succ] at h
  have h' : (colimit.ι D (Nat.succ n)).hom.comp (frobeniusEndomorphism p A) =
      (colimit.ι D n).hom := congrArg CommRingCat.Hom.hom h
  have h'' := congrArg (fun f : A →+* ↑(colimit D) => f a) h'
  change (colimit.ι D (Nat.succ n)).hom (frobeniusEndomorphism p A a) =
    (colimit.ι D n).hom a at h''
  exact h''.symm.trans
    (congrArg (colimit.ι D (Nat.succ n)).hom (frobeniusEndomorphism_apply p A a))

/-- The transition map of the Frobenius diagram from index `0` to index `n` is the `pⁿ`-th
power map. -/
theorem frobeniusDiagram_map_zero_apply (n : ℕ) (a : A) :
    (frobeniusDiagram p A).map (homOfLE (Nat.zero_le n)) a = a ^ p ^ n := by
  induction n generalizing a with
  | zero =>
      change a = a ^ p ^ 0
      simp
  | succ n ih =>
      let D := frobeniusDiagram p A
      have hfactor : homOfLE (Nat.zero_le (Nat.succ n)) =
          homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_succ n) := by subsingleton
      have hmap : D.map (homOfLE (Nat.zero_le (Nat.succ n))) =
          D.map (homOfLE (Nat.zero_le n)) ≫ CommRingCat.ofHom (frobeniusEndomorphism p A) := by
        calc
          _ = D.map (homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_succ n)) := by rw [hfactor]
          _ = D.map (homOfLE (Nat.zero_le n)) ≫ D.map (homOfLE (Nat.le_succ n)) := by
            rw [Functor.map_comp]
          _ = _ := by rw [frobeniusDiagram_map_succ]; rfl
      have hval' := by
        simpa only [CategoryTheory.ConcreteCategory.comp_apply] using
          CategoryTheory.ConcreteCategory.congr_hom hmap (show ↑(D.obj 0) from a)
      change ((D.map (homOfLE (Nat.zero_le (Nat.succ n)))).hom) a =
        frobeniusEndomorphism p A (((D.map (homOfLE (Nat.zero_le n))).hom) a) at hval'
      rw [ih, frobeniusEndomorphism_apply, ← pow_mul, ← Nat.pow_succ] at hval'
      simpa [D] using hval'

/-- An element of `A` seen at index `n` of the Frobenius diagram is its `pⁿ`-th power seen at
index `0`. -/
theorem frobeniusColimit_ι_zero_pow (n : ℕ) (a : A) :
    colimit.ι (frobeniusDiagram p A) 0 a =
      colimit.ι (frobeniusDiagram p A) n (a ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        colimit.ι (frobeniusDiagram p A) 0 a =
            colimit.ι (frobeniusDiagram p A) n (a ^ p ^ n) := ih
        _ = colimit.ι (frobeniusDiagram p A) (Nat.succ n) ((a ^ p ^ n) ^ p) :=
            frobeniusColimit_ι_succ p A n (a ^ p ^ n)
        _ = colimit.ι (frobeniusDiagram p A) (Nat.succ n) (a ^ p ^ Nat.succ n) := by
            congr 1
            rw [← pow_mul, Nat.pow_succ]

/-- The `pⁿ`-th power of an element seen at index `n` of the Frobenius diagram is the element seen
at index `0`. -/
private theorem frobeniusColimit_ι_pow_eq (n : ℕ) (a : A) :
    (colimit.ι (frobeniusDiagram p A) n).hom a ^ p ^ n =
      (colimit.ι (frobeniusDiagram p A) 0).hom a := by
  exact (map_pow (colimit.ι (frobeniusDiagram p A) n).hom a (p ^ n)).symm.trans
    (frobeniusColimit_ι_zero_pow p A n a).symm

/-- Every element of the Frobenius colimit comes from some index. -/
theorem frobeniusColimit_exists_rep (x : ↑(colimit (frobeniusDiagram p A))) :
    ∃ n : ℕ, ∃ a : A, colimit.ι (frobeniusDiagram p A) n a = x := by
  have _ : PreservesColimit (frobeniusDiagram p A) (forget CommRingCat.{u}) :=
    frobeniusDiagram_forget_preservesColimit p A
  obtain ⟨n, _, a, rfl⟩ := CategoryTheory.Limits.Concrete.exists_hom_ι_eq_of_isColimit
    (frobeniusDiagram p A) (colimit.isColimit _) x 0
  exact ⟨n, a, rfl⟩

/-- The `p`-th power map is bijective on the Frobenius colimit. -/
private theorem frobeniusColimit_pow_bijective :
    Function.Bijective fun x : ↑(colimit (frobeniusDiagram p A)) => x ^ p := by
  let D := frobeniusDiagram p A
  let G : colimit D ⟶ colimit D := (colimit.isColimit D).desc (frobeniusShiftCocone p A)
  have hG_apply (n : ℕ) (a : A) :
      G.hom (colimit.ι D n a) = colimit.ι D (Nat.succ n) a := by
    have h' : G.hom.comp (colimit.ι D n).hom = (colimit.ι D (Nat.succ n)).hom :=
      congrArg CommRingCat.Hom.hom ((colimit.isColimit D).fac (frobeniusShiftCocone p A) n)
    exact congrArg (fun f : A →+* ↑(colimit D) => f a) h'
  have hleft (x : ↑(colimit D)) : G.hom (x ^ p) = x := by
    obtain ⟨n, a, rfl⟩ := frobeniusColimit_exists_rep p A x
    calc
      G.hom ((colimit.ι D n).hom a ^ p) = G.hom ((colimit.ι D n).hom (a ^ p)) :=
        congrArg G.hom (map_pow (colimit.ι D n).hom a p).symm
      _ = (colimit.ι D (Nat.succ n)).hom (a ^ p) := hG_apply n (a ^ p)
      _ = (colimit.ι D n).hom a := (frobeniusColimit_ι_succ p A n a).symm
  have hright (x : ↑(colimit D)) : (G.hom x) ^ p = x := by
    obtain ⟨n, a, rfl⟩ := frobeniusColimit_exists_rep p A x
    calc
      (G.hom ((colimit.ι D n).hom a)) ^ p = (colimit.ι D (Nat.succ n)).hom a ^ p := by
        rw [hG_apply]
      _ = (colimit.ι D (Nat.succ n)).hom (a ^ p) :=
        (map_pow (colimit.ι D (Nat.succ n)).hom a p).symm
      _ = (colimit.ι D n).hom a := (frobeniusColimit_ι_succ p A n a).symm
  exact Function.bijective_iff_has_inverse.mpr ⟨G.hom, hleft, hright⟩

/-! ### Identification with the absolute weak normalization -/

open PrimeSpectrum in
/-- For `p` prime and `A` an algebra over `ZMod p`, the colimit of the Frobenius sequence of `A`
is the absolute weak normalization of `A`, by a unique isomorphism compatible with the canonical
maps out of `A`. -/
@[stacks 0EVW "frobenius_colimit"]
theorem existsUnique_frobeniusColimit_iso_absoluteWeakNormalization
    (p : ℕ) (hp : p.Prime) (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    letI : Fact p.Prime := ⟨hp⟩
    ∃! e : colimit (frobeniusDiagram p A) ≅
        CommRingCat.of (AbsoluteWeakNormalization A),
      colimit.ι (frobeniusDiagram p A) 0 ≫ e.hom =
        CommRingCat.ofHom (algebraMap A (AbsoluteWeakNormalization A)) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let D := frobeniusDiagram p A
  let C : Type u := ↑(colimit D)
  let _ : _root_.Algebra A C := RingHom.toAlgebra (colimit.ι D 0).hom
  let _ : _root_.Algebra (ZMod p) C :=
    RingHom.toAlgebra ((algebraMap A C).comp (algebraMap (ZMod p) A))
  have _ : PreservesColimit D (forget CommRingCat.{u}) :=
    frobeniusDiagram_forget_preservesColimit p A
  have hker : RingHom.ker (algebraMap A C) ≤ nilradical A := by
    intro a ha
    rw [mem_nilradical]
    have ha' : colimit.ι D 0 a = 0 := by
      change (algebraMap A C) a = 0
      exact RingHom.mem_ker.mp ha
    have ha'' : colimit.ι D 0 a = colimit.ι D 0 0 := by simpa using ha'
    obtain ⟨k, f, g, hfg⟩ := CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq D a 0 ha''
    rw [Subsingleton.elim f (homOfLE (Nat.zero_le k)),
      Subsingleton.elim g (homOfLE (Nat.zero_le k))] at hfg
    refine ⟨p ^ k, ?_⟩
    rw [frobeniusDiagram_map_zero_apply p A k a] at hfg
    rw [show (D.map (homOfLE (Nat.zero_le k))).hom 0 = 0 from map_zero _] at hfg
    exact hfg
  have hpzero : (p : C) = 0 := by
    have hpA : (p : A) = 0 := by
      rw [show (p : A) = algebraMap (ZMod p) A (p : ZMod p) from (map_natCast _ p).symm,
        CharP.cast_eq_zero (ZMod p) p, map_zero]
    rw [show (p : C) = algebraMap A C (p : A) by simp, hpA, map_zero]
  have hgen : _root_.Algebra.adjoin A {x : C | ∃ n > 0, x ^ p ^ n ∈ (algebraMap A C).range ∧
      p ^ n • x ∈ (algebraMap A C).range} = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨m, a, rfl⟩ := frobeniusColimit_exists_rep p A x
    have hxpow : (colimit.ι D m).hom a ^ p ^ m = algebraMap A C a :=
      frobeniusColimit_ι_pow_eq p A m a
    have hxpow' : (colimit.ι D m).hom a ^ p ^ (m + 1) = algebraMap A C (a ^ p) := by
      calc
        _ = ((colimit.ι D m).hom a ^ p ^ m) ^ p := by rw [Nat.pow_succ, pow_mul]
        _ = _ := by rw [hxpow, map_pow]
    have hsmul : p ^ (m + 1) • (colimit.ι D m).hom a = 0 := by
      simp [nsmul_eq_mul, Nat.cast_pow, hpzero]
    apply _root_.Algebra.subset_adjoin
    exact ⟨m + 1, Nat.succ_pos m, ⟨a ^ p, hxpow'.symm⟩,
      ⟨0, by simpa [nsmul_eq_mul] using hsmul.symm⟩⟩
  have hspec :=
    isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top.{u, u, u, u}
      (R := A) (S := C) p hp hker hgen
  have hawn : IsAbsolutelyWeaklyNormalRing C :=
    (isAbsolutelyWeaklyNormalRing_iff_perfectRing p hp C).2
      ⟨frobeniusColimit_pow_bijective p A⟩
  let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A C))
  have hfhomeo : IsHomeomorph f := hspec.1
  have hringIntegral : (algebraMap A C).IsIntegral := by
    intro x
    obtain ⟨n, a, rfl⟩ := frobeniusColimit_exists_rep p A x
    have hxpow : (colimit.ι D n).hom a ^ p ^ n = algebraMap A C a :=
      frobeniusColimit_ι_pow_eq p A n a
    exact IsIntegral.of_pow (pow_pos hp.pos n) (hxpow ▸ isIntegral_algebraMap)
  have hfIntegral : IsIntegralHom f :=
    (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom (algebraMap A C))).2 hringIntegral
  let U : Type u := ULift.{u, u} C
  let T : Type u := TensorProduct A U C
  let _ : _root_.Algebra U T := _root_.Algebra.TensorProduct.leftAlgebra
  let _ : _root_.Algebra C T := _root_.Algebra.TensorProduct.rightAlgebra
  have _ : _root_.Algebra.IsPushout A C U T := TensorProduct.isPushout'
  obtain ⟨hkerT, hgenT⟩ := hspec.2.2 U T
  have hspecT :=
    isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top.{u, u, u, u}
      (R := U) (S := T) p hp hkerT hgenT
  let fU : Spec (CommRingCat.of U) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A U))
  let eRing : CommRingCat.of U ≅ CommRingCat.of C :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv (R := C) : U ≃+* C)
  let eSpec : Spec (CommRingCat.of C) ≅ Spec (CommRingCat.of U) := Scheme.Spec.mapIso eRing.op
  have hecomp : eSpec.hom ≫ fU = f := by
    change Spec.map eRing.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A U)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C))
    rw [← Spec.map_comp]
    congr 1
  have heinv : eSpec.inv ≫ f = fU := by
    calc
      eSpec.inv ≫ f = eSpec.inv ≫ (eSpec.hom ≫ fU) := by rw [← hecomp]
      _ = fU := by simp
  let ePull := AlgebraicGeometry.pullbackSpecIso A U C
  have hleft : Function.Injective (pullback.fst fU f) := by
    have hmap : Function.Injective (Spec.map (CommRingCat.ofHom
        (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (A := U) (B := C)))) := by
      change Function.Injective (PrimeSpectrum.comap (algebraMap U T))
      exact hspecT.1.injective
    intro x y hxy
    refine (Scheme.homeoOfIso ePull).injective (hmap ?_)
    have hs := AlgebraicGeometry.pullbackSpecIso_hom_fst A U C
    have hpt (z : ↑(pullback fU f)) : Spec.map (CommRingCat.ofHom
        (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (A := U) (B := C)))
          (ePull.hom z) = pullback.fst fU f z := by
      simpa only [fU, f, ePull, Scheme.Hom.comp_apply] using congrArg (fun g => g z) hs
    exact (hpt x).trans (hxy.trans (hpt y).symm)
  let pHom := pullback.map f f fU f eSpec.hom (𝟙 _) (𝟙 _) hecomp.symm (by simp)
  let pInv := pullback.map fU f f f eSpec.inv (𝟙 _) (𝟙 _) heinv.symm (by simp)
  have pHomFst : pHom ≫ pullback.fst fU f = pullback.fst f f ≫ eSpec.hom := by
    dsimp [pHom, pullback.map]
    rw [pullback.lift_fst]
  have pHomSnd : pHom ≫ pullback.snd fU f = pullback.snd f f := by
    dsimp [pHom, pullback.map]
    rw [pullback.lift_snd]
    simp
  have pInvFst : pInv ≫ pullback.fst f f = pullback.fst fU f ≫ eSpec.inv := by
    dsimp [pInv, pullback.map]
    rw [pullback.lift_fst]
  have pInvSnd : pInv ≫ pullback.snd f f = pullback.snd fU f := by
    dsimp [pInv, pullback.map]
    rw [pullback.lift_snd]
    simp
  let ePullback : pullback f f ≅ pullback fU f :=
    { hom := pHom
      inv := pInv
      hom_inv_id := by
        refine pullback.hom_ext ?_ ?_
        · calc
            pHom ≫ pInv ≫ pullback.fst f f = (pHom ≫ pullback.fst fU f) ≫ eSpec.inv := by
              rw [pInvFst, ← Category.assoc]
            _ = (pullback.fst f f ≫ eSpec.hom) ≫ eSpec.inv := by rw [pHomFst]
            _ = pullback.fst f f := by simp [Category.assoc]
        · calc
            pHom ≫ pInv ≫ pullback.snd f f = pHom ≫ pullback.snd fU f := by rw [pInvSnd]
            _ = pullback.snd f f := pHomSnd
      inv_hom_id := by
        refine pullback.hom_ext ?_ ?_
        · calc
            pInv ≫ pHom ≫ pullback.fst fU f = (pInv ≫ pullback.fst f f) ≫ eSpec.hom := by
              rw [pHomFst, ← Category.assoc]
            _ = (pullback.fst fU f ≫ eSpec.inv) ≫ eSpec.hom := by rw [pInvFst]
            _ = pullback.fst fU f := by simp [Category.assoc]
        · calc
            pInv ≫ pHom ≫ pullback.snd fU f = pInv ≫ pullback.snd f f := by rw [pHomSnd]
            _ = pullback.snd fU f := pInvSnd }
  have hfstSelf : Function.Injective (pullback.fst f f) := by
    intro x y hxy
    refine (Scheme.homeoOfIso ePullback).injective (hleft ?_)
    have hproj (z : ↑(pullback f f)) :
        pullback.fst fU f ((Scheme.homeoOfIso ePullback) z) = eSpec.hom (pullback.fst f f z) := by
      rw [Scheme.homeoOfIso_apply]
      change (pHom ≫ pullback.fst fU f) z = _
      rw [pHomFst, Scheme.Hom.comp_apply]
    rw [hproj x, hproj y, hxy]
  have hUI : UniversallyInjective f := by
    refine (UniversallyInjective.iff_diagonal f).2 ⟨fun z => ⟨pullback.fst f f z, ?_⟩⟩
    refine hfstSelf ?_
    change (pullback.diagonal f ≫ pullback.fst f f) (pullback.fst f f z) = pullback.fst f f z
    rw [pullback.diagonal_fst]
    rfl
  have hsurj : Surjective f := ⟨hfhomeo.surjective⟩
  have huniv : UniversalHomeomorphism f :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
      ⟨hfIntegral, hUI, hsurj⟩
  let CObj : AbsoluteWeakNormalizationCategory A := ⟨CommAlgCat.of A C, huniv⟩
  let term := absoluteWeakNormalizationCandidate_isTerminal A
  let m := term.from CObj
  have hmIso : IsIso m :=
    (isIso_toAbsoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing A C huniv).2 hawn
  let e : CommRingCat.of C ≅ CommRingCat.of (AbsoluteWeakNormalization A) :=
    (forget₂ (CommAlgCat A) CommRingCat).mapIso
      ((ObjectProperty.ι (IsAbsoluteWeakNormalizationCandidate A)).mapIso (asIso m))
  have heCompat : colimit.ι D 0 ≫ e.hom =
      CommRingCat.ofHom (algebraMap A (AbsoluteWeakNormalization A)) := by
    apply CommRingCat.hom_ext
    ext a
    exact m.hom.hom.commutes' a
  refine ⟨e, heCompat, fun e' he' ↦ ?_⟩
  let hm' : CObj ⟶ absoluteWeakNormalizationCandidate A := by
    refine ⟨CommAlgCat.ofHom { toRingHom := e'.hom.hom, commutes' := ?_ }⟩
    intro a
    have h := congrArg (fun g : CommRingCat.of A ⟶
      CommRingCat.of (AbsoluteWeakNormalization A) => g a) he'
    change e'.hom.hom ((colimit.ι D 0).hom a) = _ at h
    exact h
  have hterm : hm' = m := term.hom_ext _ _
  exact Iso.ext (CommRingCat.hom_ext
    (congrArg (fun q : CObj ⟶ absoluteWeakNormalizationCandidate A =>
      q.hom.hom.toRingHom) hterm))

end Algebra

end
