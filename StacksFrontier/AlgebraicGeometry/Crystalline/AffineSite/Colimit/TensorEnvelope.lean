module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.CategoryTheory.Limits.Finite.NonemptyColimits
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Nonempty finite colimits in the affine crystalline site

Let `(A, I, γ) → C` be an affine crystalline situation.  This file shows that the category
`CRIS(C/A)` of divided power thickenings of `C` over `(A, I, γ)` has all colimits indexed by a
nonempty finite category, that these colimits are computed on quotients by the divided power
ideal, and that the same holds for the full subcategory `Cris(C/A)` of thickenings whose
quotient is `C` itself.

The two generating cases are a binary coproduct and a coequalizer.  A coproduct of `X` and `Y`
is built by pushing out the two thickenings along the image of the base in `X × Y`, and then
taking the divided power envelope of the kernel of the map to `B_X/J_X ⊗_C B_Y/J_Y`; its
quotient is that tensor product, which is the coproduct of the quotients.  A coequalizer is
built from the coequalizer of the underlying rings followed by the divided power envelope of
the image of the divided power ideal.  Together these give all nonempty finite colimits.  The
quotient functor is a left adjoint — its right adjoint equips a `C`-algebra with the zero
ideal — hence preserves them; and since a thickening in the image of a nonempty finite colimit
of objects of `Cris(C/A)` again has quotient `C`, the subcategory inherits the colimits and
its inclusion preserves them.

## Main results

* `Crystalline.binaryCoproductWithTensorProductQuotient` — a binary coproduct in `CRIS(C/A)`
  whose quotient is the tensor product over `C` of the two quotients.
* `Crystalline.exists_coequalizer_with_quotient` — a coequalizer in `CRIS(C/A)` whose image
  under the quotient functor is a coequalizer of `C`-algebras.
* `Crystalline.hasNonemptyFiniteColimits_dividedPowerThickening` — `CRIS(C/A)` has all
  nonempty finite colimits.
* `Crystalline.preservesColimitsOfShape_quotientFunctor` — the quotient functor preserves
  them.
* `Crystalline.DividedPowerThickening.instHasNonemptyFiniteColimits` and
  `Crystalline.preservesColimitsOfShape_crystallineThickeningInclusion` — `Cris(C/A)` has
  them too, and the inclusion into `CRIS(C/A)` preserves them.

## References

* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Crystalline

section BinaryCoproduct

lemma envelope_ext
    (A : DividedPowerRing.{u}) {B : Type u} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (E : DividedPowerEnvelope A f J hJ) (Q : DividedPowerRing.{u})
    (a : DividedPowers.DPMorphism A.dividedPowers Q.dividedPowers)
    (q₁ q₂ : DividedPowers.DPMorphism E.object.dividedPowers Q.dividedPowers)
    (h₁ : q₁.comp E.structureMap = a) (h₂ : q₂.comp E.structureMap = a)
    (heq : q₁.toRingHom.comp E.algebraMap.toRingHom =
      q₂.toRingHom.comp E.algebraMap.toRingHom) : q₁ = q₂ := by
  have hEq : E.homEquiv Q a ⟨q₁, h₁⟩ = E.homEquiv Q a ⟨q₂, h₂⟩ := by
    apply Subtype.ext
    rw [E.homEquiv_apply, E.homEquiv_apply]
    exact IdealPair.Hom.ext_toRingHom _ _ heq
  exact congrArg Subtype.val ((E.homEquiv Q a).injective hEq)

lemma baseImageKerStable
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    S.A.dividedPowers.IsSubDPIdeal
      (RingHom.ker (X.fromBase.toRingHom.prod Y.fromBase.toRingHom).rangeRestrict ⊓
        S.A.ideal) := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  show S.A.dividedPowers.IsSubDPIdeal (RingHom.ker ψ ⊓ S.A.ideal)
  refine ⟨inf_le_right, ?_⟩
  intro n hn a ha
  have hφ : φ a = 0 := Subtype.ext_iff.mp (RingHom.mem_ker.mp ha.1)
  have key : ∀ Z : DividedPowerThickening.{u, v, w} S, Z.fromBase a = 0 →
      Z.fromBase (S.A.dividedPowers.dpow n a) = 0 := fun Z hz =>
    (Z.fromBase.dpow_comp a ha.2).symm.trans
      (by rw [show Z.fromBase.toRingHom a = 0 from hz, Z.ring.dividedPowers.dpow_eval_zero hn])
  have hdx := key X (congrArg Prod.fst hφ)
  have hdy := key Y (congrArg Prod.snd hφ)
  exact ⟨RingHom.mem_ker.mpr (Subtype.ext (Prod.ext hdx hdy)), S.A.dividedPowers.dpow_mem hn ha.2⟩

noncomputable def baseImage
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) : DividedPowerRing.{w} := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  have hker := baseImageKerStable X Y
  exact { carrier := φ.range
          ideal := S.A.ideal.map ψ
          dividedPowers := DividedPowers.Quotient.OfSurjective.dividedPowers
            S.A.dividedPowers φ.rangeRestrict_surjective rfl hker }

noncomputable def baseToImage
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    DividedPowers.DPMorphism S.A.dividedPowers (baseImage X Y).dividedPowers := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  refine { toRingHom := ψ
           ideal_comp := ?_
           dpow_comp := ?_ }
  · exact le_rfl
  · intro n a ha
    exact (DividedPowers.Quotient.OfSurjective.dpow_apply
      S.A.dividedPowers φ.rangeRestrict_surjective rfl
      (baseImageKerStable X Y) ha)

noncomputable def baseImageToLeft
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    baseImage X Y ⟶ X.ring := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  let π : (baseImage X Y) →+* X.ring :=
    (RingHom.fst X.ring Y.ring).comp (Subring.subtype φ.range)
  refine { toRingHom := π
           ideal_comp := ?_
           dpow_comp := ?_ }
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hxp : x ∈ S.A.ideal.map ψ := hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective ψ φ.rangeRestrict_surjective).mp hxp
    change X.fromBase a ∈ X.ring.ideal
    exact X.fromBase.ideal_comp (Ideal.mem_map_of_mem X.fromBase.toRingHom ha)
  · intro n x hx
    have hxp : x ∈ S.A.ideal.map ψ := hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective ψ φ.rangeRestrict_surjective).mp hxp
    have hdp := (baseToImage X Y).dpow_comp a ha (n := n)
    change (baseImage X Y).dividedPowers.dpow n (ψ a) =
      ψ (S.A.dividedPowers.dpow n a) at hdp
    rw [hdp]
    exact X.fromBase.dpow_comp a ha

noncomputable def baseImageToRight
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    baseImage X Y ⟶ Y.ring := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  let π : (baseImage X Y) →+* Y.ring :=
    (RingHom.snd X.ring Y.ring).comp (Subring.subtype φ.range)
  refine { toRingHom := π
           ideal_comp := ?_
           dpow_comp := ?_ }
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hxp : x ∈ S.A.ideal.map ψ := hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective ψ φ.rangeRestrict_surjective).mp hxp
    change Y.fromBase a ∈ Y.ring.ideal
    exact Y.fromBase.ideal_comp (Ideal.mem_map_of_mem Y.fromBase.toRingHom ha)
  · intro n x hx
    have hxp : x ∈ S.A.ideal.map ψ := hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective ψ φ.rangeRestrict_surjective).mp hxp
    have hdp := (baseToImage X Y).dpow_comp a ha (n := n)
    change (baseImage X Y).dividedPowers.dpow n (ψ a) =
      ψ (S.A.dividedPowers.dpow n a) at hdp
    rw [hdp]
    exact Y.fromBase.dpow_comp a ha

lemma baseToImage_left
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    (baseImageToLeft X Y).comp (baseToImage X Y) = X.fromBase := by
  ext x
  rfl

lemma baseToImage_right
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    (baseImageToRight X Y).comp (baseToImage X Y) = Y.fromBase := by
  ext x
  rfl

lemma baseToImage_surjective
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    Function.Surjective (baseToImage X Y) := by
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  exact φ.rangeRestrict_surjective

noncomputable def imagePushout
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) : DividedPowerRing.{w} :=
  pushout (baseImageToLeft X Y) (baseImageToRight X Y)

/-- The base map of a thickening is compatible with the structure map to its quotient. -/
private lemma quotient_mk_fromBase {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S) (a : S.A) :
    Ideal.Quotient.mk X.ring.ideal (X.fromBase a) = X.toQuotient (algebraMap S.A S.C a) :=
  congrArg (fun h : S.A →+* (X.ring ⧸ X.ring.ideal) => h a) X.commutes

lemma baseImage_quotient_balanced
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (Algebra.TensorProduct.includeLeftRingHom (R := S.C)
      (A := X.ring ⧸ X.ring.ideal) (B := Y.ring ⧸ Y.ring.ideal)).comp
        (DividedPowerRing.quotientRingHom (baseImageToLeft X Y)) =
    (Algebra.TensorProduct.includeRight (R := S.C)
      (A := X.ring ⧸ X.ring.ideal) (B := Y.ring ⧸ Y.ring.ideal)).toRingHom.comp
        (DividedPowerRing.quotientRingHom (baseImageToRight X Y)) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  let φ : S.A →+* X.ring × Y.ring :=
    X.fromBase.toRingHom.prod Y.fromBase.toRingHom
  let ψ : S.A →+* φ.range := φ.rangeRestrict
  apply Ideal.Quotient.ringHom_ext
  ext x
  obtain ⟨a, rfl⟩ := φ.rangeRestrict_surjective x
  show (Ideal.Quotient.mk X.ring.ideal (X.fromBase a)) ⊗ₜ[S.C]
      (1 : Y.ring ⧸ Y.ring.ideal) =
    (1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C]
      (Ideal.Quotient.mk Y.ring.ideal (Y.fromBase a))
  rw [quotient_mk_fromBase X a, quotient_mk_fromBase Y a]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap S.A S.C a)

noncomputable abbrev zeroDividedPowerRing (R : Type w) [CommRing R] :
    DividedPowerRing.{w} :=
  { carrier := R, ideal := ⊥, dividedPowers := dividedPowersBot R }

noncomputable def imagePushoutToTensor
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    imagePushout X Y ⟶
      zeroDividedPowerRing
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  let T := (X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)
  let Q : DividedPowerRing.{w} :=
    { carrier := T, ideal := ⊥, dividedPowers := dividedPowersBot T }
  let l : X.ring →+* T :=
    (Algebra.TensorProduct.includeLeftRingHom (R := S.C)).comp
      (Ideal.Quotient.mk X.ring.ideal)
  let r : Y.ring →+* T :=
    (Algebra.TensorProduct.includeRight (R := S.C)).toRingHom.comp
      (Ideal.Quotient.mk Y.ring.ideal)
  have hl : ∀ x ∈ X.ring.ideal, l x = 0 := fun x hx => by
    simp [l, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hr : ∀ x ∈ Y.ring.ideal, r x = 0 := fun x hx => by
    simp [r, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  let fl : X.ring ⟶ Q := dpMorphismToBot X.ring.dividedPowers l hl
  let fr : Y.ring ⟶ Q := dpMorphismToBot Y.ring.dividedPowers r hr
  have h : baseImageToLeft X Y ≫ fl = baseImageToRight X Y ≫ fr := by
    ext x
    have hb := congrArg (fun f => f (Ideal.Quotient.mk (baseImage X Y).ideal x))
      (baseImage_quotient_balanced X Y)
    exact hb
  exact pushout.desc fl fr h

lemma pushoutDescLeft
    {A B C D : DividedPowerRing.{w}} (f : A ⟶ B) (g : A ⟶ C)
    (h : B ⟶ D) (k : C ⟶ D) (e : f ≫ h = g ≫ k) (x : B) :
    (pushout.desc h k e) ((pushout.inl f g) x) = h x :=
  congrArg (fun m : B ⟶ D => m x) (pushout.inl_desc h k e)

lemma pushoutDescRight
    {A B C D : DividedPowerRing.{w}} (f : A ⟶ B) (g : A ⟶ C)
    (h : B ⟶ D) (k : C ⟶ D) (e : f ≫ h = g ≫ k) (x : C) :
    (pushout.desc h k e) ((pushout.inr f g) x) = k x :=
  congrArg (fun m : C ⟶ D => m x) (pushout.inr_desc h k e)

lemma imagePushoutToTensor_left
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (x : X.ring) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (imagePushoutToTensor X Y)
      ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) x) =
      (Ideal.Quotient.mk X.ring.ideal x) ⊗ₜ[S.C]
        (1 : Y.ring ⧸ Y.ring.ideal) := by
  unfold imagePushoutToTensor
  exact pushoutDescLeft _ _ _ _ _ x

lemma imagePushoutToTensor_right
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (y : Y.ring) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (imagePushoutToTensor X Y)
      ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) y) =
      (1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C]
        (Ideal.Quotient.mk Y.ring.ideal y) := by
  unfold imagePushoutToTensor
  exact pushoutDescRight _ _ _ _ _ y

lemma imagePushoutToTensor_surjective
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    Function.Surjective (imagePushoutToTensor X Y) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (imagePushoutToTensor X Y).toRingHom.map_zero⟩
  | tmul x y =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    let a' : imagePushout X Y :=
      (pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) a
    let b' : imagePushout X Y :=
      (pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) b
    refine ⟨a' * b', ?_⟩
    have hl : (imagePushoutToTensor X Y).toRingHom a' =
        (Ideal.Quotient.mk X.ring.ideal a) ⊗ₜ[S.C]
          (1 : Y.ring ⧸ Y.ring.ideal) := imagePushoutToTensor_left X Y a
    have hr : (imagePushoutToTensor X Y).toRingHom b' =
        (1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C]
          (Ideal.Quotient.mk Y.ring.ideal b) := imagePushoutToTensor_right X Y b
    show (imagePushoutToTensor X Y).toRingHom (a' * b') = _
    rw [map_mul, hl, hr]
    simp
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', (imagePushoutToTensor X Y).toRingHom.map_add a' b'⟩

noncomputable def imageToPushout
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    baseImage X Y ⟶ imagePushout X Y :=
  baseImageToLeft X Y ≫
    pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)

noncomputable def tensorEnvelope
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    DividedPowerEnvelope (imagePushout X Y) (RingHom.id _)
      (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (by
        rw [Ideal.map_id, RingHom.ker_eq_comap_bot]
        exact Ideal.map_le_iff_le_comap.mp
          (imagePushoutToTensor X Y).ideal_comp) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  exact dividedPowerEnvelope (imagePushout X Y) (RingHom.id _)
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (by
      rw [Ideal.map_id, RingHom.ker_eq_comap_bot]
      exact Ideal.map_le_iff_le_comap.mp
        (imagePushoutToTensor X Y).ideal_comp)

noncomputable def tensorEnvelopeQuotientEquiv
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    ((tensorEnvelope X Y).object ⧸ (tensorEnvelope X Y).object.ideal) ≃+*
      (X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  exact (envelopeQuotientEquiv (A := imagePushout X Y) (RingHom.id _)
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (by
      rw [Ideal.map_id, RingHom.ker_eq_comap_bot]
      exact Ideal.map_le_iff_le_comap.mp
        (imagePushoutToTensor X Y).ideal_comp) (tensorEnvelope X Y)).1.trans
    (RingHom.quotientKerEquivOfSurjective
      (imagePushoutToTensor_surjective X Y))

private lemma envelopeQuotientEquiv_apply_structureMap
    (A : DividedPowerRing.{w}) (J : Ideal A)
    (hJ : A.ideal.map (RingHom.id A) ≤ J)
    (E : DividedPowerEnvelope A (RingHom.id A) J hJ) (a : A) :
    (envelopeQuotientEquiv (A := A) (RingHom.id A) J hJ E).1
      (Ideal.Quotient.mk E.object.ideal (E.structureMap a)) =
      Ideal.Quotient.mk J a := by
  have halg := congrArg (fun f : A →+* E.object => f a) E.algebraMap_comp
  change E.algebraMap.toRingHom a = E.structureMap.toRingHom a at halg
  have hx := (envelopeQuotientEquiv (A := A) (RingHom.id A) J hJ E).2 a
  rwa [halg] at hx

lemma envelopeStructureQuotient_surjective
    (A : DividedPowerRing.{w}) (J : Ideal A)
    (hJ : A.ideal.map (RingHom.id A) ≤ J)
    (E : DividedPowerEnvelope A (RingHom.id A) J hJ) :
    Function.Surjective
      ((Ideal.Quotient.mk E.object.ideal).comp E.structureMap.toRingHom) := by
  intro z
  let e := (envelopeQuotientEquiv (A := A) (RingHom.id A) J hJ E).1
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e z)
  refine ⟨a, e.injective ?_⟩
  show e (Ideal.Quotient.mk E.object.ideal (E.structureMap a)) = e z
  rw [envelopeQuotientEquiv_apply_structureMap, ha]

lemma tensorEnvelopeQuotientEquiv_apply_structureMap
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (p : imagePushout X Y) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    tensorEnvelopeQuotientEquiv X Y
      (Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal
        ((tensorEnvelope X Y).structureMap p)) =
      (imagePushoutToTensor X Y) p := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  unfold tensorEnvelopeQuotientEquiv
  rw [RingEquiv.trans_apply, envelopeQuotientEquiv_apply_structureMap,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

lemma imagePushoutToTensor_base
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (a : S.A) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (imagePushoutToTensor X Y)
      ((imageToPushout X Y) ((baseToImage X Y) a)) =
      algebraMap S.C ((X.ring ⧸ X.ring.ideal) ⊗[S.C]
        (Y.ring ⧸ Y.ring.ideal)) (algebraMap S.A S.C a) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  show (imagePushoutToTensor X Y)
    ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y))
      ((baseImageToLeft X Y) ((baseToImage X Y) a))) = _
  have hbase := congrArg
    (fun f : DividedPowers.DPMorphism S.A.dividedPowers X.ring.dividedPowers => f a)
      (baseToImage_left X Y)
  change (baseImageToLeft X Y) ((baseToImage X Y) a) = X.fromBase a at hbase
  rw [hbase, imagePushoutToTensor_left X Y, quotient_mk_fromBase X a]
  rfl

end BinaryCoproduct

end Crystalline
