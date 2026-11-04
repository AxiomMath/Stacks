module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.Koszul.Defs
import StacksFrontier.RingTheory.Koszul.ExteriorBasisMatrix

@[expose] public noncomputable section

/-!
# The extended alternating Čech complex as a colimit of Koszul complexes

For a finite sequence in a commutative ring, the extended alternating Čech complex is the
filtered colimit of the Koszul complexes on the positive powers of that sequence, regraded so that
the `q`-th exterior power of a sequence of length `r` sits in cohomological degree `r - q`. The
transition map fixes a standard exterior-basis vector up to multiplication by the product of the
sequence entries whose indices do not occur in that vector.

## Main definitions

* `Cech.koszulRegradingFunctor` reflects a nonnegative chain complex about `r` to get a
  nonnegative cochain complex.
* `Cech.koszulPowerCochainComplex` places a Koszul complex on positive powers in the
  cohomological degrees used by the extended alternating Čech complex.
* `Cech.koszulRegradeHom` is the canonical identification of an exterior-power term with
  the corresponding term of the regraded complex.
* `Cech.koszulPowerDiagram` packages chosen successor maps as a sequential diagram.

## Main results

* `Cech.cechComplex_isColimit_koszulPowerComplexes` identifies the extended alternating
  Čech complex with the colimit of these regraded Koszul complexes.

## References

* [The Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ExteriorAlgebra

attribute [local instance 2000] OreLocalization.instAddCommGroup
  OreLocalization.instAddCommMonoidOreLocalization

namespace Cech

universe u v

/-- Regrade a nonnegative chain complex as a nonnegative cochain complex whose degrees are
reflected about `r`. -/
public noncomputable abbrev koszulRegradingFunctor (R : Type u) [CommRing R] (r : ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R) ⋙
    shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-(r : ℤ)) ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor (ModuleCat.{u} R)

/-- The Koszul complex on the `(n + 1)`-st powers of `f`, regraded so that its top exterior
power is in cohomological degree zero and its zeroth exterior power is in degree `r`. -/
public noncomputable abbrev koszulPowerCochainComplex
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (koszulRegradingFunctor R r).obj
    (Koszul.seqComplex (fun i ↦ f i ^ (n + 1)))

/-- The canonical identification of the degree-`q` term of a Koszul complex with degree `p` of
its cohomological regrading, when `p + q = r`. -/
public noncomputable abbrev koszulRegradeHom
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).X q ⟶
      (koszulPowerCochainComplex f n).X p :=
  ((Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).extendXIso
      ComplexShape.embeddingDownNat rfl).inv ≫
    eqToHom (by
      subst r
      simp [koszulPowerCochainComplex])

/-- The sequential diagram of regraded Koszul complexes associated to chosen transition maps. -/
public noncomputable abbrev koszulPowerDiagram
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (σ : ∀ n : ℕ,
      Koszul.seqComplex (fun i ↦ f i ^ (n + 1)) ⟶
        Koszul.seqComplex (fun i ↦ f i ^ (n + 2))) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  Functor.ofSequence (fun n ↦ (koszulRegradingFunctor R r).map (σ n))

private abbrev exteriorBasis (R : Type u) [CommRing R] (r q : ℕ) :
    Module.Basis {s : Finset (Fin r) // s.card = q} R (⋀[R]^q (Fin r → R)) :=
  (Pi.basisFun R (Fin r)).exteriorPower q

private lemma exteriorBasis_apply {R : Type u} [CommRing R] {r q : ℕ}
    (s : {s : Finset (Fin r) // s.card = q}) :
    exteriorBasis R r q s =
      ⟨ExteriorAlgebra.ιMulti R q (fun k ↦ Pi.single (s.1.orderEmbOfFin s.2 k) 1),
        Koszul.ιMulti_mem q _⟩ := by
  show (Pi.basisFun R (Fin r)).exteriorPower q
    (⟨s.1, s.2⟩ : Set.powersetCard (Fin r) q) = _
  rw [exteriorPower.basis_apply]
  apply Subtype.ext
  simp [exteriorPower.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    Function.comp_def, Pi.basisFun_apply]

private alias orderEmbOfFin_erase := Koszul.orderEmbOfFin_erase

private abbrev eraseIndex {r q : ℕ} (s : {s : Finset (Fin r) // s.card = q + 1})
    (k : Fin (q + 1)) : {s : Finset (Fin r) // s.card = q} :=
  ⟨s.1.erase (s.1.orderEmbOfFin s.2 k), by
    rw [Finset.card_erase_of_mem (s.1.orderEmbOfFin_mem s.2 k), s.2]
    omega⟩

private lemma d_exteriorBasis {R : Type u} [CommRing R] {r q : ℕ}
    (φ : Module.Dual R (Fin r → R)) (s : {s : Finset (Fin r) // s.card = q + 1}) :
    Koszul.d φ q (exteriorBasis R r (q + 1) s) =
      ∑ k : Fin (q + 1),
        ((-1 : R) ^ k.val * φ (Pi.single (s.1.orderEmbOfFin s.2 k) 1)) •
          exteriorBasis R r q (eraseIndex s k) := by
  apply Subtype.ext
  simp only [exteriorBasis_apply, Koszul.d_apply_coe,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  rw [Koszul.contraction_ιMulti]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  funext j
  dsimp only [Function.comp_apply, eraseIndex]
  rw [orderEmbOfFin_erase]
  rfl

private lemma prod_compl_erase {α R : Type*} [Fintype α] [DecidableEq α]
    [CommMonoid R] (g : α → R) (s : Finset α) {i : α} (hi : i ∈ s) :
    (∏ j ∈ (s.erase i)ᶜ, g j) = g i * ∏ j ∈ sᶜ, g j := by
  rw [Finset.compl_erase, Finset.prod_insert (by simpa)]

private def complementProductMap {R : Type u} [CommRing R] {r : ℕ}
    (g : Fin r → R) (q : ℕ) : (⋀[R]^q (Fin r → R)) →ₗ[R] (⋀[R]^q (Fin r → R)) :=
  (exteriorBasis R r q).constr R
    (fun s ↦ (∏ i ∈ s.1ᶜ, g i) • exteriorBasis R r q s)

private lemma complementProductMap_basis {R : Type u} [CommRing R] {r : ℕ}
    (g : Fin r → R) (q : ℕ) (s : {s : Finset (Fin r) // s.card = q}) :
    complementProductMap g q (exteriorBasis R r q s) =
      (∏ i ∈ s.1ᶜ, g i) • exteriorBasis R r q s :=
  Module.Basis.constr_basis _ _ _ _

private lemma complementProductMap_comm {R : Type u} [CommRing R] {r : ℕ}
    (f g : Fin r → R) (q : ℕ) :
    (Koszul.d (Koszul.seqDual (fun i ↦ f i * g i)) q).comp
        (complementProductMap g (q + 1)) =
      (complementProductMap g q).comp (Koszul.d (Koszul.seqDual f) q) := by
  apply (exteriorBasis R r (q + 1)).ext
  intro s
  simp only [LinearMap.comp_apply, complementProductMap_basis, map_smul,
    d_exteriorBasis, Koszul.seqDual_single, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [eraseIndex]
  rw [prod_compl_erase g s.1 (s.1.orderEmbOfFin_mem s.2 k)]
  congr 1
  ring

private def powerTransition {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    Koszul.seqComplex (fun i ↦ f i ^ (n + 1)) ⟶
      Koszul.seqComplex (fun i ↦ f i ^ (n + 2)) where
  f q := ModuleCat.ofHom (complementProductMap f q)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [Koszul.seqComplex_d, Koszul.seqComplex_d]
    apply ModuleCat.hom_ext
    change (Koszul.d _ j).comp (complementProductMap f (j + 1)) =
      (complementProductMap f j).comp (Koszul.d _ j)
    simpa only [pow_succ] using complementProductMap_comm (fun i ↦ f i ^ (n + 1)) f j

private lemma powerTransition_basis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n q : ℕ) (s : {s : Finset (Fin r) // s.card = q}) :
    (powerTransition f n).f q (exteriorBasis R r q s) =
      (∏ i ∈ s.1ᶜ, f i) • exteriorBasis R r q s :=
  complementProductMap_basis f q s

private abbrev degreeIso {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).X q ≅
      (koszulPowerCochainComplex f n).X p :=
  ((Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).extendXIso
    ComplexShape.embeddingDownNat (show -(q : ℤ) = (p : ℤ) + -(r : ℤ) by omega)).symm

private lemma extendXIso_inv_eq {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] {I J : Type*} {c : ComplexShape I} {d : ComplexShape J}
    (K : HomologicalComplex C c) (e : c.Embedding d) (i : I) (j : J) (h : e.f i = j) :
    (K.extendXIso e h).inv = (K.extendXIso e (rfl : e.f i = e.f i)).inv ≫
      eqToHom (congrArg (K.extend e).X h) := by
  subst j
  simp

private lemma degreeIso_eq {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (degreeIso f n p q h).hom = koszulRegradeHom f n p q h :=
  extendXIso_inv_eq _ _ _ _ (by change -(q : ℤ) = (p : ℤ) + -(r : ℤ); omega)

private lemma degreeIso_d {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + (q + 1) = r) :
    (degreeIso f n p (q + 1) h).hom ≫
        (koszulPowerCochainComplex f n).d p (p + 1) =
      ((-1 : ℤ) ^ r) • (ModuleCat.ofHom (Koszul.d (Koszul.seqDual
        (fun i ↦ f i ^ (n + 1))) q) ≫
          (degreeIso f n (p + 1) q (by omega)).hom) := by
  show _ ≫ ((-(r : ℤ)).negOnePow •
    ((Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).extend
      ComplexShape.embeddingDownNat).d ((p : ℤ) + -(r : ℤ)) (↑(p + 1) + -(r : ℤ))) = _
  rw [HomologicalComplex.extend_d_eq _ _
    (show -(↑(q + 1) : ℤ) = (p : ℤ) + -(r : ℤ) by omega)
    (show -(q : ℤ) = (↑(p + 1) : ℤ) + -(r : ℤ) by omega)]
  simp only [degreeIso, Iso.symm_hom, Units.smul_def, Preadditive.comp_zsmul,
    Iso.inv_hom_id_assoc, Koszul.seqComplex_d, Int.negOnePow_neg,
    Int.coe_negOnePow_natCast]

private lemma degreeIso_transition {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (degreeIso f n p q h).hom ≫
      ((koszulRegradingFunctor R r).map (powerTransition f n)).f p =
    (powerTransition f n).f q ≫ (degreeIso f (n + 1) p q h).hom := by
  show _ ≫ (HomologicalComplex.extendMap _ _).f _ = _
  rw [HomologicalComplex.extendMap_f _ _
    (show -(q : ℤ) = (p : ℤ) + -(r : ℤ) by omega)]
  simp only [degreeIso, Iso.symm_hom, Iso.inv_hom_id_assoc]

private lemma isZero_degree {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (h : r < p) :
    IsZero ((koszulPowerCochainComplex f n).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro q
  show -(q : ℤ) ≠ (p : ℤ) + -(r : ℤ)
  omega

private alias card_filter_orderEmb := Koszul.card_filter_orderEmbOfFin

private lemma card_filter_compl {r : ℕ} (s : Finset (Fin r)) (i : Fin r) :
    (s.filter (· < i)).card + (sᶜ.filter (· < i)).card = i.val := by
  rw [← Finset.card_union_of_disjoint]
  · rw [← Finset.filter_union, Finset.union_compl]
    convert Fin.card_Iio i using 2
    ext j
    simp
  · exact Finset.disjoint_filter_filter disjoint_compl_right

private abbrev orientation {R : Type*} [CommRing R] {r : ℕ} (s : Finset (Fin r)) : R :=
  (-1 : R) ^ ((∑ i ∈ s, i.val) + r * s.card)

private lemma orientation_insert {R : Type*} [CommRing R] {r : ℕ}
    (s : Finset (Fin r)) (i : Fin r) (hi : i ∉ s) :
    ((-1 : R) ^ r * (-1 : R) ^ (sᶜ.filter (· < i)).card) *
      orientation (R := R) (insert i s) =
      (Cech.cechSign s i : R) * orientation s := by
  have hc := card_filter_compl s i
  simp only [orientation, Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
    Cech.cechSign, Int.cast_pow, Int.cast_neg, Int.cast_one, ← pow_add]
  have he : r + (sᶜ.filter (· < i)).card +
        (i.val + (∑ j ∈ s, j.val) + r * (s.card + 1)) =
      (s.filter (· < i)).card + ((∑ j ∈ s, j.val) + r * s.card) +
        2 * (r + (sᶜ.filter (· < i)).card) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [he, pow_add, pow_mul]
  simp

private abbrev fraction {R : Type*} [CommRing R] (g x : R) (n : ℕ) :
    LocalizedModule (Submonoid.powers g) R :=
  LocalizedModule.mk x ⟨g ^ n, n, rfl⟩

private lemma fraction_smul {R : Type*} [CommRing R] (g a x : R) (n : ℕ) :
    a • fraction g x n = fraction g (a * x) n :=
  LocalizedModule.smul'_mk a x _

private lemma fraction_cancel {R : Type*} [CommRing R] (g x : R) (n : ℕ) :
    g ^ n • fraction g x n = LocalizedModule.mkLinearMap (Submonoid.powers g) R x := by
  rw [fraction_smul]
  exact LocalizedModule.mk_cancel (S := Submonoid.powers g) ⟨g ^ n, n, rfl⟩ x

private lemma cechι_fraction {R : Type*} [CommRing R] {r : ℕ}
    (f : Fin r → R) (s : Finset (Fin r)) (i : Fin r) (hi : i ∉ s) (x : R) (n : ℕ) :
    Cech.cechι f R (Finset.subset_insert i s) (fraction (∏ j ∈ s, f j) x n) =
      fraction (∏ j ∈ insert i s, f j) (f i ^ n * x) n := by
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap
    (Cech.cechSub f (insert i s)) R)
    (⟨(∏ j ∈ insert i s, f j) ^ n, n, rfl⟩ : Cech.cechSub f (insert i s))
  show (∏ j ∈ insert i s, f j) ^ n •
    Cech.cechι f R (Finset.subset_insert i s) (fraction (∏ j ∈ s, f j) x n) =
    (∏ j ∈ insert i s, f j) ^ n • fraction (∏ j ∈ insert i s, f j) (f i ^ n * x) n
  rw [fraction_cancel]
  conv_lhs => rw [Finset.prod_insert hi, mul_pow, mul_smul,
    ← map_smul, fraction_cancel, Cech.cechι_mk, ← map_smul]
  rfl

private abbrev complementIndex {r p q : ℕ} (h : p + q = r)
    (s : {s : Finset (Fin r) // s.card = q}) : {t : Finset (Fin r) // t.card = p} :=
  ⟨s.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, s.2]; omega⟩

/-- The generator of the `t`-th summand of the Čech term given by `x / (∏ i ∈ t, f i) ^ (n + 1)`. -/
private abbrev cechFraction {R : Type u} [CommRing R] {r p : ℕ} (f : Fin r → R) (n : ℕ)
    (t : {t : Finset (Fin r) // t.card = p}) (x : R) : Cech.cechTerm f R p :=
  DirectSum.lof R _ (fun t ↦ Cech.cechMod f R t.1) t (fraction (∏ i ∈ t.1, f i) x (n + 1))

private def localizeExterior {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (⋀[R]^q (Fin r → R)) →ₗ[R] Cech.cechTerm f R p :=
  (exteriorBasis R r q).constr R (fun s ↦ cechFraction f n (complementIndex h s) (orientation s.1ᶜ))

private lemma localizeExterior_basis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r)
    (s : {s : Finset (Fin r) // s.card = q}) :
    localizeExterior f n p q h (exteriorBasis R r q s) =
      cechFraction f n (complementIndex h s) (orientation s.1ᶜ) :=
  Module.Basis.constr_basis _ _ _ _

private lemma localizeExterior_d {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + (q + 1) = r) :
    (Cech.cechD f R p).comp (localizeExterior f n p (q + 1) h) =
      (-1 : R) ^ r • ((localizeExterior f n (p + 1) q (by omega)).comp
        (Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (n + 1))) q)) := by
  apply (exteriorBasis R r (q + 1)).ext
  intro s
  simp only [LinearMap.comp_apply, localizeExterior_basis,
    LinearMap.smul_apply, d_exteriorBasis, Koszul.seqDual_single, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Cech.cechD_lof f R p (complementIndex h s)]
  symm
  dsimp only [complementIndex]
  refine Finset.sum_bij
    (fun k _ ↦ ⟨s.1.orderEmbOfFin s.2 k, by simp⟩)
    (by simp) ?_ ?_ ?_
  · intro a _ b _ hab
    apply (s.1.orderEmbOfFin s.2).injective
    exact congrArg (fun b : ↥(s.1ᶜᶜ) ↦ (b.1 : Fin r)) hab
  · intro b _
    have hb : b.1 ∈ s.1 := by simpa using b.2
    obtain ⟨k, hk⟩ := (s.1.orderIsoOfFin s.2).surjective ⟨b.1, hb⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Subtype.ext (congrArg (fun b : ↥s.1 ↦ (b.1 : Fin r)) hk)
  intro k _
  have hi := s.1.orderEmbOfFin_mem s.2 k
  have hin : s.1.orderEmbOfFin s.2 k ∉ s.1ᶜ := by simp
  rw [cechι_fraction f s.1ᶜ _ hin]
  dsimp only [eraseIndex]
  simp only [Finset.compl_erase]
  rw [← map_smul, fraction_smul, ← Int.cast_smul_eq_zsmul R,
    ← map_smul, fraction_smul]
  have hs := orientation_insert (R := R) s.1ᶜ (s.1.orderEmbOfFin s.2 k) hin
  simp only [compl_compl, card_filter_orderEmb s.1 s.2 k] at hs
  have he : (-1 : R) ^ r * ((-1 : R) ^ k.val * f (s.1.orderEmbOfFin s.2 k) ^ (n + 1)) *
        orientation (insert (s.1.orderEmbOfFin s.2 k) s.1ᶜ) =
      (Cech.cechSign s.1ᶜ (s.1.orderEmbOfFin s.2 k) : R) *
        (f (s.1.orderEmbOfFin s.2 k) ^ (n + 1) * orientation s.1ᶜ) := by
    calc
      _ = f (s.1.orderEmbOfFin s.2 k) ^ (n + 1) *
        (((-1 : R) ^ r * (-1 : R) ^ k.val) *
          orientation (insert (s.1.orderEmbOfFin s.2 k) s.1ᶜ)) := by ring
      _ = _ := by rw [hs]; ring
  rw [he]

private lemma fraction_succ {R : Type*} [CommRing R] (g x : R) (n : ℕ) :
    g • fraction g x (n + 1) = fraction g x n := by
  rw [fraction_smul]
  have he : (⟨g ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers g) =
      ⟨g, 1, pow_one g⟩ * ⟨g ^ n, n, rfl⟩ :=
    Subtype.ext (pow_succ' g n)
  show LocalizedModule.mk (S := Submonoid.powers g) (g * x)
    ⟨g ^ (n + 1), n + 1, rfl⟩ = _
  rw [he]
  exact LocalizedModule.mk_cancel_common_left
    (⟨g, 1, pow_one g⟩ : Submonoid.powers g) ⟨g ^ n, n, rfl⟩ x

/-- Multiplying by the denominator base lowers the exponent of a Čech generator by one. -/
private lemma prod_smul_cechFraction {R : Type u} [CommRing R] {r p : ℕ} (f : Fin r → R) (n : ℕ)
    (t : {t : Finset (Fin r) // t.card = p}) (x : R) :
    (∏ i ∈ t.1, f i) • cechFraction f (n + 1) t x = cechFraction f n t x := by
  rw [← map_smul, fraction_succ]

private lemma localizeExterior_transition {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (localizeExterior f (n + 1) p q h).comp (complementProductMap f q) =
      localizeExterior f n p q h := by
  apply (exteriorBasis R r q).ext
  intro s
  simp only [LinearMap.comp_apply, complementProductMap_basis, map_smul,
    localizeExterior_basis]
  exact prod_smul_cechFraction f n (complementIndex h s) _

private def cechLegComponent {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) :
    (koszulPowerCochainComplex f n).X p ⟶ (Cech.cechComplex f R).X p :=
  if h : p ≤ r then
    (degreeIso f n p (r - p) (by omega)).inv ≫
      ModuleCat.ofHom (localizeExterior f n p (r - p) (by omega))
  else 0

private lemma cechLegComponent_degreeIso {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r) :
    (degreeIso f n p q h).hom ≫ cechLegComponent f n p =
      ModuleCat.ofHom (localizeExterior f n p q h) := by
  have hp : p ≤ r := by omega
  have hq : r - p = q := by omega
  subst q
  simp only [cechLegComponent, dite_eq_left hp, Iso.hom_inv_id_assoc]

private lemma isZero_cechTerm {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (p : ℕ) (hp : r < p) : IsZero ((Cech.cechComplex f R).X p) := by
  have : IsEmpty {s : Finset (Fin r) // s.card = p} := ⟨fun s ↦ by
    have := Finset.card_le_univ s.1
    simp only [Fintype.card_fin, s.2] at this
    omega⟩
  show IsZero (ModuleCat.of R (Cech.cechTerm f R p))
  exact ModuleCat.isZero_of_subsingleton _

private def cechLeg {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) : koszulPowerCochainComplex f n ⟶ Cech.cechComplex f R where
  f p := cechLegComponent f n p
  comm' p j hpj := by
    obtain rfl : p + 1 = j := hpj
    by_cases hp : p < r
    · let q := r - (p + 1)
      have h : p + (q + 1) = r := by omega
      apply (cancel_epi (degreeIso f n p (q + 1) h).hom).mp
      rw [← Category.assoc, cechLegComponent_degreeIso,
        ← Category.assoc (degreeIso f n p (q + 1) h).hom, degreeIso_d f n p q h,
        Preadditive.zsmul_comp, Category.assoc, cechLegComponent_degreeIso]
      apply ModuleCat.hom_ext
      simp only [Cech.cechComplex, CochainComplex.of_d, ModuleCat.hom_comp,
        ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
      change (Cech.cechD f R p).comp (localizeExterior f n p (q + 1) h) =
        ((-1 : ℤ) ^ r) • ((localizeExterior f n (p + 1) q (by omega)).comp
          (Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (n + 1))) q))
      rw [← Int.cast_smul_eq_zsmul R]
      simpa using localizeExterior_d f n p q h
    · exact (isZero_cechTerm f (p + 1) (by omega)).eq_of_tgt _ _

private lemma fraction_eq_zero {R : Type*} [CommRing R] (g x : R) (n : ℕ) :
    fraction g x n = 0 ↔ ∃ k : ℕ, g ^ k * x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨u, k, rfl⟩, hu⟩
    exact ⟨k, by simpa [Submonoid.smul_def, smul_eq_mul] using hu⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨g ^ k, k, rfl⟩, by simpa [Submonoid.smul_def, smul_eq_mul] using hk⟩

private lemma map_basis_add {R : Type*} [CommRing R] {I : Type*}
    (F : ℕ ⥤ ModuleCat.{u} R) (B : ∀ n, Module.Basis I R (F.obj n)) (g : I → R)
    (h : ∀ n i, F.map (homOfLE (Nat.le_succ n)) (B n i) = g i • B (n + 1) i)
    (n k : ℕ) (i : I) :
    F.map (homOfLE (Nat.le_add_right n k)) (B n i) = g i ^ k • B (n + k) i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : homOfLE (Nat.le_add_right n (k + 1)) =
        homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_succ (n + k)) := Subsingleton.elim _ _
    rw [he, F.map_comp]
    simp only [ModuleCat.comp_apply, ih, map_smul]
    show g i ^ k • F.map (homOfLE (Nat.le_succ (n + k))) (B (n + k) i) =
      g i ^ (k + 1) • B ((n + k) + 1) i
    rw [h, smul_smul, pow_succ]

private def isColimit_diagonalLocalization {R : Type u} [CommRing R]
    {I : Type v} [Fintype I] [DecidableEq I]
    (F : ℕ ⥤ ModuleCat.{max u v} R) (B : ∀ n, Module.Basis I R (F.obj n))
    (g : I → R) (a : I → Rˣ)
    (j : F ⟶ (Functor.const ℕ).obj
      (ModuleCat.of R (DirectSum I (fun i ↦ LocalizedModule (Submonoid.powers (g i)) R))))
    (hmap : ∀ n i, F.map (homOfLE (Nat.le_succ n)) (B n i) = g i • B (n + 1) i)
    (hj : ∀ n i, j.app n (B n i) = DirectSum.lof R I
      (fun i ↦ LocalizedModule (Submonoid.powers (g i)) R) i
        (fraction (g i) (a i) (n + 1))) :
    IsColimit ({ pt := _, ι := j } : Cocone F) := by
  let L := fun i ↦ LocalizedModule (Submonoid.powers (g i)) R
  have hnat (n m : ℕ) (hnm : n ≤ m) (x : F.obj n) :
      j.app m (F.map (homOfLE hnm) x) = j.app n x :=
    ConcreteCategory.congr_hom (j.naturality (homOfLE hnm)) x
  have hcoord (n : ℕ) (x : F.obj n) (i : I) :
      DirectSum.component R I L i (j.app n x) =
        fraction (g i) ((B n).repr x i * a i) (n + 1) := by
    dsimp only [L]
    conv_lhs => rw [← (B n).sum_repr x]
    simp only [map_sum, map_smul, hj]
    rw [map_sum]
    simp only [map_smul]
    change (∑ k, (B n).repr x k •
      (DFinsupp.single k (fraction (g k) (a k) (n + 1)) : DirectSum I L) i) = _
    simp only [DFinsupp.single_apply, smul_dite, smul_zero,
      Finset.sum_dite_eq', Finset.mem_univ, ↓reduceIte]
    exact fraction_smul _ _ _ _
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{max u v, max u v} _
  letI : PreservesColimit F (forget (ModuleCat.{max u v} R)) := by
    change PreservesColimit F
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat ⋙ forget AddCommGrpCat)
    infer_instance
  letI : ReflectsColimit F (forget (ModuleCat.{max u v} R)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget (ModuleCat R))
  apply Types.FilteredColimit.isColimitOf'
  · change ∀ y : DirectSum I L, ∃ n x, y = j.app n x
    intro y
    induction y using DirectSum.induction_lon (R := R) (M := L) with
    | zero => exact ⟨0, 0, (map_zero _).symm⟩
    | add y z hy hz =>
      obtain ⟨n, x, rfl⟩ := hy
      obtain ⟨m, w, rfl⟩ := hz
      refine ⟨max n m, F.map (homOfLE (le_max_left _ _)) x +
        F.map (homOfLE (le_max_right _ _)) w, ?_⟩
      rw [map_add, hnat, hnat]
    | lof i y =>
      induction y using LocalizedModule.induction_on with
      | h x s =>
        obtain ⟨k, hk⟩ := s.2
        have hs : s = (⟨g i ^ k, k, rfl⟩ : Submonoid.powers (g i)) := Subtype.ext hk.symm
        subst s
        refine ⟨k, (g i * x * (↑((a i)⁻¹) : R)) • B k i, ?_⟩
        rw [map_smul, hj]
        change DirectSum.lof R I L i (fraction (g i) x k) =
          (g i * x * (↑((a i)⁻¹) : R)) • DirectSum.lof R I L i
            (fraction (g i) (a i) (k + 1))
        rw [← (DirectSum.lof R I L i).map_smul, fraction_smul]
        have hm : g i * x * (↑((a i)⁻¹) : R) * ↑(a i) = g i * x := by
          rw [mul_assoc, Units.inv_mul, mul_one]
        rw [hm, ← fraction_smul, fraction_succ]
  · intro n x y hxy
    change j.app n x = j.app n y at hxy
    have hz : j.app n (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hk (i : I) : ∃ k, g i ^ k * (B n).repr (x - y) i = 0 := by
      have hh := congrArg (DirectSum.component R I L i) hz
      rw [hcoord, map_zero, fraction_eq_zero] at hh
      obtain ⟨k, hk⟩ := hh
      refine ⟨k, ?_⟩
      have hh := congrArg (· * (↑((a i)⁻¹) : R)) hk
      simpa only [mul_assoc, Units.mul_inv, mul_one, zero_mul] using hh
    choose k hk using hk
    let N := ∑ i, k i
    have hN (i : I) : k i ≤ N := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    refine ⟨n + N, homOfLE (Nat.le_add_right n N), ?_⟩
    change F.map (homOfLE (Nat.le_add_right n N)) x =
      F.map (homOfLE (Nat.le_add_right n N)) y
    apply sub_eq_zero.mp
    rw [← map_sub, ← (B n).sum_repr (x - y), map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, map_basis_add F B g hmap, smul_smul]
    have he : g i ^ N * (B n).repr (x - y) i = 0 := by
      rw [← Nat.sub_add_cancel (hN i), pow_add, mul_assoc, hk, mul_zero]
    rw [mul_comm, he, zero_smul]

private def complementEquiv {r p q : ℕ} (h : p + q = r) :
    {s : Finset (Fin r) // s.card = q} ≃ {t : Finset (Fin r) // t.card = p} where
  toFun := complementIndex h
  invFun := complementIndex (by omega)
  left_inv s := Subtype.ext (compl_compl s.1)
  right_inv s := Subtype.ext (compl_compl s.1)

private abbrev degreeBasis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (hp : p ≤ r) :
    Module.Basis {t : Finset (Fin r) // t.card = p} R ((koszulPowerCochainComplex f n).X p) :=
  ((exteriorBasis R r (r - p)).map (degreeIso f n p (r - p) (by omega)).toLinearEquiv).reindex
    (complementEquiv (by omega))

private lemma degreeBasis_apply {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (hp : p ≤ r) (t : {t : Finset (Fin r) // t.card = p}) :
    degreeBasis f n p hp t = (degreeIso f n p (r - p) (by omega)).hom
      (exteriorBasis R r (r - p) (complementIndex (by omega) t)) := by
  simp only [degreeBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  rfl

private lemma cechLeg_basis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p q : ℕ) (h : p + q = r)
    (s : {s : Finset (Fin r) // s.card = q}) :
    (cechLeg f n).f p ((degreeIso f n p q h).hom (exteriorBasis R r q s)) =
      cechFraction f n (complementIndex h s) (orientation s.1ᶜ) := by
  show (cechLegComponent f n p) ((degreeIso f n p q h).hom _) = _
  rw [← ModuleCat.comp_apply, cechLegComponent_degreeIso]
  exact localizeExterior_basis f n p q h s

private lemma cechLeg_degreeBasis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (hp : p ≤ r)
    (t : {t : Finset (Fin r) // t.card = p}) :
    (cechLeg f n).f p (degreeBasis f n p hp t) =
      cechFraction f n t (orientation t.1) := by
  rw [degreeBasis_apply, cechLeg_basis]
  rw [compl_compl]
  congr 1
  exact Subtype.ext (compl_compl t.1)

private lemma transition_degreeBasis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (hp : p ≤ r)
    (t : {t : Finset (Fin r) // t.card = p}) :
    ((koszulRegradingFunctor R r).map (powerTransition f n)).f p (degreeBasis f n p hp t) =
      (∏ i ∈ t.1, f i) • degreeBasis f (n + 1) p hp t := by
  rw [degreeBasis_apply, degreeBasis_apply, ← ModuleCat.comp_apply, degreeIso_transition,
    ModuleCat.comp_apply, powerTransition_basis, map_smul]
  congr 1
  exact congrArg (fun s : Finset (Fin r) ↦ ∏ i ∈ s, f i) (compl_compl t.1)

private lemma cechLeg_naturality {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    (koszulPowerDiagram f (powerTransition f)).map (homOfLE (Nat.le_succ n)) ≫
      cechLeg f (n + 1) = cechLeg f n := by
  rw [Functor.ofSequence_map_homOfLE_succ]
  ext p : 1
  by_cases hp : p ≤ r
  · apply ModuleCat.hom_ext
    apply (degreeBasis f n p hp).ext
    intro t
    show (cechLeg f (n + 1)).f p
      (((koszulRegradingFunctor R r).map (powerTransition f n)).f p (degreeBasis f n p hp t)) =
        (cechLeg f n).f p (degreeBasis f n p hp t)
    rw [transition_degreeBasis, map_smul, cechLeg_degreeBasis, cechLeg_degreeBasis]
    exact prod_smul_cechFraction f n t _
  · exact (isZero_degree f n p (by omega)).eq_of_src _ _

private def cechCocone {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    Cocone (koszulPowerDiagram f (powerTransition f)) where
  pt := Cech.cechComplex f R
  ι := NatTrans.ofSequence (cechLeg f)
    (fun n ↦ (cechLeg_naturality f n).trans (Category.comp_id _).symm)

private def cechCoconeIsColimit {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    IsColimit (cechCocone f) := by
  apply HomologicalComplex.isColimitOfEval
  intro p
  by_cases hp : p ≤ r
  · let E := HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) p
    apply isColimit_diagonalLocalization
      (koszulPowerDiagram f (powerTransition f) ⋙ E) (fun n ↦ degreeBasis f n p hp)
      (fun t ↦ ∏ i ∈ t.1, f i)
      (fun t ↦ (-1 : Rˣ) ^ ((∑ i ∈ t.1, i.val) + r * t.1.card))
    · intro n t
      change (E.map ((koszulPowerDiagram f (powerTransition f)).map
        (homOfLE (Nat.le_succ n)))) (degreeBasis f n p hp t) = _
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact transition_degreeBasis f n p hp t
    · intro n t
      change (cechLeg f n).f p (degreeBasis f n p hp t) =
        cechFraction f n t (↑((-1 : Rˣ) ^ ((∑ i ∈ t.1, i.val) + r * t.1.card)) : R)
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
      exact cechLeg_degreeBasis f n p hp t
  · exact
      { desc := fun _ ↦ 0
        fac := fun _ n ↦ (isZero_degree f n p (by omega)).eq_of_src _ _
        uniq := fun _ _ _ ↦ (isZero_cechTerm f p (by omega)).eq_of_src _ _ }

private lemma orientation_eq {R : Type*} [CommRing R] {r p : ℕ}
    (t : Finset (Fin r)) (ht : t.card = p) :
    orientation (R := R) t =
      (-1 : R) ^ ((∑ i ∈ t, (i.val + 1)) + p + r * p) := by
  simp only [orientation, Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, mul_one, ht]
  rw [show (∑ i ∈ t, i.val) + p + p + r * p =
    ((∑ i ∈ t, i.val) + r * p) + 2 * p by omega]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The extended alternating Čech complex of a finite sequence `f` is the colimit of the
regraded Koszul complexes on its positive powers. The transition maps multiply each standard
exterior-basis vector by the product of the entries of `f` indexed by its complement, and the
colimit cocone sends the basis vector indexed by `s` to the localized generator indexed by the
complement `t` of `s`, with sign `(-1) ^ (∑ i ∈ t, (i + 1) + p + r * p)`. -/
@[stacks 0913]
public theorem cechComplex_isColimit_koszulPowerComplexes
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    ∃ σ : ∀ n : ℕ,
        Koszul.seqComplex (fun i ↦ f i ^ (n + 1)) ⟶
          Koszul.seqComplex (fun i ↦ f i ^ (n + 2)),
      (∀ (n q : ℕ) (s : Finset (Fin r)) (hs : s.card = q),
        (σ n).f q
            ⟨ExteriorAlgebra.ιMulti R q
                (fun k ↦ Pi.single (s.orderEmbOfFin hs k) 1),
              Koszul.ιMulti_mem q _⟩ =
          (∏ i ∈ sᶜ, f i) •
            ⟨ExteriorAlgebra.ιMulti R q
                (fun k ↦ Pi.single (s.orderEmbOfFin hs k) 1),
              Koszul.ιMulti_mem q _⟩) ∧
      ∃ ι : ∀ n : ℕ, koszulPowerCochainComplex f n ⟶ Cech.cechComplex f R,
        ∃ hι : ∀ n : ℕ,
            (koszulPowerDiagram f σ).map (homOfLE (Nat.le_succ n)) ≫
              ι (n + 1) = ι n,
          (∀ (n p q : ℕ) (s t : Finset (Fin r)) (hs : s.card = q) (ht : t.card = p)
              (hcard : p + q = r) (_ : Disjoint s t) (_ : s ∪ t = Finset.univ),
            (ι n).f p
                (koszulRegradeHom f n p q hcard
                  ⟨ExteriorAlgebra.ιMulti R q
                      (fun k ↦ Pi.single (s.orderEmbOfFin hs k) 1),
                    Koszul.ιMulti_mem q _⟩) =
              DirectSum.lof R {w : Finset (Fin r) // w.card = p}
                (fun w ↦ Cech.cechMod f R w.1) ⟨t, ht⟩
                (LocalizedModule.mk
                  ((-1 : R) ^ ((∑ i ∈ t, (i.val + 1)) + p + r * p))
                  ⟨(∏ i ∈ t, f i) ^ (n + 1), n + 1, rfl⟩)) ∧
          Nonempty (IsColimit
            ({ pt := Cech.cechComplex f R
               ι := NatTrans.ofSequence
                 (F := koszulPowerDiagram f σ)
                 (G := (Functor.const ℕ).obj (Cech.cechComplex f R)) ι
                 (fun n ↦ (hι n).trans (Category.comp_id _).symm) } :
              Cocone (koszulPowerDiagram f σ))) := by
  refine ⟨powerTransition f, ?_, cechLeg f, cechLeg_naturality f, ?_, ⟨cechCoconeIsColimit f⟩⟩
  · intro n q s hs
    simpa only [exteriorBasis_apply] using powerTransition_basis f n q ⟨s, hs⟩
  · intro n p q s t hs ht hcard hd hu
    have hst : sᶜ = t := IsCompl.compl_eq ⟨hd, codisjoint_iff.mpr hu⟩
    rw [← degreeIso_eq f n p q hcard,
      ← exteriorBasis_apply (⟨s, hs⟩ : {s : Finset (Fin r) // s.card = q}), cechLeg_basis]
    have he := congrArg (fun t : {t : Finset (Fin r) // t.card = p} ↦
      DirectSum.lof R _ (fun t ↦ Cech.cechMod f R t.1) t
        (fraction (∏ i ∈ t.1, f i) (orientation t.1) (n + 1)))
      (show complementIndex hcard ⟨s, hs⟩ = ⟨t, ht⟩ from Subtype.ext hst)
    exact he.trans (by rw [orientation_eq t ht])

end Cech
