module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.Statement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The eight assertions of Stacks Tag 03SC are closed under extensions

For a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of abelian sheaves on the small étale site of a
Noetherian scheme `X` over a field, if the eight assertions of Tag 03SC
(`Stacks.EtaleCohomology.TorsionCurveAssertions`) hold for `F₁` and `F₃`, they hold for `F₂`
([Stacks, Tag 0A5C]). Consequently, if they hold for every sheaf of a suitable class killed by a
prime, they hold for every sheaf of that class killed by a positive integer.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.isConstructibleEtaleSheaf_outer`:
  constructibility of the middle term of a short exact sequence passes to the outer terms.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_shortExact`: closure under extensions.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_cohomology_concentrated`: a sheaf whose
  cohomology is finite and concentrated in degree zero, with the restriction conditions,
  satisfies the eight assertions.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_isZero` and
  `Stacks.EtaleCohomology.TorsionCurveAssertions.of_iso`: the zero sheaf satisfies the
  assertions, and they are invariant under isomorphism.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_nsmul_id_eq_zero_of_pow` and
  `Stacks.EtaleCohomology.TorsionCurveAssertions.of_nsmul_id_eq_zero`: the `ℓ`-primary
  dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ZeroObject

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- Constructibility of the middle term of a short exact sequence passes to the outer terms, on a
Noetherian scheme. -/
@[sga "4 IX 2.6" "(i bis), special case"]
theorem isConstructibleEtaleSheaf_outer [IsNoetherian X]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h : IsConstructibleSmallEtaleSheaf S.X₂) :
    IsConstructibleSmallEtaleSheaf S.X₁ ∧ IsConstructibleSmallEtaleSheaf S.X₃ := by
  obtain ⟨B, hX, hB⟩ := h
  have h' := IsConstructibleEtaleSheafIn.outer_of_shortExact hS hB
  exact ⟨⟨B, hX, h'.1⟩, ⟨B, hX, h'.2⟩⟩

/-- **Stacks Tag 0A5C.** On a Noetherian scheme over a field, the eight assertions of Tag 03SC
pass from the outer terms of a short exact sequence to its middle term. -/
theorem of_shortExact [IsNoetherian X]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₁ : TorsionCurveAssertions f S.X₁) (h₃ : TorsionCurveAssertions f S.X₃) :
    TorsionCurveAssertions f S.X₂ where
  vanishing q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact.{u, u + 1, u + 1} hS h₁.vanishing
      h₃.vanishing q hq
  vanishing_of_isAffine hX q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine.{u, u + 1, u + 1} hS
      h₁.vanishing_of_isAffine h₃.vanishing_of_isAffine hX q hq
  vanishing_of_isPrimePowerTorsion p hp hp0 h₂ q hq :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion.{u, u + 1, u + 1} p hS
      (h₁.vanishing_of_isPrimePowerTorsion p hp hp0) (h₃.vanishing_of_isPrimePowerTorsion p hp hp0)
      h₂ q hq
  finite_of_isPrimeToCharacteristicTorsion hc ht q := by
    have hc' := isConstructibleEtaleSheaf_outer hS hc
    have ht' := isPrimeToCharacteristicTorsion_of_shortExact (ringExpChar k) hS ht
    have := h₁.finite_of_isPrimeToCharacteristicTorsion hc'.1 ht'.1 q
    have := h₃.finite_of_isPrimeToCharacteristicTorsion hc'.2 ht'.2 q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  finite_of_isProper hf hc q := by
    have hc' := isConstructibleEtaleSheaf_outer hS hc
    have := h₁.finite_of_isProper hf hc'.1 q
    have := h₃.finite_of_isProper hf hc'.2 q
    exact finite_sheafCohomology_X₂_of_shortExact hS q
  bijective_of_isPrimeToCharacteristicTorsion ht k' _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion
      (scalarExtensionFst k k' f) (ringExpChar k) hS
      (fun h => h₁.bijective_of_isPrimeToCharacteristicTorsion h k')
      (fun h => h₃.bijective_of_isPrimeToCharacteristicTorsion h k') ht q
  bijective_of_isProper hf k' _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isProper
      (scalarExtensionFst k k' f) f hS (fun h => h₁.bijective_of_isProper h k')
      (fun h => h₃.bijective_of_isProper h k') hf q
  surjective_restriction U _ :=
    surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing U.ι hS h₁.vanishing
      (h₁.surjective_restriction U) (h₃.surjective_restriction U)

/-- Cohomology is finite in every degree if it is finite in degree zero and vanishes above. -/
private theorem finite_of_concentrated {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} G q))
    (hfinite : Finite (Sheaf.H.{u + 1} G 0)) (q : ℕ) : Finite (Sheaf.H.{u + 1} G q) := by
  cases q with
  | zero => exact hfinite
  | succ n => have := hvanish (n + 1) n.succ_pos; exact Finite.of_subsingleton

/-- **A sheaf whose cohomology is concentrated in degree zero and finite there satisfies the eight
assertions**, provided restriction to every scalar extension by an algebraically closed field is
bijective and the positive-degree cohomology of its restriction to every open vanishes. -/
theorem of_cohomology_concentrated {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} G q))
    (hfinite : Finite (Sheaf.H.{u + 1} G 0))
    (hrestr : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ), Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) G q))
    (hopen : ∀ (U : X.Opens)
      [HasExt.{u + 1} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj G) 2)) :
    TorsionCurveAssertions f G where
  vanishing q hq := hvanish q (by omega)
  vanishing_of_isAffine _ q hq := hvanish q (by omega)
  vanishing_of_isPrimePowerTorsion _ _ _ _ q hq := hvanish q (by omega)
  finite_of_isPrimeToCharacteristicTorsion _ _ q := finite_of_concentrated hvanish hfinite q
  finite_of_isProper _ _ q := finite_of_concentrated hvanish hfinite q
  bijective_of_isPrimeToCharacteristicTorsion _ k' _ _ _ _ q := hrestr k' q
  bijective_of_isProper _ k' _ _ _ _ q := hrestr k' q
  surjective_restriction U _ := fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- **The eight assertions hold for the zero sheaf.** -/
theorem of_isZero {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hG : IsZero G) :
    TorsionCurveAssertions f G := by
  have hv : ∀ {Y : Scheme.{u}} [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
      (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}), IsZero H →
      ∀ q, Subsingleton (Sheaf.H.{u + 1} H q) := fun H hH q =>
    subsingleton_ext_of_isZero_right _ hH q
  refine of_cohomology_concentrated f (fun q _ => hv G hG q)
    (have := hv G hG 0; Finite.of_subsingleton) (fun k' _ _ _ _ q => ?_) (fun U _ => ?_)
  · have := hv G hG q
    have := hv _ ((etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' f)).map_isZero hG) q
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · exact hv _ ((etaleAbelianInverseImage.{u, u + 1} U.ι).map_isZero hG) 2

/-- **The eight assertions depend only on the isomorphism class of the sheaf**, on a Noetherian
scheme. -/
theorem of_iso [IsNoetherian X] {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (h : TorsionCurveAssertions f F) : TorsionCurveAssertions f G := by
  have hS : (ShortComplex.mk e.hom (0 : G ⟶ 0) (by simp)).ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := e.inv
        s := 0
        f_r := by simp
        s_g := (isZero_zero _).eq_of_tgt _ _
        id := by simp }
  exact of_shortExact f hS h (of_isZero f (isZero_zero _))

/-- If the eight assertions hold for sheaves of `P` killed by `a` and by `b`, they hold for the
sheaves of `P` killed by `a * b`. -/
private theorem of_nsmul_id_eq_zero_mul [IsNoetherian X]
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃) (a b : ℕ)
    (ha : ∀ G, P G → a • 𝟙 G = 0 → TorsionCurveAssertions f G)
    (hb : ∀ G, P G → b • 𝟙 G = 0 → TorsionCurveAssertions f G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hPF : P F) (hF : (a * b) • 𝟙 F = 0) :
    TorsionCurveAssertions f F := by
  have hS := kernelQuotientShortComplex_shortExact (a • 𝟙 F)
  have hPS := hP _ hS hPF
  exact of_shortExact f hS (ha _ hPS.1 (nsmul_id_kernel_eq_zero F a))
    (hb _ hPS.2 (nsmul_id_cokernel_eq_zero F a b hF))

/-- On a Noetherian scheme over a field, let `P` be a class of abelian sheaves passing from the
middle term of a short exact sequence to its outer terms. If the eight assertions of Tag 03SC hold
for every sheaf of `P` killed by `a`, they hold for every sheaf of `P` killed by `a ^ n`. -/
theorem of_nsmul_id_eq_zero_of_pow [IsNoetherian X]
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃) (a : ℕ)
    (h : ∀ G, P G → a • 𝟙 G = 0 → TorsionCurveAssertions f G) :
    ∀ (n : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), P F →
      a ^ n • 𝟙 F = 0 → TorsionCurveAssertions f F := by
  intro n
  induction n with
  | zero =>
    intro F _ hF
    exact of_isZero f ((IsZero.iff_id_eq_zero F).mpr (by simpa using hF))
  | succ n ih =>
    intro F hPF hF
    exact of_nsmul_id_eq_zero_mul f P hP a (a ^ n) h ih F hPF (by rwa [← pow_succ'])

/-- **The `ℓ`-primary dévissage of Tag 03SC.** On a Noetherian scheme over a field, let `P` be a
class of abelian sheaves passing from the middle term of a short exact sequence to its outer
terms. If the eight assertions hold for every sheaf of `P` killed by a prime, they hold for every
sheaf of `P` killed by a positive integer. -/
theorem of_nsmul_id_eq_zero [IsNoetherian X]
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G, P G → ℓ • 𝟙 G = 0 → TorsionCurveAssertions f G) :
    ∀ (m : ℕ), m ≠ 0 → ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, P F →
      m • 𝟙 F = 0 → TorsionCurveAssertions f F := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm F hPF hF
    obtain rfl | hm1 : m = 1 ∨ 1 < m := by omega
    · exact of_isZero f ((IsZero.iff_id_eq_zero F).mpr (by simpa using hF))
    · have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      have hfpos : 0 < m.factorization m.minFac :=
        hp.factorization_pos_of_dvd hm (Nat.minFac_dvd m)
      obtain ⟨b, hb⟩ := Nat.ordProj_dvd m m.minFac
      have hbne : b ≠ 0 := by
        rintro rfl
        exact hm (hb.trans (Nat.mul_zero _))
      have htwo : 2 ≤ m.minFac ^ m.factorization m.minFac :=
        hp.two_le.trans (Nat.le_self_pow hfpos.ne' _)
      have hblt : b < m := by
        rw [hb]
        exact (by omega : b < 2 * b).trans_le (Nat.mul_le_mul_right b htwo)
      exact of_nsmul_id_eq_zero_mul f P hP _ b
        (of_nsmul_id_eq_zero_of_pow f P hP m.minFac (h _ hp) (m.factorization m.minFac))
        (ih b hblt hbne) F hPF (by rw [← hb]; exact hF)

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
