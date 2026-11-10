module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleExhaustion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImageAssertions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReductionSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedSupportVanishing

/-!
# The eight assertions for sheaves killed by a prime: transfer lemmas

After the reductions of `Stacks.EtaleCohomology.TorsionCurveAssertions.of_constructible`, the proof
of Stacks Tag 03SC is about constructible sheaves killed by a prime `ℓ`. For two such sheaves `A`
and `B` with `A` nonzero, the torsion conditions of assertions (3), (4) and (6) pass from `A` to
`B`: if `A` is `p`-power torsion then `ℓ = p` (a sheaf killed by `ℓ` and by powers of a different
prime is zero), so `B` is `p`-power torsion too; and if `A` is torsion prime to the characteristic,
then so is `ℓ`, hence `B`. This discharges the side conditions of the sub-sheaf direction of
Tag 0GJA and of Tag 0A5D for sheaves killed by `ℓ`.

## Main results

* `Stacks.EtaleCohomology.isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero`,
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_shortExact_X₁_of_nsmul`: the sub-sheaf
  direction of Tag 0GJA for sheaves killed by `ℓ`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_extensionByZero_sub`: Tag 0GJA from `F` to
  `j_! j⁻¹ F`, for `F` constructible and killed by `ℓ`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_directImage_of_nsmul`: Tag 0A5D for a
  constructible sheaf killed by `ℓ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Transfer

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {C' : Type*} [Category* C'] {J' : GrothendieckTopology C'} {ℓ : ℕ} (hℓ : ℓ.Prime)
  {A : Sheaf J AddCommGrpCat.{u + 1}} {B : Sheaf J' AddCommGrpCat.{u + 1}} (hA : ℓ • 𝟙 A = 0)
  (hB : ℓ • 𝟙 B = 0) (hnz : ¬ IsZero A)
include hℓ hA hB hnz

/-- `p`-power torsion passes between nonzero sheaves killed by the same prime. -/
theorem isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero (p : ℕ)
    (hp : Stacks.Torsion.IsPrimePowerTorsion J p A) :
    Stacks.Torsion.IsPrimePowerTorsion J' p B := by
  rw [Stacks.Torsion.isPrimePowerTorsion_iff_locallyKilledBy] at hp ⊢
  by_cases hdvd : ℓ ∣ p
  · obtain ⟨m, rfl⟩ := hdvd
    refine locallyKilledBy_of_nsmul_id_eq_zero J' ⟨1, one_pos, (pow_one _).symm⟩ ?_
    rw [mul_nsmul, hB, smul_zero]
  · exact (hnz (isZero_of_locallyKilledBy_of_nsmul_id_eq_zero J (fun n ⟨r, _, hn⟩ => by
      rw [hn]; exact Nat.Coprime.pow_left _
        ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hdvd)))) hp hA)).elim

/-- Torsion prime to an integer passes between nonzero sheaves killed by the same prime. -/
theorem isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero (c : ℕ)
    (hc : Stacks.Torsion.IsPrimeToCharacteristicTorsion J c A) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J' c B := by
  rw [Stacks.Torsion.isPrimeToCharacteristicTorsion_iff_locallyKilledBy] at hc ⊢
  by_cases hcop : Nat.Coprime ℓ c
  · exact locallyKilledBy_of_nsmul_id_eq_zero J' ⟨hℓ.pos, hcop⟩ hB
  · have hdvd : ℓ ∣ c := (Nat.Prime.dvd_iff_not_coprime hℓ).mpr hcop
    exact (hnz (isZero_of_locallyKilledBy_of_nsmul_id_eq_zero J (fun n ⟨_, hn⟩ =>
      Nat.Coprime.coprime_dvd_right hdvd hn) hc hA)).elim

end Transfer

/-- An additive functor preserves `ℓ • 𝟙 A = 0`. -/
private theorem nsmul_id_obj_eq_zero {D E : Type*} [Category* D] [Category* E] [Preadditive D]
    [Preadditive E] (F : D ⥤ E) [F.Additive] {ℓ : ℕ} {A : D} (h : ℓ • 𝟙 A = 0) :
    ℓ • 𝟙 (F.obj A) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The sub-sheaf direction of Tag 0GJA for sheaves killed by a prime**: the torsion side
conditions of `of_shortExact_X₁` are discharged. -/
theorem of_shortExact_X₁_of_nsmul {ℓ : ℕ} (hℓ : ℓ.Prime)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₁ : ℓ • 𝟙 S.X₁ = 0) (h₂ℓ : ℓ • 𝟙 S.X₂ = 0)
    (h₂ : TorsionCurveAssertions f S.X₂)
    (hpos : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} S.X₃ q))
    (hc : IsConstructibleSmallEtaleSheaf S.X₁ →
      IsConstructibleSmallEtaleSheaf S.X₂ ∧ Finite (Sheaf.H.{u + 1} S.X₃ 0))
    (hres : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ), Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) S.X₃ q))
    (hopen : ∀ (V : X.Opens)
      [HasExt.{u + 1} (Sheaf (V : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} V.ι).obj S.X₃) 1)) :
    TorsionCurveAssertions f S.X₁ := by
  by_cases hz : IsZero S.X₁
  · exact of_isZero f hz
  exact of_shortExact_X₁ f hS h₂ hpos hc
    (fun p => isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ h₂ℓ hz p)
    (isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ h₂ℓ hz _) hres hopen

variable [IsAlgClosed k] {Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
  [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsFinite (i ≫ f)]

include hij in
/-- **Stacks Tag 0GJA, from `F` to `j_! j⁻¹ F`**, for a constructible sheaf killed by a prime: with
`Z` finite over `k` and `U` its open complement, the eight assertions for `F` give them for
`j_! j⁻¹ F`. -/
theorem of_extensionByZero_sub {ℓ : ℕ} (hℓ : ℓ.Prime)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F)
    (hℓF : ℓ • 𝟙 F = 0) (h : TorsionCurveAssertions f F) :
    TorsionCurveAssertions f ((extensionByZero.{u, u + 1} j).obj
      ((etaleRestriction.{u, u + 1} j).obj F)) := by
  have hS := openClosedShortComplex_shortExact.{u, u + 1} i j hij F
  have := finite_of_isFinite_over_field (i ≫ f)
  obtain ⟨hA, hcl, hsep⟩ := isAffine_isClosed_isSepClosed_of_isFinite (i ≫ f)
  let : HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  set Q := (openClosedShortComplex.{u, u + 1} i j hij F).X₃
  have hQ : IsZero ((etaleRestriction.{u, u + 1} j).obj Q) :=
    isZero_etaleRestriction_etaleAbelianDirectImage.{u, u + 1} i j hij _
  have hv : ∀ q, 0 < q → Subsingleton (Sheaf.H.{u + 1} Q q) := fun q hq =>
    subsingleton_sheafH_of_isZero_etaleRestriction_of_affine_closedPoints i j hij hcl hsep Q hQ q hq
  have h₁ : ℓ • 𝟙 (openClosedShortComplex.{u, u + 1} i j hij F).X₁ = 0 := by
    change ℓ • 𝟙 ((extensionByZero.{u, u + 1} j).obj ((etaleRestriction.{u, u + 1} j).obj F)) = 0
    exact nsmul_id_obj_eq_zero _ (nsmul_id_obj_eq_zero _ hℓF)
  refine of_shortExact_X₁_of_nsmul f hℓ hS h₁ hℓF h hv
    (fun _ => ⟨hF, finite_sheafH_zero_directImage_inverseImage i hF⟩) (fun k' _ _ _ _ q => ?_)
    (fun V _ => ?_)
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed k k' f Q
    · have := hv q hq
      have := isFinite_pullback_scalarExtension f i k'
      have := subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij
        (scalarExtensionFst k k' f) (K := k') (pullback.snd i (scalarExtensionFst k k' f) ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) Q hQ q hq
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · have := isFinite_pullback_opens f i V
    exact subsingleton_sheafH_inverseImage_of_isZero_etaleRestriction i j hij V.ι (K := k)
      (pullback.fst i V.ι ≫ i ≫ f) Q hQ 1 one_pos

end TorsionCurveAssertions

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) (π : X ⟶ Y)
  [IsFinite π]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Stacks Tag 0A5D for a constructible sheaf killed by a prime**: the eight assertions for `G`
over `X` give them for `π_* G` over `Y`. -/
theorem of_directImage_of_nsmul {ℓ : ℕ} (hℓ : ℓ.Prime)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hG : IsConstructibleSmallEtaleSheaf G)
    (hℓG : ℓ • 𝟙 G = 0) (h : TorsionCurveAssertions (π ≫ fY) G) :
    TorsionCurveAssertions fY ((etaleAbelianDirectImage.{u, u + 1} π).obj G) := by
  by_cases hz : IsZero ((etaleAbelianDirectImage.{u, u + 1} π).obj G)
  · exact of_isZero fY hz
  have h₁ := nsmul_id_obj_eq_zero (etaleAbelianDirectImage.{u, u + 1} π) hℓG
  exact of_directImage fY π G h (fun _ => hG)
    (fun p => isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ hℓG hz p)
    (isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ h₁ hℓG hz _)

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
