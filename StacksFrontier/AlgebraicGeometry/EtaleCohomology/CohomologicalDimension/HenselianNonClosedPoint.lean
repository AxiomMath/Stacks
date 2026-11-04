module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FractionFieldVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurveTorsionBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections

/-!
# The residue fields at the non-closed points of a henselian Noetherian local base

Let `A` be a henselian Noetherian local ring of dimension `D` whose residue field is finite or
separably closed, `n` an integer invertible in `A`, and `P ≠ 𝔪` a prime of `A`. Granting
Travaux de Gabber, Exposé XVIII-A, Corollary 1.2
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`), the étale cohomology of `Spec κ(P)` with
coefficients killed by `n` vanishes above `2D`, hence above `1 + 2D`. This is input (3) of
Stacks 0DC6 (`AlgebraicGeometry.Scheme.ResidueFieldVanishingBound`) at the non-closed points of
the base.

## Proof

Let `j : Spec κ(P) ⟶ Spec A` and `𝓕` a sheaf on `Spec κ(P)` killed by `n`; `D ≥ 1` as `P ≠ 𝔪`.

* `H^a(Spec A, 𝓖) = 0` for `a > 1` and `𝓖` killed by `n`: by Gabber's theorem (Stacks 09ZI)
  this is the cohomology of the residue field, of `n`-cohomological dimension at most one.
* `R^b j_* 𝓕 = 0` for `b > 2D - 1`: the stalk at a geometric point `s` is the cohomology of
  `Spec κ(P) ×_{Spec A} Spec 𝒪^{sh}_s = Spec (κ(P) ⊗_A 𝒪^{sh}_s)` (Stacks 03Q9), and
  `𝒪^{sh}_s` is a strictly henselian Noetherian local ring, ind-étale over `A`, of dimension at
  most `D`; its fibre over `P` is bounded by `2D - 1`
  (`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_tensor_residueField`).
* The Leray spectral sequence for `j` then kills `H^m(Spec κ(P), 𝓕)` for `m > 2D`: for `q ≤ 2D - 1`
  the sheaf `R^q j_* 𝓕` is killed by `n` and `m - q > 1`.

The source passes to `R = A ⧸ P` and its fraction field `κ(P)`; here the Leray spectral sequence
is taken for `Spec κ(P) ⟶ Spec A` directly, which needs neither that `A ⧸ P` is henselian nor an
identification of `κ(P)` with `Frac(A ⧸ P)`. The dimension bound used is that of `A`, which is
what the conclusion `1 + 2 dim S` asks for.

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_strictHenselizationBaseChange_residueField`:
  the bound `2D - 1` for `Spec κ(P) ×_{Spec A} Spec 𝒪^{sh}_s`.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_spec_residueField_of_lt`: `R^b j_* 𝓕 = 0` for
  `b > 2D - 1`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_residueField_of_henselianLocalRing`: the
  bound `2D` for `Spec κ(P)`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_of_ne_closedPoint`: input (3)
  of Stacks 0DC6 at the non-closed points of a base `S ≅ Spec A`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

section StrictHenselization

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] (hS : B.Contains (Spec (.of A)))
  (s : GeometricPoint (Spec (.of A)))

/-- The ring map from `A` to the étale local ring of `Spec A` at a geometric point `s`: the map to
the local ring at the image of `s`, followed by the ordinary-to-étale germ map. -/
def specEtaleLocalRingMap : A →+* ↥(etaleLocalRing B (Spec (.of A)) hS s) :=
  (structureSheafStalkFromLocalRing B (Spec (.of A)) hS s).comp
    (StructureSheaf.toStalk A (s.hom (closedPoint s.residueField))).hom

/-- The strict henselization of `Spec A` at `s` maps to `Spec A` by the spectrum of
`specEtaleLocalRingMap`. -/
theorem strictHenselizationToBase_eq_spec_map :
    strictHenselizationToBase B (Spec (.of A)) hS s =
      Spec.map (CommRingCat.ofHom (specEtaleLocalRingMap B A hS s)) := by
  rw [strictHenselizationToBase, Spec.fromSpecStalk_eq']
  exact (Spec.map_comp (StructureSheaf.toStalk A _)
    (CommRingCat.ofHom (structureSheafStalkFromLocalRing B (Spec (.of A)) hS s))).symm

/-- **The fibre of `Spec A` over `P` after base change to a strict henselization.** Let `A` be a
Noetherian ring of dimension at most `D ≥ 1` with `n > 0` invertible in `A`, `P` a prime of `A`
and `s` a geometric point of `Spec A`. Granting Corollary 1.2, `2D - 1` bounds the étale
cohomology of `Spec κ(P) ×_{Spec A} Spec 𝒪^{sh}_s` with coefficients killed by `n`. -/
theorem isTorsionVanishingBound_strictHenselizationBaseChange_residueField [IsNoetherianRing A]
    {n : ℕ} (hn : 0 < n) (h : FractionFieldVanishingBound.{u} n) (P : Ideal A) [P.IsPrime]
    {D : ℕ} (hD : 1 ≤ D) (hdim : ringKrullDim A ≤ D) (hnA : IsUnit (n : A)) :
    IsTorsionVanishingBound (strictHenselizationBaseChange B hS
      (Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))) s) n
      ((2 * D - 1 : ℕ) : WithBot ℕ∞) := by
  set x := s.hom (closedPoint s.residueField)
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let O := ↥(etaleLocalRing B (Spec (.of A)) hS s)
  let : Algebra A O := (specEtaleLocalRingMap B A hS s).toAlgebra
  let : Algebra A ((Spec (.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A x
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk x) O :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hind : StacksDraft.IndEtale A O :=
    StacksDraft.indEtale_comp (StacksDraft.indEtale_atPrime x.asIdeal)
      (indEtale_etaleLocalRing B _ hS s)
  have : IsNoetherianRing ((Spec (.of A)).presheaf.stalk x) :=
    IsLocalization.isNoetherianRing x.asIdeal.primeCompl _ inferInstance
  have : IsNoetherianRing O :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := (Spec (.of A)).presheaf.stalk x)
      (ResidueField O)
  have hdimO : ringKrullDim O ≤ D :=
    (ringKrullDim_le_of_ind_etale A O (StacksDraft.indEtale_iff.mp hind)).trans hdim
  have hnO : IsUnit (n : O) := by
    simpa only [map_natCast] using hnA.map (algebraMap A O)
  refine IsTorsionVanishingBound.of_iso ?_
    (isTorsionVanishingBound_spec_tensor_residueField hn h P O hind hD hdimO hnO)
  exact pullback.congrHom rfl (strictHenselizationToBase_eq_spec_map B A hS s) ≪≫
    pullbackSpecIso A P.ResidueField O

end StrictHenselization

/-- An additive functor between sheaf categories preserves sheaves killed by `n`. -/
private lemma forall_nsmul_eq_zero_obj {X Y : Scheme.{u}}
    (Φ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Φ.Additive] {n : ℕ}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : ∀ (T : X.Etale) (x : F.obj.obj (Opposite.op T)), n • x = 0) :
    ∀ (T : Y.Etale) (x : (Φ.obj F).obj.obj (Opposite.op T)), n • x = 0 :=
  (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero _).2
    (nsmul_id_obj_eq_zero _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF))

/-- **The higher direct images from the point `P` vanish above `2D - 1`.** Let `A` be a
Noetherian ring of dimension at most `D ≥ 1` with `n > 0` invertible in `A`, `P` a prime of `A`,
`j : Spec κ(P) ⟶ Spec A`, and `𝓕` a sheaf on `Spec κ(P)` killed by `n`. Granting Corollary 1.2,
`R^b j_* 𝓕 = 0` for `b > 2D - 1`: its stalk at a geometric point `s` is the cohomology of the
base change of `j` to the strict henselization at `s` (Stacks 03Q9). -/
theorem isZero_rightDerived_spec_residueField_of_lt (A : Type u) [CommRing A]
    [IsNoetherianRing A] {n : ℕ} (hn : 0 < n) (h : FractionFieldVanishingBound.{u} n)
    (P : Ideal A) [P.IsPrime] {D : ℕ} (hD : 1 ≤ D) (hdim : ringKrullDim A ≤ D)
    (hnA : IsUnit (n : A))
    (F : Sheaf (Spec (.of P.ResidueField)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (T : (Spec (.of P.ResidueField)).Etale) (x : F.obj.obj (Opposite.op T)), n • x = 0)
    {q : ℕ} (hq : 2 * D - 1 < q) :
    IsZero (((smallEtaleDirectImageAb.{u + 1}
      (Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField)))).rightDerived q).obj F) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))
  let B := BigEtaleSite.containing (Spec (.of A))
  have hS : B.Contains (Spec (.of A)) := BigEtaleSite.contains_containing _
  let G := ((smallEtaleDirectImageAb.{u + 1} j).rightDerived q).obj F
  have hiso : IsIso (0 : G ⟶ G) := by
    refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s => ?_
    have hsrc : IsZero ((smallEtaleStalkAb s.hom).obj G) := by
      refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS j s F q).2 ?_
      refine isTorsionVanishingBound_strictHenselizationBaseChange_residueField B A hS s hn h P
        hD hdim hnA _ ?_ q (by exact_mod_cast hq)
      -- the inverse image of `𝓕` is killed by `n`
      exact forall_nsmul_eq_zero_obj
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS j s)) hF
    exact ⟨⟨0, hsrc.eq_of_src _ _, hsrc.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero G).2 ?_
  rw [← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]

/-- **The bound `2D` at a point of a henselian Noetherian local ring.** Let `A` be a henselian
Noetherian local ring of dimension at most `D ≥ 1`, `n > 0` invertible in `A`, such that `1`
bounds the cohomology of its residue field with coefficients killed by `n`, and `P` a prime of
`A`. Granting Corollary 1.2, `2D` bounds the étale cohomology of `Spec κ(P)` with coefficients
killed by `n`.

Leray for `j : Spec κ(P) ⟶ Spec A`: `H^a(Spec A, 𝓖) = 0` for `a > 1` (Stacks 09ZI) and
`R^b j_* 𝓕 = 0` for `b > 2D - 1`. -/
theorem isTorsionVanishingBound_spec_residueField_of_henselianLocalRing (A : Type u)
    [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {n : ℕ} (hn : 0 < n)
    (hk : IsTorsionVanishingBound (Spec (.of (ResidueField A))) n 1)
    (h : FractionFieldVanishingBound.{u} n) (P : Ideal A) [P.IsPrime] {D : ℕ} (hD : 1 ≤ D)
    (hdim : ringKrullDim A ≤ D) (hnA : IsUnit (n : A)) :
    IsTorsionVanishingBound (Spec (.of P.ResidueField)) n ((2 * D : ℕ) : WithBot ℕ∞) := by
  intro F hF m hm
  have hm' : 2 * D < m := by exact_mod_cast hm
  have hA := isTorsionVanishingBound_spec_of_henselianLocalRing A hn hk
  refine LerayVanishing.subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived
    (Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))) F m fun q hq => ?_
  rcases le_or_gt q (2 * D - 1) with hq' | hq'
  · exact hA _ (forall_nsmul_eq_zero_obj _ hF) (m - q)
      (by exact_mod_cast (by omega : 1 < m - q))
  · exact Sheaf.subsingleton_H_of_isZero
      (isZero_rightDerived_spec_residueField_of_lt A hn h P hD hdim hnA F hF hq') _

/-- An element of `WithBot ℕ∞` which is nonnegative and not `⊤` is a natural number. -/
private lemma exists_natCast_eq_of_nonneg_of_lt_top {a : WithBot ℕ∞} (h0 : 0 ≤ a)
    (ht : a < ⊤) : ∃ m : ℕ, a = m := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top => exact absurd ht (lt_irrefl _)
    | coe m => exact ⟨m, by simp⟩

/-- **Input (3) of Stacks 0DC6 at the non-closed points of the base**, from Travaux de Gabber,
Exposé XVIII-A, Corollary 1.2. Let `A` be a henselian Noetherian local ring whose residue field
is finite or separably closed, `S ≅ Spec A`, and `n` invertible in `A`. Granting Corollary 1.2
(`FractionFieldVanishingBound n`), for every point `s` of `S` other than the closed point,
`1 + 2 dim S` bounds the étale cohomology of `Spec κ(s)` with coefficients killed by `n`. -/
theorem isTorsionVanishingBound_residueField_of_ne_closedPoint {S : Scheme.{u}} (A : Type u)
    [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    (hk : Finite (ResidueField A) ∨ IsSepClosed (ResidueField A)) (e : S ≅ Spec (.of A))
    {n : ℕ} (hnA : IsUnit (n : A)) (h : FractionFieldVanishingBound.{u} n) (s : S)
    (hs : s ≠ e.inv.base (closedPoint A)) :
    IsTorsionVanishingBound (Spec (.of (S.residueField s))) n (1 + 2 * topologicalKrullDim S) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hnA
  have hk1 : IsTorsionVanishingBound (Spec (.of (ResidueField A))) n 1 := by
    rcases hk with hk | hk
    · exact isTorsionVanishingBound_spec_of_finite _ hn
    · exact (isTorsionVanishingBound_spec_of_isSepClosed _ hn).mono zero_le_one
  have hdimS : topologicalKrullDim S = ringKrullDim A := by
    have hhomeo : IsHomeomorph e.hom.base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
    rw [hhomeo.topologicalKrullDim_eq]
    change topologicalKrullDim (PrimeSpectrum A) = _
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  obtain ⟨D, hD⟩ := exists_natCast_eq_of_nonneg_of_lt_top
    (ringKrullDim_nonneg_of_nontrivial (R := A)) ringKrullDim_lt_top
  -- the point `y` of `Spec A` under `s`, and its prime `P ≠ 𝔪`
  let y : Spec (.of A) := e.hom.base s
  let P : Ideal A := y.asIdeal
  have : P.IsPrime := PrimeSpectrum.isPrime y
  have hsy : e.inv.base y = s := by
    change (e.hom ≫ e.inv).base s = s
    rw [e.hom_inv_id]
    rfl
  have hPm : P ≠ maximalIdeal A := fun hP =>
    hs <| hsy.symm.trans <| congrArg e.inv.base <| PrimeSpectrum.ext hP
  have hD1 : 1 ≤ D := by
    refine Nat.one_le_iff_ne_zero.2 fun hD0 => hPm ?_
    subst hD0
    have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.2 (by rw [hD])
    exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_zero_iff.1 this P inferInstance)
  have hP := isTorsionVanishingBound_spec_residueField_of_henselianLocalRing A hn hk1 h P hD1
    hD.le hnA
  -- `κ(s) ≅ κ(P)`
  let c : CommRingCat.of P.ResidueField ≅ S.residueField s :=
    (Spec.residueFieldIso (.of A) y).symm ≪≫ asIso (e.hom.residueFieldMap s)
  refine (IsTorsionVanishingBound.of_iso (Scheme.Spec.mapIso c.op) hP).mono ?_
  rw [hdimS, hD]
  exact_mod_cast (by omega : 2 * D ≤ 1 + 2 * D)

end AlgebraicGeometry.Scheme

end
