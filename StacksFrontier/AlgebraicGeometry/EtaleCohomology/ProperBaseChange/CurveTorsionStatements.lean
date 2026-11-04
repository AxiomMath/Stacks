module
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian

/-!
# The eight statements of Situation 0A52: invariance and degenerate sheaves

Let `π : X ⟶ Spec k` be a scheme over a field and `F` an abelian sheaf on `X_étale`.
`Stacks.EtaleCohomology.CurveTorsionStatementsGeneral π F` is the assertion that the eight
statements of [Stacks, Tag 0A52] hold for `F`. This file proves that this assertion depends on `F`
only up to isomorphism and holds for a zero sheaf, and that a sheaf killed by an integer prime to
`l` which is moreover `l`-power torsion is zero.

## Main results

* `Stacks.EtaleCohomology.CurveTorsionStatementsGeneral.of_iso`: the eight statements transfer
  along an isomorphism of abelian sheaves.
* `Stacks.EtaleCohomology.curveTorsionStatements_of_isZero`: the eight statements hold for a zero
  sheaf; `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_isZero_general` is the
  bijectivity of every restriction map on the cohomology of a zero sheaf.
* `Stacks.EtaleCohomology.isZero_of_isPrimePowerTorsion_of_nsmul_eq_zero` and
  `Stacks.EtaleCohomology.isZero_of_isPrimeToCharacteristicTorsion_of_nsmul_eq_zero`: an abelian
  sheaf killed by `n` is zero as soon as it is `l`-power torsion for some `l` prime to `n`, or
  torsion prime to `n`.

## References

* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w w'

namespace Stacks.EtaleCohomology

section Torsion

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- The sections of the target of an isomorphism of abelian presheaves are the images of those of
its source, compatibly with restriction. -/
private theorem iso_inv_restrict {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (e : P ≅ Q) {U V : C}
    (f : V ⟶ U) (x : Q.obj (op U)) :
    e.hom.app (op V) (P.map f.op (e.inv.app (op U) x)) = Q.map f.op x := by
  rw [← ConcreteCategory.comp_apply, e.hom.naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (e.inv.app (op U)), Iso.inv_hom_id_app,
    ConcreteCategory.id_apply]

/-- The sections of the target of an isomorphism of abelian sheaves are the images of those of its
source, compatibly with restriction. -/
private theorem sheaf_iso_inv_restrict {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) {U V : C}
    (f : V ⟶ U) (x : G.obj.obj (op U)) :
    e.hom.hom.app (op V) (F.obj.map f.op (e.inv.hom.app (op U) x)) = G.obj.map f.op x :=
  iso_inv_restrict ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso e) f x

/-- **Being `l`-power torsion transports along an isomorphism of abelian sheaves.** -/
theorem isPrimePowerTorsion_of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (l : ℕ)
    (hF : Stacks.Torsion.IsPrimePowerTorsion J l F) :
    Stacks.Torsion.IsPrimePowerTorsion J l G := by
  intro U x
  obtain ⟨R, hR, h⟩ := hF U (e.inv.hom.app (op U) x)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨r, hr, hx⟩ := h V f hf
  refine ⟨r, hr, ?_⟩
  have := congrArg (e.hom.hom.app (op V)) hx
  rwa [map_nsmul, map_zero, sheaf_iso_inv_restrict e f x] at this

/-- **Being torsion prime to `p` transports along an isomorphism of abelian sheaves.** -/
theorem isPrimeToCharacteristicTorsion_of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (p : ℕ) (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion J p F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J p G := by
  intro U x
  obtain ⟨R, hR, h⟩ := hF U (e.inv.hom.app (op U) x)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, hn, hnp, hx⟩ := h V f hf
  refine ⟨n, hn, hnp, ?_⟩
  have := congrArg (e.hom.hom.app (op V)) hx
  rwa [map_nsmul, map_zero, sheaf_iso_inv_restrict e f x] at this

end Torsion

section Vanishing

/-- An element of an abelian group killed by two coprime integers is zero. -/
private theorem eq_zero_of_coprime_nsmul {A : Type*} [AddCommGroup A] {a b : ℕ}
    (hab : Nat.Coprime a b) {y : A} (ha : a • y = 0) (hb : b • y = 0) : y = 0 := by
  have h := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero ha) (addOrderOf_dvd_of_nsmul_eq_zero hb)
  rwa [hab.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at h

variable {X : Scheme.{u}}

/-- An abelian sheaf whose sections all vanish locally is zero. -/
private theorem isZero_of_locally_eq_zero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : ∀ (U : X.Etale) (x : F.obj.obj (op U)), ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (f : V ⟶ U), R f → F.obj.map f.op x = 0) : IsZero F := by
  have hsep : Presieve.IsSeparated X.smallEtaleTopology
      (F.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    ((isSheaf_iff_isSheaf_of_type X.smallEtaleTopology _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u + 1})
        X.smallEtaleTopology F.obj).1 F.property)).isSeparated
  rw [IsZero.iff_id_eq_zero]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  ext x
  obtain ⟨R, hR, hx⟩ := h U.unop x
  refine (hsep R hR).ext fun V f hf ↦ ?_
  change F.obj.map f.op x = F.obj.map f.op 0
  rw [map_zero, hx V f hf]

/-- **A sheaf killed by `n` which is `l`-power torsion, with `l` prime to `n`, is zero.** -/
theorem isZero_of_isPrimePowerTorsion_of_nsmul_eq_zero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {l n : ℕ} (hln : Nat.Coprime l n) (hn : ∀ (U : X.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hF : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F) : IsZero F := by
  refine isZero_of_locally_eq_zero fun U x ↦ ?_
  obtain ⟨R, hR, h⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨r, -, hr⟩ := h V f hf
  exact eq_zero_of_coprime_nsmul (Nat.Coprime.pow_left r hln) hr (hn V _)

/-- **A sheaf killed by `n` which is torsion prime to `n` is zero.** -/
theorem isZero_of_isPrimeToCharacteristicTorsion_of_nsmul_eq_zero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ}
    (hn : ∀ (U : X.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology n F) :
    IsZero F := by
  refine isZero_of_locally_eq_zero fun U x ↦ ?_
  obtain ⟨R, hR, h⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨m, -, hm, hmx⟩ := h V f hf
  exact eq_zero_of_coprime_nsmul hm hmx (hn V _)

end Vanishing

section Cohomology

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The map on étale cohomology induced by an isomorphism of abelian sheaves is bijective. -/
theorem bijective_sheafH_map_of_iso
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (n : ℕ) :
    Function.Bijective (Sheaf.H.map.{w'} e.hom n) :=
  Function.bijective_iff_has_inverse.2 ⟨Sheaf.H.map.{w'} e.inv n,
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply],
    fun y ↦ by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]⟩

end Cohomology

attribute [local instance] _root_.AlgebraicGeometry.hasExt_smallEtaleSheaf_objectUniverse

section Statements

variable {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))

/-- Restriction along any morphism is bijective on the cohomology of a zero sheaf. -/
theorem bijective_etaleCohomologyRestrictionMap_of_isZero_general {Y : Scheme.{u}} (i : Y ⟶ X)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsZero F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q) := by
  have := Sheaf.subsingleton_H_of_isZero hF q
  have := Sheaf.subsingleton_H_of_isZero
    ((etaleAbelianInverseImage.{u, 0} i).map_isZero hF) q
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The eight statements of Situation 0A52 hold for a zero sheaf.** -/
theorem curveTorsionStatements_of_isZero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsZero F) :
    CurveTorsionStatementsGeneral.{u, 0} π F := by
  have hH : ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) := Sheaf.subsingleton_H_of_isZero hF
  exact ⟨fun q _ ↦ hH q, fun _ q _ ↦ hH q, fun _ _ q _ ↦ hH q,
    fun _ _ q ↦ Finite.of_subsingleton, fun _ _ q ↦ Finite.of_subsingleton,
    fun k' _ _ _ _ q ↦ bijective_etaleCohomologyRestrictionMap_of_isZero_general _ hF q,
    fun _ k' _ _ _ q ↦ bijective_etaleCohomologyRestrictionMap_of_isZero_general _ hF q,
    fun U ↦ (bijective_etaleCohomologyRestrictionMap_of_isZero_general U.ι hF 2).2⟩

/-- Restriction on the cohomology of the target of an isomorphism of sheaves, as a composite of
restriction on the source with the maps induced by the isomorphism. -/
private theorem etaleCohomologyRestrictionMap_eq_comp_of_iso {Y : Scheme.{u}} (i : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} i G q : _ → _) =
      (Sheaf.H.map ((etaleAbelianInverseImage.{u, 0} i).map e.hom) q) ∘
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q) ∘ (Sheaf.H.map e.inv q) :=
  funext fun y ↦ by
    have h : ∀ x : Sheaf.H.{u + 1} F q,
        etaleCohomologyRestrictionMap.{u, 0, u + 1} i G q (Sheaf.H.map e.hom q x) =
          Sheaf.H.map ((etaleAbelianInverseImage.{u, 0} i).map e.hom) q
            (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q x) :=
      etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, u + 1} i e.hom q
    rw [Function.comp_apply, Function.comp_apply, ← h, ← Sheaf.H.map_comp_apply, e.inv_hom_id,
      Sheaf.H.map_id_apply]

/-- Bijectivity of restriction transfers along an isomorphism of sheaves. -/
private theorem bijective_etaleCohomologyRestrictionMap_of_iso {Y : Scheme.{u}} (i : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i G q) := by
  rw [etaleCohomologyRestrictionMap_eq_comp_of_iso i e q]
  exact (bijective_sheafH_map_of_iso ((etaleAbelianInverseImage.{u, 0} i).mapIso e) q).comp
    (h.comp (bijective_sheafH_map_of_iso e.symm q))

/-- Surjectivity of restriction transfers along an isomorphism of sheaves. -/
private theorem surjective_etaleCohomologyRestrictionMap_of_iso {Y : Scheme.{u}} (i : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i G q) := by
  rw [etaleCohomologyRestrictionMap_eq_comp_of_iso i e q]
  exact (bijective_sheafH_map_of_iso ((etaleAbelianInverseImage.{u, 0} i).mapIso e) q).2.comp
    (h.comp (bijective_sheafH_map_of_iso e.symm q).2)

/-- Constructibility on Mathlib's small étale site transports along an isomorphism. -/
private theorem isConstructibleEtaleAbelianSheaf_of_iso'
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} G :=
  isConstructibleAbelianSheaf_congr _ _
    ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)
      AddCommGrpCat.{u + 1}).inverse.mapIso e) hF

/-- **The eight statements of Situation 0A52 transfer along an isomorphism of abelian sheaves.** -/
theorem CurveTorsionStatementsGeneral.of_iso
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (h : CurveTorsionStatementsGeneral.{u, 0} π F) : CurveTorsionStatementsGeneral.{u, 0} π G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hsub : ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) →
      Subsingleton (Sheaf.H.{u + 1} G q) := fun q _ ↦
    (bijective_sheafH_map_of_iso e.symm q).1.subsingleton
  have hfin : ∀ q, Finite (Sheaf.H.{u + 1} F q) →
      Finite (Sheaf.H.{u + 1} G q) := fun q _ ↦
    Finite.of_injective _ (bijective_sheafH_map_of_iso e.symm q).1
  exact ⟨fun q hq ↦ hsub q (h1 q hq), fun hX q hq ↦ hsub q (h2 hX q hq),
    fun hp ht q hq ↦ hsub q (h3 hp (isPrimePowerTorsion_of_iso e.symm _ ht) q hq),
    fun hc ht q ↦ hfin q (h4 (isConstructibleEtaleAbelianSheaf_of_iso' e.symm hc)
      (isPrimeToCharacteristicTorsion_of_iso e.symm _ ht) q),
    fun hc hp q ↦ hfin q (h5 (isConstructibleEtaleAbelianSheaf_of_iso' e.symm hc) hp q),
    fun k' _ _ _ ht q ↦ bijective_etaleCohomologyRestrictionMap_of_iso _ e q
      (h6 k' (isPrimeToCharacteristicTorsion_of_iso e.symm _ ht) q),
    fun hp k' _ _ _ q ↦ bijective_etaleCohomologyRestrictionMap_of_iso _ e q (h7 hp k' q),
    fun U ↦ surjective_etaleCohomologyRestrictionMap_of_iso U.ι e 2 (h8 U)⟩

end Statements

end Stacks.EtaleCohomology

end
