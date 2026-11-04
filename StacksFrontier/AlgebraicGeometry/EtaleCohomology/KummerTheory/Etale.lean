module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ShortExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# The étale Kummer sequence

If a natural number `n` is invertible on a scheme `S`, then the `n`-th power map on the sheaf
of units is locally surjective for the étale topology, so the Kummer sequence
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` is short exact on both the big and the small étale site of `S`.

## Main results

* `AlgebraicGeometry.unitsPresheaf_isSheaf_bigEtale` — the multiplicative presheaf is a sheaf
  on a chosen big étale site.
* `AlgebraicGeometry.kummerSequence_shortExact_bigEtale`,
  `AlgebraicGeometry.kummerSequence_shortExact_smallEtale` — the Kummer sequence is short exact.

## Implementation notes

Local surjectivity is the content. A unit `a` on an object `T` of the site acquires an `n`-th
root on the standard étale cover of `T` obtained by adjoining a root of `X ^ n - a` to the
Laurent ring of global functions: the derivative `n X ^ (n - 1)` is a unit there because `n` is
invertible and the root is, so that algebra is étale and faithfully flat. The resulting étale
covering of the underlying scheme is then refined by a covering of the chosen site. Short
exactness follows from `AlgebraicGeometry.kummerSequence_shortExact_of_isLocallySurjective`.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Polynomial

namespace AlgebraicGeometry

universe u

/-- The units of global functions form a sheaf on a chosen big étale site: the fpqc sheaf
property restricts along the continuous inclusion of the big étale site into the schemes over
the base. -/
public theorem unitsPresheaf_isSheaf_bigEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Presheaf.IsSheaf (BigEtaleOver.topology B S hS)
      (unitsPresheaf (BigEtaleOver.toScheme B S hS)) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat)
  exact isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS
    (unitsPresheaf (Over.forget S) ⋙ CategoryTheory.forget AddCommGrpCat)
    (unitsPresheaf_comp_forget_isSheaf_fpqc S)

private noncomputable def kummerPolynomial {R : Type*} [CommRing R]
    (a : R) (n : ℕ) : R[X] :=
  X ^ n - C a

private lemma kummerPolynomial_root_pow {R : Type*} [CommRing R]
    (a : R) (n : ℕ) :
    (AdjoinRoot.root (kummerPolynomial a n)) ^ n =
      algebraMap R (AdjoinRoot (kummerPolynomial a n)) a := by
  have h : aeval (AdjoinRoot.root (kummerPolynomial a n))
      (kummerPolynomial a n) = 0 := by
    rw [kummerPolynomial, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  change aeval (AdjoinRoot.root (kummerPolynomial a n)) (X ^ n - C a) = 0 at h
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

private lemma kummerPolynomial_monic {R : Type*} [CommRing R] (a : R) {n : ℕ} (hn : 0 < n) :
    (kummerPolynomial a n).Monic :=
  monic_X_pow_sub_C a (Nat.ne_of_gt hn)

private lemma kummerPolynomial_root_isUnit {R : Type*} [CommRing R]
    (a : R) (n : ℕ) (hn : 0 < n) (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root (kummerPolynomial a n)) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt hn)).mp
  rw [kummerPolynomial_root_pow]
  exact ha.map _

private lemma kummerPolynomial_derivative_isUnit {R : Type*} [CommRing R]
    (a : R) (n : ℕ) (hn : 0 < n) (ha : IsUnit a)
    (hnunit : IsUnit (n : R)) :
    IsUnit (aeval (AdjoinRoot.root (kummerPolynomial a n))
      (kummerPolynomial a n).derivative) := by
  have hd : aeval (AdjoinRoot.root (kummerPolynomial a n))
      (kummerPolynomial a n).derivative =
        (n : AdjoinRoot (kummerPolynomial a n)) *
          (AdjoinRoot.root (kummerPolynomial a n)) ^ (n - 1) := by
    calc
      aeval (AdjoinRoot.root (kummerPolynomial a n))
          (kummerPolynomial a n).derivative =
            aeval (AdjoinRoot.root (kummerPolynomial a n))
              (C (n : R) * X ^ (n - 1)) := by
        simp [kummerPolynomial, derivative_X_pow]
      _ = _ := by simp
  rw [hd]
  exact (hnunit.map (algebraMap R (AdjoinRoot (kummerPolynomial a n)))).mul
    ((kummerPolynomial_root_isUnit a n hn ha).pow (n - 1))

private lemma kummerPolynomial_algebra_etale {R : Type*} [CommRing R]
    (a : R) (n : ℕ) (hn : 0 < n) (ha : IsUnit a)
    (hnunit : IsUnit (n : R)) :
    Algebra.Etale R (AdjoinRoot (kummerPolynomial a n)) := by
  let f := kummerPolynomial a n
  have hu : IsUnit (AdjoinRoot.mk f f.derivative) := by
    simpa [AdjoinRoot.aeval_eq] using
      kummerPolynomial_derivative_isUnit a n hn ha hnunit
  let P : StandardEtalePair R := ⟨f, kummerPolynomial_monic a hn, f.derivative, ⟨1, 0, 1, by simp⟩⟩
  have hle : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤
      IsUnit.submonoid (AdjoinRoot P.f) := by
    rintro x ⟨k, rfl⟩
    exact hu.pow k
  let e1 : AdjoinRoot P.f ≃ₐ[AdjoinRoot P.f]
      Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atUnits _ _ hle
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    (e1.restrictScalars R).symm)

private lemma kummerPolynomial_algebra_faithfullyFlat {R : Type*} [CommRing R]
    [Nontrivial R]
    (a : R) (n : ℕ) (hn : 0 < n) :
    Module.FaithfullyFlat R (AdjoinRoot (kummerPolynomial a n)) := by
  have hm := kummerPolynomial_monic a hn
  have hdeg : 0 < (kummerPolynomial a n).degree := by
    rw [kummerPolynomial, degree_X_pow_sub_C hn]
    exact_mod_cast hn
  have : Nontrivial (AdjoinRoot (kummerPolynomial a n)) :=
    (AdjoinRoot.nontrivial_iff_of_monic hm).2 hdeg
  have : Module.Free R (AdjoinRoot (kummerPolynomial a n)) := hm.free_adjoinRoot
  infer_instance

private abbrev kummerLaurentRing (T : Scheme.{u}) :=
  LaurentPolynomial (↑(Scheme.Γ.obj (Opposite.op T)))

private abbrev kummerRootAlgebra (T : Scheme.{u}) (n : ℕ) :=
  AdjoinRoot (kummerPolynomial (LaurentPolynomial.T 1 : kummerLaurentRing T) n)

private noncomputable def kummerUnitMap (T : Scheme.{u})
    (f : Γ(T, ⊤)ˣ) :
    CommRingCat.of (kummerLaurentRing T) ⟶
      CommRingCat.of Γ(T, ⊤) :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id _) f)

private noncomputable def kummerRootTargetMap {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) :
    T ⟶ Spec (CommRingCat.of (kummerLaurentRing T)) :=
  ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of (kummerLaurentRing T)))
    (kummerUnitMap T f).op

private noncomputable def kummerRootCoverMap (T : Scheme.{u}) (n : ℕ) :
    Spec (CommRingCat.of (kummerRootAlgebra T n)) ⟶
      Spec (CommRingCat.of (kummerLaurentRing T)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (kummerLaurentRing T) (kummerRootAlgebra T n)))

private noncomputable def kummerLaurentCoordinate (T : Scheme.{u}) :
    Γ(Spec (CommRingCat.of (kummerLaurentRing T)), ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv.hom.toMonoidHom)
    (LaurentPolynomial.isUnit_T (1 : ℤ)).unit

private noncomputable def kummerRootCoordinate {T : Scheme.{u}}
    (n : ℕ) (hn : 0 < n) : (kummerRootAlgebra T n)ˣ :=
  (kummerPolynomial_root_isUnit (LaurentPolynomial.T 1 : kummerLaurentRing T) n hn
    (LaurentPolynomial.isUnit_T 1)).unit

private noncomputable def kummerRootOnSpec {T : Scheme.{u}}
    (n : ℕ) (hn : 0 < n) :
    Γ(Spec (CommRingCat.of (kummerRootAlgebra T n)), ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of (kummerRootAlgebra T n))).inv.hom.toMonoidHom)
    (kummerRootCoordinate n hn)

private lemma kummerRootCoordinate_val_pow {T : Scheme.{u}}
    (n : ℕ) (hn : 0 < n) :
    (kummerRootCoordinate (T := T) n hn : kummerRootAlgebra T n) ^ n =
      algebraMap (kummerLaurentRing T) (kummerRootAlgebra T n)
        (LaurentPolynomial.T 1) := by
  show (((kummerPolynomial_root_isUnit (LaurentPolynomial.T 1) n hn
      (LaurentPolynomial.isUnit_T 1)).unit : (kummerRootAlgebra T n)ˣ) :
        kummerRootAlgebra T n) ^ n = _
  rw [IsUnit.unit_spec, kummerPolynomial_root_pow]

private lemma kummerRootCoverMap_coordinate_pow {T : Scheme.{u}}
    (n : ℕ) (hn : 0 < n) :
    Units.map (kummerRootCoverMap T n).appTop.hom.toMonoidHom
        (kummerLaurentCoordinate T) = kummerRootOnSpec (T := T) n hn ^ n := by
  apply Units.ext
  show (kummerRootCoverMap T n).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
        (LaurentPolynomial.T 1)) =
    ((Scheme.ΓSpecIso (CommRingCat.of (kummerRootAlgebra T n))).inv.hom
      (kummerRootCoordinate (T := T) n hn)) ^ n
  rw [← map_pow, kummerRootCoordinate_val_pow]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (algebraMap (kummerLaurentRing T) (kummerRootAlgebra T n)))
  exact (congrArg (fun k => k.hom (LaurentPolynomial.T 1)) h).symm

private lemma kummerRootTargetMap_coordinate {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) :
    Units.map (kummerRootTargetMap f).appTop.hom.toMonoidHom
        (kummerLaurentCoordinate T) = f := by
  apply Units.ext
  show (kummerRootTargetMap f).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
        (LaurentPolynomial.T 1)) = (f : Γ(T, ⊤))
  have h := ΓSpec_adjunction_homEquiv_eq (kummerUnitMap T f)
  have h' := congrArg (fun g => g.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
          (LaurentPolynomial.T 1))) h
  have hId := Iso.inv_hom_id_apply
    (Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T)))
    (LaurentPolynomial.T 1)
  change (kummerRootTargetMap f).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
        (LaurentPolynomial.T 1)) =
    (kummerUnitMap T f).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
          (LaurentPolynomial.T 1))) at h'
  rw [hId] at h'
  change (kummerRootTargetMap f).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (kummerLaurentRing T))).inv
        (LaurentPolynomial.T 1)) =
    LaurentPolynomial.eval₂ (RingHom.id _) f (LaurentPolynomial.T 1) at h'
  rw [LaurentPolynomial.eval₂_T] at h'
  exact h'.trans (congrArg Units.val (pow_one f))

@[sga "1 XIII 5.4" "étaleness of U′₁ → U₁"]
private lemma kummerRootCoverMap_etale {T : Scheme.{u}}
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : ↑(Scheme.Γ.obj (Opposite.op T)))) :
    Etale (kummerRootCoverMap T n) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).2
  show (algebraMap (kummerLaurentRing T) (kummerRootAlgebra T n)).Etale
  exact RingHom.etale_algebraMap.mpr <|
    kummerPolynomial_algebra_etale (LaurentPolynomial.T 1 : kummerLaurentRing T)
      n hn (LaurentPolynomial.isUnit_T 1)
      (hnunit.map (algebraMap (↑(Scheme.Γ.obj (Opposite.op T)))
        (kummerLaurentRing T)))

private lemma kummerRootCoverMap_surjective {T : Scheme.{u}}
    [Nontrivial (↑(Scheme.Γ.obj (Opposite.op T)))] (n : ℕ) (hn : 0 < n) :
    Surjective (kummerRootCoverMap T n) :=
  ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
    (algebraMap (kummerLaurentRing T) (kummerRootAlgebra T n)))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (kummerPolynomial_algebra_faithfullyFlat
        (LaurentPolynomial.T 1 : kummerLaurentRing T) n hn))).2

private noncomputable def kummerRootScheme {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) (n : ℕ) : Scheme.{u} :=
  Limits.pullback (kummerRootCoverMap T n) (kummerRootTargetMap f)

private noncomputable def kummerRootProjection {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) (n : ℕ) : kummerRootScheme f n ⟶ T :=
  Limits.pullback.snd (kummerRootCoverMap T n) (kummerRootTargetMap f)

private noncomputable def kummerRootPullbackUnit {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) (n : ℕ) (hn : 0 < n) :
    Γ(kummerRootScheme f n, ⊤)ˣ :=
  Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
    (kummerRootTargetMap f)).appTop.hom.toMonoidHom
      (kummerRootOnSpec (T := T) n hn)

private lemma kummerRootPullbackUnit_pow {T : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) (n : ℕ) (hn : 0 < n) :
    kummerRootPullbackUnit f n hn ^ n =
      Units.map (Limits.pullback.snd (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom f := by
  have h1 : kummerRootPullbackUnit f n hn ^ n =
      Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (kummerRootOnSpec (T := T) n hn ^ n) := by
    apply Units.ext
    show (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom
        (Units.val (kummerRootOnSpec (T := T) n hn)) ^ n =
      (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom
        (Units.val (kummerRootOnSpec (T := T) n hn) ^ n)
    rw [map_pow]
  have h2 : Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (kummerRootOnSpec (T := T) n hn ^ n) =
      Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (Units.map (kummerRootCoverMap T n).appTop.hom.toMonoidHom
          (kummerLaurentCoordinate T)) :=
    congrArg (Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
      (kummerRootTargetMap f)).appTop.hom.toMonoidHom)
      (kummerRootCoverMap_coordinate_pow (T := T) n hn).symm
  have h3 : Units.map (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (Units.map (kummerRootCoverMap T n).appTop.hom.toMonoidHom
          (kummerLaurentCoordinate T)) =
      Units.map (Limits.pullback.snd (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (Units.map (kummerRootTargetMap f).appTop.hom.toMonoidHom
          (kummerLaurentCoordinate T)) := by
    apply Units.ext
    show (Limits.pullback.fst (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom
        ((kummerRootCoverMap T n).appTop.hom
          (Units.val (kummerLaurentCoordinate T))) =
      (Limits.pullback.snd (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom
        ((kummerRootTargetMap f).appTop.hom
          (Units.val (kummerLaurentCoordinate T)))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    exact congrArg (fun g => g.appTop.hom (Units.val (kummerLaurentCoordinate T)))
      (Limits.pullback.condition (f := kummerRootCoverMap T n)
        (g := kummerRootTargetMap f))
  have h4 : Units.map (Limits.pullback.snd (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom
        (Units.map (kummerRootTargetMap f).appTop.hom.toMonoidHom
          (kummerLaurentCoordinate T)) =
      Units.map (Limits.pullback.snd (kummerRootCoverMap T n)
        (kummerRootTargetMap f)).appTop.hom.toMonoidHom f :=
    congrArg (Units.map (Limits.pullback.snd (kummerRootCoverMap T n)
      (kummerRootTargetMap f)).appTop.hom.toMonoidHom)
      (kummerRootTargetMap_coordinate (T := T) f)
  exact h1.trans (h2.trans (h3.trans h4))

private lemma kummerRootWitness_pow {T V : Scheme.{u}}
    (f : Γ(T, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (q : V ⟶ kummerRootScheme f n) (g : V ⟶ T)
    (h : q ≫ kummerRootProjection f n = g) :
    Units.map g.appTop.hom.toMonoidHom f =
      Units.map q.appTop.hom.toMonoidHom (kummerRootPullbackUnit f n hn) ^ n := by
  have hcomp : Units.map (q ≫ kummerRootProjection f n).appTop.hom.toMonoidHom f =
      Units.map q.appTop.hom.toMonoidHom
        (Units.map (kummerRootProjection f n).appTop.hom.toMonoidHom f) := by
    apply Units.ext
    show (q ≫ kummerRootProjection f n).appTop.hom (f : Γ(T, ⊤)) =
      q.appTop.hom ((kummerRootProjection f n).appTop.hom (f : Γ(T, ⊤)))
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hpow := congrArg (Units.map q.appTop.hom.toMonoidHom)
    (kummerRootPullbackUnit_pow f n hn)
  calc
    Units.map g.appTop.hom.toMonoidHom f =
        Units.map (q ≫ kummerRootProjection f n).appTop.hom.toMonoidHom f := by rw [h]
    _ = Units.map q.appTop.hom.toMonoidHom
        (Units.map (kummerRootProjection f n).appTop.hom.toMonoidHom f) := hcomp
    _ = Units.map q.appTop.hom.toMonoidHom (kummerRootPullbackUnit f n hn ^ n) := hpow.symm
    _ = Units.map q.appTop.hom.toMonoidHom (kummerRootPullbackUnit f n hn) ^ n := by
      apply Units.ext
      simp only [Units.coe_map, Units.val_pow_eq_pow_val, map_pow]

private lemma additive_unit_pow {R : Type*} [CommRing R] (x : Rˣ) (n : ℕ) :
    n • (Additive.ofMul x : Additive Rˣ) = Additive.ofMul (x ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp

private lemma nat_pos_of_isUnit_cast {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (hn : IsUnit (n : R)) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro h0
  subst n
  exact (IsUnit.ne_zero hn) (by simp)

private lemma unitsPresheaf_map_additive {C : Type*} [Category C]
    (F : C ⥤ Scheme.{u}) {V U : C} (g : V ⟶ U) (x : Γ(F.obj U, ⊤)ˣ) :
    (unitsPresheaf F).map g.op (Additive.ofMul x) =
      Additive.ofMul (Units.map (F.map g).appTop.hom.toMonoidHom x) :=
  rfl

private lemma kummerRootProjection_etale {T : Scheme.{u}}
    (f : (Scheme.Γ.obj (Opposite.op T))ˣ) (n : ℕ) (hn : 0 < n)
    (hnunit : IsUnit (n : ↑(Scheme.Γ.obj (Opposite.op T)))) :
    Etale (kummerRootProjection f n) := by
  have : Etale (kummerRootCoverMap T n) := kummerRootCoverMap_etale n hn hnunit
  show Etale (Limits.pullback.snd (kummerRootCoverMap T n)
    (kummerRootTargetMap f))
  infer_instance

private lemma kummerRootProjection_surjective {T : Scheme.{u}}
    [Nontrivial (↑(Scheme.Γ.obj (Opposite.op T)))]
    (f : (Scheme.Γ.obj (Opposite.op T))ˣ) (n : ℕ) (hn : 0 < n) :
    Surjective (kummerRootProjection f n) := by
  have : Surjective (kummerRootCoverMap T n) := kummerRootCoverMap_surjective n hn
  show Surjective (Limits.pullback.snd (kummerRootCoverMap T n)
    (kummerRootTargetMap f))
  infer_instance

private lemma isUnit_natCast_appTop {X Y : Scheme.{u}} (φ : X ⟶ Y) {n : ℕ}
    (hn : IsUnit (n : Γ(Y, ⊤))) : IsUnit (n : Γ(X, ⊤)) := by
  rw [← map_natCast φ.appTop.hom n]
  exact hn.map _

private lemma kummerRootCover_mem_etalePrecoverage {T : Scheme.{u}}
    [Nontrivial (↑(Scheme.Γ.obj (Opposite.op T)))] (f : Γ(T, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (hnT : IsUnit (n : Γ(T, ⊤))) :
    (PreZeroHypercover.singleton (kummerRootProjection f n)).presieve₀ ∈
      Scheme.etalePrecoverage T := by
  apply (Scheme.presieve₀_mem_precoverage_iff _).2
  constructor
  · intro x
    obtain ⟨y, hy⟩ := (kummerRootProjection_surjective f n hn).surj x
    exact ⟨PUnit.unit, y, hy⟩
  · intro i
    simpa [PreZeroHypercover.singleton] using kummerRootProjection_etale f n hn hnT

private lemma nsmul_ofMul_unitsMap_kummerRootPullbackUnit {C : Type*} [Category C]
    (F : C ⥤ Scheme.{u}) {U V : C} (g : V ⟶ U) (f : Γ(F.obj U, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (q : F.obj V ⟶ kummerRootScheme f n) (hq : q ≫ kummerRootProjection f n = F.map g) :
    n • (Additive.ofMul (Units.map q.appTop.hom.toMonoidHom (kummerRootPullbackUnit f n hn)) :
      Additive Γ(F.obj V, ⊤)ˣ) = (unitsPresheaf F).map g.op (Additive.ofMul f) := by
  rw [← ofMul_pow, unitsPresheaf_map_additive, kummerRootWitness_pow f n hn q _ hq]

private lemma imageSieve_powerPresheaf_mem_of_subsingleton {C : Type*} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u}) (n : ℕ) {U : C}
    [Subsingleton Γ(F.obj U, ⊤)] (s : (unitsPresheaf F).obj (Opposite.op U)) :
    Presheaf.imageSieve (powerPresheaf F n) s ∈ J U := by
  have hs : s = Additive.ofMul (1 : Γ(F.obj U, ⊤)ˣ) :=
    congrArg Additive.ofMul (Subsingleton.elim (Additive.toMul s : Γ(F.obj U, ⊤)ˣ) 1)
  apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
  intro V g _
  refine ⟨Additive.ofMul (1 : Γ(F.obj V, ⊤)ˣ), ?_⟩
  rw [hs]
  show n • (Additive.ofMul (1 : Γ(F.obj V, ⊤)ˣ) : Additive (Γ(F.obj V, ⊤)ˣ)) =
    (unitsPresheaf F).map g.op (Additive.ofMul (1 : Γ(F.obj U, ⊤)ˣ))
  rw [← ofMul_pow, unitsPresheaf_map_additive]
  simp

private lemma imageSieve_powerPresheaf_mem_of_kummerRoot_factor {C : Type*} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u}) {n : ℕ} (hn : 0 < n) {U : C}
    (s : (unitsPresheaf F).obj (Opposite.op U)) (W : PreZeroHypercover U)
    (hW : Sieve.generate W.presieve₀ ∈ J U)
    (q : ∀ i, F.obj (W.X i) ⟶ kummerRootScheme (Additive.toMul s : Γ(F.obj U, ⊤)ˣ) n)
    (hq : ∀ i, q i ≫ kummerRootProjection _ n = F.map (W.f i)) :
    Presheaf.imageSieve (powerPresheaf F n) s ∈ J U := by
  apply J.superset_covering ?_ hW
  apply (Sieve.generate_le_iff _ _).2
  rintro V g ⟨i⟩
  exact ⟨Additive.ofMul (Units.map (q i).appTop.hom.toMonoidHom (kummerRootPullbackUnit _ n hn)),
    nsmul_ofMul_unitsMap_kummerRootPullbackUnit F (W.f i) _ n hn (q i) (hq i)⟩

/-- The `n`-th power map is locally surjective at `s` as soon as the Kummer root cover of the
underlying scheme (an étale cover when `n` is invertible) is refined by a covering of the site. -/
private lemma imageSieve_powerPresheaf_mem_of_refines_kummerRoot_cover {C : Type*} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u}) (n : ℕ) {U : C}
    (s : (unitsPresheaf F).obj (Opposite.op U)) (hnT : IsUnit (n : Γ(F.obj U, ⊤)))
    (H : (PreZeroHypercover.singleton
          (kummerRootProjection (Additive.toMul s : Γ(F.obj U, ⊤)ˣ) n)).presieve₀ ∈
        Scheme.etalePrecoverage (F.obj U) →
      ∃ W : PreZeroHypercover U, Sieve.generate W.presieve₀ ∈ J U ∧
        ∃ q : ∀ i, F.obj (W.X i) ⟶ kummerRootScheme (Additive.toMul s : Γ(F.obj U, ⊤)ˣ) n,
          ∀ i, q i ≫ kummerRootProjection _ n = F.map (W.f i)) :
    Presheaf.imageSieve (powerPresheaf F n) s ∈ J U := by
  by_cases hR : Nontrivial (Γ(F.obj U, ⊤))
  · have hnpos : 0 < n := nat_pos_of_isUnit_cast hnT
    obtain ⟨W, hW, q, hq⟩ := H (@kummerRootCover_mem_etalePrecoverage _ hR _ n hnpos hnT)
    exact imageSieve_powerPresheaf_mem_of_kummerRoot_factor J F hnpos s W hW q hq
  · have : Subsingleton Γ(F.obj U, ⊤) := not_nontrivial_iff_subsingleton.mp hR
    exact imageSieve_powerPresheaf_mem_of_subsingleton J F n s

private lemma bigEtale_power_isLocallySurjective
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    Presheaf.IsLocallySurjective (BigEtaleOver.topology B S hS)
      (powerPresheaf (BigEtaleOver.toScheme B S hS) n) := by
  refine ⟨fun {U} s => ?_⟩
  refine imageSieve_powerPresheaf_mem_of_refines_kummerRoot_cover _ _ n s
    (isUnit_natCast_appTop (B.inclusion.map U.hom) hn) fun h𝒰 => ?_
  obtain ⟨𝒱, h𝒱, ⟨φ⟩⟩ :=
    BigEtaleSite.exists_covering_refining_etale_cover B (T := U.left) (𝒰 := _) h𝒰
  let W : PreZeroHypercover U := {
    I₀ := 𝒱.I₀
    X i := Over.mk (𝒱.f i ≫ U.hom)
    f i := Over.homMk (𝒱.f i)
  }
  have hW : BigEtaleOver.IsCovering B S hS ⟨U, W⟩ := by
    show B.IsCovering ⟨U.left, W.map (Over.forget (B.obj S hS))⟩
    simpa [W, PreZeroHypercover.map] using h𝒱
  exact ⟨W, Precoverage.generate_mem_toGrothendieck ⟨W, rfl, hW⟩, fun i => φ.h₀ i,
    fun i => φ.w₀ i⟩

private lemma smallEtale_power_isLocallySurjective
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS)
      (powerPresheaf (SmallEtale.toScheme B S hS) n) := by
  refine ⟨fun {U} s => ?_⟩
  refine imageSieve_powerPresheaf_mem_of_refines_kummerRoot_cover _ _ n s
    (isUnit_natCast_appTop (B.inclusion.map U.obj.hom) hn) fun h𝒰 => ?_
  obtain ⟨𝒱, h𝒱, ⟨φ⟩⟩ :=
    BigEtaleSite.exists_covering_refining_etale_cover B (T := U.obj.left) (𝒰 := _) h𝒰
  let W : PreZeroHypercover U := {
    I₀ := 𝒱.I₀
    X i := ⟨Over.mk (𝒱.f i ≫ U.obj.hom), by
      show Etale (B.inclusion.map (𝒱.f i ≫ U.obj.hom))
      rw [Functor.map_comp]
      have hcoverEtale :=
        (Scheme.presieve₀_mem_precoverage_iff (𝒱.map B.inclusion)).mp
          (BigEtaleSite.IsCovering.etale h𝒱)
      have : Etale (B.inclusion.map (𝒱.f i)) := hcoverEtale.2 i
      have : Etale (B.inclusion.map U.obj.hom) := U.property
      infer_instance⟩
    f i := ObjectProperty.homMk (Over.homMk (𝒱.f i) rfl)
  }
  have hW : SmallEtale.IsCovering B S hS ⟨U, W⟩ := by
    show B.IsCovering ⟨U.obj.left,
      (W.map (SmallEtale.inclusion B S hS)).map (BigEtaleOver.forget B S hS)⟩
    have hmap : (W.map (SmallEtale.inclusion B S hS)).map (BigEtaleOver.forget B S hS) = 𝒱 := by
      ext <;> rfl
    rwa [hmap]
  exact ⟨W, Precoverage.generate_mem_toGrothendieck ⟨W, rfl, hW⟩, fun i => φ.h₀ i,
    fun i => φ.w₀ i⟩

/-- The Kummer sequence of abelian sheaves on the big étale site is short exact
when the exponent is invertible on the base. -/
@[stacks 03PL "big étale site",
  sga "1 XI 6.1" "exact sequence (big)",
  sga "4 XVIII 1.6.1" "m = O_X (Y empty)",
  sga "4 IX 3.2" "big étale site",
  sga "4½ Arcata 2.2.5" "more general",
  sga "4½ Sommes_trig 4.7" "special case",
  sga "7 IX 14.3" "special case"]
public theorem kummerSequence_shortExact_bigEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    (kummerSequence (BigEtaleOver.topology B S hS)
      (BigEtaleOver.toScheme B S hS)
      (unitsPresheaf_isSheaf_bigEtale B S hS) n).ShortExact := by
  let J := BigEtaleOver.topology B S hS
  let F := BigEtaleOver.toScheme B S hS
  have : J.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance
  exact kummerSequence_shortExact_of_isLocallySurjective J F
    (unitsPresheaf_isSheaf_bigEtale B S hS) n
    (bigEtale_power_isLocallySurjective B S hS n hn)

/-- The Kummer sequence of abelian sheaves on the small étale site is short exact
when the exponent is invertible on the base. -/
@[stacks 03PL "small étale site",
  sga "4 IX 3.2",
  sga "1 XI 6.1" "exact sequence (small)",
  sga "4½ Arcata 2.2.5",
  sga "4½ Sommes_trig 4.7" "special case",
  sga "7 IX 14.3" "special case"]
public theorem kummerSequence_shortExact_smallEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    (kummerSequence (SmallEtale.topology B S hS)
      (SmallEtale.toScheme B S hS)
      (unitsPresheaf_isSheaf_smallEtale B S hS) n).ShortExact := by
  let J := SmallEtale.topology B S hS
  let F := SmallEtale.toScheme B S hS
  have : J.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance
  exact kummerSequence_shortExact_of_isLocallySurjective J F
    (unitsPresheaf_isSheaf_smallEtale B S hS) n
    (smallEtale_power_isLocallySurjective B S hS n hn)

end AlgebraicGeometry

end
