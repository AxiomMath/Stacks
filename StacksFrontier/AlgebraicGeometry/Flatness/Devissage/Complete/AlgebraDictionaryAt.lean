module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraDictionary
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmoothFactorization

/-!
# The pointed conditions of a one-step dévissage, read on rings

A one-step dévissage `(Z, Y, i, π, 𝒢, z, y)` of `ℱ/X/S` *at* a point `x` (Stacks 05H5) carries
four conditions beyond the dévissage over the image of `x`: the local dimension of the support
of the fibre module is maximal at `x`, the chosen point `z` of the closed subscheme lies over
`x` and above `y`, the fibre of the finite morphism above `y` is the single point `z`, and the
residue field of `y` is purely transcendental over the residue field of `f x`.

All four schemes of a one-step dévissage are affine, so each of its points is a prime of the
corresponding ring of functions. This file translates the conditions that only mention points
and residue fields into the shape in which `Module.DevissageStageData.Pointed` records them, which
is the pointed half of the dictionary of Stacks 05I0 (2), in the direction geometry ⇒ algebra:

* the chosen point `y` becomes the prime `qᵢ` of `Γ(Y, ⊤)` and the chosen point `z` the prime
  `q'ᵢ` of `Γ(Z, ⊤)`;
* `π ⁻¹' {y} = {z}` becomes the uniqueness of the prime of `Γ(Z, ⊤)` above `qᵢ`, which is
  Stacks 05HZ (2);
* `κ(f x) ⊆ κ(y)` purely transcendental becomes `κ(qᵢ₋₁) ⊆ κ(qᵢ)` purely transcendental, which
  is Stacks 05HZ (1).

## Main definitions

* `AlgebraicGeometry.Scheme.residueFieldIsoOfAffine`: the residue field of a point of an affine
  scheme is the residue field of the corresponding prime of its ring of functions.
* `Ideal.ResidueField.congr`: the residue fields of two equal primes are isomorphic.

## Main results

* `AlgebraicGeometry.comap_asIdeal_isoSpec_hom_eq_iff`: **a prime of the functions on the source
  of a morphism of affine schemes contracts to the prime of a point `y` of the target exactly
  when the corresponding point of the source lies above `y`.** This is the whole dictionary
  between the point conditions of Stacks 05H5 and the prime conditions of Stacks 05HZ.
* `AlgebraicGeometry.purelyTranscendental_residueField_appTop`: **if the residue extension at a
  point of the source of a morphism of affine schemes is purely transcendental, then so is the
  extension of residue fields of the corresponding primes.** This is Stacks 05HZ (1) for one
  stage.
* `AlgebraicGeometry.OneStepDevissageAt.comap_upperPrime_appTop` and
  `AlgebraicGeometry.OneStepDevissageAt.upperPrime_unique`: **the prime of `Γ(Z, ⊤)` attached to
  the chosen point of the closed subscheme is the unique prime above the prime of `Γ(Y, ⊤)`
  attached to the chosen point of the smooth scheme.** This is Stacks 05HZ (2) for one stage.
* `AlgebraicGeometry.OneStepDevissageAt.comap_lowerPrime_appTop` and
  `AlgebraicGeometry.OneStepDevissageAt.purelyTranscendental_residueField`: the chosen prime of
  `Γ(Y, ⊤)` lies over the prime of the base and has purely transcendental residue extension
  over it.

## Implementation notes

The comparison of the scheme-theoretic residue field `X.residueField x` with `Ideal.ResidueField`
of the corresponding prime is `AlgebraicGeometry.Scheme.residueFieldIsoOfAffine`, built from
`AlgebraicGeometry.Scheme.Spec.residueFieldIso` and the residue field map of the canonical
isomorphism `X ≅ Spec Γ(X, ⊤)`. Its characterising property is
`AlgebraicGeometry.Scheme.algebraMap_residueFieldIsoOfAffine`: it carries the structure map of
the residue field of the prime to the evaluation `Γ(X, ⊤) → X.residueField x`. Pure
transcendence is then transported across it by
`Stacks.Flatness.purelyTranscendental_of_factorisation`, which takes the two comparison
isomorphisms as opaque data.

Primes are passed as variables together with an equation identifying them with
`(X.isoSpec.hom x).asIdeal`, as in `AlgebraicGeometry.asIdeal_isoSpec_hom_fiberι_eq_map`: the
`Ideal.IsPrime` instance of a prime read off a point is not found by instance synthesis, and the
prime a consumer has in hand is one it built by contraction rather than that syntactic form.
`Ideal.ResidueField.congr` moves the residue field across such an equation.

The two conditions of `Module.DevissageStageData.Pointed` that this file does **not** supply
are the two that mention the fibre module: `lowerPrime_mem_fiberSupport` and
`relativeDimension_eq_support`. Both need the support of the fibre module over the fibre ring
`κ(r) ⊗_R Γ(Y, ⊤)` to be compared with `AlgebraicGeometry.SheafOfModules.supp` of the fibre of
the module being dévissed, across the closed immersion `i` and the finite morphism `π`; the
dimension condition needs in addition that the local dimension of a support is unchanged by a
finite morphism with a singleton fibre over the point in question. The supremum half of the
dimension condition — that an algebra all of whose fibres have one dimension has that relative
dimension, which is what
`AlgebraicGeometry.OneStepDevissage.fiber_dimension` provides — is
`Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber`.

## References

* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-! ### The residue field of a prime, across an equality of primes -/

/-- The residue fields of two equal primes of a ring are canonically isomorphic. The two primes
carry separate `Ideal.IsPrime` instances, so the two residue fields are not the same type. -/
public def Ideal.ResidueField.congr {R : Type u} [CommRing R] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) : I.ResidueField ≃+* J.ResidueField where
  __ := Ideal.ResidueField.map I J (RingHom.id R) (by rwa [Ideal.comap_id])
  invFun := Ideal.ResidueField.map J I (RingHom.id R) (by rwa [Ideal.comap_id, eq_comm])
  left_inv := by
    have hc : (Ideal.ResidueField.map J I (RingHom.id R)
          (by rwa [Ideal.comap_id, eq_comm])).comp
        (Ideal.ResidueField.map I J (RingHom.id R) (by rwa [Ideal.comap_id])) =
        RingHom.id I.ResidueField :=
      Ideal.ResidueField.ringHom_ext_iff.2 (by ext a; simp [Ideal.ResidueField.map_algebraMap])
    exact RingHom.congr_fun hc
  right_inv := by
    have hc : (Ideal.ResidueField.map I J (RingHom.id R) (by rwa [Ideal.comap_id])).comp
        (Ideal.ResidueField.map J I (RingHom.id R)
          (by rwa [Ideal.comap_id, eq_comm])) = RingHom.id J.ResidueField :=
      Ideal.ResidueField.ringHom_ext_iff.2 (by ext a; simp [Ideal.ResidueField.map_algebraMap])
    exact RingHom.congr_fun hc

/-- `Ideal.ResidueField.congr` commutes with the structure maps of the two residue fields. -/
@[simp]
public lemma Ideal.ResidueField.congr_algebraMap {R : Type u} [CommRing R] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) (a : R) :
    Ideal.ResidueField.congr h (algebraMap R I.ResidueField a) =
      algebraMap R J.ResidueField a :=
  Ideal.ResidueField.map_algebraMap I J (RingHom.id R) _ a

namespace AlgebraicGeometry

/-! ### Primes and points of an affine scheme -/

/-- A point of an affine scheme corresponds to a prime exactly when the prime corresponds back to
the point. -/
private theorem asIdeal_isoSpec_hom_eq_iff_inv {Z : Scheme.{u}} [IsAffine Z] (z : Z)
    (p : Ideal Γ(Z, ⊤)) [hp : p.IsPrime] :
    (Z.isoSpec.hom z).asIdeal = p ↔ Z.isoSpec.inv (⟨p, hp⟩ : Spec Γ(Z, ⊤)) = z := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show (⟨p, hp⟩ : Spec Γ(Z, ⊤)) = Z.isoSpec.hom z from PrimeSpectrum.ext h.symm]
    exact (Scheme.homeoOfIso Z.isoSpec).symm_apply_apply z
  · rw [← h]
    exact congrArg PrimeSpectrum.asIdeal ((Scheme.homeoOfIso Z.isoSpec).apply_symm_apply _)

/-- **A prime of the functions on the source of a morphism of affine schemes contracts to the
prime of a point of the target exactly when the corresponding point of the source lies above
that point.**

This is the dictionary between the conditions on points of Stacks 05H5 and the conditions on
primes of Stacks 05HZ: the uniqueness of the prime above `qᵢ` is the statement that the fibre of
`π` above `y` is a single point, and the contraction conditions are the statements that the
chosen points are mapped to one another. -/
public theorem comap_asIdeal_isoSpec_hom_eq_iff {Z Y : Scheme.{u}} [IsAffine Z] [IsAffine Y]
    (π : Z ⟶ Y) (y : Y) (qY : Ideal Γ(Y, ⊤)) [qY.IsPrime]
    (hqY : (Y.isoSpec.hom y).asIdeal = qY) (p : Ideal Γ(Z, ⊤)) [hp : p.IsPrime] :
    p.comap π.appTop.hom = qY ↔ π (Z.isoSpec.inv ⟨p, hp⟩) = y := by
  have key : Spec.map π.appTop (⟨p, hp⟩ : Spec Γ(Z, ⊤)) =
      Y.isoSpec.hom (π (Z.isoSpec.inv ⟨p, hp⟩)) := by
    have h := congrArg (fun k : Z ⟶ Spec Γ(Y, ⊤) ↦ k (Z.isoSpec.inv ⟨p, hp⟩))
      (Scheme.isoSpec_hom_naturality π)
    simp only [Scheme.Hom.comp_apply] at h
    rwa [show Z.isoSpec.hom (Z.isoSpec.inv ⟨p, hp⟩) = ⟨p, hp⟩ from
      (Scheme.homeoOfIso Z.isoSpec).apply_symm_apply _] at h
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hpt : Spec.map π.appTop (⟨p, hp⟩ : Spec Γ(Z, ⊤)) = Y.isoSpec.hom y :=
      PrimeSpectrum.ext (h.trans hqY.symm)
    rw [key] at hpt
    exact (Scheme.homeoOfIso Y.isoSpec).injective hpt
  · rw [h] at key
    exact (congrArg PrimeSpectrum.asIdeal key).trans hqY

/-- The prime attached to a point of the source of a morphism of affine schemes contracts to the
prime attached to its image. -/
public theorem comap_asIdeal_isoSpec_hom {Z Y : Scheme.{u}} [IsAffine Z] [IsAffine Y]
    (π : Z ⟶ Y) (z : Z) (y : Y) (hzy : π z = y)
    (qZ : Ideal Γ(Z, ⊤)) [hqZp : qZ.IsPrime] (hqZ : (Z.isoSpec.hom z).asIdeal = qZ)
    (qY : Ideal Γ(Y, ⊤)) [qY.IsPrime] (hqY : (Y.isoSpec.hom y).asIdeal = qY) :
    qZ.comap π.appTop.hom = qY := by
  refine (comap_asIdeal_isoSpec_hom_eq_iff π y qY hqY qZ).2 ?_
  rw [(asIdeal_isoSpec_hom_eq_iff_inv z qZ).1 hqZ]
  exact hzy

/-- **A prime of the functions on the source of a morphism of affine schemes whose fibre above a
point is a single point, contracting to the prime of that point, is the prime of that single
point.** This is the uniqueness clause of Stacks 05HZ (2), read off the singleton fibre of
Stacks 05H5 (3). -/
public theorem eq_of_comap_asIdeal_isoSpec_hom_eq {Z Y : Scheme.{u}} [IsAffine Z] [IsAffine Y]
    (π : Z ⟶ Y) (z : Z) (y : Y) (hfib : π ⁻¹' {y} = {z})
    (qZ : Ideal Γ(Z, ⊤)) [qZ.IsPrime] (hqZ : (Z.isoSpec.hom z).asIdeal = qZ)
    (qY : Ideal Γ(Y, ⊤)) [qY.IsPrime] (hqY : (Y.isoSpec.hom y).asIdeal = qY)
    (p : Ideal Γ(Z, ⊤)) [hp : p.IsPrime] (h : p.comap π.appTop.hom = qY) : p = qZ := by
  have hmem : Z.isoSpec.inv (⟨p, hp⟩ : Spec Γ(Z, ⊤)) ∈ π ⁻¹' {y} :=
    (comap_asIdeal_isoSpec_hom_eq_iff π y qY hqY p).1 h
  rw [hfib] at hmem
  exact ((asIdeal_isoSpec_hom_eq_iff_inv z p).2 hmem).symm.trans hqZ

/-! ### Residue fields of points of an affine scheme -/

/-- Evaluation at a point is unchanged by the canonical identification of the residue fields of
two equal points. -/
public lemma Scheme.Γevaluation_residueFieldCongr {X : Scheme.{u}} {a b : X} (h : a = b) :
    X.Γevaluation a ≫ (X.residueFieldCongr h).hom = X.Γevaluation b := by
  subst h
  simp

/-- **The residue field of a point of an affine scheme is the residue field of the corresponding
prime of its ring of functions.** -/
public def Scheme.residueFieldIsoOfAffine (X : Scheme.{u}) [IsAffine X] (x : X) :
    letI := (X.isoSpec.hom x).isPrime
    CommRingCat.of (X.isoSpec.hom x).asIdeal.ResidueField ≅ X.residueField x :=
  letI := (X.isoSpec.hom x).isPrime
  (Scheme.Spec.residueFieldIso Γ(X, ⊤) (X.isoSpec.hom x)).symm ≪≫
    asIso (X.isoSpec.hom.residueFieldMap x)

/-- **The characterising property of `AlgebraicGeometry.Scheme.residueFieldIsoOfAffine`:** it
carries the structure map of the residue field of the prime to evaluation at the point. -/
public lemma Scheme.algebraMap_residueFieldIsoOfAffine (X : Scheme.{u}) [IsAffine X] (x : X) :
    letI := (X.isoSpec.hom x).isPrime
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (X.isoSpec.hom x).asIdeal.ResidueField) ≫
        (X.residueFieldIsoOfAffine x).hom = X.Γevaluation x := by
  let _ := (X.isoSpec.hom x).isPrime
  change CommRingCat.ofHom (algebraMap Γ(X, ⊤) (X.isoSpec.hom x).asIdeal.ResidueField) ≫
      ((Scheme.Spec.residueFieldIso Γ(X, ⊤) (X.isoSpec.hom x)).symm ≪≫
        asIso (X.isoSpec.hom.residueFieldMap x)).hom = _
  rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, ← Category.assoc,
    Scheme.Spec.algebraMap_residueFieldIso_inv]
  have h : (Spec Γ(X, ⊤)).presheaf.germ ⊤ (X.isoSpec.hom x) trivial ≫
      (Spec Γ(X, ⊤)).residue (X.isoSpec.hom x) =
      (Spec Γ(X, ⊤)).Γevaluation (X.isoSpec.hom x) := rfl
  rw [Category.assoc (Scheme.ΓSpecIso Γ(X, ⊤)).inv, h, Scheme.Γevaluation_naturality]
  change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ Scheme.Hom.appTop X.toSpecΓ ≫ X.Γevaluation x = _
  rw [← Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.id_comp]

/-- `AlgebraicGeometry.Scheme.residueFieldIsoOfAffine`, precomposed with the identification of
the residue field of a prime equal to that of the point, carries the structure map to evaluation
at the point. -/
public lemma Scheme.algebraMap_congr_residueFieldIsoOfAffine (X : Scheme.{u}) [IsAffine X]
    (x : X) (p : Ideal Γ(X, ⊤)) [p.IsPrime] (hp : (X.isoSpec.hom x).asIdeal = p) :
    letI := (X.isoSpec.hom x).isPrime
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) p.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.congr hp.symm).toRingHom ≫
        (X.residueFieldIsoOfAffine x).hom = X.Γevaluation x := by
  let _ := (X.isoSpec.hom x).isPrime
  rw [← Category.assoc, show CommRingCat.ofHom (algebraMap Γ(X, ⊤) p.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.congr hp.symm).toRingHom =
      CommRingCat.ofHom (algebraMap Γ(X, ⊤) (X.isoSpec.hom x).asIdeal.ResidueField) by
    ext a; exact Ideal.ResidueField.congr_algebraMap hp.symm a]
  exact X.algebraMap_residueFieldIsoOfAffine x

/-! ### Pure transcendence of a residue extension, read on rings -/

/-- **Stacks 05HZ (1) for one stage.** For a morphism `g : Y ⟶ S` of affine schemes, a point `y`
of `Y` with image `s`, and the primes `r` of `Γ(S, ⊤)` and `p` of `Γ(Y, ⊤)` corresponding to `s`
and to `y`, the scheme-theoretic residue extension `κ(s) ⊆ κ(y)` being purely transcendental
gives that the extension `κ(r) ⊆ κ(p)` of residue fields of primes is purely transcendental.

The algebra structure on the right is the one `Module.DevissageStageData.Pointed` records,
induced by `g` on functions; on the left it is the one
`AlgebraicGeometry.OneStepDevissageAt` records. -/
public theorem purelyTranscendental_residueField_appTop {Y S : Scheme.{u}} [IsAffine Y]
    [IsAffine S] (g : Y ⟶ S) (y : Y) (s : S) (hgy : g y = s)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r)
    (p : Ideal Γ(Y, ⊤)) [p.IsPrime] (hp : (Y.isoSpec.hom y).asIdeal = p)
    (hcomap : r = p.comap g.appTop.hom)
    (hPT : letI := ((S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (Y.residueField y)) :
    letI := (Ideal.ResidueField.map r p g.appTop.hom hcomap).toAlgebra
    PurelyTranscendental r.ResidueField p.ResidueField := by
  let _ := (S.isoSpec.hom s).isPrime
  let _ := (Y.isoSpec.hom y).isPrime
  let _ := ((S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y).hom.toAlgebra
  let _ := (Ideal.ResidueField.map r p g.appTop.hom hcomap).toAlgebra
  let b : CommRingCat.of r.ResidueField ⟶ S.residueField s :=
    CommRingCat.ofHom (Ideal.ResidueField.congr hr.symm).toRingHom ≫
      (S.residueFieldIsoOfAffine s).hom
  let m : S.residueField s ⟶ Y.residueField y :=
    (S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y
  let c : Y.residueField y ⟶ CommRingCat.of p.ResidueField :=
    (Y.residueFieldIsoOfAffine y).inv ≫
      CommRingCat.ofHom (Ideal.ResidueField.congr hp).toRingHom
  have hb : Function.Bijective b.hom :=
    (ConcreteCategory.bijective_of_isIso (S.residueFieldIsoOfAffine s).hom).comp
      (Ideal.ResidueField.congr hr.symm).bijective
  have hc : Function.Bijective c.hom :=
    (Ideal.ResidueField.congr hp).bijective.comp
      (ConcreteCategory.bijective_of_isIso (Y.residueFieldIsoOfAffine y).inv)
  have hsquare : CommRingCat.ofHom (algebraMap Γ(S, ⊤) r.ResidueField) ≫ b ≫ m ≫ c =
      g.appTop ≫ CommRingCat.ofHom (algebraMap Γ(Y, ⊤) p.ResidueField) := by
    have hb' : CommRingCat.ofHom (algebraMap Γ(S, ⊤) r.ResidueField) ≫ b = S.Γevaluation s :=
      S.algebraMap_congr_residueFieldIsoOfAffine s r hr
    have hm' : S.Γevaluation s ≫ m = g.appTop ≫ Y.Γevaluation y := by
      change S.Γevaluation s ≫ (S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y = _
      rw [← Scheme.Γevaluation_residueFieldCongr hgy]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact Scheme.Γevaluation_naturality g y
    have hc' : Y.Γevaluation y ≫ c =
        CommRingCat.ofHom (algebraMap Γ(Y, ⊤) p.ResidueField) := by
      change Y.Γevaluation y ≫ (Y.residueFieldIsoOfAffine y).inv ≫
        CommRingCat.ofHom (Ideal.ResidueField.congr hp).toRingHom = _
      have hinv : Y.Γevaluation y ≫ (Y.residueFieldIsoOfAffine y).inv =
          CommRingCat.ofHom
            (algebraMap Γ(Y, ⊤) (Y.isoSpec.hom y).asIdeal.ResidueField) :=
        Iso.comp_inv_eq _ |>.2 (Y.algebraMap_residueFieldIsoOfAffine y).symm
      rw [← Category.assoc, hinv]
      ext a
      exact Ideal.ResidueField.congr_algebraMap hp a
    rw [← Category.assoc, hb', ← Category.assoc, hm', Category.assoc, hc']
  refine Stacks.Flatness.purelyTranscendental_of_factorisation b hb m c hc
    (RingEquiv.refl (S.residueField s)) (RingEquiv.refl (Y.residueField y))
    (fun _ => rfl) (fun a => ?_) hPT
  have hmap : (Ideal.ResidueField.map r p g.appTop.hom hcomap) = (b ≫ m ≫ c).hom := by
    refine Ideal.ResidueField.ringHom_ext_iff.2 (RingHom.ext fun a₀ => ?_)
    have h2 := congrArg (fun φ : Γ(S, ⊤) ⟶ CommRingCat.of p.ResidueField => φ.hom a₀) hsquare
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h2 ⊢
    rw [Ideal.ResidueField.map_algebraMap]
    exact h2.symm
  exact RingHom.congr_fun hmap a

/-! ### The pointed data of a one-step dévissage, read on rings -/

namespace OneStepDevissageAt

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- The prime attached to the chosen point of the closed subscheme contracts, along the finite
morphism, to the prime attached to the chosen point of the smooth scheme. This is the second
half of Stacks 05HZ (2) for one stage. -/
public theorem comap_upperPrime_appTop (D : OneStepDevissageAt f F x)
    (qZ : Ideal Γ(D.toOneStepDevissage.Z, ⊤)) [qZ.IsPrime]
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [qY.IsPrime]
    (hqZ : letI := D.toOneStepDevissage.affine_Z
      (D.toOneStepDevissage.Z.isoSpec.hom D.z).asIdeal = qZ)
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY) :
    qZ.comap D.toOneStepDevissage.π.appTop.hom = qY :=
  let := D.toOneStepDevissage.affine_Y
  let := D.toOneStepDevissage.affine_Z
  comap_asIdeal_isoSpec_hom D.toOneStepDevissage.π D.z D.y D.π_z qZ hqZ qY hqY

/-- **Stacks 05HZ (2) for one stage.** The prime attached to the chosen point of the closed
subscheme is the *only* prime of the functions on that subscheme contracting to the prime
attached to the chosen point of the smooth scheme. This is the ring-theoretic reading of
`AlgebraicGeometry.OneStepDevissageAt.fiber_eq_singleton`. -/
public theorem upperPrime_unique (D : OneStepDevissageAt f F x)
    (qZ : Ideal Γ(D.toOneStepDevissage.Z, ⊤)) [qZ.IsPrime]
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [qY.IsPrime]
    (hqZ : letI := D.toOneStepDevissage.affine_Z
      (D.toOneStepDevissage.Z.isoSpec.hom D.z).asIdeal = qZ)
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (p : Ideal Γ(D.toOneStepDevissage.Z, ⊤)) (hp : p.IsPrime)
    (h : p.comap D.toOneStepDevissage.π.appTop.hom = qY) : p = qZ :=
  let := D.toOneStepDevissage.affine_Y
  let := D.toOneStepDevissage.affine_Z
  let := hp
  eq_of_comap_asIdeal_isoSpec_hom_eq D.toOneStepDevissage.π D.z D.y D.fiber_eq_singleton
    qZ hqZ qY hqY p h

/-- The prime attached to the chosen point of the smooth scheme contracts to the prime attached
to the image of the point at which the dévissage is taken: it lies over the base prime. -/
public theorem comap_lowerPrime_appTop (D : OneStepDevissageAt f F x)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r) :
    qY.comap D.toOneStepDevissage.g.appTop.hom = r :=
  let := D.toOneStepDevissage.affine_Y
  let := D.toOneStepDevissage.affine_S
  comap_asIdeal_isoSpec_hom D.toOneStepDevissage.g D.y (f x) D.g_y qY hqY r hr

/-- **Stacks 05HZ (1) for one stage.** The residue field of the prime attached to the chosen
point of the smooth scheme is purely transcendental over the residue field of the prime attached
to the image of the point at which the dévissage is taken. -/
public theorem purelyTranscendental_residueField (D : OneStepDevissageAt f F x)
    (qY : Ideal Γ(D.toOneStepDevissage.Y, ⊤)) [qY.IsPrime]
    (hqY : letI := D.toOneStepDevissage.affine_Y
      (D.toOneStepDevissage.Y.isoSpec.hom D.y).asIdeal = qY)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : letI := D.toOneStepDevissage.affine_S
      (S.isoSpec.hom (f x)).asIdeal = r)
    (hcomap : r = qY.comap D.toOneStepDevissage.g.appTop.hom) :
    letI := (Ideal.ResidueField.map r qY
      D.toOneStepDevissage.g.appTop.hom hcomap).toAlgebra
    PurelyTranscendental r.ResidueField qY.ResidueField :=
  let := D.toOneStepDevissage.affine_Y
  let := D.toOneStepDevissage.affine_S
  purelyTranscendental_residueField_appTop D.toOneStepDevissage.g D.y (f x) D.g_y r hr
    qY hqY hcomap D.residueField_purelyTranscendental

end OneStepDevissageAt

end AlgebraicGeometry

end
