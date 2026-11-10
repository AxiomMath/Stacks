module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting

/-!
# The spectrum of the étale local ring as an object of the site

Let `Y` be an algebraic space over a scheme `S` and `ȳ` a geometric point of `Y`.  The étale
local ring `𝒪_{Y, ȳ}` of `AlgebraicGeometry.Space.etaleLocalRing` is a colimit over the small
étale neighbourhoods of `ȳ`, whose objects live in `Type (u + 1)`, so it is a ring in
`Type (u + 1)`.  By Stacks 04KF it is isomorphic to the strict henselization of the local ring
of any étale neighbourhood, which lives in `Type u`.  This file fixes such a model `A` of
`𝒪_{Y, ȳ}` in `Type u`, attached to a chosen affine étale neighbourhood `(U₀, ū₀)`, and shows
that when `Y` is locally Noetherian `Spec A` is an object of the big fppf site, flat over `U₀`.
The morphism `Spec A ⟶ U₀ ⟶ Y` is the canonical morphism `Spec 𝒪_{Y, ȳ} ⟶ Y`: on functions on
`U₀` it is the germ map at `ȳ`.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleNeighborhood`: a chosen affine small étale neighbourhood
  of `ȳ`.
* `AlgebraicGeometry.Space.etaleLocalRingModel`: the model `A` of `𝒪_{Y, ȳ}` in `Type u`, with
  `AlgebraicGeometry.Space.etaleLocalRingModelEquiv : A ≃+* 𝒪_{Y, ȳ}`.
* `AlgebraicGeometry.Space.etaleLocalRingModelGerm`: the germ map `Γ(U₀, 𝒪) ⟶ A`.
* `AlgebraicGeometry.Space.etaleLocalRingModelEval` and
  `AlgebraicGeometry.Space.etaleLocalRingSpecGeometricPoint`: the evaluation `A ⟶ κ(ȳ)` at the
  closed point and the morphism `Spec κ(ȳ) ⟶ Spec A` it defines.
* `AlgebraicGeometry.Space.etaleLocalRingSpecObject` and
  `AlgebraicGeometry.Space.etaleLocalRingSpecToChart`: `Spec A` as an object of the site and its
  morphism to `U₀`.

## Main results

* `Cardinal.mk_quotient_maximalIdeal_pow_le` and `Cardinal.mk_le_max_residueField_pow_aleph0`:
  for a Noetherian local ring `A` with residue field `κ`, `#(A ⧸ 𝔪 ⁿ) ≤ max ℵ₀ #κ` and
  `#A ≤ (max ℵ₀ #κ) ^ ℵ₀`, by the Krull intersection theorem.  The finite-length bound they
  rest on is `AlgebraicGeometry.Space.cardinalMk_le_max_residueField_of_isFiniteLength`.
* `AlgebraicGeometry.Space.etaleLocalRingModelEquiv_germ`: the model germ map followed by the
  comparison is the germ map of the étale local ring.
* `AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRingModel` and
  `AlgebraicGeometry.Space.contains_spec_etaleLocalRingModel`: for `Y` locally Noetherian, `A`
  is Noetherian and `Spec A` lies in the site; the cardinality bound is
  `Cardinal.mk_le_max_residueField_pow_aleph0`, the residue field of `A` being a subfield of
  the field of `ȳ`.
* `AlgebraicGeometry.Space.flat_etaleLocalRingSpecToChart`: `Spec A ⟶ U₀` is flat.
* `AlgebraicGeometry.Space.etaleLocalRingSpecGeometricPoint_comp`: the closed point of `Spec A`
  lies over `ȳ`: `Spec κ(ȳ) ⟶ Spec A ⟶ U₀` is the lift of `ȳ` to `U₀`.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

/-! ### The cardinality of a Noetherian local ring -/

namespace Cardinal

open Cardinal

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The quotient of a Noetherian local ring by a power of its maximal ideal has cardinality at
most the maximum of `ℵ₀` and the cardinality of the residue field. -/
theorem mk_quotient_maximalIdeal_pow_le (n : ℕ) :
    #(A ⧸ maximalIdeal A ^ n) ≤ max ℵ₀ #(ResidueField A) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (A ⧸ maximalIdeal A ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact (Cardinal.mk_le_aleph0).trans (le_max_left _ _)
  have hne : maximalIdeal A ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self hn.ne')
  have : Nontrivial (A ⧸ maximalIdeal A ^ n) := Ideal.Quotient.nontrivial_iff.2 hne
  have : IsLocalRing (A ⧸ maximalIdeal A ^ n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax := map_maximalIdeal_of_surjective (Ideal.Quotient.mk (maximalIdeal A ^ n))
    Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (A ⧸ maximalIdeal A ^ n) := Ideal.Quotient.isNoetherianRing _
  have : IsArtinianRing (A ⧸ maximalIdeal A ^ n) := by
    refine (isArtinianRing_iff_isNilpotent_maximalIdeal _).2 ⟨n, ?_⟩
    rw [← hmax, ← Ideal.map_pow, Ideal.map_quotient_self]
    rfl
  refine (AlgebraicGeometry.Space.cardinalMk_le_max_residueField_of_isFiniteLength
    ((isArtinianRing_iff_isFiniteLength _).1 inferInstance)).trans (max_le_max le_rfl ?_)
  have : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ n)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine Cardinal.mk_le_of_surjective (f := ResidueField.map (Ideal.Quotient.mk _)) fun z => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨residue A a, ResidueField.map_residue _ a⟩

/-- **The cardinality of a Noetherian local ring** is at most `(max ℵ₀ #κ) ^ ℵ₀`, `κ` its
residue field: by the Krull intersection theorem the ring embeds in `∏ₙ A ⧸ 𝔪 ⁿ`. -/
theorem mk_le_max_residueField_pow_aleph0 :
    #A ≤ (max ℵ₀ #(ResidueField A)) ^ ℵ₀ := by
  let ι : A → ∀ n : ULift.{u} ℕ, A ⧸ maximalIdeal A ^ n.down := fun a n => Ideal.Quotient.mk _ a
  have hι : Function.Injective ι := by
    intro a b hab
    rw [← sub_eq_zero]
    have hmem : ∀ n : ℕ, a - b ∈ maximalIdeal A ^ n := fun n =>
      Ideal.Quotient.eq.1 (congrFun hab ⟨n⟩)
    have : a - b ∈ (⨅ n : ℕ, maximalIdeal A ^ n) := Submodule.mem_iInf _ |>.2 hmem
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top]
      at this
  calc #A ≤ #(∀ n : ULift.{u} ℕ, A ⧸ maximalIdeal A ^ n.down) :=
        Cardinal.mk_le_of_injective hι
    _ = Cardinal.prod fun n : ULift.{u} ℕ => #(A ⧸ maximalIdeal A ^ n.down) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : ULift.{u} ℕ => max ℵ₀ #(ResidueField A) :=
        Cardinal.prod_le_prod _ _ fun n => mk_quotient_maximalIdeal_pow_le n.down
    _ = (max ℵ₀ #(ResidueField A)) ^ ℵ₀ := by
        rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_uLift,
          Cardinal.mk_nat, Cardinal.lift_aleph0]

end Cardinal

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Y : AlgebraicSpaces B S hS) (y : GeometricPoint B S hS Y.1)

/-- A chosen small étale neighbourhood of `ȳ` whose chart is an affine scheme. -/
def affineEtaleNeighborhood : SmallEtaleNeighborhood y :=
  (exists_smallEtaleNeighborhoodHom_isAffine B S hS Y y
    (nonempty_smallEtaleNeighborhood Y.2 y).some).choose

/-- The chart `U₀` of the chosen affine étale neighbourhood of `ȳ` is an affine scheme. -/
instance isAffine_affineEtaleNeighborhood :
    IsAffine (chartScheme (affineEtaleNeighborhood Y y).chart) :=
  (exists_smallEtaleNeighborhoodHom_isAffine B S hS Y y
    (nonempty_smallEtaleNeighborhood Y.2 y).some).choose_spec.choose_spec

/-- **A model of the étale local ring `𝒪_{Y, ȳ}` in `Type u`**: the strict henselization of the
local ring of the chosen affine étale neighbourhood, which is `𝒪_{Y, ȳ}` by Stacks 04KF. -/
abbrev etaleLocalRingModel : Type u :=
  (chartHenselizationTower B S hS Y.1 (affineEtaleNeighborhood Y y)).strictHenselization

/-- The model of the étale local ring is the étale local ring (Stacks 04KF). -/
def etaleLocalRingModelEquiv : etaleLocalRingModel Y y ≃+* etaleLocalRing B S hS Y.1 y :=
  chartStrictHenselizationEquiv B S hS Y.1 Y.2 (affineEtaleNeighborhood Y y)

/-- The germ map `Γ(U₀, 𝒪) ⟶ A` at `ȳ` on the chosen affine neighbourhood: the germ at the point
under `ȳ`, followed by the structure map of the strict henselization. -/
def etaleLocalRingModelGerm :
    Γ(chartScheme (affineEtaleNeighborhood Y y).chart, ⊤) →+* etaleLocalRingModel Y y :=
  (algebraMap (chartLocalRing B S hS Y.1 (affineEtaleNeighborhood Y y))
    (etaleLocalRingModel Y y)).comp
    ((chartScheme (affineEtaleNeighborhood Y y).chart).presheaf.germ ⊤
      (chartPoint B S hS Y.1 (affineEtaleNeighborhood Y y)) trivial).hom

/-- The model germ map, followed by the comparison with the étale local ring, is the germ map of
the étale local ring on the chosen neighbourhood. -/
theorem etaleLocalRingModelEquiv_germ (a : Γ(chartScheme (affineEtaleNeighborhood Y y).chart, ⊤)) :
    etaleLocalRingModelEquiv Y y (etaleLocalRingModelGerm Y y a) =
      etaleLocalRingGerm B S hS Y.1 y (op (affineEtaleNeighborhood Y y)) a :=
  chartLocalRingToEtaleLocalRing_germ B S hS Y.1 Y.2 (affineEtaleNeighborhood Y y) a

/-- The model germ map is flat: a localization followed by a strict henselization. -/
theorem flat_etaleLocalRingModelGerm : (etaleLocalRingModelGerm Y y).Flat := by
  let V := affineEtaleNeighborhood Y y
  let X := chartScheme V.chart
  let x := chartPoint B S hS Y.1 V
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have h₁ : (X.presheaf.germ ⊤ x trivial).hom.Flat :=
    RingHom.flat_algebraMap_iff.1 (IsLocalization.flat _
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl)
  have h₂ : (algebraMap (chartLocalRing B S hS Y.1 V) (etaleLocalRingModel Y y)).Flat := by
    let T := chartHenselizationTower B S hS Y.1 V
    have : Module.Flat (chartLocalRing B S hS Y.1 V) T.henselization := T.henselizationIsFlat
    have : Module.Flat T.henselization T.strictHenselization := T.strictHenselizationIsFlat
    have : IsScalarTower (chartLocalRing B S hS Y.1 V) T.henselization T.strictHenselization :=
      T.isScalarTower
    exact RingHom.flat_algebraMap_iff.2
      (Module.Flat.trans (chartLocalRing B S hS Y.1 V) T.henselization T.strictHenselization)
  exact h₁.comp h₂

variable {Y y} in
/-- For `Y` locally Noetherian the model of the étale local ring is Noetherian. -/
theorem isNoetherianRing_etaleLocalRingModel
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsNoetherianRing (etaleLocalRingModel Y y) :=
  have := isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y.1 Y.2 hY y
  isNoetherianRing_of_ringEquiv _ (etaleLocalRingModelEquiv Y y).symm

/-- The residue field of the model of the étale local ring is no larger than the field of the
geometric point: it is a separable closure inside that field. -/
theorem mk_residueField_etaleLocalRingModel_le :
    Cardinal.mk (ResidueField (etaleLocalRingModel Y y)) ≤ Cardinal.mk y.val.carrier := by
  let V := affineEtaleNeighborhood Y y
  let T := chartHenselizationTower B S hS Y.1 V
  obtain ⟨e, -⟩ := T.strictHenselizationIsHenselization.exists_residueFieldEquiv
  exact (Cardinal.mk_congr e.symm.toEquiv).le.trans
    (Cardinal.mk_le_of_injective Subtype.val_injective)

variable {Y y} in
/-- **The spectrum of the étale local ring is an object of the site**, for `Y` locally
Noetherian: its model `A` is a Noetherian local ring whose residue field embeds in the field of
`ȳ`, so `#A ≤ (max ℵ₀ #κ(ȳ)) ^ ℵ₀`, which the strong limit cutoff of the site exceeds. -/
theorem contains_spec_etaleLocalRingModel
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    B.Contains (Spec (.of (etaleLocalRingModel Y y))) := by
  have := isNoetherianRing_etaleLocalRingModel (y := y) hY
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ y.val.contained
    ((Cardinal.mk_le_max_residueField_pow_aleph0).trans ?_)
  rw [Scheme.size_Spec]
  exact Cardinal.power_le_power_right (max_le_max le_rfl
    (mk_residueField_etaleLocalRingModel_le Y y))

/-- The canonical morphism `Spec A ⟶ U₀` from the spectrum of the model of the étale local ring
to the chart of the chosen affine neighbourhood: the spectrum of the germ map. -/
def etaleLocalRingSpecToChartScheme :
    Spec (.of (etaleLocalRingModel Y y)) ⟶ chartScheme (affineEtaleNeighborhood Y y).chart :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingModelGerm Y y)) ≫
    (chartScheme (affineEtaleNeighborhood Y y).chart).isoSpec.inv

/-- The canonical morphism `Spec A ⟶ U₀` is flat. -/
instance flat_etaleLocalRingSpecToChartScheme : Flat (etaleLocalRingSpecToChartScheme Y y) :=
  haveI : Flat (Spec.map (CommRingCat.ofHom (etaleLocalRingModelGerm Y y))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (flat_etaleLocalRingModelGerm Y y)
  inferInstanceAs (Flat (_ ≫ _))

/-- On functions, `Spec A ⟶ U₀` is the germ map. -/
theorem etaleLocalRingSpecToChartScheme_appTop
    (a : Γ(chartScheme (affineEtaleNeighborhood Y y).chart, ⊤)) :
    (etaleLocalRingSpecToChartScheme Y y).appTop a =
      (Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).inv (etaleLocalRingModelGerm Y y a) := by
  rw [etaleLocalRingSpecToChartScheme, Scheme.Hom.comp_appTop,
    Stacks.RelativeSpec.isoSpec_inv_appTop]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (etaleLocalRingModelGerm Y y))).symm a

/-- **The evaluation `A ⟶ κ(ȳ)` at the closed point.**  The residue map of the model `A` of the
étale local ring, followed by the identification of its residue field with the separable
closure of `κ(u₀)` inside the field `κ(ȳ)` of the geometric point. -/
def etaleLocalRingModelEval : etaleLocalRingModel Y y →+* y.val.carrier :=
  (IntermediateField.val (separableClosure (ResidueField (chartLocalRing B S hS Y.1
      (affineEtaleNeighborhood Y y)))
      (chartGeometricPoint (affineEtaleNeighborhood Y y)).residueField)).toRingHom.comp
    ((chartHenselizationTower B S hS Y.1
      (affineEtaleNeighborhood Y y)).strictHenselizationResidueEquiv.symm.toRingHom.comp
      (residue (etaleLocalRingModel Y y)))

/-- The evaluation at the closed point kills the maximal ideal. -/
theorem etaleLocalRingModelEval_eq_zero {a : etaleLocalRingModel Y y}
    (ha : a ∈ maximalIdeal (etaleLocalRingModel Y y)) : etaleLocalRingModelEval Y y a = 0 := by
  simp [etaleLocalRingModelEval, (residue_eq_zero_iff a).2 ha]

/-- On the local ring `𝒪_{U₀, u₀}` of the chart, the evaluation at the closed point is the
evaluation of germs at the geometric point `Spec κ(ȳ) ⟶ U₀`. -/
theorem etaleLocalRingModelEval_algebraMap
    (r : chartLocalRing B S hS Y.1 (affineEtaleNeighborhood Y y)) :
    etaleLocalRingModelEval Y y (algebraMap _ (etaleLocalRingModel Y y) r) =
      Scheme.stalkClosedPointTo (chartGeometricPoint (affineEtaleNeighborhood Y y)).hom r := by
  let T := chartHenselizationTower B S hS Y.1 (affineEtaleNeighborhood Y y)
  let k := ResidueField (chartLocalRing B S hS Y.1 (affineEtaleNeighborhood Y y))
  let K := (chartGeometricPoint (affineEtaleNeighborhood Y y)).residueField
  change ((T.strictHenselizationResidueEquiv.symm
    (residue T.strictHenselization (algebraMap _ T.strictHenselization r)) : separableClosure k K) :
      K) = _
  rw [← T.strictHenselizationResidueEquiv_residue r, RingEquiv.symm_apply_apply]
  change algebraMap k K (residue _ r) = _
  exact congrArg (fun φ : (chartScheme (affineEtaleNeighborhood Y y).chart).presheaf.stalk
      (chartPoint B S hS Y.1 (affineEtaleNeighborhood Y y)) ⟶ CommRingCat.of K => φ r)
    (Scheme.residue_descResidueField
      (f := Scheme.stalkClosedPointTo (chartGeometricPoint (affineEtaleNeighborhood Y y)).hom))

/-- **The closed point of `Spec 𝒪_{Y, ȳ}` over `ȳ`**: the morphism `Spec κ(ȳ) ⟶ Spec A` given by
the evaluation at the closed point. -/
def etaleLocalRingSpecGeometricPoint :
    Spec (.of y.val.carrier) ⟶ Spec (.of (etaleLocalRingModel Y y)) :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingModelEval Y y))

/-- **The closed point of `Spec 𝒪_{Y, ȳ}` lies over `ȳ`**: `Spec κ(ȳ) ⟶ Spec A ⟶ U₀` is the lift of
`ȳ` to the chosen neighbourhood `U₀`. -/
theorem etaleLocalRingSpecGeometricPoint_comp :
    etaleLocalRingSpecGeometricPoint Y y ≫ etaleLocalRingSpecToChartScheme Y y =
      (chartGeometricPoint (affineEtaleNeighborhood Y y)).hom := by
  let U := chartScheme (affineEtaleNeighborhood Y y).chart
  let h := (chartGeometricPoint (affineEtaleNeighborhood Y y)).hom
  have hring : CommRingCat.ofHom (etaleLocalRingModelGerm Y y) ≫
      CommRingCat.ofHom (etaleLocalRingModelEval Y y) =
      U.presheaf.germ ⊤ (chartPoint B S hS Y.1 (affineEtaleNeighborhood Y y)) trivial ≫
        Scheme.stalkClosedPointTo h := by
    ext a
    exact etaleLocalRingModelEval_algebraMap Y y _
  rw [etaleLocalRingSpecGeometricPoint, etaleLocalRingSpecToChartScheme, ← Spec.map_comp_assoc,
    hring, Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpec_top]
  change Spec.map (Scheme.stalkClosedPointTo h) ≫ (isAffineOpen_top U).fromSpecStalk trivial = h
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo h) ≫ ·)
    (IsAffineOpen.fromSpecStalk_eq_fromSpecStalk _ _)).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk h)

variable {Y y}

/-- **`Spec 𝒪_{Y, ȳ}` as an object of the site**, through the model `A` of the étale local ring,
over `S` through the chosen affine neighbourhood. -/
def etaleLocalRingSpecObject
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (etaleLocalRingSpecToChartScheme Y y ≫
      B.inclusion.map
        ((SmallEtale.toOver B S hS Y.1).obj (affineEtaleNeighborhood Y y).chart).hom) :
    B.obj (contains_spec_etaleLocalRingModel (y := y) hY) ⟶ B.obj hS)

/-- The morphism `Spec 𝒪_{Y, ȳ} ⟶ U₀` in the site. -/
def etaleLocalRingSpecToChart
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    etaleLocalRingSpecObject (y := y) hY ⟶
      (SmallEtale.toOver B S hS Y.1).obj (affineEtaleNeighborhood Y y).chart :=
  Over.homMk (ObjectProperty.homMk (etaleLocalRingSpecToChartScheme Y y)) rfl

/-- The scheme underlying the object `Spec 𝒪_{Y, ȳ}` of the site is affine. -/
instance isAffine_etaleLocalRingSpecObject
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The morphism of schemes underlying the morphism `Spec 𝒪_{Y, ȳ} ⟶ U₀` of the site is flat. -/
instance flat_etaleLocalRingSpecToChart
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    Flat ((BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY)) :=
  inferInstanceAs (Flat (etaleLocalRingSpecToChartScheme Y y))

end AlgebraicGeometry.Space

end
