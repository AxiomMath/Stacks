module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic
public import StacksFrontier.AlgebraicGeometry.ResidueFieldTransport
public import StacksFrontier.RingTheory.Localization.IntegralMaximalIdeals

/-!
# The fibre of an integral morphism is the maximal spectrum of the pushforward stalk

Let `f : Y ⟶ X` be an integral morphism of schemes and let `x` be a point of `X`. The stalk
`S = (f_* 𝒪_Y)_x` is an `𝒪_{X,x}`-algebra, and the points of `Y` above `x` correspond to the
maximal ideals of `S`, compatibly with residue fields: the residue field of `Y` at a point `y`
above `x` is the quotient of `S` by the corresponding maximal ideal, as an extension of the
residue field of `X` at `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardStalkResidueMap` is the evaluation of the stalk of
  `f_* 𝒪_Y` at `x` on a point of `Y` above `x`, followed by passage to its residue field.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_fibreEquivMaximalSpectrum`: the fibre of `f` over `x` is
  equivalent to the maximal spectrum of `(f_* 𝒪_Y)_x`, compatibly with residue fields over the
  residue field of `x`.

## Implementation notes

The computation is local: on an affine open `U ∋ x`, with `R = Γ(X, U)`, `T = Γ(Y, f⁻¹U)` and
`p ⊆ R` the prime of `x`, the ring `S` is the localization of `T` at the image of the complement
of `p` (`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`), and `R → T` is
integral. The points of `f⁻¹U` above `x` are the primes of `T` lying over `p`, and
`IsLocalization.isMaximal_map_of_under_eq` together with
`IsLocalization.under_under_eq_of_isMaximal` identifies those with the maximal ideals of `S`.

The residue-field half factors through the affine model twice. The residue field of `Y` at `y` is
the residue field of the prime `q ⊆ T` of `y`, because `Spec Γ(Y, f⁻¹U) → Y` is an open immersion
and so an isomorphism on stalks; and the residue field of `q` is the residue field of the maximal
ideal `qS`, because localizing `T` at `p` and then at `qS` is localizing `T` at `q`
(`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`). Since `qS` is maximal, the
latter residue field is the quotient by `qS`. That last comparison is available only for the
standard model `Localization`, so `S` is transported to it by `IsLocalization.algEquiv`.

Because the chosen affine open is not part of the statement, the equivalence and the
residue-field isomorphisms are produced existentially. The compatibility of the resulting
isomorphism with the two maps out of `𝒪_{X,x}` is checked on `T` and extended to `S` by
`IsLocalization.ringHom_ext`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Evaluation of the stalk of `f_* 𝒪_Y` at `x` on a point `y` of `Y` above `x`, followed by
passage to the residue field of `Y` at `y`. -/
public noncomputable def Scheme.Hom.pushforwardStalkResidueMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {x : X} (y : Y) (hy : f y = x) :
    (f.base _* Y.presheaf).stalk x →+* Y.residueField y :=
  ((Y.residue y).hom.comp
      (Y.presheaf.stalkPushforward CommRingCat f.base y).hom).comp
    (eqToHom (congrArg (f.base _* Y.presheaf).stalk hy.symm)).hom

/-- Transporting a stalk along an equality of points turns a germ into the germ at the other
point. -/
private theorem stalk_eqToHom_comp_germ {Z : TopCat.{u}} (G : TopCat.Presheaf CommRingCat Z)
    {a b : Z} (h : a = b) (W : Opens Z) (ha : a ∈ W) :
    (eqToHom (congrArg G.stalk h)).hom.comp (G.germ W a ha).hom =
      (G.germ W b (h ▸ ha)).hom := by
  cases h
  rfl

/-- The prime of `Γ(Y, V)` attached to the point of an affine open `V` coming from a prime is
that prime. -/
private theorem primeIdealOf_fromSpec {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    (q : PrimeSpectrum Γ(Y, V)) (hq : hV.fromSpec q ∈ V) :
    hV.primeIdealOf ⟨hV.fromSpec q, hq⟩ = q := by
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  exact hV.fromSpec.isOpenEmbedding.injective
    (hV.fromSpec_primeIdealOf ⟨hV.fromSpec q, hq⟩)

/-- The residue field of `Y` at a point of an affine open `V` is the residue field of the prime
of `Γ(Y, V)` that the point determines. -/
private noncomputable def residueFieldEquivResidueFieldPrime {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) (q : PrimeSpectrum Γ(Y, V)) :
    Y.residueField (hV.fromSpec q) ≃+* q.asIdeal.ResidueField :=
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  haveI : IsIso (hV.fromSpec.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hV.isOpenImmersion_fromSpec).2 q
  haveI : IsLocalRing ((Spec Γ(Y, V)).presheaf.stalk q) := (Spec Γ(Y, V)).isLocalRing q
  haveI : IsIso (hV.fromSpec.residueFieldMap q) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (hV.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  (RingEquiv.ofBijective (hV.fromSpec.residueFieldMap q).hom
      (ConcreteCategory.bijective_of_isIso _)).trans
    (Scheme.Spec.residueFieldIso (CommRingCat.of Γ(Y, V)) q).commRingCatIsoToRingEquiv

/-- Read through the residue field of the corresponding prime, the residue of a germ at a point
of an affine open is the image of the section in that residue field. -/
private theorem residueFieldEquivResidueFieldPrime_comp_germ {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) (q : PrimeSpectrum Γ(Y, V)) (hq : hV.fromSpec q ∈ V) :
    (residueFieldEquivResidueFieldPrime hV q).toRingHom.comp
        ((Y.residue (hV.fromSpec q)).hom.comp
          (Y.presheaf.germ V (hV.fromSpec q) hq).hom) =
      algebraMap Γ(Y, V) q.asIdeal.ResidueField := by
  let T := Γ(Y, V)
  let j := hV.fromSpec
  let specIso := Scheme.Spec.residueFieldIso (CommRingCat.of T) q
  have hNat : (j.residueFieldMap q).hom.comp (Y.residue (j q)).hom =
      ((Spec T).residue q).hom.comp (j.stalkMap q).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap j q)
  have hGermJ : (j.stalkMap q).hom.comp (Y.presheaf.germ V (j q) hq).hom =
      ((Spec T).presheaf.germ (j ⁻¹ᵁ V) q hq).hom.comp (j.app V).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap j V q hq)
  have hGlobal : ((Spec T).presheaf.germ (j ⁻¹ᵁ V) q hq).hom.comp (j.app V).hom =
      ((Spec T).presheaf.germ ⊤ q trivial).hom.comp (Scheme.ΓSpecIso T).inv.hom := by
    rw [hV.fromSpec_app_self, CommRingCat.hom_comp, ← RingHom.comp_assoc]
    have hres := congrArg CommRingCat.Hom.hom
      ((Spec T).presheaf.germ_res (eqToHom hV.fromSpec_preimage_self) q hq)
    simp only [CommRingCat.hom_comp] at hres
    rw [hres]
  have hIso : specIso.hom.hom.comp
      (((Spec T).residue q).hom.comp
        (((Spec T).presheaf.germ ⊤ q trivial).hom.comp (Scheme.ΓSpecIso T).inv.hom)) =
      algebraMap T q.asIdeal.ResidueField := by
    have hInv := congrArg CommRingCat.Hom.hom
      (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of T) q)
    change specIso.inv.hom.comp (algebraMap T q.asIdeal.ResidueField) = _ at hInv
    calc
      _ = specIso.hom.hom.comp
          (specIso.inv.hom.comp (algebraMap T q.asIdeal.ResidueField)) :=
        congrArg (fun k => specIso.hom.hom.comp k) hInv.symm
      _ = _ := by ext z; exact specIso.inv_hom_id_apply _
  have hCompose : (j.residueFieldMap q).hom.comp
      ((Y.residue (j q)).hom.comp (Y.presheaf.germ V (j q) hq).hom) =
      ((Spec T).residue q).hom.comp
        (((Spec T).presheaf.germ ⊤ q trivial).hom.comp (Scheme.ΓSpecIso T).inv.hom) := by
    rw [← RingHom.comp_assoc, hNat, RingHom.comp_assoc, hGermJ, hGlobal]
  refine RingHom.ext fun t => ?_
  change specIso.commRingCatIsoToRingEquiv
    ((j.residueFieldMap q).hom
      (((Y.residue (j q)).hom.comp (Y.presheaf.germ V (j q) hq).hom) t)) = _
  calc
    _ = specIso.commRingCatIsoToRingEquiv
        ((((Spec T).residue q).hom.comp
          (((Spec T).presheaf.germ ⊤ q trivial).hom.comp
            (Scheme.ΓSpecIso T).inv.hom)) t) := by
          congr 1
          exact RingHom.congr_fun hCompose t
    _ = _ := RingHom.congr_fun hIso t

/-- The two maps from `𝒪_{X,x}` to the residue field of `Y` at a point above `x` -- through the
residue field of `x`, and through the stalk of `f_* 𝒪_Y` -- agree. -/
private theorem pushforwardStalkResidueMap_comp_algebraMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (x : X) (y : Y) (hy : f y = x) :
    letI : Algebra (X.presheaf.stalk x) ((f.base _* Y.presheaf).stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom.toAlgebra
    ((f.residueFieldMap y).hom.comp
        (X.residueFieldCongr hy.symm).hom.hom).comp (X.residue x).hom =
      (f.pushforwardStalkResidueMap y hy).comp
        (algebraMap (X.presheaf.stalk x) ((f.base _* Y.presheaf).stalk x)) := by
  subst hy
  change ((f.residueFieldMap y).hom.comp (X.residue (f y)).hom) = _
  rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
  rfl

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegralHom f]

/-- **The fibre of an integral morphism is the maximal spectrum of the pushforward stalk.** The
points of `Y` above `x` correspond to the maximal ideals of the stalk at `x` of `f_* 𝒪_Y`, and
the residue field of `Y` at such a point is the quotient of that stalk by the corresponding
maximal ideal, as an extension of the residue field of `X` at `x`. -/
public theorem Scheme.Hom.exists_fibreEquivMaximalSpectrum (x : X) :
    letI : Algebra (X.presheaf.stalk x) ((f.base _* Y.presheaf).stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom.toAlgebra
    ∃ e : {y : Y // f y = x} ≃ MaximalSpectrum ((f.base _* Y.presheaf).stalk x),
      ∀ y : {y : Y // f y = x},
        ∃ ε : Y.residueField y.1 ≃+* ((f.base _* Y.presheaf).stalk x ⧸ (e y).asIdeal),
          ε.toRingHom.comp (f.pushforwardStalkResidueMap y.1 y.2) =
              Ideal.Quotient.mk (e y).asIdeal ∧
            (ε.toRingHom.comp ((f.residueFieldMap y.1).hom.comp
                (X.residueFieldCongr y.2.symm).hom.hom)).comp (X.residue x).hom =
              (Ideal.Quotient.mk (e y).asIdeal).comp
                (algebraMap (X.presheaf.stalk x) ((f.base _* Y.presheaf).stalk x)) := by
  classical
  let F := f.base _* Y.presheaf
  let S := F.stalk x
  let : Algebra (X.presheaf.stalk x) S :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom.toAlgebra
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(X, U)
  let T := Γ(Y, V)
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hxU⟩
  let : Algebra R T := (f.app U).hom.toAlgebra
  let N : Submonoid T := Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl
  have : Algebra.IsIntegral R T :=
    Algebra.isIntegral_def.mpr fun z => f.isIntegral_app U hU z
  let : Algebra T S := (F.germ U x hxU).hom.toAlgebra
  have : IsLocalization N S := hU.isLocalization_pushforwardStalk f hxU
  let : Algebra R S := ((F.germ U x hxU).hom.comp (f.app U).hom).toAlgebra
  have : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmemV : ∀ y : Y, f y = x → y ∈ V := fun y hy => by
    change f y ∈ U
    rwa [hy]
  -- The prime of `T` attached to a point of `Y` above `x` lies over `p`.
  have hunder : ∀ (y : Y) (hy : f y = x),
      (hV.primeIdealOf ⟨y, hmemV y hy⟩).asIdeal.under R = p.asIdeal := by
    intro y hy
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := y) U hU V hV le_rfl
      (hmemV y hy)
    have happ : (f.appLE U V le_rfl).hom = (f.app U).hom :=
      congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app f)
    have hpoint : (⟨f y, hmemV y hy⟩ : U) = ⟨x, hxU⟩ := Subtype.ext hy
    rw [happ, hpoint] at h
    exact congrArg PrimeSpectrum.asIdeal h
  -- The two directions of the correspondence.
  let toMax : {y : Y // f y = x} → MaximalSpectrum S := fun y =>
    ⟨(hV.primeIdealOf ⟨y.1, hmemV y.1 y.2⟩).asIdeal.map (algebraMap T S),
      IsLocalization.isMaximal_map_of_under_eq p.asIdeal (hunder y.1 y.2)⟩
  have hprime : ∀ m : MaximalSpectrum S, (m.asIdeal.under T).IsPrime := fun m =>
    have := m.isMaximal.isPrime
    Ideal.IsPrime.comap _
  let toPrime : MaximalSpectrum S → PrimeSpectrum T := fun m =>
    ⟨m.asIdeal.under T, hprime m⟩
  have hfromSpec : ∀ m : MaximalSpectrum S, f (hV.fromSpec (toPrime m)) = x := by
    intro m
    have hq : (toPrime m).asIdeal.under R = p.asIdeal := by
      have := m.isMaximal
      exact IsLocalization.under_under_eq_of_isMaximal p.asIdeal m.asIdeal
    have hspec : Spec.map (f.appLE U V le_rfl) (toPrime m) = p := by
      apply PrimeSpectrum.ext
      change (toPrime m).asIdeal.comap (f.appLE U V le_rfl).hom = p.asIdeal
      rw [Scheme.Hom.appLE_eq_app]
      exact hq
    have hp := congrArg (fun g => g (toPrime m))
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV (le_rfl : V ≤ f ⁻¹ᵁ U))
    change hU.fromSpec (Spec.map (f.appLE U V le_rfl) (toPrime m)) =
      f (hV.fromSpec (toPrime m)) at hp
    rw [← hp, hspec]
    exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  let toFibre : MaximalSpectrum S → {y : Y // f y = x} := fun m =>
    ⟨hV.fromSpec (toPrime m), hfromSpec m⟩
  have hleft : ∀ y, toFibre (toMax y) = y := by
    intro y
    apply Subtype.ext
    change hV.fromSpec (toPrime (toMax y)) = y.1
    have hq : (toPrime (toMax y)).asIdeal = (hV.primeIdealOf ⟨y.1, hmemV y.1 y.2⟩).asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint N S (hV.primeIdealOf _).isPrime
        (IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq p.asIdeal (hunder y.1 y.2))
    rw [show toPrime (toMax y) = hV.primeIdealOf ⟨y.1, hmemV y.1 y.2⟩ from
      PrimeSpectrum.ext hq]
    exact hV.fromSpec_primeIdealOf _
  have hright : ∀ m, toMax (toFibre m) = m := by
    intro m
    apply MaximalSpectrum.ext
    change (hV.primeIdealOf ⟨hV.fromSpec (toPrime m), _⟩).asIdeal.map (algebraMap T S) =
      m.asIdeal
    rw [primeIdealOf_fromSpec hV (toPrime m) (hmemV _ (hfromSpec m))]
    exact IsLocalization.map_under N S m.asIdeal
  refine ⟨⟨toMax, toFibre, hleft, hright⟩, ?_⟩
  intro y
  have hyV : y.1 ∈ V := hmemV y.1 y.2
  let q : PrimeSpectrum T := hV.primeIdealOf ⟨y.1, hyV⟩
  let M : Ideal S := q.asIdeal.map (algebraMap T S)
  have hdisj : Disjoint (N : Set T) (q.asIdeal : Set T) :=
    IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq p.asIdeal (hunder y.1 y.2)
  have : M.IsMaximal := IsLocalization.isMaximal_map_of_under_eq p.asIdeal (hunder y.1 y.2)
  have hyEq : hV.fromSpec q = y.1 := hV.fromSpec_primeIdealOf _
  have hqV : hV.fromSpec q ∈ V := hyEq ▸ hyV
  -- The residue field of `y`, read on the affine model.
  let eYSpec : Y.residueField y.1 ≃+* q.asIdeal.ResidueField :=
    (Scheme.residueFieldCongr (X := Y) hyEq.symm).commRingCatIsoToRingEquiv.trans
      (residueFieldEquivResidueFieldPrime hV q)
  -- Transport to the standard localization, where the residue field of a maximal ideal is the
  -- quotient by it.
  let L := Localization N
  let eSL : S ≃ₐ[T] L := IsLocalization.algEquiv N S L
  let ML : Ideal L := q.asIdeal.map (algebraMap T L)
  have : ML.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint N L q.asIdeal q.isPrime hdisj
  have : ML.IsMaximal := IsLocalization.isMaximal_map_of_under_eq p.asIdeal (hunder y.1 y.2)
  have hMLmap : ML = M.map (eSL.toRingEquiv : S →+* L) := by
    change q.asIdeal.map (algebraMap T L) =
      (q.asIdeal.map (algebraMap T S)).map (eSL.toRingEquiv : S →+* L)
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun t => (eSL.commutes t).symm
  have hunderML : ML.under T = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint N L q.isPrime hdisj
  let eQuot : (S ⧸ M) ≃+* (L ⧸ ML) := Ideal.quotientEquiv M ML eSL.toRingEquiv hMLmap
  let eLocal : q.asIdeal.ResidueField ≃ₐ[T] ML.ResidueField :=
    (Ideal.residueFieldAlgEquiv q.asIdeal (ML.under T) (AlgEquiv.refl (R := T))
        hunderML.symm).trans
      (IsLocalRing.ResidueField.mapAlgEquiv
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization N ML))
  let eQuotL : (L ⧸ ML) ≃+* ML.ResidueField :=
    RingEquiv.ofBijective (algebraMap (L ⧸ ML) ML.ResidueField)
      ML.bijective_algebraMap_quotient_residueField
  let ε : Y.residueField y.1 ≃+* (S ⧸ M) :=
    ((eYSpec.trans eLocal.toRingEquiv).trans eQuotL.symm).trans eQuot.symm
  -- Evaluation of the stalk at `y` is the quotient map, checked on `T`.
  have hNchart : (f.pushforwardStalkResidueMap y.1 y.2).comp (algebraMap T S) =
      (Y.residue y.1).hom.comp (Y.presheaf.germ V y.1 hyV).hom := by
    change ((Y.residue y.1).hom.comp
        (Y.presheaf.stalkPushforward CommRingCat f.base y.1).hom).comp
      ((eqToHom (congrArg F.stalk y.2.symm)).hom.comp (F.germ U x hxU).hom) = _
    rw [stalk_eqToHom_comp_germ F y.2.symm U hxU, RingHom.comp_assoc]
    congr 1
    exact congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base Y.presheaf U y.1
        (y.2.symm ▸ hxU))
  have hPoint : (Scheme.residueFieldCongr (X := Y)
        hyEq.symm).commRingCatIsoToRingEquiv.toRingHom.comp
      ((Y.residue y.1).hom.comp (Y.presheaf.germ V y.1 hyV).hom) =
      (Y.residue (hV.fromSpec q)).hom.comp
        (Y.presheaf.germ V (hV.fromSpec q) hqV).hom := by
    change (eqToHom (congrArg Y.residueField hyEq.symm)).hom.comp _ = _
    rw [← RingHom.comp_assoc, residueField_eqToHom_comp_residue Y hyEq.symm, RingHom.comp_assoc,
      stalk_eqToHom_comp_germ Y.presheaf hyEq.symm V hyV]
  have hEvalY : (eYSpec.toRingHom.comp (f.pushforwardStalkResidueMap y.1 y.2)).comp
      (algebraMap T S) = algebraMap T q.asIdeal.ResidueField := by
    rw [RingHom.comp_assoc, hNchart]
    change (residueFieldEquivResidueFieldPrime hV q).toRingHom.comp
      ((Scheme.residueFieldCongr (X := Y) hyEq.symm).commRingCatIsoToRingEquiv.toRingHom.comp
        ((Y.residue y.1).hom.comp (Y.presheaf.germ V y.1 hyV).hom)) = _
    rw [hPoint]
    exact residueFieldEquivResidueFieldPrime_comp_germ hV q hqV
  have heval : ε.toRingHom.comp (f.pushforwardStalkResidueMap y.1 y.2) =
      Ideal.Quotient.mk M := by
    refine IsLocalization.ringHom_ext N (RingHom.ext fun t => ?_)
    change eQuot.symm (eQuotL.symm (eLocal
      (eYSpec ((f.pushforwardStalkResidueMap y.1 y.2) ((algebraMap T S) t))))) =
      Ideal.Quotient.mk M ((algebraMap T S) t)
    have hval : eYSpec ((f.pushforwardStalkResidueMap y.1 y.2) ((algebraMap T S) t)) =
        (algebraMap T q.asIdeal.ResidueField) t := by
      simpa using RingHom.congr_fun hEvalY t
    rw [hval, eLocal.commutes]
    apply eQuot.injective
    rw [eQuot.apply_symm_apply]
    apply eQuotL.injective
    rw [eQuotL.apply_symm_apply]
    change (algebraMap T ML.ResidueField) t =
      algebraMap (L ⧸ ML) ML.ResidueField
        (Ideal.Quotient.mk ML (eSL ((algebraMap T S) t)))
    rw [eSL.commutes]
    exact (IsScalarTower.algebraMap_apply T L ML.ResidueField t).trans
      (congrArg (fun k : L →+* ML.ResidueField => k ((algebraMap T L) t))
        (IsScalarTower.algebraMap_eq L (L ⧸ ML) ML.ResidueField))
  refine ⟨ε, heval, ?_⟩
  rw [RingHom.comp_assoc, pushforwardStalkResidueMap_comp_algebraMap f x y.1 y.2,
    ← RingHom.comp_assoc, heval]
  rfl

end AlgebraicGeometry

end
