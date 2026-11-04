module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria

/-!
# Existence in the valuative criterion for representable morphisms

For a representable morphism `f` of presheaves on the big fppf site of `S`, allowing a
dominating extension of the valuation ring does not change the existence half of the
valuative criterion: every valuative square for `f` already has a lift.

The content is a descent of the dominating extension along the representing scheme. Given
a lift over the dominating valuation ring `R'`, the pullback of `f` along the bottom edge
is a scheme `P`; the lift and the dominating extension assemble into a map
`Spec R' ⟶ P` and the generic point into a map `Spec K ⟶ P`. Comparing their stalks shows
that the local homomorphism out of the stalk of `P` at the image of the closed point
factors through the original valuation ring `R`, and the resulting map `Spec R ⟶ P` is the
desired lift.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterion_existence_iff_lift`

## Implementation notes

The argument uses only representability of the morphism, so the statement applies to
representable transformations of presheaves without assuming separately that their source
and target are algebraic spaces. Valuative squares are those of the chosen big fppf site,
as in the definition of the valuative criterion for spaces.

## References

* [Stacks Project, Tag 03K8](https://stacks.math.columbia.edu/tag/03K8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A valuation ring is maximal among the subrings of its fraction field that it dominates:
if `R → R'` is a local homomorphism of valuation rings compatible with an extension
`K → K'` of fraction fields, then an element of `K` whose image in `K'` is integral over
`R'` is already integral over `R`. -/
private lemma valuation_extension_mem
    {R R' K K' : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (f : R →+* R') (g : K →+* K') [IsLocalHom f]
    (hfg : (algebraMap R' K').comp f = g.comp (algebraMap R K))
    (x : K) (hx : ∃ y : R', algebraMap R' K' y = g x) :
    ∃ r : R, algebraMap R K r = x := by
  by_cases hxR : ∃ r : R, algebraMap R K r = x
  · exact hxR
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hxR
    exact ⟨0, by simp [hx0]⟩
  obtain ⟨r', hr'⟩ := hx
  obtain hInt | hInv := ValuationRing.isInteger_or_isInteger (R := R) (K := K) x
  · change ∃ r : R, algebraMap R K r = x at hInt
    exact False.elim (hxR hInt)
  · obtain ⟨r, hr⟩ := hInv
    have hr_nonunit : ¬ IsUnit r := by
      intro hu
      apply hxR
      let s : R := (hu.unit⁻¹ : Rˣ).val
      refine ⟨s, ?_⟩
      have hmulR : r * s = 1 := by simp [s]
      have hmulK : algebraMap R K r * algebraMap R K s = 1 := by
        simpa using congrArg (algebraMap R K) hmulR
      rw [hr] at hmulK
      have hcancel : x⁻¹ * algebraMap R K s = x⁻¹ * x := by
        rw [hmulK, inv_mul_cancel₀ hx_ne]
      exact mul_left_cancel₀ (inv_ne_zero hx_ne) hcancel
    have hfr_nonunit : ¬ IsUnit (f r) := by
      intro hu
      exact hr_nonunit ((isUnit_map_iff f r).mp hu)
    have hgx_ne : g x ≠ 0 := by
      intro hgx0
      exact hx_ne (g.injective (by simpa using hgx0))
    have hfr : algebraMap R' K' (f r) = (g x)⁻¹ := by
      calc
        algebraMap R' K' (f r) = g (algebraMap R K r) := RingHom.congr_fun hfg r
        _ = (g x)⁻¹ := by rw [hr, map_inv₀]
    have hprod : f r * r' = 1 := by
      apply (IsFractionRing.injective R' K')
      calc
        algebraMap R' K' (f r * r') = (g x)⁻¹ * g x := by rw [map_mul, hfr, hr']
        _ = algebraMap R' K' 1 := by simpa using inv_mul_cancel₀ hgx_ne
    exact False.elim (hfr_nonunit (isUnit_iff_exists_inv.mpr ⟨r', hprod⟩))

/-- A local homomorphism from a local ring `A` to a valuation ring `R'` which on fraction
fields factors through a subfield `K` factors through the dominated valuation ring `R`,
again by a local homomorphism. -/
private lemma valuation_extension_local_map
    {A R R' K K' : Type u}
    [CommRing A] [IsLocalRing A]
    [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (f : R →+* R') (g : K →+* K') [IsLocalHom f]
    (hfg : (algebraMap R' K').comp f = g.comp (algebraMap R K))
    (φ' : A →+* R') [IsLocalHom φ'] (φ : A →+* K)
    (hφ : (algebraMap R' K').comp φ' = g.comp φ) :
    ∃ φR : A →+* R, IsLocalHom φR ∧ (algebraMap R K).comp φR = φ := by
  have hmem : ∀ a : A, ∃ r : R, algebraMap R K r = φ a := by
    intro a
    apply valuation_extension_mem f g hfg (φ a)
    exact ⟨φ' a, RingHom.congr_fun hφ a⟩
  let φR : A →+* R := {
    toFun := fun a => Classical.choose (hmem a)
    map_one' := by
      apply (IsFractionRing.injective R K)
      simpa only [map_one] using Classical.choose_spec (hmem 1)
    map_mul' := by
      intro a b
      apply (IsFractionRing.injective R K)
      simpa only [map_mul, Classical.choose_spec (hmem a),
        Classical.choose_spec (hmem b)] using Classical.choose_spec (hmem (a * b))
    map_zero' := by
      apply (IsFractionRing.injective R K)
      simpa only [map_zero] using Classical.choose_spec (hmem 0)
    map_add' := by
      intro a b
      apply (IsFractionRing.injective R K)
      simpa only [map_add, Classical.choose_spec (hmem a),
        Classical.choose_spec (hmem b)] using Classical.choose_spec (hmem (a + b)) }
  have hcomp : (algebraMap R K).comp φR = φ := by
    ext a
    exact Classical.choose_spec (hmem a)
  have hφ'R : φ' = f.comp φR := by
    ext a
    apply (IsFractionRing.injective R' K')
    calc
      algebraMap R' K' (φ' a) = g (φ a) := RingHom.congr_fun hφ a
      _ = g (algebraMap R K (φR a)) := congrArg g (RingHom.congr_fun hcomp a).symm
      _ = algebraMap R' K' (f (φR a)) := (RingHom.congr_fun hfg (φR a)).symm
  have hlocal : IsLocalHom φR := by
    refine ⟨fun a ha ↦ ?_⟩
    apply (isUnit_map_iff φ' a).mp
    rw [hφ'R]
    exact (isUnit_map_iff f (φR a)).2 ha
  exact ⟨φR, hlocal, hcomp⟩

/-- The spectrum of the inclusion of a domain into a fraction field carries the closed
point of the field to the generic point of the domain. -/
private alias spec_fractionField_map_closedPoint :=
  AlgebraicGeometry.Space.spec_algebraMap_closedPoint_eq_genericPoint

/-- A commuting square of maps to a scheme `P` from the spectra of a valuation ring and of
a subfield of its fraction field induces, on the stalk of `P` at the image of the closed
point, a square of ring homomorphisms. -/
private theorem scheme_stalk_extension_compatibility
    {P : Scheme.{u}} {R R' K K' : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [ValuationRing R']
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (fieldMap : K →+* K')
    (t : Spec (.of R') ⟶ P) (g : Spec (.of K) ⟶ P)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ t =
      Spec.map (CommRingCat.ofHom fieldMap) ≫ g)
    (hsp : g (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳
      t (IsLocalRing.closedPoint (CommRingCat.of R'))) :
    (algebraMap R' K').comp (Scheme.stalkClosedPointTo t).hom =
      fieldMap.comp ((P.presheaf.stalkSpecializes hsp ≫
        Scheme.stalkClosedPointTo g).hom) := by
  let x := t (IsLocalRing.closedPoint (CommRingCat.of R'))
  let β : P.presheaf.stalk x ⟶ CommRingCat.of K :=
    P.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo g
  change (algebraMap R' K').comp (Scheme.stalkClosedPointTo t).hom =
    fieldMap.comp β.hom
  have hring : Scheme.stalkClosedPointTo t ≫ CommRingCat.ofHom (algebraMap R' K') =
      β ≫ CommRingCat.ofHom fieldMap := by
    have hspec : Spec.map
        (Scheme.stalkClosedPointTo t ≫ CommRingCat.ofHom (algebraMap R' K')) =
        Spec.map (β ≫ CommRingCat.ofHom fieldMap) := by
      apply (cancel_mono (P.fromSpecStalk x)).mp
      calc
        Spec.map (Scheme.stalkClosedPointTo t ≫ CommRingCat.ofHom (algebraMap R' K')) ≫
            P.fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ t := by
            rw [Spec.map_comp]
            change Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
                (Spec.map (Scheme.stalkClosedPointTo t) ≫ P.fromSpecStalk
                  (t (IsLocalRing.closedPoint (CommRingCat.of R')))) = _
            rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
        _ = Spec.map (CommRingCat.ofHom fieldMap) ≫ g := h
        _ = Spec.map (β ≫ CommRingCat.ofHom fieldMap) ≫ P.fromSpecStalk x := by
          rw [Spec.map_comp]
          simp only [β, Spec.map_comp, Category.assoc,
            Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
          rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact Spec.map_injective hspec
  exact congrArg CommRingCat.Hom.hom hring

/-- For a local ring `R` and a point of `Spec R` inseparable from the closed point, the
composite of the stalk comparison with the canonical morphism out of the spectrum of the
stalk is the identity of `Spec R`. -/
private theorem specMap_stalkClosedPointComparison_inv_fromSpecStalk
    {R : CommRingCat.{u}} [IsLocalRing R] {y : Spec R}
    (h : Inseparable (IsLocalRing.closedPoint R) y) :
    Spec.map (((stalkClosedPointIso R).symm ≪≫ (Spec R).presheaf.stalkCongr h).inv) ≫
      (Spec R).fromSpecStalk y = 𝟙 (Spec R) := by
  rw [Iso.trans_inv, Iso.symm_inv, Spec.map_comp, Category.assoc]
  rw [show Spec.map ((Spec R).presheaf.stalkCongr h).inv ≫ (Spec R).fromSpecStalk y =
      Spec.map (stalkClosedPointIso R).inv from
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := Spec R)
      (x := IsLocalRing.closedPoint R) (y := y) h.le).trans (Spec_stalkClosedPointIso R).symm]
  rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

/-- Let `p : P ⟶ Spec R` be a morphism to the spectrum of a local ring, let
`g : Spec K ⟶ P` be a morphism from the spectrum of a field, and let `x` be a point of `P`
specialized by the closed point of `Spec K` and carried by `p` to the closed point of
`Spec R`. If `g ≫ p` is the spectrum of `φ : R →+* K`, then the composite of `φ` with the
stalk comparison at `x` is `φ` itself. -/
private theorem stalkClosedPointComparison_comp_stalkClosedPointTo
    {P : Scheme.{u}} {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    (p : P ⟶ Spec (.of R)) (g : Spec (.of K) ⟶ P) (φ : R →+* K) (x : P)
    (hxbase : p x = IsLocalRing.closedPoint (CommRingCat.of R))
    (hsp : g (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ x)
    (hgp : g ≫ p = Spec.map (CommRingCat.ofHom φ)) :
    ((stalkClosedPointIso (.of R)).symm ≪≫
        (Spec (.of R)).presheaf.stalkCongr (.of_eq hxbase.symm)).hom ≫
      p.stalkMap x ≫ (P.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo g) =
      CommRingCat.ofHom φ := by
  have he : Spec.map ((stalkClosedPointIso (CommRingCat.of R)).symm ≪≫
        (Spec (.of R)).presheaf.stalkCongr (Inseparable.of_eq hxbase.symm)).hom =
      (Spec (.of R)).fromSpecStalk (p x) := by
    rw [Iso.trans_hom, Iso.symm_hom, Spec.map_comp, Spec_stalkClosedPointIso]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq hxbase.symm).ge
  have hb : Spec.map (P.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo g) ≫
      P.fromSpecStalk x = g := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_comp, he, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, hb, hgp]

/-- For a representable morphism, a lift after a dominating extension exists
exactly when every valuative square has a lift before extension. -/
@[stacks 03K8]
public theorem valuativeCriterion_existence_iff_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    ValuativeCriterion.Existence f ↔
      (∀ q : ValuativeSquare f, Nonempty q.Lift) := by
  constructor
  · intro h q
    obtain ⟨e, ⟨l⟩⟩ := h q
    let C := BigFppfOver B S hS
    let RObj := siteObject B S hS q.ring_mem q.base
    let R'Obj := siteObject B S hS e.square.ring_mem e.square.base
    let KObj := siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
    let K'Obj := siteObject B S hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base)
    let qFrac : KObj ⟶ RObj := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
        B.obj q.field_mem ⟶ B.obj q.ring_mem)
    let eFrac : K'Obj ⟶ R'Obj := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K))) :
        B.obj e.square.field_mem ⟶ B.obj e.square.ring_mem)
    let pb := hf.isPullback q.special
    let V := hf.pullback q.special
    have hcompat : l.map ≫ f = yoneda.map e.specialOver ≫ q.special := by
      rw [l.special_comm, e.special_comm]
    let ηNat : yoneda.obj R'Obj ⟶ yoneda.obj V :=
      pb.lift l.map (yoneda.map e.specialOver) hcompat
    let η : R'Obj ⟶ V := yonedaEquiv ηNat
    have hgcompat : q.generic ≫ f = yoneda.map
        qFrac ≫ q.special := q.comm
    let γNat : yoneda.obj KObj ⟶ yoneda.obj V :=
      pb.lift q.generic
        (yoneda.map qFrac) hgcompat
    let γ : KObj ⟶ V := yonedaEquiv γNat
    let P : Scheme := (BigFppfOver.toScheme B S hS).obj V
    let t : Spec (.of e.square.R) ⟶ P :=
      (BigFppfOver.toScheme B S hS).map η
    let g : Spec (.of q.K) ⟶ P :=
      (BigFppfOver.toScheme B S hS).map γ
    have hbasepaths : e.genericOver ≫ qFrac = eFrac ≫ e.specialOver := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      change B.inclusion.map e.genericOver.left ≫ B.inclusion.map qFrac.left =
        B.inclusion.map eFrac.left ≫ B.inclusion.map e.specialOver.left
      rw [e.genericOver_left, e.specialOver_left]
      simp only [qFrac, eFrac, Over.homMk_left, Over.mk_left, ObjectProperty.ι_obj,
        ObjectProperty.ι_map, ObjectProperty.homMk_hom]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext e.fraction_comm.symm
    have hpaths : yoneda.map e.genericOver ≫ γNat = yoneda.map eFrac ≫ ηNat := by
      apply pb.hom_ext
      · dsimp only [γNat, ηNat]
        rw [Category.assoc, pb.lift_fst, Category.assoc, pb.lift_fst]
        rw [← e.generic_comm, l.generic_comm]
      · dsimp only [γNat, ηNat]
        rw [Category.assoc, pb.lift_snd, Category.assoc, pb.lift_snd]
        rw [← yoneda.map_comp, ← yoneda.map_comp]
        exact congrArg yoneda.map hbasepaths
    have hpathsC : e.genericOver ≫ γ = eFrac ≫ η := by
      calc
        e.genericOver ≫ γ = yonedaEquiv (yoneda.map e.genericOver ≫ γNat) := by
          simpa [γ] using yonedaEquiv_naturality γNat e.genericOver
        _ = yonedaEquiv (yoneda.map eFrac ≫ ηNat) :=
          congrArg (yonedaEquiv (X := K'Obj) (F := yoneda.obj V)) hpaths
        _ = eFrac ≫ η := by
          simpa [η] using (yonedaEquiv_naturality ηNat eFrac).symm
    have htg : Spec.map (CommRingCat.ofHom e.fieldMap) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ t := by
      have hscheme := congrArg (BigFppfOver.toScheme B S hS).map
        hpathsC
      change B.inclusion.map e.genericOver.left ≫ g =
        B.inclusion.map eFrac.left ≫ t at hscheme
      calc
        Spec.map (CommRingCat.ofHom e.fieldMap) ≫ g =
            B.inclusion.map e.genericOver.left ≫ g := by rw [e.genericOver_left]
        _ = B.inclusion.map eFrac.left ≫ t := hscheme
        _ = Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ t := by
          simp [eFrac]
    have : IsLocalHom e.fieldMap := ⟨fun a ha => by
      apply isUnit_iff_ne_zero.mpr
      intro ha0
      subst a
      simp at ha⟩
    have hsp : g (IsLocalRing.closedPoint (CommRingCat.of q.K)) ⤳
        t (IsLocalRing.closedPoint (CommRingCat.of e.square.R)) := by
      have hspec : g (IsLocalRing.closedPoint (CommRingCat.of q.K)) =
          t (genericPoint (Spec (.of e.square.R))) := by
        have hpoint := congrArg (fun v : Spec (.of e.square.K) ⟶ P =>
          v (IsLocalRing.closedPoint (CommRingCat.of e.square.K))) htg
        change g (Spec.map (CommRingCat.ofHom e.fieldMap) _) =
          t (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) _) at hpoint
        rw [show Spec.map (CommRingCat.ofHom e.fieldMap)
          (IsLocalRing.closedPoint (CommRingCat.of e.square.K)) =
          IsLocalRing.closedPoint (CommRingCat.of q.K) from Spec_closedPoint,
          spec_fractionField_map_closedPoint] at hpoint
        exact hpoint
      rw [hspec]
      exact (IsLocalRing.specializes_closedPoint
        (genericPoint (Spec (.of e.square.R)))).map t.continuous
    let β : P.presheaf.stalk
        (t (IsLocalRing.closedPoint (CommRingCat.of e.square.R))) ⟶ CommRingCat.of q.K :=
      P.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo g
    have hβ : (algebraMap e.square.R e.square.K).comp
        (Scheme.stalkClosedPointTo t).hom = e.fieldMap.comp β.hom :=
      scheme_stalk_extension_compatibility (R := q.R) (R' := e.square.R)
        (K := q.K) (K' := e.square.K) e.fieldMap t g htg.symm hsp
    have : IsLocalHom e.ringMap := e.isLocalHom
    obtain ⟨φR, hφRlocal, hφR⟩ := valuation_extension_local_map
      (A := P.presheaf.stalk
        (t (IsLocalRing.closedPoint (CommRingCat.of e.square.R))))
      (R := q.R) (R' := e.square.R) (K := q.K) (K' := e.square.K)
      e.ringMap e.fieldMap e.fraction_comm (Scheme.stalkClosedPointTo t).hom β.hom hβ
    let x := t (IsLocalRing.closedPoint (CommRingCat.of e.square.R))
    let p : P ⟶ Spec (.of q.R) := (BigFppfOver.toScheme B S hS).map
      (hf.snd q.special)
    let u : Spec (.of q.R) ⟶ P := (SpecToEquivOfLocalRing P (CommRingCat.of q.R)).symm
      ⟨x, ⟨CommRingCat.ofHom φR, hφRlocal⟩⟩
    have hyon : ∀ {Z : C} (a : yoneda.obj Z ⟶ yoneda.obj V), yoneda.map (yonedaEquiv a) = a := by
      intro Z a
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map]
    have hlift : ∀ {Z : C} (a : yoneda.obj Z ⟶ X) (b : Z ⟶ RObj)
        (hab : a ≫ f = yoneda.map b ≫ q.special),
        yonedaEquiv (pb.lift a (yoneda.map b) hab) ≫ hf.snd q.special = b := by
      intro Z a b hab
      apply yoneda.map_injective
      rw [yoneda.map_comp, hyon]
      exact pb.lift_snd a (yoneda.map b) hab
    have hηs : η ≫ hf.snd q.special = e.specialOver := hlift _ _ _
    have hγs : γ ≫ hf.snd q.special = qFrac := hlift _ _ _
    have hgp : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := by
      change (BigFppfOver.toScheme B S hS).map
          (γ ≫ hf.snd q.special) = _
      rw [hγs]
      change B.inclusion.map qFrac.left = _
      simp [qFrac]
    have htp : t ≫ p = Spec.map (CommRingCat.ofHom e.ringMap) := by
      change (BigFppfOver.toScheme B S hS).map (η ≫ hf.snd q.special) = _
      rw [hηs]
      change B.inclusion.map e.specialOver.left = _
      exact e.specialOver_left
    have hxbase : p x = IsLocalRing.closedPoint (CommRingCat.of q.R) := by
      let z : Spec (.of e.square.R) :=
        primeSpectrumOrderIsoSpec e.square.R (IsLocalRing.closedPoint (CommRingCat.of e.square.R))
      have hh := congrArg (fun v : Spec (.of e.square.R) ⟶ Spec (.of q.R) => v z) htp
      have hh' : p (t z) = Spec.map (CommRingCat.ofHom e.ringMap) z := by
        simpa only [Scheme.Hom.comp_apply] using hh
      have hz : z = IsLocalRing.closedPoint (CommRingCat.of e.square.R) := rfl
      change p (t z) = IsLocalRing.closedPoint (CommRingCat.of q.R)
      rw [hh', hz, Spec_closedPoint]
    let e₀ : CommRingCat.of q.R ≅
        (Spec (.of q.R)).presheaf.stalk (p x) :=
      (stalkClosedPointIso (.of q.R)).symm ≪≫
        (Spec (.of q.R)).presheaf.stalkCongr (.of_eq hxbase.symm)
    let α : CommRingCat.of q.R ⟶ P.presheaf.stalk x := e₀.hom ≫ p.stalkMap x
    have hαβ : α ≫ β = CommRingCat.ofHom (algebraMap q.R q.K) :=
      (Category.assoc e₀.hom (p.stalkMap x) β).trans
        (stalkClosedPointComparison_comp_stalkClosedPointTo p g (algebraMap q.R q.K) x
          hxbase hsp hgp)
    have hcomp : (algebraMap q.R q.K).comp (φR.comp α.hom) = algebraMap q.R q.K := by
      calc
        (algebraMap q.R q.K).comp (φR.comp α.hom) =
            ((algebraMap q.R q.K).comp φR).comp α.hom := by rw [RingHom.comp_assoc]
        _ = β.hom.comp α.hom := by rw [hφR]
        _ = algebraMap q.R q.K := CommRingCat.hom_ext_iff.mp hαβ
    have hRend : φR.comp α.hom = RingHom.id q.R := by
      apply RingHom.ext
      intro r
      apply (IsFractionRing.injective q.R q.K)
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun F : q.R →+* q.K => F r) hcomp
    have hαid : α ≫ CommRingCat.ofHom φR = 𝟙 (CommRingCat.of q.R) := CommRingCat.hom_ext hRend
    have hstalk : p.stalkMap x ≫ CommRingCat.ofHom φR = e₀.inv := by
      apply (cancel_epi e₀.hom).mp
      calc
        e₀.hom ≫ (p.stalkMap x ≫ CommRingCat.ofHom φR) =
            (e₀.hom ≫ p.stalkMap x) ≫ CommRingCat.ofHom φR :=
              (Category.assoc _ _ _).symm
        _ = α ≫ CommRingCat.ofHom φR := rfl
        _ = 𝟙 _ := hαid
        _ = e₀.hom ≫ e₀.inv := (Iso.hom_inv_id e₀).symm
    have huClosed : u (IsLocalRing.closedPoint q.R) = x := by
      have hh := (SpecToEquivOfLocalRing P (CommRingCat.of q.R)).right_inv
        ⟨x, ⟨CommRingCat.ofHom φR, hφRlocal⟩⟩
      exact congrArg Sigma.fst hh
    have hbase : u ≫ p = 𝟙 (Spec (.of q.R)) := by
      dsimp [u, SpecToEquivOfLocalRing]
      rw [Category.assoc]
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := p) (x := x)]
      rw [← Spec.map_comp_assoc (p.stalkMap x) (CommRingCat.ofHom φR)
        ((Spec (.of q.R)).fromSpecStalk (p x))]
      rw [hstalk]
      exact specMap_stalkClosedPointComparison_inv_fromSpecStalk _
    have hgenP :
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ u = g := by
      dsimp [u, SpecToEquivOfLocalRing]
      calc
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
            Spec.map (CommRingCat.ofHom φR) ≫ P.fromSpecStalk x =
          Spec.map (CommRingCat.ofHom φR ≫
            CommRingCat.ofHom (algebraMap q.R q.K)) ≫ P.fromSpecStalk x := by
              simp only [← Spec.map_comp_assoc]
        _ = Spec.map β ≫ P.fromSpecStalk x := by
          rw [← CommRingCat.ofHom_comp]
          have hφR' : CommRingCat.ofHom ((algebraMap q.R q.K).comp φR) = β :=
            CommRingCat.hom_ext hφR
          rw [hφR']
        _ = Spec.map (P.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo g) ≫
              P.fromSpecStalk x := by
          dsimp [β]
        _ = Spec.map (Scheme.stalkClosedPointTo g) ≫
              P.fromSpecStalk (g (IsLocalRing.closedPoint (CommRingCat.of q.K))) := by
          rw [Spec.map_comp, Category.assoc,
            Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
        _ = g := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := g)
    let uV : RObj ⟶ V := Over.homMk (ObjectProperty.homMk u) (by
      apply B.inclusion.map_injective
      rw [← Over.w (hf.snd q.special)]
      simp only [ObjectProperty.ι_map]
      change u ≫ (p ≫ B.inclusion.map RObj.hom) = B.inclusion.map RObj.hom
      rw [← Category.assoc, hbase]
      simp)
    have huSnd : uV ≫ hf.snd q.special = 𝟙 RObj := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      change u ≫ p = 𝟙 (Spec (.of q.R))
      simpa [uV, BigFppfOver.toScheme] using hbase
    have hgenV : qFrac ≫ uV = γ := Over.OverMorphism.ext (B.inclusion.map_injective hgenP)
    let m : yoneda.obj RObj ⟶ X := yoneda.map uV ≫ hf.fst q.special
    have hgen : yoneda.map qFrac ≫ m = q.generic := by
      calc
        yoneda.map qFrac ≫ m =
            (yoneda.map qFrac ≫ yoneda.map uV) ≫ hf.fst q.special := by
              simp only [m, Category.assoc]
        _ = yoneda.map (qFrac ≫ uV) ≫ hf.fst q.special := by
          rw [← yoneda.map_comp]
        _ = yoneda.map γ ≫ hf.fst q.special := by rw [hgenV]
        _ = q.generic := by
          rw [show yoneda.map γ = γNat from hyon _]
          exact pb.lift_fst q.generic (yoneda.map qFrac) hgcompat
    have hspecial : m ≫ f = q.special := by
      dsimp [m]
      rw [Category.assoc, pb.w]
      rw [← yoneda.map_comp_assoc, huSnd]
      simp
    exact ⟨⟨m, hgen, hspecial⟩⟩
  · exact valuativeCriterionExistence_of_forall_nonempty_lift f

end AlgebraicGeometry.Space

end
