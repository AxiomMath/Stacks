module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective

/-!
# Extending a local homomorphism to a morphism

A local homomorphism between the local rings at two points over the same point of a base
scheme, compatible with the maps from the local ring of the base, is induced by a morphism over
the base on an open neighbourhood of the source point when the target is locally of finite type
and the germ map of the source is injective at the point; in particular when the source is
integral, locally Noetherian, or reduced with finitely many irreducible components.

## Main results

* `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isGermInjectiveAt` gives the
  finite-type case for a source whose germ map is injective at the point.
* `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isReduced` gives the
  finite-type case for a reduced source with finitely many irreducible components.
* `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isIntegral` gives the
  finite-type case for an integral source.
* `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isLocallyNoetherian` gives the
  finite-type case for a locally Noetherian source.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Specialization along an equality of points is the transport isomorphism. -/
lemma stalkSpecializes_of_eq_eqToHom {Z : Scheme.{u}} {a b : Z} (e : a = b) :
    Z.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes =
      eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) e).symm := by
  cases e
  simp

/-- The stalk congruence isomorphism along an equality of points is the transport
isomorphism. -/
lemma stalkCongr_of_eq_eqToHom {Z : Scheme.{u}} {a b : Z} (e : a = b) :
    (Z.presheaf.stalkCongr (.of_eq e)).hom =
      eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) e) := by
  cases e
  simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]

/-- Transport isomorphisms of stalks compose along composed equalities of points. -/
lemma stalk_eqToHom_trans {Z : Scheme.{u}} {a b c : Z}
    (e : a = b) (f : b = c) :
    eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) e) ≫
      eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) f) =
        eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) (e.trans f)) := by
  cases e
  cases f
  simp

/-- Transporting a stalk congruence isomorphism along a compatible pair of equalities of
points. -/
lemma stalkCongr_transport {Z : Scheme.{u}} {a b c : Z}
    (e : a = b) (p : a = c) (q : b = c) :
    eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) p).symm ≫
      (Z.presheaf.stalkCongr (.of_eq e)).hom =
        eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z) q).symm := by
  cases e
  have hpq : p = q := Subsingleton.elim _ _
  rw [hpq, stalkCongr_of_eq_eqToHom]
  all_goals simp

/-- The map on stalks at the closed point induced by equal morphisms out of a spectrum agree
up to the transport isomorphism. -/
lemma stalkClosedPointTo_congr {Z : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] {f g : Spec R ⟶ Z} (e : f = g) :
    Scheme.stalkClosedPointTo f =
      eqToHom (congrArg (fun z ↦ Z.presheaf.stalk z)
        (congrArg (fun h : Spec R ⟶ Z => h (IsLocalRing.closedPoint R)) e)) ≫
        Scheme.stalkClosedPointTo g := by
  cases e
  simp

/-- From the canonical equality of morphisms out of the spectrum of the source stalk, read
off the image of the source point and the induced map on stalks. -/
lemma finish_local_extension_of_spec_eq
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (x : X) (y : Y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφlocal : IsLocalHom φ.hom)
    (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y)
    (hspec : Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f)
    (_hf : f ≫ pY = U.ι ≫ pX) :
    ∃ hfy : f ⟨x, hxU⟩ = y,
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
        ((f.stalkMap ⟨x, hxU⟩).hom.comp
          (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = φ.hom := by
  let z : Spec (X.presheaf.stalk x) := IsLocalRing.closedPoint _
  have hclosed : (X.fromSpecStalk x) z = x := by
    change (X.fromSpecStalk x) (IsLocalRing.closedPoint _) = x
    simp
  have hUclosed : U.fromSpecStalkOfMem x hxU z = ⟨x, hxU⟩ := by
    apply Subtype.ext
    change U.ι ((U.fromSpecStalkOfMem x hxU) z) = x
    rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, hclosed]
  have hφz : (Spec.map φ) z = IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
    show Spec.map φ (IsLocalRing.closedPoint (X.presheaf.stalk x)) = _
    exact Spec_closedPoint
  have hpoint : f ((U.fromSpecStalkOfMem x hxU) z) = y := by
    rw [← Scheme.Hom.comp_apply, ← hspec, Scheme.Hom.comp_apply, hφz,
      Scheme.fromSpecStalk_closedPoint]
  have hfy : f ⟨x, hxU⟩ = y := (congrArg f hUclosed).symm.trans hpoint
  refine ⟨hfy, ?_⟩
  let e := AlgebraicGeometry.SpecToEquivOfLocalRing Y
    (CommRingCat.of (X.presheaf.stalk x))
  have he : e (U.fromSpecStalkOfMem x hxU ≫ f) = ⟨y, ⟨φ, hφlocal⟩⟩ := by
    rw [← hspec]
    show e (e.symm ⟨y, ⟨φ, hφlocal⟩⟩) = _
    exact e.apply_symm_apply _
  obtain ⟨hpointSpec, hmap⟩ :=
    (AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff).mp he
  rw [AlgebraicGeometry.SpecToEquivOfLocalRing_apply_fst] at hpointSpec
  change f ((U.fromSpecStalkOfMem x hxU) z) = y at hpointSpec
  rw [AlgebraicGeometry.SpecToEquivOfLocalRing_apply_snd_coe] at hmap
  have hmap' : Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU ≫ f) =
      eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpointSpec) ≫ φ := by
    calc
      _ = (Y.presheaf.stalkCongr (Inseparable.of_eq hpointSpec)).hom ≫ φ := hmap
      _ = _ := congrArg (fun q ↦ q ≫ φ) (stalkCongr_of_eq_eqToHom hpointSpec)
  have hcomp : Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU ≫ f) =
      f.stalkMap ((U.fromSpecStalkOfMem x hxU) z) ≫
        Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU) := by
    simpa using Scheme.stalkClosedPointTo_comp (U.fromSpecStalkOfMem x hxU) f
  have hfacCat :
      eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpointSpec).symm ≫
        f.stalkMap ((U.fromSpecStalkOfMem x hxU) z) ≫
          Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU) = φ := by
    rw [← hcomp, hmap']
    simp
  let q : U.toScheme := (U.fromSpecStalkOfMem x hxU) z
  have hbase : U.ι q = x := congrArg Subtype.val hUclosed
  have hsourceComp :
      U.ι.stalkMap q ≫ Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU) =
        (X.presheaf.stalkCongr (.of_eq hbase)).hom := by
    have hfrom : U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x :=
      Scheme.Opens.fromSpecStalkOfMem_ι U x hxU
    have hsc : Scheme.stalkClosedPointTo (X.fromSpecStalk x) =
        (X.presheaf.stalkCongr (.of_eq hclosed)).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk x
    rw [← Scheme.stalkClosedPointTo_comp, stalkClosedPointTo_congr hfrom, hsc,
      stalkCongr_of_eq_eqToHom hclosed, stalkCongr_of_eq_eqToHom hbase]
    exact stalk_eqToHom_trans (congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ X ↦ g z) hfrom) hclosed
  let qx : U := ⟨x, hxU⟩
  have hsourceCongr := Scheme.Hom.stalkMap_congr_point U.ι q qx hUclosed
  have hsourceOther :
      U.ι.stalkMap q ≫ (U.toScheme.presheaf.stalkCongr (.of_eq hUclosed)).hom ≫
          (U.stalkIso qx).hom = (X.presheaf.stalkCongr (.of_eq hbase)).hom := by
    calc
      _ = (X.presheaf.stalkCongr (.of_eq hbase)).hom ≫ U.ι.stalkMap qx ≫
          (U.stalkIso qx).hom :=
        congrArg (fun k ↦ k ≫ (U.stalkIso qx).hom) hsourceCongr
      _ = (X.presheaf.stalkCongr (.of_eq hbase)).hom := by
        rw [← U.stalkIso_inv qx]
        simp
  have hsource' :
      Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU) =
        (U.toScheme.presheaf.stalkCongr (.of_eq hUclosed)).hom ≫
          (U.stalkIso qx).hom := by
    apply (cancel_epi (U.ι.stalkMap q)).mp
    rw [hsourceComp, hsourceOther]
  have hmapPoint := Scheme.Hom.stalkMap_congr_point f q qx hUclosed
  have htransport :
      eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpoint).symm ≫
          (Y.presheaf.stalkCongr (.of_eq (congrArg f hUclosed))).hom =
        eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm :=
    stalkCongr_transport (congrArg f hUclosed) hpoint hfy
  have hfacOpen :
      eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm ≫
          f.stalkMap qx ≫ (U.stalkIso qx).hom = φ := by
    calc
      _ = eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpoint).symm ≫
          (Y.presheaf.stalkCongr (.of_eq (congrArg f hUclosed))).hom ≫
            f.stalkMap qx ≫ (U.stalkIso qx).hom := by
        rw [← htransport]
        simp [Category.assoc]
      _ = eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpoint).symm ≫
          f.stalkMap q ≫ (U.toScheme.presheaf.stalkCongr (.of_eq hUclosed)).hom ≫
            (U.stalkIso qx).hom :=
        (congrArg (fun k ↦ eqToHom
          (congrArg (fun z ↦ Y.presheaf.stalk z) hpoint).symm ≫ k ≫
            (U.stalkIso qx).hom) hmapPoint).symm
      _ = eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hpoint).symm ≫
          f.stalkMap q ≫ Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem x hxU) := by
        rw [← hsource']
      _ = φ := hfacCat
  simpa only [CommRingCat.hom_comp, RingHom.comp_assoc, qx] using
    congrArg CommRingCat.Hom.hom hfacOpen

/-- Compatibility over the base, restated as an equality of morphisms of stalks. -/
lemma localHom_compat
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    {s : S} (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom) :
    pY.stalkMap y ≫ CommRingCat.ofHom phi =
      S.presheaf.stalkSpecializes (Inseparable.of_eq (hx.trans hy.symm)).specializes ≫
        pX.stalkMap x := by
  have e : pX x = pY y := hx.trans hy.symm
  let φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x := CommRingCat.ofHom phi
  have htransport :
      eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm ≫
        S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes =
      eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm := by
    rw [stalkSpecializes_of_eq_eqToHom e, eqToHom_trans]
  refine (cancel_epi (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm)).mp ?_
  show _ ≫ pY.stalkMap y ≫ φ = _
  calc
    _ = (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm ≫
        pY.stalkMap y) ≫ φ := by rw [Category.assoc]
    _ = eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm ≫ pX.stalkMap x :=
      CommRingCat.hom_ext hphiS
    _ = _ := by rw [← htransport, Category.assoc]

/-- A compatible local homomorphism is induced by a morphism on an open neighbourhood when the
target is locally of finite type over the base and the germ map of the source is injective at
the point. -/
lemma exists_open_morphism_inducing_localHom_of_isGermInjectiveAt
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphi : IsLocalHom phi)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom)
    (hft : LocallyOfFiniteType pY) (hgerm : X.IsGermInjectiveAt x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : (U : Scheme.{u}) ⟶ Y)
      (_hf : f ≫ pY = U.ι ≫ pX)
      (hfy : f ⟨x, hxU⟩ = y),
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxU⟩).hom.comp
            (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = phi := by
  let φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x := CommRingCat.ofHom phi
  have : IsLocalHom φ.hom := hphi
  obtain ⟨U, hxU, f, hspec, hf⟩ := spread_out_of_isGermInjective pX pY (hx.trans hy.symm) φ
    (localHom_compat pX pY x y hx hy phi hphiS)
  exact ⟨U, hxU, f, hf, finish_local_extension_of_spec_eq pX pY x y φ hphi U hxU f hspec hf⟩

/-- A compatible local homomorphism is induced by a morphism on an open neighbourhood when the
target is locally of finite type and the source is reduced with finitely many irreducible
components. -/
@[stacks 0BX6 "local_extension", ega "I 6.5.1" "(ii), X reduced case"]
lemma exists_open_morphism_inducing_localHom_of_isReduced
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphi : IsLocalHom phi)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom)
    (hft : LocallyOfFiniteType pY) (hred : IsReduced X)
    (hcomp : (irreducibleComponents X).Finite) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : (U : Scheme.{u}) ⟶ Y)
      (_hf : f ≫ pY = U.ι ≫ pX)
      (hfy : f ⟨x, hxU⟩ = y),
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxU⟩).hom.comp
            (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = phi := by
  have := X.isGermInjective_of_isReduced_of_finite_irreducibleComponents hcomp
  exact exists_open_morphism_inducing_localHom_of_isGermInjectiveAt pX pY s x y hx hy phi
    hphi hphiS hft inferInstance

/-- A compatible local homomorphism is induced by a morphism on an open neighbourhood when the
target is locally of finite type over the base and the source is integral. -/
@[stacks 0BX6 "local_extension, Y locally of finite type and X integral"]
lemma exists_open_morphism_inducing_localHom_of_isIntegral
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphi : IsLocalHom phi)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom)
    (hft : LocallyOfFiniteType pY) (hint : IsIntegral X) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : (U : Scheme.{u}) ⟶ Y)
      (_hf : f ≫ pY = U.ι ≫ pX)
      (hfy : f ⟨x, hxU⟩ = y),
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxU⟩).hom.comp
            (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = phi :=
  exists_open_morphism_inducing_localHom_of_isGermInjectiveAt pX pY s x y hx hy phi
    hphi hphiS hft inferInstance

/-- A compatible local homomorphism is induced by a morphism on an open neighbourhood when the
target is locally of finite type over the base and the source is locally Noetherian. -/
@[stacks 0BX6 "local_extension, Y locally of finite type and X locally Noetherian"]
lemma exists_open_morphism_inducing_localHom_of_isLocallyNoetherian
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphi : IsLocalHom phi)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom)
    (hft : LocallyOfFiniteType pY) (hnoeth : IsLocallyNoetherian X) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : (U : Scheme.{u}) ⟶ Y)
      (_hf : f ≫ pY = U.ι ≫ pX)
      (hfy : f ⟨x, hxU⟩ = y),
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxU⟩).hom.comp
            (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = phi :=
  exists_open_morphism_inducing_localHom_of_isGermInjectiveAt pX pY s x y hx hy phi
    hphi hphiS hft inferInstance

end AlgebraicGeometry

end
