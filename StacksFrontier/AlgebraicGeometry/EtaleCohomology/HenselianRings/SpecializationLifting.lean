module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.GeometricPoints
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# Lifting specializations to a strict henselization

The canonical morphism from the strict henselization of a scheme at a geometric point to that
scheme is weakly étale, so it is flat and generalizing and it induces separable algebraic
residue-field extensions. Consequently a geometric point over a generization of the image of the
geometric point lifts to the strict henselization, and the lift still specializes to the
canonical point there.

## Main results

* `AlgebraicGeometry.weaklyEtale_etaleLocalRing` says the étale local ring at a geometric point
  is weakly étale over the ordinary local ring at its image.
* `AlgebraicGeometry.strictHenselizationToBase_weaklyEtale` says the structure morphism of the
  strict henselization is weakly étale.
* `AlgebraicGeometry.isSeparable_residueField_strictHenselizationToBase` says the residue field
  at a point of the strict henselization is separable over the residue field at its image.
* `AlgebraicGeometry.exists_lift_toStrictHenselization_of_specializes` lifts a geometric point
  over a generization to the strict henselization, compatibly with the specialization.

## References

* [Stacks Project, Tag 0GJ5](https://stacks.math.columbia.edu/tag/0GJ5)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The étale local ring at a geometric point is weakly étale over the ordinary local ring at
the image of that point. -/
public theorem weaklyEtale_etaleLocalRing (s : GeometricPoint S) :
    Algebra.WeaklyEtale ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      ↥(etaleLocalRing B S hS s) :=
  Algebra.weaklyEtale_of_ind_etale (indEtale_etaleLocalRing B S hS s)

/-- The canonical morphism from the strict henselization at a geometric point to the scheme is
weakly étale. -/
public theorem strictHenselizationToBase_weaklyEtale (s : GeometricPoint S) :
    WeaklyEtale (strictHenselizationToBase B S hS s) := by
  have hspec : WeaklyEtale (Spec.map (CommRingCat.ofHom
      (structureSheafStalkFromLocalRing B S hS s))) :=
    (ProEtale.weaklyEtale_spec_iff _ _ _).2 (weaklyEtale_etaleLocalRing B S hS s)
  change WeaklyEtale (Spec.map (CommRingCat.ofHom
    (structureSheafStalkFromLocalRing B S hS s)) ≫
      S.fromSpecStalk (s.hom (closedPoint s.residueField)))
  have : WeaklyEtale (S.fromSpecStalk (s.hom (closedPoint s.residueField))) :=
    weaklyEtale_fromSpecStalk S (s.hom (closedPoint s.residueField))
  infer_instance

/-- The residue field map of a morphism at a point, transported along the identifications of the
residue fields with the residue fields of the stalks, is the map induced on stalks. -/
private theorem equivQuotMaximalIdeal_comp_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (maximalIdeal (X.presheaf.stalk x))
      (Localization.AtPrime (maximalIdeal (X.presheaf.stalk x)))).toRingHom.comp
        (f.residueFieldMap x).hom =
      (Ideal.ResidueField.map (maximalIdeal (Y.presheaf.stalk (f x)))
        (maximalIdeal (X.presheaf.stalk x)) (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom).symm).comp
        (IsLocalization.AtPrime.equivQuotMaximalIdeal (maximalIdeal (Y.presheaf.stalk (f x)))
          (Localization.AtPrime (maximalIdeal (Y.presheaf.stalk (f x))))).toRingHom := by
  ext z
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let p := maximalIdeal A
  let q := maximalIdeal C
  change IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
      (IsLocalRing.ResidueField.map (f.stalkMap x).hom (IsLocalRing.residue A r)) =
    Ideal.ResidueField.map p q (f.stalkMap x).hom _
      (IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)
        (IsLocalRing.residue A r))
  have hl : IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
      (IsLocalRing.ResidueField.map (f.stalkMap x).hom (IsLocalRing.residue A r)) =
      algebraMap C q.ResidueField ((f.stalkMap x).hom r) := by
    rw [IsLocalRing.ResidueField.map_residue]
    exact IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk q _ _
  have hr : IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)
      (IsLocalRing.residue A r) = algebraMap A p.ResidueField r :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p _ _
  rw [hl, hr, Ideal.ResidueField.map_algebraMap]

/-- The residue field at a point of the strict henselization at a geometric point is separable
over the residue field at the image of that point in the scheme. -/
@[stacks 0GJ5 "the residue-field extension"]
public theorem isSeparable_residueField_strictHenselizationToBase (sbar : GeometricPoint S)
    (x : strictHenselization B S hS sbar) :
    let f := strictHenselizationToBase B S hS sbar
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (S.residueField (f x))
      ((strictHenselization B S hS sbar).residueField x) := by
  dsimp only
  let f := strictHenselizationToBase B S hS sbar
  let X := strictHenselization B S hS sbar
  let A := S.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let p := IsLocalRing.maximalIdeal A
  let q := IsLocalRing.maximalIdeal C
  let : Algebra A C := (f.stalkMap x).hom.toAlgebra
  let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal C).isPrime
  let : IsLocalHom (f.stalkMap x).hom := inferInstance
  have hpq : p = q.comap (f.stalkMap x).hom :=
    (IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom).symm
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (f.stalkMap x).hom hpq).toAlgebra
  have : WeaklyEtale f := strictHenselizationToBase_weaklyEtale B S hS sbar
  have hres := isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A C
    (ProEtale.weaklyEtale_stalkMap f x) p q hpq
  let eY : S.residueField (f x) ≃+* p.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)).toRingEquiv
  let eX : X.residueField x ≃+* q.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)).toRingEquiv
  have hcompat : eX.toRingHom.comp ((f.residueFieldMap x).hom) =
      (Ideal.ResidueField.map p q (f.stalkMap x).hom hpq).comp eY.toRingHom :=
    equivQuotMaximalIdeal_comp_residueFieldMap f x
  have he : (algebraMap (S.residueField (f x)) (X.residueField x)).comp
      eY.symm.toRingHom = eX.symm.toRingHom.comp
      (algebraMap p.ResidueField q.ResidueField) := by
    refine RingHom.ext fun z => eX.injective ?_
    change eX ((f.residueFieldMap x).hom (eY.symm z)) =
      eX (eX.symm ((algebraMap p.ResidueField q.ResidueField) z))
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcompat (eY.symm z)).trans
      (congrArg (Ideal.ResidueField.map p q (f.stalkMap x).hom hpq) (eY.apply_symm_apply z))
  exact (Algebra.IsSeparable.iff_of_equiv_equiv eY.symm eX.symm he).mp hres.1

/-- A geometric point over a generization lifts to the strict henselization at a geometric point
over the specialization, and the lifted point specializes to the canonical point of the strict
henselization. -/
@[stacks 0GJ5 "lifting the generic geometric point"]
public theorem exists_lift_toStrictHenselization_of_specializes
    (t s : S) (hts : t ⤳ s) (tbar sbar : GeometricPoint S)
    (ht : tbar.LiesOver t) (hs : sbar.LiesOver s) :
    ∃ lift : tbar.source ⟶ strictHenselization B S hS sbar,
      (lift ≫ strictHenselizationToBase B S hS sbar = tbar.hom) ∧
      (lift default ⤳ (geometricPointToStrictHenselization B S hS sbar) default) := by
  let f := strictHenselizationToBase B S hS sbar
  let X := strictHenselization B S hS sbar
  let sgeom := geometricPointToStrictHenselization B S hS sbar
  have : WeaklyEtale f := strictHenselizationToBase_weaklyEtale B S hS sbar
  have hsbase : f (sgeom default) = s := by
    have hcomp := congrArg (fun g : sbar.source ⟶ S => g default)
      (geometricPointToStrictHenselization_comp B S hS sbar)
    change f (sgeom default) = sbar.hom default at hcomp
    simpa [GeometricPoint.LiesOver] using hcomp.trans hs
  have hgen : t ⤳ f (sgeom default) := by simpa [hsbase] using hts
  obtain ⟨x, hxs, hxt⟩ := (Flat.generalizingMap f) hgen
  let K := tbar.residueField
  let y₀ : S := tbar.hom (closedPoint K)
  have hdefault : (default : tbar.source) = closedPoint K := Subsingleton.elim _ _
  have hyt : y₀ = t := by
    dsimp [y₀]
    rw [← hdefault]
    exact ht
  have hxy : f x = y₀ := hxt.trans hyt.symm
  let a₀ : S.residueField y₀ ⟶ .of K :=
    S.descResidueField (Scheme.stalkClosedPointTo tbar.hom)
  let e₀ := S.residueFieldCongr hxy
  let a : S.residueField (f x) ⟶ .of K := e₀.hom ≫ a₀
  let A := S.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let p := IsLocalRing.maximalIdeal A
  let q := IsLocalRing.maximalIdeal C
  let g := f.stalkMap x
  let : Algebra A C := g.hom.toAlgebra
  let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal C).isPrime
  let : IsLocalHom g.hom := inferInstance
  have hpq : p = q.comap g.hom := (IsLocalRing.maximalIdeal_comap g.hom).symm
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q g.hom hpq).toAlgebra
  have hres := isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A C
    (ProEtale.weaklyEtale_stalkMap f x) p q hpq
  have : Algebra.IsAlgebraic p.ResidueField q.ResidueField := hres.2
  let eY : S.residueField (f x) ≃+* p.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)).toRingEquiv
  let eX : X.residueField x ≃+* q.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)).toRingEquiv
  let α : p.ResidueField →+* K := a.hom.comp eY.symm.toRingHom
  let : Algebra p.ResidueField K := α.toAlgebra
  let c : q.ResidueField →ₐ[p.ResidueField] K := IsAlgClosed.lift
  let β : X.residueField x →+* K := c.toRingHom.comp eX.toRingHom
  have hcompat : eX.toRingHom.comp (f.residueFieldMap x).hom =
      (Ideal.ResidueField.map p q g.hom hpq).comp eY.toRingHom :=
    equivQuotMaximalIdeal_comp_residueFieldMap f x
  have hfac : β.comp (f.residueFieldMap x).hom = a.hom := by
    ext z
    change c ((eX.toRingHom.comp (f.residueFieldMap x).hom) z) = a.hom z
    rw [RingHom.congr_fun hcompat z]
    change c (algebraMap p.ResidueField q.ResidueField (eY z)) = a.hom z
    rw [c.commutes]
    change α (eY z) = a.hom z
    simp [α]
  have hmap : f.residueFieldMap x ≫ CommRingCat.ofHom β = a :=
    CommRingCat.hom_ext hfac
  have hs₀ : Spec.map a₀ ≫ S.fromSpecResidueField y₀ = tbar.hom :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S tbar.hom
  have hs' : Spec.map a ≫ S.fromSpecResidueField (f x) = tbar.hom :=
    calc
      Spec.map a ≫ S.fromSpecResidueField (f x) =
          Spec.map a₀ ≫ (Spec.map e₀.hom ≫ S.fromSpecResidueField (f x)) := by
        simp [a, Category.assoc]
      _ = Spec.map a₀ ≫ S.fromSpecResidueField y₀ := by
        rw [S.residueFieldCongr_fromSpecResidueField hxy]
      _ = tbar.hom := hs₀
  let lift : tbar.source ⟶ X := Spec.map (CommRingCat.ofHom β) ≫ X.fromSpecResidueField x
  refine ⟨lift, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom β) ≫ X.fromSpecResidueField x ≫ f = tbar.hom
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← hs', ← hmap, ← Category.assoc,
      ← Spec.map_comp]
    rfl
  · have hpoint : lift default = x := Scheme.fromSpecResidueField_apply x _
    exact hpoint ▸ hxs

add_to_stacks 0GJ5 "the special geometric point"
  geometricPointToStrictHenselization
add_to_stacks 0GJ5 "compatibility of the special geometric point"
  geometricPointToStrictHenselization_comp

end AlgebraicGeometry

end
