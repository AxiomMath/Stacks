module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.RingTheory.FiniteStability
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationTerminal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Functoriality of absolute weak normalization

A ring homomorphism induces a unique compatible homomorphism between the absolute weak
normalizations of its source and target.

## Main results

* `AlgebraicGeometry.existsUnique_absoluteWeakNormalizationMap` is that statement.

## Implementation notes

The absolute weak normalization of `A` is a colimit over the finitely presented `A`-algebras
with universal homeomorphic spectrum map, so a map out of it is a compatible family of maps out
of those stages.  For a stage `B` over `A`, the base change `A' ⊗[A] B` is a finitely presented
`A'`-algebra whose spectrum map is again a universal homeomorphism, so it is a stage over `A'`,
and the terminal map of `AlgebraicGeometry.absoluteWeakNormalizationCategoryObject` sends it
into the absolute weak normalization of `A'`.  Uniqueness is uniqueness of a map out of a
colimit, together with surjectivity of the colimit's structure maps onto its carrier, which is
the joint surjectivity of a filtered colimit of types.

Source and target live in possibly different universes `u` and `v`, as the statement is about
a bare ring homomorphism; the colimit side of each is formed within its own universe.

No hypothesis beyond those of Tag 0EUR is used: `A` and `A'` are arbitrary commutative rings.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry


open Algebra
open scoped TensorProduct

private noncomputable def isColimit_forgetCommAlgCat
    {R : Type u} [CommRing R] {J : Type*} [Category* J] [IsConnected J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone c) := by
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat) := by
    change PreservesColimitsOfShape J
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
    infer_instance
  exact isColimitOfPreserves _ hc

private noncomputable def isColimit_underlyingUniverseLift
    {R : Type u} [CommRing R] {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((CategoryTheory.uliftFunctor.{v, u}).mapCocone
      ((forget CommRingCat.{u}).mapCocone
        ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone c))) := by
  let : IsConnected J := IsFiltered.isConnected J
  let hcR := isColimit_forgetCommAlgCat hc
  let hcT := isColimitOfPreserves (forget CommRingCat.{u}) hcR
  exact isColimitOfPreserves CategoryTheory.uliftFunctor.{v, u} hcT

private theorem exists_ringHomOfFilteredColimit
    {R : Type u} [CommRing R] {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    {T : Type v} [CommRing T] (g : ∀ i, F.obj i →+* T)
    (hg : ∀ {i j} (f : i ⟶ j), (g j).comp (F.map f).hom.toRingHom = g i) :
    ∃ k : c.pt →+* T, ∀ i x, k ((c.ι.app i).hom x) = g i x := by
  classical
  let E : J ⥤ Type (max u v) :=
    F ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat ⋙
      forget CommRingCat.{u} ⋙ CategoryTheory.uliftFunctor.{v, u}
  let s : Cocone E :=
    { pt := ULift.{u} T
      ι :=
        { app := fun i => TypeCat.ofHom
            (fun x : E.obj i => (ULift.up (g i x.down) : ULift.{u} T))
          naturality := by
            intro i j f
            ext x
            change (ULift.up (g j ((F.map f).hom x.down)) : ULift.{u} T) =
              ULift.up (g i x.down)
            exact congrArg ULift.up
              (congrArg (fun q : F.obj i →+* T ↦ q x.down) (hg f)) } }
  let ht := isColimit_underlyingUniverseLift.{u, v} hc
  let h := ht.desc s
  have hfac (i : J) (x : F.obj i) : h ⟨(c.ι.app i).hom x⟩ = ⟨g i x⟩ :=
    congrArg (fun q : E.obj i ⟶ s.pt ↦ ConcreteCategory.hom q ⟨x⟩) (ht.fac s i)
  have hs₂ (x y : c.pt) : ∃ i, ∃ a b : F.obj i,
      (c.ι.app i).hom a = x ∧ (c.ι.app i).hom b = y := by
    obtain ⟨i, a, b, ha, hb⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ ht ⟨x⟩ ⟨y⟩
    exact ⟨i, a.down, b.down, ULift.up.inj ha, ULift.up.inj hb⟩
  let : Nonempty J := IsFiltered.nonempty
  refine ⟨
    { toFun := fun x ↦ (h ⟨x⟩).down
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_⟩
  · let i : J := Classical.arbitrary J
    rw [← map_one (c.ι.app i).hom, hfac, map_one]
  · intro x y
    obtain ⟨i, a, b, rfl, rfl⟩ := hs₂ x y
    rw [← map_mul (c.ι.app i).hom, hfac, hfac, hfac, map_mul]
  · let i : J := Classical.arbitrary J
    rw [← map_zero (c.ι.app i).hom, hfac, map_zero]
  · intro x y
    obtain ⟨i, a, b, rfl, rfl⟩ := hs₂ x y
    rw [← map_add (c.ι.app i).hom, hfac, hfac, hfac, map_add]
  · intro i x
    exact ULift.up.inj (hfac i x)

private noncomputable def ringHomOfFilteredColimit
    {R : Type u} [CommRing R] {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    {T : Type v} [CommRing T] (g : ∀ i, F.obj i →+* T)
    (hg : ∀ {i j} (f : i ⟶ j), (g j).comp (F.map f).hom.toRingHom = g i) :
    c.pt →+* T :=
  (exists_ringHomOfFilteredColimit hc g hg).choose

private theorem ringHomOfFilteredColimit_fac
    {R : Type u} [CommRing R] {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    {T : Type v} [CommRing T] (g : ∀ i, F.obj i →+* T)
    (hg : ∀ {i j} (f : i ⟶ j), (g j).comp (F.map f).hom.toRingHom = g i)
    (i : J) (x : F.obj i) :
    ringHomOfFilteredColimit hc g hg ((c.ι.app i).hom x) = g i x :=
  (exists_ringHomOfFilteredColimit hc g hg).choose_spec i x

private noncomputable def smallTensorRep
    {A : Type u} {A' : Type v} {B : Type u}
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [IsScalarTower A A' A']
    [Algebra.FinitePresentation A B] :
    Σ C : CommAlgCat.{v} A', (A' ⊗[A] B) ≃ₐ[A'] C := by
  let T := A' ⊗[A] B
  let : Algebra A' T := inferInstance
  let : Algebra.FinitePresentation A' T := inferInstance
  have hf : (algebraMap A' T).FiniteType :=
    RingHom.finiteType_algebraMap.mpr Algebra.FiniteType.of_finitePresentation
  let h := hf.exists_smallRepr
  let P := h.choose
  let e := h.choose_spec.choose
  have he : algebraMap A' T = e.toRingHom.comp (algebraMap A' P.eval.obj) :=
    h.choose_spec.choose_spec
  let g : P.eval.obj ≃ₐ[A'] T := {
    e with
    commutes' := fun a => (DFunLike.congr_fun he a).symm
  }
  exact ⟨P.eval.obj, g.symm⟩

private theorem isPurelyInseparable_specResidueFieldMap_iff {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (z : Spec (.of B)) :
    letI : (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).asIdeal.IsPrime :=
      (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).isPrime
    letI : z.asIdeal.IsPrime := z.isPrime
    ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap
        z).hom.IsPurelyInseparable ↔
      (Ideal.ResidueField.map (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).asIdeal
        z.asIdeal (algebraMap A B) (by simpa only [Spec.map_apply, CommRingCat.hom_ofHom]
          using PrimeSpectrum.comap_asIdeal (algebraMap A B) z)).IsPurelyInseparable := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let pSpec := Spec.map (CommRingCat.ofHom (algebraMap A B)) z
  let p₀ := pSpec.asIdeal
  let q₀ := z.asIdeal
  let : p₀.IsPrime := pSpec.isPrime
  let : q₀.IsPrime := z.isPrime
  have hpq : p₀ = q₀.comap (algebraMap A B) := by
    simpa [p₀, q₀, pSpec, Spec.map_apply] using
      (PrimeSpectrum.comap_asIdeal (algebraMap A B) z)
  let idealMap := Ideal.ResidueField.map p₀ q₀ (algebraMap A B) hpq
  let ePiso := Scheme.Spec.residueFieldIso (CommRingCat.of A) pSpec
  let eQiso := Scheme.Spec.residueFieldIso (CommRingCat.of B) z
  let eP := ePiso.commRingCatIsoToRingEquiv
  let eQ := eQiso.commRingCatIsoToRingEquiv
  have hP : eP.symm.toRingHom = ePiso.inv.hom := rfl
  have hQ : eQ.toRingHom = eQiso.hom.hom := rfl
  have hbridge := specResidueFieldMap_bridge (CommRingCat.ofHom (algebraMap A B)) z
  have hbridge' : eQ.toRingHom.comp
      ((f.residueFieldMap z).hom.comp eP.symm.toRingHom) = idealMap := by
    rw [← RingHom.comp_assoc, hQ, hP]
    rw [CommRingCat.hom_comp ePiso.inv
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap z ≫ eQiso.hom),
      CommRingCat.hom_comp
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap z) eQiso.hom] at hbridge
    simpa [ePiso, eQiso, f, pSpec, p₀, q₀, idealMap, Spec.map_apply,
      CommRingCat.hom_ofHom] using hbridge
  change (f.residueFieldMap z).hom.IsPurelyInseparable ↔ idealMap.IsPurelyInseparable
  refine ⟨fun hpure ↦ hbridge' ▸
    ((RingHom.isPurelyInseparable_of_surjective _ eP.symm.surjective).comp hpure).comp
      (RingHom.isPurelyInseparable_of_surjective _ eQ.surjective), fun hIdealPure ↦ ?_⟩
  have hmap : (f.residueFieldMap z).hom =
      eQ.symm.toRingHom.comp (idealMap.comp eP.toRingHom) := by
    ext a
    apply eQ.injective
    have heval := congrArg (fun g => g (eP a)) hbridge'
    have heval' : eQ.toRingHom ((f.residueFieldMap z).hom a) = idealMap (eP a) := by
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using heval
    change eQ.toRingHom ((f.residueFieldMap z).hom a) =
      eQ.toRingHom (eQ.symm.toRingHom (idealMap (eP.toRingHom a)))
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] using heval'
  rw [hmap]
  simpa [p₀] using RingHom.isPurelyInseparable_congr eP eQ idealMap hIdealPure

private theorem universalHomeomorphism_ringCriterion {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    Algebra.IsIntegral A B ∧
      Function.Bijective (PrimeSpectrum.comap (algebraMap A B)) ∧
      (∀ (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
        (hpq : p = q.comap (algebraMap A B)),
        (Ideal.ResidueField.map p q (algebraMap A B) hpq).IsPurelyInseparable) := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  obtain ⟨hInt, hUI, _⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hB
  have hbij : Function.Bijective (PrimeSpectrum.comap (algebraMap A B)) :=
    (hB.universally_isHomeomorph _ _ _ IsPullback.of_id_snd).bijective
  have hcrit := ((tfae_universallyInjective f).out 1 3).mp hUI
  refine ⟨algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hInt), hbij, ?_⟩
  rintro _ _ q hq rfl
  exact (isPurelyInseparable_specResidueFieldMap_iff ⟨q, hq⟩).mp (hcrit.2 ⟨q, hq⟩)

private theorem universalHomeomorphism_of_ringCriterion {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hInt : Algebra.IsIntegral A B)
    (hbij : Function.Bijective (PrimeSpectrum.comap (algebraMap A B)))
    (hins : ∀ (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
      (hpq : p = q.comap (algebraMap A B)),
      (Ideal.ResidueField.map p q (algebraMap A B) hpq).IsPurelyInseparable) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  apply (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
  refine ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr hInt), ?_, ?_⟩
  · apply ((tfae_universallyInjective f).out 1 3).mpr
    exact ⟨hbij.injective, fun z ↦ (isPurelyInseparable_specResidueFieldMap_iff z).mpr
      (@hins _ (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).isPrime _ z.isPrime _)⟩
  · exact ⟨hbij.surjective⟩

private theorem universalHomeomorphism_smallBaseChange
    {A B : Type u} {A' C : Type v}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing C]
    [Algebra A B] [Algebra A A'] [Algebra A' C]
    [IsScalarTower A A' A']
    (e : (A' ⊗[A] B) ≃ₐ[A'] C)
    (hB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A' C)).op) := by
  let T := A' ⊗[A] B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A B T := inferInstance
  let : Algebra A C := Algebra.compHom C (algebraMap A A')
  let : IsScalarTower A A' C :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := A') (A := C) rfl
  let : Algebra B C :=
    ((AlgHom.restrictScalars A e.toAlgHom).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B))).toAlgebra
  let : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := C) (by
      ext a
      simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      rw [IsScalarTower.algebraMap_apply A A' C, ← e.commutes]
      change e (algebraMap A' T (algebraMap A A' a)) =
        e (algebraMap B T (algebraMap A B a))
      congr 1
      exact (IsScalarTower.algebraMap_apply A A' T a).symm.trans
        (IsScalarTower.algebraMap_apply A B T a))
  have hpush : Algebra.IsPushout A B A' C := by
    let : Algebra B T := Algebra.TensorProduct.rightAlgebra
    let : IsScalarTower A A' T := inferInstance
    let : IsScalarTower A B T := inferInstance
    apply Algebra.IsPushout.symm
    apply Algebra.IsPushout.of_equiv e
    ext b
    rfl
  obtain ⟨hInt, hbij, hins⟩ := universalHomeomorphism_ringCriterion hB
  let : Algebra.IsIntegral A B := hInt
  let : Algebra.IsPushout A B A' C := hpush
  obtain ⟨_, hbase⟩ :=
    PrimeSpectrum.isHomeomorph_comap_and_baseChange_of_bijective_comap_of_isPurelyInseparable
      hbij hins
  obtain ⟨hIntC, hbijC, hinsC⟩ := hbase A' C
  exact universalHomeomorphism_of_ringCriterion hIntC hbijC hinsC

private noncomputable def stageRep
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    (i : AbsoluteWeakNormalizationIndex A) :
    Σ C : CommAlgCat.{v} A',
      (A' ⊗[A] (absoluteWeakNormalizationDiagram A).obj i) ≃ₐ[A'] C := by
  let : Algebra.FinitePresentation A ((absoluteWeakNormalizationDiagram A).obj i) :=
    absoluteWeakNormalizationDiagram_obj_finitePresentation A i
  exact smallTensorRep

private noncomputable def candidateSmall
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    (i : AbsoluteWeakNormalizationIndex A) :
    AbsoluteWeakNormalizationCategory A' :=
  ⟨(stageRep (A := A) (A' := A') i).1,
    universalHomeomorphism_smallBaseChange
      (stageRep (A := A) (A' := A') i).2
      (absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i)⟩

private noncomputable def candidateSmallMap
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    {i j : AbsoluteWeakNormalizationIndex A} (f : i ⟶ j) :
    candidateSmall (A := A) (A' := A') i ⟶
      candidateSmall (A := A) (A' := A') j := by
  let ri := stageRep (A := A) (A' := A') i
  let rj := stageRep (A := A) (A' := A') j
  let t : (A' ⊗[A] (absoluteWeakNormalizationDiagram A).obj i) →ₐ[A']
      (A' ⊗[A] (absoluteWeakNormalizationDiagram A).obj j) :=
    Algebra.TensorProduct.map (AlgHom.id A' A') ((absoluteWeakNormalizationDiagram A).map f).hom
  exact ObjectProperty.homMk (CommAlgCat.ofHom
    (rj.2.toAlgHom.comp (t.comp ri.2.symm.toAlgHom)))

private noncomputable def stageComponent
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    (i : AbsoluteWeakNormalizationIndex A) :
    (absoluteWeakNormalizationDiagram A).obj i →+* AbsoluteWeakNormalization A' := by
  let r := stageRep (A := A) (A' := A') i
  let k := (absoluteWeakNormalizationCategoryObject_isTerminal A').from
    (candidateSmall (A := A) (A' := A') i)
  exact (k.hom.hom.toRingHom.comp r.2.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := A) (A := A')
      (B := (absoluteWeakNormalizationDiagram A).obj i)).toRingHom

private theorem stageComponent_naturality
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    {i j : AbsoluteWeakNormalizationIndex A} (f : i ⟶ j) :
    (stageComponent (A := A) (A' := A') j).comp
      ((absoluteWeakNormalizationDiagram A).map f).hom.toRingHom =
      stageComponent (A := A) (A' := A') i := by
  let ri := stageRep (A := A) (A' := A') i
  let rj := stageRep (A := A) (A' := A') j
  let ki := (absoluteWeakNormalizationCategoryObject_isTerminal A').from
    (candidateSmall (A := A) (A' := A') i)
  let kj := (absoluteWeakNormalizationCategoryObject_isTerminal A').from
    (candidateSmall (A := A) (A' := A') j)
  let t := candidateSmallMap (A := A) (A' := A') f
  have ht : t ≫ kj = ki :=
    (absoluteWeakNormalizationCategoryObject_isTerminal A').hom_ext _ _
  ext x
  have ht' : kj.hom.hom.comp t.hom.hom = ki.hom.hom := by
    simpa [t, CommAlgCat.hom_comp] using congrArg (fun q => q.hom.hom) ht
  have hi : t.hom.hom (ri.2
      (Algebra.TensorProduct.includeRight (R := A) (A := A')
        (B := (absoluteWeakNormalizationDiagram A).obj i) x)) =
      rj.2 (Algebra.TensorProduct.includeRight (R := A) (A := A')
        (B := (absoluteWeakNormalizationDiagram A).obj j)
        (((absoluteWeakNormalizationDiagram A).map f).hom x)) := by
    change (rj.2.toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id A' A')
        ((absoluteWeakNormalizationDiagram A).map f).hom).comp
        ri.2.symm.toAlgHom)) (ri.2 _) = _
    simp [Algebra.TensorProduct.includeRight_apply]
  change kj.hom.hom (rj.2 (Algebra.TensorProduct.includeRight
      (R := A) (A := A') (B := (absoluteWeakNormalizationDiagram A).obj j)
      (((absoluteWeakNormalizationDiagram A).map f).hom x))) =
    ki.hom.hom (ri.2 (Algebra.TensorProduct.includeRight
      (R := A) (A := A') (B := (absoluteWeakNormalizationDiagram A).obj i) x))
  rw [← hi]
  exact (AlgHom.ext_iff.mp ht') _

private theorem stageComponent_algebraMap
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    (i : AbsoluteWeakNormalizationIndex A) (a : A) :
    stageComponent (A := A) (A' := A') i
      (algebraMap A ((absoluteWeakNormalizationDiagram A).obj i) a) =
      algebraMap A' (AbsoluteWeakNormalization A') (algebraMap A A' a) := by
  let r := stageRep (A := A) (A' := A') i
  let k := (absoluteWeakNormalizationCategoryObject_isTerminal A').from
    (candidateSmall (A := A) (A' := A') i)
  change k.hom.hom (r.2 (Algebra.TensorProduct.includeRight
    (R := A) (A := A') (B := (absoluteWeakNormalizationDiagram A).obj i)
    (algebraMap A ((absoluteWeakNormalizationDiagram A).obj i) a))) = _
  rw [Algebra.TensorProduct.includeRight.commutes, IsScalarTower.algebraMap_apply A A'
    (A' ⊗[A] (absoluteWeakNormalizationDiagram A).obj i), r.2.commutes]
  change k.hom.hom (algebraMap A' (candidateSmall (A := A) (A' := A') i).obj
    (algebraMap A A' a)) = _
  exact k.hom.hom.commutes _

private theorem ringHom_ext_of_filteredColimit
    {R : Type u} [CommRing R] {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    {T : Type v} [CommRing T] {p q : c.pt →+* T}
    (h : ∀ i (x : F.obj i), p ((c.ι.app i).hom x) = q ((c.ι.app i).hom x)) :
    p = q := by
  ext x
  let ht := isColimit_underlyingUniverseLift.{u, v} hc
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit ht (ULift.up x)
  have hy' : (c.ι.app i).hom y.down = x := ULift.up.inj hy
  rw [← hy']
  exact h i y.down

private theorem eq_stageComponent_of_comp_algebraMap
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    [Algebra A A'] [IsScalarTower A A' A']
    (ψ : AbsoluteWeakNormalization A →+* AbsoluteWeakNormalization A')
    (hψ : ψ.comp (algebraMap A (AbsoluteWeakNormalization A)) =
      (algebraMap A' (AbsoluteWeakNormalization A')).comp (algebraMap A A'))
    (i : AbsoluteWeakNormalizationIndex A) (x : (absoluteWeakNormalizationDiagram A).obj i) :
    ψ ((colimit.ι (absoluteWeakNormalizationDiagram A) i).hom x) =
      stageComponent (A := A) (A' := A') i x := by
  let Z := (absoluteWeakNormalizationCategoryObject A').obj
  let : Algebra A Z := Algebra.compHom Z (algebraMap A A')
  let : IsScalarTower A A' Z :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := A') (A := Z) rfl
  let D := absoluteWeakNormalizationDiagram A
  let ψalg : AbsoluteWeakNormalization A →ₐ[A] Z := AlgHom.mk ψ (by
    intro a
    have ha := (RingHom.ext_iff.mp hψ) a
    change ψ (algebraMap A (AbsoluteWeakNormalization A) a) =
      (algebraMap A' (AbsoluteWeakNormalization A')) (algebraMap A A' a) at ha
    change ψ (algebraMap A (AbsoluteWeakNormalization A) a) = algebraMap A Z a
    rw [ha]
    rfl)
  let r := stageRep (A := A) (A' := A') i
  let k := (absoluteWeakNormalizationCategoryObject_isTerminal A').from
    (candidateSmall (A := A) (A' := A') i)
  let l : (A' ⊗[A] D.obj i) →ₐ[A'] Z :=
    Algebra.TensorProduct.lift (Algebra.ofId A' Z)
      (ψalg.comp (colimit.ι D i).hom) (fun _ _ ↦ Commute.all _ _)
  let li : candidateSmall (A := A) (A' := A') i ⟶
      absoluteWeakNormalizationCategoryObject A' :=
    ObjectProperty.homMk (CommAlgCat.ofHom (l.comp r.2.symm.toAlgHom))
  have hl : li = k :=
    (absoluteWeakNormalizationCategoryObject_isTerminal A').hom_ext _ _
  have hl' : l.comp r.2.symm.toAlgHom = k.hom.hom :=
    congrArg (fun t => t.hom.hom) hl
  have hval : l (Algebra.TensorProduct.includeRight (R := A) (A := A')
      (B := D.obj i) x) =
      k.hom.hom (r.2 (Algebra.TensorProduct.includeRight (R := A) (A := A')
        (B := D.obj i) x)) := by
    have h := congrArg (fun t : r.1 →ₐ[A'] Z =>
      t (r.2 (Algebra.TensorProduct.includeRight (R := A) (A := A')
        (B := D.obj i) x))) hl'
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.symm_apply_apply] at h
    exact h
  have heval : l (Algebra.TensorProduct.includeRight (R := A) (A := A')
      (B := D.obj i) x) = ψ ((colimit.ι D i).hom x) := by
    simp only [l, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_one, one_mul]
    rfl
  rw [← heval]
  exact hval

/-- A ring homomorphism induces a unique compatible homomorphism between absolute weak
normalizations. -/
@[stacks 0EUR "awn_functoriality"]
public theorem existsUnique_absoluteWeakNormalizationMap
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φawn : AbsoluteWeakNormalization A →+* AbsoluteWeakNormalization A',
      φawn.comp (algebraMap A (AbsoluteWeakNormalization A)) =
        (algebraMap A' (AbsoluteWeakNormalization A')).comp φ := by
  let : Algebra A A' := RingHom.toAlgebra φ
  let : IsScalarTower A A' A' :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := A') (A := A') rfl
  let D := absoluteWeakNormalizationDiagram A
  let g : ∀ i, D.obj i →+* AbsoluteWeakNormalization A' :=
    fun i => stageComponent (A := A) (A' := A') i
  have hg : ∀ {i j} (f : i ⟶ j), (g j).comp (D.map f).hom.toRingHom = g i :=
    fun f ↦ stageComponent_naturality f
  let q : AbsoluteWeakNormalization A →+* AbsoluteWeakNormalization A' :=
    ringHomOfFilteredColimit (colimit.isColimit D) g hg
  refine ⟨q, ?_, fun ψ hψ ↦ ringHom_ext_of_filteredColimit (colimit.isColimit D) fun i x ↦ ?_⟩
  · ext a
    let : Nonempty (AbsoluteWeakNormalizationIndex A) := IsFiltered.nonempty
    let i : AbsoluteWeakNormalizationIndex A := Classical.arbitrary _
    change q (algebraMap A (AbsoluteWeakNormalization A) a) =
      algebraMap A' (AbsoluteWeakNormalization A') (φ a)
    rw [← (colimit.ι D i).hom.commutes a]
    exact (ringHomOfFilteredColimit_fac (colimit.isColimit D) g hg i _).trans
      (stageComponent_algebraMap i a)
  · rw [ringHomOfFilteredColimit_fac]
    exact eq_stageComponent_of_comp_algebraMap ψ hψ i x

end AlgebraicGeometry

end
