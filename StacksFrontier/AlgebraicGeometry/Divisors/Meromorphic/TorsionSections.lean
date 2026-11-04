module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.TorsionSubsheaf.Basic

/-!
# Torsion sections on an integral scheme

For a quasi-coherent module on an integral scheme, a section over a nonempty open is torsion
at one stalk exactly when it is torsion at every stalk, and this is equivalent to vanishing at
the generic point and to vanishing in the pushforward from the generic point.

## Main results

* `AlgebraicGeometry.torsion_section_tfae` gives the four equivalent characterizations.

## References

* [Stacks Project, Tag 0AXR](https://stacks.math.columbia.edu/tag/0AXR)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.TorsionSubsheaf (IsTorsionElement)

universe u

namespace AlgebraicGeometry

private lemma affineSectionsIso_germ_eq_zero_iff {X : Scheme.{u}}
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (t : Γ(F.restrict hU.fromSpec, ⊤)) (x : Spec Γ(X, U)) :
    F.presheaf.germ U (hU.fromSpec x) (hU.isoSpec.inv x).2
      ((affineSectionsIso F hU).hom t) = 0 ↔
    (F.restrict hU.fromSpec).presheaf.germ ⊤ x trivial t = 0 := by
  have he : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hbridge : (affineSectionsIso F hU).hom t =
      F.presheaf.map (eqToHom he.symm).op t := rfl
  have hg' := ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app hU.fromSpec x F (U := ⊤) trivial) t
  have hkey : F.presheaf.germ U (hU.fromSpec x) (hU.isoSpec.inv x).2
        ((affineSectionsIso F hU).hom t) =
      (Scheme.Modules.restrictStalkNatIso hU.fromSpec x).hom.app F
        ((F.restrict hU.fromSpec).presheaf.germ ⊤ x trivial t) := by
    rw [hbridge]
    exact (F.presheaf.germ_res_apply (eqToHom he.symm) (hU.fromSpec x)
      (hU.isoSpec.inv x).2 t).trans hg'.symm
  rw [hkey]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.restrictStalkNatIso hU.fromSpec x).hom.app F)).injective

private lemma germ_eq_zero_iff_of_point_eq {X : Scheme.{u}} (F : X.Modules)
    {V : X.Opens} (s : Γ(F, V)) {x y : X} (hxy : x = y)
    (hx : x ∈ V) (hy : y ∈ V) :
    F.presheaf.germ V x hx s = 0 ↔ F.presheaf.germ V y hy s = 0 := by
  subst hxy
  rfl

private lemma spec_generic_germ_zero_annihilator
    (R : CommRingCat.{u}) [IsDomain R] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (s : Γ(F, ⊤))
    (hη : F.presheaf.germ ⊤ (genericPoint (Spec R)) trivial s = 0) :
    ∃ r : R, r ≠ 0 ∧ r • s = 0 := by
  obtain ⟨r, hr, hrs⟩ :=
    (germ_eq_zero_iff_exists_smul_eq_zero F s (genericPoint (Spec R))).mp hη
  refine ⟨r, fun hr0 ↦ hr ?_, hrs⟩
  rw [hr0, genericPoint_eq_bot_of_affine]
  simp

private lemma generic_germ_zero_torsion_at
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (s : Γ(F, U)) (x : X) (hx : x ∈ U)
    (hη : F.presheaf.germ U (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (show Nonempty U from ⟨⟨x, hx⟩⟩))) s = 0) :
    letI : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    IsTorsionElement (R := X.presheaf.stalk x) (M := ↑(F.presheaf.stalk x))
      (F.presheaf.germ U x hx s) := by
  classical
  let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  let : Module (X.presheaf.stalk (genericPoint X))
      ↑(F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsDomain Γ(X, V) := inferInstance
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hfgeneric : hV.fromSpec (genericPoint (Spec Γ(X, V))) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion hV.fromSpec
  have hηV : genericPoint X ∈ V :=
    (genericPoint_specializes x).mem_open V.isOpen hxV
  have hVUle : V ≤ U := hVU
  let sV : Γ(F, V) := F.presheaf.map (homOfLE hVUle).op s
  have hsVη : F.presheaf.germ V (genericPoint X) hηV sV = 0 := by
    dsimp only [sV]
    rw [F.presheaf.germ_res_apply (homOfLE hVUle) (genericPoint X) hηV]
    exact hη
  let t : Γ(F.restrict hV.fromSpec, ⊤) := (affineSectionsIso F hV).inv sV
  have htη : (F.restrict hV.fromSpec).presheaf.germ ⊤
      (genericPoint (Spec Γ(X, V))) trivial t = 0 := by
    apply (affineSectionsIso_germ_eq_zero_iff F hV t
      (genericPoint (Spec Γ(X, V)))).mp
    simpa [t] using (germ_eq_zero_iff_of_point_eq F sV hfgeneric.symm
      hηV ((hV.isoSpec.inv (genericPoint (Spec Γ(X, V)))).2)).mp hsVη
  obtain ⟨r, hr, hrs⟩ :=
    spec_generic_germ_zero_annihilator (CommRingCat.of Γ(X, V))
      (F.restrict hV.fromSpec) t htη
  have hkillV : r • sV = 0 := by
    have h := congrArg (fun q => (affineSectionsIso F hV).hom q) hrs
    rw [affineSectionsIso_hom_smul] at h
    simpa [t] using h
  have hscalar : X.presheaf.germ V x hxV r ≠ 0 := fun hzero ↦
    hr (germ_injective_of_isIntegral X x hxV (by simpa using hzero))
  have hkillx : (X.presheaf.germ V x hxV r) •
      (F.presheaf.germ V x hxV sV) = 0 := by
    calc
      (X.presheaf.germ V x hxV r) • (F.presheaf.germ V x hxV sV) =
          F.presheaf.germ V x hxV (r • sV) := (F.val.germ_smul x V hxV r sV).symm
      _ = 0 := by rw [hkillV]; simp
  refine ⟨X.presheaf.germ V x hxV r, hscalar, ?_⟩
  have hres : F.presheaf.germ V x hxV sV = F.presheaf.germ U x hx s := by
    show F.presheaf.germ V x hxV (F.presheaf.map (homOfLE hVUle).op s) = _
    rw [F.presheaf.germ_res_apply]
  convert hkillx using 1; simp [hres]; rfl

private def torsionAtStalk (X : Scheme.{u}) (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) (x : X) (hx : x ∈ U) : Prop :=
  letI : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  IsTorsionElement (R := X.presheaf.stalk x) (M := ↑(F.presheaf.stalk x))
    (F.presheaf.germ U x hx s)

private lemma torsion_at_implies_generic_germ_zero
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) (x : X) (hx : x ∈ U)
    (ht : torsionAtStalk X F U s x hx) :
    F.presheaf.germ U (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (show Nonempty U from ⟨⟨x, hx⟩⟩))) s = 0 := by
  classical
  let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  let : Module (X.presheaf.stalk (genericPoint X))
      ↑(F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  rcases ht with ⟨r, hr, hrs⟩
  obtain ⟨V, hxV, hV, a, ha⟩ :=
    X.presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens x r
  let W := V ⊓ U
  have hxW : x ∈ W := ⟨hxV, hx⟩
  let aW : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op a
  let sW : Γ(F, W) := F.presheaf.map (homOfLE inf_le_right).op s
  have haW : X.presheaf.germ W x hxW aW = r := by
    dsimp only [aW]
    rw [X.presheaf.germ_res_apply]
    exact ha
  have hsW : F.presheaf.germ W x hxW sW = F.presheaf.germ U x hx s := by
    dsimp only [sW]
    rw [F.presheaf.germ_res_apply]
  have hprod : F.presheaf.germ W x hxW (aW • sW) = 0 := by
    calc
      F.presheaf.germ W x hxW (aW • sW) =
          (X.presheaf.germ W x hxW aW) • (F.presheaf.germ W x hxW sW) :=
        F.val.germ_smul x W hxW aW sW
      _ = 0 := by simpa only [haW, hsW] using hrs
  have hprod' : F.presheaf.germ W x hxW (aW • sW) =
      F.presheaf.germ W x hxW 0 := by simpa using hprod
  obtain ⟨N, hxN, iNW, iW, hN⟩ :=
    F.presheaf.germ_eq x hxW hxW (aW • sW) (0 : Γ(F, W)) hprod'
  have hzN : F.presheaf.map iNW.op (aW • sW) = 0 := by
    simpa [Subsingleton.elim iNW iW] using hN
  have hηN : genericPoint X ∈ N :=
    (genericPoint_specializes x).mem_open N.isOpen hxN
  have hηW : genericPoint X ∈ W :=
    (genericPoint_specializes x).mem_open W.isOpen hxW
  have hsmulη : (X.presheaf.germ W (genericPoint X) hηW aW) •
      (F.presheaf.germ W (genericPoint X) hηW sW) = 0 := by
    calc
      (X.presheaf.germ W (genericPoint X) hηW aW) •
          (F.presheaf.germ W (genericPoint X) hηW sW) =
          F.presheaf.germ N (genericPoint X) hηN (F.presheaf.map iNW.op (aW • sW)) :=
        (F.val.germ_smul (genericPoint X) W hηW aW sW).symm.trans
          (F.presheaf.germ_res_apply iNW (genericPoint X) hηN (aW • sW)).symm
      _ = 0 := by rw [hzN]; simp
  have haη : X.presheaf.germ W (genericPoint X) hηW aW ≠ 0 := by
    have ha0 : a ≠ 0 := by
      intro ha0
      have hz : X.presheaf.germ W x hxW aW = 0 := by
        simp [aW, ha0]
      exact hr (haW.symm.trans hz)
    have haηV : genericPoint X ∈ V :=
      (genericPoint_specializes x).mem_open V.isOpen hxV
    have hηa : X.presheaf.germ V (genericPoint X) haηV a ≠ 0 := fun hz ↦
      ha0 (germ_injective_of_isIntegral X (genericPoint X) haηV (by simpa using hz))
    have heq : X.presheaf.germ W (genericPoint X) hηW aW =
        X.presheaf.germ V (genericPoint X) haηV a := by
      simp [aW]
    rwa [heq]
  exact (F.presheaf.germ_res_apply (homOfLE inf_le_right) (genericPoint X) hηW s).symm.trans
    ((smul_eq_zero.mp hsmulη).resolve_left haη)

/-- A section of a quasi-coherent module on an integral scheme is torsion at some stalk if
and only if it is torsion at every stalk; equivalently, its germ at the generic point and
its image in the pushforward from the generic point vanish. -/
@[stacks 0AXR]
theorem torsion_section_tfae
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) [Nonempty U] (s : Γ(F, U)) :
    let η := genericPoint X
    let hη : η ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))
    letI : ∀ V : X.Opens, Decidable (η ∈ V) := fun V ↦ Classical.propDecidable _
    let isTorsionAt (x : X) (hx : x ∈ U) : Prop :=
      letI : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsTorsionElement (R := X.presheaf.stalk x)
        (M := ↑(F.presheaf.stalk x)) (F.presheaf.germ U x hx s)
    List.TFAE [
      ∃ (x : X) (hx : x ∈ U), isTorsionAt x hx,
      ∀ (x : X) (hx : x ∈ U), isTorsionAt x hx,
      F.presheaf.germ U η hη s = 0,
      ((skyscraperPresheafStalkAdjunction (C := AddCommGrpCat.{u}) η).unit.app
        F.presheaf).app (op U) s = 0] := by
  classical
  let η := genericPoint X
  let hη : η ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  let : ∀ V : X.Opens, Decidable (η ∈ V) := fun V ↦ Classical.propDecidable _
  tfae_have 1 → 3 := fun ⟨x, hx, ht⟩ ↦ torsion_at_implies_generic_germ_zero X F U s x hx ht
  tfae_have 3 → 2 := fun h x hx ↦ generic_germ_zero_torsion_at X F U s x hx h
  tfae_have 2 → 1 := fun h ↦ ‹Nonempty U›.elim fun ⟨x, hx⟩ ↦ ⟨x, hx, h x hx⟩
  tfae_have 3 ↔ 4 := by
    have hmap :
        ((skyscraperPresheafStalkAdjunction (C := AddCommGrpCat.{u}) η).unit.app
          F.presheaf).app (op U) =
        (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf η (𝟙 _)).app
          (op U) := rfl
    have hU : genericPoint X ∈ U := hη
    let A : AddCommGrpCat.{u} :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).obj F.presheaf
    let g : F.presheaf.obj (op U) ⟶ A := F.presheaf.germ U (genericPoint X) hU
    let e : A ⟶ (if h : genericPoint X ∈ U then A else ⊤_ AddCommGrpCat.{u}) :=
      eqToHom (ite_eq_left hU).symm
    have hreduce :
        ((skyscraperPresheafStalkAdjunction (C := AddCommGrpCat.{u}) η).unit.app
          F.presheaf).app (op U) s = (ConcreteCategory.hom (g ≫ e)) s := by
      rw [hmap]
      dsimp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheafFunctor,
        skyscraperPresheaf]
      rw [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
      simp only [unop_op, η]
      simp only [hU, TopCat.Presheaf.stalkFunctor_obj, Functor.id_obj, ↓reduceDIte,
        skyscraperPresheaf_obj, ↓reduceIte, eqToHom_naturality, Category.comp_id,
        dite_eq_ite, g, e]
      rfl
    rw [hreduce, ConcreteCategory.comp_apply]
    exact (map_eq_zero_iff (ConcreteCategory.hom e)
      (ConcreteCategory.bijective_of_isIso e).injective).symm
  tfae_finish

end AlgebraicGeometry
