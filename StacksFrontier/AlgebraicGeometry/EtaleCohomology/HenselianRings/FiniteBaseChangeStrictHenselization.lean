module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeHenselization
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite morphisms over a strictly henselian local scheme

The base change of a finite morphism to the strict henselization at a geometric
point is a finite disjoint union of spectra of strictly henselian local rings.
Its components are indexed by the lifts of the geometric point.

## Main results

* `AlgebraicGeometry.finite_baseChange_strictHenselization_decomposition` gives the
  decomposition, with its component labels and structure maps.

## References

* [Stacks Project, Section 59, finite pushforward](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A finite morphism, after base change to a geometric point's strict
henselization, splits into strictly henselian local components indexed by the
lifts of that geometric point. -/
@[sga "4 VIII 5.4" "for f finite, partial"]
public theorem finite_baseChange_strictHenselization_decomposition
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (B : BigEtaleSite.{u}) (hY : B.Contains Y)
    (s : GeometricPoint Y) :
    let g := strictHenselizationToBase B Y hY s
    let q := geometricPointToStrictHenselization B Y hY s
    let L := {x : s.source ⟶ X // x ≫ f = s.hom}
    ∃ (_ : Finite L) (A : L → CommRingCat.{u}),
      (∀ i, StrictlyHenselianLocalRing (A i)) ∧
      ∃ (e : (∐ fun i : L => Spec (A i)) ≅ pullback f g)
        (p : ∀ i : L, s.source ⟶ Spec (A i)),
        ∀ i, (p i ≫ Sigma.ι (fun j : L => Spec (A j)) i ≫
            e.hom ≫ pullback.fst f g = i.val) ∧
          (p i ≫ Sigma.ι (fun j : L => Spec (A j)) i ≫
            e.hom ≫ pullback.snd f g = q) := by
  dsimp only
  let R := ↥(etaleLocalRing B Y hY s)
  let T := strictHenselization B Y hY s
  let I := strictHenselizationToBase B Y hY s
  let q := geometricPointToStrictHenselization B Y hY s
  let P := pullback f I
  let : IsAffine P := isAffine_of_isAffineHom (pullback.snd f I)
  let Q := Γ(T, ⊤)
  let e : Q ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let ε := structureSheafStalkToGeometricField B Y hY s
  let : StrictlyHenselianLocalRing R :=
    etaleLocalRing_strictHenselian B Y hY s
  let : IsLocalRing R := (etaleLocalRing_strictHenselian B Y hY s).toIsLocalRing
  let : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm.toRingHom⟩
  let : IsLocalHom ε := structureSheafStalkToGeometricField_isLocalHom B Y hY s
  let : IsLocalRing Q := e.symm.isLocalRing
  let : StrictlyHenselianLocalRing Q :=
    strictlyHenselianLocalRing_of_ringEquiv e.symm
  let φ : Q →+* s.residueField := ε.comp e.toRingHom
  let h : P ⟶ T := pullback.snd f I
  let A := Γ(P, ⊤)
  let : Algebra Q A := h.appTop.hom.toAlgebra
  have hAfinite : Module.Finite Q A := by
    rw [← RingHom.finite_algebraMap]
    exact IsFinite.finite_app h ⊤ (isAffineOpen_top _)
  obtain ⟨ι, hι, B', hBcomm, hBalg, hBhen, hBfinite, he⟩ :=
    exists_algEquiv_pi_strictHenselian_of_module_finite Q A
  let : Finite ι := hι
  let : ∀ i, CommRing (B' i) := hBcomm
  let : ∀ i, Algebra Q (B' i) := hBalg
  let : ∀ i, StrictlyHenselianLocalRing (B' i) := hBhen
  let : ∀ i, Module.Finite Q (B' i) := hBfinite
  let : ∀ i, IsLocalHom (algebraMap Q (B' i)) := fun i ↦
    isLocalHom_algebraMap_of_finite_local Q (B' i)
  let pointChar : (s.source ⟶ P) ≃ (A →+* s.residueField) := {
    toFun m := (Spec.homEquiv (m ≫ P.isoSpec.hom)).hom
    invFun ψ := Spec.map (CommRingCat.ofHom ψ) ≫ P.isoSpec.inv
    left_inv m := by
      apply (cancel_mono P.isoSpec.hom).1
      simp
    right_inv ψ := by
      ext a
      simp }
  have pointChar_symm_hom (ψ : A →+* s.residueField) :
      pointChar.symm ψ ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom ψ) := by
    apply Spec.homEquiv.injective
    simp [pointChar]
  have pointChar_base_iff (ψ : A →+* s.residueField) :
      pointChar.symm ψ ≫ h = q ↔
        ψ.comp (algebraMap Q A) = φ := by
    have hsymm : (pointChar.symm ψ ≫ h) ≫ T.isoSpec.hom =
        Spec.map (h.appTop ≫ CommRingCat.ofHom ψ) := by
      rw [Category.assoc, ← Scheme.isoSpec_hom_naturality h,
        ← Category.assoc (pointChar.symm ψ) P.isoSpec.hom (Spec.map (h.appTop)),
        pointChar_symm_hom, Spec.map_comp]
    have hq : q ≫ T.isoSpec.hom =
        Spec.map ((Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom ε) := by
      dsimp [q, T, R, ε, geometricPointToStrictHenselization]
      rw [Scheme.isoSpec_Spec_hom, Spec.map_comp]
    rw [← cancel_mono T.isoSpec.hom, hsymm, hq, Spec.map_inj]
    constructor
    · intro hring
      ext r
      exact congrArg (fun g : CommRingCat.of Q ⟶ CommRingCat.of s.residueField => g.hom r) hring
    · intro hchar
      ext r
      exact congrArg (fun g : Q →+* s.residueField => g r) hchar
  let L := {x : s.source ⟶ X // x ≫ f = s.hom}
  let liftChar : L ≃ {ψ : A →+* s.residueField //
      ψ.comp (algebraMap Q A) = φ} := {
    toFun := fun x => ⟨pointChar (pullback.lift x.1 q
      (x.2.trans (geometricPointToStrictHenselization_comp B Y hY s).symm)), by
      apply (pointChar_base_iff _).mp
      simp [pointChar.symm_apply_apply, pullback.lift_snd, h]⟩
    invFun := fun ψ => ⟨pointChar.symm ψ.1 ≫ pullback.fst f I, by
      have hbase := (pointChar_base_iff ψ.1).mpr ψ.2
      calc
        (pointChar.symm ψ.1 ≫ pullback.fst f I) ≫ f =
            (pointChar.symm ψ.1 ≫ h) ≫ I := by
          simp only [Category.assoc, h]
          rw [pullback.condition]
        _ = q ≫ I := congrArg (fun z : s.source ⟶ T => z ≫ I) hbase
        _ = s.hom := geometricPointToStrictHenselization_comp B Y hY s⟩
    left_inv := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      simp [pointChar.symm_apply_apply, pullback.lift_fst]
    right_inv := by
      rintro ⟨ψ, hψ⟩
      apply Subtype.ext
      refine (congrArg pointChar ?_).trans (pointChar.apply_symm_apply ψ)
      exact pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans ((pointChar_base_iff ψ).mpr hψ).symm) }
  let aEquiv : (↑A) ≃ₐ[Q] (∀ i, B' i) := Classical.choice he
  let charEquiv : ι ≃ {ψ : A →+* s.residueField //
      ψ.comp (algebraMap Q A) = φ} :=
    finiteAlgHomCharsEquiv (R := Q) (k := s.residueField) (ι := ι)
      (A := ↑A) B' aEquiv φ
  let indexEquiv : ι ≃ L := charEquiv.trans liftChar.symm
  let : Finite L := Finite.of_equiv ι indexEquiv
  let Aout : L → CommRingCat := fun ℓ => CommRingCat.of (B' (indexEquiv.symm ℓ))
  let factorHom : ∀ i, B' i →+* s.residueField := fun i =>
    Classical.choose (exists_ringHom_to_algClosed_of_finite_local_algebra
      (R := Q) (S := B' i) (k := s.residueField) φ)
  have factorHom_base (i) :
      (factorHom i).comp (algebraMap Q (B' i)) = φ :=
    Classical.choose_spec (exists_ringHom_to_algClosed_of_finite_local_algebra
      (R := Q) (S := B' i) (k := s.residueField) φ)
  have factorCharacter_formula (i) :
      ((factorHom i).comp (Pi.evalRingHom B' i)).comp
          aEquiv.toRingEquiv.toRingHom = (liftChar (indexEquiv i)).val :=
    congrArg Subtype.val (by simp [indexEquiv] : charEquiv i = liftChar (indexEquiv i))
  let σ := AlgebraicGeometry.sigmaSpec (fun i : ι => CommRingCat.of (B' i))
  let eRing : CommRingCat.of (↑A) ≅ CommRingCat.of (∀ i, B' i) :=
    { hom := CommRingCat.ofHom aEquiv.toRingEquiv.toRingHom
      inv := CommRingCat.ofHom aEquiv.toRingEquiv.symm.toRingHom
      hom_inv_id := by ext x; simp
      inv_hom_id := by ext x; simp }
  let τIso : Spec (.of (∀ i, B' i)) ≅ Spec (.of (↑A)) :=
    Scheme.Spec.mapIso eRing.op
  let eX : (∐ fun i : ι => Spec (.of (B' i))) ≅ P :=
    asIso (σ ≫ τIso.hom ≫ P.isoSpec.inv)
  let reindexIso : (∐ fun ℓ : L => Spec (Aout ℓ)) ≅
      (∐ fun i : ι => Spec (.of (B' i))) :=
    Sigma.reindex indexEquiv.symm (fun i : ι => Spec (.of (B' i)))
  have eX_post : eX.hom ≫ P.isoSpec.hom = σ ≫ τIso.hom := by
    dsimp [eX]
    simp [Category.assoc]
  have τ_hom : τIso.hom = Spec.map eRing.hom := rfl
  have componentPoint (i : ι) :
      Spec.map (CommRingCat.ofHom (factorHom i)) ≫
        Sigma.ι (fun j : ι => Spec (.of (B' j))) i ≫ eX.hom =
        pointChar.symm ((liftChar (indexEquiv i)).val) := by
    apply (cancel_mono P.isoSpec.hom).1
    rw [pointChar_symm_hom]
    have hcat : eRing.hom ≫ CommRingCat.ofHom (Pi.evalRingHom B' i) ≫
        CommRingCat.ofHom (factorHom i) =
        CommRingCat.ofHom ((liftChar (indexEquiv i)).val) := by
      ext a
      exact congrArg (fun ψ : A →+* s.residueField => ψ a)
        (factorCharacter_formula i)
    have hscheme := congrArg Spec.map hcat
    rw [Spec.map_comp, Spec.map_comp] at hscheme
    rw [Category.assoc, Category.assoc, eX_post, ← Category.assoc (Sigma.ι _ i) σ,
      AlgebraicGeometry.ι_sigmaSpec, τ_hom]
    exact hscheme
  let eFinal : (∐ fun ℓ : L => Spec (Aout ℓ)) ≅ P := reindexIso ≪≫ eX
  let pFinal : ∀ ℓ : L, s.source ⟶ Spec (Aout ℓ) := fun ℓ =>
    Spec.map (CommRingCat.ofHom (factorHom (indexEquiv.symm ℓ)))
  have finalPoint (ℓ : L) :
      pFinal ℓ ≫ Sigma.ι (fun j : L => Spec (Aout j)) ℓ ≫ eFinal.hom =
        pointChar.symm ((liftChar ℓ).val) := by
    dsimp [pFinal, eFinal, Aout]
    change Spec.map (CommRingCat.ofHom (factorHom (indexEquiv.symm ℓ))) ≫
      Sigma.ι ((fun i : ι => Spec (.of (B' i))) ∘ indexEquiv.symm) ℓ ≫
        (Sigma.reindex indexEquiv.symm (fun i : ι => Spec (.of (B' i)))).hom ≫
          eX.hom = pointChar.symm ((liftChar ℓ).val)
    rw [Sigma.ι_reindex_hom_assoc
      (f := fun i : ι => Spec (.of (B' i))) (ε := indexEquiv.symm) ℓ eX.hom]
    simpa using componentPoint (indexEquiv.symm ℓ)
  have finalPoint_fst (ℓ : L) :
      pointChar.symm ((liftChar ℓ).val) ≫ pullback.fst f I = ℓ.val := by
    simpa [liftChar] using congrArg Subtype.val (liftChar.left_inv ℓ)
  have finalPoint_snd (ℓ : L) :
      pointChar.symm ((liftChar ℓ).val) ≫ pullback.snd f I = q :=
    (pointChar_base_iff (liftChar ℓ).val).mpr (liftChar ℓ).property
  refine ⟨inferInstance, Aout, fun ℓ ↦ hBhen (indexEquiv.symm ℓ), eFinal, pFinal,
    fun ℓ ↦ ⟨?_, ?_⟩⟩
  · simpa only [Category.assoc] using (finalPoint ℓ =≫ pullback.fst f I).trans (finalPoint_fst ℓ)
  · simpa only [Category.assoc] using (finalPoint ℓ =≫ pullback.snd f I).trans (finalPoint_snd ℓ)

end AlgebraicGeometry

end
