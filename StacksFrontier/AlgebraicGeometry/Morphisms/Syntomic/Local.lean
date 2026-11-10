module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import Mathlib.Data.List.TFAE
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Local characterizations of syntomic morphisms

Syntomicity at a point is equivalent both to admitting a standard syntomic description over any
prescribed affine neighbourhood of its image and to the corresponding finite-presentation,
flatness, and complete-intersection conditions on local rings. The fibre ring
`𝒪_{X,x} / 𝔪_s 𝒪_{X,x}` is written as `κ(s) ⊗[𝒪_{S,s}] 𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.syntomicAt_tfae` gives the three equivalent local characterizations of a
  syntomic morphism.

## References

* [Stacks Project, Tag 01UE](https://stacks.math.columbia.edu/tag/01UE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The complete-intersection property transports along a ring isomorphism of the base field
and a compatible ring isomorphism of the algebra. -/
private theorem isCompleteIntersection_of_fieldEquiv
    {k K A B : Type u} [Field k] [Field K] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K B] (eK : k ≃+* K) (eAB : A ≃+* B)
    (hmap : ∀ a : k, eAB (algebraMap k A a) = algebraMap K B (eK a))
    (h : IsCompleteIntersection k A) : IsCompleteIntersection K B := by
  obtain ⟨R, instR, algR, hR, hEss, fs, hfs, ⟨eA⟩⟩ := h
  let : Algebra k K := eK.toRingHom.toAlgebra
  let : Algebra K A := ((algebraMap k A).comp eK.symm.toRingHom).toAlgebra
  let : Algebra K R := ((algebraMap k R).comp eK.symm.toRingHom).toAlgebra
  have : IsScalarTower k K A :=
    IsScalarTower.of_algebraMap_eq fun _ => by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k K R :=
    IsScalarTower.of_algebraMap_eq fun _ => by simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.EssFiniteType k R := hEss
  have hEssK : Algebra.EssFiniteType K R := Algebra.EssFiniteType.of_comp k K R
  let eAK : A ≃ₐ[K] (R ⧸ Ideal.ofList fs) := {
    eA.toRingEquiv with
    commutes' := fun c => by
      change eA (algebraMap k A (eK.symm c)) =
        algebraMap K (R ⧸ Ideal.ofList fs) c
      rw [eA.commutes]
      rfl
  }
  let eABK : A ≃ₐ[K] B := {
    eAB with
    commutes' := fun c => by
      change eAB (algebraMap k A (eK.symm c)) = algebraMap K B c
      rw [hmap, RingEquiv.apply_symm_apply]
  }
  exact ⟨R, instR, inferInstance, hR, hEssK, fs, hfs, ⟨eABK.symm.trans eAK⟩⟩

/-- Relative global complete intersection, as a property of a ring homomorphism. -/
private def relativeGCIRingHom {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) : Prop :=
  letI := φ.toAlgebra
  Algebra.IsRelativeGlobalCompleteIntersection R T

/-- `relativeGCIRingHom φ` holds iff `T` is a relative global complete intersection over `R`
via `φ`. -/
private lemma relativeGCIRingHom_iff {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) : relativeGCIRingHom φ ↔
      letI := φ.toAlgebra; Algebra.IsRelativeGlobalCompleteIntersection R T := Iff.rfl

/-- Being a relative global complete intersection is invariant under pre- and post-composition
with ring isomorphisms. -/
private lemma relativeGCIRingHom_respectsIso :
    RingHom.RespectsIso (@relativeGCIRingHom.{u}) := by
  constructor
  · intro R S T _ _ _ φ e hφ
    let : Algebra R S := φ.toAlgebra
    let : Algebra R T := (e.toRingHom.comp φ).toAlgebra
    have : Algebra.IsRelativeGlobalCompleteIntersection R S :=
      (relativeGCIRingHom_iff φ).mp hφ
    have eAlg : S ≃ₐ[R] T := { e with commutes' := fun _ => rfl }
    exact (relativeGCIRingHom_iff _).mpr
      (Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv eAlg)
  · intro R S T _ _ _ φ e hφ
    let : Algebra R S := e.toRingHom.toAlgebra
    let : Algebra S R := e.symm.toRingHom.toAlgebra
    let : Algebra S T := φ.toAlgebra
    let : Algebra R T := (φ.comp e.toRingHom).toAlgebra
    have : IsScalarTower S R T := .of_algebraMap_eq fun s => by
      simp [RingHom.algebraMap_toAlgebra]
    have : IsScalarTower R S T := .of_algebraMap_eq fun r => by
      simp [RingHom.algebraMap_toAlgebra]
    let eAlg : R ≃ₐ[S] S := {
      e with
      commutes' := fun x => by
        simp [RingHom.algebraMap_toAlgebra]
    }
    let ePush : T ⊗[S] R ≃ₐ[T] T :=
      (Algebra.TensorProduct.congr (R := S) (S := T) (A := T) (B := R) (C := T) (D := S)
        (AlgEquiv.refl (R := T) (A₁ := T)) eAlg).trans
        (Algebra.TensorProduct.rid S T T)
    have hbc : IsBaseChange T (IsScalarTower.toAlgHom S R T).toLinearMap := by
      apply IsBaseChange.of_equiv ePush.toLinearEquiv
      intro r
      change ePush (1 ⊗ₜ[S] r) = algebraMap R T r
      calc
        ePush (1 ⊗ₜ[S] r) = eAlg r • (1 : T) := by simp [ePush]
        _ = algebraMap R T r := by
          rw [Algebra.smul_def, show eAlg r = e r by rfl]
          simp [RingHom.algebraMap_toAlgebra]
    have : Algebra.IsPushout S T R T := (Algebra.isPushout_iff S T R T).mpr hbc
    have : Algebra.IsRelativeGlobalCompleteIntersection S T :=
      (relativeGCIRingHom_iff φ).mp hφ
    exact (relativeGCIRingHom_iff _).mpr
      (Algebra.IsRelativeGlobalCompleteIntersection.baseChange S T R T)

/-- Syntomicity at a point is witnessed on any prescribed affine neighbourhood of the image,
after shrinking the source chart. -/
private theorem exists_affine_restrict_syntomic {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (h : SyntomicAt f x) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V),
      RingHom.Syntomic ((f.appLE V U.1 e).hom) := by
  obtain ⟨U₀, hxU₀, V₀, e₀, hsyn₀⟩ := h
  have hstable := RingHom.syntomic_stableUnderCompositionWithLocalizationAway
  obtain ⟨r, s, hx, e, hsyn⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_appLE_of_appLE_of_isAffine
      hstable.2 RingHom.syntomic_localizationAwayPreserves x ⟨V, hV⟩ V₀
      U₀ U₀ hxU₀ hxU₀ e₀
      ((RingHom.syntomic_iff _).mpr hsyn₀) hxV
  let W : S.Opens := S.basicOpen r
  let Z : X.Opens := X.basicOpen s
  let eW : Z ≤ f ⁻¹ᵁ W := e
  let : Algebra Γ(S, V) Γ(S, W) :=
    (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom.toAlgebra
  let : Algebra Γ(S, W) Γ(X, Z) := (f.appLE W Z eW).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, Z) :=
    ((f.appLE W Z eW).hom.comp (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom).toAlgebra
  have : IsLocalization.Away r Γ(S, W) := hV.isLocalization_basicOpen r
  have : Algebra.Smooth Γ(S, V) Γ(S, W) := Algebra.Smooth.of_isLocalization_Away r
  have : IsScalarTower Γ(S, V) Γ(S, W) Γ(X, Z) :=
    IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  have hsynComp : Algebra.Syntomic Γ(S, V) Γ(X, Z) := by
    have : Algebra.Syntomic Γ(S, W) Γ(X, Z) := (RingHom.syntomic_iff _).mp hsyn
    have : Algebra.Syntomic Γ(S, V) Γ(S, W) :=
      Algebra.Smooth.syntomic Γ(S, V) Γ(S, W)
    exact Algebra.Syntomic.comp Γ(S, V) Γ(S, W) Γ(X, Z)
  have hVW : W ≤ V := S.basicOpen_le r
  have eFull : Z ≤ f ⁻¹ᵁ V := e.trans (f.preimage_mono hVW)
  have heq : CommRingCat.ofHom (S.presheaf.map (homOfLE hVW).op).hom ≫
      f.appLE W Z eW = f.appLE V Z eFull :=
    Scheme.Hom.map_appLE (f := f) (U := W) (V := Z) eW (homOfLE hVW).op
  have hsyn' : RingHom.Syntomic ((f.appLE V Z eFull).hom) := by
    rw [← heq, CommRingCat.hom_comp]
    exact (RingHom.syntomic_iff _).mpr hsynComp
  exact ⟨⟨Z, U₀.2.basicOpen s⟩, by simpa [Z] using hx, by simpa [Z] using eFull, hsyn'⟩

/-- Syntomicity at a point is witnessed by a standard syntomic restriction over any prescribed
affine neighbourhood of the image. -/
private theorem exists_affine_standardSyntomic_of_syntomicAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (h : SyntomicAt f x) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V),
      @IsStandardSyntomic U.1.toScheme V.toScheme U.2 hV (f.resLE V U.1 e) := by
  obtain ⟨U, hxU, e, hsyn⟩ := exists_affine_restrict_syntomic f x V hV hxV h
  let A := Γ(S, V)
  let B := Γ(X, U.1)
  let : Algebra A B := (f.appLE V U.1 e).hom.toAlgebra
  have : Algebra.Syntomic A B := (RingHom.syntomic_iff _).mp hsyn
  let Q : Ideal B := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : Q.IsPrime := inferInstance
  obtain ⟨g, hg, hgci⟩ :=
    Algebra.Syntomic.exists_notMem_isRelativeGlobalCompleteIntersection (R := A) Q
  have hgc : Algebra.IsRelativeGlobalCompleteIntersection A (Localization.Away g) := hgci
  let W : X.Opens := X.basicOpen g
  have hW : IsAffineOpen W := U.2.basicOpen g
  have hxW : x ∈ W := by
    have hpre : U.2.primeIdealOf ⟨x, hxU⟩ ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [U.2.fromSpec_preimage_basicOpen]
      change g ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
      exact hg
    have hx : U.2.fromSpec (U.2.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen g := hpre
    simpa [W, U.2.fromSpec_primeIdealOf] using hx
  have hWU : W ≤ U.1 := Scheme.basicOpen_le X g
  have eW : W ≤ f ⁻¹ᵁ V := hWU.trans e
  let : Algebra B Γ(X, W) :=
    (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(X, W) := U.2.isLocalization_basicOpen g
  let : Algebra A Γ(X, W) := (f.appLE V W eW).hom.toAlgebra
  have : IsScalarTower A B Γ(X, W) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    have hm := Scheme.Hom.appLE_map (f := f) (U := V) (V := U.1)
      e (homOfLE hWU).op
    exact (congrArg (fun ψ : Γ(S, V) ⟶ Γ(X, W) => ψ.hom a) hm).symm
  have : IsLocalization.Away g (Localization.Away g) := inferInstance
  let eLoc : Localization.Away g ≃ₐ[A] Γ(X, W) :=
    (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, W)).restrictScalars A
  have hgcW : Algebra.IsRelativeGlobalCompleteIntersection A Γ(X, W) :=
    hgc.of_algEquiv eLoc
  have hgcRing : relativeGCIRingHom ((f.appLE V W eW).hom) :=
    (relativeGCIRingHom_iff _).mpr hgcW
  have hgcTop : relativeGCIRingHom ((f.resLE V W eW).appTop.hom) :=
    (relativeGCIRingHom_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V W eW)).mpr hgcRing
  exact ⟨⟨W, hW⟩, hxW, eW, hgcTop⟩

/-- The three equivalent local characterizations of syntomicity at a point. -/
private theorem syntomicAt_tfae_proof {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.affineOpens) (_hxV : f x ∈ V.1) :
    List.TFAE [
      SyntomicAt f x,
      ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        IsStandardSyntomic (f.resLE V.1 U.1 hUV),
      AlgebraicGeometry.FinitePresentationAt f x ∧
        (f.stalkMap x).hom.Flat ∧
        (let A := S.presheaf.stalk (f x)
         let B := X.presheaf.stalk x
         letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
         IsCompleteIntersection (IsLocalRing.ResidueField A)
           (IsLocalRing.ResidueField A ⊗[A] B))] := by
  tfae_have 2 → 1 := by
    rintro ⟨U, hxU, hUV, hstandard⟩
    refine ⟨U, hxU, V, hUV, ?_⟩
    have hsyn : RingHom.Syntomic ((f.resLE V.1 U.1 hUV).appTop.hom) := by
      let : Algebra Γ(V.1.toScheme, ⊤) Γ(U.1.toScheme, ⊤) :=
        ((f.resLE V.1 U.1 hUV).appTop.hom).toAlgebra
      have : Algebra.IsRelativeGlobalCompleteIntersection
          Γ(V.1.toScheme, ⊤) Γ(U.1.toScheme, ⊤) := hstandard
      exact (RingHom.syntomic_iff _).mpr
        (Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _)
    have hsyn' : RingHom.Syntomic ((f.appLE V.1 U.1 hUV).hom) :=
      (RingHom.syntomic_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V.1 U.1 hUV)).mp hsyn
    exact (RingHom.syntomic_iff _).mp hsyn'
  tfae_have 1 → 2 := exists_affine_standardSyntomic_of_syntomicAt f x V.1 V.2 _hxV
  tfae_have 2 → 3 := by
    rintro ⟨U, hxU, hUV, hstandard⟩
    let R := Γ(S, V.1)
    let T := Γ(X, U.1)
    let φ := (f.appLE V.1 U.1 hUV).hom
    let : Algebra R T := φ.toAlgebra
    have hgc : relativeGCIRingHom φ :=
      (relativeGCIRingHom_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V.1 U.1 hUV)).mp ((relativeGCIRingHom_iff _).mpr hstandard)
    have : Algebra.IsRelativeGlobalCompleteIntersection R T := (relativeGCIRingHom_iff φ).mp hgc
    have hsyn : Algebra.Syntomic R T :=
      Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection R T
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨V, U, hxU, hUV, by
        change φ.FinitePresentation
        exact Algebra.Syntomic.finitePresentation⟩
    · let p : Ideal R := (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal
      let q : Ideal T := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
      have : p.IsPrime := (V.2.primeIdealOf ⟨f x, hUV hxU⟩).isPrime
      have : q.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
      have hqp : q.LiesOver p :=
        ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V.1 V.2 U.1 U.2 hUV hxU).1).symm⟩
      let _ := Localization.AtPrime.algebraOfLiesOver p q
      let hlocal := IsAffineOpen.arrowStalkMapIso f V.1 V.2 U.1 U.2 hUV hxU
      have hflat : Module.Flat R (Localization.AtPrime q) := by
        have : IsLocalization.AtPrime (Localization.AtPrime q) q := inferInstance
        have : Module.Flat R T := hsyn.flat
        have : Module.Flat T (Localization.AtPrime q) :=
          IsLocalization.flat (Localization.AtPrime q) q.primeCompl
        exact inferInstance
      have hflat' : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
        Localization.AtPrime.flat_localRingHom_iff p q |>.2 hflat
      let ψ := Localization.localRingHom p q φ hqp.over
      let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := ψ.toAlgebra
      exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff hlocal).mpr hflat'
    · let xV : V.1 := ⟨f x, hUV hxU⟩
      let xU : U.1 := ⟨x, hxU⟩
      let p : Ideal R := (V.2.primeIdealOf xV).asIdeal
      let q : Ideal T := (U.2.primeIdealOf xU).asIdeal
      have : p.IsPrime := (V.2.primeIdealOf xV).isPrime
      have : q.IsPrime := (U.2.primeIdealOf xU).isPrime
      have hqp : q.LiesOver p :=
        ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V.1 V.2 U.1 U.2 hUV hxU).1).symm⟩
      have hciUnder : IsCompleteIntersection (q.under R).ResidueField
          ((q.under R).Fiber (Localization.AtPrime q)) :=
        (Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber
          (R := R) (S := T) q).2
      have hciLoc : IsCompleteIntersection p.ResidueField
          (p.Fiber (Localization.AtPrime q)) :=
        IsCompleteIntersection.fiber_congr (q.over_def p).symm hciUnder
      let A := S.presheaf.stalk (f x)
      let B := X.presheaf.stalk x
      let : Algebra R A := S.presheaf.algebra_section_stalk xV
      have : IsLocalization.AtPrime A p := V.2.isLocalization_stalk xV
      let eA : Localization.AtPrime p ≃ₐ[R] A :=
        IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A
      let k := p.ResidueField
      let k' := IsLocalRing.ResidueField A
      let eK : k ≃ₐ[R] k' := AlgEquiv.ofBijective
        (IsLocalRing.ResidueField.mapAlgHom eA)
        (IsLocalRing.ResidueField.mapEquiv eA.toRingEquiv).bijective
      let : Algebra T B := X.presheaf.algebra_section_stalk xU
      have : IsLocalization.AtPrime B q := U.2.isLocalization_stalk xU
      let eB : Localization.AtPrime q ≃ₐ[T] B :=
        IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B
      let _ := Localization.AtPrime.algebraOfLiesOver p q
      have : IsScalarTower R T (Localization.AtPrime q) := inferInstance
      let : Algebra A B := (f.stalkMap x).hom.toAlgebra
      let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
      have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower R T B := by
        apply IsScalarTower.of_algebraMap_eq
        intro r
        change f.stalkMap x (S.presheaf.germ V.1 (f x) (hUV hxU) r) = _
        rw [Scheme.Hom.germ_stalkMap_apply f V.1 x (hUV hxU) r]
        change X.presheaf.germ (f ⁻¹ᵁ V.1) x (hUV hxU) (f.app V.1 r) =
          X.presheaf.germ U.1 x hxU
            ((X.presheaf.map (homOfLE hUV).op).hom (f.app V.1 r))
        exact (X.presheaf.germ_res_apply (homOfLE hUV) x hxU (f.app V.1 r)).symm
      let eB' : Localization.AtPrime q ≃ₐ[R] B := eB.restrictScalars R
      let eLid : A ⊗[R] B ≃ₐ[A] B := IsLocalization.algebraLid p.primeCompl A B
      let eCancel : k' ⊗[A] (A ⊗[R] B) ≃ₐ[k'] k' ⊗[R] B :=
        Algebra.TensorProduct.cancelBaseChange R A k' k' B
      let eLidTensor : k' ⊗[A] (A ⊗[R] B) ≃ₐ[A] k' ⊗[A] B :=
        Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := k')) eLid
      let eToStalk : (k' ⊗[R] B) ≃+* (k' ⊗[A] B) :=
        eCancel.toRingEquiv.symm.trans eLidTensor.toRingEquiv
      change IsCompleteIntersection k (k ⊗[R] Localization.AtPrime q) at hciLoc
      let eAB : (k ⊗[R] Localization.AtPrime q) ≃+* (k' ⊗[A] B) :=
        (Algebra.TensorProduct.congr eK eB').toRingEquiv.trans eToStalk
      apply isCompleteIntersection_of_fieldEquiv eK.toRingEquiv eAB ?_ hciLoc
      intro a
      have heLidOne : eLid (1 ⊗ₜ[R] (1 : B)) = 1 := by
        rw [← Algebra.TensorProduct.one_def, map_one]
      simp [eAB, eToStalk, eCancel, eLidTensor, eLid, heLidOne]
  tfae_have 3 → 1 := by
    rintro ⟨⟨V₀, U₀, hxU, hUV, hfp⟩, hflatStalk, hciStalk⟩
    let R := Γ(S, V₀.1)
    let T := Γ(X, U₀.1)
    let φ := (f.appLE V₀.1 U₀.1 hUV).hom
    let : Algebra R T := φ.toAlgebra
    have hfpRing : Algebra.FinitePresentation R T := hfp
    let xV : V₀.1 := ⟨f x, hUV hxU⟩
    let xU : U₀.1 := ⟨x, hxU⟩
    let p : Ideal R := (V₀.2.primeIdealOf xV).asIdeal
    let q : Ideal T := (U₀.2.primeIdealOf xU).asIdeal
    have : p.IsPrime := (V₀.2.primeIdealOf xV).isPrime
    have : q.IsPrime := (U₀.2.primeIdealOf xU).isPrime
    have hqp : q.LiesOver p :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V₀.1 V₀.2 U₀.1 U₀.2 hUV hxU).1).symm⟩
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    let hlocal := IsAffineOpen.arrowStalkMapIso f V₀.1 V₀.2 U₀.1 U₀.2 hUV hxU
    let ψ := Localization.localRingHom p q φ hqp.over
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := ψ.toAlgebra
    have hflatψ : ψ.Flat :=
      (RingHom.Flat.respectsIso.arrow_mk_iso_iff hlocal).mp hflatStalk
    have hflatLoc : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hflatψ
    let A := S.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let : Algebra R A := S.presheaf.algebra_section_stalk xV
    have : IsLocalization.AtPrime A p := V₀.2.isLocalization_stalk xV
    let eA : Localization.AtPrime p ≃ₐ[R] A :=
      IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A
    let k := p.ResidueField
    let k' := IsLocalRing.ResidueField A
    let eK : k ≃ₐ[R] k' := AlgEquiv.ofBijective
      (IsLocalRing.ResidueField.mapAlgHom eA)
      (IsLocalRing.ResidueField.mapEquiv eA.toRingEquiv).bijective
    let : Algebra T B := X.presheaf.algebra_section_stalk xU
    have : IsLocalization.AtPrime B q := U₀.2.isLocalization_stalk xU
    let eB : Localization.AtPrime q ≃ₐ[T] B :=
      IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    have : IsScalarTower R T (Localization.AtPrime q) := inferInstance
    let : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
    have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower R T B := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      change f.stalkMap x (S.presheaf.germ V₀.1 (f x) (hUV hxU) r) = _
      rw [Scheme.Hom.germ_stalkMap_apply f V₀.1 x (hUV hxU) r]
      change X.presheaf.germ (f ⁻¹ᵁ V₀.1) x (hUV hxU) (f.app V₀.1 r) =
        X.presheaf.germ U₀.1 x hxU
          ((X.presheaf.map (homOfLE hUV).op).hom (f.app V₀.1 r))
      exact (X.presheaf.germ_res_apply (homOfLE hUV) x hxU (f.app V₀.1 r)).symm
    let eB' : Localization.AtPrime q ≃ₐ[R] B := eB.restrictScalars R
    let eLid : A ⊗[R] B ≃ₐ[A] B := IsLocalization.algebraLid p.primeCompl A B
    let eCancel : k' ⊗[A] (A ⊗[R] B) ≃ₐ[k'] k' ⊗[R] B :=
      Algebra.TensorProduct.cancelBaseChange R A k' k' B
    let eLidTensor : k' ⊗[A] (A ⊗[R] B) ≃ₐ[A] k' ⊗[A] B :=
      Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := k')) eLid
    let eToStalk : (k' ⊗[R] B) ≃+* (k' ⊗[A] B) :=
      eCancel.toRingEquiv.symm.trans eLidTensor.toRingEquiv
    let eAB : (k ⊗[R] Localization.AtPrime q) ≃+* (k' ⊗[A] B) :=
      (Algebra.TensorProduct.congr eK eB').toRingEquiv.trans eToStalk
    have hciLoc : IsCompleteIntersection k (k ⊗[R] Localization.AtPrime q) := by
      change IsCompleteIntersection k' (k' ⊗[A] B) at hciStalk
      apply isCompleteIntersection_of_fieldEquiv eK.symm.toRingEquiv eAB.symm ?_ hciStalk
      intro c
      apply eAB.injective
      rw [eAB.apply_symm_apply]
      have hmap : ∀ a : k,
          eAB (algebraMap k (k ⊗[R] Localization.AtPrime q) a) =
            algebraMap k' (k' ⊗[A] B) (eK a) := by
        intro a
        have heLidOne : eLid (1 ⊗ₜ[R] (1 : B)) = 1 := by
          rw [← Algebra.TensorProduct.one_def, map_one]
        simp [eAB, eToStalk, eCancel, eLidTensor, eLid, heLidOne]
      have hh := (hmap (eK.symm c)).symm
      rwa [eK.apply_symm_apply] at hh
    have hring := (Algebra.exists_notMem_syntomic_tfae p q).out 3 1
    have hcriteria : ∃ g ∉ q,
        Algebra.FinitePresentation R (Localization.Away g) ∧
          (let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
            (Localization.localRingHom p q (algebraMap R T) hqp.over).toAlgebra
           Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) ∧
            IsCompleteIntersection p.ResidueField
              (p.Fiber (Localization.AtPrime q)) := by
      refine ⟨1, Ideal.one_notMem q, ?_, by simpa [ψ] using hflatLoc, hciLoc⟩
      have : IsLocalization.Away (1 : T) T :=
        IsLocalization.away_of_isUnit_of_bijective T isUnit_one Function.bijective_id
      have eT : Localization.Away (1 : T) ≃ₐ[T] T :=
        IsLocalization.algEquiv (Submonoid.powers (1 : T)) _ T
      exact Algebra.FinitePresentation.equiv (eT.symm.restrictScalars R)
    obtain ⟨g, hg, hsyn⟩ := hring.mp hcriteria
    let W : X.Opens := X.basicOpen g
    have hW : IsAffineOpen W := U₀.2.basicOpen g
    have hxW : x ∈ W := by
      have hpre : U₀.2.primeIdealOf xU ∈ U₀.2.fromSpec ⁻¹ᵁ X.basicOpen g := by
        rw [U₀.2.fromSpec_preimage_basicOpen]
        change g ∉ (U₀.2.primeIdealOf xU).asIdeal
        exact hg
      have hx : U₀.2.fromSpec (U₀.2.primeIdealOf xU) ∈ X.basicOpen g := hpre
      simpa [W, xU, U₀.2.fromSpec_primeIdealOf] using hx
    have hWU : W ≤ U₀.1 := Scheme.basicOpen_le X g
    have eW : W ≤ f ⁻¹ᵁ V₀.1 := hWU.trans hUV
    let : Algebra T Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, W) := U₀.2.isLocalization_basicOpen g
    let : Algebra R Γ(X, W) := (f.appLE V₀.1 W eW).hom.toAlgebra
    have : IsScalarTower R T Γ(X, W) := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      have hm := Scheme.Hom.appLE_map (f := f) (U := V₀.1) (V := U₀.1) hUV
        (homOfLE hWU).op
      exact (congrArg (fun ψ : Γ(S, V₀.1) ⟶ Γ(X, W) => ψ.hom r) hm).symm
    have : IsLocalization.Away g (Localization.Away g) := inferInstance
    let eLoc : Localization.Away g ≃ₐ[R] Γ(X, W) :=
      (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
        Γ(X, W)).restrictScalars R
    let α := CommRingCat.ofHom (algebraMap R (Localization.Away g))
    let β := CommRingCat.ofHom ((f.appLE V₀.1 W eW).hom)
    have hcomm : α ≫ eLoc.toRingEquiv.toCommRingCatIso.hom = β := by
      ext r
      exact eLoc.commutes r
    let harr : Arrow.mk α ≅ Arrow.mk β :=
      Arrow.isoMk (Iso.refl _) eLoc.toRingEquiv.toCommRingCatIso hcomm.symm
    have hsynRing : RingHom.Syntomic (algebraMap R (Localization.Away g)) :=
      (RingHom.syntomic_iff _).mpr (by rwa [toAlgebra_algebraMap])
    have hsynApp : RingHom.Syntomic ((f.appLE V₀.1 W eW).hom) :=
      (RingHom.syntomic_respectsIso.arrow_mk_iso_iff harr).mp hsynRing
    exact ⟨⟨W, hW⟩, hxW, V₀, eW, hsynApp⟩
  tfae_finish

/-- Let `x : X` map to `s : S`, and let `V` be an affine open neighbourhood of `s`. Then the
following are equivalent:

1. `f` is syntomic at `x`;
2. some affine open neighbourhood `U` of `x`, mapping into `V`, makes the
   restricted morphism `U ⟶ V` standard syntomic;
3. `f` is of finite presentation at `x`, its map on local rings is flat, and
   its local fibre ring at `x` is a complete intersection over `κ(s)`. -/
@[stacks 01UE]
theorem syntomicAt_tfae {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.affineOpens) (_hxV : f x ∈ V.1) :
    List.TFAE [
      SyntomicAt f x,
      ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        IsStandardSyntomic (f.resLE V.1 U.1 hUV),
      AlgebraicGeometry.FinitePresentationAt f x ∧
        (f.stalkMap x).hom.Flat ∧
        (let A := S.presheaf.stalk (f x)
         let B := X.presheaf.stalk x
         letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
         IsCompleteIntersection (IsLocalRing.ResidueField A)
           (IsLocalRing.ResidueField A ⊗[A] B))] :=
  syntomicAt_tfae_proof f x V _hxV

end AlgebraicGeometry
