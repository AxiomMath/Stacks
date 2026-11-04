module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.NaiveCotangent.ConormalFiniteProjective
public import StacksFrontier.RingTheory.Smooth.SymmetricAlgebra
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.LocalizedConormalSequence
public import StacksFrontier.RingTheory.TensorAlgebra.Localization

/-!
# Improving a presentation

A finitely presented algebra admits a finite-type algebra map to the symmetric algebra of the
conormal module of a finite polynomial presentation. The augmentation retracts onto the algebra.
After localization, the enlargement has a smooth presentation with free conormal module at every
local-complete-intersection point, and has free relative differentials at every smooth point.

## Main definitions

* `Stacks.Smoothing.HasFreeConormalPresentation` records a finite polynomial presentation with
  free conormal module.

## Main results

* `Stacks.Smoothing.exists_finiteType_retraction_improving_presentation` constructs one symmetric
  algebra satisfying both localized properties and identifies its retraction with the
  augmentation.

## Implementation notes

For `a : A`, the notation `C_a` is represented by the canonical ring
`Localization.Away (algebraMap A C a)`. Its algebra structure over `Localization.Away a` is the
one induced by the canonical localized map. Local complete intersection is expressed using
`RingHom.IsLocalCompleteIntersection`.

The module in the symmetric algebra is `P.toExtension.Cotangent` for a finite polynomial
presentation `P`. It is finite, and it is projective when `R → A` is a local complete intersection.
The source does not assert projectivity for an arbitrary finitely presented algebra.

## References

* [Stacks Project, Tag 07CE](https://stacks.math.columbia.edu/tag/07CE)
* [Stacks Project, Tag 07D0](https://stacks.math.columbia.edu/tag/07D0)
-/

@[expose] public section

open MvPolynomial
open scoped TensorProduct

namespace Stacks.Smoothing

universe u v

/-- A smooth algebra map is a local complete intersection. -/
lemma ringHom_isLocalCompleteIntersection_of_smooth
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] :
    RingHom.IsLocalCompleteIntersection (algebraMap R A) := by
  have hsm : RingHom.Smooth (algebraMap R A) :=
    RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth R A›
  let : Algebra R A := (algebraMap R A).toAlgebra
  have hsm' : Algebra.Smooth R A := hsm.toAlgebra
  have hs : Algebra.Syntomic R A := Algebra.Smooth.syntomic R A
  exact ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection
    (algebraMap R A)).mp hs).2

/-- When the first cotangent cohomology of `A → B` vanishes, the base change map on
differentials is injective. -/
private lemma kaehler_mapBaseChange_injective_of_subsingleton_h1
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Subsingleton (Algebra.H1Cotangent A B)] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
  (LinearMap.injective_iff_eq_zero_of_exact
    (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B)).mpr (Subsingleton.elim _ _)

/-- For a local complete intersection `A → B`, the base-changed conormal map of a composition of
presentations is injective; the index type of the upper presentation need only be finite. -/
private lemma cotangent_map_toComp_injective_of_localCompleteIntersection
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {I J : Type*} [Finite J]
    (P : Algebra.Generators R A I) (Q : Algebra.Generators A B J)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B)) :
    Function.Injective
      ((Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B) := by
  classical
  let := Fintype.ofFinite J
  let e := (Fintype.equivFin J).symm
  let Q' := Q.reindex e
  let t : (Q.comp P).Hom (Q'.comp P) := {
    val := fun j => X (Sum.map e.symm id j)
    aeval_val := by
      intro j
      cases j <;> simp [Q', Algebra.Generators.comp_val,
        Algebra.Generators.reindex_val, e] }
  have ht : t.comp (Q.toComp P) = Q'.toComp P := by
    ext i
    simp [t, Algebra.Generators.Hom.comp_val]
  have hm :
      (Algebra.Extension.Cotangent.map t.toExtensionHom) ∘ₗ
          (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B =
        (Algebra.Extension.Cotangent.map (Q'.toComp P).toExtensionHom).liftBaseChange B := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul b x =>
      simp only [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, map_smul]
      congr 1
      calc
        _ = Algebra.Extension.Cotangent.map
            (t.toExtensionHom.comp (Q.toComp P).toExtensionHom) x :=
          (LinearMap.congr_fun (Algebra.Extension.Cotangent.map_comp _
            (Q.toComp P).toExtensionHom t.toExtensionHom) x).symm
        _ = _ := by rw [← Algebra.Generators.Hom.toExtensionHom_comp, ht]
  have hf := RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection P Q' h
  intro x y hxy
  apply hf
  rw [← LinearMap.congr_fun hm x, ← LinearMap.congr_fun hm y]
  exact congrArg (Algebra.Extension.Cotangent.map t.toExtensionHom) hxy

/-- The localization of `C` at the image of `a` is the base change of `C` along the localization
of `A` at `a`. -/
private noncomputable def localizationAwayTensorAlgEquiv
    {A C L B : Type*} [CommRing A] [CommRing C] [CommRing L] [CommRing B]
    [Algebra A C] [Algebra A L] [Algebra A B] [Algebra C B]
    [IsScalarTower A C B] [Algebra L B] [IsScalarTower A L B]
    (a : A) [IsLocalization.Away a L]
    [IsLocalization.Away (algebraMap A C a) B] :
    L ⊗[A] C ≃ₐ[L] B := by
  let P := L ⊗[A] C
  let mapC : C →ₐ[A] P := Algebra.TensorProduct.includeRight
  have ha : IsUnit (algebraMap A L a) :=
    IsLocalization.map_units L ⟨a, Submonoid.mem_powers a⟩
  have hmap (x : A) : mapC (algebraMap A C x) = algebraMap L P (algebraMap A L x) := by
    calc
      mapC (algebraMap A C x) = algebraMap A P x := mapC.commutes x
      _ = algebraMap L P (algebraMap A L x) :=
        (IsScalarTower.algebraMap_apply A L P x).symm
  have hunit : IsUnit (mapC (algebraMap A C a)) := by
    rw [hmap]
    change IsUnit ((algebraMap A L a) ⊗ₜ[A] (1 : C))
    exact ha.map (algebraMap L P)
  let bwdRing : B →+* P :=
    IsLocalization.Away.lift (algebraMap A C a) hunit (g := mapC.toRingHom)
  have hbase : (bwdRing.comp (algebraMap L B)).comp (algebraMap A L) =
      (algebraMap L P).comp (algebraMap A L) := by
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A L B, IsScalarTower.algebraMap_apply A C B,
      IsLocalization.Away.lift_eq (algebraMap A C a) hunit (algebraMap A C x)]
    exact hmap x
  have hcomm : bwdRing.comp (algebraMap L B) = algebraMap L P :=
    IsLocalization.ringHom_ext (Submonoid.powers a) hbase
  let bwd : B →ₐ[L] P := {
    toRingHom := bwdRing
    commutes' := fun x => DFunLike.congr_fun hcomm x }
  let fwd : P →ₐ[L] B :=
    Algebra.TensorProduct.lift (Algebra.ofId L B)
      ((Algebra.ofId C B).restrictScalars A) (fun _ _ => Commute.all _ _)
  have hfwdRight : (fwd.restrictScalars A).comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId C B).restrictScalars A :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ _
  have hfb : fwd.comp bwd = AlgHom.id L B := by
    have h : fwd.toRingHom.comp bwdRing = RingHom.id B := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A C a))
      ext c
      change fwd (bwdRing (algebraMap C B c)) = algebraMap C B c
      rw [IsLocalization.Away.lift_eq (algebraMap A C a) hunit c]
      exact DFunLike.congr_fun hfwdRight c
    exact AlgHom.ext (RingHom.congr_fun h)
  have hbf : bwd.comp fwd = AlgHom.id L P := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext c
      change bwd (((fwd.restrictScalars A).comp Algebra.TensorProduct.includeRight) c) =
        Algebra.TensorProduct.includeRight c
      rw [hfwdRight]
      change bwdRing (algebraMap C B c) = mapC c
      rw [IsLocalization.Away.lift_eq (algebraMap A C a) hunit c]
      rfl
  exact AlgEquiv.ofAlgHom fwd bwd hfb hbf

/-- If `R → A_a` is a local complete intersection, the localization at `a` of the conormal module
of a finite polynomial presentation of `A` is finite projective. -/
private lemma localized_cotangent_finite_projective_of_isLocalCompleteIntersection
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (P : Algebra.Generators R A (Fin n)) (a : A)
    (h : RingHom.IsLocalCompleteIntersection
      (algebraMap R (Localization.Away a))) :
    Module.Finite (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent) ∧
      Module.Projective (Localization.Away a)
        (Localization.Away a ⊗[A] P.toExtension.Cotangent) := by
  classical
  let L := Localization.Away a
  let Pa := (Algebra.Generators.localizationAway L a).comp P
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
  obtain ⟨_, n', α, hα, hreg⟩ := h
  let β : MvPolynomial (Unit ⊕ Fin n) R →ₐ[R] L := MvPolynomial.aeval Pa.val
  have hβ : Function.Surjective β := by
    simpa [β] using Pa.aeval_val_surjective
  have hregβ := RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial
    α hα hreg β hβ
  have hPa : Quasiregular.IsQuasiregularIdeal' Pa.toExtension.ker :=
    Ideal.IsKoszulRegular.isQuasiregular hregβ
  obtain ⟨hfinite, hprojective⟩ :=
    Algebra.Extension.cotangent_finite_projective_of_quasiregular Pa.toExtension hPa
  let e := localizedConormalEquiv (S := L) P a
  let : Module.Finite L Pa.toExtension.Cotangent := hfinite
  let : Module.Projective L Pa.toExtension.Cotangent := hprojective
  let : Module.Finite L (L × (L ⊗[A] P.toExtension.Cotangent)) :=
    Module.Finite.equiv e
  let : Module.Projective L (L × (L ⊗[A] P.toExtension.Cotangent)) :=
    Module.Projective.of_equiv e
  have hfinite' : Module.Finite L (L ⊗[A] P.toExtension.Cotangent) :=
    Module.Finite.of_surjective (LinearMap.snd L L _)
      (by intro x; exact ⟨(0, x), rfl⟩)
  have hprojective' : Module.Projective L (L ⊗[A] P.toExtension.Cotangent) :=
    Module.Projective.of_split (LinearMap.inr L L _)
      (LinearMap.snd L L _) (by ext x; rfl)
  exact ⟨hfinite', hprojective'⟩

/-- A surjection onto a projective module splits, identifying its source with the product of the
target and the kernel. -/
private noncomputable def projectiveQuotientSplit
    {R M F : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F] [Module.Projective R M]
    (p : F →ₗ[R] M) (hp : Function.Surjective p) :
    (M × p.ker) ≃ₗ[R] F := by
  classical
  let s := Classical.choose (Module.projective_lifting_property p LinearMap.id hp)
  have hs : p.comp s = LinearMap.id :=
    Classical.choose_spec (Module.projective_lifting_property p LinearMap.id hp)
  have hsp (x : M) : p (s x) = x := DFunLike.congr_fun hs x
  refine
    { toFun := fun x => s x.1 + x.2.1
      invFun := fun x => (p x, ⟨x - s (p x), by
        change p (x - s (p x)) = 0
        rw [map_sub, hsp]
        simp⟩)
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro x y
    change s (x.1 + y.1) + (x.2.1 + y.2.1) =
      (s x.1 + x.2.1) + (s y.1 + y.2.1)
    simp only [map_add]
    abel
  · intro r x
    change s (r • x.1) + (r • x.2.1) = r • (s x.1 + x.2.1)
    rw [map_smul]
    exact (smul_add r (s x.1) x.2.1).symm
  · rintro ⟨m, k⟩
    apply Prod.ext
    · change p (s m + k.1) = m
      rw [map_add, hsp, k.2]
      simp
    · apply Subtype.ext
      change s m + k.1 - s (p (s m + k.1)) = k.1
      rw [map_add, hsp, k.2]
      abel_nf
  · intro x
    change s (p x) + (x - s (p x)) = x
    abel

/-- A short exact sequence whose right term is projective and whose outer product is free has free
middle term. -/
private lemma free_of_split_exact
    {R X Y Z : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    [Module.Projective R Z] [Module.Free R (X × Z)]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (hg : Function.Surjective g) : Module.Free R Y := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, _⟩ :=
    ((Function.Exact.split_tfae' hexact).out 1 3 rfl rfl).mp ⟨hf, s, hs⟩
  exact Module.Free.of_equiv e.symm

/-- The base change of a finite projective module is projective. -/
private lemma projective_baseChange_of_finite_projective
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Algebra R S] [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (S ⊗[R] M) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let eFree := TensorProduct.piScalarRight R S S (Fin n)
  let f' := LinearMap.baseChange S f
  let g' := LinearMap.baseChange S g
  have hfg' : f'.comp g' = LinearMap.id := by
    simpa [f', g', LinearMap.baseChange_comp] using
      congrArg (fun h : M →ₗ[R] M => LinearMap.baseChange S h) hfg
  let : Module.Free S (S ⊗[R] (Fin n → R)) := Module.Free.of_equiv eFree.symm
  exact Module.Projective.of_split g' f' hfg'

/-- For `A_a` smooth over `R`, the localized coordinate module of a finite polynomial presentation
of `A` is the product of the differentials of `A_a` and the localized conormal module. -/
private lemma localized_presentation_differentials_equiv
    {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
    [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    {n : ℕ} (P : Algebra.Generators R A (Fin n)) (a : A)
    [IsLocalization.Away a L] (hSmooth : Algebra.Smooth R L) :
    Nonempty ((Fin n → L) ≃ₗ[L]
      KaehlerDifferential R L × (L ⊗[A] P.toExtension.Cotangent)) := by
  classical
  let : Algebra.Smooth R L := hSmooth
  have hFormal : Algebra.FormallySmooth R L := inferInstance
  let : Algebra.Smooth A L := Algebra.Smooth.of_isLocalization_Away a
  have hLCI : RingHom.IsLocalCompleteIntersection (algebraMap A L) :=
    ringHom_isLocalCompleteIntersection_of_smooth (R := A) (A := L)
  have : Algebra.FormallyEtale A L :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  let eFin : Fin 1 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => 0
    left_inv := by intro i; fin_cases i; rfl
    right_inv := by intro x; cases x; rfl }
  let Q := (Algebra.Generators.localizationAway L a).reindex eFin
  let Pa := Q.comp P
  have hSplitPa : ∃ s : Pa.toExtension.CotangentSpace →ₗ[L] Pa.toExtension.Cotangent,
      s.comp Pa.toExtension.cotangentComplex = LinearMap.id := by
    let : Algebra.FormallySmooth R Pa.toExtension.Ring := by
      show Algebra.FormallySmooth R (MvPolynomial (Fin 1 ⊕ Fin n) R)
      infer_instance
    exact (Algebra.Extension.formallySmooth_iff_split_injection Pa.toExtension).mp hFormal
  obtain ⟨sPa, hsPa⟩ := hSplitPa
  have hPaInj : Function.Injective Pa.toExtension.cotangentComplex := by
    intro x y hxy
    calc
      x = sPa (Pa.toExtension.cotangentComplex x) :=
        (LinearMap.congr_fun hsPa x).symm
      _ = sPa (Pa.toExtension.cotangentComplex y) := congrArg sPa hxy
      _ = y := LinearMap.congr_fun hsPa y
  let f := (Q.toComp P).toExtensionHom
  let fCot := Algebra.Extension.Cotangent.map f
  let fSpace := Algebra.Extension.CotangentSpace.map f
  let fCotL := fCot.liftBaseChange L
  let fSpaceL := fSpace.liftBaseChange L
  have hfCot : Function.Injective fCotL :=
    RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection P Q hLCI
  have hfSpace : Function.Injective fSpaceL :=
    Algebra.Generators.CotangentSpace.map_toComp_injective Q P
  have hNat : fSpaceL ∘ₗ LinearMap.baseChange L P.toExtension.cotangentComplex =
      Pa.toExtension.cotangentComplex ∘ₗ fCotL := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [fSpaceL, fCotL]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul l x =>
      simp only [fSpaceL, fCotL, LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearMap.liftBaseChange_tmul, map_smul]
      exact congrArg (l • ·) (Algebra.Extension.CotangentSpace.map_cotangentComplex f x)
  have hBaseD : Function.Injective (LinearMap.baseChange L P.toExtension.cotangentComplex) := by
    intro x y hxy
    apply hfCot
    apply hPaInj
    calc
      Pa.toExtension.cotangentComplex (fCotL x) = fSpaceL
          (LinearMap.baseChange L P.toExtension.cotangentComplex x) :=
        (LinearMap.congr_fun hNat x).symm
      _ = fSpaceL (LinearMap.baseChange L P.toExtension.cotangentComplex y) :=
        congrArg fSpaceL hxy
      _ = Pa.toExtension.cotangentComplex (fCotL y) :=
        LinearMap.congr_fun hNat y
  let eDiff := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L
  let : Module.Flat A L := IsLocalization.flat L (Submonoid.powers a)
  let dL := LinearMap.baseChange L P.toExtension.cotangentComplex
  let q := eDiff.toLinearMap ∘ₗ LinearMap.baseChange L P.toExtension.toKaehler
  have hExact₀ : Function.Exact dL
      (LinearMap.baseChange L P.toExtension.toKaehler) := by
    show Function.Exact (LinearMap.baseChange L P.toExtension.cotangentComplex)
      (LinearMap.baseChange L P.toExtension.toKaehler)
    simpa only [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_exact L P.toExtension.exact_cotangentComplex_toKaehler
  have hExact : Function.Exact dL q := by
    intro x
    constructor
    · intro hx
      have hx' : LinearMap.baseChange L P.toExtension.toKaehler x = 0 :=
        eDiff.injective (by simpa [q] using hx)
      exact (hExact₀ x).mp hx'
    · intro hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy]
      show eDiff ((LinearMap.baseChange L P.toExtension.toKaehler) (dL y)) = 0
      simpa only [map_zero] using congrArg eDiff ((hExact₀ (dL y)).mpr ⟨y, rfl⟩)
  have hq : Function.Surjective q :=
    eDiff.surjective.comp (LinearMap.baseChange_surjective L P.toExtension.toKaehler_surjective)
  let dK : (L ⊗[A] P.toExtension.Cotangent) →ₗ[L] q.ker :=
    dL.codRestrict q.ker fun x => (hExact (dL x)).mpr ⟨x, rfl⟩
  have hdK : Function.Bijective dK := by
    constructor
    · exact fun x y hxy => hBaseD (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨y, hy⟩ := (hExact x.1).mp x.2
      exact ⟨y, Subtype.ext hy⟩
  let eKer := LinearEquiv.ofBijective dK hdK
  let : Module.Projective L (KaehlerDifferential R L) :=
    inferInstance
  let eSplit := projectiveQuotientSplit q hq
  let eProd :=
    (LinearEquiv.prodCongr (LinearEquiv.refl L (KaehlerDifferential R L)) eKer).trans eSplit
  let eF := (LinearEquiv.baseChange A L P.toExtension.CotangentSpace (Fin n → A)
      (P.cotangentSpaceBasis.repr.trans (Finsupp.linearEquivFunOnFinite A A (Fin n)))).trans
      (TensorProduct.piScalarRight A L L (Fin n))
  exact ⟨eF.symm.trans eProd.symm⟩

/-- Along a flat base change, the conormal module of the natural presentation of a symmetric
algebra becomes the base change of the kernel of the chosen presentation of its module. -/
private noncomputable def symmetricAlgebra_cotangent_baseChange_equiv_of_flat
    {A C B M K : Type*} [CommRing A] [CommRing C] [CommRing B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup K] [Module A K] [Algebra A C] [Algebra A B] [Algebra C B]
    [IsScalarTower A C B] [SMulCommClass A C B]
    (m : ℕ) (i : K →ₗ[A] (Fin m → A)) (p : (Fin m → A) →ₗ[A] M)
    (hi : Function.Injective i) (hip : Function.Exact i p) (hp : Function.Surjective p)
    (ι : M →ₗ[A] C) (hι : IsSymmetricAlgebra ι)
    (f : Fin m → C)
    (hα : Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := C) f))
    (hαX : ∀ j : Fin m,
      (MvPolynomial.aeval (R := A) (S₁ := C) f) (MvPolynomial.X (R := A) j) =
        ι (p ((Pi.basisFun A (Fin m)) j)))
    [Module.Flat A B] :
    B ⊗[C] (Algebra.Extension.ofSurjective (MvPolynomial.aeval (R := A) (S₁ := C) f) hα).Cotangent
      ≃ₗ[B] B ⊗[A] K := by
  classical
  let P : Algebra.Extension A C :=
    Algebra.Extension.ofSurjective (MvPolynomial.aeval (R := A) (S₁ := C) f) hα
  have hSym := cotangentComplex_of_isSymmetricAlgebra m i p hi hip hp C ι hι
    (MvPolynomial.aeval (R := A) (S₁ := C) f) hα hαX
  let eK : C ⊗[A] K →ₗ[C] P.Cotangent := Classical.choose hSym
  have hSym₁ := Classical.choose_spec hSym
  let eF : P.CotangentSpace ≃ₗ[C] (Fin m → C) := Classical.choose hSym₁
  have hSym₂ := Classical.choose_spec hSym₁
  let eΩ : KaehlerDifferential A C ≃ₗ[C] C ⊗[A] M := Classical.choose hSym₂
  have hSym₃ := Classical.choose_spec hSym₂
  have heKsurj : Function.Surjective eK := hSym₃.1
  have heq := hSym₃.2.1
  let cK := TensorProduct.AlgebraTensorModule.cancelBaseChange A C B B K
  let φ : B ⊗[A] K →ₗ[B] B ⊗[C] P.Cotangent :=
    (LinearMap.baseChange B eK) ∘ₗ cK.symm.toLinearMap
  have hφsurj : Function.Surjective φ :=
    (LinearMap.baseChange_surjective B heKsurj).comp cK.symm.surjective
  have hNat :
      (TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
        (LinearMap.baseChange B ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange C i)) ∘ₗ cK.symm.toLinearMap =
        (TensorProduct.piScalarRight A B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B i := by
    have hNat' :
        (TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ
            LinearMap.baseChange C i) =
        (TensorProduct.piScalarRight A B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B i ∘ₗ cK := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
      | tmul b z =>
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
        | tmul c k =>
          ext j
          simp only [cK, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
            LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]
          rw [map_mul, ← IsScalarTower.algebraMap_apply A C B (i k j)]
          ring
    calc
      _ = ((TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ
            LinearMap.baseChange C i)) ∘ₗ cK.symm.toLinearMap := rfl
      _ = ((TensorProduct.piScalarRight A B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B i ∘ₗ cK) ∘ₗ cK.symm.toLinearMap := by rw [hNat']
      _ = _ := by ext x; simp
  have hEqB :
      (TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
        (LinearMap.baseChange B eF.toLinearMap) ∘ₗ
          (LinearMap.baseChange B P.cotangentComplex) ∘ₗ φ =
        (TensorProduct.piScalarRight A B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B i := by
    have h0 :
        (LinearMap.baseChange B eF.toLinearMap) ∘ₗ
            (LinearMap.baseChange B P.cotangentComplex) ∘ₗ
            LinearMap.baseChange B eK =
          LinearMap.baseChange B ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ
            LinearMap.baseChange C i) := by
      simpa [eF, P, eK, LinearMap.baseChange_comp, LinearMap.comp_assoc] using
        congrArg (LinearMap.baseChange B) heq
    calc
      _ = ((TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
          (LinearMap.baseChange B eF.toLinearMap) ∘ₗ
          (LinearMap.baseChange B P.cotangentComplex) ∘ₗ
          LinearMap.baseChange B eK) ∘ₗ cK.symm.toLinearMap := by
            simp [φ, LinearMap.comp_assoc]
      _ = ((TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
          LinearMap.baseChange B ((TensorProduct.piScalarRight A C C (Fin m)).toLinearMap ∘ₗ
            LinearMap.baseChange C i)) ∘ₗ cK.symm.toLinearMap :=
          congrArg (fun f => ((TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ f) ∘ₗ
            cK.symm.toLinearMap) h0
      _ = _ := hNat
  have hiB : Function.Injective (LinearMap.baseChange B i) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := B) i hi)
  have hφinj : Function.Injective φ := by
    have hφker : φ.ker = ⊥ := by
      ext x
      simp only [Submodule.mem_bot, LinearMap.mem_ker]
      constructor
      · intro hx
        have hpi : (TensorProduct.piScalarRight A B B (Fin m)).toLinearMap
            ((LinearMap.baseChange B i) x) = 0 := by
          calc
            _ = ((TensorProduct.piScalarRight C B B (Fin m)).toLinearMap ∘ₗ
                (LinearMap.baseChange B eF.toLinearMap) ∘ₗ
                (LinearMap.baseChange B P.cotangentComplex) ∘ₗ φ) x :=
                  (LinearMap.congr_fun hEqB x).symm
            _ = 0 := by simp [hx]
        have hix : (LinearMap.baseChange B i) x = 0 :=
          (TensorProduct.piScalarRight A B B (Fin m)).injective hpi
        apply hiB
        simpa using hix
      · intro hx
        subst x
        simp
    exact LinearMap.ker_eq_bot.mp hφker
  exact (LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm

/-- `A → A_a → C_a` is a scalar tower, where `A_a → C_a` is the canonical localized map. -/
private lemma isScalarTower_away_awayMap {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (a : A) :
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap A C a)) :=
      (Localization.awayMap (algebraMap A C) a).toAlgebra
    IsScalarTower A (Localization.Away a) (Localization.Away (algebraMap A C a)) :=
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap A C a)) :=
    (Localization.awayMap (algebraMap A C) a).toAlgebra
  IsScalarTower.of_algebraMap_eq (fun x => by
    change _ = Localization.awayMap (algebraMap A C) a _
    dsimp [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_eq]
    rfl)

/-- A scalar tower `R → A → C → B` with `A → C → B` a tower gives a tower `R → A → B`. -/
private lemma isScalarTower_of_algebraMap_comp {R A C B : Type*} [CommRing R] [CommRing A]
    [CommRing C] [CommRing B] [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra A B] [Algebra C B] [Algebra R B] [IsScalarTower A C B] [IsScalarTower R C B] :
    IsScalarTower R A B :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R C B, IsScalarTower.algebraMap_apply R A C,
      IsScalarTower.algebraMap_apply A C B]

/-- If `A_a ⊗ M` is finite projective over `A_a`, then `C_a` is smooth over `A_a`, where
`C = Sym_A M`. -/
private lemma smooth_away_symmetricAlgebra {A M M₀ : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup M₀] [Module A M₀] (qequiv : M ≃ₗ[A] M₀) (a : A)
    [Module.Finite (Localization.Away a) (Localization.Away a ⊗[A] M₀)]
    [Module.Projective (Localization.Away a) (Localization.Away a ⊗[A] M₀)] :
    letI : Algebra (Localization.Away a)
      (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
      (Localization.awayMap (algebraMap A (SymmetricAlgebra A M)) a).toAlgebra
    Algebra.Smooth (Localization.Away a)
      (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) := by
  let L := Localization.Away a
  let eM : L ⊗[A] M ≃ₗ[L] L ⊗[A] M₀ := LinearEquiv.baseChange A L M M₀ qequiv
  let : Module.Finite L (L ⊗[A] M) := Module.Finite.equiv eM.symm
  let : Module.Projective L (L ⊗[A] M) := Module.Projective.of_equiv eM.symm
  have hSymSmooth : Algebra.Smooth L (SymmetricAlgebra L (L ⊗[A] M)) :=
    (symmetricAlgebra_smooth_iff_finite_projective L (L ⊗[A] M)).2
      ⟨inferInstance, inferInstance⟩
  let : Algebra L (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
    (Localization.awayMap (algebraMap A (SymmetricAlgebra A M)) a).toAlgebra
  let : IsScalarTower A L (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
    isScalarTower_away_awayMap a
  exact Algebra.Smooth.of_equiv
    ((SymmetricAlgebra.exists_algEquiv_baseChange A L M).choose.trans
      (localizationAwayTensorAlgEquiv a))

/-- The algebra has a presentation by finitely many polynomial variables whose conormal module
is free. -/
def HasFreeConormalPresentation (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] : Prop :=
  ∃ (n : ℕ) (P : Algebra.Generators R A (Fin n)),
    Module.Free A P.toExtension.Cotangent

/-- A finitely presented algebra admits one finite-type retract satisfying both local
improvements of its presentation. The retract is the symmetric algebra of the finite conormal
module of a polynomial presentation, and the retraction is its augmentation. This conormal module
is projective when the algebra is a local complete intersection over the base. -/
@[stacks 07CE]
theorem exists_finiteType_retraction_improving_presentation
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Algebra.FiniteType A C) (g : C →ₐ[R] A)
      (n : ℕ) (P : Algebra.Generators R A (Fin n))
      (e : C ≃ₐ[A] SymmetricAlgebra A P.toExtension.Cotangent),
      Module.Finite A P.toExtension.Cotangent ∧
        (RingHom.IsLocalCompleteIntersection (algebraMap R A) →
          Module.Projective A P.toExtension.Cotangent) ∧
        (∀ c : C, g c = SymmetricAlgebra.algebraMapInv (e c)) ∧
        g.comp (IsScalarTower.toAlgHom R A C) = AlgHom.id R A ∧
        (∀ a : A,
          RingHom.IsLocalCompleteIntersection (algebraMap R (Localization.Away a)) →
          (letI : Algebra (Localization.Away a)
                (Localization.Away (algebraMap A C a)) :=
              (Localization.awayMap (algebraMap A C) a).toAlgebra;
            Algebra.Smooth (Localization.Away a)
                (Localization.Away (algebraMap A C a)) ∧
              HasFreeConormalPresentation R (Localization.Away (algebraMap A C a)))) ∧
        (∀ a : A, Algebra.Smooth R (Localization.Away a) →
          Module.Free (Localization.Away (algebraMap A C a))
            (KaehlerDifferential R (Localization.Away (algebraMap A C a)))) := by
  classical
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Algebra.Generators R A (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by
      rw [heval]
      exact hf)
  let M₀ := P.toExtension.Cotangent
  let : Module.Finite A M₀ :=
    Algebra.Extension.Cotangent.finite P.fg_ker_of_finitePresentation
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' A M₀
  let F : Type v := Fin m → A
  let M : Type v := F ⧸ p.ker
  let π : F →ₗ[A] M := Submodule.mkQ p.ker
  let : Module.Finite A M := Module.Finite.of_surjective π (Submodule.mkQ_surjective _)
  let C := SymmetricAlgebra A M
  let hTower : IsScalarTower R A C := inferInstance
  let α : MvPolynomial (Fin m) A →ₐ[A] C :=
    MvPolynomial.aeval (fun i => SymmetricAlgebra.ι A M (π ((Pi.basisFun A (Fin m)) i)))
  let free : F →ₗ[A] MvPolynomial (Fin m) A :=
    (Pi.basisFun A (Fin m)).constr A MvPolynomial.X
  have hαfree : α.toLinearMap.comp free =
      (SymmetricAlgebra.ι A M).comp π := by
    apply (Pi.basisFun A (Fin m)).ext
    intro i
    simp [α, free]
  have hα : Function.Surjective α := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨MvPolynomial.C r, by
        simp only [α, MvPolynomial.aeval_C]
        rfl⟩
    | ι x =>
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective p.ker x
      exact ⟨free y, LinearMap.congr_fun hαfree y⟩
    | mul x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x * y, map_mul α x y⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add α x y⟩
  have hevalα : MvPolynomial.aeval (R := A) (fun i => α (MvPolynomial.X i)) = α := by
    ext i
    simp
  have hsurjα : Function.Surjective
      (MvPolynomial.aeval (R := A) (fun i => α (MvPolynomial.X i))) := by
    rw [hevalα]
    exact hα
  let Q : Algebra.Generators A C (Fin m) :=
    Algebra.Generators.ofSurjective (fun i => α (MvPolynomial.X i)) hsurjα
  let : Algebra.FiniteType A C := Q.finiteType
  let augA : C →ₐ[A] A := SymmetricAlgebra.lift (0 : M →ₗ[A] A)
  let g : C →ₐ[R] A := {
    toRingHom := augA.toRingHom
    commutes' := by
      intro r
      show augA (algebraMap R C r) = algebraMap R A r
      rw [show algebraMap R C = (algebraMap A C).comp (algebraMap R A) from rfl]
      simp [augA] }
  let AtoC : A →ₐ[R] C := @IsScalarTower.toAlgHom R A C _ _ _ _ _ _ hTower
  have hsection : g.comp AtoC = AlgHom.id R A := by
    ext a
    show augA (algebraMap A C a) = a
    exact augA.commutes a
  have hfiniteM₀ : Module.Finite A M₀ :=
    Algebra.Extension.Cotangent.finite P.fg_ker_of_finitePresentation
  let qequiv : M ≃ₗ[A] M₀ := p.quotKerEquivOfSurjective hp
  let eForward : C →ₐ[A] SymmetricAlgebra A M₀ :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M₀).comp qequiv.toLinearMap)
  let eBackward : SymmetricAlgebra A M₀ →ₐ[A] C :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp qequiv.symm.toLinearMap)
  have heForward (x : M) : eForward (SymmetricAlgebra.ι A M x) =
      SymmetricAlgebra.ι A M₀ (qequiv x) := by
    simp only [eForward]
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  have heBackward (x : M₀) : eBackward (SymmetricAlgebra.ι A M₀ x) =
      SymmetricAlgebra.ι A M (qequiv.symm x) := by
    simp only [eBackward]
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  have hForwardBackward : eForward.comp eBackward = AlgHom.id A _ := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    show eForward (eBackward (SymmetricAlgebra.ι A M₀ x)) = _
    rw [heBackward, heForward, qequiv.apply_symm_apply]
    simp
  have hBackwardForward : eBackward.comp eForward = AlgHom.id A _ := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    show eBackward (eForward (SymmetricAlgebra.ι A M x)) = _
    rw [heForward, heBackward, qequiv.symm_apply_apply]
    rfl
  let e : C ≃ₐ[A] SymmetricAlgebra A M₀ :=
    AlgEquiv.ofAlgHom eForward eBackward hForwardBackward hBackwardForward
  let iRel : p.ker →ₗ[A] F := p.ker.subtype
  have hiRel : Function.Injective iRel := Submodule.subtype_injective _
  have hexRel : Function.Exact iRel π := by
    simpa [iRel, π] using (LinearMap.exact_subtype_mkQ p.ker)
  let fSym : Fin m → C := fun j => α (MvPolynomial.X j)
  have hSymX : ∀ j : Fin m,
      (MvPolynomial.aeval (R := A) (S₁ := C) fSym) (MvPolynomial.X (R := A) j) =
        SymmetricAlgebra.ι A M (π ((Pi.basisFun A (Fin m)) j)) := by
    intro j
    simp [fSym, α]
  refine ⟨C, inferInstance, inferInstance, inferInstance, hTower,
    Q.finiteType, g, n, P, e, hfiniteM₀, ?_, ?_, hsection, ?_⟩
  · intro hlci
    exact (Algebra.Generators.cotangent_finite_projective_of_isLocalCompleteIntersection
      P hlci).2
  · intro c
    show augA c = SymmetricAlgebra.algebraMapInv (e c)
    have he : augA = (SymmetricAlgebra.algebraMapInv (R := A) (M := M₀)).comp e := by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro x
      simp [e, eForward, augA, SymmetricAlgebra.algebraMapInv_ι]
    exact congrArg (fun f : C →ₐ[A] A => f c) he
  · constructor
    · intro a ha
      let L := Localization.Away a
      let B := Localization.Away (algebraMap A C a)
      let : Algebra L B := (Localization.awayMap (algebraMap A C) a).toAlgebra
      have hproj₀ := localized_cotangent_finite_projective_of_isLocalCompleteIntersection P a ha
      let : Module.Finite L (L ⊗[A] M₀) := hproj₀.1
      let : Module.Projective L (L ⊗[A] M₀) := hproj₀.2
      let : IsScalarTower A L B := isScalarTower_away_awayMap a
      let hSmoothB : Algebra.Smooth L B := smooth_away_symmetricAlgebra qequiv a
      let : Algebra.Smooth L B := hSmoothB
      let : Module.Flat A L := IsLocalization.flat L (Submonoid.powers a)
      let : Module.Flat L B := hSmoothB.flat
      let : Module.Flat A B := Module.Flat.trans A L B
      let : IsScalarTower R A B := isScalarTower_of_algebraMap_comp (C := C)
      let eKbase : B ⊗[C] Q.toExtension.Cotangent ≃ₗ[B] B ⊗[A] p.ker :=
        symmetricAlgebra_cotangent_baseChange_equiv_of_flat (A := A) (C := C) (B := B)
          (M := M) (K := p.ker) m iRel π hiRel hexRel (Submodule.mkQ_surjective _)
          (SymmetricAlgebra.ι A M) SymmetricAlgebra.isSymmetricAlgebra_ι fSym hsurjα hSymX
      let Qloc := (Algebra.Generators.localizationAway B (algebraMap A C a)).comp Q
      let eQloc : Qloc.toExtension.Cotangent ≃ₗ[B]
          B × (B ⊗[C] Q.toExtension.Cotangent) :=
        localizedConormalEquiv (S := B) Q (algebraMap A C a)
      let eZ : Qloc.toExtension.Cotangent ≃ₗ[B] (B × (B ⊗[A] p.ker)) :=
        eQloc.trans (LinearEquiv.prodCongr (LinearEquiv.refl B B) eKbase)
      let : Algebra.Smooth A L := Algebra.Smooth.of_isLocalization_Away a
      have hSmoothAB : Algebra.Smooth A B := Algebra.Smooth.comp A L B
      let : Algebra.Smooth A B := hSmoothAB
      have hLCIAB := ringHom_isLocalCompleteIntersection_of_smooth (R := A) (A := B)
      let eCancelM := TensorProduct.AlgebraTensorModule.cancelBaseChange A L B B M₀
      have hXproj : Module.Projective B (B ⊗[A] M₀) := by
        let : Module.Projective B (B ⊗[L] (L ⊗[A] M₀)) :=
          projective_baseChange_of_finite_projective (R := L) (S := B)
            (M := L ⊗[A] M₀)
        exact Module.Projective.of_equiv eCancelM
      let : Module.Projective B (B ⊗[A] M₀) := hXproj
      let pB : B ⊗[A] F →ₗ[B] B ⊗[A] M₀ :=
        TensorProduct.AlgebraTensorModule.lTensor B B p
      have hpB : Function.Surjective pB := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => exact ⟨0, by simp [pB]⟩
        | add x y hx hy =>
            obtain ⟨u, rfl⟩ := hx
            obtain ⟨v, rfl⟩ := hy
            exact ⟨u + v, by simp [pB]⟩
        | tmul b z =>
            obtain ⟨y, rfl⟩ := hp z
            exact ⟨b ⊗ₜ[A] y, by simp [pB]⟩
      let eSplitB := projectiveQuotientSplit pB hpB
      let eKerB : B ⊗[A] p.ker ≃ₗ[B] pB.ker := LinearMap.tensorKerEquiv B B p
      let : Module.Free B (B ⊗[A] F) :=
        Module.Free.of_equiv (TensorProduct.piScalarRight A B B (Fin m)).symm
      let : Module.Free B ((B ⊗[A] M₀) × pB.ker) :=
        Module.Free.of_equiv eSplitB.symm
      let : Module.Projective B ((B ⊗[A] M₀) × pB.ker) := Module.Projective.of_free
      have hKerProj : Module.Projective B pB.ker :=
        Module.Projective.of_split (LinearMap.inr B (B ⊗[A] M₀) pB.ker)
          (LinearMap.snd B (B ⊗[A] M₀) pB.ker) (by ext x; rfl)
      let : Module.Projective B pB.ker := hKerProj
      let : Module.Projective B (B ⊗[A] p.ker) :=
        Module.Projective.of_equiv eKerB.symm
      let : Module.Projective B (B × (B ⊗[A] p.ker)) := inferInstance
      let ePair :=
        LinearEquiv.prodCongr (LinearEquiv.refl B (B ⊗[A] M₀)) eKerB
      let : Module.Free B ((B ⊗[A] M₀) × (B ⊗[A] p.ker)) :=
        Module.Free.of_equiv (ePair.trans eSplitB).symm
      let : Module.Free B (B × ((B ⊗[A] M₀) × (B ⊗[A] p.ker))) := inferInstance
      let eAll : ((B ⊗[A] M₀) × Qloc.toExtension.Cotangent) ≃ₗ[B]
          (B × ((B ⊗[A] M₀) × (B ⊗[A] p.ker))) := {
        toFun x := let z := eZ x.2; (z.1, (x.1, z.2))
        invFun x := (x.2.1, eZ.symm (x.1, x.2.2))
        left_inv := by
          intro x
          rcases x with ⟨m, q⟩
          simp
        right_inv := by
          intro x
          rcases x with ⟨b, m, k⟩
          simp
        map_add' := by
          intro x y
          rcases x with ⟨m₁, q₁⟩
          rcases y with ⟨m₂, q₂⟩
          simp
        map_smul' := by
          intro r x
          rcases x with ⟨m, q⟩
          simp }
      let : Module.Free B ((B ⊗[A] M₀) × Qloc.toExtension.Cotangent) :=
        Module.Free.of_equiv eAll.symm
      let Qcomp := Qloc.comp P
      let fcomp : (B ⊗[A] P.toExtension.Cotangent) →ₗ[B] Qcomp.toExtension.Cotangent :=
        LinearMap.liftBaseChange B
          (Algebra.Extension.Cotangent.map (Qloc.toComp P).toExtensionHom)
      let gcomp : Qcomp.toExtension.Cotangent →ₗ[B] Qloc.toExtension.Cotangent :=
        Algebra.Extension.Cotangent.map (Qloc.ofComp P).toExtensionHom
      have hInj : Function.Injective fcomp :=
        cotangent_map_toComp_injective_of_localCompleteIntersection P Qloc hLCIAB
      have hExact : Function.Exact fcomp gcomp := Algebra.Generators.Cotangent.exact Qloc P
      have hSurj : Function.Surjective gcomp :=
        Algebra.Generators.Cotangent.surjective_map_ofComp Qloc P
      let : Module.Projective B Qloc.toExtension.Cotangent :=
        Module.Projective.of_equiv eZ.symm
      have hFreeComp : Module.Free B Qcomp.toExtension.Cotangent :=
        free_of_split_exact fcomp gcomp hInj hExact hSurj
      let Ploc := Qloc.comp P
      let idx := (Unit ⊕ Fin m) ⊕ Fin n
      let eIdx : Fin (Fintype.card idx) ≃ idx := (Fintype.equivFin idx).symm
      let PlocFin := Ploc.reindex eIdx
      let eRen : MvPolynomial idx R ≃ₐ[R] MvPolynomial (Fin (Fintype.card idx)) R :=
        MvPolynomial.renameEquiv R eIdx.symm
      have hRen :
          (IsScalarTower.toAlgHom R PlocFin.toExtension.Ring B).comp eRen.toAlgHom =
            IsScalarTower.toAlgHom R Ploc.toExtension.Ring B := by
        ext i
        show algebraMap PlocFin.Ring B (eRen (X i)) = algebraMap Ploc.Ring B (X i)
        rw [PlocFin.algebraMap_apply, Ploc.algebraMap_apply]
        simp [eRen, PlocFin, Algebra.Generators.reindex_val]
      have hRenSymm :
          (IsScalarTower.toAlgHom R Ploc.toExtension.Ring B).comp eRen.symm.toAlgHom =
            IsScalarTower.toAlgHom R PlocFin.toExtension.Ring B := by
        ext i
        show algebraMap Ploc.Ring B (eRen.symm (X i)) = algebraMap PlocFin.Ring B (X i)
        rw [Ploc.algebraMap_apply, PlocFin.algebraMap_apply]
        simp [eRen, PlocFin, Algebra.Generators.reindex_val]
      let renHom : Ploc.toExtension.Hom PlocFin.toExtension :=
        Algebra.Extension.Hom.ofAlgHom eRen.toAlgHom hRen
      let renHomSymm : PlocFin.toExtension.Hom Ploc.toExtension :=
        Algebra.Extension.Hom.ofAlgHom eRen.symm.toAlgHom hRenSymm
      have hRenId : renHomSymm.comp renHom = Algebra.Extension.Hom.id _ := by
        apply Algebra.Extension.Hom.ext
        ext i
        show eRen.symm (eRen i) = i
        exact eRen.symm_apply_apply i
      have hRenIdSymm : renHom.comp renHomSymm = Algebra.Extension.Hom.id _ := by
        apply Algebra.Extension.Hom.ext
        ext i
        show eRen (eRen.symm i) = i
        exact eRen.apply_symm_apply i
      have hCotLeft :
          (Algebra.Extension.Cotangent.map renHomSymm) ∘ₗ
            Algebra.Extension.Cotangent.map renHom = LinearMap.id := by
        simpa only [hRenId, Algebra.Extension.Cotangent.map_id,
          LinearMap.restrictScalars_self] using
          (Algebra.Extension.Cotangent.map_comp _ renHom renHomSymm).symm
      have hCotRight :
          (Algebra.Extension.Cotangent.map renHom) ∘ₗ
            Algebra.Extension.Cotangent.map renHomSymm = LinearMap.id := by
        simpa only [hRenIdSymm, Algebra.Extension.Cotangent.map_id,
          LinearMap.restrictScalars_self] using
          (Algebra.Extension.Cotangent.map_comp _ renHomSymm renHom).symm
      have hReindex : Ploc.toExtension.Cotangent ≃ₗ[B] PlocFin.toExtension.Cotangent :=
        LinearEquiv.ofLinearMap (Algebra.Extension.Cotangent.map renHom)
          (Algebra.Extension.Cotangent.map renHomSymm) hCotRight hCotLeft
      exact ⟨hSmoothB, ⟨Fintype.card idx, PlocFin,
        Module.Free.of_equiv hReindex⟩⟩
    · intro a hs
      let L := Localization.Away a
      let B := Localization.Away (algebraMap A C a)
      let : Algebra.Smooth R L := hs
      let : Algebra.Smooth A L := Algebra.Smooth.of_isLocalization_Away a
      let : Algebra L B := (Localization.awayMap (algebraMap A C) a).toAlgebra
      let : IsScalarTower A L B := isScalarTower_away_awayMap a
      let : IsScalarTower R A B := isScalarTower_of_algebraMap_comp (C := C)
      let : IsScalarTower R L B :=
        IsScalarTower.of_algebraMap_eq (R := R) (S := L) (A := B) fun r => by
          calc
            algebraMap R B r = algebraMap A B (algebraMap R A r) :=
              IsScalarTower.algebraMap_apply R A B r
            _ = algebraMap L B (algebraMap R L r) := by
              rw [IsScalarTower.algebraMap_apply A L B,
                ← IsScalarTower.algebraMap_apply R A L]
      have hLCIRL := ringHom_isLocalCompleteIntersection_of_smooth (R := R) (A := L)
      have hproj₀ := localized_cotangent_finite_projective_of_isLocalCompleteIntersection
        P a hLCIRL
      let : Module.Finite L (L ⊗[A] M₀) := hproj₀.1
      let : Module.Projective L (L ⊗[A] M₀) := hproj₀.2
      have hSmoothB : Algebra.Smooth L B := smooth_away_symmetricAlgebra qequiv a
      let e₂ := localizationAwayTensorAlgEquiv (A := A) (C := C) (L := L) (B := B) a
      let : Algebra.Smooth L B := hSmoothB
      let : Module.Flat L B := hSmoothB.flat
      let hSym := cotangentComplex_of_isSymmetricAlgebra m iRel π hiRel hexRel
        (Submodule.mkQ_surjective _) (C := SymmetricAlgebra A M) (SymmetricAlgebra.ι A M)
        SymmetricAlgebra.isSymmetricAlgebra_ι α hα (by
          intro j
          rw [← hevalα]
          exact hSymX j)
      let eOmegaC := Classical.choose (Classical.choose_spec (Classical.choose_spec hSym))
      have hE₂right (c : C) : e₂ (1 ⊗ₜ[A] c) = algebraMap C B c := by
        simp [e₂, localizationAwayTensorAlgEquiv]
      let hPush : Algebra.IsPushout A L C B :=
        ⟨IsBaseChange.of_equiv e₂.toLinearEquiv hE₂right⟩
      let : Algebra.IsPushout A L C B := hPush
      let eOmega₁ := LinearEquiv.baseChange C B _ _ eOmegaC
      let eOmega₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A C B B M
      let eOmega₃ := LinearEquiv.baseChange A B M M₀ qequiv
      let eCancelM := TensorProduct.AlgebraTensorModule.cancelBaseChange A L B B M₀
      let eOmega : KaehlerDifferential L B ≃ₗ[B] B ⊗[L] (L ⊗[A] M₀) :=
        (KaehlerDifferential.tensorKaehlerEquiv A L C B).symm.trans
          (eOmega₁.trans (eOmega₂.trans (eOmega₃.trans eCancelM.symm)))
      obtain ⟨ec⟩ := localized_presentation_differentials_equiv P a hs
      let gDiff := KaehlerDifferential.map R L B B
      have hgDiff : Function.Surjective gDiff :=
        KaehlerDifferential.map_surjective R L B
      obtain ⟨sDiff, hsDiff⟩ :=
        gDiff.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hgDiff)
      have hsplitDiff : ∃ k : KaehlerDifferential L B →ₗ[B]
          KaehlerDifferential R B, gDiff.comp k = LinearMap.id :=
        ⟨sDiff, hsDiff⟩
      obtain ⟨eDiff, _, _⟩ :=
        (((KaehlerDifferential.exact_mapBaseChange_map R L B).split_tfae
          (kaehler_mapBaseChange_injective_of_subsingleton_h1 (R := R) (A := L) (B := B))
          hgDiff).out 1 3).mp
          hsplitDiff
      let ecB := LinearEquiv.baseChange L B _ _ ec
      let eAll : KaehlerDifferential R B ≃ₗ[B] (Fin n → B) :=
        eDiff.trans
          (((LinearEquiv.refl B (B ⊗[L] KaehlerDifferential R L)).prodCongr eOmega).trans
            ((TensorProduct.prodRight L B B (KaehlerDifferential R L)
                (L ⊗[A] M₀)).symm.trans
              (ecB.symm.trans (TensorProduct.piScalarRight L B B (Fin n)))))
      exact Module.Free.of_equiv eAll.symm

end Stacks.Smoothing
