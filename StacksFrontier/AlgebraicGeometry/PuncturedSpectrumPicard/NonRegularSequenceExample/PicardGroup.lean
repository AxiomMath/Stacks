module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.NonRegularSequenceExample.SquareZero
import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension
import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology
import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison

/-!
# The Picard group of the punctured spectrum in the non-regular-sequence example

Reduction modulo `w` is a first-order thickening of punctured spectra, its ideal sheaf is the
structure sheaf of the subscheme, depth two makes `H¹` of the punctured spectrum nonzero, and
units lift along the reduction; the exact sequence of [Stacks, Tag 0C6R] then makes the Picard
group of the punctured spectrum of `A` nontrivial ([Stacks, Tag 0F9L]).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.MvPowerSeries.RegularParameters

namespace Stacks.PuncturedSpectrumPicard.NonRegularSequence

universe u

open scoped Pointwise

/-! ### The reduction map of punctured spectra is a first-order thickening -/

/-- A surjection of rings with square-zero kernel induces a first-order thickening of their
spectra. -/
private theorem isFirstOrderThickening_specMap {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q) (hker : RingHom.ker q ^ 2 = ⊥) :
    Stacks.Thickenings.IsFirstOrderThickening (Spec.map (CommRingCat.ofHom q)) :=
  ⟨IsClosedImmersion.spec_of_surjective _ hq,
    (AlgebraicGeometry.ker_pow_spec_map_eq_bot_iff (CommRingCat.ofHom q) 2).mpr hker⟩

/-- Restricting a first-order thickening to an open of the ambient scheme gives a first-order
thickening: the kernel ideal sheaf of the restriction is the kernel ideal sheaf of the original
read on the image opens. -/
private theorem isFirstOrderThickening_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Stacks.Thickenings.IsFirstOrderThickening f) (U : Y.Opens) :
    Stacks.Thickenings.IsFirstOrderThickening (f ∣_ U) := by
  have hci : IsClosedImmersion f := hf.1
  refine ⟨IsZariskiLocalAtTarget.restrict hci U, Scheme.IdealSheafData.ext (funext fun V => ?_)⟩
  have h := congrArg (fun J : Y.IdealSheafData =>
    J.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩) hf.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply] at h ⊢
  rwa [Scheme.ker_morphismRestrict_ideal]

/-- A surjection of local rings pulls the punctured spectrum of the target back to the punctured
spectrum of the source: the induced map of spectra is injective and matches the closed points. -/
private theorem specMap_preimage_puncturedSpectrum {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (q : A →+* B) (hq : Function.Surjective q) :
    (Spec.map (CommRingCat.ofHom q)) ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A =
      Stacks.Divisors.puncturedSpectrum B := by
  ext x
  change PrimeSpectrum.comap q x ≠ IsLocalRing.closedPoint A ↔
    x ≠ IsLocalRing.closedPoint B
  let : IsLocalHom q := IsLocalHom.of_surjective q hq
  rw [← IsLocalRing.comap_closedPoint q]
  exact not_congr ((PrimeSpectrum.comap_injective_of_surjective q hq).eq_iff)

open CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

/-! ### The ideal sheaf of the thickening is the structure sheaf of the subscheme -/

section AffineIdealKernel

/-- Global sections of modules on an affine scheme is an additive functor. -/
private theorem gamma_additive {R : CommRingCat.{u}} :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

attribute [local instance] gamma_additive

/-- Two morphisms out of a quasi-coherent module on an affine scheme agree as soon as they
agree on global sections. -/
private theorem affine_hom_ext {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (hM : IsIso M.fromTildeΓ) (f g : M ⟶ N)
    (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  have : Epi M.fromTildeΓ := @IsIso.epi_of_iso _ _ _ _ _ hM
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := Scheme.Modules.fromTildeΓNatTrans.naturality f
  have hg := Scheme.Modules.fromTildeΓNatTrans.naturality g
  exact hf.symm.trans ((congrArg (fun a => (tilde.functor R).map a ≫ N.fromTildeΓ) h).trans hg)

/-- A morphism out of the value of a right adjoint at an object where the counit is invertible
comes from a morphism of the objects themselves. -/
private theorem map_surjective_of_counit_isIso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ G) {M N : D} (hM : IsIso (adj.counit.app M))
    (h : G.obj M ⟶ G.obj N) : ∃ f : M ⟶ N, G.map f = h := by
  have := hM
  let f := inv (adj.counit.app M) ≫ (adj.homEquiv _ N).symm h
  refine ⟨f, ?_⟩
  have hf : adj.counit.app M ≫ f = (adj.homEquiv _ N).symm h := by simp [f]
  have hh := congrArg (adj.homEquiv _ N) hf
  rw [← adj.homEquiv_symm_id M, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply] at hh
  change (adj.homEquiv _ M) ((adj.homEquiv _ M).symm (𝟙 _)) ≫ G.map f = h at hh
  simpa only [Equiv.apply_symm_apply, Category.id_comp] using hh

/-- A map of global sections out of a quasi-coherent module on an affine scheme is induced by a
map of modules. -/
private theorem affine_hom_exists {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (hM : IsIso M.fromTildeΓ)
    (h : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    ∃ f : M ⟶ N, moduleSpecΓFunctor.map f = h :=
  map_surjective_of_counit_isIso (tilde.adjunction (R := R)) hM h

/-- A short complex of quasi-coherent modules on an affine scheme which is exact on global
sections is exact. -/
private theorem affine_exact_of_top {R : CommRingCat.{u}} (S : ShortComplex (Spec R).Modules)
    (h₁ : IsIso S.X₁.fromTildeΓ) (h₂ : IsIso S.X₂.fromTildeΓ) (h₃ : IsIso S.X₃.fromTildeΓ)
    (h : (S.map moduleSpecΓFunctor).Exact) : S.Exact := by
  let e : (S.map moduleSpecΓFunctor).map (tilde.functor R) ≅ S :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ h₁) (@asIso _ _ _ _ _ h₂)
      (@asIso _ _ _ _ _ h₃)
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.f).symm
      (Scheme.Modules.fromTildeΓNatTrans.naturality S.g).symm
  exact (ShortComplex.exact_iff_of_iso e).mp (h.map (tilde.functor R))

/-- A map of quasi-coherent modules on an affine scheme that is injective on global sections is
a monomorphism. -/
private theorem affine_mono_of_top {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) (f : M ⟶ N)
    (hf : Mono (moduleSpecΓFunctor.map f)) : Mono f := by
  have hn := Scheme.Modules.fromTildeΓNatTrans.naturality f
  have := hf
  have : (tilde.functor R).PreservesMonomorphisms := inferInstance
  have h1 : Mono ((tilde.functor R).map (moduleSpecΓFunctor.map f)) := inferInstance
  have : Mono ((tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    @mono_comp _ _ _ _ _ _ h1 _ (@IsIso.mono_of_iso _ _ _ _ _ hN)
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at hn
  have : Mono (M.fromTildeΓ ≫ f) := hn ▸ ‹Mono _›
  have := hM
  exact (mono_comp_iff_of_isIso M.fromTildeΓ f).mp inferInstance

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.pushforward
  AlgebraicGeometry.moduleSpecΓFunctor
  AlgebraicGeometry.modulesSpecToSheaf
  ModuleCat.restrictScalars
  CategoryTheory.sheafCompose
  TopCat.Sheaf.forget

/-- Multiplication by `w` only sees the class of its argument modulo the kernel of `q`, because
`w` annihilates that kernel. -/
private theorem mul_section_reduction {A B : Type*} [CommRing A] [CommRing B]
    (q : A →+* B) (σ : B →+* A) (w : A)
    (hqσ : ∀ b, q (σ b) = b) (hw : w ^ 2 = 0)
    (hex : Function.Exact (fun b => w * σ b) q) (a : A) :
    w * σ (q a) = w * a := by
  have hqa : q (a - σ (q a)) = 0 := by simp [hqσ]
  obtain ⟨b, hb⟩ := (hex _).mp hqa
  have h : w * (a - σ (q a)) = 0 := by
    rw [← hb]
    linear_combination σ b * hw
  linear_combination -h

/-- **The ideal sheaf of a square-zero extension of affine schemes is the pushforward of the
structure sheaf of the closed subscheme.**  Let `q : A → B` be a surjection of rings with a
ring-homomorphism section `σ`, whose kernel is the image of `b ↦ w · σ b` for an element `w` with
`w² = 0`.  Then multiplication by `w` presents `q_* 𝒪_{Spec B}` as the kernel of
`𝒪_{Spec A} ⟶ q_* 𝒪_{Spec B}`, which is the ideal sheaf of `Spec q`. -/
private theorem affine_squareZero_kernel
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (σ : B →+* A) (w : A)
    (hqσ : ∀ b, q (σ b) = b) (hqw : q w = 0) (hw : w ^ 2 = 0)
    (hinj : Function.Injective (fun b => w * σ b))
    (hex : Function.Exact (fun b => w * σ b) q) :
    ∃ (β : (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom q))).obj
        (SheafOfModules.unit (Spec (.of B)).ringCatSheaf) ⟶
        SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      (hβ : β ≫ SheafOfModules.unitToPushforwardObjUnit
        (Spec.map (CommRingCat.ofHom q)).toRingCatSheafHom = 0),
      Nonempty (IsLimit (KernelFork.ofι β hβ)) := by
  let f := Spec.map (CommRingCat.ofHom q)
  let O : (Spec (.of A)).Modules := SheafOfModules.unit (Spec (.of A)).ringCatSheaf
  let P : (Spec (.of A)).Modules := (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit (Spec (.of B)).ringCatSheaf)
  let φ : O ⟶ P := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let γA := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let γB := (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  have hnat (a : A) : f.appTop.hom (γA a) = γB (q a) :=
    congrArg (fun g : CommRingCat.of A ⟶ Γ(Spec (.of B), ⊤) => g a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  let MP : ModuleCat A := moduleSpecΓFunctor.obj P
  let MO : ModuleCat A := moduleSpecΓFunctor.obj O
  let : Module A MP := MP.isModule
  let : Module A MO := MO.isModule
  let μ : MP ⟶ MO :=
    ConcreteCategory.ofHom (C := ModuleCat A) (X := MP) (Y := MO)
      (show MP →ₗ[A] MO from {
      toFun := fun b => γA (w * σ (γB.symm b))
      map_add' := by
        have key : ∀ s t : Γ(Spec (.of B), ⊤),
            γA (w * σ (γB.symm (s + t))) =
              γA (w * σ (γB.symm s)) + γA (w * σ (γB.symm t)) := by
          intro s t
          rw [map_add γB.symm, map_add σ, mul_add, map_add γA]
        exact key
      map_smul' := by
        intro a b
        change Γ(Spec (.of B), ⊤) at b
        change γA (w * σ (γB.symm (f.appTop.hom (γA a) * b))) =
          γA a * γA (w * σ (γB.symm b))
        rw [hnat, map_mul γB.symm, γB.symm_apply_apply, map_mul σ, ← map_mul γA]
        congr 1
        rw [← mul_assoc, mul_section_reduction q σ w hqσ hw hex]
        ring })
  have hPiso : IsIso P.fromTildeΓ :=
    isIso_fromTildeΓ_pushforward (CommRingCat.ofHom q)
      (SheafOfModules.unit (Spec (.of B)).ringCatSheaf)
  have hOiso : IsIso O.fromTildeΓ := inferInstance
  obtain ⟨β, hβtop⟩ := affine_hom_exists (M := P) (N := O) hPiso μ
  have hβapply (b : Γ(Spec (.of B), ⊤)) : β.val.app (op ⊤) b =
      γA (w * σ (γB.symm b)) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hβtop) b
  have hz : β ≫ φ = 0 := by
    apply affine_hom_ext hPiso
    ext b
    change f.appTop.hom (β.val.app (op ⊤) b) = 0
    rw [hβapply b, hnat, map_mul, hqw, zero_mul, map_zero]
  have hmono : Mono (moduleSpecΓFunctor.map β) := by
    rw [hβtop]
    exact (ModuleCat.mono_iff_injective μ).mpr fun x y h =>
      γB.symm.injective (hinj (γA.injective h))
  have : Mono β := affine_mono_of_top hPiso hOiso β hmono
  have hS : (ShortComplex.mk β φ hz).Exact := by
    apply affine_exact_of_top (S := ShortComplex.mk β φ hz) hPiso hOiso hPiso
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro x
    change f.appTop.hom x = 0 ↔ ∃ b, β.val.app (op ⊤) b = x
    obtain ⟨a, rfl⟩ := γA.surjective x
    rw [hnat, map_eq_zero_iff γB γB.injective]
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := (hex a).mp ha
      exact ⟨γB b, by rw [hβapply (γB b), γB.symm_apply_apply]; exact congrArg γA hb⟩
    · rintro ⟨b, hb⟩
      rw [hβapply b] at hb
      exact (hex a).mpr ⟨γB.symm b, γA.injective hb⟩
  exact ⟨β, hz, ⟨hS.fIsKernel⟩⟩

end AffineIdealKernel

section IdealSheafRestriction

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  structureSheafRing RingedSpaceModuleAdjunction.structureSheafHom
  SheafOfModules.toSheaf PresheafOfModules.toPresheaf
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.pushforward
  AlgebraicGeometry.Scheme.Opens.toScheme
  TopologicalSpace.Opens.toTopCat
  AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso
  AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.instCategory
  AlgebraicGeometry.Scheme.Modules.restrictFunctor
  SheafOfModules.forget

/-- **Restricting the pushforward of a structure sheaf to an open of the target is the
pushforward along the restricted morphism.**  Both have sections over `W ⊆ U` the functions on
`f ⁻¹ (U ∩ W)`; the comparison is the transport along that equality of opens, and its naturality
holds because the opens of a space form a thin category. -/
@[implicit_reducible]
private def restrictPushforwardUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W => ?_) ?_)
  · let e := X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U W.unop)).op
    refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso e) ?_
    intro r
    apply AddCommGrpCat.hom_ext
    ext s
    change Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ W.unop)) at s
    change Γ(U.toScheme, W.unop) at r
    change ((f ∣_ U).app W.unop).hom r *
      (show Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ W.unop) from e.hom s) =
      e.hom ((f.app (U.ι ''ᵁ W.unop)).hom ((U.ι.appIso W.unop).inv r) * s)
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, morphismRestrict_app, map_mul]
    rfl
  · have key : ∀ (A B C D : (Opens ↥X)ᵒᵖ) (m₁ : A ⟶ B) (m₂ : B ⟶ D) (m₃ : A ⟶ C) (m₄ : C ⟶ D)
        (t : X.presheaf.obj A),
        (X.presheaf.map m₂).hom ((X.presheaf.map m₁).hom t) =
          (X.presheaf.map m₄).hom ((X.presheaf.map m₃).hom t) := by
      intro A B C D m₁ m₂ m₃ m₄ t
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← X.presheaf.map_comp,
        ← X.presheaf.map_comp]
      exact congrArg (fun m => (X.presheaf.map m).hom t) (Subsingleton.elim _ _)
    intro W V g
    ext s
    exact key _ _ _ _ _ _ _ _ s

/-- The comparison of `restrictPushforwardUnitIso` carries the structure-sheaf map of `f` to
that of `f ∣_ U`. -/
private theorem restrictPushforwardUnitIso_compat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) :
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (restrictPushforwardUnitIso f U).hom =
        SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change Γ(U.toScheme, W.unop) at s
  change (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op).hom
      ((f.app (U.ι ''ᵁ W.unop)).hom ((U.ι.appIso W.unop).inv s)) =
    ((f ∣_ U).app W.unop).hom s
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, morphismRestrict_app]
  rfl

/-- **A kernel presentation of the ideal sheaf restricts to an open.**  Restriction to an open
is exact, so it carries a kernel presentation of the ideal sheaf of `f` by the pushforward of the
structure sheaf of the source to one for `f ∣_ U`. -/
private theorem restrict_squareZero_kernel {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (β : (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit Y.ringCatSheaf)
    (hβ : β ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom = 0)
    (hlim : IsLimit (KernelFork.ofι β hβ)) :
    Nonempty ((Scheme.Modules.pushforward (f ∣_ U)).obj
        (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) ≅
      Stacks.ClosedImmersion.idealSheaf (f ∣_ U).toLRSHom.toShHom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let : PreservesFiniteLimits (F ⋙ Scheme.Modules.toPresheaf U.toScheme) := by
    change PreservesFiniteLimits (Scheme.Modules.toPresheaf Y ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj U.ι.opensFunctor.op)
    let : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
    let : PreservesFiniteLimits
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj U.ι.opensFunctor.op) :=
      inferInstance
    infer_instance
  let : ReflectsFiniteLimits (Scheme.Modules.toPresheaf U.toScheme) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  let : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F (Scheme.Modules.toPresheaf U.toScheme)
  let φ := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let ψ := SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom
  let eO := Scheme.Modules.restrictUnitIso U.ι
  let eP := restrictPushforwardUnitIso f U
  have hφ : eO.hom ≫ ψ = F.map φ ≫ eP.hom := by
    have hc : eO.inv ≫ F.map φ ≫ eP.hom = ψ := restrictPushforwardUnitIso_compat f U
    rw [← hc, Iso.hom_inv_id_assoc]
  let b := eP.inv ≫ F.map β ≫ eO.hom
  have hb : b ≫ ψ = 0 := by
    calc b ≫ ψ = eP.inv ≫ F.map β ≫ eO.hom ≫ ψ := by simp only [b, Category.assoc]
      _ = eP.inv ≫ F.map β ≫ F.map φ ≫ eP.hom := by rw [hφ]
      _ = eP.inv ≫ F.map (β ≫ φ) ≫ eP.hom := by
            rw [F.map_comp]; simp only [Category.assoc]
      _ = 0 := by rw [hβ, F.map_zero, zero_comp, comp_zero]
  let h : IsLimit (KernelFork.ofι b hb) :=
    IsKernel.ofIso (F.map φ) (KernelFork.mapIsLimit _ hlim F) (KernelFork.ofι b hb)
      eO eP eP hφ (by simp [b])
  let e2 : (KernelFork.ofι b hb).pt ≅ kernel ψ :=
    h.conePointUniqueUpToIso (limit.isLimit (parallelPair ψ 0))
  refine ⟨e2.trans (eqToIso ?_)⟩
  rfl

/-- **The ideal sheaf of a first-order thickening, as an abelian sheaf on the closed
subscheme.**  An identification of the ideal sheaf on the ambient scheme with the pushforward of
the structure sheaf of the closed subscheme becomes, after pulling back along the thickening — a
homeomorphism — an identification of `𝒪_X` with `ℐ|_X`. -/
private def idealAddSheafOnSubIsoOfPushforwardIso {X Y : Scheme.{u}} (i : X ⟶ Y)
    (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (e : (Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      Stacks.Thickenings.idealAddSheafOnSub i := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)
  let K := Stacks.Thickenings.idealAddSheaf i
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{u} i.base
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i.base
  let ea : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F ≅ K :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e
  letI : IsIso adj.counit :=
    ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso AddCommGrpCat.{u}
      hi.1.isClosedEmbedding.isEmbedding.isInducing
  exact (asIso (adj.counit.app F)).symm ≪≫ L.mapIso ea

/-- **The thickening of punctured spectra carries the identification of its ideal sheaf.**  For a
split surjection `q : A → B` whose kernel is `w · σ(B)` with `w² = 0`, and an open `U` of
`Spec A` with preimage `V`, the restriction of `Spec q` over `U` is a morphism `V ⟶ U`
compatible with `Spec q`, and its ideal sheaf, pulled back to `V`, is the structure sheaf
of `V`. -/
private theorem exists_restrict_thickening_idealIso
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (σ : B →+* A) (w : A)
    (hqσ : ∀ b, q (σ b) = b) (hqw : q w = 0) (hw : w ^ 2 = 0)
    (hinj : Function.Injective (fun b => w * σ b))
    (hex : Function.Exact (fun b => w * σ b) q)
    (U : (Spec (.of A)).Opens) (V : (Spec (.of B)).Opens)
    (hpre : (Spec.map (CommRingCat.ofHom q)) ⁻¹ᵁ U = V)
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((Spec.map (CommRingCat.ofHom q)) ∣_ U)) :
    ∃ (i : V.toScheme ⟶ U.toScheme) (_ : Stacks.Thickenings.IsFirstOrderThickening i),
      i ≫ U.ι = V.ι ≫ Spec.map (CommRingCat.ofHom q) ∧
      Nonempty ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).obj
        (SheafOfModules.unit V.toScheme.ringCatSheaf) ≅
          Stacks.Thickenings.idealAddSheafOnSub i) := by
  subst V
  obtain ⟨β, hβ, ⟨hlim⟩⟩ := affine_squareZero_kernel q σ w hqσ hqw hw hinj hex
  obtain ⟨e⟩ := restrict_squareZero_kernel _ U β hβ hlim
  exact ⟨_, hi, morphismRestrict_ι _ U, ⟨idealAddSheafOnSubIsoOfPushforwardIso _ hi e⟩⟩

end IdealSheafRestriction

attribute [local implicit_reducible]
  TopCat.Sheaf
  CategoryTheory.sheafCompose
  structureSheafRing
  RingedSpaceModuleAdjunction.structureSheafHom
  SheafOfModules.toSheaf
  PresheafOfModules.toPresheaf
  Stacks.Cohomology.SheafTorsor.sheafCohomologyOne

/-! ### Depth two makes `H¹` of the punctured spectrum nonzero -/

/-- **Local cohomology is nonzero in the degree equal to the depth.**  This is the nonvanishing
half of [Stacks, Tag 0AVZ]: the depth is the infimum of the degrees in which local cohomology
with support in the maximal ideal is nonzero, and that infimum, being a natural number, is
attained. -/
private theorem nontrivial_localCohomologyModule_of_depth_eq
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (hn : Module.depth A (IsLocalRing.maximalIdeal A) A = n) :
    Nontrivial (Stacks.LocalCohomology.localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) (ModuleCat.of A A) (n : ℤ)) := by
  let I := IsLocalRing.maximalIdeal A
  let M : ModuleCat.{u} A := ModuleCat.of A A
  have hIM : I • (⊤ : Submodule A M) ≠ ⊤ := by
    simpa [M, I] using (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  let S : Set ℕ∞ := {d | ∃ j : ℕ, d = (j : ℕ∞) ∧ Nontrivial
    (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (j : ℤ))}
  have hd : sInf S = n :=
    (Stacks.LocalCohomology.depth_eq_sInf_nontrivial_localCohomologyWithSupportIn.{u, u}
      A I M hIM).symm.trans hn
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, sInf_empty] at hd
    exact ENat.natCast_ne_top n hd.symm
  obtain ⟨j, hj, hnt⟩ : (n : ℕ∞) ∈ S := hd ▸ csInf_mem hS
  have hjn : j = n := by exact_mod_cast hj.symm
  subst j
  have := hnt
  exact (Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule A I
    (IsNoetherian.noetherian _) M (n : ℤ)).toLinearEquiv.toEquiv.symm.nontrivial

/-- **The first cohomology of the structure sheaf of the complement of the closed point is
nonzero at depth two.**  By the comparison of [Stacks, Tag 0DWR] between `H^n(U, 𝒪_U)` and
`H^{n+1}_𝔪(A)` for `n ≥ 1`, this is the nonvanishing of `H²_𝔪(A)`. -/
private theorem nontrivial_sheafH_one_unit_complementZeroLocus_of_depth_eq_two
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology
      ↥(Stacks.LocalCohomology.complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme))
      AddCommGrpCat.{u})]
    (hd : Module.depth A (IsLocalRing.maximalIdeal A) A = 2) :
    Nontrivial (CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf (Stacks.LocalCohomology.complementZeroLocus A
          (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit (Stacks.LocalCohomology.complementZeroLocus A
          (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf)) 1) := by
  let hnt : Nontrivial (_root_.Hgroup
      (Stacks.LocalCohomology.complementZeroLocus A
        (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (Stacks.LocalCohomology.complementZeroLocus A
        (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf)) := by
    rw [← not_subsingleton_iff_nontrivial, ← AddCommGrpCat.isZero_iff_subsingleton]
    intro h
    have h2 : IsZero (_root_.Hgroup
        (Stacks.LocalCohomology.complementZeroLocus A
          (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf ⊤ 1
        (Stacks.LocalCohomology.complementTilde A (IsLocalRing.maximalIdeal A)
          (ModuleCat.of A A))) :=
      h.of_iso ((_root_.Hfunctor (Stacks.LocalCohomology.complementZeroLocus A
        (IsLocalRing.maximalIdeal A) : Scheme).ringCatSheaf ⊤ 1).mapIso
          (Stacks.LocalCohomology.complementTildeRingIsoUnit A (IsLocalRing.maximalIdeal A)))
    have h3 :=
      (Stacks.LocalCohomology.isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _) (ModuleCat.of A A) 1 le_rfl).1 h2
    rw [show ((1 : ℕ) : ℤ) + 1 = ((2 : ℕ) : ℤ) from by norm_num,
      ModuleCat.isZero_iff_subsingleton] at h3
    exact not_subsingleton_iff_nontrivial.2
      (nontrivial_localCohomologyModule_of_depth_eq A 2 hd) h3
  exact (Stacks.Cohomology.ModuleComparison.schemeHgroupTopAddEquivSheafH
    (Stacks.LocalCohomology.complementZeroLocus A
      (IsLocalRing.maximalIdeal A) : Scheme) 1 _).symm.toEquiv.nontrivial

/-- **The first cohomology of the structure sheaf of a depth-two punctured spectrum is
nonzero.** -/
private theorem nontrivial_sheafH_one_unit_puncturedSpectrum_of_depth_eq_two
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [hExt : HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (hd : Module.depth A (IsLocalRing.maximalIdeal A) A = 2) :
    Nontrivial (CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf
        (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit
          (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf)) 1) := by
  revert hExt
  rw [AlgebraicGeometry.puncturedSpectrum_eq_complementZeroLocus A]
  intro hExt
  exact nontrivial_sheafH_one_unit_complementZeroLocus_of_depth_eq_two A hd

/-! ### Units lift along the reduction of punctured spectra -/

/-- A map of sheaves of abelian groups that is surjective on global sections is surjective on
degree-zero cohomology, which is global sections. -/
private theorem surjective_sheafH_zero_map {Y : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} Y} (f : F ⟶ G)
    (hf : Function.Surjective (f.hom.app (op (⊤ : Opens Y)))) :
    Function.Surjective (CategoryTheory.Sheaf.H.map.{u} f 0) := by
  have hT : IsTerminal (⊤ : Opens Y) := isTerminalTop
  intro y
  obtain ⟨s, hs⟩ := hf (CategoryTheory.Sheaf.H.equiv₀ G hT y)
  refine ⟨(CategoryTheory.Sheaf.H.equiv₀ F hT).symm s, ?_⟩
  apply (CategoryTheory.Sheaf.H.equiv₀ G hT).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality hT f, AddEquiv.apply_symm_apply, hs]

/-- If every invertible global function on the closed subscheme lifts to the ambient scheme,
the units map of the sequence of [Stacks, Tag 0C6R] is surjective in degree zero. -/
private theorem surjective_unitsToSubCohomology_zero {X X' : Scheme.{u}} (i : X ⟶ X')
    (hsurj : Function.Surjective (Units.map i.appTop.hom.toMonoidHom)) :
    Function.Surjective (Stacks.Thickenings.unitsToSubCohomology i 0) := by
  refine surjective_sheafH_zero_map _ fun s => ?_
  obtain ⟨t, ht⟩ := hsurj s.toMul
  refine ⟨Additive.ofMul t, ?_⟩
  rw [Stacks.Thickenings.unitsRestrictionSheafHom_app]
  exact congrArg Additive.ofMul ht

/-- **Units lift along the reduction of punctured spectra of a split surjection of local
rings.**  If `q : A → B` has a ring-homomorphism section `σ` and the global functions on the
punctured spectrum of `B` are `B` itself, then every invertible global function on the punctured
spectrum of `B` is the restriction of one on the punctured spectrum of `A`: lift it to `B` along
the identification, apply `σ`, and push it up. -/
private theorem surjective_units_appTop_puncturedSpectrum
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (q : A →+* B) (σ : B →+* A) (hσ : ∀ b, q (σ b) = b)
    (i : (Stacks.Divisors.puncturedSpectrum B).toScheme ⟶
      (Stacks.Divisors.puncturedSpectrum A).toScheme)
    (hi : i ≫ (Stacks.Divisors.puncturedSpectrum A).ι =
      (Stacks.Divisors.puncturedSpectrum B).ι ≫ Spec.map (CommRingCat.ofHom q))
    (hB : Function.Bijective (((Scheme.ΓSpecIso (.of B)).inv ≫
      (Stacks.Divisors.puncturedSpectrum B).ι.appTop).hom)) :
    Function.Surjective (Units.map i.appTop.hom.toMonoidHom) := by
  let U := Stacks.Divisors.puncturedSpectrum A
  let V := Stacks.Divisors.puncturedSpectrum B
  let γA := ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom
  let γB := ((Scheme.ΓSpecIso (.of B)).inv ≫ V.ι.appTop).hom
  let eB := RingEquiv.ofBijective γB hB
  have hc (a : A) : i.appTop.hom (γA a) = γB (q a) := by
    have htop := congrArg (fun f => f.appTop) hi
    simp only [Scheme.Hom.comp_appTop] at htop
    have hh : (Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop ≫ i.appTop =
        CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (.of B)).inv ≫ V.ι.appTop := by
      rw [htop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)]
      rfl
    exact congrArg (fun f : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) => f a) hh
  intro v
  refine ⟨Units.map (γA.comp σ).toMonoidHom (Units.map eB.symm.toMonoidHom v), ?_⟩
  apply Units.ext
  change i.appTop.hom (γA (σ (eB.symm (v : Γ(V.toScheme, ⊤))))) = v
  rw [hc, hσ]
  exact eB.apply_symm_apply _

/-! ### The conclusion of Stacks 0F9L -/

/-- **The exact sequence of [Stacks, Tag 0C6R] forces a nontrivial Picard group.**  Let
`i : X ⟶ X'` be a first-order thickening with square-zero ideal sheaf `ℐ`.  The sequence of
[Stacks, Tag 0C6R] reads

`H⁰(X', 𝒪_{X'}^*) → H⁰(X, 𝒪_X^*) → H¹(X, ℐ) → Pic(X')`,

so if the first map is surjective then `H¹(X, ℐ) → Pic(X')` is injective, and a nontrivial
`H¹(X, ℐ)` makes `Pic(X')` nontrivial.  This is the step the source of [Stacks, Tag 0F9L]
uses to conclude. -/
private theorem not_subsingleton_picardGroup_of_firstOrderThickening
    {X X' : Scheme.{u}} (i : X ⟶ X') (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (hunits : Function.Surjective (Stacks.Thickenings.unitsToSubCohomology i 0))
    (hH1 : Nontrivial (CategoryTheory.Sheaf.H.{u}
      (Stacks.Thickenings.idealAddSheafOnSub i) 1)) :
    ¬ Subsingleton (Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
      (_root_.structureSheaf X'.sheaf).property) := by
  intro hsub
  have hb0 : ∀ b, Stacks.Thickenings.thickeningBoundary i hi 0 b = 0 := by
    intro b
    obtain ⟨a, rfl⟩ := hunits b
    exact (Stacks.Thickenings.exact_unitsToSubCohomology i hi 0).apply_apply_eq_zero a
  have hu0 : ∀ c, Stacks.Thickenings.unitsToIdealCohomology i hi c = 0 := fun c => by
    change (Stacks.Thickenings.idealCohomologyEquiv i hi 1).symm
      (Stacks.Thickenings.thickeningBoundary i hi 0 c) = 0
    rw [hb0 c, map_zero]
  have hx0 : ∀ x : CategoryTheory.Sheaf.H.{u}
      (Stacks.Thickenings.idealAddSheafOnSub i) 1, x = 0 := by
    intro x
    obtain ⟨c, hc⟩ := (Stacks.Thickenings.exact_unitsToIdealCohomology i hi x).mp
      (hsub.allEq _ 0)
    exact hc.symm.trans (hu0 c)
  obtain ⟨x, y, hxy⟩ := hH1
  exact hxy ((hx0 x).trans (hx0 y).symm)

/-- **[Stacks, Tag 0F9L], the punctured spectra.**  Reduction modulo `w` is a first-order
thickening `i : U₀ ⟶ U` of the punctured spectrum of `A₀` inside that of `A`, lying over
`Spec` of the reduction `q : A → A₀`; every invertible global function on `U₀` is the
restriction of one on `U`; and the ideal sheaf of `i`, pulled back to `U₀`, is the structure
sheaf of `U₀`.

These are the source's three geometric inputs.  The thickening is `A = A₀[w]/(w²)` read on
spectra and restricted to the punctured spectra; the lifting of units is the section `ι` of `q`
together with `Γ(U₀, 𝒪_{U₀}) = A₀`; and the identification of the ideal sheaf is multiplication
by `w`, which carries `A₀` isomorphically onto the kernel `wA` of `q`. -/
@[stacks 0F9L "the punctured spectra: reduction modulo w is a first-order thickening U₀ ⟶ U \
over Spec of the reduction, invertible global functions lift along it, and its ideal sheaf \
pulled back to U₀ is the structure sheaf of U₀"]
public theorem exists_puncturedSpectrum_firstOrderThickening (k : Type u) [Field k] :
    ∃ (q : exampleRing k →+* intermediateRing k)
      (i : (Stacks.Divisors.puncturedSpectrum (intermediateRing k)).toScheme ⟶
        (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme)
      (_ : Stacks.Thickenings.IsFirstOrderThickening i),
      (∀ p : powerSeriesRing k 8,
        q (Ideal.Quotient.mk (eightVariableIdeal k) p) =
          Ideal.Quotient.mk (sevenVariableIdeal k) (MvPowerSeries.killCompl sevenToEight p)) ∧
      i ≫ (Stacks.Divisors.puncturedSpectrum (exampleRing k)).ι =
        (Stacks.Divisors.puncturedSpectrum (intermediateRing k)).ι ≫
          Spec.map (CommRingCat.ofHom q) ∧
      Function.Surjective (Stacks.Thickenings.unitsToSubCohomology i 0) ∧
      Nonempty ((SheafOfModules.toSheaf
        (Stacks.Divisors.puncturedSpectrum (intermediateRing k)).toScheme.ringCatSheaf).obj
          (SheafOfModules.unit
            (Stacks.Divisors.puncturedSpectrum (intermediateRing k)).toScheme.ringCatSheaf) ≅
        Stacks.Thickenings.idealAddSheafOnSub i) := by
  let : Nontrivial (intermediateRing k) := intermediateRing_nontrivial k
  let : Nontrivial (exampleRing k) := exampleRing_nontrivial k
  obtain ⟨e, ι, q, hι, hq, he, hew, hqι, hqw, hinj, hex⟩ :=
    exampleRing_equiv_truncatedPolynomial k
  have hsurj : Function.Surjective q := fun a => ⟨ι a, hqι a⟩
  have hker : RingHom.ker q ^ 2 = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [pow_two]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    obtain ⟨a, ha⟩ := (hex x).mp hx
    obtain ⟨b, hb⟩ := (hex y).mp hy
    rw [← ha, ← hb]
    change squareZeroCoordinate k * ι a * (squareZeroCoordinate k * ι b) = 0
    calc
      _ = squareZeroCoordinate k ^ 2 * (ι a * ι b) := by ring
      _ = 0 := by rw [squareZeroCoordinate_sq, zero_mul]
  obtain ⟨i, hthick, hc, hα⟩ := exists_restrict_thickening_idealIso q ι
    (squareZeroCoordinate k) hqι hqw (squareZeroCoordinate_sq k) hinj hex
    (Stacks.Divisors.puncturedSpectrum (exampleRing k))
    (Stacks.Divisors.puncturedSpectrum (intermediateRing k))
    (specMap_preimage_puncturedSpectrum q hsurj)
    (isFirstOrderThickening_morphismRestrict _ (isFirstOrderThickening_specMap q hsurj hker) _)
  exact ⟨q, i, hthick, hq, hc,
    surjective_unitsToSubCohomology_zero i
      (surjective_units_appTop_puncturedSpectrum q ι hqι i hc
        (intermediateRing_globalSections_puncturedSpectrum k)),
    hα⟩

/-- **[Stacks, Tag 0F9L], the conclusion in the small model.** The Picard group of the
punctured spectrum of
`A = k⟦a,b,x,y,z,u,v,w⟧/(a³, b³, xa² + yab + zb², w²)`
is nontrivial.

The proof is the source's.  `exists_puncturedSpectrum_firstOrderThickening` supplies the
first-order thickening `i : U₀ ⟶ U`, the lifting of invertible global functions along it, and
the identification of its ideal sheaf with `𝒪_{U₀}`; `intermediateRing_depth` and
`nontrivial_sheafH_one_unit_puncturedSpectrum_of_depth_eq_two` make `H¹(U₀, 𝒪_{U₀})` nonzero.
The sequence of [Stacks, Tag 0C6R] then makes `H¹(U₀, ℐ) → Pic(U)` injective, so `Pic(U)` is
nonzero.

The Picard group here is the one the sequence of [Stacks, Tag 0C6R] is stated at in this
library, `Stacks.SheafOfModules.Picard.PicardGroup`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Picard.lean`): the universe-shrunk model of
Tag 040B.  It is a different constant from the `Stacks.SheafOfModules.PicardGroup` of
`StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean` that
`AlgebraicGeometry.Scheme.picardGroup` abbreviates, and at which [Stacks, Tag 0F2I] and the
companion example `Stacks.PuncturedSpectrumPicard.QuadricCone.picardGroup_not_subsingleton'`
are stated — but the two are isomorphic as abelian groups by
`Stacks.SheafOfModules.picardGroupShrinkAddEquiv`, compatibly with the class of an invertible
module, so this statement and
`exampleRing_scheme_picardGroup_puncturedSpectrum_not_subsingleton` are equivalent and the
latter is the clause of the tag.

The library's third Picard-group development, `Stacks.SheafPicardGroup.PicardGroup` — see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Divisors/DivisorPicardClass.lean` — has
no comparison isomorphism to either of these two, and nothing here goes through it.

`exampleRing_picardGroup_puncturedSpectrum_not_subsingleton` is this statement with the
source's three geometric inputs taken as arguments rather than proved. -/
public theorem exampleRing_picardGroup_puncturedSpectrum_not_subsingleton'
    (k : Type u) [Field k] :
    ¬ Subsingleton (Stacks.SheafOfModules.Picard.PicardGroup
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.sheaf.obj
      (_root_.structureSheaf
        (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.sheaf).property) := by
  let : Nontrivial (intermediateRing k) := intermediateRing_nontrivial k
  let : IsNoetherianRing (intermediateRing k) := inferInstance
  obtain ⟨q, i, hthick, hq, hc, hunits, ⟨α⟩⟩ :=
    exists_puncturedSpectrum_firstOrderThickening k
  have := nontrivial_sheafH_one_unit_puncturedSpectrum_of_depth_eq_two (intermediateRing k)
    (intermediateRing_depth k)
  exact not_subsingleton_picardGroup_of_firstOrderThickening i hthick hunits
    (Stacks.Thickenings.cohomologyEquivOfIso α 1).symm.toEquiv.nontrivial

/-- **[Stacks, Tag 0F9L], the conclusion in the small model**, given the source's three
geometric inputs.  The Picard group of the punctured spectrum of
`A = k⟦a,b,x,y,z,u,v,w⟧/(a³, b³, xa² + yab + zb², w²)` is nontrivial.

The inputs are arguments here: the first-order thickening `i` of the punctured spectra with
`hthick`, the lifting `hunits` of invertible global functions along it, and the nonvanishing
`hH1` of `H¹(U₀, ℐ)`.  All three are proved in this file — by
`exists_puncturedSpectrum_firstOrderThickening`, `intermediateRing_depth` and
`nontrivial_sheafH_one_unit_puncturedSpectrum_of_depth_eq_two` — and
`exampleRing_picardGroup_puncturedSpectrum_not_subsingleton'` is this statement with them
discharged. -/
public theorem exampleRing_picardGroup_puncturedSpectrum_not_subsingleton
    (k : Type u) [Field k]
    (i : (Stacks.Divisors.puncturedSpectrum (intermediateRing k)).toScheme ⟶
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme)
    (hthick : Stacks.Thickenings.IsFirstOrderThickening i)
    (hunits : Function.Surjective (Stacks.Thickenings.unitsToSubCohomology i 0))
    (hH1 : Nontrivial (CategoryTheory.Sheaf.H.{u}
      (Stacks.Thickenings.idealAddSheafOnSub i) 1)) :
    ¬ Subsingleton (Stacks.SheafOfModules.Picard.PicardGroup
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.sheaf.obj
      (_root_.structureSheaf
        (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.sheaf).property) :=
  not_subsingleton_picardGroup_of_firstOrderThickening i hthick hunits hH1

/-- **[Stacks, Tag 0F9L], the conclusion.** The Picard group of the punctured spectrum
`U = Spec A ∖ {𝔪}` of
`A = k⟦a,b,x,y,z,u,v,w⟧/(a³, b³, xa² + yab + zb², w²)`
is nontrivial.  Together with `powerSeriesRing_isRegularLocalRing` and
`powerSeriesRing_dimension` — the ambient ring `B = k⟦a,b,x,y,z,u,v,w⟧` is regular of
dimension `8`, and `A = B/(f₁, f₂, f₃, f₄)` with `r = 4`, so `dim B - r = 4 ≥ 4` — this is
the source's witness that [Stacks, Tag 0F2I] fails without the hypothesis that
`f₁, …, f_r` be a regular sequence.

The Picard group is `AlgebraicGeometry.Scheme.picardGroup`, the same one [Stacks, Tag 0F2I]
and the companion example
`Stacks.PuncturedSpectrumPicard.QuadricCone.picardGroup_not_subsingleton'` are stated at, so
this is literally the negation of that proposition's conclusion for this `A`.

The argument itself runs in the universe-shrunk model of Tag 040B, where the exact sequence of
[Stacks, Tag 0C6R] lives: it is
`exampleRing_picardGroup_puncturedSpectrum_not_subsingleton'`, carried here across
`Stacks.SheafOfModules.picardGroupShrinkAddEquiv`, the isomorphism of abelian groups between
the two models. -/
@[stacks 0F9L "the conclusion: the Picard group of the punctured spectrum is nontrivial, at \
the same Scheme.picardGroup that Stacks 0F2I is stated at, so this is literally the negation \
of that proposition's conclusion for this A"]
public theorem exampleRing_scheme_picardGroup_puncturedSpectrum_not_subsingleton
    (k : Type u) [Field k] :
    ¬ Subsingleton
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.picardGroup := by
  intro hPic
  have e := (Stacks.SheafOfModules.picardGroupShrinkAddEquiv
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum (exampleRing k)).toScheme.ringCatIsSheaf).symm.toEquiv
  exact exampleRing_picardGroup_puncturedSpectrum_not_subsingleton' k
    (e.subsingleton_congr.mpr hPic)


end Stacks.PuncturedSpectrumPicard.NonRegularSequence
