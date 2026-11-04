module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Modules on an affine scheme and their global sections

Let `X` be an affine scheme. Global sections over `⊤` identify the quasi-coherent modules on `X`
with the modules over `Γ(X, ⊤)`; this file proves the parts of that identification used for
coherent adic systems on affine schemes (Stacks 087W).

The quasi-inverse is `affineTilde`: the module `M` goes to `M̃` on `Spec Γ(X, ⊤)`, restricted back
along `X.isoSpec.hom`. It is left adjoint to global sections (`affineTildeAdjunction`) and fully
faithful, so the unit `M ⟶ Γ(M̃, ⊤)` is an isomorphism; and on a Noetherian affine scheme it sends
finite modules to coherent sheaves and realizes a surjection of finite modules as a sheaf quotient
by an ideal power.

In the other direction, a coherent module on a Noetherian affine scheme has finite global
sections, and a module annihilated by `I ^ n` on global sections has `I ^ n M = 0` as sheaves.

## Main definitions

* `Stacks.Coherent.affineRestrictionEquivalence` — restriction along `X.isoSpec.hom` as an
  equivalence `(Spec Γ(X, ⊤)).Modules ≌ X.Modules`.
* `Stacks.Coherent.affineTilde` — the quasi-inverse of global sections.
* `Stacks.Coherent.affineTildeAdjunction` — its adjunction with global sections.

## Main results

* `Stacks.Coherent.coherentAdicTerm_finiteSections` — a coherent module on a Noetherian affine
  scheme has finite global sections.
* `Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful` — global sections are fully faithful
  on quasi-coherent modules.
* `Stacks.Coherent.affineTildeSectionsIso` — the unit of the adjunction is an isomorphism.
* `Stacks.Coherent.affine_idealPowerMultiple_eq_bot` — a module whose global sections are
  annihilated by `I ^ n` has `I ^ n M = 0`.
* `Stacks.Coherent.affineTildeQuotientIso` — a surjection of modules with kernel `I ^ n` becomes,
  after `affineTilde`, the sheaf quotient by the `n`-th ideal-power multiple.
* `Stacks.Coherent.affineTilde_coherent` — `affineTilde` carries finite modules to coherent
  sheaves.

## Implementation notes

The affine scheme is used as given rather than replaced by a spectrum, so two restrictions appear:
`X.isoSpec.hom : X ⟶ Spec Γ(X, ⊤)` and its inverse `(isAffineOpen_top X).fromSpec`. They are the
same morphism up to `IsAffineOpen.fromSpec_top`, which is what makes
`affineRestrictionEquivalence` an equivalence.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Bridging instances for the scalar action on sections

The module structure on sections is declared over `X.ringCatSheaf.obj.obj U` in
`Mathlib.Algebra.Category.ModuleCat.Sheaf` and over `Γ(X, U)` in
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, and instance search cannot cross the `TopCat.Sheaf`
definition to see that the two agree. The bridging instances are stated once in
`Completion.IdealPowerQuasicoherent` and re-enabled here. -/

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsModuleRingCatSheaf

local instance moduleEvaluationΓ {X : Scheme.{u}} (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) ((SheafOfModules.evaluation X.ringCatSheaf U).obj M) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

local instance moduleRestrictScalarsSections {X : Scheme.{u}} (M : X.Modules)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    Module (X.presheaf.obj V)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj (M.val.obj V)) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj V)
    ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj (M.val.obj V)))

attribute [local instance] Stacks.Algebraization.sectionsSMulCommClassΓ

/-- Being of finite type is invariant under isomorphism, at the universe instantiation that
`X.Modules` for `X : Scheme.{u}` requires. -/
public theorem isFiniteType_of_iso_local {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (hM : M.IsFiniteType) : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ : ∃ σ : M.LocalGeneratorsData.{u, u, u, u}, σ.IsFiniteType :=
    hM.exists_localGeneratorsData
  let τ : N.LocalGeneratorsData.{u, u, u, u} := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i => (σ.generators i).equivOfIso
      ((SheafOfModules.overFunctor X.ringCatSheaf (σ.X i)).mapIso e) }
  exact SheafOfModules.IsFiniteType.mk (M := N) ⟨τ, ⟨fun i => ⟨(hσ.isFiniteType i).finite⟩⟩⟩

/-- An affine scheme is locally Noetherian as soon as its ring of global sections is. -/
public theorem isLocallyNoetherian_of_isNoetherianRing_top (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] : IsLocallyNoetherian X :=
  isLocallyNoetherian_of_affine_cover
    (S := fun _ : Unit => ⟨⊤, isAffineOpen_top X⟩) (by simp) (fun _ => inferInstance)

/-- Restriction along a morphism of schemes preserves modules of finite type. -/
private theorem isFiniteType_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (hM : M.IsFiniteType) : (M.restrict f).IsFiniteType :=
  isFiniteType_of_iso_local ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    (AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M)

/-- A coherent module on a Noetherian affine scheme is the sheaf associated with a finite module
over the ring of global sections. -/
@[ega "I 10.10.5" "(a) ⇒ (c), special case"]
public theorem coherentAdicTerm_finiteTilde
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [M.IsCoherent] :
    Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn M ⊤ (isAffineOpen_top X) := by
  have htfae := @Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X
    (isLocallyNoetherian_of_isNoetherianRing_top X) M
  exact (htfae.out 1 4 (h₁ := rfl) (h₂ := rfl)).mp ‹_› ⊤ (isAffineOpen_top X)

/-- A coherent module on a Noetherian affine scheme has finite module of global sections. -/
public theorem coherentAdicTerm_finiteSections
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [M.IsCoherent] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  have hloc : IsLocallyNoetherian X := isLocallyNoetherian_of_isNoetherianRing_top X
  have htfae := @Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X hloc M
  obtain ⟨hqc, hft⟩ := (htfae.out 1 2 (h₁ := rfl) (h₂ := rfl)).mp ‹M.IsCoherent›
  let f := (isAffineOpen_top X).fromSpec
  have hfi : IsOpenImmersion f := (isAffineOpen_top X).isOpenImmersion_fromSpec
  let F' := M.restrict f
  have hRestr : F'.IsFiniteType := isFiniteType_restrict f M hft
  have hQ : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f M
  let R : CommRingCat.{u} := Γ(X, ⊤)
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let qM : P.FullSubcategory := ⟨F', hQ⟩
  let E := AlgebraicGeometry.tildeEquiv (R := R)
  let m := E.inverse.obj qM
  let eCounit : (tilde m) ≅ qM.obj := {
    hom := (E.counitIso.app qM).hom.hom
    inv := (E.counitIso.app qM).inv.hom
    hom_inv_id := congrArg (fun g => g.hom) (E.counitIso.app qM).hom_inv_id
    inv_hom_id := congrArg (fun g => g.hom) (E.counitIso.app qM).inv_hom_id }
  have htilde : (tilde m).IsFiniteType :=
    isFiniteType_of_iso_local eCounit.symm hRestr
  have hm : Module.Finite Γ(X, ⊤) m := (AlgebraicGeometry.tilde_isFiniteType_iff m).mp htilde
  let eTop := Stacks.Algebraization.affineSectionsEquiv M ⊤ (isAffineOpen_top X)
  have hmod : Module.Finite Γ(X, ⊤) Γ(F', ⊤) := hm
  exact Module.Finite.of_surjective eTop.toLinearMap eTop.surjective

/-- The global sections over `⊤` of the restriction of `M` to `Spec Γ(X, ⊤)` are the global
sections of `M`. -/
public noncomputable def affineRestrictionSectionsIso
    (X : Scheme.{u}) [IsAffine X] (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
      (M.restrict (isAffineOpen_top X).fromSpec) ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj M :=
  (Stacks.Algebraization.affineSectionsEquiv M ⊤ (isAffineOpen_top X)).toModuleIso

/-- Pullback along an isomorphism of schemes is an equivalence on modules. -/
public alias pullback_isEquivalence_of_iso :=
  AlgebraicGeometry.isEquivalence_modulesPullback_of_iso

/-- Global sections are fully faithful on the quasi-coherent modules of an affine scheme. -/
public noncomputable def affineQuasicoherentSectionsFullyFaithful
    (X : Scheme.{u}) [IsAffine X] :
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).FullyFaithful := by
  let f := (isAffineOpen_top X).fromSpec
  have hf : f = X.isoSpec.inv := IsAffineOpen.fromSpec_top
  have hpb : (Scheme.Modules.pullback f).IsEquivalence := by
    rw [hf]
    exact pullback_isEquivalence_of_iso X.isoSpec.symm
  have hr : (Scheme.Modules.restrictFunctor f).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (Scheme.Modules.pullback f)).ofIso
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have hrfull := hr.full
  have hrfaithful := hr.faithful
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let Q := SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf
  let H := Q.lift (P.ι ⋙ Scheme.Modules.restrictFunctor f) (fun M =>
    Scheme.Modules.isQuasicoherent_restrictFunctor f M.obj)
  let K := H ⋙ (tildeEquiv (R := Γ(X, ⊤))).inverse
  have hH : H.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (G := Q.ι) ((P.fullyFaithfulι).comp hr)
  have hK : K.FullyFaithful := hH.comp
    (tildeEquiv (R := Γ(X, ⊤))).symm.fullyFaithfulFunctor
  apply hK.ofIso
  refine NatIso.ofComponents (fun M => affineRestrictionSectionsIso X M.obj) ?_
  intro M N φ
  ext x
  have hImage : (⊤ : X.Opens) = f ''ᵁ ⊤ := by simp [f]
  exact congrArg (fun g => g.hom x)
    (φ.hom.val.naturality (eqToHom hImage).op).symm

/-- A map of global sections of quasi-coherent modules on an affine scheme comes from a map of
modules. -/
public noncomputable def affineQuasicoherentHomLift
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj M ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj N) : M ⟶ N :=
  ((affineQuasicoherentSectionsFullyFaithful X).preimage
    (X := ⟨M, inferInstance⟩) (Y := ⟨N, inferInstance⟩) f).hom

/-- `affineQuasicoherentHomLift` is a section of taking global sections. -/
public theorem affineQuasicoherentHomLift_map
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj M ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj N) :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
      (affineQuasicoherentHomLift f) = f :=
  (affineQuasicoherentSectionsFullyFaithful X).map_preimage
    (X := ⟨M, inferInstance⟩) (Y := ⟨N, inferInstance⟩) f

/-- Two maps of quasi-coherent modules on an affine scheme agreeing on global sections are
equal. -/
public theorem affineQuasicoherentHom_ext
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {f g : M ⟶ N}
    (h : (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map f =
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map g) : f = g :=
  congrArg (fun k => k.hom)
    ((affineQuasicoherentSectionsFullyFaithful X).map_injective
      (X := ⟨M, inferInstance⟩) (Y := ⟨N, inferInstance⟩) h)

/-- Restriction along `X.isoSpec.hom` is an equivalence between the modules on
`Spec Γ(X, ⊤)` and those on an affine `X`. -/
public noncomputable def affineRestrictionEquivalence (X : Scheme.{u}) [IsAffine X] :
    (Spec Γ(X, ⊤)).Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.restrictFunctor X.isoSpec.hom)
    (Scheme.Modules.restrictFunctor (isAffineOpen_top X).fromSpec)
    ((Scheme.Modules.restrictFunctorComp (isAffineOpen_top X).fromSpec X.isoSpec.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr
        (by simpa only [IsAffineOpen.fromSpec_top] using X.isoSpec.inv_hom_id) ≪≫
      Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp X.isoSpec.hom (isAffineOpen_top X).fromSpec).symm ≪≫
      Scheme.Modules.restrictFunctorCongr
        (by simpa only [IsAffineOpen.fromSpec_top] using X.isoSpec.hom_inv_id) ≪≫
      Scheme.Modules.restrictFunctorId)

/-- The quasi-inverse of global sections on an affine scheme: the associated sheaf on
`Spec Γ(X, ⊤)`, restricted back to `X`. -/
public noncomputable def affineTilde (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor _ ⋙ (affineRestrictionEquivalence X).functor

/-- `affineTilde` is left adjoint to global sections. -/
public noncomputable def affineTildeAdjunction (X : Scheme.{u}) [IsAffine X] :
    affineTilde X ⊣ SheafOfModules.evaluation X.ringCatSheaf (op ⊤) := by
  let adj := (tilde.adjunction (R := Γ(X, ⊤))).comp
    (affineRestrictionEquivalence X).toAdjunction
  apply adj.ofNatIsoRight
  refine NatIso.ofComponents (fun M => affineRestrictionSectionsIso X M) ?_
  intro M N φ
  ext x
  have hImage : (⊤ : X.Opens) = (isAffineOpen_top X).fromSpec ''ᵁ ⊤ := by simp
  exact congrArg (fun g => g.hom x)
    (φ.val.naturality (eqToHom hImage).op).symm

/-- The image of `affineTilde` consists of quasi-coherent modules. -/
public theorem affineTilde_quasicoherent (X : Scheme.{u}) [IsAffine X]
    (M : ModuleCat.{u} Γ(X, ⊤)) : ((affineTilde X).obj M).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.hom (tilde M)

/-- The unit of `affineTildeAdjunction` is an isomorphism: a module is the global sections of the
sheaf it generates. -/
public noncomputable def affineTildeSectionsIso (X : Scheme.{u}) [IsAffine X]
    (M : ModuleCat.{u} Γ(X, ⊤)) :
    M ≅ (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj ((affineTilde X).obj M) := by
  have hfull : (affineTilde X).Full := inferInstanceAs
    (tilde.functor _ ⋙ (affineRestrictionEquivalence X).functor).Full
  have hfaithful : (affineTilde X).Faithful := inferInstanceAs
    (tilde.functor _ ⋙ (affineRestrictionEquivalence X).functor).Faithful
  let adj := affineTildeAdjunction X
  have hunit : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  exact asIso (adj.unit.app M)

/-- A scalar annihilating the global sections of a quasi-coherent module on an affine scheme
annihilates its sections over every open. -/
public theorem affine_annihilator_restrict {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (a : Γ(X, ⊤))
    (ha : ∀ x : Γ(M, ⊤), a • x = 0) (U : X.Opens) (x : Γ(M, U)) :
    X.presheaf.map U.leTop.op a • x = 0 := by
  let σ : M ⟶ M := { val := {
    app := fun V => ModuleCat.ofHom
      (LinearMap.lsmul Γ(X, V.unop) Γ(M, V.unop)
        (X.presheaf.map V.unop.leTop.op a))
    naturality := by
      rintro ⟨V⟩ ⟨W⟩ i
      ext y
      have hsm := M.val.map_smul i
        (show X.ringCatSheaf.obj.obj (op V) from X.presheaf.map V.leTop.op a) y
      have hcomp : (ConcreteCategory.hom (X.ringCatSheaf.obj.map i))
          (X.presheaf.map V.leTop.op a) = X.presheaf.map W.leTop.op a :=
        (ConcreteCategory.congr_hom (X.presheaf.map_comp V.leTop.op i) a).symm
      exact (congrArg (fun r => r • (ConcreteCategory.hom (M.val.map i)) y) hcomp).symm.trans
        hsm.symm } }
  have hσ : σ = 0 := by
    apply affineQuasicoherentHom_ext
    ext (y : Γ(M, ⊤))
    show X.presheaf.map (𝟙 (op ⊤)) a • y = 0
    rw [X.presheaf.map_id]
    exact ha y
  exact congrArg (fun f : M ⟶ M => f.val.app (op U) x) hσ

/-- A quasi-coherent module whose global sections are annihilated by `I ^ n` has sections over
every affine open annihilated by the `n`-th power of the ideal there. -/
public theorem affine_idealPower_annihilates {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (h : I ^ n • (⊤ : Submodule Γ(X, ⊤) Γ(M, ⊤)) = ⊥)
    (U : X.affineOpens) :
    (Scheme.IdealSheafData.ofIdealTop I).ideal U ^ n •
      (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥ := by
  have hle : (Scheme.IdealSheafData.ofIdealTop I).ideal U ^ n ≤
      Module.annihilator Γ(X, U) Γ(M, U) := by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal, ← Ideal.map_pow,
      Ideal.map_le_iff_le_comap]
    intro a ha
    refine Module.mem_annihilator.mpr fun x => affine_annihilator_restrict M a (fun y => ?_) U.1 x
    simpa only [h, Submodule.mem_bot] using Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
  exact eq_bot_iff.mpr (Submodule.smul_le.mpr fun a ha x _ => Module.mem_annihilator.mp (hle ha) x)

/-- A quasi-coherent module on an affine scheme whose global sections are annihilated by `I ^ n`
has `I ^ n M = 0` as a subsheaf. -/
public theorem affine_idealPowerMultiple_eq_bot {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (h : I ^ n • (⊤ : Submodule Γ(X, ⊤) Γ(M, ⊤)) = ⊥) :
    Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop I) n M = ⊥ := by
  exact eq_bot_iff.mpr ((Stacks.Algebraization.idealPowerMultiple_le_iff _ _ _ _).mpr fun U =>
    (affine_idealPower_annihilates I n M h U).trans_le bot_le)

/-- A map out of `M` whose target is annihilated by `I ^ n` on every affine open kills the
subsheaf `I ^ n M`: the subsheaf is contained in the sectionwise kernel. -/
public theorem idealPowerMultiple_le_kernelSubmodule {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, I.ideal U ^ n •
      (⊤ : Submodule Γ(X, U) Γ(N, U)) = ⊥) :
    Stacks.Algebraization.idealPowerMultiple I n M ≤ Stacks.Algebraization.kernelSubmodule f := by
  apply (Stacks.Algebraization.idealPowerMultiple_le_iff _ _ _ _).mpr
  intro U
  apply Submodule.smul_le.mpr
  intro a ha x _
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj]
  show f.app U.1 (a • x) = 0
  rw [Scheme.Modules.Hom.app_smul]
  simpa only [h U, Submodule.mem_bot] using
    Submodule.smul_mem_smul ha (Submodule.mem_top (x := f.app U.1 x))

/-- `affineTilde` carries annihilation by `I ^ n` from the module to the global sections of the
sheaf. -/
public theorem affineTilde_power_annihilates (X : Scheme.{u}) [IsAffine X]
    (I : Ideal Γ(X, ⊤)) (n : ℕ) (M : ModuleCat.{u} Γ(X, ⊤))
    (h : I ^ n • (⊤ : Submodule Γ(X, ⊤) M) = ⊥) :
    I ^ n • (⊤ : Submodule Γ(X, ⊤) Γ((affineTilde X).obj M, ⊤)) = ⊥ := by
  let e := (affineTildeSectionsIso X M).toLinearEquiv
  have h2 := map_smul_top_local (I ^ n) e.toLinearMap e.surjective
  rw [h, Submodule.map_bot] at h2
  exact h2.symm

/-- A surjection `p : M ⟶ N` of modules with kernel `I ^ n M` becomes, after `affineTilde`, the
sheaf quotient by the `n`-th ideal-power multiple. -/
public noncomputable def affineTildeQuotientIso (X : Scheme.{u}) [IsAffine X]
    (I : Ideal Γ(X, ⊤)) (n : ℕ) {M N : ModuleCat.{u} Γ(X, ⊤)}
    (p : M ⟶ N) (hp : Function.Surjective p.hom)
    (hk : LinearMap.ker p.hom = I ^ n • (⊤ : Submodule Γ(X, ⊤) M)) :
    { e : Stacks.Algebraization.idealPowerQuotient (Scheme.IdealSheafData.ofIdealTop I) n
        ((affineTilde X).obj M) ≅ (affineTilde X).obj N //
      cokernel.π (Stacks.Algebraization.idealPowerMultiple
        (Scheme.IdealSheafData.ofIdealTop I) n ((affineTilde X).obj M)).ι ≫ e.hom =
        (affineTilde X).map p } := by
  let L := affineTilde X
  let adj := affineTildeAdjunction X
  let P := Stacks.Algebraization.idealPowerMultiple
    (Scheme.IdealSheafData.ofIdealTop I) n (L.obj M)
  have hLN : (L.obj N).IsQuasicoherent := affineTilde_quasicoherent X N
  have hLM : (L.obj M).IsQuasicoherent := affineTilde_quasicoherent X M
  have hN : I ^ n • (⊤ : Submodule Γ(X, ⊤) N) = ⊥ := by
    rw [← map_smul_top_local (I ^ n) p.hom hp, ← hk, ← Submodule.comap_bot, Submodule.map_comap_eq]
    simp
  let P' : X.Modules := P.toSheafOfModules
  let Pι : P' ⟶ L.obj M := P.ι
  have hPker : P ≤ Stacks.Algebraization.kernelSubmodule (L.map p) :=
    idealPowerMultiple_le_kernelSubmodule _ _ _
      (affine_idealPower_annihilates I n _ (affineTilde_power_annihilates X I n N hN))
  have w : Pι ≫ L.map p = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext x
    have hx := hPker (op V) x.property
    rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj] at hx
    exact hx
  have hpepi : Epi p := (ModuleCat.epi_iff_surjective _).mpr hp
  have hLadj : L.IsLeftAdjoint := adj.isLeftAdjoint
  have hLepi : Epi (L.map p) := inferInstance
  let hc : IsColimit (CokernelCofork.ofπ (L.map p) w) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro Z g wg
    let k := adj.homEquiv M Z g
    have hker : LinearMap.ker p.hom ≤ LinearMap.ker k.hom := by
      rw [hk]
      intro x hx
      let e := (affineTildeSectionsIso X M).toLinearEquiv
      have hex : e x ∈ I ^ n • (⊤ : Submodule Γ(X, ⊤) Γ(L.obj M, ⊤)) := by
        have hh := Submodule.mem_map_of_mem (f := e.toLinearMap) hx
        rwa [map_smul_top_local (I ^ n) e.toLinearMap e.surjective] at hh
      have hgen : I ^ n • (⊤ : Submodule Γ(X, ⊤) Γ(L.obj M, ⊤)) ≤
          P.toSubmodule.obj (op ⊤) := by
        have hh := (Stacks.Algebraization.idealPowerMultiple_le_iff
          (Scheme.IdealSheafData.ofIdealTop I) n (L.obj M) P).mp le_rfl
          ⟨⊤, isAffineOpen_top X⟩
        simpa [Scheme.IdealSheafData.ofIdealTop_ideal] using hh
      exact congrArg (fun f => f.val.app (op ⊤) ⟨e x, hgen hex⟩) wg
    let d := (exists_desc_of_ker_le p k hp hker).choose
    have hd : p ≫ d = k := (exists_desc_of_ker_le p k hp hker).choose_spec
    refine ⟨(adj.homEquiv N Z).symm d, ?_⟩
    apply (adj.homEquiv M Z).injective
    rwa [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  let e := (cokernelIsCokernel P.ι).coconePointUniqueUpToIso hc
  exact ⟨e, (cokernelIsCokernel P.ι).comp_coconePointUniqueUpToIso_hom hc
    WalkingParallelPair.one⟩

/-- `affineTilde` carries a finite module over a Noetherian ring of global sections to a coherent
sheaf. -/
public theorem affineTilde_coherent (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (M : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M] :
    ((affineTilde X).obj M).IsCoherent := by
  have hloc : IsLocallyNoetherian X := isLocallyNoetherian_of_isNoetherianRing_top X
  have hft : ((affineTilde X).obj M).IsFiniteType :=
    isFiniteType_restrict X.isoSpec.hom (tilde M)
      ((AlgebraicGeometry.tilde_isFiniteType_iff M).mpr inferInstance)
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X
    ((affineTilde X).obj M)).out 1 2 (h₁ := rfl) (h₂ := rfl)).mpr
      ⟨affineTilde_quasicoherent X M, hft⟩

end Stacks.Coherent

end
