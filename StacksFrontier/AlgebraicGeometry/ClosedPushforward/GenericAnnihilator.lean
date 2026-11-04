module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.IdealAnnihilatorQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The annihilator of the ideal sheaf near the generic point of an integral closed subscheme

Let `i : Z ⟶ X` be a closed immersion with `Z` integral, let `ξ` be the generic point of `Z`,
and let `ℱ` be a coherent `𝒪_X`-module whose stalk at `i ξ` is annihilated by the maximal ideal
of the local ring `𝒪_{X, i ξ}`. The subsheaf `𝒜 ⊆ ℱ` of sections annihilated by the ideal sheaf
`ℐ = ker(i^♯)` is then coherent, is annihilated by `ℐ` by construction, and the inclusion
`𝒜 ⟶ ℱ` is an isomorphism over an open neighbourhood of `i ξ`.

This is the geometric input of [Stacks, Tag 01YE]: it replaces `ℱ` near `i ξ` by a module that
is annihilated by `ℐ`, hence by [Stacks, Tag 087T] a direct image from `Z`, which is what makes
the dévissage of a coherent module along an integral closed subscheme start.

## Main definitions

* `Stacks.ClosedImmersion.StalkKilledByMaximalIdeal`: the stalk of a module at a point is
  annihilated by the maximal ideal of the local ring at that point. This is the hypothesis of
  [Stacks, Tag 01YE].

## Main results

* `Stacks.ClosedImmersion.exists_coherent_annihilator_submodule_isIso_near`: under that
  hypothesis at the generic point of an integral closed subscheme, the annihilator subsheaf of
  the ideal sheaf is a coherent submodule of `ℱ`, annihilated by the ideal sheaf, whose
  inclusion is invertible after restriction to a neighbourhood of `i ξ`. The proof needs `X`
  only locally Noetherian, which is
  `Stacks.ClosedImmersion.exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian`.

## Implementation notes

The ideal sheaf is realised as `kernel (SheafOfModules.unitToPushforwardObjUnit
i.toRingCatSheafHom)`, which is `Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom` written
in the category `X.Modules` rather than in modules over the structure sheaf of the underlying
ringed space; this is the spelling for which
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf` and the annihilator
API of [Stacks, Tag 01PO] both apply without transporting along an identification of ring
sheaves.

The annihilator subsheaf itself is `AlgebraicGeometry.annihilatorSubsheaf`, and the three facts
about it that the argument needs are [Stacks, Tag 01PO]: its sections over an affine open are
exactly those killed by the sections of `ℐ` over that open, it is quasi-coherent, and its germs
at a point are exactly the germs of `ℱ` killed by the germs of `ℐ`. The hypothesis on the stalk
enters only through that last description, via the identification of the kernel of
`𝒪_{X, i ξ} ⟶ 𝒪_{Z, ξ}` with the maximal ideal: `Z` is integral and `ξ` is its generic point,
so `𝒪_{Z, ξ}` is the function field of `Z`, hence a field, and the kernel of a surjection onto
a field from a local ring is its maximal ideal.

Invertibility near `i ξ` comes from [Stacks, Tag 01Y3]: the inclusion is injective on every
stalk, and surjective on the stalk at `i ξ` exactly by the hypothesis, so it is an isomorphism
after restriction to a neighbourhood. Tag 01Y3 is stated with `SheafOfModules.Hom.over`, while
the conclusion here is stated with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`; the two
restrictions are identified by `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, which is the
content of `isIso_restrictFunctor_map_of_isIso_over` below. Tag 01Y3 also phrases the stalk
hypothesis with `PresheafOfModules.toPresheaf` where the annihilator API of Tag 01PO uses
`AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf`; the two agree definitionally, and
`isIso_stalkFunctor_map_val_of_bijective` isolates that identification so that no other proof
pays for it.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE
open Stacks.AlgebraicGeometry.CoherentKernel
open Stacks.AlgebraicGeometry.CoherentOfFiniteType

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-- The stalk of `F` at `x` is annihilated by the maximal ideal of the local ring at `x`.

This is the hypothesis of [Stacks, Tag 01YE] on the coherent module being devissaged. -/
def StalkKilledByMaximalIdeal (F : X.Modules) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  ∀ a : X.presheaf.stalk x, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
    ∀ s : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x, a • s = 0

/-! ### The local ring at the generic point of an integral scheme -/

/-- The local ring of an integral scheme at its generic point is a field: it is the function
field of the scheme. -/
@[ega "I 8.2.1" "partial", ega "IV 8.1.2" "partial"]
private theorem isField_stalk_of_isGenericPoint [AlgebraicGeometry.IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) : IsField (Z.presheaf.stalk ξ) := by
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  rw [hξ.eq (genericPoint_spec Z)]
  exact Field.toIsField Z.functionField

/-- The maximal ideal of the local ring of an integral scheme at its generic point is zero,
that local ring being a field. -/
private theorem maximalIdeal_stalk_eq_bot_of_isGenericPoint [AlgebraicGeometry.IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    IsLocalRing.maximalIdeal (Z.presheaf.stalk ξ) = ⊥ :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mp (isField_stalk_of_isGenericPoint ξ hξ)

/-- A closed immersion is surjective on stalks. Stated separately because elaborating the
instance that supplies it expands through the stalk colimits of the structure sheaves. -/
private theorem surjective_stalkMap (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (ξ : Z) :
    Function.Surjective (i.stalkMap ξ).hom :=
  i.stalkMap_surjective ξ

/-- The kernel of the map of local rings induced by a closed immersion of an integral scheme,
at the generic point, is the maximal ideal: the target is a field, so the kernel is a maximal
ideal of a local ring. -/
private theorem ker_stalkMap_eq_maximalIdeal [AlgebraicGeometry.IsIntegral Z] (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    RingHom.ker (i.stalkMap ξ).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i ξ)) := by
  have hbot : (⊥ : Ideal (Z.presheaf.stalk ξ)).IsMaximal := by
    rw [← maximalIdeal_stalk_eq_bot_of_isGenericPoint ξ hξ]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hkerMax : (RingHom.ker (i.stalkMap ξ).hom).IsMaximal := by
    change (Ideal.comap (i.stalkMap ξ).hom (⊥ : Ideal (Z.presheaf.stalk ξ))).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective _ (surjective_stalkMap i ξ) (K := ⊥) (H := hbot)
  exact IsLocalRing.eq_maximalIdeal hkerMax

/-- The germ at `i ξ` of a function killed by the comorphism of a closed immersion lies in the
maximal ideal of `𝒪_{X, i ξ}`, when `Z` is integral with generic point `ξ`. -/
private theorem germ_mem_maximalIdeal_of_app_eq_zero [AlgebraicGeometry.IsIntegral Z]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (U : X.Opens) (hx : i ξ ∈ U) (a : Γ(X, U))
    (ha : (i.app U).hom a = 0) :
    X.presheaf.germ U (i ξ) hx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i ξ)) := by
  rw [← ker_stalkMap_eq_maximalIdeal i ξ hξ, RingHom.mem_ker]
  let cStalk := (TopCat.Presheaf.stalkFunctor CommRingCat (i ξ)).map i.toLRSHom.c
  let stPush := Z.presheaf.stalkPushforward CommRingCat i.base ξ
  have hgerm : cStalk.hom (X.presheaf.germ U (i ξ) hx a) =
      TopCat.Presheaf.germ (i.base _* Z.presheaf) U (i ξ) hx ((i.app U).hom a) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U (i ξ) hx i.toLRSHom.c a
  change stPush.hom (cStalk.hom (X.presheaf.germ U (i ξ) hx a)) = 0
  rw [hgerm, ha]
  simp

/-- Taking germs is `𝒪_X`-linear: the germ of `r • s` is the germ of `r` acting on the germ
of `s`. This is `PresheafOfModules.germ_smul` with the module structure on the stalk spelled the
way `StalkKilledByMaximalIdeal` spells it. -/
private theorem germ_smul_stalk (G : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (s : Γ(G, U)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    (ConcreteCategory.hom (TopCat.Presheaf.germ G.val.presheaf U x hx)) (r • s) =
      (ConcreteCategory.hom (X.presheaf.germ U x hx)) r •
        (ConcreteCategory.hom (TopCat.Presheaf.germ G.val.presheaf U x hx)) s := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
  exact PresheafOfModules.germ_smul G.val x U hx r s

/-! ### Lifting a section through a kernel -/

/-- A section of `F` over `U` killed by `f : F ⟶ G` is the image of a section of `kernel f`
over `U`: kernels of sheaves of modules are computed section by section. -/
private theorem kernel_section_lift {F G : X.Modules} (f : F ⟶ G) (U : X.Opens)
    (a : F.val.obj (op U)) (ha : (f.val.app (op U)).hom a = 0) :
    ∃ b : (kernel f).val.obj (op U), (kernel.ι f).val.app (op U) b = a := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : E.Additive := { map_add := by intros; rfl }
  let fU := E.map f
  let b : fU.hom.ker := ⟨a, ha⟩
  let e := PreservesKernel.iso E f ≪≫ ModuleCat.kernelIsoKer fU
  refine ⟨e.inv b, ?_⟩
  have hα : (PreservesKernel.iso E f).inv ≫ E.map (kernel.ι f) = kernel.ι (E.map f) :=
    PreservesKernel.iso_inv_ι (G := E) (f := f)
  have he : e.inv ≫ E.map (kernel.ι f) = ModuleCat.ofHom fU.hom.ker.subtype := by
    calc
      e.inv ≫ E.map (kernel.ι f) =
          (ModuleCat.kernelIsoKer fU).inv ≫
            ((PreservesKernel.iso E f).inv ≫ E.map (kernel.ι f)) := by
        simp [e, Category.assoc]
      _ = (ModuleCat.kernelIsoKer fU).inv ≫ kernel.ι fU := by rw [hα]
      _ = ModuleCat.ofHom fU.hom.ker.subtype := ModuleCat.kernelIsoKer_inv_kernel_ι fU
  exact congrArg (fun g => g.hom b) he

/-- The inclusion of a kernel is a monomorphism, being the inclusion of a limit fork.

The library carries no instance for `Mono (kernel.ι f)`, and a form general enough to be
registered as one is not usable here: with the category a variable, instance search can no
longer discharge its own `HasZeroMorphisms` side condition. Every consumer below therefore
receives this proof as an explicit instance argument. -/
private theorem mono_kernel_ι {F G : X.Modules} (f : F ⟶ G) : Mono (kernel.ι f) := by
  have hfork : Mono (Fork.ι (Fork.ofι (kernel.ι f)
      ((kernel.condition f).trans comp_zero.symm))) :=
    Fork.IsLimit.mono (kernelIsKernel f)
  exact hfork

/-! ### Restriction to an open, in the two spellings -/

/-- A morphism of `𝒪_X`-modules whose restriction to `U` in the slice-category sense
`SheafOfModules.Hom.over` is invertible is invertible after restriction along `U.ι`.

The two restrictions agree up to the natural isomorphism
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. -/
private theorem isIso_restrictFunctor_map_of_isIso_over (U : X.Opens) {F G : X.Modules}
    (f : F ⟶ G) (h : IsIso (f.over U)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let E := Scheme.Modules.overEquiv U
  let η := Scheme.Modules.overFunctorEquiv U
  let eF := η.app F
  let eG := η.app G
  have hnat : E.functor.map (f.over U) ≫ eG.hom =
      eF.hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f := η.hom.naturality f
  have : IsIso (E.functor.map (f.over U)) := Functor.map_isIso _ (f.over U)
  have heq : eF.inv ≫ E.functor.map (f.over U) ≫ eG.hom =
      (Scheme.Modules.restrictFunctor U.ι).map f := by
    rw [hnat, Iso.inv_hom_id_assoc]
  rw [← heq]
  infer_instance

/-- The hypothesis of [Stacks, Tag 01Y3] is bijectivity of the map of stalks of the underlying
presheaves of abelian groups. This records that it may be checked in the
`AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf` spelling used by the annihilator API of
[Stacks, Tag 01PO]. -/
private theorem isIso_stalkFunctor_map_val_of_bijective {F G : X.Modules} (φ : F ⟶ G) (x : X)
    (h : Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf φ))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 h

/-! ### The annihilator subsheaf of the ideal sheaf -/

/-- The comorphism of `i` as a morphism of `𝒪_X`-modules `𝒪_X ⟶ i_*𝒪_Z`. Its kernel is the
ideal sheaf `ℐ = ker(i^♯)` cutting out the closed subscheme, written as an object of
`X.Modules`; that kernel is `Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom`. -/
private abbrev unitComorphism (i : Z ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- The annihilator of the ideal sheaf `ℐ = ker(i^♯)` inside `F`: the largest submodule of `F`
all of whose sections are killed by the sections of `ℐ` over the same open. This is the
submodule produced by [Stacks, Tag 01PO]. -/
private abbrev kerAnnihilator (i : Z ⟶ X) (F : X.Modules) : F.Submodule :=
  @AlgebraicGeometry.annihilatorSubsheaf X (kernel (unitComorphism i)) F
    (kernel.ι (unitComorphism i)) (mono_kernel_ι _)

/-- The ideal sheaf of a closed immersion is quasi-coherent, which is one assertion of
[Stacks, Tag 01QO]. -/
private theorem isQuasicoherent_kernel_unitComorphism (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    (kernel (unitComorphism i)).IsQuasicoherent :=
  isQuasicoherent_idealSheaf i

/-- A section of the ideal sheaf over `U`, read as a function on `U`. -/
private abbrev idealSection (i : Z ⟶ X) (U : X.Opens)
    (r : Γ(kernel (unitComorphism i), U)) : Γ(X, U) :=
  Scheme.Modules.Hom.app (X := X) (kernel.ι (unitComorphism i)) U r

/-- Every section of the ideal sheaf is killed by the comorphism of `i`, by the defining
property of a kernel. -/
private theorem app_idealSection_eq_zero (i : Z ⟶ X) (U : X.Opens)
    (r : Γ(kernel (unitComorphism i), U)) : (i.app U).hom (idealSection i U r) = 0 :=
  congrArg (fun f => (f.val.app (op U)).hom r) (kernel.condition (unitComorphism i))

/-- The inclusion of a submodule is injective on every stalk, being injective on sections over
every open. -/
private theorem injective_stalk_submodule_ι (F : X.Modules) (A : F.Submodule) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf A.ι)) :=
  TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (fun _ _ _ h => Subtype.ext h) x

/-- The ideal sheaf of a closed immersion into a locally Noetherian scheme is of finite type: it
is a quasi-coherent submodule of the structure sheaf, which is coherent by [Stacks, Tag 01XZ]. -/
private theorem isFiniteType_kernel_unitComorphism_of_isLocallyNoetherian (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X] :
    (kernel (unitComorphism i)).IsFiniteType :=
  @isFiniteType_of_mono_of_isQuasicoherent X inferInstance (kernel (unitComorphism i))
    (SheafOfModules.unit X.ringCatSheaf) (isQuasicoherent_kernel_unitComorphism i)
    (_root_.isQuasicoherent_of_isCoherent _)
    (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _
      (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X))
    (kernel.ι (unitComorphism i)) (mono_kernel_ι _)

/-- The annihilator subsheaf is quasi-coherent, which is [Stacks, Tag 01PO] part (1). -/
private theorem isQuasicoherent_kerAnnihilator_of_isLocallyNoetherian (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules)
    [F.IsCoherent] : (kerAnnihilator i F).toSheafOfModules.IsQuasicoherent :=
  @AlgebraicGeometry.annihilatorSubsheaf_isQuasicoherent X (kernel (unitComorphism i)) F
    (kernel.ι (unitComorphism i)) (mono_kernel_ι _) (isQuasicoherent_kernel_unitComorphism i)
    (isFiniteType_kernel_unitComorphism_of_isLocallyNoetherian i)
    (_root_.isQuasicoherent_of_isCoherent F)

/-- The annihilator subsheaf is coherent: it is a quasi-coherent submodule of a coherent module
on a locally Noetherian scheme, so [Stacks, Tag 01Y1] applies. -/
private theorem isCoherent_kerAnnihilator_of_isLocallyNoetherian (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules)
    [F.IsCoherent] : (kerAnnihilator i F).toSheafOfModules.IsCoherent :=
  Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule F
    (kerAnnihilator i F) (isQuasicoherent_kerAnnihilator_of_isLocallyNoetherian i F)

/-- The annihilator subsheaf is annihilated by the ideal sheaf cutting out `Z`. Annihilation is
tested on the affine opens by `Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal`, where it
suffices to use the sections of the ideal over the open itself by [Stacks, Tag 01PO] part (2);
and a function in the ideal of the affine open is exactly one killed by the comorphism, hence
the image of a section of the ideal sheaf. -/
private theorem annihilatedByKer_kerAnnihilator_of_isLocallyNoetherian (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules)
    [F.IsCoherent] : AnnihilatedByKer i (kerAnnihilator i F).toSheafOfModules := by
  rw [annihilatedByKer_iff_ker_ideal]
  intro U a ha m
  have ha' : (i.app U.1).hom a = 0 := RingHom.mem_ker.mp (i.ideal_ker_le U ha)
  have hq : ((unitComorphism i).val.app (op U.1)).hom a = 0 := ha'
  obtain ⟨b, hb⟩ := kernel_section_lift (unitComorphism i) U.1 a hq
  set mF : Γ(F, U.1) :=
    Scheme.Modules.Hom.app (X := X) (kerAnnihilator i F).ι U.1 m
  have hz := (@AlgebraicGeometry.mem_annihilatorSubsheaf_iff_of_isAffine X
    (kernel (unitComorphism i)) F (kernel.ι (unitComorphism i)) (mono_kernel_ι _)
    (isQuasicoherent_kernel_unitComorphism i) U mF).mp m.property b
  refine Subtype.ext ?_
  change (show Γ(X, U.1) from a) • mF = 0
  rwa [← hb]

/-- The inclusion of the annihilator subsheaf is surjective on the stalk at `i ξ`. By
[Stacks, Tag 01PO] part (3) a germ of `F` at `i ξ` is a germ of the annihilator exactly when
every germ of the ideal sheaf kills it; and a germ of the ideal sheaf lies in the maximal ideal
of `𝒪_{X, i ξ}`, which kills the whole stalk of `F` by hypothesis. -/
private theorem surjective_stalk_kerAnnihilator_of_isLocallyNoetherian
    [AlgebraicGeometry.IsIntegral Z] (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (F : X.Modules) [F.IsCoherent]
    (hF : StalkKilledByMaximalIdeal F (i ξ)) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab.{u} (i ξ)).map
      (Scheme.Modules.Hom.mapPresheaf (kerAnnihilator i F).ι)) := by
  intro s
  refine (@AlgebraicGeometry.mem_range_stalk_annihilatorSubsheaf_iff X
    (kernel (unitComorphism i)) F (kernel.ι (unitComorphism i)) (mono_kernel_ι _)
    (isQuasicoherent_kernel_unitComorphism i)
    (isFiniteType_kernel_unitComorphism_of_isLocallyNoetherian i)
    (_root_.isQuasicoherent_of_isCoherent F) (i ξ) s).2 ?_
  intro U hx t _ r
  exact (germ_smul_stalk F (i ξ) U hx (idealSection i U r) t).trans
    (hF _ (germ_mem_maximalIdeal_of_app_eq_zero i ξ hξ U hx (idealSection i U r)
      (app_idealSection_eq_zero i U r)) (TopCat.Presheaf.germ F.val.presheaf U (i ξ) hx t))

/-! ### The main result -/

/-- **[Stacks, Tag 01YE], the integral case, over a locally Noetherian scheme.** Let `i : Z ⟶ X` be
a closed immersion into a locally Noetherian scheme with `Z` integral, let `ξ` be the generic point
of `Z`, and let `F` be a coherent `𝒪_X`-module whose stalk at `i ξ` is annihilated by the maximal
ideal of `𝒪_{X, i ξ}`. Then there is a coherent submodule `A ⊆ F`, annihilated by the ideal sheaf
cutting out `Z`, whose inclusion becomes an isomorphism after restriction to some open
neighbourhood of `i ξ`.

The submodule is the annihilator of the ideal sheaf inside `F`; it is annihilated by the ideal
sheaf by construction, and the hypothesis on the stalk is exactly what makes its inclusion
bijective on the stalk at `i ξ`, hence an isomorphism near `i ξ` by [Stacks, Tag 01Y3]. -/
theorem exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z))
    (F : X.Modules) [F.IsCoherent] (hF : StalkKilledByMaximalIdeal F (i ξ)) :
    ∃ A : F.Submodule, A.toSheafOfModules.IsCoherent ∧
      AnnihilatedByKer i A.toSheafOfModules ∧
      ∃ U : X.Opens, i ξ ∈ U ∧
        IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map A.ι) := by
  have hAcoh : (kerAnnihilator i F).toSheafOfModules.IsCoherent :=
    isCoherent_kerAnnihilator_of_isLocallyNoetherian i F
  have hstalk := isIso_stalkFunctor_map_val_of_bijective (kerAnnihilator i F).ι (i ξ)
    ⟨injective_stalk_submodule_ι F (kerAnnihilator i F) (i ξ),
      surjective_stalk_kerAnnihilator_of_isLocallyNoetherian i ξ hξ F hF⟩
  obtain ⟨U, hU, hiso⟩ :=
    @AlgebraicGeometry.exists_isIso_over_of_stalk_isIso _ _ F
      (kerAnnihilator i F).toSheafOfModules inferInstance
      (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ hAcoh)
      (kerAnnihilator i F).ι (i ξ) hstalk
  exact ⟨kerAnnihilator i F, hAcoh, annihilatedByKer_kerAnnihilator_of_isLocallyNoetherian i F,
    U, hU, isIso_restrictFunctor_map_of_isIso_over U (kerAnnihilator i F).ι hiso⟩

/-- **[Stacks, Tag 01YE], the integral case.** Let `i : Z ⟶ X` be a closed immersion into a
Noetherian scheme with `Z` integral, let `ξ` be the generic point of `Z`, and let `F` be a
coherent `𝒪_X`-module whose stalk at `i ξ` is annihilated by the maximal ideal of
`𝒪_{X, i ξ}`. Then there is a coherent submodule `A ⊆ F`, annihilated by the ideal sheaf
cutting out `Z`, whose inclusion becomes an isomorphism after restriction to some open
neighbourhood of `i ξ`.

The submodule is the annihilator of the ideal sheaf inside `F`; it is annihilated by the ideal
sheaf by construction, and the hypothesis on the stalk is exactly what makes its inclusion
bijective on the stalk at `i ξ`, hence an isomorphism near `i ξ` by [Stacks, Tag 01Y3]. -/
theorem exists_coherent_annihilator_submodule_isIso_near [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z))
    (F : X.Modules) [F.IsCoherent] (hF : StalkKilledByMaximalIdeal F (i ξ)) :
    ∃ A : F.Submodule, A.toSheafOfModules.IsCoherent ∧
      AnnihilatedByKer i A.toSheafOfModules ∧
      ∃ U : X.Opens, i ξ ∈ U ∧
        IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map A.ι) :=
  exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian i ξ hξ F hF

end Stacks.ClosedImmersion

end
