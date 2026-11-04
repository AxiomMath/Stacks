module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.Annihilator

/-!
# Modules over a quotient of the structure sheaf

Let `F` be a sheaf of modules on a ringed space `X` and let `I ⊆ 𝒪_X` be an ideal subsheaf
contained in the annihilator of `F`. Then the `𝒪_X`-action on `F` descends to an action of the
quotient sheaf of rings `𝒪_X/I`, this is the only such action restricting to the given one, and
on stalks it is the ordinary action of `𝒪_{X,x}/I_x` on `F_x`.

## Main definitions

* `Stacks.SheafOfModules.quotientRingSheaf`: the quotient sheaf of rings `𝒪_X/I`, packaged with
  its locally surjective quotient map and the identification of `I` as the sectionwise kernel.
* `Stacks.SheafOfModules.quotientRingSheafModule`: the descended `𝒪_X/I`-module.
* `Stacks.SheafOfModules.quotientRingSheafStalkIdealEquiv`: the canonical identification
  `𝒪_{X,x}/I_x ≃+* (𝒪_X/I)_x`.
* `Stacks.SheafOfModules.quotientStalkSMul`: the descended action on the stalk of `F`.

## Main results

* `Stacks.SheafOfModules.quotientRingSheafModule_restrictScalars` and
  `Stacks.SheafOfModules.quotientRingSheafModule_unique`: restricting the descended action along
  the quotient map returns `F`, and that property determines the descended module.
* `Stacks.SheafOfModules.mem_idealSheafStalk_iff`: the kernel of the quotient map on stalks
  consists exactly of the germs of local sections of `I`.
* `Stacks.SheafOfModules.quotientRingSheafModule_stalk_smul`: on stalks the descended action is
  the ordinary action of a quotient ring on a module killed by the ideal.

## Implementation notes

The descent itself is `Stacks.SheafOfModules.ChangeOfRings.liftedSheaf`, which lifts the action
along any locally surjective map of sheaves of rings whose sectionwise kernel annihilates the
module. Because that construction leaves the underlying presheaf of abelian groups untouched, the
compatibility with the original action is an equality of sheaves of modules rather than merely an
isomorphism, and the stalk statement needs no transport along an identification of stalks.

The stalk of `F` and the stalk of the descended module are the same abelian group, but the two
scalar actions are indexed by different base sheaves, so the one coming from the descended module
is named `quotientStalkSMul` in order to state their comparison. The stalk results fix the module
universe to that of the space, which is where `TopCat.Presheaf.stalk` is available.

## References

* [Stacks Project, Tag 0H2K](https://stacks.math.columbia.edu/tag/0H2K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u v

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing SheafedSpace.sheaf sheafCompose
  ModuleCat.restrictScalars

variable (X : RingedSpace.{u, u}) (I : (SheafOfModules.unit (structureSheafRing X)).Submodule)

/-! ### The quotient of the structure sheaf by an ideal subsheaf -/

/-- The ideal of sections over `U` cut out by an ideal subsheaf of the structure sheaf. -/
noncomputable abbrev sectionIdeal (U : (Opens X.carrier)ᵒᵖ) : Ideal (X.presheaf.obj U) :=
  I.toSubmodule.obj U

/-- Restriction maps the sections of an ideal subsheaf into the sections over a smaller open. -/
theorem sectionIdeal_map {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    sectionIdeal X I U ≤ (sectionIdeal X I V).comap (X.presheaf.map f).hom :=
  fun _ ha => I.toSubmodule.map_mem f ha

/-- The sectionwise quotient `U ↦ 𝒪_X(U)/I(U)`, a presheaf of commutative rings. -/
noncomputable def quotientCommRingPresheaf : (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (X.presheaf.obj U ⧸ sectionIdeal X I U)
  map f := CommRingCat.ofHom (Ideal.quotientMap _ (X.presheaf.map f).hom (sectionIdeal_map X I f))
  map_id U := by
    ext a
    simp
  map_comp f g := by
    ext a
    simp

/-- The sectionwise quotient `U ↦ 𝒪_X(U)/I(U)`, read as a presheaf of not necessarily
commutative rings, which is the form the sheaf-of-modules API takes as its base. -/
noncomputable abbrev quotientRingPresheaf : (Opens X.carrier)ᵒᵖ ⥤ RingCat.{u} :=
  quotientCommRingPresheaf X I ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The sectionwise quotient map `𝒪_X → 𝒪_X/I`. -/
noncomputable def toQuotientCommRingPresheaf : X.presheaf ⟶ quotientCommRingPresheaf X I where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal X I U))
  naturality _ _ f :=
    CommRingCat.hom_ext (Ideal.quotientMap_comp_mk (sectionIdeal_map X I f)).symm

/-- The sheaf of rings `𝒪_X/I`, obtained by sheafifying the sectionwise quotients. -/
noncomputable def quotientRingSheafification :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}).obj
    (quotientRingPresheaf X I)

/-- A presentation of the quotient of the structure sheaf by an ideal subsheaf `I`: a sheaf of
rings together with a locally surjective map from `𝒪_X` whose sectionwise kernel is `I`. -/
structure QuotientRingSheaf where
  /-- The quotient sheaf of rings. -/
  sheaf : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}
  /-- The quotient map. -/
  quotientMap : structureSheafRing X ⟶ sheaf
  /-- The quotient map is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective
    (Opens.grothendieckTopology X.carrier) quotientMap.hom
  /-- The ideal subsheaf is exactly the sectionwise kernel of the quotient map. -/
  ker_eq (U : (Opens X.carrier)ᵒᵖ) (r : (structureSheafRing X).obj.obj U) :
    quotientMap.hom.app U r = 0 ↔ r ∈ I.toSubmodule.obj U

/-- The quotient of the structure sheaf by an ideal subsheaf, presented by the sheafification of
the sectionwise quotients. -/
noncomputable def quotientRingSheaf : QuotientRingSheaf X I := by
  let q₀ : X.presheaf ⋙ forget₂ CommRingCat RingCat ⟶ quotientRingPresheaf X I :=
    Functor.whiskerRight (toQuotientCommRingPresheaf X I) (forget₂ CommRingCat RingCat)
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier)
    (quotientRingPresheaf X I)
  have hq₀ (U : (Opens X.carrier)ᵒᵖ) (r : (structureSheafRing X).obj.obj U) :
      q₀.app U r = Ideal.Quotient.mk (sectionIdeal X I U) r := rfl
  refine ⟨quotientRingSheafification X I, ⟨q₀ ≫ η⟩, ?_, ?_⟩
  · have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) q₀ :=
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ y => Ideal.Quotient.mk_surjective y)
    have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) η := by
      dsimp only [η]; infer_instance
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) (q₀ ≫ η)
    infer_instance
  · intro U r
    change η.app U (q₀.app U r) = 0 ↔ r ∈ I.toSubmodule.obj U
    constructor
    · intro h
      have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier) η := by
        dsimp only [η]; infer_instance
      have hS : Presheaf.equalizerSieve (q₀.app U r) 0 ∈
          Opens.grothendieckTopology X.carrier U.unop :=
        Presheaf.equalizerSieve_mem _ η (q₀.app U r) 0 (by simpa using h)
      refine I.isSheaf r ((Opens.grothendieckTopology X.carrier).superset_covering
        (fun V f hf => ?_) hS)
      have hs : q₀.app (op V) ((structureSheafRing X).obj.map f.op r) = 0 := by
        have hmap : ((structureSheafRing X).obj.map f.op).hom r =
            ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map f.op).hom r := rfl
        rw [hmap, NatTrans.naturality_apply q₀ f.op r, hf, map_zero]
      change (structureSheafRing X).obj.map f.op r ∈ I.toSubmodule.obj (op V)
      rw [hq₀] at hs
      exact (Submodule.Quotient.mk_eq_zero _).mp hs
    · intro hr
      have hz : q₀.app U r = 0 := (Submodule.Quotient.mk_eq_zero _).2 hr
      rw [hz, map_zero]

/-- The quotient map onto `𝒪_X/I` is locally surjective. -/
instance quotientMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (quotientRingSheaf X I).quotientMap.hom :=
  (quotientRingSheaf X I).locallySurjective

/-! ### The descended module structure -/

section Descent

variable (F : SheafOfModules.{v} (structureSheafRing X))

/-- The sectionwise kernel of the quotient map annihilates a module annihilated by `I`. -/
theorem smul_eq_zero_of_mem_ker_quotientMap (hI : I ≤ annihilatorSheaf X F)
    (U : (Opens X.carrier)ᵒᵖ) (a : (structureSheafRing X).obj.obj U)
    (ha : a ∈ RingHom.ker ((quotientRingSheaf X I).quotientMap.hom.app U).hom)
    (m : F.val.obj U) : a • m = 0 := by
  have haI : a ∈ I.toSubmodule.obj U :=
    ((quotientRingSheaf X I).ker_eq U a).mp (RingHom.mem_ker.mp ha)
  simpa using (mem_annihilatorSheaf_iff X F U a).mp (hI U haI) U (𝟙 U) m

/-- **Stacks Project, Tag 0H2K.** The canonical `𝒪_X/I`-module structure on a sheaf of modules
annihilated by the ideal subsheaf `I`: its underlying presheaf of abelian groups is that of `F`,
and a local section of `𝒪_X/I` acts through any local lift of it to `𝒪_X`. -/
@[stacks 0H2K "the descended module structure"]
noncomputable def quotientRingSheafModule (hI : I ≤ annihilatorSheaf X F) :
    SheafOfModules.{v} (quotientRingSheaf X I).sheaf :=
  ChangeOfRings.liftedSheaf (quotientRingSheaf X I).quotientMap F
    (smul_eq_zero_of_mem_ker_quotientMap X I F hI)

/-- Two presheaves of modules with the same sectionwise modules and the same underlying presheaf
of abelian groups are equal. -/
private theorem presheafOfModules_eq_of_obj_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{v} R} (hobj : M.obj = N.obj)
    (hpresheaf : M.presheaf = N.presheaf) : M = N := by
  cases M
  cases N
  dsimp only at hobj
  cases hobj
  congr 1
  funext U V restriction
  apply ModuleCat.hom_ext
  ext element
  exact congrArg (fun morphism => morphism element)
    (eq_of_heq (Functor.hcongr_hom hpresheaf restriction))

/-- Sheaves of modules with equal underlying presheaves of modules are equal. -/
private theorem sheafOfModules_eq_of_val_eq {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.{v} R}
    (h : A.val = B.val) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- A morphism of `ModuleCat` which is the identity on underlying abelian groups identifies its
source and target. -/
private theorem moduleCat_eq_of_forget_eq {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (h : (forget₂ (ModuleCat R) AddCommGrpCat).obj M =
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N) (f : M ⟶ N)
    (hf : (forget₂ (ModuleCat R) AddCommGrpCat).map f = eqToHom h) : M = N := by
  rcases M with ⟨carrier, group, action⟩
  rcases N with ⟨carrier', group', action'⟩
  obtain ⟨htype, hgroup⟩ := AddCommGrpCat.mk.inj h
  cases htype
  cases eq_of_heq hgroup
  rename_i group sourceAction targetAction
  have hf_apply (element : carrier) : f element = element := by
    simpa using congrArg (fun morphism => morphism element) hf
  obtain rfl := Module.ext' sourceAction targetAction fun scalar element => by
    have hmap := @LinearMap.map_smul _ _ _ _ _ _ sourceAction targetAction f.hom scalar element
    rwa [hf_apply, hf_apply] at hmap
  rfl

/-- **Stacks Project, Tag 0H2K.** The descended action is compatible with the given one:
restricting scalars along the quotient map returns `F`. -/
@[stacks 0H2K "compatibility with the given action"]
theorem quotientRingSheafModule_restrictScalars (hI : I ≤ annihilatorSheaf X F) :
    (SheafOfModules.restrictScalars (quotientRingSheaf X I).quotientMap).obj
      (quotientRingSheafModule X I F hI) = F := by
  have hobj : ((SheafOfModules.restrictScalars
      (quotientRingSheaf X I).quotientMap).obj (quotientRingSheafModule X I F hI)).val.obj =
      F.val.obj := by
    funext U
    exact congrArg (fun P => @ModuleCat.of _ _ _ _ P) (Module.ext' _ _ fun r m =>
      ChangeOfRings.liftedSMul_app (quotientRingSheaf X I).quotientMap F
        (smul_eq_zero_of_mem_ker_quotientMap X I F hI) r m)
  exact sheafOfModules_eq_of_val_eq (presheafOfModules_eq_of_obj_eq hobj rfl)

/-- **Stacks Project, Tag 0H2K.** The descended action is the only `𝒪_X/I`-action whose
restriction of scalars along the quotient map is the given `𝒪_X`-action. -/
@[stacks 0H2K "uniqueness of the descended action"]
theorem quotientRingSheafModule_unique (hI : I ≤ annihilatorSheaf X F)
    (G : SheafOfModules.{v} (quotientRingSheaf X I).sheaf)
    (hG : (SheafOfModules.restrictScalars (quotientRingSheaf X I).quotientMap).obj G = F) :
    G = quotientRingSheafModule X I F hI := by
  set H := quotientRingSheafModule X I F hI
  have hv : (((SheafOfModules.restrictScalars
        (quotientRingSheaf X I).quotientMap).obj G).val) =
      (((SheafOfModules.restrictScalars (quotientRingSheaf X I).quotientMap).obj H).val) :=
    congrArg SheafOfModules.val
      (hG.trans (quotientRingSheafModule_restrictScalars X I F hI).symm)
  have hpresheaf : G.val.presheaf = H.val.presheaf :=
    congrArg (fun M : PresheafOfModules (structureSheafRing X).obj => M.presheaf) hv
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (α := (quotientRingSheaf X I).quotientMap.hom) (M₁ := G.val) (M₂ := H.val) H.isSheaf
  let lift : G.val ⟶ H.val := e.symm (eqToHom hv)
  have hlift_presheaf :
      (PresheafOfModules.toPresheaf (quotientRingSheaf X I).sheaf.obj).map lift =
        eqToHom hpresheaf := by
    have hlift := e.apply_symm_apply (eqToHom hv)
    change (PresheafOfModules.restrictScalars
      (quotientRingSheaf X I).quotientMap.hom).map lift = eqToHom hv at hlift
    have h1 : (PresheafOfModules.toPresheaf (quotientRingSheaf X I).sheaf.obj).map lift =
        (PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
          ((PresheafOfModules.restrictScalars
            (quotientRingSheaf X I).quotientMap.hom).map lift) := rfl
    rw [h1, hlift]
    exact eqToHom_map (PresheafOfModules.toPresheaf (structureSheafRing X).obj) hv
  have hobj : G.val.obj = H.val.obj := by
    funext U
    refine moduleCat_eq_of_forget_eq (congrArg (fun P => P.obj U) hpresheaf) (lift.app U) ?_
    have h := congrArg (fun morphism => morphism.app U) hlift_presheaf
    rwa [eqToHom_app] at h
  exact sheafOfModules_eq_of_val_eq (presheafOfModules_eq_of_obj_eq hobj hpresheaf)

end Descent

/-! ### Behaviour on stalks -/

/-- The quotient map is surjective on stalks. -/
theorem quotientRingSheaf_stalkMap_surjective (x : X.carrier) :
    Function.Surjective (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor RingCat x).map
      (quotientRingSheaf X I).quotientMap.hom)) :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    (quotientRingSheaf X I).quotientMap.hom).mp
      (quotientRingSheaf X I).locallySurjective x

/-- The stalk at `x` of the ideal subsheaf, presented as the kernel of the quotient map on
stalks. -/
noncomputable abbrev idealSheafStalk (x : X.carrier) :
    Ideal (TopCat.Presheaf.stalk (C := RingCat) (structureSheafRing X).obj x) :=
  RingHom.ker (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor RingCat x).map
    (quotientRingSheaf X I).quotientMap.hom))

/-- The stalk of an ideal subsheaf is a two-sided ideal, being the kernel of a ring map. -/
instance idealSheafStalk_isTwoSided (x : X.carrier) : (idealSheafStalk X I x).IsTwoSided :=
  inferInstanceAs (RingHom.ker (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor RingCat x).map
      (quotientRingSheaf X I).quotientMap.hom))).IsTwoSided

/-- The kernel of the quotient map on stalks consists exactly of the germs of local sections of
the ideal subsheaf. -/
theorem mem_idealSheafStalk_iff (x : X.carrier)
    (r : TopCat.Presheaf.stalk (C := RingCat) (structureSheafRing X).obj x) :
    r ∈ idealSheafStalk X I x ↔
      ∃ (U : Opens X.carrier) (hx : x ∈ U) (s : (structureSheafRing X).obj.obj (op U)),
        s ∈ I.toSubmodule.obj (op U) ∧
          TopCat.Presheaf.germ (structureSheafRing X).obj U x hx s = r := by
  constructor
  · intro hr
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (structureSheafRing X).obj r
    have hzero : ((TopCat.Presheaf.stalkFunctor RingCat x).map
        (quotientRingSheaf X I).quotientMap.hom).hom
        (TopCat.Presheaf.germ (structureSheafRing X).obj U x hxU s) = 0 := RingHom.mem_ker.mp hr
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hzero
    have hzero' : TopCat.Presheaf.germ (quotientRingSheaf X I).sheaf.obj U x hxU
        ((quotientRingSheaf X I).quotientMap.hom.app (op U) s) =
        TopCat.Presheaf.germ (quotientRingSheaf X I).sheaf.obj ⊤ x (Opens.mem_top x) 0 := by
      rwa [map_zero]
    obtain ⟨W, hxW, iW, _, heq⟩ := TopCat.Presheaf.germ_eq
      (quotientRingSheaf X I).sheaf.obj x hxU (Opens.mem_top x)
      ((quotientRingSheaf X I).quotientMap.hom.app (op U) s) 0 hzero'
    have hqzero : (quotientRingSheaf X I).quotientMap.hom.app (op W)
        ((structureSheafRing X).obj.map iW.op s) = 0 := by
      rw [← ConcreteCategory.comp_apply,
        (quotientRingSheaf X I).quotientMap.hom.naturality iW.op, ConcreteCategory.comp_apply]
      simpa using heq
    exact ⟨W, hxW, (structureSheafRing X).obj.map iW.op s,
      ((quotientRingSheaf X I).ker_eq (op W) _).mp hqzero,
      TopCat.Presheaf.germ_res_apply (structureSheafRing X).obj iW x hxW s⟩
  · rintro ⟨U, hxU, s, hsI, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor RingCat x).map
        (quotientRingSheaf X I).quotientMap.hom)
      (TopCat.Presheaf.germ (structureSheafRing X).obj U x hxU s) = 0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (quotientRingSheaf X I).quotientMap.hom s,
      ((quotientRingSheaf X I).ker_eq (op U) s).mpr hsI]
    exact map_zero _

/-- The canonical identification of the stalk of `𝒪_X/I` with the quotient of the local ring of
`X` at `x` by the stalk of `I`. -/
noncomputable def quotientRingSheafStalkIdealEquiv (x : X.carrier) :
    (TopCat.Presheaf.stalk (C := RingCat) (structureSheafRing X).obj x ⧸ idealSheafStalk X I x) ≃+*
      TopCat.Presheaf.stalk (C := RingCat) (quotientRingSheaf X I).sheaf.obj x :=
  RingHom.quotientKerEquivOfSurjective (quotientRingSheaf_stalkMap_surjective X I x)

/-- The descended action of the stalk of `𝒪_X/I` on the stalk of `F` at `x`.  The stalk of `F`
and the stalk of the descended module are the same abelian group, and this is the action of the
latter. -/
noncomputable def quotientStalkSMul (F : SheafOfModules.{u} (structureSheafRing X))
    (hI : I ≤ annihilatorSheaf X F) (x : X.carrier)
    (a : TopCat.Presheaf.stalk (C := RingCat) (quotientRingSheaf X I).sheaf.obj x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :
    TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x :=
  a • (show TopCat.Presheaf.stalk (C := Ab.{u})
    (quotientRingSheafModule X I F hI).val.presheaf x from m)

/-- Germ form of the descended action: the image in `𝒪_X/I` of a local section of `𝒪_X` acts on
germs of `F` exactly as that section does. -/
theorem quotientStalkSMul_germ (F : SheafOfModules.{u} (structureSheafRing X))
    (hI : I ≤ annihilatorSheaf X F) (x : X.carrier) (U : Opens X.carrier) (hx : x ∈ U)
    (s : (structureSheafRing X).obj.obj (op U)) (t : F.val.obj (op U)) :
    quotientStalkSMul X I F hI x
        (TopCat.Presheaf.germ (quotientRingSheaf X I).sheaf.obj U x hx
          ((quotientRingSheaf X I).quotientMap.hom.app (op U) s))
        (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx t) =
      TopCat.Presheaf.germ (structureSheafRing X).obj U x hx s •
        TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx t := by
  have hgermQuotient := PresheafOfModules.germ_ringCat_smul
    (quotientRingSheafModule X I F hI).val x U hx
    ((quotientRingSheaf X I).quotientMap.hom.app (op U) s) t
  have hlift := ChangeOfRings.liftedSMul_app (quotientRingSheaf X I).quotientMap F
    (smul_eq_zero_of_mem_ker_quotientMap X I F hI) s t
  have hgerm := PresheafOfModules.germ_ringCat_smul F.val x U hx s t
  exact hgermQuotient.symm.trans
    ((congrArg (ConcreteCategory.hom (TopCat.Presheaf.germ
      (quotientRingSheafModule X I F hI).val.presheaf U x hx)) hlift).trans hgerm)

/-- **Stacks Project, Tag 0H2K.** On stalks the descended action is the ordinary action of the
quotient ring `𝒪_{X,x}/I_x` on the stalk `F_x`, which the stalk of `I` annihilates: the class of a
germ `r` acts on `F_x` exactly as `r` itself. -/
@[stacks 0H2K "the action on stalks"]
theorem quotientRingSheafModule_stalk_smul (F : SheafOfModules.{u} (structureSheafRing X))
    (hI : I ≤ annihilatorSheaf X F) (x : X.carrier)
    (r : TopCat.Presheaf.stalk (C := RingCat) (structureSheafRing X).obj x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :
    quotientStalkSMul X I F hI x
        (quotientRingSheafStalkIdealEquiv X I x
          (Ideal.Quotient.mk (idealSheafStalk X I x) r)) m = r • m := by
  rw [show quotientRingSheafStalkIdealEquiv X I x (Ideal.Quotient.mk (idealSheafStalk X I x) r) =
        ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor RingCat x).map
          (quotientRingSheaf X I).quotientMap.hom) r from
      RingHom.quotientKerEquivOfSurjective_apply_mk
        (quotientRingSheaf_stalkMap_surjective X I x) r]
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (structureSheafRing X).obj r
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply (structureSheafRing X).obj
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hxW s,
      ← TopCat.Presheaf.germ_res_apply F.val.presheaf
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hxW t,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact quotientStalkSMul_germ X I F hI x (U ⊓ V) hxW _ _

end Stacks.SheafOfModules
