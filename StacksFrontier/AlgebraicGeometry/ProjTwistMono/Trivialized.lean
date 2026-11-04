module

public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An epimorphism between invertible sheaves of modules on a scheme is an isomorphism

Let `X` be a scheme and `f : M ⟶ N` an epimorphism of sheaves of `𝒪_X`-modules with `M` and `N`
invertible. This file proves that `f` is an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistMono.ratio`: the section of the structure sheaf that a
  morphism becomes when read through trivializations of its source and target.
* `Stacks.AlgebraicGeometry.ProjTwistMono.trivOfIsoUnit`: the sectionwise trivialization over
  the whole space given by an isomorphism of a sheaf of modules with the unit.
* `Stacks.AlgebraicGeometry.ProjTwistMono.homOfTriv` and `isoUnitOfTriv`: the morphism to the
  unit, and the isomorphism with the unit, given by a sectionwise trivialization over the whole
  space.
* `Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjFreeIso`: the pullback of a free sheaf of
  modules along any morphism of schemes is free with the same index set.
* `Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso`: the pullback of the unit along
  any morphism of schemes is the unit.
* `Stacks.AlgebraicGeometry.ProjTwistMono.restrictPullbackIsoUnit`: the restriction of a pullback
  to an open over which the morphism factors through an open where the module pulls back to the
  unit is the unit.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible`: an epimorphism between
  invertible sheaves of modules on a scheme is an isomorphism.
* `Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_trivializations` and
  `isIso_of_locallySurjective_of_trivializations`: the same with invertibility replaced by the
  hypothesis that each point has a neighbourhood over which both modules are sectionwise trivial,
  and in the second with epimorphy replaced by local surjectivity on sections.
* `Stacks.AlgebraicGeometry.ProjTwistMono.θ_app_eq`: read through a trivialization of the source
  and one of the target over the same open, a morphism is multiplication by `ratio`.
* `Stacks.AlgebraicGeometry.ProjTwistMono.bijective_app_of_locally`: bijectivity on sections is
  local.
* `Stacks.AlgebraicGeometry.ProjTwistMono.bijective_app_of_isIso_restrict` and
  `isIso_of_isIso_restrict_locally`: being an isomorphism is local on the base.
* `Stacks.AlgebraicGeometry.ProjTwistMono.epi_restrictFunctor_map`: the restriction functor to
  an open subscheme preserves epimorphisms.
* `Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top`: the preimage of an open under
  its own inclusion is everything.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry
open Stacks.SheafDescent

namespace Stacks.AlgebraicGeometry.ProjTwistMono

universe u

attribute [local implicit_reducible] sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The module structure on the sections of a sheaf of modules on a scheme, at the spelling of
the ring of sections in which `Stacks.SheafDescent.Trivialization` is linear. -/
local instance moduleSections (M : X.Modules) (W : X.Opens) :
    Module ((structureRingPresheaf X.presheaf).obj (op W) : Type u) (Γ(M, W) : Type u) :=
  (M.val.obj (op W)).isModule

/-- The section of the structure sheaf over `V` that the trivializations `σ` and `τ` turn `f`
into: the image under `τ` of the image under `f` of the basis section of `σ`. -/
noncomputable def ratio {M N : X.Modules} (f : M ⟶ N) {V : X.Opens}
    (σ : Trivialization X.presheaf M.val V) (τ : Trivialization X.presheaf N.val V) :
    ((structureRingPresheaf X.presheaf).obj (op V) : Type u) :=
  τ.θ V (𝟙 V) (f.app V σ.basis)

/-- Read through the two trivializations, a morphism is multiplication by `ratio`. -/
theorem θ_app_eq {M N : X.Modules} (f : M ⟶ N) {V : X.Opens}
    (σ : Trivialization X.presheaf M.val V) (τ : Trivialization X.presheaf N.val V)
    {W : X.Opens} (h : W ⟶ V) (m : Γ(M, W)) :
    τ.θ W h (f.app W m) =
      σ.θ W h m * (structureRingPresheaf X.presheaf).map h.op (ratio f σ τ) := by
  have hnat : f.app W (σ.basisAt h) = N.val.map h.op (f.app V σ.basis) :=
    PresheafOfModules.naturality_apply f.val h.op σ.basis
  have hθ : τ.θ W h (N.val.map h.op (f.app V σ.basis)) =
      (structureRingPresheaf X.presheaf).map h.op (ratio f σ τ) := by
    have hn := τ.θ_naturality (𝟙 V) h (f.app V σ.basis)
    rwa [Category.comp_id] at hn
  have hsm : f.app W (σ.θ W h m • σ.basisAt h) = σ.θ W h m • f.app W (σ.basisAt h) :=
    (f.val.app (op W)).hom.map_smul _ _
  refine Eq.trans (congrArg (fun y => τ.θ W h (f.app W y)) (σ.eq_smul_basisAt h m)) ?_
  refine Eq.trans (congrArg (τ.θ W h) hsm) ?_
  refine Eq.trans (map_smul (τ.θ W h) _ _) ?_
  exact Eq.trans (congrArg (fun z => σ.θ W h m • z) (hnat ▸ hθ)) (smul_eq_mul _ _)

/-- Where `ratio` restricts to a unit, the morphism is bijective on sections. -/
theorem bijective_app_of_isUnit {M N : X.Modules} (f : M ⟶ N) {V : X.Opens}
    (σ : Trivialization X.presheaf M.val V) (τ : Trivialization X.presheaf N.val V)
    {W : X.Opens} (h : W ⟶ V)
    (hu : IsUnit ((structureRingPresheaf X.presheaf).map h.op (ratio f σ τ))) :
    Function.Bijective (ConcreteCategory.hom (f.app W)) := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : w * (structureRingPresheaf X.presheaf).map h.op (ratio f σ τ) = 1 :=
    (mul_comm _ _).trans hw
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun n => (σ.θ W h).symm (τ.θ W h n * w), fun m => ?_, fun n => ?_⟩
  · dsimp only
    rw [θ_app_eq f σ τ h m, mul_assoc, hw, mul_one]
    exact (σ.θ W h).symm_apply_apply m
  · refine (τ.θ W h).injective ?_
    dsimp only
    refine Eq.trans (θ_app_eq f σ τ h _) ?_
    refine Eq.trans (congrArg
      (fun z => z * (structureRingPresheaf X.presheaf).map h.op (ratio f σ τ))
      ((σ.θ W h).apply_symm_apply (τ.θ W h n * w))) ?_
    rw [mul_assoc, hw', mul_one]

/-- From a section that lifts the target's local basis, `ratio` restricts to a unit. -/
theorem isUnit_ratio_res {M N : X.Modules} (f : M ⟶ N) {V : X.Opens}
    (σ : Trivialization X.presheaf M.val V) (τ : Trivialization X.presheaf N.val V)
    {W : X.Opens} (h : W ⟶ V) (s : Γ(M, W)) (hs : f.app W s = τ.basisAt h) :
    IsUnit ((structureRingPresheaf X.presheaf).map h.op (ratio f σ τ)) :=
  IsUnit.of_mul_eq_one_right (σ.θ W h s)
    ((θ_app_eq f σ τ h s).symm.trans ((congrArg (τ.θ W h) hs).trans (τ.θ_basisAt h)))

/-! ### From local bijectivity on sections to an isomorphism -/

/-- A morphism of sheaves of modules on a scheme that is bijective on all sections is an
isomorphism. -/
private theorem isIso_of_bijective_app {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Bijective (ConcreteCategory.hom (f.app U))) : IsIso f :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (h U)

/-- Restriction in two steps is restriction. -/
theorem res_res {M : X.Modules} {W W' U : X.Opens} (a : W ⟶ U) (b : W' ⟶ W) (c : W' ⟶ U)
    (m : Γ(M, U)) :
    M.presheaf.map b.op (M.presheaf.map a.op m) = M.presheaf.map c.op m := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- **Bijectivity on sections is local.** A morphism of sheaves of modules bijective on the
sections over every open inside some neighbourhood of each point is bijective on the sections
over every open. -/
theorem bijective_app_of_locally {M N : X.Modules} (f : M ⟶ N) (V : ↥X → X.Opens)
    (hxV : ∀ x, x ∈ V x)
    (hbij : ∀ (x : ↥X) (W : X.Opens), W ≤ V x →
      Function.Bijective (ConcreteCategory.hom (f.app W)))
    (U : X.Opens) : Function.Bijective (ConcreteCategory.hom (f.app U)) := by
  classical
  let C : ↥U → X.Opens := fun i => V i.1 ⊓ U
  have hle : ∀ i : ↥U, C i ≤ V i.1 := fun _ => inf_le_left
  let iCU : ∀ i : ↥U, C i ⟶ U := fun _ => homOfLE inf_le_right
  have hcover : U ≤ iSup C := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, ⟨hxV x, hx⟩⟩
  constructor
  · intro m m' hmm
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) C U iCU
      hcover m m' fun i => (hbij i.1 (C i) (hle i)).injective ?_
    exact (PresheafOfModules.naturality_apply f.val (iCU i).op m).trans <|
      (congrArg (N.presheaf.map (iCU i).op) hmm).trans
        (PresheafOfModules.naturality_apply f.val (iCU i).op m').symm
  · intro t
    choose u hu using fun i : ↥U =>
      (hbij i.1 (C i) (hle i)).surjective (N.presheaf.map (iCU i).op t)
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf C u := by
      intro i j
      refine (hbij i.1 (C i ⊓ C j) ((inf_le_left).trans (hle i))).injective ?_
      exact
        (PresheafOfModules.naturality_apply f.val (Opens.infLELeft (C i) (C j)).op (u i)).trans <|
        (congrArg (N.presheaf.map (Opens.infLELeft (C i) (C j)).op) (hu i)).trans <|
        (res_res _ _ (homOfLE (le_trans inf_le_left (iCU i).le)) t).trans <|
        (res_res _ _ (homOfLE (le_trans inf_le_left (iCU i).le)) t).symm.trans <|
        (congrArg (N.presheaf.map (Opens.infLERight (C i) (C j)).op) (hu j)).symm.trans
          (PresheafOfModules.naturality_apply f.val (Opens.infLERight (C i) (C j)).op (u j)).symm
    obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) C U iCU hcover u hcompat
    refine ⟨m, TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X) C U
      iCU hcover _ t fun i => ?_⟩
    exact (PresheafOfModules.naturality_apply f.val (iCU i).op m).symm.trans <|
      (congrArg (f.app (C i)) (hm i)).trans (hu i)

/-! ### The core result -/

/-- **A locally surjective morphism between sectionwise trivial modules is an isomorphism.**
The hypothesis `hsurj` is local surjectivity on sections, spelled out; `htriv` asks that each
point have a neighbourhood over which both modules are sectionwise trivial. -/
theorem isIso_of_locallySurjective_of_trivializations {M N : X.Modules} (f : M ⟶ N)
    (hsurj : ∀ (U : X.Opens) (t : Γ(N, U)) (x : ↥X), x ∈ U →
      ∃ (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)),
        f.app W s = N.presheaf.map (homOfLE hWU).op t ∧ x ∈ W)
    (htriv : ∀ x : ↥X, ∃ (V : X.Opens) (_ : x ∈ V),
      Nonempty (Trivialization X.presheaf M.val V) ∧
        Nonempty (Trivialization X.presheaf N.val V)) :
    IsIso f := by
  classical
  have key : ∀ x : ↥X, ∃ W : X.Opens, x ∈ W ∧
      ∀ W' : X.Opens, W' ≤ W → Function.Bijective (ConcreteCategory.hom (f.app W')) := by
    intro x
    obtain ⟨V, hxV, ⟨σ⟩, ⟨τ⟩⟩ := htriv x
    obtain ⟨W, hWV, s, hs, hxW⟩ := hsurj V τ.basis x hxV
    refine ⟨W, hxW, fun W' hW' => bijective_app_of_isUnit f σ τ (homOfLE (hW'.trans hWV))
      (isUnit_ratio_res f σ τ (homOfLE (hW'.trans hWV))
        (M.presheaf.map (homOfLE hW').op s) ?_)⟩
    exact (PresheafOfModules.naturality_apply f.val (homOfLE hW').op s).trans <|
      (congrArg (N.presheaf.map (homOfLE hW').op) hs).trans (res_res _ _ _ τ.basis)
  choose W hxW hbij using key
  exact isIso_of_bijective_app f (bijective_app_of_locally f W hxW hbij)

/-! ### Epimorphisms -/

/-- An epimorphism between sheaves of modules on a scheme is an isomorphism when each point
has a neighbourhood over which both modules are sectionwise trivial. -/
theorem isIso_of_epi_of_trivializations {M N : X.Modules} (f : M ⟶ N) (hepi : Epi f)
    (htriv : ∀ x : ↥X, ∃ (V : X.Opens) (_ : x ∈ V),
      Nonempty (Trivialization X.presheaf M.val V) ∧
        Nonempty (Trivialization X.presheaf N.val V)) :
    IsIso f := by
  have hls : TopCat.Presheaf.IsLocallySurjective (Scheme.Modules.Hom.mapPresheaf f) :=
    @Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi _ _ _ _ _ _ _ _ f hepi
  refine isIso_of_locallySurjective_of_trivializations f (fun U t x hx => ?_) htriv
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls U t x hx
  exact ⟨V, hVU, s, hs, hxV⟩

/-- **An epimorphism between invertible sheaves of modules on a scheme is an isomorphism.** -/
@[sga "3 VIII 4.7" "partial"]
theorem isIso_of_epi_of_isInvertible {M N : X.Modules} (f : M ⟶ N) (hepi : Epi f)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    IsIso f := by
  obtain ⟨VM, hVM, tM⟩ :=
    Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
      (X := X.toRingedSpace) X.ringCatSheaf.2 M
  obtain ⟨VN, hVN, tN⟩ :=
    Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
      (X := X.toRingedSpace) X.ringCatSheaf.2 N
  refine isIso_of_epi_of_trivializations f hepi fun x => ?_
  obtain ⟨y, hy⟩ := Opens.mem_iSup.mp (hVM ▸ (Opens.mem_top x))
  obtain ⟨z, hz⟩ := Opens.mem_iSup.mp (hVN ▸ (Opens.mem_top x))
  exact ⟨VM y ⊓ VN z, ⟨hy, hz⟩,
    ⟨(tM y).some.comp (homOfLE inf_le_left)⟩, ⟨(tN z).some.comp (homOfLE inf_le_right)⟩⟩

/-! ### The pullback of a free sheaf of modules -/

/-- **The pullback of a free sheaf of modules along a morphism of schemes is free**, with the
same index set. -/
noncomputable def pullbackObjFreeIso {Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I := by
  haveI : (Opens.map f.base).Final := CategoryTheory.final_of_representablyFlat _
  haveI : (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom f)).IsRightAdjoint :=
    ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction f⟩⟩
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-! ### Trivializations from isomorphisms with the unit -/

/-- An isomorphism of a sheaf of modules on a scheme with the unit gives a sectionwise
trivialization over the whole space. -/
noncomputable def trivOfIsoUnit {L : X.Modules} (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    Trivialization X.presheaf L.val ⊤ where
  θ W _ :=
    { toFun := fun m => ConcreteCategory.hom (e.hom.app W) m
      map_add' := fun m m' => map_add (ConcreteCategory.hom (e.hom.app W)) m m'
      map_smul' := fun r m => (e.hom.val.app (op W)).hom.map_smul r m
      invFun := fun a => ConcreteCategory.hom (e.inv.app W) a
      left_inv := fun m =>
        ConcreteCategory.congr_hom
          (congrArg (fun g => Scheme.Modules.Hom.app g W) e.hom_inv_id) m
      right_inv := fun a =>
        ConcreteCategory.congr_hom
          (congrArg (fun g => Scheme.Modules.Hom.app g W) e.inv_hom_id) a }
  θ_naturality {_ _} _ h' m := PresheafOfModules.naturality_apply e.hom.val h'.op m

/-- The morphism to the unit determined by a trivialization over the whole space: its
component over an open is the trivialization's own linear isomorphism there. -/
noncomputable def homOfTriv {L : X.Modules} (t : Trivialization X.presheaf L.val ⊤) :
    L ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨{ app := fun W => ModuleCat.ofHom (t.θ W.unop (homOfLE le_top)).toLinearMap
     naturality := fun {_ W'} h => by
       ext m
       exact t.θ_naturality (homOfLE le_top) h.unop m }⟩

/-- **A sectionwise trivialization over the whole space is an isomorphism with the unit**,
with forward morphism `homOfTriv`. -/
noncomputable def isoUnitOfTriv {L : X.Modules} (t : Trivialization X.presheaf L.val ⊤) :
    L ≅ SheafOfModules.unit X.ringCatSheaf :=
  haveI : IsIso (homOfTriv t) := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (t.θ W (homOfLE le_top)).bijective
  asIso (homOfTriv t)

/-! ### From an isomorphism on an open subscheme to bijectivity on the ambient sections -/

/-- The image of the preimage of a smaller open under an open immersion is that open.
Alias of `AlgebraicGeometry.image_preimage_ι`. -/
alias image_preimage_eq_of_le := AlgebraicGeometry.image_preimage_ι

/-- **A morphism whose restriction to an open subscheme is an isomorphism is bijective on the
sections over every open inside it.** -/
theorem bijective_app_of_isIso_restrict {M N : X.Modules} (f : M ⟶ N) {V : X.Opens}
    (h : IsIso ((Scheme.Modules.restrictFunctor V.ι).map f)) {W : X.Opens} (hW : W ≤ V) :
    Function.Bijective (ConcreteCategory.hom (f.app W)) := by
  have hb : ∀ V' : V.toScheme.Opens,
      Function.Bijective (ConcreteCategory.hom (f.app (V.ι ''ᵁ V'))) := fun V' =>
    (ConcreteCategory.isIso_iff_bijective _).mp (Scheme.Modules.Hom.isIso_iff_isIso_app.mp h V')
  exact image_preimage_eq_of_le hW ▸ hb (V.ι ⁻¹ᵁ W)

/-- **Being an isomorphism is local on the base**, for sheaves of modules on a scheme: a
morphism whose restriction to each member of an open cover is an isomorphism is an
isomorphism. -/
theorem isIso_of_isIso_restrict_locally {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : ↥X, ∃ (V : X.Opens) (_ : x ∈ V),
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map f)) :
    IsIso f := by
  choose V hxV hiso using h
  exact isIso_of_bijective_app f <| bijective_app_of_locally f V hxV
    fun x W hW => bijective_app_of_isIso_restrict f (hiso x) hW

/-! ### The restriction functor preserves epimorphisms -/

/-- **The restriction functor to an open subscheme preserves epimorphisms.** -/
theorem epi_restrictFunctor_map {Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    {M N : Y.Modules} (φ : M ⟶ N) (hepi : Epi φ) :
    Epi ((Scheme.Modules.restrictFunctor g).map φ) := by
  refine ⟨fun {Z} a b hab => ?_⟩
  refine ((Scheme.Modules.restrictAdjunction g).homEquiv N Z).injective
    (hepi.left_cancellation _ _ ?_)
  rw [← Adjunction.homEquiv_naturality_left, hab, Adjunction.homEquiv_naturality_left]

/-! ### The pullback of the unit -/

/-- **The pullback of the unit along a morphism of schemes is the unit**, by Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`. -/
noncomputable def pullbackObjUnitIso {Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : (Opens.map f.base).Final := CategoryTheory.final_of_representablyFlat _
  haveI : (SheafOfModules.pushforward.{u} (Scheme.Hom.toRingCatSheafHom f)).IsRightAdjoint :=
    ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction f⟩⟩
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom)

/-- The preimage of an open under its own inclusion is everything. -/
theorem preimage_self_eq_top (V : X.Opens) : V.ι ⁻¹ᵁ V = ⊤ := by
  refine top_le_iff.mp fun y _ => ?_
  have hrange : V.ι.base y ∈ V.ι.opensRange := ⟨y, rfl⟩
  rwa [Scheme.Opens.opensRange_ι] at hrange

/-- **A pullback is the unit on an open where the morphism factors through a trivializing open.**

If `q : X ⟶ Y` carries `W ≤ X` into an open `D` of `Y` on which `M` pulls back to the unit, by a
morphism `k` witnessing the factorization, then the restriction to `W` of `q^* M` is the unit. -/
noncomputable def restrictPullbackIsoUnit {Y : Scheme.{u}} (q : X ⟶ Y) (W : X.Opens)
    (M : Y.Modules) (D : Y.Opens) (k : W.toScheme ⟶ D.toScheme) (hk : k ≫ D.ι = W.ι ≫ q)
    (e : (Scheme.Modules.pullback D.ι).obj M ≅ SheafOfModules.unit D.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((Scheme.Modules.pullback q).obj M) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp W.ι q).app M ≪≫
    (Scheme.Modules.pullbackCongr hk.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp k D.ι).app M).symm ≪≫
    (Scheme.Modules.pullback k).mapIso e ≪≫ pullbackObjUnitIso k

end Stacks.AlgebraicGeometry.ProjTwistMono

end
