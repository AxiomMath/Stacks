module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Pullback preserves locally quasi-coherent modules

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`. The inverse image `f^* = f^{-1} : Mod(𝒴_ét, 𝒪_𝒴) → Mod(𝒳_ét, 𝒪_𝒳)` preserves
locally quasi-coherent modules.

## Main definitions

* `PresheafOfModules.isoOfForgetIso`: a family of maps between the sections of two presheaves of
  modules which is additive, scalar-compatible, and realizes an isomorphism of the underlying
  presheaves of sets, is an isomorphism of presheaves of modules.
* `AlgebraicGeometry.Stack.etaleSheafOfSections`: the presheaf of sections of an étale sheaf of
  modules, as a sheaf of sets.
* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageForgetIso` and
  `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageMap`: the identification of the
  restriction at `x` of the inverse image of an étale sheaf of modules with the restriction of
  that sheaf at `f x`, on the underlying presheaves of sets, and its map on sections.
* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageIso`: the same identification
  as an isomorphism of presheaves of modules.

## Main results

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageMap_add` and
  `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageMap_smul`: that identification
  is additive and compatible with the scalars on sections.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_modulePullback`: the inverse image of a locally
  quasi-coherent module is locally quasi-coherent.

## References

* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w v' w' m

namespace PresheafOfModules

/-- A family of maps between the sections of two presheaves of modules over one presheaf of
rings which is additive and compatible with the scalar action, and which realizes an
isomorphism of the underlying presheaves of sets, is an isomorphism of presheaves of modules. -/
noncomputable def isoOfForgetIso {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{m} R}
    (e : M.presheaf ⋙ forget AddCommGrpCat ≅ N.presheaf ⋙ forget AddCommGrpCat)
    (g : ∀ U : Cᵒᵖ, ↥(M.obj U) → ↥(N.obj U))
    (hg : ∀ (U : Cᵒᵖ) (x : M.obj U), g U x = e.hom.app U x)
    (hadd : ∀ (U : Cᵒᵖ) (x y : M.obj U), g U (x + y) = g U x + g U y)
    (hsmul : ∀ (U : Cᵒᵖ) (r : R.obj U) (x : M.obj U), g U (r • x) = r • g U x) :
    M ≅ N := by
  refine PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine (LinearEquiv.ofBijective
      ({ toFun := g U, map_add' := hadd U, map_smul' := hsmul U } :
        M.obj U →ₗ[R.obj U] N.obj U) ⟨?_, ?_⟩).toModuleIso
    · intro a b hab
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
        (((hg U a).symm.trans hab).trans (hg U b))
    · intro b
      obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app U)).2 b
      exact ⟨a, (hg U a).trans ha⟩
  · intro U V i
    ext x
    have hnat := ConcreteCategory.congr_hom (e.hom.naturality i) x
    exact ((hg V _).trans hnat).trans (congrArg (N.map i) (hg U x).symm)

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids)

/-- The structure presheaf of the source of a 1-morphism is the restriction along it of the
structure presheaf of the target, for the étale topology. -/
theorem ringStructureSheafCore_obj_eq_comp :
    (ringStructureSheafCore B S hS (f ⋙ q) hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj =
      f.op ⋙ (ringStructureSheafCore B S hS q hq (etaleTopology B)
        (etaleTopology_le_topology B)).obj :=
  ringStructureSheafCore_obj_eq B S hS (f ⋙ q) q hp hq f rfl (etaleTopology B)
    (etaleTopology_le_topology B)

/-- The inverse image of presheaves of modules along a strictly presented 1-morphism, for the
étale topology: restriction along `f`, then restriction of scalars along
`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq_comp`. -/
noncomputable abbrev modulePresheafPullback :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
        (etaleTopology_le_topology B)).obj ⥤
      PresheafOfModules.{m} (ringStructureSheafCore B S hS (f ⋙ q) hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj :=
  PresheafOfModules.pushforward₀ f (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj ⋙
    PresheafOfModules.restrictScalars
      (eqToHom (ringStructureSheafCore_obj_eq_comp B S hS q hq f hp))

variable (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)

/-- The presheaf of sections of an étale sheaf of modules on a category fibred in groupoids, as
a sheaf of sets. -/
noncomputable def etaleSheafOfSections :
    Sheaf (associatedTopology B S hS q (etaleTopology B)) (Type m) :=
  ⟨G.presheaf ⋙ forget AddCommGrpCat, Presheaf.isSheaf_comp_of_isSheaf _ _ _ hG⟩

variable (hf : (f ⋙ q).IsFibredOneMorphism q f) (x : 𝒳)

/-- The identification of the restriction at `x` of the inverse image of an étale sheaf of
modules with the restriction of that sheaf at `f x`, as an isomorphism of the underlying
presheaves of sets of the two restricted modules. -/
noncomputable def restrictModuleToSmallEtaleInverseImageForgetIso :
    (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
          (etaleTopology_le_topology B)
          ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj
            G)).presheaf ⋙ forget AddCommGrpCat ≅
      (restrictModuleToSmallEtale B E h S hS q hq (f.obj x) (etaleTopology B)
          (etaleTopology_le_topology B) G).presheaf ⋙ forget AddCommGrpCat :=
  restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf x
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)

/-- The map on sections of `restrictModuleToSmallEtaleInverseImageForgetIso`, at one small étale
object. -/
noncomputable def restrictModuleToSmallEtaleInverseImageMap
    (W : (SmallEtale E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x)))ᵒᵖ) :
    ↥((restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
        (etaleTopology_le_topology B)
        ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) →
      ↥((restrictModuleToSmallEtale B E h S hS q hq (f.obj x) (etaleTopology B)
        (etaleTopology_le_topology B) G).obj W) :=
  (restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf x
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)).hom.app W

/-- The map on sections is the component of `restrictModuleToSmallEtaleInverseImageForgetIso`. -/
theorem restrictModuleToSmallEtaleInverseImageMap_eq
    (W : (SmallEtale E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x)))ᵒᵖ)
    (a : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) :
    restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x W a =
      (restrictModuleToSmallEtaleInverseImageForgetIso.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x).hom.app W a :=
  rfl

/-- On sections over `W`, `restrictModuleToSmallEtaleInverseImageMap` is restriction of sections
of `G` along the comparison arrow of `existsUnique_inverseImageComparisonLift`. -/
private theorem restrictModuleToSmallEtaleInverseImageMap_eq_map
    (W : (SmallEtale E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x)))ᵒᵖ)
    (y : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) :
    restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x W y =
      ((etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG).obj.map
        (existsUnique_inverseImageComparisonLift B E h S hS q hq f hp x W.unop).exists.choose.op)
        y := by
  classical
  obtain ⟨hφ1, hφ2⟩ :=
    (existsUnique_inverseImageComparisonLift B E h S hS q hq f hp x W.unop).exists.choose_spec
  have happ := restrictToSmallEtaleInverseImageIso_app B E h S hS q hq f hp hf x
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG) W.unop _ hφ1 hφ2
  change (restrictToSmallEtaleInverseImageIso B E h S hS q hq f hp hf x
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)).hom.app
      (Opposite.op W.unop) y = _
  rw [happ]
  rfl

/-- The map `restrictModuleToSmallEtaleInverseImageMap` on sections is additive. -/
theorem restrictModuleToSmallEtaleInverseImageMap_add
    (W : (SmallEtale E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x)))ᵒᵖ)
    (a b : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) :
    restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x W (a + b) =
      restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf x W a +
        restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf x W b := by
  simp only [restrictModuleToSmallEtaleInverseImageMap_eq_map.{u, v, w, v', w', m}
    B E h S hS q hq f hp G hG hf x W]
  exact map_add (G.presheaf.map _).hom a b

/-- The map `restrictModuleToSmallEtaleInverseImageMap` on sections is compatible with the scalar
actions. -/
theorem restrictModuleToSmallEtaleInverseImageMap_smul
    (W : (SmallEtale E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x)))ᵒᵖ)
    (r : (SmallEtale.structureSheaf E (q.obj (f.obj x)).left.1
      (contains_base B E h S hS q (f.obj x))).obj.obj W)
    (a : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj W) :
    restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x W (r • a) =
      r • restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
        B E h S hS q hq f hp G hG hf x W a := by
  have hφ :=
    (existsUnique_inverseImageComparisonLift B E h S hS q hq f hp x W.unop).exists.choose_spec
  let φ := (existsUnique_inverseImageComparisonLift B E h S hS q hq f hp x W.unop).exists.choose
  have hPeq : (Over.post (X := f.obj x) (q ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS q hq (f.obj x)
  have hQeq : (Over.post (X := x) ((f ⋙ q) ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS (f ⋙ q) hp x
  let V := (smallEtaleInclusion B E h (q.obj (f.obj x)).left.1
    (contains_base B E h S hS q (f.obj x))).obj W.unop
  let bb := (Over.post (X := x) ((f ⋙ q) ⋙ Over.forget (B.obj hS))).inv.obj V
  let Isrc := localStructurePresheafIso B E h S hS (f ⋙ q) hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let Itar := localStructurePresheafIso B E h S hS q hq (f.obj x) (etaleTopology B)
    (etaleTopology_le_topology B)
  have hΓ := congrArg (fun g => Scheme.Γ.map ((B.inclusion).map g).op) hφ.2
  have hring : (ringStructureSheafCore B S hS q hq (etaleTopology B)
        (etaleTopology_le_topology B)).obj.map φ.op
      ((RingCat.Hom.hom
        ((eqToHom (ringStructureSheafCore_obj_eq_comp B S hS q hq f hp)).app
          (Opposite.op bb.left))) (Isrc.hom.app W r)) = Itar.hom.app W r := by
    simp only [Isrc, Itar, eqToHom_app]
    show (Scheme.Γ.map (B.inclusion.map (q.map φ).left).op).hom
      ((Scheme.Γ.map (B.inclusion.map ((Over.post (X := x)
        ((f ⋙ q) ⋙ Over.forget (B.obj hS))).objObjPreimageIso V).hom.left).op).hom r) =
        (Scheme.Γ.map (B.inclusion.map ((Over.post (X := f.obj x)
          (q ⋙ Over.forget (B.obj hS))).objObjPreimageIso V).hom.left).op).hom r
    have hcomp := Scheme.Γ.map_comp
      (B.inclusion.map ((Over.post (X := x)
        ((f ⋙ q) ⋙ Over.forget (B.obj hS))).objObjPreimageIso V).hom.left).op
      (B.inclusion.map (q.map φ).left).op
    exact (congrArg (fun g => g.hom r) hcomp).symm.trans (congrArg (fun g => g.hom r) hΓ)
  rw [restrictModuleToSmallEtaleInverseImageMap_eq_map.{u, v, w, v', w', m}
    B E h S hS q hq f hp G hG hf x W,
    restrictModuleToSmallEtaleInverseImageMap_eq_map.{u, v, w, v', w', m}
    B E h S hS q hq f hp G hG hf x W]
  let s := (RingCat.Hom.hom
    ((eqToHom (ringStructureSheafCore_obj_eq_comp B S hS q hq f hp)).app
      (Opposite.op bb.left))) (Isrc.hom.app W r)
  let aG : G.obj (Opposite.op (f.obj bb.left)) := a
  show G.map φ.op (s • aG) = (Itar.hom.app W r) • G.map φ.op aG
  rw [G.map_smul, hring]

/-- The restriction at an object `x` of `𝒳` of the inverse image of a presheaf of modules on
`𝒴` is canonically the restriction at `f x` of that presheaf of modules, as presheaves of
modules on the small étale site of the scheme they both lie over. -/
noncomputable def restrictModuleToSmallEtaleInverseImageIso :
    restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
        (etaleTopology_le_topology B)
        ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) ≅
      restrictModuleToSmallEtale B E h S hS q hq (f.obj x) (etaleTopology B)
        (etaleTopology_le_topology B) G :=
  PresheafOfModules.isoOfForgetIso
    (restrictModuleToSmallEtaleInverseImageForgetIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf x)
    (restrictModuleToSmallEtaleInverseImageMap.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf x)
    (restrictModuleToSmallEtaleInverseImageMap_eq.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf x)
    (restrictModuleToSmallEtaleInverseImageMap_add.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf x)
    (restrictModuleToSmallEtaleInverseImageMap_smul.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG hf x)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids) (hf : (f ⋙ q).IsFibredOneMorphism q f)

include hf

/-- The inverse image of presheaves of modules along a 1-morphism of categories fibred in
groupoids over the big fppf category of `S` preserves local quasi-coherence. -/
@[stacks 06WL]
theorem isLocallyQuasicoherent_modulePullback
    (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS q hq G) :
    IsLocallyQuasicoherent B E h S hS (f ⋙ q) hp
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) := by
  classical
  have : (f ⋙ q).IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  refine ⟨?_, ?_⟩
  · have := (hf.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    exact f.op_comp_isSheaf_of_isSheaf _ _ _ hG.1
  · intro y
    let eModule := restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
      B E h S hS q hq f hp G hG.1 hf y
    let Rsmall := SmallEtale.structureSheaf E (q.obj (f.obj y)).left.1
      (contains_base B E h S hS q (f.obj y))
    obtain ⟨hMtar, hQCtar⟩ := hG.2 (f.obj y)
    have hMsrc : Presheaf.IsSheaf (SmallEtale.topology E (q.obj (f.obj y)).left.1
        (contains_base B E h S hS q (f.obj y)))
        (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp y (etaleTopology B)
          (etaleTopology_le_topology B)
          ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).presheaf :=
      (Presheaf.isSheaf_of_iso_iff
        ((PresheafOfModules.toPresheaf Rsmall.obj).mapIso eModule)).2 hMtar
    exact ⟨hMsrc, SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((SheafOfModules.fullyFaithfulForget Rsmall).preimageIso eModule :
        (⟨_, hMsrc⟩ : SheafOfModules Rsmall) ≅ ⟨_, hMtar⟩).symm hQCtar⟩

end AlgebraicGeometry.Stack

end
