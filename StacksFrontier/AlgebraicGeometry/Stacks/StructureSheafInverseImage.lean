module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePullbackMap

/-!
# The inverse image of the structure sheaf of a fibred category

The inverse image of sheaves of modules of **Stacks 06WE** along a 1-morphism `f : 𝒳 ⥤ 𝒴` of
categories fibred in groupoids is objectwise restriction of modules along `f`, and the structure
presheaf of rings of `𝒳` is the restriction along `f` of the structure presheaf of rings of `𝒴`.
Hence the inverse image of the structure sheaf of `𝒴`, viewed as a module over itself, *is* the
structure sheaf of `𝒳`.

The same identification is then read inside `LQCoh^fbc` of **Stacks 07AQ**, where the structure
sheaf is the unit object of `QCoh(𝒪_𝒳)` carried over by the inclusion of **Lemma 0778**.  That
form is what the relative pullback maps of **Stacks 06UM** at the structure sheaf are built from.

## Main definitions

* `AlgebraicGeometry.Stack.locallyQuasicoherentStructureSheafPullbackIso`: the identification as
  an isomorphism `pr^*𝒪_𝒲 ≅ 𝒪_𝒬` in `LQCoh^fbc(𝒪_𝒬)`.

## Main results

* `AlgebraicGeometry.Stack.modulePullback_obj_unit`: the inverse image of the structure sheaf is
  the structure sheaf.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangePullback_obj_structureSheaf`: the
  same equality for the inverse image on `LQCoh^fbc` at the unit object of `QCoh`.

## Implementation notes

Both equalities are transports along the scalar identification
`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`, and the resulting isomorphism is the
identity on sections: a section of `𝒪_𝒲` above `pr x` is a section of `𝒪_𝒬` above `x`.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w v' w'

namespace AlgebraicGeometry.Stack

/-- The inverse image of presheaves of modules along `eqToHom` of an equality `T = F.op ⋙ R` of
presheaves of rings takes the rank-one free module of `R` to the rank-one free module of `T`: at
every object both are the coefficient ring acting on itself. -/
private theorem pushforward_eqToHom_obj_unit {C : Type v} [Category.{w} C] {D : Type v'}
    [Category.{w'} D] (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) (T : Cᵒᵖ ⥤ RingCat.{u})
    (e : T = F.op ⋙ R) :
    (PresheafOfModules.pushforward (eqToHom e)).obj (PresheafOfModules.unit R) =
      PresheafOfModules.unit T := by
  subst e
  rfl

/-- A sheaf of modules is determined by its underlying presheaf of modules. -/
private theorem sheafOfModules_eq_of_val {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (h : M.val = N.val) : M = N := by
  obtain ⟨M, hM⟩ := M
  obtain ⟨N, hN⟩ := N
  subst h
  rfl

section Pullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of the structure sheaf is the structure sheaf.**  The inverse image of
sheaves of modules of **Stacks 06WE** along a 1-morphism `f` of categories fibred in groupoids is
objectwise restriction along `f`, and the structure presheaf of rings of the source is the
restriction along `f` of the one of the target
(`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`); so the inverse image takes the
structure sheaf of the target, as a module over itself, to the structure sheaf of the source. -/
theorem modulePullback_obj_unit {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (modulePullback.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).obj
        (SheafOfModules.unit (ringStructureSheafCore B S hS q hq τ hτ)) =
      SheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ) :=
  sheafOfModules_eq_of_val (pushforward_eqToHom_obj_unit f
    (ringStructureSheafCore B S hS q hq τ hτ).obj (ringStructureSheafCore B S hS p hp τ hτ).obj
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ))

end Pullback

section LocallyQuasicoherent

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒲 : Type (u + 1)} [Category.{u} 𝒲] {𝒬 : Type (u + 1)} [Category.{u} 𝒬]
  (w : 𝒲 ⥤ BigFppfOver B S hS) (hw : w.IsFiberedInGroupoids)
  (z : 𝒬 ⥤ BigFppfOver B S hS) (hz : z.IsFiberedInGroupoids)
  (pr : 𝒬 ⥤ 𝒲) (hpr : pr ⋙ w = z)
  (hincW : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS w hw,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS w hw
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS w hw .etale).obj F).val)
  (hincQ : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS z hz,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS z hz
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS z hz .etale).obj F).val)
  (hlq : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS w hw,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS z hz
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS z w hz hw pr hpr
        (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val)

/-- **The inverse image of the structure sheaf is the structure sheaf, read in `LQCoh^fbc`.**
The structure sheaf of `𝒲` is the unit object of `QCoh(𝒪_𝒲)` carried into `LQCoh^fbc(𝒪_𝒲)` by
the inclusion of **Lemma 0778**, and the inverse image on `LQCoh^fbc` restricts the inverse image
of **Stacks 06WE**, so `AlgebraicGeometry.Stack.modulePullback_obj_unit` applies verbatim. -/
theorem locallyQuasicoherentFlatBaseChangePullback_obj_structureSheaf :
    (locallyQuasicoherentFlatBaseChangePullback B E hE S hS z hz w hw pr hpr hlq).obj
        ((quasicoherentToFlatBaseChange B E hE S hS w hw hincW).obj
          (FibredSite.quasicoherentTensorUnit B S hS w hw)) =
      (quasicoherentToFlatBaseChange B E hE S hS z hz hincQ).obj
        (FibredSite.quasicoherentTensorUnit B S hS z hz) :=
  ObjectProperty.FullSubcategory.ext (modulePullback_obj_unit B S hS z w hz hw pr hpr
    (etaleTopology B) (etaleTopology_le_topology B))

/-- **The identification `pr^*𝒪_𝒲 ≅ 𝒪_𝒬` in `LQCoh^fbc(𝒪_𝒬)`.**  The isomorphism attached to
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangePullback_obj_structureSheaf`; it is
the identity on sections. -/
def locallyQuasicoherentStructureSheafPullbackIso :
    (locallyQuasicoherentFlatBaseChangePullback B E hE S hS z hz w hw pr hpr hlq).obj
        ((quasicoherentToFlatBaseChange B E hE S hS w hw hincW).obj
          (FibredSite.quasicoherentTensorUnit B S hS w hw)) ≅
      (quasicoherentToFlatBaseChange B E hE S hS z hz hincQ).obj
        (FibredSite.quasicoherentTensorUnit B S hS z hz) :=
  eqToIso (locallyQuasicoherentFlatBaseChangePullback_obj_structureSheaf
    B E hE S hS w hw z hz pr hpr hincW hincQ hlq)

end LocallyQuasicoherent

end AlgebraicGeometry.Stack

end
