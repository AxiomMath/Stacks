module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleFunctoriality
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# Functoriality of sheaves of modules on fibred categories (Stacks 06WE)

A 1-morphism `f : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over the big fppf category of a
scheme `S` induces inverse- and direct-image functors on sheaves of modules over their
structure sheaves, for each of the associated topologies of Stacks 06TP. They restrict the
corresponding functors on presheaves of modules (Stacks 06WD) and form an adjoint pair.

The inverse image is objectwise restriction of modules along `f`, in an arbitrary module
universe. The direct image is defined in a module universe large enough for the two sites.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullback`: the inverse image of sheaves of modules, in an
  arbitrary module universe.
* `AlgebraicGeometry.Stack.moduleSheafPushforward`: the direct image of sheaves of modules.
* `AlgebraicGeometry.Stack.ModuleSheafFunctoriality`: the direct image, its identification with
  the direct image of presheaves of modules, and the adjunction, as one package.
* `AlgebraicGeometry.Stack.moduleSheafAdjunction`: the adjunction between the inverse and the
  direct image.

## Main results

* `AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`: the scalar identification that makes
  objectwise restriction a module over the structure sheaf of the source.
* `AlgebraicGeometry.Stack.moduleSheafFunctoriality`: the adjoint pair of inverse- and
  direct-image functors on sheaves of modules.
* `AlgebraicGeometry.Stack.modulePullback_obj_val_presheaf` and
  `AlgebraicGeometry.Stack.moduleSheafPushforward_obj_val`: the two functors restrict the
  presheaf-level ones of Stacks 06WD.

## Implementation notes

The underlying presheaf of rings of `AlgebraicGeometry.Stack.ringStructureSheafCore` does not
depend on the topology, so the presheaf-level functors of Stacks 06WD — which are stated for the
fppf structure sheaf — apply verbatim at every one of the associated topologies; only the sheaf
condition changes.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WD](https://stacks.math.columbia.edu/tag/06WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w m v' w' n

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include hf

/-- The structure presheaf of rings of the source is the restriction along `f` of the one of the
target. -/
theorem ringStructureSheafCore_obj_eq :
    (ringStructureSheafCore B S hS p hp τ hτ).obj =
      f.op ⋙ (ringStructureSheafCore B S hS q hq τ hτ).obj := by
  rw [ringStructureSheafCore_obj, ringStructureSheafCore_obj, ← hf]
  rfl

include hp hq

/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in
groupoids, in an arbitrary module universe: objectwise restriction of modules along `f`, with
scalars transported along `AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`. -/
@[stacks 06WE "the inverse image, in an arbitrary module universe"]
noncomputable def modulePullback :
    SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ) ⥤
      SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ) :=
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  SheafOfModules.pushforward
    (F := f) (J := associatedTopology B S hS p τ) (K := associatedTopology B S hS q τ)
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)⟩

/-- On underlying abelian presheaves the inverse image of sheaves of modules is precomposition
with `f.op`. -/
@[simp]
theorem modulePullback_obj_val_presheaf
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ)) :
    ((modulePullback B S hS p q hp hq f hf τ hτ).obj M).val.presheaf =
      f.op ⋙ M.val.presheaf := rfl

/-- The inverse image of sheaves of modules is the restriction of the inverse image of
presheaves of modules of Stacks 06WD: on underlying presheaves of modules it is
`PresheafOfModules.pushforward₀` followed by transport of scalars. -/
noncomputable def modulePullbackForgetIso :
    modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ ⋙
        SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ) ≅
      SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ) ⋙
        PresheafOfModules.pushforward₀ f
          (ringStructureSheafCore B S hS q hq τ hτ).obj ⋙
        PresheafOfModules.restrictScalars
          (eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)) :=
  Iso.refl _

/-- The direct image of sheaves of modules along a 1-morphism of categories fibred in groupoids,
its identification with the direct image of presheaves of modules of Stacks 06WD, and its
adjunction with the inverse image, in a module universe large enough for the two
categories. -/
structure ModuleSheafFunctoriality where
  /-- The direct image of sheaves of modules. -/
  pushforward :
    SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS p hp τ hτ) ⥤
      SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS q hq τ hτ)
  /-- The direct image restricts the direct image of presheaves of modules of Stacks 06WD. -/
  pushforward_iso :
    pushforward ⋙ SheafOfModules.forget.{max u v w m v' w'}
        (ringStructureSheafCore B S hS q hq τ hτ) ≅
      SheafOfModules.forget.{max u v w m v' w'}
        (ringStructureSheafCore B S hS p hp τ hτ) ⋙
        (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).pushforward
  /-- The inverse image is left adjoint to the direct image. -/
  adjunction : modulePullback B S hS p q hp hq f hf τ hτ ⊣ pushforward

/-- The inverse image of sheaves of modules, in an arbitrary module universe. -/
noncomputable abbrev ModuleSheafFunctoriality.pullback
    (_ : ModuleSheafFunctoriality.{u, v, w, m} B S hS p q hp hq f hf τ hτ) :
    SheafOfModules.{n} (ringStructureSheafCore B S hS q hq τ hτ) ⥤
      SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ hτ) :=
  modulePullback B S hS p q hp hq f hf τ hτ

/-- In the module universe of the adjunction, the inverse image of sheaves of modules restricts
the inverse image of presheaves of modules of Stacks 06WD. -/
noncomputable def ModuleSheafFunctoriality.pullback_iso
    (W : ModuleSheafFunctoriality.{u, v, w, m} B S hS p q hp hq f hf τ hτ) :
    W.pullback ⋙ SheafOfModules.forget.{max u v w m v' w'}
        (ringStructureSheafCore B S hS p hp τ hτ) ≅
      SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ) ⋙
        (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).pullback :=
  modulePullbackForgetIso B S hS p q hp hq f hf τ hτ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget _)
      (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).pullback_iso.symm

/-- The direct image of sheaves of modules along a 1-morphism of categories fibred in
groupoids: the direct image of presheaves of modules of Stacks 06WD, which preserves the sheaf
condition. -/
noncomputable def moduleSheafPushforward :
    SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS p hp τ hτ) ⥤
      SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS q hq τ hτ) :=
  have hF : Functor.IsFibredOneMorphism p q f := hq.isFibredOneMorphism hf
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let W := moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf
  { obj := fun M =>
      { val := W.pushforward.obj M.val
        isSheaf := by
          have hD := ((f.sheafPushforwardCocontinuous AddCommGrpCat.{max u v w m v' w'}
            (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).obj
              ((SheafOfModules.toSheaf (ringStructureSheafCore B S hS p hp τ hτ)).obj
                M)).property
          exact (Presheaf.isSheaf_of_iso_iff (W.pushforward_iso.app M.val ≪≫
            ((hF.directImageCompSheafToPresheafIso (τ.over (B.obj hS))
              AddCommGrpCat.{max u v w m v' w'}).app
                ((SheafOfModules.toSheaf
                  (ringStructureSheafCore B S hS p hp τ hτ)).obj M)).symm)).2 hD }
    map := fun {_ _} g => ⟨W.pushforward.map g.val⟩
    map_id := fun M => SheafOfModules.hom_ext (W.pushforward.map_id M.val)
    map_comp := fun g h => SheafOfModules.hom_ext (W.pushforward.map_comp g.val h.val) }

/-- The underlying presheaf of modules of the direct image is the direct image of presheaves of
modules of Stacks 06WD. -/
theorem moduleSheafPushforward_obj_val
    (M : SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS p hp τ hτ)) :
    ((moduleSheafPushforward.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).obj M).val =
      (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).pushforward.obj M.val := rfl

/-- The inverse image of sheaves of modules is left adjoint to the direct image. -/
@[stacks 06WE "the adjunction"]
noncomputable def moduleSheafAdjunction :
    modulePullback.{u, v, w, max u v w m v' w', v', w'} B S hS p q hp hq f hf τ hτ ⊣
      moduleSheafPushforward.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ :=
  (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).adjunction.restrictFullyFaithful
    (SheafOfModules.fullyFaithfulForget (ringStructureSheafCore B S hS q hq τ hτ))
    (SheafOfModules.fullyFaithfulForget (ringStructureSheafCore B S hS p hp τ hτ))
    (Functor.isoWhiskerLeft (SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ))
        (moduleFunctoriality.{u, v, w, m} B S hS p q hp hq f hf).pullback_iso ≪≫
      (modulePullbackForgetIso.{u, v, w, max u v w m v' w', v', w'}
        B S hS p q hp hq f hf τ hτ).symm)
    (Iso.refl _)

/-- The adjoint pair of inverse- and direct-image functors on sheaves of modules induced by a
1-morphism of categories fibred in groupoids. -/
@[stacks 06WE "the adjoint pair on sheaves of modules"]
noncomputable def moduleSheafFunctoriality :
    ModuleSheafFunctoriality.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ where
  pushforward := moduleSheafPushforward.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ
  pushforward_iso := Iso.refl _
  adjunction := moduleSheafAdjunction.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ

end AlgebraicGeometry.Stack

end
