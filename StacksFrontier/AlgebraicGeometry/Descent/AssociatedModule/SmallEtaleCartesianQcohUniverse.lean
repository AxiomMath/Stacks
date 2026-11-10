module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianUniverse
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous

/-!
# Cartesian modules on the small étale site are quasi-coherent, at section universe `u + 1`

Let `S` be a scheme contained in a big étale site `B`, and let `𝒢` be a sheaf of modules on the
small étale site `S_étale`, with sections in `Type (u + 1)`, which is *cartesian between affine
objects*: for every morphism `T ⟶ T'` of `S_étale` with affine underlying schemes the base-change
comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.  This file proves that `𝒢` is
quasi-coherent on the site, the converse half of Descent, Proposition 03DX (2) at `τ = étale`,
at the section universe of the higher direct images of Stacks 0765.

## The route

The universe-`u` statement
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines` goes through the
associated module of the restriction to the small Zariski site, that is through Mathlib's
quasi-coherent modules on a scheme, whose sections are pinned to the universe of the scheme.  Here
the argument stays on the étale side:

* the coefficient rings are raised to `Type (u + 1)` by `Stacks.Modules.sheafRingULiftUp`, which
  changes neither the sections nor quasi-coherence, so that the rings and the module sections
  live in one universe;
* quasi-coherence on `S_étale` is quasi-coherence of the restriction to the dense subsite of
  affine objects, `Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`;
* on the affine subsite every base-change map is an isomorphism, which is condition (1) of
  Stacks 0GZX, and that implies quasi-coherence by
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_presheafRingULiftUp_iff`: the
  base-change comparison of a presheaf of modules is bijective exactly when it is so after raising
  the universe of the coefficient rings.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_succ`:
  **a sheaf of modules on `S_étale` with sections in `Type (u + 1)` which is cartesian between
  affine objects is quasi-coherent.**
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ`:
  the two halves of Descent, Proposition 03DX (2) together, at section universe `u + 1`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PresheafOfModules

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)
open scoped _root_.Stacks.PresheafOfModules.ChangeOfRings

universe v r z m

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ CommRingCat.{r})

/-- **The base-change comparison does not see the universe of the coefficient rings.**  For a
presheaf of `𝒪`-modules `N` and an arrow `f`, the comparison `𝒪(Y) ⊗_{𝒪(X)} N(X) ⟶ N(Y)` is
bijective exactly when the comparison for `N` read over the universe lift of `𝒪` is: the two
tensor products are identified by `b ⊗ x ↦ ULift.up b ⊗ x`, compatibly with the two
comparisons, which both send `b ⊗ x` to `b • N(f)(x)`. -/
theorem bijective_restrictionBaseChange_presheafRingULiftUp_iff
    (N : PresheafOfModules.{max m r u v z} (structureRingPresheaf 𝒪)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Function.Bijective (restrictionBaseChange.{u, v, max u v r z, max m r u v z}
        (R := Stacks.Modules.ringULift.{u, v, r, z} 𝒪)
        ((Stacks.Modules.presheafRingULiftUp.{u, v, r, z, max m r u v z} 𝒪).obj N) f) ↔
      Function.Bijective (restrictionBaseChange.{u, v, r, max m u v z} (R := 𝒪) N f) := by
  classical
  let N' := (Stacks.Modules.presheafRingULiftUp.{u, v, r, z, max m r u v z} 𝒪).obj N
  let R' := Stacks.Modules.ringULift.{u, v, r, z} 𝒪
  let c := restrictionBaseChange.{u, v, r, max m u v z} (R := 𝒪) N f
  let c' := restrictionBaseChange.{u, v, max u v r z, max m r u v z} (R := R') N' f
  let S := (ModuleCat.restrictScalars (𝒪.map f).hom).obj (ModuleCat.of _ (𝒪.obj Y))
  let S' := (ModuleCat.restrictScalars (R'.map f).hom).obj (ModuleCat.of _ (R'.obj Y))
  let T := TensorProduct (𝒪.obj X) S (N.obj X)
  let T' := TensorProduct (R'.obj X) S' (N'.obj X)
  let φ : S →+ N.obj X →+ T' :=
    { toFun := fun b =>
        { toFun := fun x => TensorProduct.tmul (R'.obj X) (show S' from ULift.up b) x
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext x
        exact TensorProduct.zero_tmul _ _
      map_add' := fun b b' => by
        ext x
        exact TensorProduct.add_tmul _ _ _ }
  let ψ : S' →+ N'.obj X →+ T :=
    { toFun := fun b =>
        { toFun := fun x => TensorProduct.tmul (𝒪.obj X) (show S from ULift.down b) x
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext x
        exact TensorProduct.zero_tmul _ _
      map_add' := fun b b' => by
        ext x
        exact TensorProduct.add_tmul _ _ _ }
  let α : T →+ T' := TensorProduct.liftAddHom φ (fun a b x =>
    TensorProduct.smul_tmul (show ↑(R'.obj X) from ULift.up a) (show S' from ULift.up b)
      (show ↑(N'.obj X) from x))
  let β : T' →+ T := TensorProduct.liftAddHom ψ (fun a b x =>
    TensorProduct.smul_tmul (show ↑(𝒪.obj X) from ULift.down a) (show S from ULift.down b)
      (show ↑(N.obj X) from x))
  have hβα : ∀ t : T, β (α t) = t := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul b x => rfl
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  have hαβ : ∀ t : T', α (β t) = t := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul b x => rfl
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  have hcomp : ∀ s : T, c' (α s) = c s := fun s => by
    induction s using TensorProduct.inductionOn with
    | tmul b x =>
      exact (restrictionBaseChange_tmul.{u, v, max u v r z, max m r u v z} (R := R') N' f
          (ULift.up b) x).trans
        (restrictionBaseChange_tmul.{u, v, r, max m u v z} (R := 𝒪) N f b x).symm
    | add s s' hs hs' => exact (congrArg c' (map_add α s s')).trans ((c'.hom.map_add _ _).trans
        ((congrArg₂ (· + ·) hs hs').trans (c.hom.map_add s s').symm))
  have hαbij : Function.Bijective α :=
    ⟨Function.LeftInverse.injective hβα, Function.RightInverse.surjective hαβ⟩
  have heq : (fun t : T => c t) = (fun t : T' => c' t) ∘ α := funext fun t => (hcomp t).symm
  have key : Function.Bijective (fun t : T => c t) ↔ Function.Bijective (fun t : T' => c' t) := by
    rw [heq]
    exact Function.Bijective.of_comp_iff _ hαbij
  exact key.symm

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying presheaf of sets of the structure sheaf of `S_étale` is a sheaf. -/
theorem isSheaf_forget_structureSheaf :
    Presheaf.IsSheaf (topology B S hS) ((structureSheaf B S hS).obj ⋙ forget RingCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_globalSections B S hS)

/-- **A sheaf of modules on `S_étale` with sections in `Type (u + 1)` which is cartesian between
affine objects is quasi-coherent**: the converse half of Descent, Proposition 03DX (2) at
`τ = étale`, at the section universe of the higher direct images of Stacks 0765.

The coefficient rings are raised to `Type (u + 1)`, which changes neither the sections nor
quasi-coherence (`Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown`); quasi-coherence is
then read on the dense subsite of affine objects
(`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`), where every base-change map is
an isomorphism by hypothesis, read across the lift of the rings by
`Stacks.PresheafOfModules.bijective_restrictionBaseChange_presheafRingULiftUp_iff`, and that is
condition (1) of Stacks 0GZX, which gives quasi-coherence by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`. -/
theorem isQuasicoherentOnSite_of_bijective_restrictionBaseChange_succ
    (G : SheafOfModules.{u + 1} (structureSheaf B S hS))
    (hG : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        Function.Bijective
          (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
            G.val g.op)) :
    G.IsQuasicoherentOnSite := by
  have h𝒪 : Presheaf.IsSheaf (topology B S hS)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (commStructurePresheaf B S hS)) := (structureSheaf B S hS).property
  have hset : Presheaf.IsSheaf (topology B S hS)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (commStructurePresheaf B S hS) ⋙ forget RingCat.{u}) :=
    isSheaf_forget_structureSheaf B S hS
  let up := Stacks.Modules.sheafRingULiftUp.{u + 1, u, u, 0, u + 1} h𝒪 hset
  suffices hup : (up.obj G).IsQuasicoherentOnSite by
    exact Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown.{u + 1, u, u, 0} h𝒪 hset
      (up.obj G)
  have hO' : Presheaf.IsSheaf (topology B S hS)
      (Stacks.Modules.ringULift.{u + 1, u, u, 0} (commStructurePresheaf B S hS)) := by
    have : HasLimitsOfSize.{u, u + 1} CommRingCat.{u + 1} :=
      hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
    refine (Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget CommRingCat.{u + 1})).mpr ?_
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ CategoryTheory.uliftFunctor.{u + 1, u} hset
  let O' : Sheaf (topology B S hS) CommRingCat.{u + 1} := ⟨_, hO'⟩
  have hds : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have hcc : (SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  have : HasLimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  have : ∀ V : SmallEtale B S hS,
      HasWeakSheafify ((topology B S hS).over V) AddCommGrpCat.{u + 1} := fun V =>
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1}
      ((topology B S hS).over V)).1
  have : ∀ V : SmallEtale B S hS,
      ((topology B S hS).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := fun V =>
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u}
      ((topology B S hS).over V)
  have : ∀ V : SmallAffineEtale B S hS,
      HasWeakSheafify ((SmallAffineEtale.topology B S hS).over V) AddCommGrpCat.{u + 1} :=
    fun V => (GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1}
      ((SmallAffineEtale.topology B S hS).over V)).1
  have : ∀ V : SmallAffineEtale B S hS,
      ((SmallAffineEtale.topology B S hS).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := fun V =>
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u}
      ((SmallAffineEtale.topology B S hS).over V)
  refine (Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff
    (SmallAffineEtale.topology B S hS) (topology B S hS) (SmallAffineEtale.inclusion B S hS)
    (Stacks.Modules.structureSheafRingULift.{u + 1, u, u, 0} hset) (up.obj G)).2 ?_
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
    (affineRingedSite (SmallAffineEtale.topology B S hS) (topology B S hS)
      (SmallAffineEtale.inclusion B S hS) O') _ (fun U V f => ?_)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact (Stacks.PresheafOfModules.bijective_restrictionBaseChange_presheafRingULiftUp_iff.{u + 1,
    u, u, 0, u + 1} (commStructurePresheaf B S hS) G.val
      ((SmallAffineEtale.inclusion B S hS).map f).op).2
    (hG ((SmallAffineEtale.inclusion B S hS).map f) U.2 V.2)

/-- **Descent, Proposition 03DX (2) at `τ = étale`, at section universe `u + 1`.**  A sheaf of
modules on the small étale site of a scheme, with sections in `Type (u + 1)`, is quasi-coherent
exactly when it is cartesian between affine objects. -/
theorem isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ
    (G : SheafOfModules.{u + 1} (structureSheaf B S hS)) :
    G.IsQuasicoherentOnSite ↔ ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        Function.Bijective
          (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
            G.val g.op) :=
  ⟨fun hG _ _ g hT hT' =>
    bijective_restrictionBaseChange_of_isQuasicoherentOnSite_univ.{u, u + 1} B S hS G hG hT hT' g,
    isQuasicoherentOnSite_of_bijective_restrictionBaseChange_succ B S hS G⟩

end AlgebraicGeometry.SmallEtale

end
