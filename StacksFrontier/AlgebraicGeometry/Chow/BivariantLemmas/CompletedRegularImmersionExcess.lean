module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# Restriction of the Gysin class of a regular immersion, with excess

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let

```
Z' --i'--→ X'
|          |
g          f
↓          ↓
Z  --i---→ X
```

be a cartesian square of schemes locally of finite type over `S` whose horizontal arrows are
regular immersions. Write `𝒞 = 𝒞_{Z/X}` and `𝒞' = 𝒞_{Z'/X'}` for the conormal sheaves; the
canonical map `g^*𝒞 ⟶ 𝒞'` of Stacks 0473 is surjective, and suppose its kernel `𝒦` is finite
locally free. Then the restriction along `f` of the class `i^! = c(Z ⟶ X, 𝒞^∨)` of the normal
bundle is

  `res(i^!) = c_top(𝒦^∨) ∘ (i')^!`

in `A^*(Z' ⟶ X')^∧`. This is an instance of the counterpart of Stacks 0FV7 for immersions: by the
counterpart of the base-change clause of Stacks 0FBK, `res(i^!)` is `c(Z' ⟶ X', g^*(𝒞^∨))`, and the
counterpart of Stacks 0FBL applies to the short exact sequence

  `0 ⟶ (𝒞')^∨ ⟶ g^*(𝒞^∨) ⟶ 𝒦^∨ ⟶ 0`,

the dual of `0 ⟶ 𝒦 ⟶ g^*𝒞 ⟶ 𝒞' ⟶ 0` read through `(g^*(𝒞^∨))^∨ ≅ g^*𝒞`.

## Main results

* `Stacks.Chow.completedBivariantTransport_completedBivariantRestriction_ofIsRegularImmersion` —
  `res(i^!) = c_top(𝒦^∨) ∘ (i')^!` in `A^*(Z' ⟶ X')^∧`.

## Implementation notes

All modules in sight are finite locally free over locally Noetherian schemes, hence reflexive,
and the inclusion `(𝒞')^∨ ⟶ g^*(𝒞^∨)` is produced from its dual: a morphism
`b : ℳ^∨ ⟶ (ℳ')^∨` of duals of reflexive modules is the dual of
`ℳ' ⟶ (ℳ')^∨∨ ⟶ ℳ^∨∨ ⟶ ℳ`. No pairing computation is needed.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (i₂ : Z' ⟶ X') [IsImmersion i₂] (g' : Z' ⟶ Z)
  (sq : IsPullback i₂ g' f i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
  (hi₂ : i₂ ≫ (f ≫ sX) = sZ')

/-- For a cartesian square `Z' = Z ×_X X'` whose horizontal arrows `i : Z ⟶ X` and `i' : Z' ⟶ X'`
are regular immersions, and with `𝒦` the kernel of the surjection `g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of
Stacks 0473, assumed finite locally free, the restriction (Stacks 0F9Z) along `f : X' ⟶ X` of the
class of the normal bundle `𝒞_{Z/X}^∨` of `i`, carried to `Z'` along `Z ×_X X' ≅ Z'`, is
`c_top(𝒦^∨)` composed with the class of the normal bundle `𝒞_{Z'/X'}^∨` of `i'`, in
`A^*(Z' ⟶ X')^∧`. -/
theorem completedBivariantTransport_completedBivariantRestriction_ofIsRegularImmersion
    (hr : IsRegularImmersion i) (hr₂ : IsRegularImmersion i₂) (𝒦 : Z'.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒦]
    (e : 𝒦 ≅ kernel (Stacks.Immersion.immersionConormalSheafMap i₂ i g' f
      (Stacks.Immersion.toShHom_square sq.w))) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf 𝒦) :=
      isFiniteLocallyFree_dualSheaf_of_schemeOpens 𝒦 inferInstance
    completedBivariantTransport C (pullback.fst i f ≫ sZ) sZ' (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) i₂ hi₂ sq.flip.isoPullback.symm
        sq.flip.isoPullback_inv_snd
        (completedBivariantRestrictionViaSequence C sZ sX i hi f
          (completedVirtualNormalGysinClassOfImmersion C sZ sX i hi
            (VirtualNormalBundle.ofIsRegularImmersion i hr))) =
      completedBivariantGroup.copy C (Category.id_comp i₂) _ hi₂
        (completedBivariantCompositeOfInvertible C sZ' sZ' (f ≫ sX) (𝟙 Z') i₂
          (Category.id_comp sZ') hi₂ (topChernClassOfInvertible C sZ' (dualSheaf 𝒦))
          (completedVirtualNormalGysinClassOfImmersion C sZ' (f ≫ sX) i₂ hi₂
            (VirtualNormalBundle.ofIsRegularImmersion i₂ hr₂))) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  have hdual (F : Z'.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf F) :=
    isFiniteLocallyFree_dualSheaf_of_schemeOpens F inferInstance
  have hiso (F : Z'.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
      IsIso (toDoubleDual F) :=
    toDoubleDual_isIso_of_isFiniteLocallyFree F inferInstance
  let N := VirtualNormalBundle.ofIsRegularImmersion i hr
  let N' := VirtualNormalBundle.ofIsRegularImmersion i₂ hr₂
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf (conormalModule i₂)) :=
    N'.isFiniteLocallyFree
  let Nb := N.baseChange i i₂ g' f sq
  let c := Stacks.Immersion.immersionConormalSheafMap i₂ i g' f
    (Stacks.Immersion.toShHom_square sq.w)
  have : Epi c := Stacks.Immersion.epi_immersionConormalSheafMap i₂ i g' f sq
  -- `α : (g^*(𝒞^∨))^∨ ≅ g^*𝒞`, through which the surjection of `g^*(𝒞^∨)` is `g^*𝒞 ⟶ 𝒞'`
  let α : dualSheaf Nb.bundle ≅ (modulePullback g'.toLRSHom.toShHom).obj (conormalModule i) :=
    (@asIso _ _ _ _ (pullbackDualMap g' N.bundle)
        (pullbackDualMap_isIso g' N.bundle N.isFiniteLocallyFree)).symm ≪≫
      (modulePullback g'.toLRSHom.toShHom).mapIso (conormalReflexiveIso i hr).symm
  let δ' := conormalReflexiveIso i₂ hr₂
  have hsurj : Nb.surjection = α.hom ≫ c := (Category.assoc _ _ _).symm
  -- the kernel sequence `0 ⟶ 𝒦 ⟶ g^*𝒞 ⟶ 𝒞' ⟶ 0`, read through `α` and `𝒞' ≅ 𝒞'^∨∨`
  have hK : (ShortComplex.mk (kernel.ι c) c (kernel.condition c)).ShortExact :=
    { exact := ShortComplex.exact_kernel c }
  have hS₁ := shortExact_conjugate _ hK e.symm α.symm δ'
  let ψ : dualSheaf Nb.bundle ⟶ dualSheaf (dualSheaf (conormalModule i₂)) :=
    α.symm.inv ≫ c ≫ δ'.hom
  let a : 𝒦 ⟶ dualSheaf Nb.bundle := e.symm.inv ≫ kernel.ι c ≫ α.symm.hom
  -- its dual `0 ⟶ 𝒞'^∨∨∨ ⟶ (g^*(𝒞^∨))^∨∨ ⟶ 𝒦^∨ ⟶ 0`
  obtain ⟨w₂, hS₂⟩ := exists_dualSheaf_shortExact a ψ
    (conjugate_comp_conjugate_eq_zero (ShortComplex.mk (kernel.ι c) c (kernel.condition c))
      e.symm α.symm δ') hS₁.mono_f hS₁.epi_g hS₁.exact
    inferInstance inferInstance inferInstance
  -- the sequence `0 ⟶ 𝒞'^∨ ⟶ g^*(𝒞^∨) ⟶ 𝒦^∨ ⟶ 0`
  let S₂ := ShortComplex.mk (dualMap ψ) (dualMap a) w₂
  let β₁ := (asIso (toDoubleDual (dualSheaf (conormalModule i₂)))).symm
  let β₂ := (asIso (toDoubleDual Nb.bundle)).symm
  have hS₃ := shortExact_conjugate S₂ hS₂ β₁ β₂ (Iso.refl _)
  let inc : dualSheaf (conormalModule i₂) ⟶ Nb.bundle := β₁.inv ≫ dualMap ψ ≫ β₂.hom
  let pr : Nb.bundle ⟶ dualSheaf 𝒦 := β₂.inv ≫ dualMap a ≫ (Iso.refl (dualSheaf 𝒦)).hom
  have hdt : ∀ (F : Z'.Modules) [IsIso (toDoubleDual (dualSheaf F))],
      dualMap (toDoubleDual F) = inv (toDoubleDual (dualSheaf F)) := fun F _ =>
    IsIso.eq_inv_of_hom_inv_id (toDoubleDual_dualMap_comp F)
  have hinc : inc =
      toDoubleDual (dualSheaf (conormalModule i₂)) ≫ dualMap ψ ≫ inv (toDoubleDual Nb.bundle) := by
    simp only [inc, β₁, β₂, Iso.symm_inv, Iso.symm_hom, asIso_hom, asIso_inv]
  have hdi : dualMap inc = ψ := by
    have h0 : dualMap (toDoubleDual Nb.bundle) ≫ dualMap (inv (toDoubleDual Nb.bundle)) =
        𝟙 _ := by
      rw [← dualMap_comp, IsIso.inv_hom_id, dualMap_id]
    rw [hdt Nb.bundle, IsIso.inv_comp_eq, Category.comp_id] at h0
    rw [hinc]
    simp only [dualMap_comp, h0, hdt (dualSheaf (conormalModule i₂))]
    rw [← (show doubleDualMap ψ = dualMap (dualMap ψ) from rfl), ← toDoubleDual_naturality,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hsigma : dualMap inc ≫ N'.surjection = Nb.surjection := by
    rw [hdi, hsurj]
    change (α.hom ≫ c ≫ δ'.hom) ≫ δ'.inv = α.hom ≫ c
    exact (Category.assoc _ _ _).trans (congrArg (α.hom ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (c ≫ ·) δ'.hom_inv_id).trans (Category.comp_id _))))
  have h₁ :=
    completedBivariantTransport_completedBivariantRestriction_completedVirtualNormalGysinClass
      C sZ sX i hi i.coborderRange i.liftCoborder i.liftCoborder_ι f i₂ g' sq sZ' hi₂ N
      i₂.coborderRange i₂.liftCoborder i₂.liftCoborder_ι
  have h₂ := completedVirtualNormalGysinClassOfOpen_eq_of_isTopChernComposition C sZ' (f ≫ sX) i₂
    hi₂ i₂.coborderRange i₂.liftCoborder i₂.liftCoborder_ι Nb N' (dualSheaf 𝒦) inc pr
    (conjugate_comp_conjugate_eq_zero S₂ β₁ β₂ (Iso.refl _)) hS₃ hsigma
  exact h₁.trans h₂

end Stacks.Chow

end
