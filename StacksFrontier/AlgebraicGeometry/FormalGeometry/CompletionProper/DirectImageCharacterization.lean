module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageAlgebraization
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison `(f_*𝓕)/𝒥ⁿ ⟶ f_*(𝓕/ℐⁿ𝓕)`, and the characterization of `α`

Let `f : X ⟶ Y` be a morphism of schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of ideals and
set `ℐ = f^{-1}𝒥 𝒪_X`. For a sheaf of `𝒪_X`-modules `𝓕` there is a canonical comparison

`δ_m : (f_*𝓕) / 𝒥 ᵐ (f_*𝓕) ⟶ f_*(𝓕 / ℐ ᵐ 𝓕)`,

because `𝒥 ᵐ (f_*𝓕)` is killed by the direct image of the projection `𝓕 ⟶ 𝓕/ℐ ᵐ 𝓕`. This file
builds it, and uses it to state the condition by which the proof of [Stacks, Tag 088B]
*characterizes* its map `α`, rather than constructing it.

## Why this is what Stacks 088B needs

The source's `α : (𝒢_n) ⟶ (f_*𝓕) ^∧` is pinned down by the requirement that each composite

`𝒢_n --α_n--> (f_*𝓕) / 𝒥 ⁿ (f_*𝓕) --δ_n--> f_*(𝓕 / ℐ ⁿ 𝓕)`

be the map `γ_n` of `Stacks.Coherent.directImageComparison`, and it is *that* description —
rather than any construction of `α` — which the source's first paragraph uses to make the
question local on `Y`, so that `Y` may be taken affine.

This library's `α` is `Stacks.Coherent.properDirectImageCompletionMap`, the completion of
`c : 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` read through an algebraization `e : (𝒢_n) ≅ 𝒢 ^∧`. A map presented
that way cannot be restricted to an open of `Y`, since an affine open of `Y` carries no
algebraization inherited from a global one. The predicate below replaces that presentation by the
source's own, and is stated levelwise exactly as the source states it ("each composite ... agrees
with `γ_n`").

## Main definitions

* `Stacks.Coherent.directImageQuotientComparison` — **the map `δ_m`.**
* `Stacks.Coherent.IsDirectImageCharacterized` — **the source's characterization of `α`**: the
  property of a morphism `α : (𝒢_n) ⟶ (f_*𝓕) ^∧` that `δ_n ∘ α_n = γ_n` at every level.

## Main results

* `Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap` — that `𝒥 ᵐ (f_*𝓕)` is
  killed by `f_*(𝓕 ⟶ 𝓕/ℐ ᵐ 𝓕)`, which is what makes `δ_m` exist. Proved for an **arbitrary**
  morphism of schemes.
* `Stacks.Coherent.directImageQuotientComparison_π` — the normalization of `δ_m`: it reads the
  direct image of the projection on `X` as a map out of the quotient on `Y`.

## Implementation notes

`Stacks.Algebraization.pushforwardAdicQuotientMap` is the same comparison for a **closed
immersion**, where it is moreover an isomorphism. Its construction of the map does not generalize:
it reads the ideal of `ℐ` on the preimage `i ⁻¹ U` of an affine open of `Y`, which is affine for a
closed immersion and is not affine for a general `f`. The proof below therefore checks the
inclusion `𝒥 ᵐ (f_*𝓕) ≤ Ker(f_*π)` by covering `f ⁻¹ U` with affine opens `V` of `X` and using
that `𝒥 ᵐ 𝓕`, being a subsheaf, satisfies the sheaf condition
(`AlgebraicGeometry.Scheme.Modules.Submodule.isSheaf`) — the locality step that
`Stacks.Algebraization.idealPowerMultiple_le_of_basis` performs for the ambient scheme. On such a
`V` the comorphism carries `𝒥(U) ᵐ` into `ℐ(V) ᵐ`, by
`Stacks.IdealSheaf.ideal_comap_appLE` and `Ideal.map_pow`.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### The comparison `(f_*𝓕)/𝒥ᵐ ⟶ f_*(𝓕/ℐᵐ𝓕)` -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`𝒥 ᵐ (f_*𝓕)` is killed by the direct image of the projection `𝓕 ⟶ 𝓕/ℐ ᵐ 𝓕`.**

The inclusion `𝒥 ᵐ (f_*𝓕) ≤ Ker(f_*π)` is checked on an affine open `U` of `Y`. A section of
`f_*𝓕` over `U` is a section of `𝓕` over `f ⁻¹ U`, which need not be affine, so the product
`r • x` with `r ∈ 𝒥(U) ᵐ` is shown to lie in `𝒥 ᵐ 𝓕` by the sheaf condition for that subsheaf:
on an affine open `V ⊆ f ⁻¹ U` the comorphism carries `𝒥(U) ᵐ` into `ℐ(V) ᵐ` by
`Stacks.IdealSheaf.ideal_comap_appLE`, and the affine opens contained in `f ⁻¹ U` cover it.

This is the unconditional fact which makes the comparison map of this file exist for an arbitrary
morphism of schemes. -/
public theorem idealPowerMultiple_pushforward_comp_eq_zero_of_comap
    (J : Y.IdealSheafData) (m : ℕ) (F : X.Modules) :
    (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι ≫
      (Scheme.Modules.pushforward f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι) = 0 := by
  rw [submodule_ι_comp_eq_zero_iff]
  refine (idealPowerMultiple_le_iff J m _ _).2 fun U => ?_
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  -- the kernel of the projection on `X` contains `ℐ ᵐ 𝓕`
  have hker := (submodule_ι_comp_eq_zero_iff (idealPowerMultiple (J.comap f) m F)
      (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι)).1
    (cokernel.condition (C := X.Modules) _)
  refine hker _ ?_
  -- the section lies in `ℐ ᵐ 𝓕` because it does so locally on `f ⁻¹ U`
  refine (idealPowerMultiple (J.comap f) m F).isSheaf _ ?_
  rw [Opens.mem_grothendieckTopology]
  intro z hz
  obtain ⟨W, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz (f ⁻¹ᵁ U.1).isOpen
  refine ⟨V, homOfLE hVU, ?_, hzV⟩
  -- on the affine open `V` the comorphism carries `𝒥(U) ᵐ` into `ℐ(V) ᵐ`
  have hmap : Ideal.map (f.appLE U.1 V hVU).hom (J.ideal U ^ m) =
      (J.comap f).ideal ⟨V, hV⟩ ^ m := by
    rw [Ideal.map_pow, Stacks.IdealSheaf.ideal_comap_appLE J f U ⟨V, hV⟩ hVU]
  -- the comorphism's value on `V`, spelled as the restriction of the value on `f ⁻¹ U`
  have hrV : (X.presheaf.map (homOfLE hVU).op).hom ((f.app U.1).hom r) ∈
      (J.comap f).ideal ⟨V, hV⟩ ^ m :=
    hmap ▸ Ideal.mem_map_of_mem (f.appLE U.1 V hVU).hom hr
  have hmem := Submodule.smul_le.mp
    (Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj (J.comap f) m F ⟨V, hV⟩)
    _ hrV (F.val.map (homOfLE hVU).op x) Submodule.mem_top
  -- restricting `r • x` to `V` is the action of the restricted scalar on the restriction
  exact Eq.mpr (congrArg
    (fun y => y ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (J.comap f) m F).toSubmodule.obj (op V))
    (F.val.map_smul (homOfLE hVU).op ((f.app U.1).hom r) x)) hmem

/-- **The comparison `δ_m : (f_*𝓕)/𝒥 ᵐ (f_*𝓕) ⟶ f_*(𝓕/ℐ ᵐ 𝓕)`**, for an arbitrary morphism of
schemes `f : X ⟶ Y`.

It is the map out of the quotient induced by the direct image of the projection
`𝓕 ⟶ 𝓕/ℐ ᵐ 𝓕`, which kills `𝒥 ᵐ (f_*𝓕)` by
`Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap`. -/
public def directImageQuotientComparison (J : Y.IdealSheafData) (m : ℕ) (F : X.Modules) :
    idealPowerQuotient J m ((Scheme.Modules.pushforward f).obj F) ⟶
      (Scheme.Modules.pushforward f).obj (idealPowerQuotient (J.comap f) m F) :=
  cokernel.desc (C := Y.Modules) _ _
    (idealPowerMultiple_pushforward_comp_eq_zero_of_comap f J m F)

/-- **The normalization of `δ_m`.** It reads the direct image of the projection on `X` as a map
out of the quotient on `Y`; the projection being an epimorphism, this determines `δ_m`. -/
@[simp]
public theorem directImageQuotientComparison_π (J : Y.IdealSheafData) (m : ℕ) (F : X.Modules) :
    cokernel.π (C := Y.Modules)
        (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι ≫
      directImageQuotientComparison f J m F =
    (Scheme.Modules.pushforward f).map
      (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι) :=
  cokernel.π_desc (C := Y.Modules) _ _ _

end Comparison

/-! ### The source's characterization of `α` -/

section Characterization

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData) (G : CoherentAdicSystems J)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)

/-- **The property by which the proof of Stacks 088B characterizes its map `α`.** A morphism

`α : (𝒢_n) ⟶ (f_*𝓕) ^∧`

of inverse systems of `𝒪_Y`-modules is *characterized* when, at every level `n`, the composite

`𝒢_n --α_n--> (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕) --δ_n--> f_*(𝓕 / ℐ ⁿ⁺¹ 𝓕)`

is the map `γ_n` of `Stacks.Coherent.directImageComparison`. The two `eqToHom`s are the object
formulas of Stacks 0880 (`Stacks.Algebraization.completionFunctor_obj`) and of the direct image
of a completion (`Stacks.Coherent.pushforward_completion_obj`), which identify the levels of the
two completions with the quotients that `δ` is stated between.

This is the source's own description of `α`, stated levelwise exactly as the source states it.
Unlike `Stacks.Coherent.properDirectImageCompletionMap` it mentions no algebraization of
`(𝒢_n)`, which is what makes it a condition that can be imposed over an open of `Y`. -/
public def IsDirectImageCharacterized
    (α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj) : Prop :=
  ∀ n : ℕ,
    α.app (op n) ≫ eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) ≫
        directImageQuotientComparison f J (n + 1) F.obj =
      (directImageComparison f J G F β).app (op n) ≫
        eqToHom (pushforward_completion_obj f J F n)

end Characterization

/-! ### The library's `α` satisfies the source's characterization -/

section CharacterizationOfConstruction

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (b : (Scheme.Modules.pullback f).obj 𝒢.obj ≅ F.obj)

/-- **The `α` this library constructs is the `α` the source characterizes.** Let the system be
the completion `𝒢 ^∧` of a coherent `𝒪_Y`-module, let `β : f^*(𝒢 ^∧) ≅ 𝓕 ^∧` be the source's
isomorphism, and let `b : f^*𝒢 ≅ 𝓕` descend `β` in the sense `hb`: that `b` followed by the
projection of `𝓕` onto the `n`-th term of its completion is the pullback of the projection of
`𝒢` followed by `β_n`. Then the library's map

`α = ` `Stacks.Coherent.properDirectImageCompletionMap` — the completion of
`c : 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` —

satisfies `Stacks.Coherent.IsDirectImageCharacterized`.

This is what makes the predicate of this file a *restatement* of Stacks 088B rather than a new
condition: the map the library already builds is the one the source pins down by its composites
with `Stacks.Coherent.directImageComparison`.

The proof cancels the epimorphism of Stacks 0880 and reads both sides out of `𝒢`. On the left,
`Stacks.Algebraization.completionFunctor_map_quotient` turns the completion of `c` into `c`
followed by a projection, and `Stacks.Coherent.directImageQuotientComparison_π` turns that
projection followed by `δ` into the direct image of the projection on `X`. On the right,
naturality of the unit of `f^* ⊣ f_*` moves the projection past the adjunction map. The two sides
then differ by exactly `hb`. -/
public theorem isDirectImageCharacterized_properDirectImageCompletionMap
    (β : (coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢) ≅
      (completionFunctor X (J.comap f)).obj F)
    (hb : ∀ n : ℕ, b.hom ≫ completionProjection X (J.comap f) F n =
      (Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n) ≫
        β.hom.hom.app (op n)) :
    IsDirectImageCharacterized f J ((completionFunctor Y J).obj 𝒢) F β
      (properDirectImageCompletionMap f J 𝒢 F b ((completionFunctor Y J).obj 𝒢)
        (Iso.refl _)) := by
  intro n
  -- the `α` of the library, with the identity algebraization
  have hα : properDirectImageCompletionMap f J 𝒢 F b ((completionFunctor Y J).obj 𝒢)
        (Iso.refl _) =
      ((completionFunctor Y J).map (properAdjunctionDescent f 𝒢 F b)).hom :=
    Category.id_comp _
  rw [hα]
  have hepi := Stacks.Algebraization.epi_completionProjection Y J 𝒢 n
  refine (@cancel_epi _ _ _ _ _ (completionProjection Y J 𝒢 n) hepi _ _).mp ?_
  -- a projection onto a level, read through the object formula of Stacks 0880
  have hπJ : completionProjection Y J (properPushforwardCoherent f F) n ≫
      eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) =
      cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι :=
    (Category.assoc (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι)
        (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n).symm)
        (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n))).trans
      ((congrArg (fun k => cokernel.π (C := Y.Modules)
            (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
  have hπI : cokernel.π (C := X.Modules)
      (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι =
      completionProjection X (J.comap f) F n ≫
        eqToHom (completionFunctor_obj X (J.comap f) F n) :=
    ((Category.assoc (cokernel.π (C := X.Modules)
            (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι)
          (eqToHom (completionFunctor_obj X (J.comap f) F n).symm)
          (eqToHom (completionFunctor_obj X (J.comap f) F n))).trans
      ((congrArg (fun k => cokernel.π (C := X.Modules)
            (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))).symm
  -- the direct image of a completion, levelwise, is the direct image of the `eqToHom`
  have heP : eqToHom (pushforward_completion_obj f J F n) =
      (Scheme.Modules.pushforward f).map
        (eqToHom (completionFunctor_obj X (J.comap f) F n)) :=
    (eqToHom_map (Scheme.Modules.pushforward f)
      (completionFunctor_obj X (J.comap f) F n)).symm
  -- the left side, read out of `𝒢`
  have hL : completionProjection Y J 𝒢 n ≫
      ((completionFunctor Y J).map (properAdjunctionDescent f 𝒢 F b)).hom.app (op n) ≫
        eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) ≫
          directImageQuotientComparison f J (n + 1) F.obj =
      (properAdjunctionDescent f 𝒢 F b).hom ≫
        (Scheme.Modules.pushforward f).map (cokernel.π (C := X.Modules)
          (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι) :=
    (Category.assoc _ _ _).symm.trans
      (((congrArg (fun z => z ≫ eqToHom (completionFunctor_obj Y J
              (properPushforwardCoherent f F) n) ≫
            directImageQuotientComparison f J (n + 1) F.obj)
          (completionFunctor_map_quotient Y J (properAdjunctionDescent f 𝒢 F b) n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (properAdjunctionDescent f 𝒢 F b).hom ≫ z)
              (Category.assoc _ _ _).symm).trans
            ((congrArg (fun z => (properAdjunctionDescent f 𝒢 F b).hom ≫
                z ≫ directImageQuotientComparison f J (n + 1) F.obj) hπJ).trans
              (congrArg (fun z => (properAdjunctionDescent f 𝒢 F b).hom ≫ z)
                (directImageQuotientComparison_π f J (n + 1) F.obj)))))))
  -- the right side, read out of `𝒢` by naturality of the unit
  have hR : completionProjection Y J 𝒢 n ≫
      (directImageComparison f J ((completionFunctor Y J).obj 𝒢) F β).app (op n) ≫
        eqToHom (pushforward_completion_obj f J F n) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj ≫
        (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).map
            (completionProjection Y J 𝒢 n) ≫
          (Scheme.Modules.pushforward f).map (β.hom.hom.app (op n)) ≫
            (Scheme.Modules.pushforward f).map
              (eqToHom (completionFunctor_obj X (J.comap f) F n)) :=
    (congrArg (fun z => completionProjection Y J 𝒢 n ≫
        z ≫ eqToHom (pushforward_completion_obj f J F n))
      (directImageComparison_app f J ((completionFunctor Y J).obj 𝒢) F β (op n))).trans
    ((congrArg (fun z => completionProjection Y J 𝒢 n ≫
          (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (((completionFunctor Y J).obj 𝒢).obj.obj (op n)) ≫
            (Scheme.Modules.pushforward f).map (β.hom.hom.app (op n)) ≫ z) heP).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map (β.hom.hom.app (op n)) ≫
              (Scheme.Modules.pushforward f).map
                (eqToHom (completionFunctor_obj X (J.comap f) F n)))
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
              (completionProjection Y J 𝒢 n))).trans
          (Category.assoc _ _ _))))
  -- the two sides differ by `hb`
  have hfinal : b.hom ≫ cokernel.π (C := X.Modules)
        (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι =
      (Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n) ≫
        β.hom.hom.app (op n) ≫ eqToHom (completionFunctor_obj X (J.comap f) F n) :=
    (congrArg (fun z => b.hom ≫ z) hπI).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ eqToHom (completionFunctor_obj X (J.comap f) F n))
            (hb n)).trans (Category.assoc _ _ _)))
  -- the direct images of the two composites agree
  have hmid : (Scheme.Modules.pushforward f).map b.hom ≫
        (Scheme.Modules.pushforward f).map (cokernel.π (C := X.Modules)
          (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι) =
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).map
          (completionProjection Y J 𝒢 n) ≫
        (Scheme.Modules.pushforward f).map (β.hom.hom.app (op n)) ≫
          (Scheme.Modules.pushforward f).map
            (eqToHom (completionFunctor_obj X (J.comap f) F n)) :=
    (Functor.map_comp (Scheme.Modules.pushforward f) b.hom
        (cokernel.π (C := X.Modules)
          (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι)).symm.trans
      ((congrArg (Scheme.Modules.pushforward f).map hfinal).trans
        ((Functor.map_comp (Scheme.Modules.pushforward f)
            ((Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n))
            (β.hom.hom.app (op n) ≫
              eqToHom (completionFunctor_obj X (J.comap f) F n))).trans
          (congrArg (fun z => (Scheme.Modules.pushforward f).map
                ((Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n)) ≫ z)
            (Functor.map_comp (Scheme.Modules.pushforward f) (β.hom.hom.app (op n))
              (eqToHom (completionFunctor_obj X (J.comap f) F n))))))
  refine hL.trans (hR.trans ?_).symm
  exact (congrArg (fun z =>
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj ≫ z) hmid.symm).trans
    ((Category.assoc ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj)
          ((Scheme.Modules.pushforward f).map b.hom)
          ((Scheme.Modules.pushforward f).map (cokernel.π (C := X.Modules)
            (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι))).symm.trans
      (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map (cokernel.π (C := X.Modules)
            (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι))
        (properAdjunctionDescent_hom f 𝒢 F b).symm))

end CharacterizationOfConstruction

end Stacks.Coherent

end
