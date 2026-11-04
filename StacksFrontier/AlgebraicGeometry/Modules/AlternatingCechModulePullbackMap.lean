module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange

/-!
# The alternating Čech complex along a morphism over the base

Let `f : X ⟶ Spec A` and `f' : X' ⟶ Spec A` be schemes over the same affine base, let
`g : X' ⟶ X` be a morphism over `Spec A` (`g ≫ f = f'`), let `U : I → X.Opens` be a family of
opens and `U'` its inverse image (`U' i = g ⁻¹ᵁ U i`), and let `F` be an `𝒪_X`-module. Pulling
sections back along `g` defines a morphism of complexes of `A`-modules

`Č_alt(U, F) ⟶ Č_alt(U', g^* F)`,

`Stacks.Cech.alternatingCechModuleComplexPullbackMap`. It is the comparison
`Stacks.Cech.cochainBaseChange` of the base-change theory for the identity of `A`: commutation
with the differentials and preservation of alternating cochains are proved there for an arbitrary
morphism of schemes, and the base being fixed is what makes the comparison `A`-linear.

In the proof of the theorem of the cube this is the restriction of a Čech cochain of an invertible
module on `X ×_S Y` to the two faces `X ×_S y` and `x ×_S Y`.

## Main definitions

* `Stacks.Cech.alternatingCechModuleComplexPullbackMap`: the morphism of complexes.

## Main results

* `Stacks.Cech.baseRingHom_comp_app_of_comp`: the structural ring maps commute with `g`.
* `Stacks.Cech.alternatingCechModuleComplexPullbackMap_f_apply`: its value on a cochain.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (f' : X' ⟶ Spec (.of A)) (g : X' ⟶ X) (hg : g ≫ f = f')

include hg in
/-- The structural ring maps of two schemes over `Spec A` commute with a morphism over `Spec A`. -/
theorem baseRingHom_comp_app_of_comp (W : X.Opens) :
    baseRingHom f W ≫ g.app W = CommRingCat.ofHom (RingHom.id A) ≫ baseRingHom f' (g ⁻¹ᵁ W) := by
  subst hg
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Category.id_comp]
  simp only [baseRingHom, globalRingHom, Category.assoc, Scheme.Hom.comp_appTop]
  rw [g.naturality]
  rfl

variable {I : Type u} (U : I → X.Opens) (U' : I → X'.Opens) (hU' : ∀ i, U' i = g ⁻¹ᵁ U i)
  (F : X.Modules)

/-- Pulling back an alternating Čech cochain along a morphism over the base, as an `A`-linear
map. -/
def alternatingCochainPullbackₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
    alternatingSubmodule f U F p →ₗ[A]
      alternatingSubmodule f' U' ((Scheme.Modules.pullback g).obj F) p :=
  letI := cochainModule f U F p
  letI := cochainModule f' U' ((Scheme.Modules.pullback g).obj F) p
  { toFun := fun s ↦ ⟨cochainBaseChange g U U' (Equiv.refl I) F hU' p s.1,
      cochainBaseChange_isAlternating g U U' (Equiv.refl I) F hU' p s.1 s.2⟩
    map_add' := fun s t ↦ Subtype.ext (cochainBaseChange_add g U U' (Equiv.refl I) F hU' p s.1 t.1)
    map_smul' := fun a s ↦ Subtype.ext
      (cochainBaseChange_smul g U U' (Equiv.refl I) F hU' (RingHom.id A) f f'
        (baseRingHom_comp_app_of_comp f f' g hg) p a s.1) }

/-- The underlying cochain of the pullback of an alternating cochain `s` is the pullback
`cochainBaseChange` of the underlying cochain of `s`. -/
theorem alternatingCochainPullbackₗ_apply (p : ℕ) (s : alternatingCechModuleObj f U F p) :
    (alternatingCochainPullbackₗ f f' g hg U U' hU' F p s).1 =
      cochainBaseChange g U U' (Equiv.refl I) F hU' p s.1 := rfl

/-- The morphism of alternating Čech complexes `Č_alt(U, F) ⟶ Č_alt(U', g^* F)` of `A`-modules
given by pulling back sections along a morphism `g` over `Spec A`. -/
def alternatingCechModuleComplexPullbackMap :
    alternatingCechModuleComplex f U F ⟶
      alternatingCechModuleComplex f' U' ((Scheme.Modules.pullback g).obj F) :=
  CochainComplex.ofHom
    (fun p ↦ ModuleCat.ofHom (alternatingCochainPullbackₗ f f' g hg U U' hU' F p))
    (fun p ↦ by
      rw [alternatingCechModuleComplex_d, alternatingCechModuleComplex_d]
      ext s
      exact Subtype.ext (cochainBaseChange_cechD g U U' (Equiv.refl I) F hU' p s.1))

/-- In degree `p`, the morphism `alternatingCechModuleComplexPullbackMap` sends a cochain `s` to
the cochain whose underlying cochain is `cochainBaseChange` of the underlying cochain of `s`. -/
theorem alternatingCechModuleComplexPullbackMap_f_apply (p : ℕ)
    (s : (alternatingCechModuleComplex f U F).X p) :
    (((alternatingCechModuleComplexPullbackMap f f' g hg U U' hU' F).f p).hom s).1 =
      cochainBaseChange g U U' (Equiv.refl I) F hU' p s.1 := rfl

end Stacks.Cech

end

end
