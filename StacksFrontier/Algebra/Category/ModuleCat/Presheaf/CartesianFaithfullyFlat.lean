module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cartesian presheaves of modules: faithfully flat descent and restriction along a functor

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
it. `M` is *cartesian* over `g : Y ⟶ V` when the base-change comparison
`R(Y) ⊗_{R(V)} M(V) ⟶ M(Y)` is an isomorphism. This file proves that a linear map is bijective
when its base changes to the factors of a faithfully flat finite product are, which gives descent
of the cartesian condition along a finite family `q_i : Y_i ⟶ Y` whose rings form a faithfully
flat product over `R(Y)`, and it relates the cartesian condition for the restriction of a
presheaf of modules along a functor to the cartesian condition for the presheaf itself.

## Main results

* `Module.FaithfullyFlat.bijective_of_lTensor_pi`: a linear map is bijective when its base changes
  to the factors of a faithfully flat finite product are.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_presheafPushforward_iff` and
  `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso_presheafPushforward`: the
  comparison of the restriction of a presheaf of modules along a functor is that of the presheaf
  itself along the image morphism.

## Implementation notes

The restriction along a functor `G` is taken over a presheaf of rings `S` with a proof
`S = G.op ⋙ O`, and its structure map is `eqToHom` of that proof.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u r m w u₁ v₁ u₂ v₂

namespace Module.FaithfullyFlat

/-- A linear map is bijective as soon as its base changes to the factors of a faithfully flat
finite product are. -/
@[ega "0 6.4.1" "more general", ega "IV 2.5.8.7" "more general"]
theorem bijective_of_lTensor_pi {A : Type*} [CommRing A] {ι : Type*} [Finite ι]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)] [∀ i, Module A (B i)]
    [Module.FaithfullyFlat A (∀ i, B i)] {N N' : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (φ : N →ₗ[A] N')
    (h : ∀ i, Function.Bijective (φ.lTensor (B i))) : Function.Bijective φ := by
  classical
  have := Fintype.ofFinite ι
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A (∀ i, B i) φ]
  let eN := TensorProduct.piLeft A N B
  let eN' := TensorProduct.piLeft A N' B
  have key : ∀ x, eN' (φ.lTensor (∀ i, B i) x) = fun i => φ.lTensor (B i) (eN x i) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b n => funext i; simp [eN, eN']
    | add x y hx hy => funext i; simp only [map_add, Pi.add_apply, hx, hy]
  have hpi : Function.Bijective (fun (x : ∀ i, B i ⊗[A] N) i => φ.lTensor (B i) (x i)) :=
    ⟨fun x y hxy => funext fun i => (h i).1 (congrFun hxy i),
      fun y => ⟨fun i => ((h i).2 (y i)).choose, funext fun i => ((h i).2 (y i)).choose_spec⟩⟩
  have hc : (φ.lTensor (∀ i, B i)) = eN'.symm ∘ (fun x i => φ.lTensor (B i) (x i)) ∘ eN := by
    funext x
    apply eN'.injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
    exact key x
  rw [hc]
  exact eN'.symm.bijective.comp (hpi.comp eN.bijective)

end Module.FaithfullyFlat

namespace Stacks.PresheafOfModules

/-- The base-change comparison of the restriction of a presheaf of modules along a functor is an
isomorphism if and only if that of the presheaf itself along the image morphism is. -/
theorem isIso_restrictionBaseChange_presheafPushforward_iff {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) (O : Dᵒᵖ ⥤ RingCat.{w}) (S : Cᵒᵖ ⥤ RingCat.{w})
    (hS : S = G.op ⋙ O) [Stacks.TerminalBaseChange.CommSections O]
    [Stacks.TerminalBaseChange.CommSections S]
    (M : PresheafOfModules.{w} O) {X Y : C} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{_, _, w, w} (R := Stacks.TerminalBaseChange.commPresheaf S)
      ((PresheafOfModules.pushforward (F := G) (R := O) (eqToHom hS)).obj M) f.op) ↔
    IsIso (restrictionBaseChange.{_, _, w, w} (R := Stacks.TerminalBaseChange.commPresheaf O) M
      (G.map f).op) := by
  subst hS
  exact Iff.rfl

/-- A presheaf of modules isomorphic to the restriction of `M` along a functor is cartesian over
every morphism whose image `M` is cartesian over. -/
theorem isIso_restrictionBaseChange_of_iso_presheafPushforward {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) (O : Dᵒᵖ ⥤ RingCat.{w}) (S : Cᵒᵖ ⥤ RingCat.{w})
    (hS : S = G.op ⋙ O) [Stacks.TerminalBaseChange.CommSections O]
    [Stacks.TerminalBaseChange.CommSections S]
    (M : PresheafOfModules.{w} O) (N : PresheafOfModules.{w} S)
    (e : N ≅ (PresheafOfModules.pushforward (F := G) (R := O) (eqToHom hS)).obj M) {X Y : C}
    (f : X ⟶ Y)
    (h : IsIso (restrictionBaseChange.{_, _, w, w} (R := Stacks.TerminalBaseChange.commPresheaf O)
      M (G.map f).op)) :
    IsIso (restrictionBaseChange.{_, _, w, w} (R := Stacks.TerminalBaseChange.commPresheaf S)
      N f.op) := by
  have h' := (isIso_restrictionBaseChange_presheafPushforward_iff G O S hS M f).2 h
  exact isIso_restrictionBaseChange_of_iso e.symm f.op

end Stacks.PresheafOfModules

end
