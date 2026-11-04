module

public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.InternalHomInjectiveComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of the internal Hom into an injective module

Let `(X, 𝒪_X)` be a ringed space, `A` an `𝒪_X`-module and `I` an injective `𝒪_X`-module. The
sections of `𝓗om(A, I)` over an open `U` are the morphisms `A|_U ⟶ I|_U`. Every such morphism
is the restriction of a morphism `A ⟶ I`, extended by zero away from `U` (see
`Stacks.SupportedExtension.exists_extension_of_injective`). Two consequences are recorded here:

* the global sections of `𝓗om(A, I)` are the morphisms `A ⟶ I`;
* `𝓗om(A, I)` is flasque.

## Main definitions

* `Stacks.SheafHomInjective.sectionOf`: the section of `𝓗om(A, I)` over `U` given by a morphism
  `A ⟶ I`.

## Main results

* `Stacks.SheafHomInjective.sectionOf_top_injective` and
  `Stacks.SheafHomInjective.sectionOf_top_surjective`: morphisms `A ⟶ I` are global sections.
* `Stacks.SheafHomInjective.isFlasque_toSheaf_internalHom`: the underlying abelian sheaf of
  `𝓗om(A, I)` is flasque.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.InternalHom Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.SheafHomInjective

variable {X : Type u} [TopologicalSpace X]
    {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The section of `𝓗om(A, I)` over `U` given by a morphism `A ⟶ I`. -/
abbrev sectionOf {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (U : Opens X)
    (g : A ⟶ I) : ((SH O A).obj I).val.obj (op U) :=
  (restrFun O.obj U).map g.val

/-- The restriction of `sectionOf U g` to `V ⊆ U` is `sectionOf V g`. -/
theorem map_sectionOf {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {U V : Opens X} (h : V ≤ U) (g : A ⟶ I) :
    ((SH O A).obj I).val.map (homOfLE h).op (sectionOf U g) = sectionOf V g :=
  rfl

/-- `sectionOf` is natural in the target. -/
theorem sectionOf_comp {A I I' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (U : Opens X) (g : A ⟶ I) (k : I ⟶ I') :
    sectionOf U (g ≫ k) = ((SH O A).map k).val.app (op U) (sectionOf U g) :=
  rfl

/-- A section over `W` of `𝓗om(A, I)` is `sectionOf W ψ` for any `ψ : A ⟶ I` agreeing with it
on the opens of `W`. -/
theorem sectionOf_eq_of_agree {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {W : Opens X} (β : ((SH O A).obj I).val.obj (op W)) (ψ : A ⟶ I)
    (hψ : ∀ (V : Opens X) (hV : V ≤ W) (s : A.val.obj (op V)),
      ψ.val.app (op V) s = β.app (op (Over.mk (homOfLE hV))) s) :
    sectionOf W ψ = β :=
  PresheafOfModules.hom_ext fun Z => ModuleCat.hom_ext <| LinearMap.ext fun x =>
    hψ Z.unop.left (leOfHom Z.unop.hom) x

/-- Every section over `W` of `𝓗om(A, I)` with `I` injective is `sectionOf W ψ` for a morphism
`ψ : A ⟶ I`. -/
theorem exists_sectionOf_eq {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    [Injective I] {W : Opens X} (β : ((SH O A).obj I).val.obj (op W)) :
    ∃ ψ : A ⟶ I, sectionOf W ψ = β := by
  let R' := (Stacks.SheafOfModules.Tensor.ringSheaf O).over W
  let φ : A.over W ⟶ I.over W := (SheafOfModules.fullyFaithfulForget R').preimage β
  have hφ : φ.val = β := (SheafOfModules.fullyFaithfulForget R').map_preimage (X := A.over W)
    (Y := I.over W) β
  obtain ⟨ψ, hψ⟩ := Stacks.SupportedExtension.exists_extension_of_injective A I W φ
  refine ⟨ψ, sectionOf_eq_of_agree β ψ fun V hV s => ?_⟩
  rw [hψ V hV s, hφ]
  rfl

/-- Morphisms `A ⟶ I` are determined by their global section of `𝓗om(A, I)`. -/
theorem sectionOf_top_injective
    {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} :
    Function.Injective (sectionOf (A := A) (I := I) ⊤) := fun _ _ h =>
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun V =>
    congrArg (fun α : (restrFun O.obj ⊤).obj A.val ⟶ (restrFun O.obj ⊤).obj I.val =>
      α.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))) h

/-- Every global section of `𝓗om(A, I)` with `I` injective is a morphism `A ⟶ I`. -/
theorem sectionOf_top_surjective
    {A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} [Injective I] :
    Function.Surjective (sectionOf (A := A) (I := I) ⊤) :=
  fun β => exists_sectionOf_eq β

/-- **The internal Hom into an injective module is flasque.** -/
@[sga "2 VI 1.5", sga "4 V 4.10" "special case"]
theorem isFlasque_toSheaf_internalHom
    (A I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) [Injective I] :
    TopCat.Sheaf.IsFlasque (X := TopCat.of X)
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
        ((SH O A).obj I)) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro β
    obtain ⟨ψ, rfl⟩ := exists_sectionOf_eq (A := A) (I := I) (W := V.unop) β
    exact ⟨sectionOf U.unop ψ, map_sectionOf (O := O) (leOfHom i.unop) ψ⟩

end Stacks.SheafHomInjective

end
