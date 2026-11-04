module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections

/-!
# Global sections along a composite of morphisms of topoi

`MorphismOfTopoi.pushforwardTerminalHomEquiv` identifies the global sections of a direct image
`g_*E` with the global sections of `E`. The identification is compatible with composition:
given morphisms of topoi `φ : Sh(C) ⟶ Sh(D)`, `ψ : Sh(D) ⟶ Sh(E)` and `χ : Sh(C) ⟶ Sh(E)`
together with any natural transformation `τ : φ_* ⋙ ψ_* ⟶ χ_*`, going round through `ψ_*φ_*E`
and then applying `τ` gives the same global section of `E` as going through `χ_*E` directly. No
relation between `τ` and the inverse images is assumed.

## Main results

* `MorphismOfTopoi.hom_ext_pushforward_terminal`: two morphisms into the direct image of the
  terminal sheaf agree.
* `MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_eq`: the global section of `g_*E`
  corresponding to a global section `k` of `E` is `α ≫ g_*k` for any morphism `α : 1 ⟶ g_*1`.
* `MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_comp` and
  `MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans`: the compatibility with composition, in
  its inverse and its forward form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' w'' v u v' u' v'' u''

namespace MorphismOfTopoi

section Terminal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- Any two morphisms from a fixed sheaf into the direct image of the terminal sheaf agree. -/
theorem hom_ext_pushforward_terminal {A : Sheaf K (Type w')}
    (m n : A ⟶ g.pushforward.obj (⊤_ (Sheaf J (Type w)))) : m = n := by
  rw [← (g.adj.homEquiv A (⊤_ (Sheaf J (Type w)))).apply_symm_apply m,
    ← (g.adj.homEquiv A (⊤_ (Sheaf J (Type w)))).apply_symm_apply n]
  exact congrArg _ (Subsingleton.elim _ _)

/-- The global section of `g_*E` attached to a global section `k` of `E` is the direct image of
`k` precomposed with any morphism `α : 1 ⟶ g_*1`. -/
theorem pushforwardTerminalHomEquiv_symm_eq (E : Sheaf J (Type w))
    (k : ⊤_ (Sheaf J (Type w)) ⟶ E)
    (α : ⊤_ (Sheaf K (Type w')) ⟶ g.pushforward.obj (⊤_ (Sheaf J (Type w)))) :
    (g.pushforwardTerminalHomEquiv E).symm k = α ≫ g.pushforward.map k := by
  have h : (g.pushforwardTerminalHomEquiv E).symm k =
      g.adj.unit.app (⊤_ (Sheaf K (Type w'))) ≫
        g.pushforward.map ((inverseImageTerminalIso g).hom ≫ k) := by
    dsimp [pushforwardTerminalHomEquiv, Iso.homFromEquiv]
    rw [Adjunction.homEquiv_unit]
  rw [h, CategoryTheory.Functor.map_comp, ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ g.pushforward.map k)
    (hom_ext_pushforward_terminal g _ α)

end Terminal

section Composition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  {E : Type u''} [Category.{v''} E] {L : GrothendieckTopology E}
  (φ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (ψ : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
  (χ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf L (Type w'')))
  (τ : φ.pushforward ⋙ ψ.pushforward ⟶ χ.pushforward)

/-- For a global section `k` of `F`, the global section of `ψ_*φ_*F` it produces in two steps,
read through any natural transformation `τ : φ_* ⋙ ψ_* ⟶ χ_*`, is the global section of `χ_*F`
it produces in one. -/
theorem pushforwardTerminalHomEquiv_symm_comp (F : Sheaf J (Type w))
    (k : ⊤_ (Sheaf J (Type w)) ⟶ F) :
    (ψ.pushforwardTerminalHomEquiv (φ.pushforward.obj F)).symm
          ((φ.pushforwardTerminalHomEquiv F).symm k) ≫ τ.app F =
      (χ.pushforwardTerminalHomEquiv F).symm k := by
  set αφ := (φ.pushforwardTerminalHomEquiv (⊤_ (Sheaf J (Type w)))).symm (𝟙 _)
  set αψ := (ψ.pushforwardTerminalHomEquiv (⊤_ (Sheaf K (Type w')))).symm (𝟙 _)
  rw [pushforwardTerminalHomEquiv_symm_eq φ F k αφ,
    pushforwardTerminalHomEquiv_symm_eq ψ (φ.pushforward.obj F) _ αψ,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  have hnat : ψ.pushforward.map (φ.pushforward.map k) ≫ τ.app F =
      τ.app (⊤_ (Sheaf J (Type w))) ≫ χ.pushforward.map k := τ.naturality k
  simp only [hnat, pushforwardTerminalHomEquiv_symm_eq χ F k
    (αψ ≫ ψ.pushforward.map αφ ≫ τ.app (⊤_ (Sheaf J (Type w)))), Category.assoc]

/-- `MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_comp` read forwards: a global section of
`ψ_*φ_*F`, pushed through `τ` and read on `F` in one step, is what reading it on `F` in two
steps gives. -/
theorem pushforwardTerminalHomEquiv_natTrans (F : Sheaf J (Type w))
    (c : ⊤_ (Sheaf L (Type w'')) ⟶ ψ.pushforward.obj (φ.pushforward.obj F)) :
    χ.pushforwardTerminalHomEquiv F (c ≫ τ.app F) =
      φ.pushforwardTerminalHomEquiv F
        (ψ.pushforwardTerminalHomEquiv (φ.pushforward.obj F) c) := by
  have h := pushforwardTerminalHomEquiv_symm_comp φ ψ χ τ F
    (φ.pushforwardTerminalHomEquiv F
      (ψ.pushforwardTerminalHomEquiv (φ.pushforward.obj F) c))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  rw [h, Equiv.apply_symm_apply]

end Composition

end MorphismOfTopoi

end
