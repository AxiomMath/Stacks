module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardPreservesModuleSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras

/-!
# Pushforward along a closed embedding commutes with sheafification of modules

Let `f : Z ⟶ X` be a closed embedding of topological spaces. The preimage functor
`Opens.map f : Opens X ⥤ Opens Z` is not cocontinuous in general (an open of `X` disjoint from
the image of `f` is covered on `Z` by the empty family), but whiskering along it still preserves
local injectivity and local surjectivity of a morphism of presheaves whose source, respectively
target, is trivial on the empty open. Presheaves of modules over a sheaf of rings are trivial on
the empty open, so pushforward along `f` commutes with sheafification of presheaves of modules.

## Main results

* `Stacks.ClosedImmersion.isLocallyInjective_whisker_opensMap` and
  `Stacks.ClosedImmersion.isLocallySurjective_whisker_opensMap`: whiskering along `Opens.map f`
  preserves local injectivity of a morphism whose source has at most one section over the empty
  open, and local surjectivity of one which is surjective over the empty open.
* `Stacks.ClosedImmersion.preservesModuleSheafification_opensMap`: `Opens.map f` is compatible
  with sheafification of presheaves of modules over any sheaf of rings on `Z`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Topology

universe w' v' u' u

namespace Stacks.ClosedImmersion

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
  {X Z : TopCat.{u}} (f : Z ⟶ X) (hf : IsClosedEmbedding f)
  {F G : (Opens Z)ᵒᵖ ⥤ A} (φ : F ⟶ G)

/-- The open complement of the image of a closed embedding. -/
def complRange : Opens X := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩

include hf in
/-- Every open of `X` is covered by the opens which are disjoint from the image of `f` or are
contained in an open `V` whose preimage lies in a given covering sieve of the preimage. -/
theorem mem_grothendieckTopology_of_opensMap {U : Opens X} (S : Sieve U)
    (T : Sieve ((Opens.map f).obj U)) (hT : T ∈ Opens.grothendieckTopology Z _)
    (h₁ : ∀ (V : Opens X) (i : V ⟶ U), (Opens.map f).obj V = ⊥ → S i)
    (h₂ : ∀ (V : Opens X) (i : V ⟶ U), T ((Opens.map f).map i) → S i) :
    S ∈ Opens.grothendieckTopology X U := by
  intro x hx
  by_cases hxr : x ∈ Set.range f
  · obtain ⟨z, rfl⟩ := hxr
    obtain ⟨W, g, hg, hzW⟩ := hT z hx
    obtain ⟨V', hV', hW⟩ := hf.isInducing.isOpen_iff.mp W.isOpen
    have hle : (Opens.map f).obj (⟨V', hV'⟩ ⊓ U) ≤ W := fun y hy ↦ by
      show y ∈ (W : Set Z); rw [← hW]; exact hy.1
    refine ⟨⟨V', hV'⟩ ⊓ U, homOfLE inf_le_right, h₂ _ _ ?_, ?_, hx⟩
    · convert T.downward_closed hg (homOfLE hle) using 1
      exact Subsingleton.elim _ _
    · show z ∈ f ⁻¹' V'
      rwa [hW]
  · refine ⟨complRange f hf ⊓ U, homOfLE inf_le_right, h₁ _ _ ?_, hxr, hx⟩
    ext z
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hz ↦ hz.1 ⟨z, rfl⟩

include hf in
/-- **Whiskering along the preimage functor of a closed embedding preserves local injectivity**
of a morphism of presheaves whose source has at most one section over the empty open. -/
theorem isLocallyInjective_whisker_opensMap
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Z) φ]
    (h : ∀ x y : ToType (F.obj (op ⊥)), x = y) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft (Opens.map f).op φ) where
  equalizerSieve_mem {U} x y hxy := by
    exact mem_grothendieckTopology_of_opensMap f hf _ _
      (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Z) φ x y hxy)
      (fun _ _ hV ↦ by rw [← hV] at h; exact h _ _) (fun _ _ hi ↦ hi)

include hf in
/-- **Whiskering along the preimage functor of a closed embedding preserves local
surjectivity** of a morphism of presheaves which is surjective over the empty open. -/
theorem isLocallySurjective_whisker_opensMap
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z) φ]
    (h : ∀ y : ToType (G.obj (op ⊥)), ∃ x : ToType (F.obj (op ⊥)), φ.app _ x = y) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft (Opens.map f).op φ) where
  imageSieve_mem {U} s := by
    exact mem_grothendieckTopology_of_opensMap f hf _ _
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology Z) φ s)
      (fun _ _ hV ↦ by rw [← hV] at h; exact h _) (fun _ _ hi ↦ hi)

omit [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA] in
/-- A sheaf on a topological space with values in a concrete category whose forgetful functor
preserves terminal objects has at most one section over the empty open. -/
theorem subsingleton_obj_bot {B : Type u'} [Category.{v'} B] {FB : B → B → Type*}
    {CB : B → Type w'} [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory.{w'} B FB]
    [Limits.PreservesLimit (Functor.empty.{0} B) (forget B)]
    (P : Sheaf (Opens.grothendieckTopology Z) B) : Subsingleton (ToType (P.obj.obj (op ⊥))) :=
  ((Limits.Types.isTerminalEquivUnique _)
    ((P.isTerminalOfBotCover ⊥ (fun _ h => h.elim)).isTerminalObj (forget B) _)).instSubsingleton

omit [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA] in
include hf in
/-- **Pushforward along a closed embedding is compatible with sheafification of presheaves of
modules** over a sheaf of rings on the source. -/
theorem preservesModuleSheafification_opensMap
    (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) :
    Stacks.SheafOfModules.PushforwardSheafification.PreservesModuleSheafification.{u}
      (Opens.grothendieckTopology X) (Opens.map f) R where
  isLocallyInjective P := by
    have : Subsingleton (R.obj.obj (op ⊥)) := subsingleton_obj_bot R
    exact isLocallyInjective_whisker_opensMap f hf _ fun a b ↦
      (Module.subsingleton (R.obj.obj (op ⊥)) (P.obj (op ⊥))).elim a b
  isLocallySurjective P := by
    have := subsingleton_obj_bot
      ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj P.presheaf)
    exact isLocallySurjective_whisker_opensMap f hf _ fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end Stacks.ClosedImmersion
