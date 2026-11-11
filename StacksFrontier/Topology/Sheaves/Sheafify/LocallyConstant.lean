module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sheaves.LocalPredicate
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of the constant presheaf is the constant sheaf (Stacks tag 0081)

Let `X` be a topological space and `A` a set. Write `A_p` for the constant presheaf with value
`A` and `A̲` for the constant sheaf with value `A` of Stacks 006W, the sheaf assigning to an open
`U ⊆ X` the set of locally constant maps `U → A`, with restriction of functions as restriction
maps. Stacks 0081 (Example 6.17.4) asserts that the map `A_p → A̲`, sending `a` to the constant
function with value `a`, induces an isomorphism `A_p^# → A̲`.

* `TopCat.isLocallyConstantLocal X A` is the local predicate "is locally constant" on
  functions `U → A`, and `TopCat.locallyConstantSheaf X A` the sheaf `A̲` it cuts out
  (a subsheaf of the sheaf of all functions to `A`).
* `TopCat.constantPresheafToLocallyConstant X A : A_p ⟶ A̲` is the canonical map.
* `TopCat.isIso_sheafifyLift_constantPresheafToLocallyConstant` (Stacks 0081) proves that the
  induced map `sheafifyLift : sheafify J A_p ⟶ A̲` is an isomorphism, for
  `J = Opens.grothendieckTopology X`; `TopCat.sheafifyConstantPresheafIsoLocallyConstantSheaf`
  packages it as an isomorphism. The proof shows that `A_p ⟶ A̲` is locally injective and
  locally surjective, hence becomes an isomorphism after sheafification.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

universe u

open TopologicalSpace Opposite

variable (X : TopCat.{u}) (A : Type u)

/-- Being locally constant is a local predicate on maps `U → A` from the opens `U` of `X`. -/
def isLocallyConstantLocal : LocalPredicate fun _ : X ↦ A where
  pred {_} f := IsLocallyConstant f
  res {_ _} i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f w := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨V, hxV, i, hV⟩ := w x
    have h := (IsLocallyConstant.iff_eventually_eq _).1 hV ⟨x, hxV⟩
    have e := (Opens.isOpenEmbedding_of_le i.le).map_nhds_eq ⟨x.1, hxV⟩
    rw [show x = Set.inclusion (SetLike.coe_subset_coe.2 i.le) ⟨x.1, hxV⟩ from rfl, ← e]
    exact Filter.eventually_map.2 h

/-- The constant sheaf `A̲` with value `A` (Stacks 006W): the sheaf assigning to an open
`U ⊆ X` the set of locally constant maps `U → A`, with restriction of functions as restriction
maps. -/
noncomputable def locallyConstantSheaf : TopCat.Sheaf (Type u) X :=
  subsheafToTypes (isLocallyConstantLocal X A)

/-- The canonical map `A_p ⟶ A̲` from the constant presheaf with value `A` to the sheaf of
locally constant maps, sending `a ∈ A_p(U) = A` to the constant map `U → A` with value `a`. -/
noncomputable def constantPresheafToLocallyConstant :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ (locallyConstantSheaf X A).obj where
  app _ := ↾fun a ↦ ⟨fun _ ↦ a, IsLocallyConstant.const a⟩

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (constantPresheafToLocallyConstant X A) where
  equalizerSieve_mem {U} a b h := by
    intro x hx
    have hab : a = b :=
      congrArg (fun s : {f : ∀ y : U.unop, A // IsLocallyConstant f} ↦ s.1 ⟨x, hx⟩) h
    exact ⟨U.unop, 𝟙 _, hab, hx⟩

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (constantPresheafToLocallyConstant X A) where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨f, hf⟩ := s
    let W : Opens X := ⟨Subtype.val '' (f ⁻¹' {f ⟨x, hx⟩}), U.isOpen.isOpenMap_subtype_val _ (hf _)⟩
    have hWU : W ≤ U := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    refine ⟨W, homOfLE hWU, ⟨f ⟨x, hx⟩, ?_⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
    refine Subtype.ext (funext fun y ↦ ?_)
    obtain ⟨z, hz, hzy⟩ := y.2
    have : (⟨y.1, hWU y.2⟩ : U) = z := Subtype.ext hzy.symm
    change f ⟨x, hx⟩ = f ⟨y.1, hWU y.2⟩
    rw [this]
    exact hz.symm

/-- **Stacks 0081** (Example 6.17.4). Let `X` be a topological space and `A` a set. The map
`A_p ⟶ A̲` from the constant presheaf with value `A` to the constant sheaf with value `A`
(the sheaf of locally constant maps to `A`) induces an isomorphism `A_p^# ⟶ A̲`: the
sheafification of the constant presheaf with value `A` is the constant sheaf with value `A`. -/
@[stacks 0081]
theorem isIso_sheafifyLift_constantPresheafToLocallyConstant :
    IsIso (sheafifyLift (Opens.grothendieckTopology X) (constantPresheafToLocallyConstant X A)
      (locallyConstantSheaf X A).property) := by
  set J := Opens.grothendieckTopology X
  set η := constantPresheafToLocallyConstant X A
  have hW : J.W (sheafifyLift J η (locallyConstantSheaf X A).property) := by
    rw [J.W_iff]
    have h₁ := (J.W_iff _).1 (J.W_of_isLocallyBijective η)
    have h₂ := (J.W_iff _).1 (J.W_toSheafify ((Functor.const (Opens X)ᵒᵖ).obj A))
    rw [← toSheafify_sheafifyLift J η (locallyConstantSheaf X A).property,
      Functor.map_comp] at h₁
    exact IsIso.of_isIso_comp_left
      ((presheafToSheaf J (Type u)).map (toSheafify J ((Functor.const (Opens X)ᵒᵖ).obj A))) _
  let φ := ((sheafificationAdjunction J (Type u)).homEquiv _ (locallyConstantSheaf X A)).symm η
  have : IsIso φ := (J.W_sheafToPresheaf_map_iff_isIso φ).1 hW
  exact Functor.map_isIso (sheafToPresheaf J (Type u)) φ

/-- The isomorphism `A_p^# ≅ A̲` of Stacks 0081, from the sheafification of the constant presheaf
with value `A` to the sheaf of locally constant maps to `A`, induced by
`constantPresheafToLocallyConstant`. -/
noncomputable def sheafifyConstantPresheafIsoLocallyConstantSheaf :
    sheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≅
      (locallyConstantSheaf X A).obj :=
  haveI := isIso_sheafifyLift_constantPresheafToLocallyConstant X A
  asIso (sheafifyLift _ (constantPresheafToLocallyConstant X A) (locallyConstantSheaf X A).property)

/-- The isomorphism `sheafifyConstantPresheafIsoLocallyConstantSheaf` is induced by
`constantPresheafToLocallyConstant`: precomposed with the sheafification unit it gives back
`constantPresheafToLocallyConstant`. -/
lemma toSheafify_comp_sheafifyConstantPresheafIsoLocallyConstantSheaf_hom :
    toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
        (sheafifyConstantPresheafIsoLocallyConstantSheaf X A).hom =
      constantPresheafToLocallyConstant X A :=
  toSheafify_sheafifyLift _ _ _

end TopCat
