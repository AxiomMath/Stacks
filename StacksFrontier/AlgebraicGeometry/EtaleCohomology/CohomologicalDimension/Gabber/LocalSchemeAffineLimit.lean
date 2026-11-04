module

public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction

/-!
# The local scheme at a point as a directed limit of affine open neighbourhoods

Let `X` be a scheme, `η` a point of `X` and `V₀` an affine open neighbourhood of `η`. This file
reindexes `AlgebraicGeometry.isLimitSpecStalkCone` — `Spec 𝒪_{X,η}` is the limit of the affine
open neighbourhoods of `η` — to the directed preorder of the affine open neighbourhoods of `η`
contained in `V₀`, ordered by reverse inclusion, with least element `V₀`. This is the shape of
index the limit theorems for étale cohomology (Stacks 09YQ) are stated over. The diagram is
written as a diagram of objects of the small étale site of `X`, the opens `V ↦ (V ⟶ X)`.

## Main definitions

* `AlgebraicGeometry.Scheme.LocalAffineIndex η V₀`: the index preorder.
* `AlgebraicGeometry.Scheme.localAffineEtaleDiagram η V₀`: the diagram `V ↦ (V ⟶ X)` of étale
  `X`-schemes.
* `AlgebraicGeometry.Scheme.localAffineCone η V₀`: the cone with vertex `Spec 𝒪_{X,η}` on the
  underlying schemes.

## Main results

* `AlgebraicGeometry.Scheme.isLimitLocalAffineCone`: it is a limit cone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (η : X) (V₀ : AffineOpenNhds X η)

/-- The affine open neighbourhoods of `η` contained in `V₀`, ordered by reverse inclusion. -/
abbrev LocalAffineIndex : Type u :=
  {V : X.Opens // IsAffineOpen V ∧ η ∈ V ∧ V ≤ V₀.obj.1}ᵒᵈ

/-- Two affine open neighbourhoods of `η` in `V₀` contain a third. -/
instance : IsDirected (LocalAffineIndex η V₀) (· ≤ ·) := ⟨fun a b => by
  obtain ⟨W, hW, hηW, hWab⟩ := exists_isAffineOpen_mem_and_subset
    (show η ∈ (OrderDual.ofDual a).1 ⊓ (OrderDual.ofDual b).1 from
      ⟨(OrderDual.ofDual a).2.2.1, (OrderDual.ofDual b).2.2.1⟩)
  refine ⟨OrderDual.toDual ⟨W, hW, hηW, ?_⟩, ?_, ?_⟩
  · exact fun x hx => (OrderDual.ofDual a).2.2.2 (hWab hx).1
  · exact fun x hx => (hWab hx).1
  · exact fun x hx => (hWab hx).2⟩

/-- `V₀` itself is the least element of the index. -/
instance : OrderBot (LocalAffineIndex η V₀) where
  bot := OrderDual.toDual ⟨V₀.obj.1, V₀.property, V₀.obj.2, le_rfl⟩
  bot_le a := (OrderDual.ofDual a).2.2.2

/-- The index is nonempty: it contains `V₀`. -/
instance : Nonempty (LocalAffineIndex η V₀) := ⟨⊥⟩

/-- The inclusion of the index into the affine open neighbourhoods of `η`. -/
def localAffineIndexToNhds : (LocalAffineIndex η V₀)ᵒᵖ ⥤ AffineOpenNhds X η where
  obj i := ⟨⟨(OrderDual.ofDual i.unop).1, (OrderDual.ofDual i.unop).2.2.1⟩,
    (OrderDual.ofDual i.unop).2.1⟩
  map {i j} f := ObjectProperty.homMk (homOfLE (show (OrderDual.ofDual i.unop).1 ≤
    (OrderDual.ofDual j.unop).1 from leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The affine open neighbourhoods contained in `V₀` are initial among all affine open
neighbourhoods of `η`. -/
instance : (localAffineIndexToNhds η V₀).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun W => by
    obtain ⟨V, hV, hηV, hVW⟩ := exists_isAffineOpen_mem_and_subset
      (show η ∈ W.obj.1 ⊓ V₀.obj.1 from ⟨W.obj.2, V₀.obj.2⟩)
    exact ⟨op (OrderDual.toDual ⟨V, hV, hηV, fun x hx => (hVW hx).2⟩),
      ⟨ObjectProperty.homMk (homOfLE fun x hx => (hVW hx).1)⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, (affineOpenNhds X η).ι.map_injective (Subsingleton.elim _ _)⟩)

/-- **The diagram of the affine open neighbourhoods of `η` in `V₀`**, as étale `X`-schemes. -/
def localAffineEtaleDiagram : (LocalAffineIndex η V₀)ᵒᵖ ⥤ X.Etale :=
  localAffineIndexToNhds η V₀ ⋙ (affineOpenNhds X η).ι ⋙ OpenNhds.inclusion η ⋙ opensToEtale X

/-- The underlying diagram of schemes is the diagram of affine open neighbourhoods. -/
theorem localAffineEtaleDiagram_comp_forget :
    localAffineEtaleDiagram η V₀ ⋙ Scheme.Etale.forget X ⋙ Over.forget X =
      localAffineIndexToNhds η V₀ ⋙ affineOpenNhdsDiagram X η :=
  rfl

/-- **The cone with vertex `Spec 𝒪_{X,η}`** on the affine open neighbourhoods of `η` in `V₀`. -/
def localAffineCone :
    Cone (localAffineEtaleDiagram η V₀ ⋙ Scheme.Etale.forget X ⋙ Over.forget X) :=
  (specStalkCone X η).whisker (localAffineIndexToNhds η V₀)

/-- The vertex of `localAffineCone η V₀` is `Spec 𝒪_{X,η}`. -/
theorem localAffineCone_pt : (localAffineCone η V₀).pt = Spec (X.presheaf.stalk η) := rfl

/-- The leg of `localAffineCone η V₀` at `V` is the canonical morphism `Spec 𝒪_{X,η} ⟶ V`. -/
theorem localAffineCone_π_app (i : (LocalAffineIndex η V₀)ᵒᵖ) :
    (localAffineCone η V₀).π.app i =
      Scheme.Opens.fromSpecStalkOfMem (X := X) (OrderDual.ofDual i.unop).1 η
        (OrderDual.ofDual i.unop).2.2.1 :=
  rfl

/-- The legs of the cone followed by the structure morphisms are `X.fromSpecStalk η`. -/
theorem localAffineCone_π_app_comp (i : (LocalAffineIndex η V₀)ᵒᵖ) :
    (localAffineCone η V₀).π.app i ≫ ((localAffineEtaleDiagram η V₀).obj i).hom =
      X.fromSpecStalk η :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

/-- **`Spec 𝒪_{X,η}` is the limit of the affine open neighbourhoods of `η` in `V₀`.** -/
def isLimitLocalAffineCone : IsLimit (localAffineCone η V₀) :=
  (Functor.Initial.isLimitWhiskerEquiv (localAffineIndexToNhds η V₀) (specStalkCone X η)).symm
    (isLimitSpecStalkCone X η)

/-- Each scheme of the underlying diagram is affine. -/
instance isAffine_localAffineDiagram_obj (i : (LocalAffineIndex η V₀)ᵒᵖ) :
    IsAffine ((localAffineEtaleDiagram η V₀ ⋙ Scheme.Etale.forget X ⋙ Over.forget X).obj i) :=
  (OrderDual.ofDual i.unop).2.1

/-- Each étale `X`-scheme `V ⟶ X` of the diagram has affine source. -/
instance isAffine_localAffineEtaleDiagram_obj_left (i : (LocalAffineIndex η V₀)ᵒᵖ) :
    IsAffine ((localAffineEtaleDiagram η V₀).obj i).left :=
  (OrderDual.ofDual i.unop).2.1

/-- The transition morphisms of the underlying diagram are affine. -/
instance isAffineHom_localAffineDiagram_map {i j : (LocalAffineIndex η V₀)ᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((localAffineEtaleDiagram η V₀ ⋙ Scheme.Etale.forget X ⋙ Over.forget X).map a) :=
  inferInstance

/-- The transition morphisms of the étale diagram are affine on underlying schemes. -/
instance isAffineHom_localAffineEtaleDiagram_map_left {i j : (LocalAffineIndex η V₀)ᵒᵖ}
    (a : i ⟶ j) : IsAffineHom ((localAffineEtaleDiagram η V₀).map a).left :=
  isAffineHom_localAffineDiagram_map η V₀ a

end AlgebraicGeometry.Scheme

end
