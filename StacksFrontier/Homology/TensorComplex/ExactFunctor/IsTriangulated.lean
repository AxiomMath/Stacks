module

public import StacksFrontier.Homology.TensorComplex.ExactFunctor.LeftMappingCone
public import StacksFrontier.Homology.TensorComplex.ExactFunctor.RightMappingCone
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring with a fixed complex is a triangulated functor (Stacks Tag 06Y8)

`main_left` and `main_right`: `Tleft G` and `Tright G`, with their `CommShift ℤ` data, are
exact functors of triangulated categories on `K(C)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

/-- **Statement 1.**  For a fixed complex `G`, the functor
`Tleft G : F ↦ Tot(G ⊗ F)` on `K(Mod(O_X))` can be equipped with a functorial isomorphism
`ξ` (a `CommShift ℤ` datum) making it an *exact functor of triangulated categories* (Stacks
Tag 06Y8, left version).

Here `ξ` is the canonical comparison isomorphism `Tot(G ⊗ F[1]) ≅ Tot(G ⊗ F)[1]` of Stacks
Tag 0FNG, and `Functor.IsTriangulated` packages exactly the requirement of Definition 3: the
`CommShift` natural isomorphism together with preservation of distinguished triangles.

Note the descent of the functor to `K(Mod(O_X))` is *asserted as content* (via `Tleft`,
which is built from `TleftCochain_preservesHomotopyRel`), not assumed as a hypothesis. -/
@[stacks 06Y8, sga "4 XVII 7.3.3" "special case"]
theorem main_left (G : CochainComplex C ℤ) :
    ∃ e : (Tleft G).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (Tleft G) e _ _ _ _ _ _ _ _ := by
  refine ⟨TleftCommShift G, ?_⟩
  let := TleftCommShift G
  exact ⟨fun T hT => Tleft_mapTriangle_distinguished G T hT⟩

/-- **Statement 2.**  For a fixed complex `G`, the functor
`Tright G : F ↦ Tot(F ⊗ G)` on `K(Mod(O_X))` can be equipped with a functorial isomorphism
`ξ` making it an exact functor of triangulated categories (Stacks Tag 06Y8, right version).
This is genuinely distinct from `main_left` (the two differ by the commutativity isomorphism
with its sign `(-1)^{pq}`). -/
@[stacks 06Y8, sga "4 XVII 7.3.3" "special case"]
theorem main_right (G : CochainComplex C ℤ) :
    ∃ e : (Tright G).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (Tright G) e _ _ _ _ _ _ _ _ := by
  refine ⟨TrightCommShift G, ?_⟩
  let := TrightCommShift G
  exact ⟨fun T hT => Tright_mapTriangle_distinguished G T hT⟩
