module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem.DerivedCompositorAssoc
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian simplicial systems of modules from a cocycle isomorphism (Stacks 0GMF)

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. **Stacks 0GMF**: an object `K₀` of the derived category of `O_0`-modules on the
degree-zero component together with an isomorphism `α : Lf_{δ¹₁}^* K₀ ≅ Lf_{δ¹₀}^* K₀` on the
degree-one component satisfying the cocycle condition on the degree-two component determines a
*cartesian* simplicial system of the derived category of modules (Stacks 0D9N), whose object in
degree `n` is `K_n = Lf_{τⁿₙ}^* K₀`, the derived pullback of `K₀` along the last vertex of `⦋n⦌`.

The construction follows the source. A pair `(K₀, α)` assigns to every pair of vertices `i ≤ j`
of `⦋n⦌` a comparison `derivedModuleEdgeTransport` between the derived pullbacks of `K₀` along
them, obtained by pulling `α` back along the edge joining them; the cocycle condition says exactly
that these comparisons compose (`derivedModuleEdgeTransport_comp`), and the transition of the
system at `φ : m ⟶ n` pulls back to the image of the last vertex of `⦋m⦌` and then transports
along the edge from there to the last vertex of `⦋n⦌`. The coherence input, the cocycle law for
the compositor of derived pullbacks, is
the sibling file `DerivedCocycleSystem/DerivedCompositorAssoc.lean`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.DerivedModuleCocyclePair`: the pair `(K₀, α)` with its
  cocycle condition, the input datum of Stacks 0GMF.
* `CategoryTheory.SimplicialSiteSituation.pairDerivedModuleSystem`: **Stacks 0GMF**, the simplicial
  system it determines.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleEdgeTransport`: the comparison between the
  derived pullbacks of `K₀` along two vertices of `⦋n⦌` joined by an edge, obtained from `α`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.pairDerivedModuleSystem_obj`: **Stacks 0GMF**, the object
  of
  the system in degree `n` is `Lf_{τⁿₙ}^* K₀`.
* `CategoryTheory.SimplicialSiteSituation.pairDerivedModuleSystem_cartesian`: **Stacks 0GMF**, the
  system is cartesian — every transition map is invertible, for every simplex map and not only
  for the faces.
* `CategoryTheory.SimplicialSiteSituation.pairDerivedModuleTransition_comp`: the cocycle condition
  of Stacks 0D9N for the transitions of the system.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleEdgeTransport_comp` and
  `.derivedModuleEdgeTransport_self`: the edge transports compose and are the identity on a
  degenerate edge; the first is the content of the cocycle condition and the second follows from
  it.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleEdgeTransport_map`: edge transport is
  compatible with pulling back along a simplex map.

## Implementation notes

*There is no unit clause, and that is what the source says.* Stacks 0GMF asserts that the `K_n`
form a cartesian simplicial system, and a simplicial system of the derived category of modules
(Stacks 0D9N) carries the cocycle condition and nothing else:
`CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem` has no `map_id` field, as
the implementation notes of its own module record, contrasting it with the abelian analogue
Stacks 0D9G where the identity comparison is available as an isomorphism of exact functors. So
no unit law `Lf_{𝟙}^* ≅ 𝟭` is proved here, and no identification `K_0 ≅ K₀` in degree zero is
offered: `pairDerivedModuleSystem_obj` gives `K_n = Lf_{τⁿₙ}^* K₀` on the nose, which is the
source's
"Set `K_n = Lf_{τⁿₙ}^* K_0`", and in degree zero the last vertex is the identity simplex map
rather than a transport away from it. The absence of a unit clause is deliberate, not an
omission.

*The devices that keep the elaborator inside its default budget* — opaque definitions such as
`derivedEdgeSource`, `derivedEdgeTarget` and `derivedEdgeMapPaste`, and reassociated variants
such as `derivedEdgeTransport_map_assoc` — are recorded in the implementation notes of
the sibling file `DerivedCocycleSystem/DerivedCompositorAssoc.lean`.

*The simplicial combinatorics is not rebuilt.* Mathlib's `SimplexCategory.const`,
`mkOfLe` and `mkOfLeComp`, the computations
`SimplexCategory.delta_one_comp_mkOfLe`, `.delta_zero_comp_mkOfLe`, `.vertexMap_comp`,
`.edgeMap_comp`, `.hom_le` and the six degree-two face identities all come from
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianPair.lean`, where Stacks 0D7I put them.
In the notation of the source, `const (mk 0) (mk n) i` is `τⁿᵢ`, its last-vertex case is
`τⁿₙ` and
`mkOfLe i j h` is `τⁿᵢⱼ`; the last takes `h : i ≤ j` because that is when it is a simplex
map, and the source only ever uses it at `i = φ(n) ≤ m = j`.

## References

* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0GME](https://stacks.math.columbia.edu/tag/0GME)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_pushforwardModules_map)
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The pair `(K₀, α)` of Stacks 0GMF -/

/-- The identification of the derived pullbacks of an object along two factorizations `ψ ≫ φ`
and `ψ' ≫ φ'` of one simplex map. -/
def derivedModuleGlueOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedTransitionPullback O φ).obj ((S.derivedTransitionPullback O ψ).obj K) ≅
      (S.derivedTransitionPullback O φ').obj ((S.derivedTransitionPullback O ψ').obj K) :=
  S.derivedModulePasteIsoOfEq O ψ φ v h K ≪≫ (S.derivedModulePasteIsoOfEq O ψ' φ' v h' K).symm

/-- The identification of two factorizations, written out. -/
theorem derivedModuleGlueOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedModuleGlueOfEq O ψ ψ' φ φ' v h h' K).hom =
      (S.derivedModulePasteIsoOfEq O ψ φ v h K).hom ≫
        (S.derivedModulePasteIsoOfEq O ψ' φ' v h' K).inv :=
  rfl

/-- The inverse of the identification of two factorizations, written out. -/
theorem derivedModuleGlueOfEq_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (K : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedModuleGlueOfEq O ψ ψ' φ φ' v h h' K).inv =
      (S.derivedModulePasteIsoOfEq O ψ' φ' v h' K).hom ≫
        (S.derivedModulePasteIsoOfEq O ψ φ v h K).inv :=
  rfl

/-- The identification of the two derived pullbacks of `Lf_{δ¹₁}^* K` to degree two occurring in
the cocycle condition, along `δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`. -/
def derivedModuleGlueLeft (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O (SimplexCategory.δ (2 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K) ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K) :=
  S.derivedModuleGlueOfEq O _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one K

/-- The identification of `Lf_{δ²₂}^* Lf_{δ¹₀}^* K` with `Lf_{δ²₀}^* Lf_{δ¹₁}^* K`, along
`δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀`. -/
def derivedModuleGlueMiddle (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O (SimplexCategory.δ (2 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K) ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K) :=
  S.derivedModuleGlueOfEq O _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero K

/-- The identification of the two derived pullbacks of `Lf_{δ¹₀}^* K` to degree two occurring in
the cocycle condition, along `δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`. -/
def derivedModuleGlueRight (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K) ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 3))).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K) :=
  S.derivedModuleGlueOfEq O _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one K

/-- **Stacks 0GMF, the input datum.** An object `K₀` of the derived category of `O_0`-modules on
the degree-zero component together with an isomorphism
`α : Lf_{δ¹₁}^* K₀ ≅ Lf_{δ¹₀}^* K₀` on the degree-one component satisfying the cocycle condition
`Lf_{δ²₁}^* α = Lf_{δ²₀}^* α ∘ Lf_{δ²₂}^* α` on the degree-two component, read through the
canonical identifications of the three degree-two pullbacks. -/
structure DerivedModuleCocyclePair where
  /-- The object of the derived category of modules on the degree-zero component. -/
  obj : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules
  /-- The comparison isomorphism between the two derived pullbacks to degree one. -/
  iso : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj obj ≅
    (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj obj
  /-- The cocycle condition on the degree-two component. -/
  cocycle :
    (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 3))).map iso.hom =
      (S.derivedModuleGlueLeft O obj).inv ≫
        (S.derivedTransitionPullback O (SimplexCategory.δ (2 : Fin 3))).map iso.hom ≫
        (S.derivedModuleGlueMiddle O obj).hom ≫
        (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 3))).map iso.hom ≫
        (S.derivedModuleGlueRight O obj).hom

/-! ### Transport along the edges of a simplex -/

/-- The comparison between the derived pullbacks of `K` along the two ends of an edge `φ` of a
simplex, obtained from the derived pullback of `α` along `φ`. -/
def derivedModuleTransportAlongIso (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (S.derivedTransitionPullback O v).obj K ≅ (S.derivedTransitionPullback O w).obj K :=
  (S.derivedModulePasteIsoOfEq O _ φ v h₁ K).symm ≪≫
    (S.derivedTransitionPullback O φ).mapIso α ≪≫ S.derivedModulePasteIsoOfEq O _ φ w h₀ K

/-- Transport along an edge, as a morphism. -/
def derivedModuleTransportAlong (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (S.derivedTransitionPullback O v).obj K ⟶ (S.derivedTransitionPullback O w).obj K :=
  (S.derivedModuleTransportAlongIso O K α φ v w h₁ h₀).hom

/-- Transport along an edge is invertible. -/
instance derivedModuleTransportAlong_isIso
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    IsIso (S.derivedModuleTransportAlong O K α φ v w h₁ h₀) :=
  inferInstanceAs (IsIso (S.derivedModuleTransportAlongIso O K α φ v w h₁ h₀).hom)

/-- The identification of the derived pullback of `Lf_{δ¹₁}^* K` along the edge from the vertex
`i` to the vertex `j` of `⦋n⦌` with the derived pullback of `K` along the vertex `i`. Opaque, so
that the statements below are short enough to elaborate. -/
def derivedEdgeSource (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K) ≅
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj K :=
  S.derivedModulePasteIsoOfEq O (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h) K

/-- The identification of the derived pullback of `Lf_{δ¹₀}^* K` along the edge from the vertex
`i` to the vertex `j` of `⦋n⦌` with the derived pullback of `K` along the vertex `j`. -/
def derivedEdgeTarget (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).obj
        ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K) ≅
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj K :=
  S.derivedModulePasteIsoOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h) K

/-- The identification of the derived pullback along an edge of `⦋m⦌`, pulled back along a
simplex map, with the pullback along the image edge. -/
def derivedEdgeMapPaste {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1)) (h : i ≤ j)
    (X : DerivedCategory (S.componentRingedTopos O ⦋1⦌).Modules) :
    (S.derivedTransitionPullback O φ).obj
        ((S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).obj X) ≅
      (S.derivedTransitionPullback O
        (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h))).obj X :=
  S.derivedModulePasteIsoOfEq O (SimplexCategory.mkOfLe i j h) φ _
    (SimplexCategory.edgeMap_comp φ i j h) X

/-- The comparison between the derived pullbacks of `K` along two vertices `i ≤ j` of `⦋n⦌`,
obtained from the derived pullback of `α` along the edge joining them. -/
def derivedModuleEdgeTransportIso (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj K ≅
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj K :=
  S.derivedModuleTransportAlongIso O K α (SimplexCategory.mkOfLe i j h) _ _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h)
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h)

/-- Transport along an edge of `⦋n⦌`, as a morphism. -/
def derivedModuleEdgeTransport (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj K ⟶
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj K :=
  (S.derivedModuleEdgeTransportIso O K α i j h).hom

/-- Transport along an edge of `⦋n⦌` is invertible. -/
instance derivedModuleEdgeTransport_isIso
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    IsIso (S.derivedModuleEdgeTransport O K α i j h) :=
  inferInstanceAs (IsIso (S.derivedModuleEdgeTransportIso O K α i j h).hom)

/-- Transport along an edge, written out. -/
theorem derivedModuleTransportAlong_eq
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    S.derivedModuleTransportAlong O K α φ v w h₁ h₀ =
      (S.derivedModulePasteIsoOfEq O _ φ v h₁ K).inv ≫
        (S.derivedTransitionPullback O φ).map α.hom ≫
          (S.derivedModulePasteIsoOfEq O _ φ w h₀ K).hom :=
  rfl

/-- Transport along an edge of `⦋n⦌`, written out through the two edge identifications. -/
theorem derivedModuleEdgeTransport_eq
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    S.derivedModuleEdgeTransport O K α i j h =
      (S.derivedEdgeSource O K i j h).inv ≫
        (S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).map α.hom ≫
          (S.derivedEdgeTarget O K i j h).hom :=
  rfl

/-! ### Compatibility of the transports with simplex maps -/

/-- The identification of the derived pullback of `K` along a vertex of `⦋m⦌`, pulled back along
a simplex map, with the pullback along the image vertex. -/
def derivedModuleVertexPaste {m n : SimplexCategory} (φ : m ⟶ n) (i : Fin (m.len + 1))
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O φ).obj
        ((S.derivedTransitionPullback O
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)).obj K) ≅
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n.len) (φ.toOrderHom i))).obj K :=
  S.derivedModulePasteIsoOfEq O _ φ _ (SimplexCategory.vertexMap_comp φ i) K

/-- The vertex identifications are compatible with composition of simplex maps. -/
theorem derivedModuleVertexPaste_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : Fin (l.len + 1)) (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O φ).map (S.derivedModuleVertexPaste O ψ i K).hom ≫
        (S.derivedModuleVertexPaste O φ (ψ.toOrderHom i) K).hom =
      (S.derivedModulePasteIso O ψ φ
          ((S.derivedTransitionPullback O
            (SimplexCategory.const (SimplexCategory.mk 0)
              (SimplexCategory.mk l.len) i)).obj K)).hom ≫
        (S.derivedModuleVertexPaste O (ψ ≫ φ) i K).hom := by
  have h := S.derivedModulePasteIsoOfEq_assoc O
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk l.len) i) ψ φ _ (ψ ≫ φ) _
    (SimplexCategory.vertexMap_comp ψ i) rfl
    (SimplexCategory.vertexMap_comp φ (ψ.toOrderHom i))
    (SimplexCategory.vertexMap_comp (ψ ≫ φ) i) K
  rwa [S.derivedModulePasteIsoOfEq_rfl O ψ φ] at h

/-- Pulling back the source identification of an edge of `⦋m⦌` along a simplex map gives the
source identification of the image edge. -/
theorem derivedModuleEdgePaste_one_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeSource O K i j h).hom ≫
        (S.derivedModuleVertexPaste O φ i K).hom =
      (S.derivedEdgeMapPaste O φ i j h
            ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K)).hom ≫
        (S.derivedEdgeSource O K (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h)).hom :=
  S.derivedModulePasteIsoOfEq_assoc O (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom i))
    (SimplexCategory.delta_one_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ i)
    (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) K

/-- Pulling back the target identification of an edge of `⦋m⦌` along a simplex map gives the
target identification of the image edge. -/
theorem derivedModuleEdgePaste_zero_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeTarget O K i j h).hom ≫
        (S.derivedModuleVertexPaste O φ j K).hom =
      (S.derivedEdgeMapPaste O φ i j h
            ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)).hom ≫
        (S.derivedEdgeTarget O K (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h)).hom :=
  S.derivedModulePasteIsoOfEq_assoc O (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) j)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom j))
    (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ j)
    (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) K

/-- Composing edge transport with the source identification of the edge strips the
identification: what remains is the derived pullback of `α` along the edge. -/
theorem derivedEdgeSource_comp_edgeTransport
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.derivedEdgeSource O K i j h).hom ≫ S.derivedModuleEdgeTransport O K α i j h =
      (S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).map α.hom ≫
        (S.derivedEdgeTarget O K i j h).hom := by
  rw [S.derivedModuleEdgeTransport_eq O K α i j h, Iso.hom_inv_id_assoc]

/-- The edge identification along a simplex map is natural in the object. -/
theorem derivedEdgeMapPaste_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    (i j : Fin (m.len + 1)) (h : i ≤ j)
    {X Y : DerivedCategory (S.componentRingedTopos O ⦋1⦌).Modules} (f : X ⟶ Y) :
    (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).map f) ≫
        (S.derivedEdgeMapPaste O φ i j h Y).hom =
      (S.derivedEdgeMapPaste O φ i j h X).hom ≫
        (S.derivedTransitionPullback O
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h))).map f :=
  S.derivedModulePasteIsoOfEq_naturality O (SimplexCategory.mkOfLe i j h) φ _
    (SimplexCategory.edgeMap_comp φ i j h) f

/-- The pullback along a simplex map of the identity stripping edge transport of its source
identification. -/
theorem derivedEdgeTransport_map_leftA {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeSource O K i j h).hom ≫
        (S.derivedTransitionPullback O φ).map (S.derivedModuleEdgeTransport O K α i j h) =
      (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).map α.hom) ≫
        (S.derivedTransitionPullback O φ).map (S.derivedEdgeTarget O K i j h).hom := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    S.derivedEdgeSource_comp_edgeTransport O K α i j h]

/-- The left-hand side of the compatibility of edge transport with a simplex map, first step. -/
theorem derivedEdgeTransport_map_left₁ {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeSource O K i j h).hom ≫
        ((S.derivedTransitionPullback O φ).map (S.derivedModuleEdgeTransport O K α i j h) ≫
          (S.derivedModuleVertexPaste O φ j K).hom) =
      (S.derivedTransitionPullback O φ).map
            ((S.derivedTransitionPullback O (SimplexCategory.mkOfLe i j h)).map α.hom) ≫
          ((S.derivedEdgeMapPaste O φ i j h
              ((S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)).hom ≫
            (S.derivedEdgeTarget O K (φ.toOrderHom i) (φ.toOrderHom j)
              (SimplexCategory.hom_le φ h)).hom) := by
  rw [← Category.assoc, S.derivedEdgeTransport_map_leftA O φ K α i j h, Category.assoc,
    S.derivedModuleEdgePaste_zero_comp O φ i j h K]

/-- The left-hand side of the compatibility of edge transport with a simplex map, with the
source identification of the edge stripped off. -/
theorem derivedEdgeTransport_map_left {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeSource O K i j h).hom ≫
        ((S.derivedTransitionPullback O φ).map (S.derivedModuleEdgeTransport O K α i j h) ≫
          (S.derivedModuleVertexPaste O φ j K).hom) =
      (S.derivedEdgeMapPaste O φ i j h
            ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K)).hom ≫
        (S.derivedTransitionPullback O
              (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
                (SimplexCategory.hom_le φ h))).map α.hom ≫
          (S.derivedEdgeTarget O K (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)).hom := by
  rw [S.derivedEdgeTransport_map_left₁ O φ K α i j h, ← Category.assoc,
    S.derivedEdgeMapPaste_naturality O φ i j h α.hom, Category.assoc]

/-- The right-hand side of the compatibility of edge transport with a simplex map, with the
source identification of the edge stripped off. -/
theorem derivedEdgeTransport_map_right {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O φ).map (S.derivedEdgeSource O K i j h).hom ≫
        ((S.derivedModuleVertexPaste O φ i K).hom ≫
          S.derivedModuleEdgeTransport O K α (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) =
      (S.derivedEdgeMapPaste O φ i j h
            ((S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K)).hom ≫
        (S.derivedTransitionPullback O
              (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
                (SimplexCategory.hom_le φ h))).map α.hom ≫
          (S.derivedEdgeTarget O K (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)).hom := by
  rw [← Category.assoc, S.derivedModuleEdgePaste_one_comp O φ i j h K, Category.assoc,
    S.derivedEdgeSource_comp_edgeTransport O K α]

/-- **Edge transport is compatible with pulling back along a simplex map.** -/
theorem derivedModuleEdgeTransport_map {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.derivedTransitionPullback O φ).map (S.derivedModuleEdgeTransport O K α i j h) ≫
        (S.derivedModuleVertexPaste O φ j K).hom =
      (S.derivedModuleVertexPaste O φ i K).hom ≫
        S.derivedModuleEdgeTransport O K α (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h) := by
  refine (cancel_epi ((S.derivedTransitionPullback O φ).map
    (S.derivedEdgeSource O K i j h).hom)).mp ?_
  rw [S.derivedEdgeTransport_map_left O φ K α i j h,
    S.derivedEdgeTransport_map_right O φ K α i j h]

/-- Compatibility of edge transport with a simplex map, reassociated. -/
theorem derivedEdgeTransport_map_assoc {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (i j : Fin (m.len + 1)) (h : i ≤ j)
    {Z : DerivedCategory (S.componentRingedTopos O n).Modules}
    (t : (S.derivedTransitionPullback O
      (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n.len) (φ.toOrderHom j))).obj K ⟶ Z) :
    (S.derivedTransitionPullback O φ).map (S.derivedModuleEdgeTransport O K α i j h) ≫
        (S.derivedModuleVertexPaste O φ j K).hom ≫ t =
      (S.derivedModuleVertexPaste O φ i K).hom ≫
        S.derivedModuleEdgeTransport O K α (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h) ≫ t := by
  rw [← Category.assoc _ _ t, S.derivedModuleEdgeTransport_map O φ K α i j h, Category.assoc _ _ t]

/-! ### Edge transports compose -/

/-- Edge transport read along any presentation of the edge as a simplex map. -/
theorem derivedModuleEdgeTransport_eq_transportAlong
    (K : DerivedCategory (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.derivedTransitionPullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.derivedTransitionPullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) (φ : ⦋1⦌ ⟶ ⦋n⦌)
    (hφ : SimplexCategory.mkOfLe i j h = φ)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j) :
    S.derivedModuleEdgeTransport O K α i j h = S.derivedModuleTransportAlong O K α φ _ _ h₁ h₀ := by
  subst hφ
  rfl

/-- **The cocycle condition of a pair, read as composability of the transports along the three
edges of `⦋2⦌`.** -/
theorem derivedModuleEdgeTransport_cocycle_two (Pr : S.DerivedModuleCocyclePair O) :
    S.derivedModuleEdgeTransport O Pr.obj Pr.iso (0 : Fin 3) 2 (by decide) =
      S.derivedModuleEdgeTransport O Pr.obj Pr.iso (0 : Fin 3) 1 (by decide) ≫
        S.derivedModuleEdgeTransport O Pr.obj Pr.iso (1 : Fin 3) 2 (by decide) := by
  rw [S.derivedModuleEdgeTransport_eq_transportAlong O (n := 2) Pr.obj Pr.iso 0 2 (by decide)
      (SimplexCategory.δ (1 : Fin 3)) (SimplexCategory.edgeMap_two_zero_two_eq _)
      SimplexCategory.delta_one_comp_delta_one SimplexCategory.delta_zero_comp_delta_one,
    S.derivedModuleEdgeTransport_eq_transportAlong O (n := 2) Pr.obj Pr.iso 0 1 (by decide)
      (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.edgeMap_two_zero_one_eq _)
      SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_zero_comp_delta_two,
    S.derivedModuleEdgeTransport_eq_transportAlong O (n := 2) Pr.obj Pr.iso 1 2 (by decide)
      (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.edgeMap_two_one_two_eq _)
      SimplexCategory.delta_one_comp_delta_zero SimplexCategory.delta_zero_comp_delta_zero]
  simp only [S.derivedModuleTransportAlong_eq O]
  rw [Pr.cocycle]
  simp only [derivedModuleGlueLeft, derivedModuleGlueMiddle, derivedModuleGlueRight,
    S.derivedModuleGlueOfEq_hom O,
    S.derivedModuleGlueOfEq_inv O, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Edge transports compose.** This is the content of the cocycle condition: the transport
from `i` to `k` is the transport from `i` to `j` followed by the transport from `j` to `k`. -/
theorem derivedModuleEdgeTransport_comp (Pr : S.DerivedModuleCocyclePair O) {n : ℕ}
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    S.derivedModuleEdgeTransport O Pr.obj Pr.iso i k (hij.trans hjk) =
      S.derivedModuleEdgeTransport O Pr.obj Pr.iso i j hij ≫
        S.derivedModuleEdgeTransport O Pr.obj Pr.iso j k hjk := by
  have h := congrArg
    (fun t ↦ (S.derivedTransitionPullback O
          (SimplexCategory.mkOfLeComp i j k hij hjk)).map t ≫
        (S.derivedModuleVertexPaste O (SimplexCategory.mkOfLeComp i j k hij hjk) 2 Pr.obj).hom)
    (S.derivedModuleEdgeTransport_cocycle_two O Pr)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h
  rw [S.derivedModuleEdgeTransport_map O, S.derivedModuleEdgeTransport_map O,
    S.derivedEdgeTransport_map_assoc O] at h
  exact (cancel_epi (S.derivedModuleVertexPaste O (SimplexCategory.mkOfLeComp i j k hij hjk) 0
    Pr.obj).hom).mp h

/-- Edge transport along a degenerate edge is the identity. -/
theorem derivedModuleEdgeTransport_self (Pr : S.DerivedModuleCocyclePair O) {n : ℕ}
    (i : Fin (n + 1)) :
    S.derivedModuleEdgeTransport O Pr.obj Pr.iso i i le_rfl = 𝟙 _ := by
  refine (cancel_epi (S.derivedModuleEdgeTransport O Pr.obj Pr.iso i i le_rfl)).mp ?_
  simpa using (S.derivedModuleEdgeTransport_comp O Pr i i i le_rfl le_rfl).symm

/-! ### The simplicial system attached to a pair -/

/-- The object in degree `n` of the system attached to a pair: the derived pullback of its
degree-zero object along the last vertex of `⦋n⦌`. -/
def pairDerivedModuleObj (Pr : S.DerivedModuleCocyclePair O) (n : SimplexCategory) :
    DerivedCategory (S.componentRingedTopos O n).Modules :=
  (S.derivedTransitionPullback O
    (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).obj Pr.obj

/-- The transition in the system attached to a pair, as an isomorphism: pull back to the image of
the last vertex, then transport along the edge to the last vertex. -/
def pairDerivedModuleTransitionIso (Pr : S.DerivedModuleCocyclePair O) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.derivedTransitionPullback O φ).obj (S.pairDerivedModuleObj O Pr m) ≅
      S.pairDerivedModuleObj O Pr n :=
  S.derivedModuleVertexPaste O φ (Fin.last m.len) Pr.obj ≪≫
    S.derivedModuleEdgeTransportIso O Pr.obj Pr.iso (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _)

/-- The transition in the system attached to a pair. -/
def pairDerivedModuleTransition (Pr : S.DerivedModuleCocyclePair O) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.derivedTransitionPullback O φ).obj (S.pairDerivedModuleObj O Pr m) ⟶
      S.pairDerivedModuleObj O Pr n :=
  (S.pairDerivedModuleTransitionIso O Pr φ).hom

/-- The transitions of the system attached to a pair are invertible. -/
instance pairDerivedModuleTransition_isIso (Pr : S.DerivedModuleCocyclePair O)
    {m n : SimplexCategory}
    (φ : m ⟶ n) : IsIso (S.pairDerivedModuleTransition O Pr φ) :=
  inferInstanceAs (IsIso (S.pairDerivedModuleTransitionIso O Pr φ).hom)

/-- The cocycle condition for the transitions of the system attached to a pair, first step: the
transition at `ψ` is pulled back along `φ` and the resulting edge transport carried past the
vertex identification of `φ`. -/
theorem pairDerivedTransition_compA₁ (Pr : S.DerivedModuleCocyclePair O) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.derivedTransitionPullback O φ).map
            ((S.derivedModuleVertexPaste O ψ (Fin.last l.len) Pr.obj).hom ≫
              S.derivedModuleEdgeTransport O Pr.obj Pr.iso (ψ.toOrderHom (Fin.last l.len))
                (Fin.last m.len) (Fin.le_last _)) ≫
          ((S.derivedModuleVertexPaste O φ (Fin.last m.len) Pr.obj).hom ≫
            S.derivedModuleEdgeTransport O Pr.obj Pr.iso (φ.toOrderHom (Fin.last m.len))
              (Fin.last n.len) (Fin.le_last _)) =
      (S.derivedTransitionPullback O φ).map
            (S.derivedModuleVertexPaste O ψ (Fin.last l.len) Pr.obj).hom ≫
          ((S.derivedModuleVertexPaste O φ (ψ.toOrderHom (Fin.last l.len)) Pr.obj).hom ≫
            S.derivedModuleEdgeTransport O Pr.obj Pr.iso
                (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len)))
                (φ.toOrderHom (Fin.last m.len)) (SimplexCategory.hom_le φ (Fin.le_last _)) ≫
              S.derivedModuleEdgeTransport O Pr.obj Pr.iso (φ.toOrderHom (Fin.last m.len))
                (Fin.last n.len) (Fin.le_last _)) := by
  rw [CategoryTheory.Functor.map_comp,
    Category.assoc _ _
      ((S.derivedModuleVertexPaste O φ (Fin.last m.len) Pr.obj).hom ≫
        S.derivedModuleEdgeTransport O Pr.obj Pr.iso (φ.toOrderHom (Fin.last m.len))
          (Fin.last n.len) (Fin.le_last _)),
    S.derivedEdgeTransport_map_assoc O φ Pr.obj Pr.iso (ψ.toOrderHom (Fin.last l.len))
      (Fin.last m.len) (Fin.le_last _)]

/-- The cocycle condition for the transitions of the system attached to a pair, second step: the
two edge transports compose, and the two vertex identifications compose. -/
theorem pairDerivedTransition_compA₂ (Pr : S.DerivedModuleCocyclePair O) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.derivedTransitionPullback O φ).map
            (S.derivedModuleVertexPaste O ψ (Fin.last l.len) Pr.obj).hom ≫
          ((S.derivedModuleVertexPaste O φ (ψ.toOrderHom (Fin.last l.len)) Pr.obj).hom ≫
            S.derivedModuleEdgeTransport O Pr.obj Pr.iso
                (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len)))
                (φ.toOrderHom (Fin.last m.len)) (SimplexCategory.hom_le φ (Fin.le_last _)) ≫
              S.derivedModuleEdgeTransport O Pr.obj Pr.iso (φ.toOrderHom (Fin.last m.len))
                (Fin.last n.len) (Fin.le_last _)) =
      (S.derivedModulePasteIso O ψ φ
              ((S.derivedTransitionPullback O
                (SimplexCategory.const (SimplexCategory.mk 0)
                  (SimplexCategory.mk l.len) (Fin.last l.len))).obj Pr.obj)).hom ≫
          (S.derivedModuleVertexPaste O (ψ ≫ φ) (Fin.last l.len) Pr.obj).hom ≫
            S.derivedModuleEdgeTransport O Pr.obj Pr.iso
              (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len))) (Fin.last n.len)
              (Fin.le_last _) := by
  rw [← S.derivedModuleEdgeTransport_comp O Pr,
    ← Category.assoc
      ((S.derivedTransitionPullback O φ).map
        (S.derivedModuleVertexPaste O ψ (Fin.last l.len) Pr.obj).hom)
      (S.derivedModuleVertexPaste O φ (ψ.toOrderHom (Fin.last l.len)) Pr.obj).hom _,
    S.derivedModuleVertexPaste_comp O ψ φ]
  exact Category.assoc _ _ _

/-- **The transitions of the system attached to a pair satisfy the cocycle condition of Stacks
0D9N.** Pulling back the transition at `ψ` along `φ` and following with the transition at `φ`
agrees, through the compositor of derived pullbacks, with the transition at `ψ ≫ φ`: the vertex
identifications compose by `derivedModuleVertexPaste_comp`, and the two edge transports compose by
`derivedModuleEdgeTransport_comp`, which is the cocycle condition. -/
theorem pairDerivedModuleTransition_comp (Pr : S.DerivedModuleCocyclePair O)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.derivedModulePasteIso O ψ φ (S.pairDerivedModuleObj O Pr l)).hom ≫
        S.pairDerivedModuleTransition O Pr (ψ ≫ φ) =
      (S.derivedTransitionPullback O φ).map (S.pairDerivedModuleTransition O Pr ψ) ≫
        S.pairDerivedModuleTransition O Pr φ :=
  ((S.pairDerivedTransition_compA₁ O Pr ψ φ).trans
    (S.pairDerivedTransition_compA₂ O Pr ψ φ)).symm

/-- **Stacks 0GMF.** The simplicial system of the derived category of modules attached to a pair
`(K₀, α)`: in degree `n` the derived pullback of `K₀` along the last vertex of `⦋n⦌`, with the
transition at `φ` given by pulling back to the image of the last vertex and transporting along
the edge to the last vertex. The cocycle condition of Stacks 0D9N is
`pairDerivedModuleTransition_comp`. -/
@[stacks 0GMF "the simplicial system"]
def pairDerivedModuleSystem (Pr : S.DerivedModuleCocyclePair O) :
    SimplicialDerivedModuleSystem S O where
  obj n := S.pairDerivedModuleObj O Pr n
  map φ := S.pairDerivedModuleTransition O Pr φ
  map_comp ψ φ := S.pairDerivedModuleTransition_comp O Pr ψ φ

/-- **Stacks 0GMF.** The object of the system in degree `n` is `Lf_{τⁿₙ}^* K₀`, the derived
pullback of `K₀` along the last vertex of `⦋n⦌`. -/
@[stacks 0GMF "the objects of the system"]
theorem pairDerivedModuleSystem_obj (Pr : S.DerivedModuleCocyclePair O) (n : SimplexCategory) :
    (S.pairDerivedModuleSystem O Pr).obj n =
      (S.derivedTransitionPullback O
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).obj Pr.obj :=
  rfl

/-- **Stacks 0GMF.** The system attached to a pair is cartesian: every transition map is an
isomorphism, for every simplex map and not only for the faces. -/
@[stacks 0GMF "the system is cartesian"]
theorem pairDerivedModuleSystem_cartesian (Pr : S.DerivedModuleCocyclePair O) :
    (S.pairDerivedModuleSystem O Pr).Cartesian :=
  fun φ ↦ S.pairDerivedModuleTransition_isIso O Pr φ

end CategoryTheory.SimplicialSiteSituation

end
