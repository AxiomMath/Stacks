module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Taut ring maps and representability by algebraic spaces: the refined forms

For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic spaces, we show that
`f` is representable by algebraic spaces if and only if it is given on affine étale charts by
taut continuous homomorphisms of countably indexed weakly admissible topological rings.

## Main results

* `isTaut_tfae_isRepresentableByAlgebraicSpaces'`: the equivalence of tautness on charts, in
  three forms, with representability of `f` by algebraic spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Composing the coverings of condition (2) into a covering of the source -/

section LocalProperty

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

end LocalProperty

/-! ### Stacks 0ANK -/

/-- **Stacks 0ANK.** Let `f : X ⟶ Y` be a morphism of locally countably indexed formal
algebraic spaces over `S`. The following are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has `U ⟶ V` given by a taut continuous homomorphism of
   countably indexed weakly admissible topological rings;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uᵢ ⟶ Vⱼ` given by such a taut map;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Uᵢ ⟶ Vᵢ` given by such a taut map;
4. `f` is representable by algebraic spaces.

The cycle runs `(1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1)`: the first step is Stacks 0ANG, the second is
proved here, and the last two pass between tautness and representability on charts through
Stacks 0AN5 and between charts and `f` through Stacks 0AN4. -/
theorem isTaut_tfae_isRepresentableByAlgebraicSpaces' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AN4 : ∀ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
      (b : ∀ i, W i ⟶ Y) (t : ∀ i, U i ⟶ W i), IsAffineEtaleCover B S hS U a →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (b i).hom) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (t i).hom) →
      (∀ i, a i ≫ f = t i ≫ b i) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    List.TFAE
      [ IsTautOnEveryAffineEtaleDiagram B S hS f,
        IsTautAfterTargetCover B S hS f,
        IsTautAfterSourceCover B S hS f,
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom ] := by
  have h0AKX := isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f hY.1 h0AJ3 h
  tfae_have 2 → 3 := fun h ↦
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f h
  tfae_have 3 → 4 := by
    rintro ⟨I, U, a, hUcover, hfac⟩
    choose W b t hWaffine hWetale hWsquare hWproperty using hfac
    refine h0AN4 I U W a b t hUcover hWaffine (fun i ↦ (hWetale i).1) (fun i ↦ ?_) hWsquare
    exact (h0AN5 (t i) (hUcover.1 i) (hWaffine i)
      (h0AKX X hX (U i) (a i) (hUcover.1 i) (hUcover.2.1 i))
      (h0AKX Y hY (W i) (b i) (hWaffine i) (hWetale i))).2 (hWproperty i)
  tfae_have 4 → 1 := by
    intro hf U V a b t hU hV ha hb hsq
    refine (h0AN5 t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1 ?_
    exact isRepresentableOnEverySquare_of_isRepresentable' B S hS f hf U V a b t
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha.1 hb.1 hsq
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
