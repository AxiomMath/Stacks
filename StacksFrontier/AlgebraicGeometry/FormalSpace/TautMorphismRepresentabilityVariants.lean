module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed

/-!
# Tautness and representability of morphisms of formal algebraic spaces

For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic spaces, tautness of `f`
on affine étale charts, in each of three forms, is equivalent to `f` being representable by
algebraic spaces.

## Main results

* `isTaut_tfae_isRepresentableByAlgebraicSpaces_of_cancellation`: the three tautness conditions
  on `f` and representability of `f` by algebraic spaces are equivalent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LocalProperty

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

end LocalProperty

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
4. `f` is representable by algebraic spaces. -/
theorem isTaut_tfae_isRepresentableByAlgebraicSpaces_of_cancellation {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
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
  have h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U := fun Z hZ ↦
    (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed
      B S hS Z hZ.1).2 hZ.2
  tfae_have 1 → 2 := fun h ↦
    hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible TautChartProperty f hY.1 (fun _V v _hV hv ↦
      isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS v f hX.1 hv) h
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
    exact isRepresentableOnEverySquare_of_isRepresentable B S hS f hY.1 h0AQ0 hf U V a b t
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha.1 hb.1 hsq
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
