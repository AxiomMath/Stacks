module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.FibreFinitenessDescent

/-!
# Descending the contraction step of Stacks 0AEM along an extension of the ground field

Let `p : X ⟶ Y` be a morphism of algebraic spaces over a field `k` with a section, let `X` be
reduced, and let `f : X ⟶ Z` be a morphism to a separated algebraic space. If after base change
along a morphism `Spec K ⟶ Spec k` of the site the morphism `f` factors through `p` by a morphism
all of whose fibres on points are finite, then so does `f` itself.

## Main results

* `AlgebraicGeometry.Space.exists_factorization_finite_fibres_of_relocalizeRestrict`: a
  factorization of `f` through `p` with finite fibres descends along `Spec K ⟶ Spec k`.
* `AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_relocalizeRestrict`: the
  same for a factorization through one member of a family of morphisms `p i : X ⟶ Y i` with
  sections.
* `AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_algebraicClosure`: the
  same for the extension of `k` to its algebraic closure.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (g : B.obj hK ⟶ B.obj hk)

/-- Let `p : X ⟶ Y` be a morphism of algebraic spaces over a field `k` with a section `s`, let
`X` be reduced, and let `f : X ⟶ Z` be a morphism to an algebraic space
separated over a terminal presheaf. If after base change along a morphism `Spec K ⟶ Spec k` of
the site the morphism `f` factors through `p` by a morphism all of whose fibres on points are
finite, then `f` factors through `p` over `k` by a morphism all of whose fibres on points are
finite. -/
theorem exists_factorization_finite_fibres_of_relocalizeRestrict
    {T X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (hbase : ∃ u : (OverShriek.relocalizeRestrict g).obj Y ⟶
        (OverShriek.relocalizeRestrict g).obj Z,
      (OverShriek.relocalizeRestrict g).map f = (OverShriek.relocalizeRestrict g).map p ≫ u ∧
        ∀ z : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Z),
          {x : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Y) |
            pointsMap B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Y) u x =
              z}.Finite) :
    ∃ v : Y ⟶ Z, f = p ≫ v ∧
      ∀ z : points B (Spec (.of k)) hk Z,
        {y : points B (Spec (.of k)) hk Y |
          pointsMap B (Spec (.of k)) hk Y v y = z}.Finite := by
  obtain ⟨u, hu, hufib⟩ := hbase
  obtain ⟨v, hv, hvu, -⟩ := exists_factorization_of_relocalizeRestrict_factorization B k K hk hK g
    hTterm hT hX hZ hXred qZ hqZ p s hsp f u hu
  refine ⟨v, hv, finite_fibre_pointsMap_of_relocalizeRestrict B k K hk hK g v ?_⟩
  rwa [hvu]

/-- Let `p i : X ⟶ Y i` be a family of morphisms of algebraic spaces over a field `k` with
sections `s i`, let `X` be reduced, and let `f : X ⟶ Z` be a morphism to an algebraic space
separated over a terminal presheaf. If after base change along a morphism `Spec K ⟶ Spec k` of
the site the morphism `f` factors through some `p i` by a morphism all of whose fibres on points
are finite, then `f` factors through that `p i` over `k` by a morphism all of whose fibres on
points are finite. -/
theorem exists_index_factorization_finite_fibres_of_relocalizeRestrict
    {ι : Type v} {T X Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (Y : ι → (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : ∀ i, X ⟶ Y i) (s : ∀ i, Y i ⟶ X) (hsp : ∀ i, s i ≫ p i = 𝟙 (Y i)) (f : X ⟶ Z)
    (hbase : ∃ (i : ι) (u : (OverShriek.relocalizeRestrict g).obj (Y i) ⟶
        (OverShriek.relocalizeRestrict g).obj Z),
      (OverShriek.relocalizeRestrict g).map f =
          (OverShriek.relocalizeRestrict g).map (p i) ≫ u ∧
        ∀ z : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Z),
          {x : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj (Y i)) |
            pointsMap B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj (Y i)) u x =
              z}.Finite) :
    ∃ (i : ι) (v : Y i ⟶ Z), f = p i ≫ v ∧
      ∀ z : points B (Spec (.of k)) hk Z,
        {y : points B (Spec (.of k)) hk (Y i) |
          pointsMap B (Spec (.of k)) hk (Y i) v y = z}.Finite :=
  hbase.imp fun i hi => exists_factorization_finite_fibres_of_relocalizeRestrict B k K hk hK g
    hTterm hT hX hZ hXred qZ hqZ (p i) (s i) (hsp i) f hi

/-- `AlgebraicGeometry.Space.exists_index_factorization_finite_fibres_of_relocalizeRestrict` for
the extension of the ground field `k` to its algebraic closure. -/
theorem exists_index_factorization_finite_fibres_of_algebraicClosure
    {ι : Type v} {T X Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (Y : ι → (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : ∀ i, X ⟶ Y i) (s : ∀ i, Y i ⟶ X) (hsp : ∀ i, s i ≫ p i = 𝟙 (Y i)) (f : X ⟶ Z)
    (hbase : ∃ (i : ι) (u :
        (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj (Y i) ⟶
        (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z),
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f =
          (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map (p i) ≫ u ∧
        ∀ z : points B (Spec (.of (AlgebraicClosure k)))
            (B.contains_spec_algebraicClosure k hk)
            ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z),
          {x : points B (Spec (.of (AlgebraicClosure k)))
              (B.contains_spec_algebraicClosure k hk)
              ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj (Y i)) |
            pointsMap B (Spec (.of (AlgebraicClosure k)))
                (B.contains_spec_algebraicClosure k hk)
                ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj (Y i)) u x =
              z}.Finite) :
    ∃ (i : ι) (v : Y i ⟶ Z), f = p i ≫ v ∧
      ∀ z : points B (Spec (.of k)) hk Z,
        {y : points B (Spec (.of k)) hk (Y i) |
          pointsMap B (Spec (.of k)) hk (Y i) v y = z}.Finite :=
  exists_index_factorization_finite_fibres_of_relocalizeRestrict B k (AlgebraicClosure k) hk
    (B.contains_spec_algebraicClosure k hk) (algebraicClosureMap B k hk) Y hTterm hT hX hZ
    hXred qZ hqZ p s hsp f hbase

end AlgebraicGeometry.Space

end
