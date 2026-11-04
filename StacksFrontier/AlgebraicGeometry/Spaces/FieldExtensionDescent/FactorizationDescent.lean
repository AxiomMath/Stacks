module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.MorphismDescent

/-!
# Descending a factorization along an extension of the ground field

Let `k ⊆ K` be an extension of fields whose spectra are objects of a big fppf site, let
`p : X ⟶ Y` be a morphism of algebraic spaces over `k` admitting a section, and let
`f : X ⟶ Z`. A factorization of `f` through `p` constructed after base change to `K` descends
to `k`, the second factor being `s ≫ f` for the section `s`.

## Main results

* `AlgebraicGeometry.Space.relocalizeRestrict_map_section_comp`: the second factor is
  determined: if the base change of `f` factors through the base change of `p` by `u`, then
  `u` is the base change of `s ≫ f`. No hypothesis on the spaces is needed.
* `AlgebraicGeometry.Space.eq_comp_section_comp_of_relocalizeRestrict_factorization`:
  the factorization descends, `f = p ≫ (s ≫ f)`.
* `AlgebraicGeometry.Space.exists_factorization_of_relocalizeRestrict_factorization`: the same
  as an existence statement, together with the uniqueness of the descended second factor and
  the fact that it base changes to the given one.
* `AlgebraicGeometry.Space.exists_factorization_of_relocalizeRestrict_fieldExtensionMap`: the
  same for the morphism of spectra attached to a field extension `K/k`.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (g : B.obj hK ⟶ B.obj hk)

/-- **The second factor of a descended factorization is forced.** If `p : X ⟶ Y` has a section
`s` and the base change of `f : X ⟶ Z` factors through the base change of `p` by `u`, then `u`
is the base change of `s ≫ f`. -/
theorem relocalizeRestrict_map_section_comp
    {X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (u : (OverShriek.relocalizeRestrict g).obj Y ⟶ (OverShriek.relocalizeRestrict g).obj Z)
    (hfac : (OverShriek.relocalizeRestrict g).map f =
      (OverShriek.relocalizeRestrict g).map p ≫ u) :
    (OverShriek.relocalizeRestrict g).map (s ≫ f) = u := by
  rw [Functor.map_comp, hfac, ← Category.assoc, ← Functor.map_comp, hsp,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **A factorization through a split epimorphism descends along a field extension.** Let
`p : X ⟶ Y` be a morphism of algebraic spaces over a field `k` with a section `s`, let `X` be
reduced and let `f : X ⟶ Z` be a morphism to an algebraic space separated over a terminal
presheaf. If the base change of `f` along a morphism `Spec K ⟶ Spec k` of the site factors
through the base change of `p`, then `f` factors through `p`, by `s ≫ f`. -/
theorem eq_comp_section_comp_of_relocalizeRestrict_factorization
    {T X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (u : (OverShriek.relocalizeRestrict g).obj Y ⟶ (OverShriek.relocalizeRestrict g).obj Z)
    (hfac : (OverShriek.relocalizeRestrict g).map f =
      (OverShriek.relocalizeRestrict g).map p ≫ u) :
    f = p ≫ s ≫ f :=
  eq_of_relocalizeRestrict_map_eq_of_isTerminal B k K hk hK g hTterm hT hX hZ hXred
    qZ hqZ f (p ≫ s ≫ f) (by
      rwa [Functor.map_comp, relocalizeRestrict_map_section_comp B k K hk hK g p s hsp f u hfac])

/-- **A factorization through a split epimorphism descends uniquely along a field extension.**
Let `p : X ⟶ Y` be a morphism of algebraic spaces over a field `k` with a section, let `X` be
reduced, and let `f : X ⟶ Z` be a morphism to an algebraic space separated over a terminal
presheaf. If the base change of `f` along a morphism `Spec K ⟶ Spec k` of the site factors
through the base change of `p`, then `f` factors through `p` over `k`, by a *unique* morphism,
and that morphism base changes to the given second factor. -/
theorem exists_factorization_of_relocalizeRestrict_factorization
    {T X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (u : (OverShriek.relocalizeRestrict g).obj Y ⟶ (OverShriek.relocalizeRestrict g).obj Z)
    (hfac : (OverShriek.relocalizeRestrict g).map f =
      (OverShriek.relocalizeRestrict g).map p ≫ u) :
    ∃ v : Y ⟶ Z, f = p ≫ v ∧ (OverShriek.relocalizeRestrict g).map v = u ∧
      ∀ w : Y ⟶ Z, f = p ≫ w → w = v := by
  refine ⟨s ≫ f, eq_comp_section_comp_of_relocalizeRestrict_factorization B k K hk hK g
      hTterm hT hX hZ hXred qZ hqZ p s hsp f u hfac,
    relocalizeRestrict_map_section_comp B k K hk hK g p s hsp f u hfac, fun w hw => ?_⟩
  rw [hw, ← Category.assoc, hsp, Category.id_comp]

/-- `AlgebraicGeometry.Space.exists_factorization_of_relocalizeRestrict_factorization` for the
morphism of spectra attached to a field extension `K/k`: a factorization constructed after
extending the ground field descends. -/
theorem exists_factorization_of_relocalizeRestrict_fieldExtensionMap [Algebra k K]
    {T X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (u : (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj Y ⟶
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj Z)
    (hfac : (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map f =
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map p ≫ u) :
    ∃ v : Y ⟶ Z, f = p ≫ v ∧
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map v = u ∧
      ∀ w : Y ⟶ Z, f = p ≫ w → w = v :=
  exists_factorization_of_relocalizeRestrict_factorization B k K hk hK
    (fieldExtensionMap B k K hk hK) hTterm hT hX hZ hXred qZ hqZ p s hsp f u hfac

end AlgebraicGeometry.Space

end
