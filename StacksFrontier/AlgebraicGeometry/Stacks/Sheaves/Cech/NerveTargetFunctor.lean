module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveEquivalenceOver
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# Pushing the relative Čech nerve forward along the target

Let `p : X ⥤ C` and `q : Y ⥤ C` be categories over `C`, `f : U ⥤ X` a functor and `g : X ⥤ Y` a
functor with `g ⋙ q = p`. A Čech tuple of `f` (`Stacks.RelativeCech.Tuple`: entries of `U` over a
common object of `X`) is pushed forward along `g` to a Čech tuple of `f ⋙ g`, by applying `g` to
its target and to its comparison isomorphisms. This file records that this functor is compatible
with the projections on the nose and is fully faithful when `g` is faithful, and that the structure
functor of a term of the nerve is faithful when that of `U` is.

These are the two facts the reduction of Stacks 076Z / 0770 to the affine case uses about the
terms `U ×_X ⋯ ×_X U` of the nerve of a chart: a term maps by a monomorphism to the corresponding
term `U ×_Y ⋯ ×_Y U` of the composite, as soon as `X` is fibred in setoids over `Y`; and the terms
of the nerve of a chart from a scheme are fibred in setoids over the base.

## Main definitions

* `Stacks.RelativeCech.Tuple.mapTarget`: the pushforward of tuples along `g`.

## Main results

* `Stacks.RelativeCech.Tuple.mapTarget_comp_projection`: it lies over `g` on the nose.
* `Stacks.RelativeCech.Tuple.full_mapTarget`, `Stacks.RelativeCech.Tuple.faithful_mapTarget`.
* `Stacks.RelativeCech.Tuple.faithful_projection_comp`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vC vU vX vY uC uU uX uY

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  (p : X ⥤ C) (f : U ⥤ X) (q : Y ⥤ C) (g : X ⥤ Y) (hg : g ⋙ q = p)

namespace Tuple

include hg in
/-- The image under `g` of the comparison isomorphism of a tuple lies over an identity. -/
theorem isHomLift_map_comparison {n : ℕ} (a : Tuple p f n) (i : Fin (n + 1)) :
    q.IsHomLift (𝟙 (q.obj (g.obj a.target))) (g.map (a.comparison i).hom) := by
  subst hg
  have := a.comparison_lift i
  exact Functor.isHomLift_map_of_comp_eq (p := g ⋙ q) rfl (𝟙 ((g ⋙ q).obj a.target)) _

include hg in
/-- **The pushforward of Čech tuples along `g`**: a tuple of `f` over `x` goes to the tuple of
`f ⋙ g` over `g x` with the same entries and with the images of the comparison isomorphisms. -/
def mapTarget (n : ℕ) : Tuple p f n ⥤ Tuple q (f ⋙ g) n where
  obj a := ⟨g.obj a.target, a.source, fun i => g.mapIso (a.comparison i),
    fun i => isHomLift_map_comparison p f q g hg a i⟩
  map φ := ⟨g.map (Tuple.Hom.target (p := p) (f := f) φ), Tuple.Hom.source (p := p) (f := f) φ,
    fun i => by
    simp only [Functor.comp_map, Functor.mapIso_hom, ← g.map_comp,
      Tuple.Hom.comparison_naturality (p := p) (f := f) φ i]⟩
  map_id _ := Stacks.Cech.tupleHom_ext (g.map_id _) rfl
  map_comp _ _ := Stacks.Cech.tupleHom_ext (g.map_comp _ _) rfl

/-- The pushforward of tuples lies over `g`, on the nose. -/
theorem mapTarget_comp_projection (n : ℕ) :
    mapTarget p f q g hg n ⋙ projection q (f ⋙ g) n = projection p f n ⋙ g :=
  rfl

/-- The target morphism of a morphism of tuples is determined by its first entry. -/
theorem Hom.target_eq {n : ℕ} {a b : Tuple p f n} (φ : a ⟶ b) :
    Tuple.Hom.target φ =
      (a.comparison 0).inv ≫ f.map (Tuple.Hom.source φ 0) ≫ (b.comparison 0).hom := by
  rw [Tuple.Hom.comparison_naturality φ 0, Iso.inv_hom_id_assoc]

/-- A morphism of tuples is determined by its entries. -/
private theorem hom_ext_of_source_eq {n : ℕ} {a b : Tuple p f n} {φ ψ : a ⟶ b}
    (hs : Tuple.Hom.source φ = Tuple.Hom.source ψ) : φ = ψ :=
  Stacks.Cech.tupleHom_ext (by rw [Hom.target_eq p f φ, Hom.target_eq p f ψ, hs]) hs

/-- The pushforward of tuples along `g` is faithful. -/
theorem faithful_mapTarget (n : ℕ) : (mapTarget p f q g hg n).Faithful where
  map_injective {a b} φ ψ h := by
    have hs : Tuple.Hom.source φ = Tuple.Hom.source ψ :=
      congrArg (fun k : Tuple.Hom q (f ⋙ g) _ _ => k.source) h
    exact hom_ext_of_source_eq p f hs

/-- **The pushforward of tuples along a faithful `g` is full.** A morphism of the pushed-forward
tuples has its target morphism determined by its first entry, as for any morphism of tuples; that
determined morphism is a morphism of the original tuples because `g` is faithful. -/
theorem full_mapTarget [g.Faithful] (n : ℕ) : (mapTarget p f q g hg n).Full where
  map_surjective {a b} ψ := by
    let s : ∀ i, a.source i ⟶ b.source i := Tuple.Hom.source (p := q) (f := f ⋙ g) ψ
    let tt : g.obj a.target ⟶ g.obj b.target := Tuple.Hom.target (p := q) (f := f ⋙ g) ψ
    have hnat : ∀ i, g.map (f.map (s i)) ≫ g.map (b.comparison i).hom =
        g.map (a.comparison i).hom ≫ tt :=
      fun i => Tuple.Hom.comparison_naturality (p := q) (f := f ⋙ g) ψ i
    let t : a.target ⟶ b.target := (a.comparison 0).inv ≫ f.map (s 0) ≫ (b.comparison 0).hom
    have hgt : g.map t = tt := by
      simp only [t, Functor.map_comp]
      rw [hnat 0, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, g.map_id,
        Category.id_comp]
    refine ⟨⟨t, s, fun i => g.map_injective ?_⟩, ?_⟩
    · rw [Functor.map_comp, Functor.map_comp, hnat i, hgt]
    · exact Stacks.Cech.tupleHom_ext hgt rfl

/-- **The structure functor of a term of the nerve is faithful when that of the source is.** A
morphism of tuples is determined by its entries, each entry is determined by its image in `C`
because `f ⋙ p` is faithful, and that image is the image of the target morphism up to the
identifications along the comparison isomorphisms. -/
theorem faithful_projection_comp [(f ⋙ p).Faithful] (n : ℕ) :
    (projection p f n ⋙ p).Faithful where
  map_injective {a b} φ ψ h := by
    have hφψ : p.map (Tuple.Hom.target φ) = p.map (Tuple.Hom.target ψ) := h
    have hs : Tuple.Hom.source φ = Tuple.Hom.source ψ := by
      funext i
      apply (f ⋙ p).map_injective
      simp only [Functor.comp_map]
      rw [Tuple.map_source_eq p f φ i, Tuple.map_source_eq p f ψ i, hφψ]
    exact hom_ext_of_source_eq p f hs

end Tuple

end Stacks.RelativeCech
