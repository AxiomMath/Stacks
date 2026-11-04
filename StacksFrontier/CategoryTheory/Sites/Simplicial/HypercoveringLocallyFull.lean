module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.JoinLift
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent

/-!
# The localization functor of the total site of a hypercovering is locally full

Let `(C, J)` be a site with fibre products and let `K` be a hypercovering, either of the final
presheaf or of an object `X` of `C`. The total site `(C/K)_total` of the simplicial family of
sites `n ↦ C/K_n` has localization functor `j_total : (C/K)_total ⥤ C`, respectively
`j_total : (C/K)_total ⥤ C/X`, and this file proves that `j_total` is locally full, in both
cases.

Unwound, local fullness asks this: given an object of the total site in simplicial degree `m`,
that is a chart `A ⟶ K_{m, i}`, an object in degree `n`, a chart `B ⟶ K_{n, j}`, and a morphism
`f : A ⟶ B` of the site, the arrows `A' ⟶ A` along which `f` lifts to a morphism of the total
site form a covering sieve of `A`. A morphism of the total site out of a degree-`r` object
carries a simplex map, so a lift of `f` is a chart `A' ⟶ K_{r, t}` restricting to the two given
charts along two simplex maps `⦋m⦌ ⟶ ⦋r⦌` and `⦋n⦌ ⟶ ⦋r⦌`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isLocallyFull_totalForget`: `j_total` is locally
  full, for a hypercovering of the final presheaf.
* `CategoryTheory.SimplicialSemiRepresentable.isLocallyFull_totalForget_over`: `j_total` is
  locally full for the localized topology of `C/X`, for a hypercovering of the object `X`.

## References

* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 01GN](https://stacks.math.columbia.edu/tag/01GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering SSet.stdSimplex

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C]

omit [HasEqualizers C] [HasPullbacks C] in
/-- **A chart lying over another chart along a simplex map is a morphism of the total site.**
Given a chart `w : A' ⟶ K_{c, τ}`, a chart `u` of simplicial degree `c'`, a simplex map
`b : c ⟶ c'` and a morphism `g : A' ⟶ u.left` of `C` under which the `b`-restriction of `w` is
`u`, the pair `(b, g)` is a morphism of the total site over `g`. -/
theorem exists_totalHom_of_chart (K : SimplicialObject (FormalCoproduct.{u} C))
    {c c' : SimplexCategoryᵒᵖ} (b : c ⟶ c') {τ : (K.obj c).I} {A' : C}
    (w : A' ⟶ (K.obj c).obj τ) {i : (K.obj c').I} (u : Over ((K.obj c').obj i))
    (g : A' ⟶ u.left) (hi : (K.map b).f τ = i)
    (he : (w ≫ (K.map b).φ τ) ≫ eqToHom (congrArg (K.obj c').obj hi) = g ≫ u.hom) :
    ∃ ψ : (⟨c, ⟨τ, Over.mk w⟩⟩ : Grothendieck (slices K)) ⟶ ⟨c', ⟨i, u⟩⟩,
      (totalForget K).map ψ = g := by
  subst hi
  rw [eqToHom_refl, Category.comp_id] at he
  refine ⟨⟨b, CategoryTheory.Sigma.SigmaHom.mk (Over.homMk g he.symm)⟩, ?_⟩
  have hmap : (totalForget K).map
      (⟨b, CategoryTheory.Sigma.SigmaHom.mk (Over.homMk g he.symm)⟩ :
        (⟨c, ⟨τ, Over.mk w⟩⟩ : Grothendieck (slices K)) ⟶ ⟨c', ⟨(K.map b).f τ, u⟩⟩) =
      (eqToHom (totalForget_fib_eq K b)).app ⟨τ, Over.mk w⟩ ≫
        (sliceForget K c').map
          (CategoryTheory.Sigma.SigmaHom.mk (Over.homMk g he.symm)) := rfl
  have happ : (eqToHom (totalForget_fib_eq K b)).app
        (⟨τ, Over.mk w⟩ : ComponentOver (K.obj c)) =
      eqToHom (Functor.congr_obj (totalForget_fib_eq K b)
        (⟨τ, Over.mk w⟩ : ComponentOver (K.obj c))) := eqToHom_app _ _
  rw [hmap, happ]
  exact Category.id_comp g

/-- **The localization functor of the total site of a hypercovering is locally full.** For a
hypercovering `K` of the final presheaf of `(C, J)`, the functor `j_total : (C/K)_total ⥤ C` is
locally full: a morphism of `C` between the underlying objects of two objects of the total site
lifts, locally on its source, to a morphism of the total site. -/
instance isLocallyFull_totalForget (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    (totalForget H.toSimplicialObject).IsLocallyFull P.toGrothendieck := by
  set K := H.toSimplicialObject with hKdef
  constructor
  intro U V f
  obtain ⟨⟨cU⟩, iU, uU⟩ := U
  obtain ⟨⟨cV⟩, iV, uV⟩ := V
  induction cU using SimplexCategory.rec with | _ m => ?_
  induction cV using SimplexCategory.rec with | _ n => ?_
  refine P.toGrothendieck.superset_covering ?_
    (joinLiftSieve_mem P H m n (FormalCoproduct.Hom.fromIncl iU uU.hom)
      (FormalCoproduct.Hom.fromIncl iV (f ≫ uV.hom)))
  rintro A' g ⟨t, h₁, h₂⟩
  obtain ⟨hi₁, he₁⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₁ PUnit.unit
  obtain ⟨hi₂, he₂⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₂ PUnit.unit
  obtain ⟨ψ₁, hψ₁⟩ := exists_totalHom_of_chart K (joinFst m n).op (t.φ PUnit.unit) uU g hi₁ he₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_totalHom_of_chart K (joinSnd m n).op (t.φ PUnit.unit) uV
    (g ≫ f) hi₂ (he₂.trans (Category.assoc g f uV.hom).symm)
  exact ⟨_, ψ₁, 𝟙 A', ⟨ψ₂, hψ₂.trans (congrArg (fun z => z ≫ f) hψ₁.symm)⟩,
    hψ₁.symm.trans (Category.id_comp _).symm⟩

omit [HasEqualizers C] in
/-- **The localization functor of the total site of a hypercovering of an object is locally
full.** For a hypercovering `K` of an object `X` of `(C, P)` in the sense of Stacks 01G5, the
functor `j_total : (C/K)_total ⥤ C/X` is locally full for the localized topology: a morphism of
`C/X` between the underlying objects of two objects of the total site lifts, locally on its
source, to a morphism of the total site. -/
theorem isLocallyFull_totalForget_over (P : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{u} (Over X))) (hK : IsHypercovering P K) :
    (totalForget K).IsLocallyFull (P.toGrothendieck.over X) := by
  let : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  constructor
  intro U V f
  obtain ⟨⟨cU⟩, iU, uU⟩ := U
  obtain ⟨⟨cV⟩, iV, uV⟩ := V
  induction cU using SimplexCategory.rec with | _ m => ?_
  induction cV using SimplexCategory.rec with | _ n => ?_
  refine (P.toGrothendieck.over X).superset_covering ?_
    (joinLiftSieve_mem_over P K hK m n (FormalCoproduct.Hom.fromIncl iU uU.hom)
      (FormalCoproduct.Hom.fromIncl iV (f ≫ uV.hom)))
  rintro A' g ⟨t, h₁, h₂⟩
  obtain ⟨hi₁, he₁⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₁ PUnit.unit
  obtain ⟨hi₂, he₂⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₂ PUnit.unit
  obtain ⟨ψ₁, hψ₁⟩ := exists_totalHom_of_chart K (joinFst m n).op (t.φ PUnit.unit) uU g hi₁ he₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_totalHom_of_chart K (joinSnd m n).op (t.φ PUnit.unit) uV
    (g ≫ f) hi₂ (he₂.trans (Category.assoc g f uV.hom).symm)
  exact ⟨_, ψ₁, 𝟙 A', ⟨ψ₂, hψ₂.trans (congrArg (fun z => z ≫ f) hψ₁.symm)⟩,
    hψ₁.symm.trans (Category.id_comp _).symm⟩

end CategoryTheory.SimplicialSemiRepresentable

end
