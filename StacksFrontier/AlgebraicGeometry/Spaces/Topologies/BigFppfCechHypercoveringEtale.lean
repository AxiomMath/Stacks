module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfCechHypercovering
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertyCovering

/-!
# The structure maps of a Čech hypercovering by an étale representable morphism

Let `b₀ : V₀ ⟶ Y` be an étale, relatively representable morphism of algebraic spaces and
`f : X ⟶ Y`. The simplicial algebraic space `U = (n ↦ V_n ×_Y X)` is the Čech nerve of
`V₀ ×_Y X ⟶ X`, a hypercovering for the pretopology of étale relatively representable morphisms;
hence its face maps are étale and relatively representable (Stacks 0DER), and so are their
composites, such as the last-vertex maps `U_n ⟶ U_0`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.etaleRepresentable_cechOverPullback_delta`: the face maps.
* `AlgebraicGeometry.BigFppfSpaceSite.etaleRepresentable_cechOverPullback_const_last`: the
  last-vertex maps `U_n ⟶ U_0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial Stacks.CategoryTheory.Hypercovering
open AlgebraicGeometry.Space

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The étale, relatively representable morphisms of algebraic spaces of `T`. -/
def etaleRepresentable : MorphismProperty T.Spaces := fun _ _ g =>
  Space.IsEtale T.schemeSite S T.scheme_mem g.hom ∧ yoneda.relativelyRepresentable g.hom

/-- Étale, relatively representable morphisms are stable under base change. -/
instance : (etaleRepresentable T).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _} _ _ _ _ sq hg :=
    ⟨isEtale_of_isPullback T.schemeSite S T.scheme_mem _ _ _ _ sq hg.1,
      (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
        (AlgebraicSpaces.isPullback_hom T.schemeSite S T.scheme_mem sq) hg.2⟩

/-- Identities are étale and relatively representable, and so are composites of such morphisms. -/
instance : (etaleRepresentable T).IsMultiplicative where
  id_mem X := ⟨isEtale_id T.schemeSite S T.scheme_mem X.1,
    Functor.relativelyRepresentable.of_isIso _ _⟩
  comp_mem _ _ hg hh := ⟨isEtale_comp T.schemeSite S T.scheme_mem hg.1 hh.1,
    yoneda.relativelyRepresentable.comp_mem _ _ hg.2 hh.2⟩

variable {T} {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)

/-- **The face maps of `n ↦ V_n ×_Y X` are étale and relatively representable** when `b₀` is:
the augmentation is a hypercovering for the pretopology of such morphisms (Stacks 09X8), whose
face maps belong to it (Stacks 0DER). -/
theorem etaleRepresentable_cechOverPullback_delta (hb₀ : etaleRepresentable T b₀) (n : ℕ)
    (i : Fin (n + 2)) :
    etaleRepresentable T
      ((cechOverPullback b₀ f ⋙ Over.forget X).map (SimplexCategory.δ i).op) := by
  have hs : ∀ {A Z : T.Spaces} (g : A ⟶ Z),
      Presieve.singleton g ∈ (etaleRepresentable T).pretopology Z ↔ etaleRepresentable T g :=
    fun g => Stacks.CategoryTheory.Hypercovering.singleton_mem_pretopology _ g
  have h := isHypercoveringAugmentation_cechOverPullback (etaleRepresentable T).pretopology b₀ f
    ((hs b₀).2 hb₀)
  let A : SimplicialObject.Augmented T.Spaces :=
    { left := cechOverPullback b₀ f ⋙ Over.forget X, right := X
      hom := overAugmentation (cechOverPullback b₀ f) }
  have hA : (etaleRepresentable T).IsHypercovering A :=
    { map_zero := (hs _).1 h.1
      map_one := (hs _).1 h.2.1
      matching := fun n hn => (hs _).1 (h.2.2 n hn) }
  exact MorphismProperty.IsHypercovering.face_mem _ hA n i

/-- **The last-vertex maps `U_n ⟶ U_0` of `n ↦ V_n ×_Y X` are étale and relatively
representable** when `b₀` is: they are composites of face maps. -/
theorem etaleRepresentable_cechOverPullback_const_last (hb₀ : etaleRepresentable T b₀)
    (n : ℕ) :
    etaleRepresentable T ((cechOverPullback b₀ f ⋙ Over.forget X).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) := by
  induction n with
  | zero =>
    have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ (Fin.last 0) = 𝟙 _ :=
      SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦
        Subsingleton.elim (α := Fin 1) _ _))
    rw [h0, op_id, CategoryTheory.Functor.map_id]
    exact MorphismProperty.id_mem _ _
  | succ n ih =>
    have e : SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) =
        SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) ≫ SimplexCategory.δ 0 :=
      SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ by
        simp [SimplexCategory.δ]))
    rw [e, op_comp, CategoryTheory.Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _
      (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ n 0) ih

/-- If `b₀` is étale and relatively representable, then so is the map `U(v)` of
`U = (n ↦ V_n ×_Y X)` along a composite `v = δ i ≫ δ j` of two coface maps. -/
theorem etaleRepresentable_cechOverPullback_delta_comp_delta (hb₀ : etaleRepresentable T b₀)
    (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3)) (v : ⦋n⦌ ⟶ ⦋n + 2⦌)
    (h : SimplexCategory.δ i ≫ SimplexCategory.δ j = v) :
    etaleRepresentable T ((cechOverPullback b₀ f ⋙ Over.forget X).map v.op) := by
  subst h
  rw [op_comp, CategoryTheory.Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ _ j)
    (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ _ i)

end AlgebraicGeometry.BigFppfSpaceSite

end
