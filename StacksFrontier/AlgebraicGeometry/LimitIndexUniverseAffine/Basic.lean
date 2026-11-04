module

public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.AffineAtLateStage.Basic

/-!
# Affineness at a late stage of a limit of schemes, at an independent index universe

Let `X = lim X_i` be a cofiltered limit of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S`, with affine transition morphisms. If the induced
morphism `X ⟶ S` is affine, then the structure morphism `X_j ⟶ S` is affine for every
sufficiently late stage `j`.

Here the index category `I : Type uI` with `[Category.{uI} I]` lives in a universe independent of
the universe of the schemes `Scheme.{uS}`, under two hypotheses on `I`:

* `CategoryTheory.LocallySmall.{uS} I`: the hom types of `I` are `uS`-small;
* `CategoryTheory.InitiallySmall.{uS} I`: `I` receives an initial functor from a `uS`-small
  category, which for cofiltered `I` is the existence of a `uS`-small cofinal set of objects.

## Main results

* `Stacks.AlgebraicGeometry.AffineLateStage.exists_isAffineHom_of_initiallySmall`: one stage whose
  structure morphism is affine, with the structure morphisms given as a compatible family.
* `Stacks.AlgebraicGeometry.AffineLateStage.eventually_isAffineHom_of_isLimit_of_initiallySmall`:
  every sufficiently late stage is affine over `S`, under the two hypotheses above.
* `Stacks.AlgebraicGeometry.AffineLateStage.eventually_isAffineHom_of_isLimit_of_essentiallySmall`:
  the same for an index category that is `CategoryTheory.EssentiallySmall.{uS}`.
* `Stacks.AlgebraicGeometry.AffineLateStage.eventually_isAffineHom_of_isLimit_of_thin`: the same
  for a thin index category, with `CategoryTheory.InitiallySmall.{uS} I` as the only smallness
  hypothesis.

## References

* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall AlgebraicGeometry

universe uI v uS

namespace Stacks.AlgebraicGeometry.AffineLateStage

section

variable {I : Type uI} [Category.{v} I] {S : Scheme.{uS}} (D : I ⥤ Scheme.{uS}) (c : Cone D)
  (p : ∀ i, D.obj i ⟶ S)

variable [IsCofiltered I] [LocallySmall.{uS} I] [InitiallySmall.{uS} I]
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [QuasiSeparatedSpace S]

/-- Let `D` be a cofiltered diagram of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S` with affine transition morphisms, indexed by a
category `I` that is `LocallySmall.{uS}` and `InitiallySmall.{uS}`, with the structure morphisms
given as a compatible family `p`, and let `f` be the induced morphism from a limit of `D` to `S`.
If `f` is affine then `p i` is affine for some stage `i`. -/
theorem exists_isAffineHom_of_initiallySmall [CompactSpace S]
    (hp : ∀ {i j : I} (g : j ⟶ i), p j = D.map g ≫ p i)
    (hc : IsLimit c) {f : c.pt ⟶ S} (hf : ∀ i, c.π.app i ≫ p i = f) [IsAffineHom f] :
    ∃ i : I, IsAffineHom (p i) := by
  have h₁ : ∀ {a b : CofilteredInitialModel.{uS} I} (g : a ⟶ b),
      IsAffineHom ((fromCofilteredInitialModel.{uS} I ⋙ D).map g) := by
    intros; dsimp; infer_instance
  have h₂ : ∀ a, CompactSpace ((fromCofilteredInitialModel.{uS} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  have h₃ : ∀ a, QuasiSeparatedSpace ((fromCofilteredInitialModel.{uS} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  obtain ⟨a, ha⟩ := AffineAtLateStage.exists_isAffineHom
    (fromCofilteredInitialModel.{uS} I ⋙ D)
    (c.whisker (fromCofilteredInitialModel.{uS} I))
    (fun a ↦ p ((fromCofilteredInitialModel.{uS} I).obj a))
    (fun g ↦ hp ((fromCofilteredInitialModel.{uS} I).map g))
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{uS} I) c).symm hc)
    (f := f) (fun a ↦ hf ((fromCofilteredInitialModel.{uS} I).obj a))
  exact ⟨_, ha (𝟙 a)⟩

end

/-- Let `X = lim X_i` be a cofiltered limit of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S`, with affine transition morphisms, indexed by a
category `I` in a universe independent of the scheme universe. Assume
`CategoryTheory.LocallySmall.{uS} I` and `CategoryTheory.InitiallySmall.{uS} I`. If the induced
morphism `X ⟶ S` is affine, then so is the structure morphism of every sufficiently late
stage. -/
theorem eventually_isAffineHom_of_isLimit_of_initiallySmall
    {I : Type uI} [Category.{uI} I] [IsCofiltered I]
    [LocallySmall.{uS} I] [InitiallySmall.{uS} I]
    {S : Scheme.{uS}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{uS}) (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j) := by
  obtain ⟨i, hi⟩ := exists_isAffineHom_of_initiallySmall D c (fun i ↦ t.app i)
    (fun g ↦ by simp) hc (f := f)
    (fun i ↦ by simpa using congrArg (fun α ↦ NatTrans.app α i) hf)
  refine ⟨i, fun {j} g ↦ ?_⟩
  rw [show t.app j = D.map g ≫ t.app i from by simp]
  infer_instance

/-- Let `X = lim X_i` be a cofiltered limit of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S`, with affine transition morphisms, indexed by a
category `I` that is `CategoryTheory.EssentiallySmall.{uS}`. If the induced morphism `X ⟶ S` is
affine, then so is the structure morphism of every sufficiently late stage. -/
theorem eventually_isAffineHom_of_isLimit_of_essentiallySmall
    {I : Type uI} [Category.{uI} I] [IsCofiltered I] [EssentiallySmall.{uS} I]
    {S : Scheme.{uS}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{uS}) (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j) :=
  have : LocallySmall.{uS} I := locallySmall_of_essentiallySmall I
  have : InitiallySmall.{uS} I := initiallySmall_of_essentiallySmall I
  eventually_isAffineHom_of_isLimit_of_initiallySmall D t c hc f hf

/-- Let `X = lim X_i` be a cofiltered limit of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base `S`, with affine transition morphisms, indexed by a thin
category `I` in a universe independent of the scheme universe that is
`CategoryTheory.InitiallySmall.{uS} I`. If the induced morphism `X ⟶ S` is affine, then so is the
structure morphism of every sufficiently late stage. -/
theorem eventually_isAffineHom_of_isLimit_of_thin
    {I : Type uI} [Category.{uI} I] [IsCofiltered I] [Quiver.IsThin I]
    [InitiallySmall.{uS} I]
    {S : Scheme.{uS}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{uS}) (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsAffineHom f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsAffineHom (t.app j) :=
  eventually_isAffineHom_of_isLimit_of_initiallySmall D t c hc f hf

end Stacks.AlgebraicGeometry.AffineLateStage

end
