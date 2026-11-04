module

public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Inverse image with a left adjoint, and pro-étale inverse image along a closed immersion

Let `(C, J)` and `(D, K)` be sites and let `G : C ⥤ D` be a continuous functor, so that
restriction along `G` is the inverse image `g⁻¹ = G.sheafPushforwardContinuous A J K` of the
associated morphism of topoi and the sheafified left Kan extension `g_! =
Functor.sheafPullbackConstruction.sheafPullback G A J K` is its left adjoint.  Suppose `G` has a
left adjoint `W : D ⥤ C` which is itself continuous.  Then restriction along `W` already lands in
sheaves and is a left adjoint of `g⁻¹`, so by uniqueness of left adjoints `g_!` *is* restriction
along `W`: no sheafification intervenes and `g_!F(V) = F(W V)` on the nose.  In particular `g_!`
is itself a right adjoint, i.e. it has a left adjoint of its own.

This is the mechanism by which Stacks 09BL (3) produces a left adjoint of the pro-étale inverse
image along a closed immersion `i : Z ⟶ X` of affine schemes: Stacks 09BK supplies a fully
faithful left adjoint of pro-étale base change, and the present file turns such a left adjoint
into the conclusion of 09BL (3) for the small pro-étale sites, uniformly in the universe of the
sheaves' values.  The input — a continuous left adjoint of
`AlgebraicGeometry.Scheme.proetaleBaseChange i` on the unrestricted small pro-étale sites — is
carried here as an explicit hypothesis; nothing in this file asserts its existence.

## Main definitions

* `CategoryTheory.Adjunction.sheafPullbackConstructionIso`: if the continuous functor `G` has a
  continuous left adjoint `W`, then `g_!` is restriction along `W`.
* `CategoryTheory.Adjunction.sheafPullbackConstructionObjIso`: consequently `g_!F(V) = F(W V)`.

## Main results

* `CategoryTheory.Adjunction.isRightAdjoint_sheafPullbackConstruction`: a lower shriek along a
  continuous functor with a continuous left adjoint has itself a left adjoint.
* `AlgebraicGeometry.Scheme.isRightAdjoint_proetaleInverseImage_of_adjunction`: the pro-étale
  inverse image along a morphism of schemes has a left adjoint as soon as pro-étale base change
  along that morphism has a continuous left adjoint.

## Implementation notes

* The functors are Mathlib's.  Inverse image is `Functor.sheafPushforwardContinuous`, which on
  underlying presheaves is restriction along `G.op`, and lower shriek is
  `Functor.sheafPullbackConstruction.sheafPullback`, the sheafification of the left Kan extension
  along `G.op`; the latter is the functor named by the pro-étale statement, which is why the
  identification is made for it rather than for the abstract left adjoint
  `Functor.sheafPullback`.
* The adjunction `w^s ⊣ g⁻¹` between the two restriction functors is
  `CategoryTheory.Adjunction.sheafPushforwardAdjunction`; the identification of `g_!` with `w^s`
  is then uniqueness of left adjoints.  Stacks 08NH (2), proved in
  `StacksFrontier.CategoryTheory.Sites.Cocontinuous.LeftAdjoint`, is the same statement for the
  explicit composite `sheafToPresheaf ⋙ restriction along W.op ⋙ presheafToSheaf` rather than
  for Mathlib's `sheafPullback`.
* The scheme-level statement is made for an arbitrary morphism of schemes rather than for a
  closed immersion of affine schemes: affineness and closedness enter Stacks 09BL only through
  the construction of the left adjoint, which is the hypothesis here, so assuming them would
  only weaken the statement.  Values are taken in `Type (max (u + 1) v)` with `v` free, the
  small pro-étale category of a scheme over `Type u` being a `Type (u + 1)` with morphisms in
  `Type u`; every size hypothesis of the general results holds there for every `v`.

## References

* [Stacks Project, Tag 08NH](https://stacks.math.columbia.edu/tag/08NH)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {G : C ⥤ D} {W : D ⥤ C}

/-- If a continuous functor of sites `G : C ⥤ D` has a continuous left adjoint `W : D ⥤ C`, then
the lower shriek `g_!` along `G` is restriction along `W`.

Both are left adjoints of restriction along `G`: the first by
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, the second by
`CategoryTheory.Adjunction.sheafPushforwardAdjunction`, which restricts to sheaves the adjunction
between precomposition along `W.op` and precomposition along `G.op`. -/
public def sheafPullbackConstructionIso (adj : W ⊣ G) [G.IsContinuous J K] [W.IsContinuous K J]
    [HasWeakSheafify K A] [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback G A J K ≅
      W.sheafPushforwardContinuous A K J :=
  leftAdjointUniq (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K)
    (adj.sheafPushforwardAdjunction A)

/-- For a continuous functor of sites `G` with a continuous left adjoint `W`, the sections of
`g_!F` over an object `V` of `D` are the sections of `F` over `W V`: the sheafification in the
construction of `g_!` changes nothing. -/
public def sheafPullbackConstructionObjIso (adj : W ⊣ G) [G.IsContinuous J K]
    [W.IsContinuous K J] [HasWeakSheafify K A]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F] (F : Sheaf J A) (V : D) :
    ((Functor.sheafPullbackConstruction.sheafPullback G A J K).obj F).obj.obj (Opposite.op V) ≅
      F.obj.obj (Opposite.op (W.obj V)) :=
  ((sheafToPresheaf K A).mapIso ((sheafPullbackConstructionIso adj).app F)).app (Opposite.op V)

/-- If a continuous functor of sites `G : C ⥤ D` has a continuous left adjoint `W : D ⥤ C`, then
the lower shriek `g_!` along `G` has itself a left adjoint, namely the lower shriek `w_!`
along `W`.

By `CategoryTheory.Adjunction.sheafPullbackConstructionIso` the functor `g_!` is restriction
along `W`, which is the inverse image of the morphism of topoi attached to `W` and hence has the
left adjoint built by `CategoryTheory.Functor.sheafPullbackConstruction`. -/
public theorem isRightAdjoint_sheafPullbackConstruction (adj : W ⊣ G) [G.IsContinuous J K]
    [W.IsContinuous K J] [HasWeakSheafify K A] [HasWeakSheafify J A]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]
    [∀ F : Dᵒᵖ ⥤ A, W.op.HasLeftKanExtension F] :
    (Functor.sheafPullbackConstruction.sheafPullback G A J K).IsRightAdjoint :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous W A K J).ofNatIsoRight
    (sheafPullbackConstructionIso adj).symm).isRightAdjoint

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme

universe u v

/-- The pro-étale inverse image along a morphism of schemes `i : Z ⟶ X`, on sheaves of sets for
the unrestricted small pro-étale sites, has a left adjoint as soon as pro-étale base change
along `i` has a continuous left adjoint `W`.

For a closed immersion of affine schemes such a `W` is the fully faithful lift of Stacks 09BK,
and the conclusion is Stacks 09BL (3).  The hypothesis is the whole mathematical content: it is
not proved here, and it is the only thing missing for 09BL (3), at every universe `v` of
values. -/
public theorem isRightAdjoint_proetaleInverseImage_of_adjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    (W : Z.ProEt ⥤ X.ProEt)
    [W.IsContinuous (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X)]
    (adj : W ⊣ Scheme.proetaleBaseChange i) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
      (Type (max (u + 1) v)) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).IsRightAdjoint :=
  Adjunction.isRightAdjoint_sheafPullbackConstruction (A := Type (max (u + 1) v)) adj

end AlgebraicGeometry.Scheme

end
