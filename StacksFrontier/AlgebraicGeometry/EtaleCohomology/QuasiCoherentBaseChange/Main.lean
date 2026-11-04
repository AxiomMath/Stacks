module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Zero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Embedding

/-!
# The étale cohomology of a quasi-coherent module under flat affine base change spans

Let `X ⟶ S` be a quasi-compact separated scheme over an affine scheme, `S' ⟶ S` a flat morphism
of affine schemes and `Y = X ×_S S'`. For every quasi-coherent `𝒪_X`-module `ℱ` and every degree
`q`, the classes of `H^q(Y_étale, (g^* ℱ)ᵉ)` are finite sums of images of classes of
`H^q(X_étale, ℱᵉ)` under the base change map, multiplied by functions coming from `S'`.

This is the étale incarnation of the surjectivity half of flat base change
(Stacks 02KH), proved directly on the small étale site by dimension shifting: degree zero is
`AlgebraicGeometry.QcohEtale.spans_zero`, and the induction step embeds `ℱ` into a module
whose étale cohomology upstairs vanishes in positive degrees
(`AlgebraicGeometry.QcohEtale.exists_embedding`).

## Main results

* `AlgebraicGeometry.QcohEtale.spans_of_isPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.QcohEtale

/-- `Ext` of abelian sheaves at the object universe of the small étale site. -/
local instance (priority := high) hasExt_smallEtale_succ'' (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- **The base change map spans in every degree.** -/
theorem spans_of_isPullback {S S' X Y : Scheme.{u}} [IsAffine S] [IsAffine S'] {f : X ⟶ S}
    {q : S' ⟶ S} [Flat q] [CompactSpace X] [IsSeparated (terminal.from X)] {g : Y ⟶ X}
    {h : Y ⟶ S'} (hpb : IsPullback g h f q) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Spans.{u + 1} g (fun b : Γ(S', ⊤) => h.appTop b) F n := by
  have : Flat g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : IsAffineHom g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_iff_quasiSeparated X).mpr inferInstance
  exact spans_of_forall g _ (fun F _ => spans_zero hpb F) (fun F _ => exists_embedding g F) n F

end AlgebraicGeometry.QcohEtale

end
