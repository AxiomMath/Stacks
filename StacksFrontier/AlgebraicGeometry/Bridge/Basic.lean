module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of modules along a closed immersion of ringed spaces is fully faithful

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and whose comorphism of structure sheaves `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective as a
morphism of sheaves. This file proves that `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is fully faithful.
This is the full-faithfulness assertion of Stacks Tag 08KS.

## Main results

* `Stacks.Tag08KS.modulePushforward_fullyFaithful`: **Stacks 08KS**, full faithfulness of
  `RingedSpaceModuleAdjunction.modulePushforward i`, as a `Nonempty`-truncated
  `CategoryTheory.Functor.FullyFaithful`.
* `Stacks.Tag08KS.modulePushforward_full` and `Stacks.Tag08KS.modulePushforward_faithful`:
  the two halves, as the typeclasses the category-theoretic API consumes.

## Implementation notes

Fullness factors into two independent steps, matching the two hypotheses.

Faithfulness and the *presheaf-level* fullness come from the closed embedding alone: the
underlying presheaf of abelian groups of `i_* F` is the presheaf pushforward of that of `F`
(Mathlib's `PresheafOfModules.pushforwardCompToPresheaf` is `Iso.refl`), and presheaf
pushforward along an inducing map is fully faithful
(`ClosedImmersionSheaves.presheafPushforwardFullyFaithful`). So an `𝒪_X`-linear map between
pushforwards has a unique additive preimage, and the only thing to check is that the preimage
is `𝒪_Z`-linear. That is checked open by open, using
`Topology.IsInducing.map_functorObj` to realize an arbitrary open of `Z` as the preimage of an
open of `X`, where linearity is the hypothesis.

Surjectivity of `i^♯` enters only to turn an `𝒪_X`-linear morphism between pushforwards into
an `i_*𝒪_Z`-linear one, via `PresheafOfModules.restrictHomEquivOfIsLocallySurjective`; this is
where the sheaf condition on the target is used.

The statement is deliberately phrased with the closed-embedding and local-surjectivity
hypotheses as explicit arguments on a bare morphism of ringed spaces rather than bundled into
a structure, so that it applies to a closed immersion of schemes with no transport: see
`StacksFrontier/AlgebraicGeometry/Bridge/SchemeBridge.lean`.

`Functor.FullyFaithful` carries a choice of inverse on every hom-set, so its existence is
propositionally truncated with `Nonempty`; the two instance-shaped corollaries are what
callers actually use.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08KS

/-- For an inducing continuous map, a morphism of presheaves of modules between pushforwards
has an `𝒪_Z`-linear preimage.

The additive preimage exists because presheaf pushforward along an inducing map is fully
faithful. Linearity over an arbitrary open `W` of `Z` is read off from linearity over
`IsInducing.functor.obj W`, whose preimage is `W` on the nose. -/
private lemma pushforward₀_full_of_isInducing
    {X Z : TopCat.{u}} (i : Z ⟶ X)
    (hi : Topology.IsInducing (ConcreteCategory.hom i))
    (R : (Opens Z)ᵒᵖ ⥤ RingCat.{u})
    (M N : PresheafOfModules.{u} R)
    (g : (PresheafOfModules.pushforward₀ (Opens.map i) R).obj M ⟶
      (PresheafOfModules.pushforward₀ (Opens.map i) R).obj N) :
    ∃ h : M ⟶ N, (PresheafOfModules.pushforward₀ (Opens.map i) R).map h = g := by
  let ff := ClosedImmersionSheaves.presheafPushforwardFullyFaithful
    (C := AddCommGrpCat.{u}) hi
  let gAb : (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj M.presheaf ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj N.presheaf :=
    (PresheafOfModules.toPresheaf _).map g
  let hAb := ff.preimage gAb
  have hh := ff.map_preimage gAb
  have hlin_all (U : Opens X) (r : R.obj (op ((Opens.map i).obj U)))
      (m : M.obj (op ((Opens.map i).obj U))) :
      hAb.app _ (r • m) = r • hAb.app _ m := by
    have hraw : hAb.app (op ((Opens.map i).obj U)) = gAb.app (op U) :=
      congrArg (fun t => t.app (op U)) hh
    rw [hraw]
    exact (g.app (op U)).hom.map_smul r m
  let h : M ⟶ N := PresheafOfModules.homMk hAb (by
    intro W r m
    have hW := hlin_all (hi.functor.obj W.unop)
    have heq : (Opens.map i).obj (hi.functor.obj W.unop) = W.unop :=
      hi.map_functorObj W.unop
    rw [heq] at hW
    simpa only [op_unop] using hW r m)
  exact ⟨h, (PresheafOfModules.toPresheaf _).map_injective hh⟩

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- Surjectivity of the comorphism of structure sheaves, in the form
`CategoryTheory.SheafOfModules.restrictScalars` consumes: local surjectivity of the
`RingCat`-valued `RingedSpaceModuleAdjunction.structureSheafHom`. -/
private lemma isLocallySurjective_structureSheafHom
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (structureSheafHom i).hom := by
  change Presheaf.IsLocallySurjective _
    (whiskerRight i.hom.c (forget₂ CommRingCat RingCat))
  exact ⟨fun s => hs.imageSieve_mem s⟩

/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules along a morphism of ringed
spaces whose underlying continuous map is a closed embedding and whose comorphism of structure
sheaves is surjective is fully faithful. -/
@[stacks 08KS "full_faithfulness"]
theorem modulePushforward_fullyFaithful
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    Nonempty (modulePushforward i).FullyFaithful := by
  let F := modulePushforward i
  have hsurj := isLocallySurjective_structureSheafHom i hs
  have : F.Full := ⟨by
    intro M N g
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (α := (structureSheafHom i).hom)
      (M₁ := (PresheafOfModules.pushforward₀ (Opens.map i.hom.base)
        (structureSheafRing Z).obj).obj M.val)
      (M₂ := (PresheafOfModules.pushforward₀ (Opens.map i.hom.base)
        (structureSheafRing Z).obj).obj N.val)
      (hM₂ := (F.obj N).isSheaf)
    obtain ⟨h₀, hh₀⟩ := pushforward₀_full_of_isInducing i.hom.base hi.isInducing
      (structureSheafRing Z).obj M.val N.val (e.symm g.val)
    refine ⟨⟨h₀⟩, ?_⟩
    apply SheafOfModules.hom_ext
    change e ((PresheafOfModules.pushforward₀ (Opens.map i.hom.base)
      (structureSheafRing Z).obj).map h₀) = g.val
    rw [hh₀]
    exact e.apply_symm_apply g.val⟩
  have : F.Faithful := ⟨by
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply (ClosedImmersionSheaves.presheafPushforwardFullyFaithful
      (C := AddCommGrpCat.{u}) hi.isInducing).map_injective
    exact congrArg (fun k : F.obj M ⟶ F.obj N =>
      (PresheafOfModules.toPresheaf _).map k.val) h⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules along a closed immersion of
ringed spaces is full. -/
@[stacks 08KS "full_faithfulness"]
theorem modulePushforward_full
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    (modulePushforward i).Full :=
  (Classical.choice (modulePushforward_fullyFaithful i hi hs)).full

/-- **Stacks Project, Tag 08KS.** Pushforward of sheaves of modules along a closed immersion of
ringed spaces is faithful. -/
@[stacks 08KS "full_faithfulness"]
theorem modulePushforward_faithful
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    (modulePushforward i).Faithful :=
  (Classical.choice (modulePushforward_fullyFaithful i hi hs)).faithful

end Stacks.Tag08KS
