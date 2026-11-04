module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
import StacksCore.Tactic.StacksAttribute

/-!
# Mayer--Vietoris for sheaf cohomology

For an abelian sheaf `F` on a site and a Mayer--Vietoris square `S`, Tag 01EB gives the long
exact cohomology sequence

`0 ⟶ H⁰(X₄,F) ⟶ H⁰(X₂,F) ⊞ H⁰(X₃,F) ⟶ H⁰(X₁,F) ⟶ H¹(X₄,F) ⟶ ...`

together with its functoriality in `F`. Applied to the square of two open subsets covering a
space, this is the Mayer--Vietoris sequence of the source for a sheaf of modules on a ringed
space, after forgetting to abelian groups.

Exactness of every six-term window of the sequence is Mathlib's
`GrothendieckTopology.MayerVietorisSquare.sequence_exact`. Two things have to be added. The
first is the leading zero, i.e. injectivity of `H⁰(X₄,F) ⟶ H⁰(X₂,F) ⊞ H⁰(X₃,F)`: under the
comparison with the contravariant `Ext` sequence of the square's short exact sequence, that map
is precomposition with the epimorphism of that short exact sequence, which is injective by
`Ext.precomp_mk₀_injective_of_epi`. The second is naturality of the connecting morphism in `F`;
naturality of the restriction maps is already part of
`Sheaf.cohomologyPresheafFunctor`, so only the connecting morphism needs a statement. Since the
connecting morphism is precomposition with the extension class of the square and the map
induced by `f : F ⟶ G` is postcomposition with `Ext.mk₀ f`, its naturality is exactly
associativity of Yoneda composition of `Ext` classes when the last degree is zero.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.mayerVietorisInitialSequence`: the initial six-arrow segment
  of the sequence, beginning with the zero group.

## Main results

* `Stacks.Cohomology.MayerVietoris.mayerVietorisInitialSequence_exact`: that initial segment is
  exact, leading zero included.
* `Stacks.Cohomology.MayerVietoris.mayerVietoris_delta_naturality`: the connecting morphisms are
  natural in the coefficient sheaf.
* `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact` carries the tag for
  the successive windows of the long exact sequence.

## Implementation notes

Everything is stated for an abelian sheaf on an arbitrary site and an arbitrary
Mayer--Vietoris square, which is more general than the ringed-space formulation of the source:
forget a sheaf of modules to an abelian sheaf and use `Opens.mayerVietorisSquare U V`.

The naturality proof deliberately avoids transporting the extension class along
`shortComplex_X₁` and `shortComplex_X₃`. Those equalities hold definitionally, so the two
connecting morphisms are already of the form `Ext.precomp` of one and the same class, and the
`rfl`-proof `hδ` below records that; writing the transport out instead forces the
elaborator to see through it.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.Cohomology.MayerVietoris

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite
open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- The initial segment
`0 ⟶ H⁰(X₄,F) ⟶ H⁰(X₂,F) ⊞ H⁰(X₃,F) ⟶ H⁰(X₁,F) ⟶ H¹(X₄,F)
  ⟶ H¹(X₂,F) ⊞ H¹(X₃,F) ⟶ H¹(X₁,F)`
of the Mayer--Vietoris sequence. -/
noncomputable abbrev mayerVietorisInitialSequence : ComposableArrows AddCommGrpCat.{w} 6 :=
  (S.sequence F 0 1 rfl).precomp
    (0 : AddCommGrpCat.of PUnit.{w + 1} ⟶ F.H' 0 S.X₄)

/-- The Mayer--Vietoris sequence is exact at its initial segment, including the leading zero. -/
@[stacks 01EB "initial segment"]
lemma mayerVietorisInitialSequence_exact :
    (mayerVietorisInitialSequence S F).Exact := by
  apply ComposableArrows.exact_of_δ₀
  · have hz : (mayerVietorisInitialSequence S F).map' 0 1 ≫
        (mayerVietorisInitialSequence S F).map' 1 2 = 0 := by
      simp [mayerVietorisInitialSequence]
    rw [ComposableArrows.exact₂_iff _ (ComposableArrows.isComplex₂_mk _ hz),
      ShortComplex.exact_iff_mono _ (by simp [mayerVietorisInitialSequence])]
    let hi := (S.sequenceIso F 0 1 rfl).hom
    have : IsIso (hi.app 0) := by dsimp only [hi]; infer_instance
    have e : (0 : Fin 6) ⟶ (1 : Fin 6) := ⟨PLift.up (show (0 : ℕ) ≤ 1 by decide)⟩
    have hc := hi.naturality e
    dsimp [mayerVietorisInitialSequence, ComposableArrows.precomp,
      ComposableArrows.Precomp.map] at hc ⊢
    have hmono : Mono (S.toBiprod F 0 ≫ hi.app 1) := by
      rw [hc]
      have : Mono
          ((Ext.contravariantSequence S.shortComplex_shortExact F 0 1 (by omega)).map e) := by
        dsimp only [Ext.contravariantSequence]
        exact ConcreteCategory.mono_of_injective _
          (Ext.precomp_mk₀_injective_of_epi F S.shortComplex.g)
      exact mono_comp _ _
    exact mono_of_mono (S.toBiprod F 0) (hi.app 1)
  · exact S.sequence_exact F 0 1 rfl

/-- The sheaf representing cohomology of the object `X`, namely the sheafification of the free
abelian presheaf on `X`. -/
@[sga "4 XVIII 1.4.24"]
private noncomputable abbrev representingSheaf (J : GrothendieckTopology C) (X : C)
    [HasWeakSheafify J AddCommGrpCat.{v}] : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj X ⋙ AddCommGrpCat.free)

omit [HasWeakSheafify J (Type v)] in
private lemma cohomology_map_app {G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (X : C) :
    ((Sheaf.cohomologyPresheafFunctor.{w, v, u} J n).map f).app (op X) =
      AddCommGrpCat.ofHom ((Ext.mk₀ f).postcomp (representingSheaf J X) (add_zero n)) := by
  dsimp [Sheaf.cohomologyPresheafFunctor, Abelian.extFunctor]
  rw [Abelian.extFunctorObj_map]

/-- The connecting morphisms in the Mayer--Vietoris long exact sequence are natural in the
coefficient sheaf. -/
@[stacks 01EB "functoriality"]
lemma mayerVietoris_delta_naturality {G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ ((Sheaf.cohomologyPresheafFunctor J n₁).map f).app (op S.X₄) =
      ((Sheaf.cohomologyPresheafFunctor J n₀).map f).app (op S.X₁) ≫ S.δ G n₀ n₁ h := by
  have hh : 1 + n₀ = n₁ := by omega
  rw [cohomology_map_app (F := F) f n₁ S.X₄, cohomology_map_app (F := F) f n₀ S.X₁]
  have hδ (H : Sheaf J AddCommGrpCat.{v}) : S.δ H n₀ n₁ h =
      AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp H hh) := rfl
  rw [hδ F, hδ G]
  ext x
  exact Ext.comp_assoc_of_third_deg_zero _ x (Ext.mk₀ f) hh

add_to_stacks 01EB "successive windows"
  CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact

end Stacks.Cohomology.MayerVietoris
