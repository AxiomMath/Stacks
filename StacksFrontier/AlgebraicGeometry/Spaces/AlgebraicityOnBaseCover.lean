module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProduct

/-!
# Algebraicity of an fppf sheaf is detected on an open covering of the base

Let `S` be a scheme contained in a big fppf site and let `{jᵢ : Tᵢ ⟶ S}` be a finite family of
open immersions whose images cover `S`. An fppf sheaf `F` on the big fppf site of `S` is an
algebraic space over `S` exactly when each restriction of `F` to the big fppf site of `Tᵢ` is an
algebraic space over `Tᵢ`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_forall_isAlgebraicSpace_relocalizeRestrict`: an fppf
  sheaf whose restrictions to the members of a finite open covering of the base are algebraic
  spaces is an algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_iff_forall_isAlgebraicSpace_relocalizeRestrict`: the
  resulting criterion, in both directions.
* `AlgebraicGeometry.isAlgebraicSpace_iff_isAlgebraicSpace_relocalizeRestrict_pair`: the
  criterion for a covering of the base by two opens, which is the hypothesis `S = U ∪ W` of
  Stacks 0E8Z.

## Implementation notes

The base scheme is the terminal object `Over.mk (𝟙 (B.obj hS))` of the big fppf site of `S`, so
the restriction of `F` along `jᵢ`, viewed again over `S`, is the binary product
`yoneda.obj (Over.mk jᵢ) ⨯ F`; that this product is an algebraic space over `S` exactly when the
restriction is one over `Tᵢ` is Stacks 04SH. The projections
`yoneda.obj (Over.mk jᵢ) ⨯ F ⟶ F` are base changes of the `jᵢ`, hence representable by open
immersions, and the morphism they induce from their coproduct is locally surjective; so Stacks
02WR applies, the coproduct being an algebraic space by Stacks 040T because the family is
finite. The converse direction is Stacks 03I5 part (1) and needs neither finiteness nor the
covering hypothesis.

This is the step of Stacks 0E8Z which identifies the algebraic spaces among the sheaves glued
from an open covering of the base. The source states it for a covering by two opens, which is
the case of a two-element index type.

## What is not proved

Stacks 0E8Z itself is not proved here. Its statement is that base change is an equivalence
between finitely presented algebraic spaces over `S = U ∪ W` and triples consisting of finitely
presented algebraic spaces over `U` and over `W` together with an isomorphism of their
restrictions to `U ∩ W`. Two further ingredients are needed for that and are absent:

* the equivalence between fppf sheaves on the big site of `S` and such triples, which is the
  two-member case of the descent equivalence
  `CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`
  (Stacks 04TS) and requires collapsing its cocycle datum, and
* the corresponding criterion for finite presentation in place of algebraicity, which is the
  Zariski-local-on-the-target content of Stacks 03KG, Stacks 03KM and Stacks 0410.

Only the algebraicity criterion above is established.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 040T](https://stacks.math.columbia.edu/tag/040T)
* [Stacks Project, Tag 04SH](https://stacks.math.columbia.edu/tag/04SH)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of schemes underlying the structure morphism of an object of the big fppf site
of `S` to the terminal object. -/
theorem toScheme_map_mkIdTerminal_from (a : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a) = B.inclusion.map a.hom :=
  congrArg B.inclusion.map (Over.mkIdTerminal_from_left a)

variable {I : Type (u + 1)} (T : I → Scheme.{u}) (hT : ∀ i, B.Contains (T i))
  (j : ∀ i, B.obj (hT i) ⟶ B.obj hS)

/-- **Algebraicity is detected on an open covering of the base.** Let `{jᵢ : Tᵢ ⟶ S}` be a
finite family of open immersions of a big fppf site whose images cover `S`. An fppf sheaf on
the big fppf site of `S` whose restriction along each `jᵢ` is an algebraic space over `Tᵢ` is
an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_forall_isAlgebraicSpace_relocalizeRestrict [Finite I]
    (hj : ∀ i, IsOpenImmersion (B.inclusion.map (j i)))
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (B.inclusion.map (j i)))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (h : ∀ i, IsAlgebraicSpace B (T i) (hT i) ((OverShriek.relocalizeRestrict (j i)).obj F)) :
    IsAlgebraicSpace B S hS F := by
  classical
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    essentiallySmall_bigFppfOver B S hS
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B S hS) (Type u)
  have _ : HasFiniteCoproducts (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance
  have _ : HasColimitsOfShape (Discrete I) (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ I
  -- The covering family of the base, as a family of objects of the big fppf site of `S`.
  let E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) :=
    ⟨I, fun i => Over.mk (j i), fun i => Over.mkIdTerminal.from (Over.mk (j i))⟩
  have hEf : ∀ i, (BigFppfOver.toScheme B S hS).map (E.f i) = B.inclusion.map (j i) :=
    fun i => toScheme_map_mkIdTerminal_from B S hS (Over.mk (j i))
  have hFi : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F) := fun i =>
    (isAlgebraicSpace_restrict_iff_product B (T i) S (hT i) hS (j i) F).1 (h i)
  let Fs : I → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun i =>
    ⟨yoneda.obj (E.X i) ⨯ F, (hFi i).isSheaf⟩
  have hsieve : E.sieve₀ ∈ BigFppfOver.topology B S hS (Over.mk (𝟙 (B.obj hS))) :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS E.f
      (fun i => (hEf i) ▸ hj i) (fun x => by
        obtain ⟨i, hi⟩ := hcov x
        exact ⟨i, (hEf i) ▸ hi⟩)
  refine isAlgebraicSpace_of_open_cover B S hS F hF I Fs hFi (∐ Fs) (Sigma.ι Fs)
    (coproductIsCoproduct Fs)
    (Space.coverCoproductProj hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs)).hom (fun i => ?_)
    (Space.isLocallySurjective_coverCoproductProj hF E hFi (Sigma.ι Fs)
      (coproductIsCoproduct Fs) hsieve)
    (Space.isAlgebraicSpace_finiteCoproduct B S hS _ hFi (∐ Fs) (Sigma.ι Fs)
      (coproductIsCoproduct Fs))
  rw [Space.coverCoproductProj_ι hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs) i]
  exact Space.presheaf_prod_snd (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
    (E.X i) F ((hEf i) ▸ hj i)

/-- **Stacks 0E8Z, the algebraicity criterion.** Let `{jᵢ : Tᵢ ⟶ S}` be a finite family of open
immersions of a big fppf site whose images cover `S`. An fppf sheaf on the big fppf site of `S`
is an algebraic space over `S` exactly when its restriction along each `jᵢ` is an algebraic
space over `Tᵢ`. -/
@[stacks 0E8Z "algebraicity is detected on an open covering of the base"]
theorem isAlgebraicSpace_iff_forall_isAlgebraicSpace_relocalizeRestrict [Finite I]
    (hj : ∀ i, IsOpenImmersion (B.inclusion.map (j i)))
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (B.inclusion.map (j i)))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    IsAlgebraicSpace B S hS F ↔
      ∀ i, IsAlgebraicSpace B (T i) (hT i) ((OverShriek.relocalizeRestrict (j i)).obj F) :=
  ⟨fun hFalg i => isAlgebraicSpace_relocalizeRestrict B (T i) S (hT i) hS (j i) F hFalg,
    isAlgebraicSpace_of_forall_isAlgebraicSpace_relocalizeRestrict B S hS T hT j hj hcov F hF⟩

/-- **The algebraicity criterion of Stacks 0E8Z for a covering by two opens.** Let
`jU : U ⟶ S` and `jW : W ⟶ S` be open immersions of a big fppf site whose images cover `S`, so
that `S = U ∪ W`. An fppf sheaf on the big fppf site of `S` is an algebraic space over `S`
exactly when its restrictions along `jU` and `jW` are algebraic spaces over `U` and over `W`. -/
theorem isAlgebraicSpace_iff_isAlgebraicSpace_relocalizeRestrict_pair
    (U W : Scheme.{u}) (hU : B.Contains U) (hW : B.Contains W)
    (jU : B.obj hU ⟶ B.obj hS) (jW : B.obj hW ⟶ B.obj hS)
    (hjU : IsOpenImmersion (B.inclusion.map jU))
    (hjW : IsOpenImmersion (B.inclusion.map jW))
    (hcov : ∀ x : S, x ∈ Set.range (B.inclusion.map jU) ∨
      x ∈ Set.range (B.inclusion.map jW))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    IsAlgebraicSpace B S hS F ↔
      IsAlgebraicSpace B U hU ((OverShriek.relocalizeRestrict jU).obj F) ∧
        IsAlgebraicSpace B W hW ((OverShriek.relocalizeRestrict jW).obj F) := by
  let Tp : ULift.{u + 1} Bool → Scheme.{u} := fun b => bif b.down then U else W
  have hTp : ∀ b, B.Contains (Tp b) := by rintro ⟨_ | _⟩ <;> assumption
  let jp : ∀ b : ULift.{u + 1} Bool, B.obj (hTp b) ⟶ B.obj hS := fun b =>
    Bool.rec (motive := fun c => B.obj (hTp ⟨c⟩) ⟶ B.obj hS) jW jU b.down
  exact (isAlgebraicSpace_iff_forall_isAlgebraicSpace_relocalizeRestrict B S hS Tp hTp jp
    (by rintro ⟨_ | _⟩ <;> assumption)
    (fun x => (hcov x).elim (fun hx => ⟨⟨true⟩, hx⟩) fun hx => ⟨⟨false⟩, hx⟩) F hF).trans
    ⟨fun h => ⟨h ⟨true⟩, h ⟨false⟩⟩, fun h => by rintro ⟨_ | _⟩; exacts [h.2, h.1]⟩

end AlgebraicGeometry

end
