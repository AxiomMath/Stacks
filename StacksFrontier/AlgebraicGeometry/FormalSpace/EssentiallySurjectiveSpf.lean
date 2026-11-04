module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpfDefs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageCompletionComparison

/-!
# The essential surjectivity clause of Stacks 0AN8

Let `S` be a scheme contained in a big fppf site `𝔅`, let `R` be a weakly admissible
topological ring carrying a quotient system `D` over `S` whose atlas of quotient spectra lies in
the site, and let `v : V ⟶ Spf R` be a morphism from an affine formal algebraic space over `S`
which is
representable by algebraic spaces and étale. Then `V` is the formal spectrum of the completion
`A^∧` of an étale `R`-algebra `A`, compatibly with the morphisms to `Spf R`.

This closes `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`, whose statement is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpfDefs`. The source uses it in
its proof of Stacks 0AQU; this library's Stacks 0AQU,
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_isSurjective_of_isRepresentableEtale`, does not
need it.

## Main results

* `AlgebraicGeometry.FormalSpace.hom_isoFormalSpectrumOfStageNatIsoBelow_comp`: the restricted
  colimit assembly `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIsoBelow` is an
  isomorphism *over* `Spf R` as soon as the stagewise identification it consumes is.
* `AlgebraicGeometry.FormalSpace.exists_etale_completion_iso_of_isRepresentableEtale`: the
  clause at a chosen weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`: **the essential surjectivity
  clause of Stacks 0AN8.**

## Implementation notes

Only the last two steps of the source proof are here; the first four are
`AlgebraicGeometry.FormalSpace.stageBaseChangeModel` (the chosen affine models of the stage base
changes), `AlgebraicGeometry.FormalSpace.stageLiftAlgebra` (the étale lift at the fixed `J₀`,
Stacks 04D1), `AlgebraicGeometry.FormalSpace.stageComparison` (the comparison family `φ_J` and
its compatibility with the stage transitions, Stacks 0ALI) and
`AlgebraicGeometry.FormalSpace.stageCompletionNatIso` (that family read as an isomorphism of
diagrams of sheaves over `Spf R`).

The assembly is a colimit computation over the weak ideals of definition contained in `J₀`,
which is the index the comparison family exists on and which is cofinal
(`AlgebraicGeometry.FormalSpace.final_weakIdealsBelowInclusion`). Since both sides are colimits
over that index, the over-the-base clause is checked stage by stage, where it is
`AlgebraicGeometry.FormalSpace.stageCompletionNatIso_hom_app_comp` on one side and
`CategoryTheory.Limits.pullback.condition` on the other.

The quotient system `E` on the completion and the continuous map `c` into it are Stacks 0ANM,
`AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem`; its finite-type hypothesis
is read off étaleness of the lift, and its `HasLargeSite` hypothesis is the one that
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'` carries. Stacks 0ANM states its
finite-type hypothesis for the algebra structure `RingHom.toAlgebra` builds out of the ring map,
which is not the structure the étale lift carries but has the same `algebraMap`, so
`Algebra.algebra_ext` identifies the two.

That site condition — Stacks 0AIF's `QuotientSystem.HasLargeSite`, which is also what makes
`Spf R` an affine formal algebraic space in the sense of Stacks 0AIS — is the one thing asked
here which Stacks 0AN8 does not ask, and the tag comment discloses it. Nothing is asked of `R`
itself. The condition is strictly weaker than the bound `#R < 𝔅.cutoff` on the ring, which implies
it by
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` and which is a genuine restriction
on a weakly admissible ring; the comparison is given in full on
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public section

open AlgebraicGeometry Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

/-- **The restricted colimit assembly is an isomorphism over the base.** If the stagewise
identification `α` that `AlgebraicGeometry.FormalSpace.isoFormalSpectrumOfStageNatIsoBelow`
consumes is compatible with the morphisms to `Spf B`, then so is the isomorphism
`V ≅ Spf A^∧` it produces. -/
theorem hom_isoFormalSpectrumOfStageNatIsoBelow_comp
    {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] (f : B →+* A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (D : QuotientSystem 𝔅 S hS B)
    {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)
    (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f)) (c : ContinuousHom D E)
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex B)
    (α : weakIdealsBelowInclusion B J₀ ⋙ stageBaseChangeDiagram D v ≅
      weakIdealsBelowInclusion B J₀ ⋙ (kerProjectionDiagram f ⋙ formalSpectrumDiagram E))
    (hα : ∀ J : WeakIdealsBelow B J₀,
      α.hom.app J ≫ formalSpectrumInclusion E ((kerProjectionDiagram f).obj J.1) ≫
          formalSpectrumMap hB c =
        pullback.fst (formalSpectrumInclusion D J.1) v ≫ formalSpectrumInclusion D J.1) :
    (isoFormalSpectrumOfStageNatIsoBelow f hB.1 D v E J₀ α).hom ≫ formalSpectrumMap hB c = v := by
  refine (cancel_epi (isoColimitStageBaseChangeBelow D v hB.1 J₀).inv).mp ?_
  show (isoColimitStageBaseChangeBelow D v hB.1 J₀).inv ≫
      ((isoColimitStageBaseChangeBelow D v hB.1 J₀).hom ≫
        ((HasColimit.isoOfNatIso α).hom ≫
          (colimitIsoFormalSpectrumOfCompletionBelow f hB.1 E J₀).hom)) ≫
      formalSpectrumMap hB c =
    (isoColimitStageBaseChangeBelow D v hB.1 J₀).inv ≫ v
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  refine colimit.hom_ext fun J => ?_
  have hrhs : colimit.ι (weakIdealsBelowInclusion B J₀ ⋙ stageBaseChangeDiagram D v) J ≫
      (isoColimitStageBaseChangeBelow D v hB.1 J₀).inv ≫ v =
      pullback.fst (formalSpectrumInclusion D J.1) v ≫ formalSpectrumInclusion D J.1 := by
    rw [← Category.assoc, ι_isoColimitStageBaseChangeBelow_inv]
    exact pullback.condition.symm
  have hlhs : colimit.ι (weakIdealsBelowInclusion B J₀ ⋙ stageBaseChangeDiagram D v) J ≫
      ((HasColimit.isoOfNatIso α).hom ≫
          (colimitIsoFormalSpectrumOfCompletionBelow f hB.1 E J₀).hom) ≫
        formalSpectrumMap hB c =
      pullback.fst (formalSpectrumInclusion D J.1) v ≫ formalSpectrumInclusion D J.1 := by
    rw [← Category.assoc, ← Category.assoc, HasColimit.isoOfNatIso_ι_hom, Category.assoc,
      Category.assoc, ι_colimitIsoFormalSpectrumOfCompletionBelow_hom_assoc]
    exact hα J
  exact hlhs.trans hrhs.symm

variable (𝔅 S hS)

/-- **The essential surjectivity clause of Stacks 0AN8, at a chosen weak ideal of definition.**
A morphism `v : V ⟶ Spf R` from an affine formal algebraic space over `S` which is
representable by algebraic spaces and étale exhibits `V` as the formal spectrum of the
completion of an étale `R`-algebra, compatibly with the morphisms to `Spf R`.

The only hypothesis beyond those of Stacks 0AN8 is the site condition `hD` of Stacks 0AIF; see
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`. -/
theorem exists_etale_completion_iso_of_isRepresentableEtale
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem 𝔅 S hS R) (hD : D.HasLargeSite)
    (V : FppfSheaf 𝔅 S hS) (v : V ⟶ formalSpectrum D)
    (hV : IsAffineFormalAlgebraicSpace 𝔅 S hS V) (hv : IsRepresentableEtale 𝔅 S hS v)
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
      (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver (algebraMap R A)))
      (c : ContinuousHom D E) (ε : V ≅ formalSpectrum E),
      c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A) ∧
        ε.hom ≫ formalSpectrumMap hR c = v := by
  have hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_formalSpectrum hR D hD
  have hFT : let : Algebra R (stageLiftAlgebra D v hY hV hv J₀) :=
      (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)).toAlgebra
      Algebra.FiniteType R (stageLiftAlgebra D v hY hV hv J₀) := by
    have halg : (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)).toAlgebra =
        algebra_stageLiftAlgebra D v hY hV hv J₀ :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [halg]
    infer_instance
  obtain ⟨E, c, hc⟩ := exists_completionOver_quotientSystem 𝔅 S hS
    (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) hFT hR D hD
  refine ⟨stageLiftAlgebra D v hY hV hv J₀, inferInstance, inferInstance, inferInstance, E, c,
    isoFormalSpectrumOfStageNatIsoBelow (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
      hR.1 D v E J₀ (stageCompletionNatIso D v hY hV hv J₀ E c hc), hc, ?_⟩
  exact hom_isoFormalSpectrumOfStageNatIsoBelow_comp
    (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) hR D v E c J₀ _
    (fun J => stageCompletionNatIso_hom_app_comp D v hY hV hv J₀ E c hc hR J)

/-- **Essential surjectivity of `Spf` on étale algebras.** For a McQuillan affine formal algebraic
space `Spf R` over `S`, every affine formal algebraic space `V` over `S` carrying a morphism
`V ⟶ Spf R` which is representable by algebraic spaces and étale is `Spf` of the completion `A^∧`
of an étale `R`-algebra `A`, compatibly with the morphisms to `Spf R`. -/
@[stacks 0AN8 "essential surjectivity, and only for a quotient system satisfying the site \
condition of Stacks 0AIF, that the site hold the atlas of quotient spectra: the source leaves \
that condition implicit, its sites being indexed by a cutoff it may enlarge, and a quotient \
system by itself places only the individual quotient spectra in the site, not their coproduct. \
Nothing is asked of the coefficient ring beyond the source's own hypotheses"]
theorem isEssentiallySurjectiveSpf : IsEssentiallySurjectiveSpf' 𝔅 S hS :=
  fun R _ _ _ _ hR D hD V v hV hv =>
    exists_etale_completion_iso_of_isRepresentableEtale 𝔅 S hS R hR D hD V v hV hv
      ⟨hR.1.choose, hR.1.choose_spec⟩

end AlgebraicGeometry.FormalSpace

end
