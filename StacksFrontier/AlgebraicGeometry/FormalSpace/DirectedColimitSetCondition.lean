module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpacesCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticConditionCriteria

/-!
# The set-theoretic condition for a directed colimit of affine formal spaces (Stacks 0GVM)

Let `S` be a scheme contained in a big fppf site `B` and let `(X_i)` be a directed system of
affine formal algebraic spaces over `S` whose transition morphisms are representable
thickenings. **Stacks 0GVM** asserts that the colimit `X` of such a system is an affine formal
algebraic space over `S`. Being an affine formal algebraic space (Definition 0AI7) is the
conjunction of a presentation of `X` as a directed colimit of affine schemes along thickenings
and the set-theoretic condition of Remark 0AIS. The presentation is
`AlgebraicGeometry.FormalSpace.exists_affinePresentation_of_colimit`, exactly as in the source's
proof. This file supplies the set-theoretic condition, which the source's proof passes over.

## The set-theoretic condition, and why it needs a size bound

Remark 0AIS derives the condition for a colimit from the coproduct of its stages, and observes
that this works when the index set is "not too large". That proviso cannot be dropped:
`AlgebraicGeometry.FormalSpace.not_forall_isAffineFormalAlgebraicSpace_colimit` shows that over
every nonempty scheme `S` of the site the statement of Stacks 0GVM fails for the system
`μ ↦ Spec (k ⊕ k^μ)` indexed by the finite subsets `μ` of a set as large as the size cutoff of
the site. Its stages are affine schemes, so affine formal algebraic spaces, and its transition
morphisms are thickenings; but its colimit admits no surjection from the sheaf of any object of
the site
(`AlgebraicGeometry.FormalSpace.not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram`).

The counterexample lives at the source's own generality, with no universe inflation: its index
`ULift (Finset σ)` is the lift of a `u`-small set, of cardinality exactly the size cutoff of the
site, and its stages are spectra of finite-dimensional algebras over a residue field of `S`.
The size bound is a correction, not the source's convention made explicit: the size conventions
of Sets, Section 000H bound the schemes of `(Sch/S)_fppf` but not the index sets of colimits of
sheaves, and both Lemma 0GVM and Definition 0AI7 allow an arbitrary directed set `Λ`, while
Remark 0AIS itself imposes "not too large" as an extra proviso.

So Stacks 0GVM is proved here under the size bound of Remark 0AIS, in the generality that the
argument allows. The bound is on the *cofinality* of the index set, and on nothing else: `Λ`
must have a cofinal family indexed by a set which is not too large in the sense of
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, i.e. `u`-small and of cardinality below the
cofinality of the size cutoff of the site, which is what Remark 0AIS needs for the coproduct
of the chosen surjections to be an object of the site. Every countable directed set qualifies,
and so does every directed set with a greatest element, whatever its cardinality.

The argument is that of Remark 0AIS. Each stage `X_{ι k}` of the cofinal family satisfies the
set-theoretic condition, being an affine formal algebraic space, so it receives a surjection
from the sheaf of an object `U_k` of the site. The maps `h_{U_k} ⟶ X_{ι k} ⟶ X` are jointly
surjective, since the colimit injections are jointly surjective and the family is cofinal, so
the coproduct `U = ∐ U_k`, an object of the site because the index is admissible, surjects onto
`X` (`AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_sigmaObj`). The diagonal of `X` is
representable by Stacks 0AI8 applied to the presentation of `X` by affine schemes, so the kernel
pair of `h_U ⟶ X` is itself represented by an object of the site
(`FormalSpace.satisfiesSetTheoreticCondition_of_epi_of_relativelyRepresentable_diag`).

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_of_cofinal`:
  **Stacks 0GVM**, for an index set with a cofinal family indexed by an admissible set.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_of_admissible`: the case
  of an admissible index set.
* `AlgebraicGeometry.FormalSpace.not_forall_isAffineFormalAlgebraicSpace_colimit`: without a
  size bound on the index set, the statement is false.

## References

* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheafHasColimits

/-- **Stacks 0GVM.** The colimit of a directed system of affine formal algebraic spaces over
`S` whose transition morphisms are representable thickenings -- equivalently, closed immersions
inducing isomorphisms on reductions -- is an affine formal algebraic space over `S`, provided
the index set has a cofinal family `ι : K → I` indexed by a set `K` which is not too large
(`u`-small, of cardinality below the cofinality of the size cutoff of the site; every countable
`K` qualifies).

The size bound is the proviso of observation (1) of Remark 0AIS. For a colimit
`X = colim X_λ` of a system as in Definition 0AI7, the source notes that `U = ∐_λ X_λ ⟶ X` is a
surjection of fppf sheaves, and that "if `U` is representable by an object of `(Sch/S)_fppf`"
then the set-theoretic condition is satisfied, which "is always the case if `Λ` is countable"
(Sets, Lemma 000R). Being `u`-small of cardinality below the cofinality of the size cutoff,
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, is what makes a coproduct of objects of
the site indexed by `K` an object of the site; every countable `K` qualifies
(`AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_countable`). It is asked only of a
cofinal family, which has the same colimit. Because the stages here are affine formal algebraic
spaces rather than affine schemes, each stage `X_{ι k}` is replaced by an object `U_k` of the
site surjecting onto it, as in observation (3) of Remark 0AIS, and `∐_k U_k` is the object of
the site that the proviso asks for. The bound cannot be dropped: see
`AlgebraicGeometry.FormalSpace.not_forall_isAffineFormalAlgebraicSpace_colimit`. -/
@[stacks 0GVM "corrected form: the printed statement is false for an index set as large as the \
size cutoff of the site, the colimit then failing the set-theoretic condition of Stacks 0AIS \
(AlgebraicGeometry.FormalSpace.not_forall_isAffineFormalAlgebraicSpace_colimit); stated, under \
the source's hypotheses, for an index with a cofinal family whose index is admissible for \
coproducts in the site, the proviso of Stacks 0AIS observation (1) that the coproduct of the \
stages be representable by an object of the site (always the case for a countable index), and \
with the set-theoretic condition derived, not assumed"]
theorem isAffineFormalAlgebraicSpace_colimit_of_cofinal (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    {K : Type v} [Small.{u} K] [B.AdmitsCoproductIndex K] (ι : K → I)
    (hι : ∀ i, ∃ k, i ≤ ι k) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨K', pre, hne, hdir, F, hF, ⟨eF⟩⟩ :=
    exists_affinePresentation_of_colimit B S hS D hD hthick X e
  let := pre
  have hdiag := (diagonal_isClosedImmersion B S hS F hF X eF.symm).rep
  have hU : ∀ k, ∃ (U : BigFppfOver B S hS)
      (b : J.uliftYoneda.{u + 1}.obj U ⟶ D.obj (ι k)), Epi b :=
    fun k ↦ exists_epi_uliftYoneda_of_satisfiesSetTheoreticCondition (hD (ι k)).1
  choose U b hb using hU
  obtain ⟨t, ht, -⟩ := exists_epi_uliftYoneda_sigmaObj B S hS U
    (fun k ↦ b k ≫ colimit.ι D (ι k) ≫ e.inv) (by
      intro Z g g' hgg'
      have h1 : ∀ k, colimit.ι D (ι k) ≫ e.inv ≫ g = colimit.ι D (ι k) ≫ e.inv ≫ g' :=
        fun k ↦ (cancel_epi (b k)).mp (by simpa only [Category.assoc] using hgg' k)
      have h2 : e.inv ≫ g = e.inv ≫ g' := by
        apply colimit.hom_ext
        intro i
        obtain ⟨k, hk⟩ := hι i
        rw [← colimit.w D (homOfLE hk)]
        simp only [Category.assoc, h1 k]
      exact (cancel_epi e.inv).mp h2)
  exact ⟨satisfiesSetTheoreticCondition_of_epi_of_relativelyRepresentable_diag B S hS t hdiag,
    K', pre, hne, hdir, F, hF, ⟨eF⟩⟩

/-- **Stacks 0GVM, admissible index.** The colimit of a directed system of affine formal
algebraic spaces over `S` along representable thickenings, indexed by a set which is not too
large (for instance a countable one), is an affine formal algebraic space over `S`. -/
theorem isAffineFormalAlgebraicSpace_colimit_of_admissible (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] [Small.{u} I] [B.AdmitsCoproductIndex I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D) :
    IsAffineFormalAlgebraicSpace B S hS X :=
  isAffineFormalAlgebraicSpace_colimit_of_cofinal B S hS D hD hthick X e id
    fun i ↦ ⟨i, le_rfl⟩

/-- **Stacks 0GVM needs a size bound on the index set.** Over a nonempty scheme `S` of the site
it is not the case that the colimit of every directed system of affine formal algebraic spaces
over `S` along representable thickenings is an affine formal algebraic space: the colimit of
`AlgebraicGeometry.FormalSpace.sqZeroSheafDiagram`, for a residue field of `S` and an index set
as large as the size cutoff of the site, does not satisfy the set-theoretic condition of
Remark 0AIS. This is where the proviso of observation (1) of Remark 0AIS fails: each stage has
one point, so the coproduct of the stages has as many points as the index, which is as large as
the size cutoff, while an object of the site has fewer points than the cutoff. -/
@[stacks 0GVM "the statement as printed is false: over any nonempty S, the directed system \
Spec(k + k^μ) of affine schemes along thickenings, indexed by the finite subsets μ of a set as \
large as the size cutoff of the site, has a colimit failing the set-theoretic condition of \
Stacks 0AIS, the coproduct of its stages not being an object of the site as the proviso of \
Stacks 0AIS observation (1) requires; the corrected form is \
AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_of_cofinal"]
theorem not_forall_isAffineFormalAlgebraicSpace_colimit (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) [Nonempty S] :
    ¬ ∀ (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i)) →
      (∀ ⦃i j : I⦄ (f : i ⟶ j),
        MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
          (MorphismProperty.inverseImage
            (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)) (D.map f)) →
      ∀ (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))), (X ≅ colimit D) →
        IsAffineFormalAlgebraicSpace B S hS X := by
  intro h
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let x : S := Classical.arbitrary S
  have hk := B.residueField_spec_contains hS x
  let σ : Type u := B.cutoff.out
  let D := sqZeroSheafDiagram B S hS (S.residueField x) hk (S.fromSpecResidueField x) σ
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let eG : Sheaf.sheafifiedYoneda J ≅ J.uliftYoneda.{u + 1} :=
    Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  let : PreservesLimitsOfShape WalkingCospan
      (J.uliftYoneda.{u + 1} ⋙ sheafToPresheaf J (Type (u + 1))) :=
    preservesLimitsOfShape_of_natIso J.uliftYonedaCompSheafToPresheaf.{u + 1}.symm
  let : PreservesLimitsOfShape WalkingCospan J.uliftYoneda.{u + 1} :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J (Type (u + 1)))
  let : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_of_natIso eG.symm
  have hD : ∀ μ, IsAffineFormalAlgebraicSpace B S hS (D.obj μ) := fun μ ↦
    isAffineFormalAlgebraicSpace_uliftYoneda B S hS _
  have hthick : ∀ ⦃μ ν⦄ (f : μ ⟶ ν), Q.relative (Sheaf.sheafifiedYoneda J) (D.map f) := by
    intro μ ν f
    let m := (BigAffineFppf.inclusion B S hS).map
      ((sqZeroDiagram B S hS (S.residueField x) hk (S.fromSpecResidueField x) σ).map f)
    exact (MorphismProperty.arrow_mk_iso_iff (P := Q.relative (Sheaf.sheafifiedYoneda J))
      (Arrow.isoMk (eG.app _) (eG.app _) (eG.hom.naturality m).symm)).mp
      (MorphismProperty.relative_map (P := Q)
        (isThickening_sqZeroDiagram_map B S hS (S.residueField x) hk
          (S.fromSpecResidueField x) σ f))
  exact not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram B S hS (S.residueField x)
    hk (S.fromSpecResidueField x) σ
    (Cardinal.mk_out B.cutoff).ge (h _ D hD hthick (colimit D) (Iso.refl _)).1

end AlgebraicGeometry.FormalSpace

end
