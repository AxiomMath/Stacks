module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued

/-!
# The set-theoretic condition for a bounded colimit (Stacks 0AIS)

`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit` deduces the
set-theoretic condition of Stacks 0AIS for a directed colimit of affine fppf sheaves along
thickenings *from the hypothesis that the coproduct of the stages is representable in the
site*. This file discharges that hypothesis for an index of **arbitrary** cardinality carrying
a uniform size bound: if one cardinal `μ` below the site's size cutoff dominates both the
index and every stage, the coproduct of the stages lies in the site and the set-theoretic
condition follows.

The index is *not* required to be countable, nor to be smaller than the cofinality of the
cutoff. A uniform bound is what replaces both: a coproduct of at most `μ` schemes each of size
at most `μ` has size at most `μ` (`AlgebraicGeometry.schemeSize_coproduct_le`), with no
supremum to estimate, so nothing of the cofinality of the cutoff is used. This is the same
mechanism as in `AlgebraicGeometry.FormalSpace.hasStageAtlas` and
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`, whose indexing
families — the quasi-coherent ideal sheaves with a given support — are uncountable and of
unbounded cofinality, and it goes through the same
`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_bounded_colimit`:
  **Stacks 0AIS**, for a directed colimit whose index and stages carry one size bound below
  the cutoff.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_admissible_colimit`: the
  same for an index admissible for coproducts in the site
  (`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`), where no bound on the stages is
  needed because the cofinality of the cutoff bounds their supremum. This is the hypothesis
  under which `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit`
  holds, countability being one way of meeting it.

## Why the condition is a hypothesis of the colimit step of Stacks 0GVM

The condition is not an invention of this library: Stacks 0AI7 defines an affine formal
algebraic space as a sheaf isomorphic to a directed colimit of affine schemes along thickenings
"*and `X` satisfies a set theoretic condition (see Remark 0AIS)*", and Stacks 0AIM attaches the
same clause to a formal algebraic space. So it is a clause of the predicate, and what the two
theorems below do is *verify* that clause — which the source leaves unverified except at a
countable index.

Some bound is needed: the condition is a hypothesis of
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit` and not a conclusion,
because the route to it runs through the representability of the *coproduct* of the stages
(`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`), and that
representability is not available from the axioms of a big fppf site at an index merely known
to be below the cutoff. **This much is machine-checked**, in
`StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoffSharp`: closure of a big fppf site under
coproducts indexed below its cutoff is *equivalent* to regularity of the cutoff
(`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`), hence to an inaccessible
cardinal (`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_contains_sigma`), and the
failure is realized rather than merely permitted — there is an actual site and an actual family
below its cutoff whose coproduct is not in it
(`AlgebraicGeometry.exists_bigFppfSite_family_not_contains_sigma`). The two theorems below are
the two ways of getting the coproduct anyway: a uniform bound on the stages, or an index below
the cofinality of the cutoff.

### An unformalized sketch, recorded for orientation only

It is natural to ask whether the condition is not merely unreachable but *false* for an
unbounded system. **The library proves no such thing**, here or anywhere: this module contains
only the two positive sufficient conditions below, and no declaration in it or elsewhere
refutes the set-theoretic condition for any system. What follows is a sketch, not a theorem,
and nothing in the library may cite it as a witness.

Write `κ` for the size cutoff, fix an affine open `Spec R` of `S` and take, for each set `T` of
cardinality below `κ`, the square-zero algebra `A_T = R[x_t : t ∈ T] / (x_s x_t)`. The quotient
maps `A_T ↠ A_{T'}` for `T' ⊆ T` make the spectra into a directed system of affine schemes of
the site whose transition morphisms are thickenings — the kernels are square-zero — all with
the same reduction, and whose stages have sizes cofinal in `κ`.

A surjection onto the colimit from the sheaf of an object `U` of the site ought to confine those
sizes. Such a surjection is a single section of the colimit over `U`; over each member of a
finite affine fppf refinement of an affine open covering of `U` it comes from one stage, as a
family of square-zero elements of the sections there, and for the canonical section of the stage
`A_T` to be locally a pullback of it, each `x_t` should have to be matched, on each piece of an
fppf covering of `Spec A_T`, with one member of that family or with zero. Were the family of
matches injective in `t` — the covering of `Spec A_T` being faithfully flat and the `x_t`
pairwise distinct — that would give `#T ≤ 2 ^ size U`. Since `κ` is a strong prelimit,
`2 ^ size U < κ` for every object `U` of the site, while `κ` is a limit cardinal, so a stage
exceeding that bound exists. None of this is formalized, and the injectivity step in particular
is exactly what a proof would have to supply.

What the formalized part of the story does say is that the condition does not follow from a
cardinality argument *about the colimit*; what the two theorems below use is a bound on the
*stages*.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIS, bounded colimit.** A directed colimit of affine fppf sheaves along
thickenings satisfies the set-theoretic condition as soon as one cardinal `μ` below the size
cutoff of the site bounds both the index and the size of every stage.

The coproduct of the stages is then an object of the site — a coproduct of at most `μ` schemes
of size at most `μ` has size at most `μ`, by `AlgebraicGeometry.schemeSize_coproduct_le` — and
its universe-lifted representable sheaf is the coproduct of those of the stages, which is the
hypothesis of `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`.

Nothing is asked of the cofinality of the cutoff, and the index may be uncountable: the uniform
bound dominates the supremum of the stage sizes outright. -/
@[stacks 0AIS "bounded_colimit"]
theorem satisfiesSetTheoreticCondition_of_bounded_colimit
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hI : #I ≤ Cardinal.lift.{u + 1, u} μ)
    (hstage : ∀ i : I, ((BigAffineFppf.toScheme B S hS).obj (D.obj i)).size ≤ μ)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : Nonempty (X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) :=
    Sheaf.instHasColimitsOfSize
  -- the index is `u`-small, being dominated by a cardinal of the universe of the schemes
  obtain ⟨f⟩ : Nonempty (I ↪ ULift.{u + 1, u} μ.out) :=
    (Cardinal.le_def _ _).mp (by rwa [Cardinal.mk_uLift, Cardinal.mk_out])
  have hdown : Function.Injective fun i : I ↦ (f i).down :=
    fun _ _ h ↦ f.injective (congrArg ULift.up h)
  let _ : Small.{u} I := small_of_injective hdown
  let e : Shrink.{u} I ≃ I := (equivShrink.{u} I).symm
  let Xi : Shrink.{u} I → BigFppfOver B S hS := fun k ↦
    (BigAffineFppf.inclusion B S hS).obj (D.obj (e k))
  have hmk : #(Shrink.{u} I) ≤ μ := by
    rw [← Cardinal.mk_out μ]
    exact Cardinal.mk_le_of_injective (f := fun k ↦ (f (e k)).down)
      fun _ _ h ↦ e.injective (hdown h)
  -- the coproduct of the stages, as an object of the site
  obtain ⟨V, jV, -, -, -, -, ⟨hLift⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS Xi hμ hmk
      fun k ↦ hstage (e k)
  let eH : J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
    Functor.isoWhiskerLeft J.uliftYoneda
        (sheafificationNatIso.{u, u + 1, u + 1, u + 2} J (Type (u + 1))) ≪≫
      Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf (presheafToSheaf J (Type (u + 1)))
  refine satisfiesSetTheoreticCondition_of_colimit B S hS D hD X hX
    ⟨V, J.uliftYoneda.{u + 1}.obj V, ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app V⟩, ?_⟩
  let eSmall : J.uliftYoneda.{u + 1}.obj V ≅
      ∐ fun k : Shrink.{u} I ↦ (Sheaf.sheafifiedYoneda J).obj (Xi k) :=
    IsColimit.coconePointsIsoOfNatIso hLift (coproductIsCoproduct _)
      (Discrete.natIso fun k ↦ eH.app (Xi k.as))
  exact ⟨eSmall ≪≫ Sigma.whiskerEquiv
    (f := fun k : Shrink.{u} I ↦ (Sheaf.sheafifiedYoneda J).obj (Xi k))
    (g := fun i : I ↦ (Sheaf.sheafifiedYoneda J).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) e fun _ ↦ Iso.refl _⟩

/-- **Stacks 0AIS, admissibly indexed colimit.** A directed colimit of affine fppf sheaves
along thickenings whose index is admissible for coproducts in the site — `u`-small and of
cardinality below the cofinality of the size cutoff — satisfies the set-theoretic condition.

Here the stages carry no size bound of their own: being objects of the site their sizes are
below the cutoff, and the cofinality hypothesis puts their supremum below it as well
(`Cardinal.iSup_lt_of_lt_cof_ord`), which produces the uniform bound that
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_bounded_colimit` asks for.
This is the hypothesis behind
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit`: a
countable index is admissible because the cofinality of the cutoff is uncountable. -/
theorem satisfiesSetTheoreticCondition_of_admissible_colimit
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
    [B.AdmitsCoproductIndex I] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : Nonempty (X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let e : Shrink.{u} I ≃ I := (equivShrink.{u} I).symm
  let σ : Shrink.{u} I → Cardinal.{u} := fun k ↦
    ((BigAffineFppf.toScheme B S hS).obj (D.obj (e k))).size
  let μ : Cardinal.{u} := max (max ℵ₀ #(Shrink.{u} I)) (⨆ k, σ k)
  have hcof : #(Shrink.{u} I) < B.cutoff.ord.cof :=
    BigFppfSite.AdmitsCoproductIndex.mk_shrink_lt_cutoff_cof
  have hμ : μ < B.cutoff :=
    max_lt (max_lt B.aleph0_lt_cutoff (hcof.trans_le (Ordinal.cof_ord_le _)))
      (Cardinal.iSup_lt_of_lt_cof_ord hcof fun k ↦
        ((BigAffineFppf.inclusion B S hS).obj (D.obj (e k))).left.property)
  have hmk : #(Shrink.{u} I) ≤ μ := (le_max_right _ _).trans (le_max_left _ _)
  have hI : #I ≤ Cardinal.lift.{u + 1, u} μ := by
    obtain ⟨g⟩ : Nonempty (Shrink.{u} I ↪ μ.out) :=
      (Cardinal.le_def _ _).mp (by rwa [Cardinal.mk_out])
    rw [← Cardinal.mk_out μ, ← Cardinal.mk_uLift]
    exact Cardinal.mk_le_of_injective (f := fun i ↦ ULift.up (g (equivShrink.{u} I i)))
      fun _ _ h ↦ (equivShrink.{u} I).injective (g.injective (congrArg ULift.down h))
  refine satisfiesSetTheoreticCondition_of_bounded_colimit B S hS D hD hμ hI (fun i ↦ ?_) X hX
  obtain ⟨k, rfl⟩ := e.surjective i
  exact (le_ciSup Cardinal.bddAbove_of_small k).trans (le_max_right _ _)

end AlgebraicGeometry.FormalSpace

end
