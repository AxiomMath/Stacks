module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.KernelGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraDictionary
public import StacksFrontier.RingTheory.Flat.CompleteDevissageZero

/-!
# A scheme-theoretic complete dévissage is an algebraic one

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `s : S` correspond to the prime `r` of `Γ(S, ⊤)`. Writing
`R = Γ(S, ⊤)`, `B = Γ(X, ⊤)` and `N = Γ(ℱ, ⊤)`, every chain of stages of a complete dévissage of
`ℱ/X/S` over `s` in the sense of Stacks 05HH translates into a complete dévissage of `N/B/R`
over `r` in the sense of Stacks 05HX. This is item (1) of Stacks 05I0.

Each stage is translated by `AlgebraicGeometry.OneStepDevissage.toDevissageStage`, whose twelve
conditions are supplied by
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionary.lean`, and the
stages are assembled by the introduction rules `Module.CompleteDevissage.ofStage` and
`Module.CompleteDevissage.consStageData`, which match the two constructors of
`AlgebraicGeometry.DevissageChain`.

## Main definitions

* `AlgebraicGeometry.DevissageChain.toCompleteDevissage`: **a chain of stages of a complete
  dévissage of `ℱ/X/S` over `s` is a complete dévissage of `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over the
  prime corresponding to `s`.**

## Main results

* `Module.nonempty_completeDevissage_of_completeDevissage`: **Stacks 05I0 (1).** If a complete
  dévissage of `ℱ/X/S` over `s` exists then a complete dévissage of
  `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over the prime corresponding to `s` exists.

## Implementation notes

The `Γ(S, ⊤)`-algebra structure on `Γ(X, ⊤)` is the one induced by `f` through `RingHom.toAlgebra`,
and the finiteness hypotheses that `Module.CompleteDevissage` carries as instance arguments —
that `Γ(X, ⊤)` is of finite type over `Γ(S, ⊤)` and that `Γ(ℱ, ⊤)` is a finite `Γ(X, ⊤)`-module —
are supplied in the statement itself, from local finiteness of `f` and from Stacks 01PB. They are
`Prop`-valued classes, so the choice of proof does not affect the type.

The recursion is the structural one on `AlgebraicGeometry.DevissageChain`: the final stage gives
`Module.CompleteDevissage.ofStage` and a nonfinal stage prepends itself with
`Module.CompleteDevissage.consStageData` to the translation of the dévissage of its cokernel,
whose base is the stage's smooth scheme. The instance arguments of
`Module.CompleteDevissage.consStageData` that concern the module being dévissed by the tail are
passed positionally: they are stated over the lower
algebra `st.B` of the translated stage, which instance synthesis does not unfold to `Γ(Y, ⊤)`
because `AlgebraicGeometry.OneStepDevissage.toDevissageStage` is not reducible.

Both cases of `AlgebraicGeometry.CompleteDevissage` are translated. A chain of stages becomes a
`Module.CompleteDevissage` stage by stage; the empty dévissage, which exists for the zero sheaf,
becomes `Module.CompleteDevissage.ofSubsingleton`, the one-stage dévissage of the zero module
that Stacks 05HX allows because it imposes no condition on the dimensions of the fibres of
`Spec Bᵢ → Spec R`. That omission is the same one that makes this item one-directional, and it
is the one Stacks 05I0 points out.

## Stacks 05I0 (2)

Item (2) of Stacks 05I0, the dictionary for a dévissage *at a point*, is an equivalence, and it
is proved not here but in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecCompleteDevissageAt.lean`, as
`Module.nonempty_completeDevissageAt_iff`. Both notions carry the condition on the relative
dimension — on the scheme side `AlgebraicGeometry.OneStepDevissage.fiber_dimension`, which
constrains the dimension of **every** fibre of the smooth morphism as Stacks 05H4 (5) does, and
on the ring side `Module.CompleteDevissageAt.FibresHaveRelativeDimension`, which together with
`Module.NonemptyCompleteDevissageAt.relativeDimension_eq_support` is the condition Stacks 05I0
describes as "built in" to the notion of a complete dévissage at `q`, read fibre by fibre. The
direction the source uses is `Module.nonempty_completeDevissageAt_of_completeDevissageAt`, in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraTranslationAt.lean`.

## References

* [Stacks Project, Tag 05HH](https://stacks.math.columbia.edu/tag/05HH)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A chain of stages of a scheme-theoretic complete dévissage is an algebraic complete
dévissage.**

For `f : X ⟶ S` locally of finite type between affine schemes and `ℱ` quasi-coherent of finite
type, a chain of stages of a complete dévissage of `ℱ/X/S` over `s` gives a complete dévissage of
`Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over the prime `r` of `Γ(S, ⊤)` corresponding to `s`, in the sense of
Stacks 05HX. The final stage becomes a one-stage dévissage and a nonfinal stage is prepended to
the translation of the dévissage of its cokernel. -/
public def DevissageChain.toCompleteDevissage {S : Scheme.{u}} [IsAffine S] {s : S}
    (r : Ideal Γ(S, ⊤)) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    {X : Scheme.{u}} → [IsAffine X] → {f : X ⟶ S} → {F : X.Modules} →
      {hl : LocallyOfFiniteType f} → {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      DevissageChain s X f F hl hq ht →
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      Module.CompleteDevissage Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) r
  | X, _, f, F, hl, hq, ht, .last stage hzero =>
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      Module.CompleteDevissage.ofStage
        (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
          (stage.fiber_bijective_sectionsAlpha r hr))
        stage.oneStep.closedAlgHom stage.oneStep.surjective_i_appTop
        stage.oneStep.finitePresentation_i_appTop stage.oneStep.closedSectionsLinearEquiv
        (stage.surjective_sectionsAlpha_of_isZero hzero)
  | X, _, f, F, hl, hq, ht, .more stage hqc hft _hlft tail =>
      letI := f.appTop.hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
        HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
      letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
        letI := hq
        letI := ht
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
      letI := stage.oneStep.affine_Y
      letI : Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) :=
        letI := hqc
        letI := hft
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections stage.coker
          (isAffineOpen_top stage.oneStep.Y)
      @Module.CompleteDevissage.consStageData _ _ _ _ _ _ _ _ _ _ _ _
        (stage.oneStep.toDevissageStage r stage.rank stage.sectionsAlpha
          (stage.fiber_bijective_sectionsAlpha r hr))
        stage.oneStep.closedAlgHom stage.oneStep.surjective_i_appTop
        stage.oneStep.finitePresentation_i_appTop stage.oneStep.closedSectionsLinearEquiv
        Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) inferInstance
        (inferInstanceAs
          (Module Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        (inferInstanceAs
          (Module.Finite Γ(stage.oneStep.Y, ⊤) Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens))))
        stage.cokerSectionsEquiv (tail.toCompleteDevissage r hr)

end AlgebraicGeometry

namespace Module

/-- **Stacks Project, Tag 05I0, item (1).**

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `s : S` correspond to the prime `r` of `Γ(S, ⊤)`. If there
exists a complete dévissage of `ℱ/X/S` over `s`, then there exists a complete dévissage of
`Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over `r`.

Taking `X = Spec B`, `S = Spec A` and `ℱ = Ñ` recovers the statement of the source, whose `N` is
`Γ(ℱ, ⊤)`. Remark 05I0 states this item as an implication and nothing more, and says why: the
definition of a complete dévissage of `N/B/A` over `r`, Stacks 05HX, omits the condition on the
relative dimension that Stacks 05H4 (5) puts on the smooth scheme of a one-step dévissage, so
the algebraic notion over `r` is the weaker of the two. The zero module separates them. It has
the one-stage dévissage `Module.CompleteDevissage.ofSubsingleton`, while the zero sheaf has only
the empty dévissage of Stacks 05HH: a smooth morphism with geometrically irreducible fibres has
fibres of dimension at least `0`, and `dim (Supp(ℱ_s)) = -∞`. Item (2) of the source, for the
notions *at a point*, is an equivalence, because Stacks 05HZ (4) restores that condition.

Both cases of `AlgebraicGeometry.CompleteDevissage` are covered. A chain of stages is translated
stage by stage by `AlgebraicGeometry.DevissageChain.toCompleteDevissage`. The empty dévissage,
which `AlgebraicGeometry.CompleteDevissage.empty` allows for the zero sheaf, is sent to
`Module.CompleteDevissage.ofSubsingleton`: the sections of a zero sheaf vanish, and the zero
module has a one-stage algebraic dévissage — with the zero ring upstairs and `Γ(S, ⊤)` itself as
the smooth algebra — because Stacks 05HX imposes no condition on the dimensions of the fibres,
which is the same omission that makes this item one-directional. -/
@[stacks 05I0 "(1): a geometric complete dévissage over a point gives an algebraic one"]
public theorem nonempty_completeDevissage_of_completeDevissage {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] {f : X ⟶ S} {F : X.Modules} {s : S} [hl : LocallyOfFiniteType f]
    [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : (S.isoSpec.hom s).asIdeal = r)
    (D : AlgebraicGeometry.CompleteDevissage f F s) :
    letI := f.appTop.hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
    letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
    Nonempty (Module.CompleteDevissage Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) r) := by
  let _ := f.appTop.hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
  let _ : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  cases D with
  | empty hF =>
      have :=
        Stacks.AlgebraicGeometry.FiniteTypeSubmodule.subsingleton_sections_of_isZero hF
          (⊤ : X.Opens)
      exact Module.nonempty_completeDevissage_of_subsingleton r
  | nonempty data => exact ⟨data.chain.toCompleteDevissage r hr⟩

/-- **Stacks Project, Tag 05I0, item (1).**

Let `f : X ⟶ S` be locally of finite type between affine schemes, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite type and let `s : S` correspond to the prime `r` of `Γ(S, ⊤)`. If there
exists a nonempty complete dévissage of `ℱ/X/S` over `s`, then there exists a complete dévissage
of `Γ(ℱ, ⊤)/Γ(X, ⊤)/Γ(S, ⊤)` over `r`.

Taking `X = Spec B`, `S = Spec A` and `ℱ = Ñ` recovers the statement of the source, whose `N` is
`Γ(ℱ, ⊤)`. The implication goes only in this direction: the source omits the condition on the
relative dimension from the definition of a complete dévissage of `N/B/A` over `r`, so an
algebraic dévissage carries strictly less information than a geometric one. The hypothesis is the
*nonempty* notion because `Module.CompleteDevissage`, like the zigzag of Stacks 05HX, always has
at least one stage, while `AlgebraicGeometry.CompleteDevissage` also allows the empty
dévissage of the zero sheaf. -/
@[stacks 05I0 "(1): a geometric complete dévissage over a point gives an algebraic one"]
public theorem nonempty_completeDevissage_of_nonemptyCompleteDevissage {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] {f : X ⟶ S} {F : X.Modules} {s : S} [hl : LocallyOfFiniteType f]
    [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] (r : Ideal Γ(S, ⊤)) [r.IsPrime]
    (hr : (S.isoSpec.hom s).asIdeal = r)
    (D : AlgebraicGeometry.NonemptyCompleteDevissage f F s) :
    letI := f.appTop.hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f hl
    letI : Module.Finite Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
    Nonempty (Module.CompleteDevissage Γ(S, ⊤) Γ(X, ⊤) Γ(F, (⊤ : X.Opens)) r) :=
  ⟨D.chain.toCompleteDevissage r hr⟩

end Module

end
