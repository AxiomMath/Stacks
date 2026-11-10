module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelationSystemLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded

/-!
# Algebraic spaces presented as limits of systems of étale quotients

The proof of Stacks 07SU proceeds by descending induction along the stratification of Stacks
07ST, and at every step it presents the open subspace reached so far as the limit of a directed
system of quotients `V_i / R_i` of étale equivalence relations of finite type over `Spec ℤ`, the
limit `V = lim V_i` being an étale atlas whose kernel pair is `R = lim R_i`. This file records
that presentation as a structure, `AlgebraicGeometry.Space.QuotientApproximation`, whose fields
are exactly the hypotheses of
`AlgebraicGeometry.Space.EtaleRelationSystem.hasNoetherianApproximation`, and proves that it is
transported along isomorphisms and produced by the glueing data of the problem step
(`AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData`).

## Main definitions

* `AlgebraicGeometry.Space.QuotientApproximation`: the presentation.

## Main results

* `AlgebraicGeometry.Space.QuotientApproximation.hasNoetherianApproximation`: a presheaf with
  such a presentation has a Noetherian approximation.
* `AlgebraicGeometry.Space.QuotientApproximation.ofIso`: transport along an isomorphism.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.quotientApproximation`: the
  presentation produced by the glueing data of the problem step.
* `AlgebraicGeometry.Space.QuotientApproximation.isQuasiCompactSpace_quotient`,
  `AlgebraicGeometry.Space.QuotientApproximation.isAbsolutelyQuasiSeparated_quotient`: the stages
  `V_i / R_i` are quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

/-- **A presentation of a presheaf as the limit of a system of étale quotients of finite type.**
A directed set `I`, an inverse system over it of étale equivalence relations `(V_i, R_i)` on
objects of the big fppf site of `Spec ℤ` with cartesian source squares, affine transition
morphisms `V_i ⟶ V_{i'}`, every `V_i` quasi-compact and locally of finite type over `Spec ℤ` and
every `R_i` quasi-compact; limits `V = lim V_i` and `R = lim R_i` in schemes; and a surjective
étale morphism `V ⟶ X` whose kernel pair is `R`. These are the hypotheses of
`AlgebraicGeometry.Space.EtaleRelationSystem.hasNoetherianApproximation`, the form in which the
proof of Stacks 07SU carries the open subspace reached at each step of its induction. -/
structure QuotientApproximation (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) where
  /-- The directed set indexing the system. -/
  I : Type u
  [preorder : Preorder I]
  [nonempty : Nonempty I]
  [isDirected : IsDirected I (· ≤ ·)]
  /-- The system of étale equivalence relations. -/
  E : EtaleRelationSystem B (⊤_ Scheme.{u}) hZ Iᵒᵖ
  /-- The transition morphisms `V_i ⟶ V_{i'}` are affine. -/
  hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E.obj.map g))
  /-- Every `V_i` is quasi-compact. -/
  hcpt : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))
  /-- Every `V_i` is locally of finite type over `Spec ℤ`. -/
  hlft : ∀ j, LocallyOfFiniteType
    (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j)))
  /-- Every `R_i` is quasi-compact. -/
  hrel : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.rel.obj j))
  /-- The limit `V = lim V_i`. -/
  cV : Cone E.obj
  hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV)
  /-- The limit `R = lim R_i`. -/
  cR : Cone E.rel
  hR : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cR)
  /-- The limit of the source maps. -/
  sL : cR.pt ⟶ cV.pt
  /-- The limit of the target maps. -/
  tL : cR.pt ⟶ cV.pt
  hs : ∀ j, sL ≫ cV.π.app j = cR.π.app j ≫ E.s.app j
  ht : ∀ j, tL ≫ cV.π.app j = cR.π.app j ≫ E.t.app j
  /-- The atlas `V ⟶ X`. -/
  f : yoneda.obj cV.pt ⟶ X
  /-- Its kernel pair is `R`. -/
  hf : IsPullback (yoneda.map tL) (yoneda.map sL) f f
  /-- The atlas `V ⟶ X` is surjective. -/
  hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f
  /-- The atlas `V ⟶ X` is étale. -/
  hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f

namespace QuotientApproximation

variable {hZ} {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (A : QuotientApproximation hZ X)

attribute [instance] preorder nonempty isDirected

include A in
/-- **A presheaf presented by a system of étale quotients has a Noetherian approximation.** -/
theorem hasNoetherianApproximation
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  EtaleRelationSystem.hasNoetherianApproximation B hZ A.E A.hobj A.hcpt A.hlft A.hrel A.cV A.hV A.cR
    A.hR A.sL A.tL A.hs A.ht hX A.f A.hf A.hsurj A.hetale

/-- Transport of a presentation along an isomorphism. -/
noncomputable def ofIso (e : X ≅ Y) : QuotientApproximation hZ Y where
  I := A.I
  E := A.E
  hobj := A.hobj
  hcpt := A.hcpt
  hlft := A.hlft
  hrel := A.hrel
  cV := A.cV
  hV := A.hV
  cR := A.cR
  hR := A.hR
  sL := A.sL
  tL := A.tL
  hs := A.hs
  ht := A.ht
  f := A.f ≫ e.hom
  hf := A.hf.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp)
    (by simp)
  hsurj := MorphismProperty.RespectsIso.postcomp _ e.hom A.f A.hsurj
  hetale := MorphismProperty.RespectsIso.postcomp _ e.hom A.f A.hetale

/-- Each quotient `V_i / R_i` is quasi-compact. -/
lemma isQuasiCompactSpace_quotient (j : A.Iᵒᵖ) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.E.quotient.obj j) :=
  ⟨A.E.obj.obj j, A.E.toQuotient.app j, A.hcpt j,
    quotientMap_surjective_unconditional B _ hZ (A.E.s.app j) (A.E.t.app j),
    (isEtale_iff_presheaf_of_yoneda B _ hZ _).2
      (quotientMap_etale_unconditional B _ hZ (A.E.s.app j) (A.E.t.app j))⟩

/-- Each quotient `V_i / R_i` is absolutely quasi-separated. -/
lemma isAbsolutelyQuasiSeparated_quotient (j : A.Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (A.E.quotient.obj j) := by
  have := A.hlft j
  exact AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_quotient B (⊤_ Scheme.{u}) hZ hZ _ _
    (quasiSeparatedSpace_of_locallyOfFiniteType_terminal _) (A.hrel j)

omit [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)] in
include A in
/-- **A presentation can be taken with a small index set**, smaller than the size cutoff of the
site (`AlgebraicGeometry.Space.EtaleRelationSystem.exists_small_reindex`). -/
theorem exists_small : ∃ A' : QuotientApproximation hZ X, #A'.I < B.cutoff := by
  obtain ⟨J, hJ, hne, hd, e, hJκ, ⟨hV'⟩, ⟨hR'⟩⟩ :=
    A.E.exists_small_reindex A.hobj A.hcpt A.hlft A.hrel A.cV A.hV A.cR A.hR
  let F := e.monotone.functor.op
  exact ⟨{
    I := J
    E := A.E.reindex F
    hobj := fun g => A.hobj (F.map g)
    hcpt := fun j => A.hcpt (F.obj j)
    hlft := fun j => A.hlft (F.obj j)
    hrel := fun j => A.hrel (F.obj j)
    cV := A.cV.whisker F
    hV := hV'
    cR := A.cR.whisker F
    hR := hR'
    sL := A.sL
    tL := A.tL
    hs := fun j => A.hs (F.obj j)
    ht := fun j => A.ht (F.obj j)
    f := A.f
    hf := A.hf
    hsurj := A.hsurj
    hetale := A.hetale }, hJκ⟩

/-- The system of quotients of a presentation with a small index set has bounded charts. -/
theorem chartsBounded_of_small (hI : #A.I < B.cutoff) :
    ChartsBounded B (⊤_ Scheme.{u}) hZ A.E.quotient :=
  A.E.chartsBounded hI A.hobj (fun _ => terminal.from _) (fun _ => terminal.comp_from _) A.hlft

/-- The presented presheaf is the limit of the system of quotients. -/
theorem exists_iso_limit (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X) :
    ∃ e : X ≅ limit A.E.quotient, A.f ≫ e.hom = A.E.limitToQuotient A.cV := by
  have : IsConnected A.Iᵒᵖ := IsCofiltered.isConnected _
  exact A.E.exists_iso_limit_quotient A.cV
    (BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ A.hV) A.cR
    (BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ A.hR) A.sL A.tL A.hs A.ht hX
    A.f A.hf A.hsurj A.hetale

omit [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)] in
include A in
/-- The presented presheaf is quasi-compact: it is covered by the quasi-compact limit `V`. -/
theorem isQuasiCompactSpace : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X := by
  have : ∀ {i j : A.Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((A.E.obj ⋙ BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map g) := A.hobj
  have : ∀ j, CompactSpace ((A.E.obj ⋙ BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj j) := A.hcpt
  have : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A.cV.pt) :=
    Scheme.compactSpace_of_isLimit _ _ A.hV
  exact ⟨A.cV.pt, A.f, this, A.hsurj, (isEtale_iff_presheaf_of_yoneda B _ hZ _).2 A.hetale⟩

end QuotientApproximation

namespace GluedNeighbourhoodRelationData.LimitData

variable {hZ}

/-- **The presentation produced by the glueing data of the problem step of Stacks 07SU.** -/
noncomputable def quotientApproximation {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {G : GluedNeighbourhoodRelationData B (⊤_ Scheme.{u}) hZ Iᵒᵖ}
    (L : G.LimitData)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (G.ambient.map g)))
    (hcpt : ∀ j, CompactSpace (G.ambientScheme.obj j))
    (hlft : ∀ j, LocallyOfFiniteType (terminal.from (G.ambientScheme.obj j)))
    (hkp : ∀ j, CompactSpace (G.kernelPairScheme.obj j))
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) L.atlas) :
    QuotientApproximation hZ L.space where
  I := I
  E := G.etaleRelationSystem
  hobj := hobj
  hcpt := hcpt
  hlft := hlft
  hrel j := by have := hcpt j; have := hkp j; exact G.compactSpace_rel j
  cV := L.coneV
  hV := L.isLimitV
  cR := L.relCone
  hR := L.isLimit_relCone
  sL := L.kernelSnd
  tL := L.kernelFst
  hs := L.relCone_π_source
  ht := L.relCone_π_target
  f := L.atlas
  hf := L.isPullback_kernel
  hsurj := hsurj
  hetale := L.etale_atlas

end GluedNeighbourhoodRelationData.LimitData

end AlgebraicGeometry.Space

end
