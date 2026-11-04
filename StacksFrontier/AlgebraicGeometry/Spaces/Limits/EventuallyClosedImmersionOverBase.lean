module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.CategoryTheory.Representable.RepresentedDiagram

/-!
# Closed immersions over a base algebraic space descend to a late stage

Let `Y` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, and let
`X = lim X_i` be a directed limit of algebraic spaces over `Y` with affine transition
morphisms. Assume the `X_i` are quasi-compact and quasi-separated, the transition morphisms
`X_{i'} ⟶ X_i` are closed immersions, each `X_i ⟶ Y` is locally of finite type, and
`X ⟶ Y` is a closed immersion. Then `X_i ⟶ Y` is a closed immersion for `i` large enough.
This is [Stacks, Tag 0A0T].

Closed-immersion transition morphisms are affine, so the source's separate assumption that the
transitions are affine is not stated here; omitting an implied hypothesis strengthens the
statement.

## Main results

* `AlgebraicGeometry.Space.eventually_isClosedImmersion_app_of_isRepresentable_stage`: the whole
  argument of Tag 0A0T apart from its appeal to Stacks 07SR, in the form "if *some* stage of the
  system base changed along a given affine surjective étale chart of `Y` is a scheme, then
  `X_i ⟶ Y` is a closed immersion for `i` large enough". The chart is a parameter, so this is
  not Tag 0A0T restricted to a chart; it is the reduction of Tag 0A0T to Stacks 07SR, and it
  assumes nothing that the library does not prove. It does not even ask the limit to be an
  algebraic space: that is used only to build the `AlgebraicGeometry.Space.DescentSituation`
  which Stacks 07SR is stated about, which happens one level up.
* `AlgebraicGeometry.Space.eventually_isClosedImmersion_app`: **Tag 0A0T**, under the source's
  own hypotheses and with no hypothesis of its own, which is where the tag is registered. The
  appeal to Stacks 07SR is made to
  `AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`.
* `AlgebraicGeometry.Space.eventually_isClosedImmersion_app_of_h07SR`: the same statement with
  the appeal to Stacks 07SR factored out as a parameter `h07SR`, in the form Stacks 07SR states
  it for `AlgebraicGeometry.Space.DescentSituation`. It is the step of the proof which builds
  that descent situation, and it is where
  `AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall` is
  substituted for `h07SR`, by
  ```
  fun _ _ _ E hJ _ hrep =>
    E.exists_isRepresentable_system_obj_of_isSiteSmall (.of_lt_cof_op hJ) hrep
  ```

## Implementation notes

The proof is the source's. Choose an affine scheme `W` with a surjective étale morphism
`h_W ⟶ Y`; such a chart exists because `Y` is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`,
Stacks 03H6). Base changing the whole limit situation along it is
`AlgebraicGeometry.Space.DescentSituation.baseChangeOver`, which already knows that the base
changed system is again a system of quasi-compact quasi-separated algebraic spaces with affine
transitions and that the base changed cone is again limiting. Its limit `X ×_Y W` is a scheme,
being a closed subspace of the scheme `W`. Stacks 07SR then makes some stage `X_{i₁} ×_Y W` a
scheme, and every later stage is one too, being a closed subspace of it.

Over the tail `{i | i₁ ≤ i}` the base changed system is therefore a system of *representable*
presheaves, and `CategoryTheory.representedDiagram` reads a diagram of objects of the
site off it. Yoneda reflects limits, so that diagram's cone is limiting in the site; the index
category being cofiltered, `CategoryTheory.Over.forget` preserves the limit, and
`AlgebraicGeometry.Space.isLimit_inclusion_mapCone_of_closed` transports it into `Scheme`. That
last step is the only one which is not formal: a limit computed in the cutoff category
`B.Schemes` is a limit in `Scheme` only because the vertex is small, and the vertex is small
because it is the closed subscheme cut out by `⨆ j, (p j).ker`, where `p j` runs over the closed
immersions into the terminal stage of the tail, so
`AlgebraicGeometry.Scheme.size_lt_of_isClosedImmersion` bounds it by the size of that stage.

Tag 0A0N (`AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit`) applies to the
resulting limit of schemes, and `AlgebraicGeometry.Space.isClosedImmersion_tfae` (Stacks 03M4)
carries the conclusion back from the chart to `X_i ⟶ Y`.

Quasi-compactness and quasi-separatedness of the stages are needed on the *scheme* side for
Tag 0A0N. Quasi-compactness crosses over by
`AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj`. Quasi-separatedness
crosses over not as a property of the stage but as a property of its structure morphism to the
affine chart: a quasi-separated algebraic space has quasi-separated morphisms out of it
(Stacks 073B, part (2)), a represented morphism is quasi-separated exactly when the underlying
morphism of schemes is (Stacks 03KY,
`AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff`), and a scheme quasi-separated over
an affine scheme is a quasi-separated space.

The index set is `I : Type u`, as in Situation 084R
(`AlgebraicGeometry.Space.LimitSituation`), where the source's directed set is also small
relative to the schemes. That makes the index category of the tail small, which is what lets
Tag 0A0N be used in its `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit` form,
with no smallness side condition.

## References

* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
* [Stacks Project, Tag 0A0T](https://stacks.math.columbia.edu/tag/0A0T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Filter Opposite Stacks.SeparationLocal

universe w v u

namespace AlgebraicGeometry

/-! ### The limit of a diagram of schemes with closed immersions to a terminal stage -/

/-- **The limit of a diagram of schemes whose structure morphisms to a terminal stage are closed
immersions**, together with the bound on its size which keeps it inside a size cutoff containing
the terminal stage.

The vertex is the closed subscheme of the terminal stage cut out by the supremum of the kernels
of those closed immersions. -/
noncomputable def closedDiagramLimit
    {J : Type v} [Category.{w} J] (D : J ⥤ Scheme.{u})
    (j₀ : J) (hj₀ : IsTerminal j₀)
    (hclosed : ∀ j, IsClosedImmersion (D.map (hj₀.from j)))
    (κ : Cardinal.{u}) (hsize : (D.obj j₀).size < κ) :
    {c : Cone D // Nonempty (IsLimit c) ∧ c.pt.size < κ} := by
  let p (j : J) := D.map (hj₀.from j)
  let K := ⨆ j, (p j).ker
  have hp (j : J) : IsClosedImmersion (p j) := hclosed j
  let leg (j : J) : K.subscheme ⟶ D.obj j :=
    IsClosedImmersion.lift (p j) K.subschemeι (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_iSup (fun j => (p j).ker) j)
  have hleg (j : J) : leg j ≫ p j = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hpcomp {i j : J} (g : i ⟶ j) : D.map g ≫ p j = p i := by
    rw [← D.map_comp]
    exact congrArg D.map (hj₀.hom_ext _ _)
  have hpzero : p j₀ = 𝟙 _ := by
    change D.map (hj₀.from j₀) = _
    rw [show hj₀.from j₀ = 𝟙 j₀ from hj₀.hom_ext _ _, D.map_id]
  let c : Cone D :=
    { pt := K.subscheme
      π :=
        { app := leg
          naturality := by
            intro i j g
            apply (Category.id_comp (leg j)).trans
            apply (cancel_mono (p j)).1
            calc
              leg j ≫ p j = K.subschemeι := hleg j
              _ = leg i ≫ p i := (hleg i).symm
              _ = (leg i ≫ D.map g) ≫ p j :=
                ((Category.assoc (leg i) (D.map g) (p j)).trans
                  (congrArg (fun q => leg i ≫ q) (hpcomp g))).symm } }
  refine ⟨c, ⟨{
    lift := fun s => IsClosedImmersion.lift K.subschemeι (s.π.app j₀) ?_
    fac := ?_
    uniq := ?_ }⟩, ?_⟩
  · rw [Scheme.IdealSheafData.ker_subschemeι]
    apply iSup_le
    intro j
    rw [← s.w (hj₀.from j)]
    exact Scheme.Hom.le_ker_comp _ _
  · intro s j
    apply (cancel_mono (p j)).1
    change (IsClosedImmersion.lift _ _ _ ≫ leg j) ≫ p j = _
    rw [Category.assoc, hleg, IsClosedImmersion.lift_fac]
    exact (s.w (hj₀.from j)).symm
  · intro s m hm
    apply (cancel_mono K.subschemeι).1
    rw [IsClosedImmersion.lift_fac]
    have h := hm j₀
    change m ≫ leg j₀ = s.π.app j₀ at h
    rwa [show leg j₀ = K.subschemeι by simpa [hpzero] using hleg j₀] at h
  · exact Scheme.size_lt_of_isClosedImmersion K.subschemeι hsize

/-- **A limiting cone in the size cutoff of a big fppf site whose diagram has closed immersions
to a terminal stage stays limiting in `Scheme`.**

The limit computed in `Scheme` is small by `AlgebraicGeometry.Space.closedDiagramLimit`, hence
is already an object of the cutoff; the inclusion therefore preserves this one limit, and so
carries the given limiting cone to a limiting cone. -/
noncomputable def isLimit_inclusion_mapCone_of_closed (B : BigFppfSite.{u})
    {J : Type v} [Category.{w} J] (D : J ⥤ B.Schemes)
    (j₀ : J) (hj₀ : IsTerminal j₀)
    (hclosed : ∀ j, IsClosedImmersion (B.inclusion.map (D.map (hj₀.from j))))
    (c : Cone D) (hc : IsLimit c) : IsLimit (B.inclusion.mapCone c) := by
  let L := closedDiagramLimit (D ⋙ B.inclusion) j₀ hj₀ hclosed B.cutoff (D.obj j₀).property
  have hsize : L.val.pt.size < B.cutoff := L.property.2
  let cSmall : Cone D :=
    { pt := ⟨L.val.pt, hsize⟩
      π :=
        { app j := ⟨L.val.π.app j⟩
          naturality := by
            intro i j g
            apply B.inclusion.map_injective
            exact (Category.id_comp (L.val.π.app j)).trans (L.val.w g).symm } }
  have hcSmall : IsLimit (B.inclusion.mapCone cSmall) := L.property.1.some
  let _ : PreservesLimit D B.inclusion :=
    preservesLimit_of_preserves_limit_cone (isLimitOfReflects B.inclusion hcSmall) hcSmall
  exact isLimitOfPreserves B.inclusion hc

namespace Space

/-! ### Stacks 0A0T -/

section ZeroAZeroT

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The reduction of Stacks 0A0T to Stacks 07SR.**

In the situation of Stacks 0A0T, let `p : h_U ⟶ Y` be a surjective étale chart of `Y` with `U`
affine. If some stage of the system base changed along `p` is a scheme, then `X_i ⟶ Y` is a
closed immersion for `i` large enough.

This is the whole of the source's proof except for its appeal to Stacks 07SR, which is what
produces such a stage. It assumes nothing the library does not prove. -/
theorem eventually_isClosedImmersion_app_of_isRepresentable_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ Y)
    (hcomm : ∀ j, c.π.app j ≫ t.app j = f)
    (hY : IsAlgebraicSpace B S hS Y)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
    (hClosed : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ))
    (hFT : ∀ i, IsLocallyOfFiniteType B S hS (t.app (op i)))
    (hf : IsClosedImmersion B S hS f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (p : yoneda.obj U ⟶ Y)
    (hpSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpEtale : IsEtale B S hS p)
    (hstage : ∃ i : I, (pullback (t.app (op i)) p).IsRepresentable) :
    ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i)) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) T
  let Qc := MorphismProperty.presheaf P
  have _ : HasPullbacks B.Schemes := schemeCutoff_hasPullbacks B
  have _ : PreservesLimitsOfShape WalkingCospan T := by
    dsimp only [T, BigFppfOver.toScheme, BigFppfOver.forget]
    infer_instance
  have _ : P.IsStableUnderBaseChange := ⟨by
    intro A A' A'' Z g g' k k' hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion) (hs.map T) hg⟩
  have _ : Qc.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange P
  -- The chart is étale as a morphism of presheaves.
  have hpEtaleChart : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf p := by
    have hid : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (𝟙 (yoneda.obj U)) := by
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro A A' g fst snd hpb
      have _ : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
      have _ : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
      exact (inferInstance : Etale (T.map snd))
    simpa using hpEtale U (𝟙 _) hid
  -- The affine chart, as an algebraic space.
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hUaff : IsAffine (T.obj U) := hU
  have hUcompact : CompactSpace (T.obj U) := Scheme.compactSpace_of_isAffine _
  have hUqsep : QuasiSeparatedSpace (T.obj U) := quasiSeparatedSpace_of_isAffine _
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U hU (𝟙 (yoneda.obj U))
        (isSeparated_of_isIso B S hS (𝟙 (yoneda.obj U))))
  -- The system base changed along the chart, with its limiting cone.
  let Esys := baseChangeOverSystem B S hS D t p
  let eCone := baseChangeOverCone B S hS D t p c f hcomm
  have heCone : IsLimit eCone := isLimit_baseChangeOverCone B S hS D t p c f hcomm hc
  -- The two projections of each stage, typed through the system rather than through `pullback`.
  let fstE : (j : Iᵒᵖ) → Esys.obj j ⟶ D.obj j := fun j => pullback.fst (t.app j) p
  let sndE : (j : Iᵒᵖ) → Esys.obj j ⟶ yoneda.obj U := fun j => pullback.snd (t.app j) p
  let sndLim : eCone.pt ⟶ yoneda.obj U := pullback.snd f p
  have hcond : ∀ j : Iᵒᵖ, sndE j ≫ p = fstE j ≫ t.app j := fun _ => pullback.condition.symm
  have hEalg : ∀ j : I, IsAlgebraicSpace B S hS (Esys.obj (op j)) := fun j =>
    isAlgebraicSpace_pullback B S hS (t.app (op j)) p (hD j) hUalg hY
  have hEqc : ∀ j : I, IsQuasiCompactSpace B S hS (Esys.obj (op j)) := fun j =>
    isQuasiCompactSpace_pullback B S hS hZ (t.app (op j)) p (hD j) hY (hDqc j)
      (isQuasiCompactSpace_yoneda_obj B S hS hUcompact) hYqs
  have hEqs : ∀ j : I, IsAbsolutelyQuasiSeparated B S hS hZ (Esys.obj (op j)) := fun j =>
    isAbsolutelyQuasiSeparated_pullback B S hS hZ (t.app (op j)) p (hD j) hUalg hY
      (hDqs j) hUqs
  have hEclosed : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (Esys.map φ) := by
    intro a b φ
    exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (isPullback_baseChangeOverMap B S hS (t.app a) (t.app b) (D.map φ) (by simp) p).flip
      (hClosed φ)
  have hEsnd : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b),
      Esys.map φ ≫ sndE b = sndE a := fun {a b} φ =>
    baseChangeOverSystem_map_snd B S hS D t p φ
  have heConeSnd : ∀ a : Iᵒᵖ,
      eCone.π.app a ≫ sndE a = sndLim := fun a =>
    baseChangeOverMap_snd B S hS f (t.app a) (c.π.app a) (hcomm a) p
  have hclosedSnd : IsClosedImmersion B S hS (sndLim) :=
    (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_hasPullback f p) hf
  -- Pass to the tail above the stage which is a scheme.
  obtain ⟨i₁, hi₁rep⟩ := hstage
  let Tail := {i : I // i₁ ≤ i}
  have _ : Nonempty Tail := ⟨⟨i₁, le_rfl⟩⟩
  have _ : IsDirected Tail (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨k, hak, hbk⟩ := IsDirected.directed (r := (· ≤ ·)) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩
  let incl : Tail ⥤ I :=
    { obj i := i.1
      map g := homOfLE (leOfHom g)
      map_id := by intros; exact Subsingleton.elim _ _
      map_comp := by intros; exact Subsingleton.elim _ _ }
  let inclOp := incl.op
  have hinit : Functor.Initial inclOp := by
    apply Functor.initial_of_exists_of_isCofiltered
    · intro d
      obtain ⟨k, hik, hdk⟩ := IsDirected.directed (r := (· ≤ ·)) i₁ d.unop
      exact ⟨op ⟨k, hik⟩, ⟨(homOfLE hdk).op⟩⟩
    · intro d e s s'; exact ⟨e, 𝟙 e, by simp [Subsingleton.elim s s']⟩
  let ETail := inclOp ⋙ Esys
  let eConeTail := eCone.whisker inclOp
  have heConeTail : IsLimit eConeTail :=
    (Functor.Initial.isLimitWhiskerEquiv inclOp eCone).symm heCone
  have hETailSnd : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k),
      ETail.map g ≫ sndE (inclOp.obj k) =
        sndE (inclOp.obj j) := fun {_ _} g => hEsnd (inclOp.map g)
  have heConeTailSnd : ∀ j : Tailᵒᵖ,
      eConeTail.π.app j ≫ sndE (inclOp.obj j) = sndLim := fun j =>
    heConeSnd (inclOp.obj j)
  have hETailClosed : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k),
      IsClosedImmersion B S hS (ETail.map g) := fun {_ _} g => hEclosed (inclOp.map g)
  have hETailRep : ∀ j : Tailᵒᵖ, (ETail.obj j).IsRepresentable := by
    intro j
    have _ : (Esys.obj (op i₁)).IsRepresentable := hi₁rep
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (Esys.map (homOfLE j.unop.2).op) (hEclosed _).1
  have _ : eConeTail.pt.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (sndLim) hclosedSnd.1
  let VTail := representedDiagram (C := BigFppfOver B S hS) (J := Tailᵒᵖ) ETail hETailRep
  let repE := representedDiagramIso (C := BigFppfOver B S hS) (J := Tailᵒᵖ) ETail hETailRep
  have hrep : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k), yoneda.map (VTail.map g) ≫ (repE.app k).hom =
      (repE.app j).hom ≫ ETail.map g := fun {_ _} g => repE.hom.naturality g
  have hrepInv : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k), ETail.map g ≫ (repE.app k).inv =
      (repE.app j).inv ≫ yoneda.map (VTail.map g) := fun {_ _} g => repE.inv.naturality g
  let limObj := eConeTail.pt.reprX
  let limRepr := eConeTail.pt.reprW
  let limLeg : (j : Tailᵒᵖ) → limObj ⟶ VTail.obj j := fun j =>
    yoneda.preimage (limRepr.hom ≫ eConeTail.π.app j ≫ (repE.app j).inv)
  have hlimLeg : ∀ j : Tailᵒᵖ, yoneda.map (limLeg j) =
      limRepr.hom ≫ eConeTail.π.app j ≫ (repE.app j).inv := fun _ => yoneda.map_preimage _
  let cVTail : Cone VTail :=
    { pt := limObj
      π :=
        { app := limLeg
          naturality := by
            intro j k g
            have hgoal : limLeg k = limLeg j ≫ VTail.map g := by
              refine yoneda.map_injective ?_
              rw [yoneda.map_comp, hlimLeg, hlimLeg, ← eConeTail.w g]
              simp only [Category.assoc]
              exact congrArg (fun q => limRepr.hom ≫ eConeTail.π.app j ≫ q) (hrepInv g)
            simpa using hgoal } }
  have hConeIso : (Cone.postcompose repE.hom).obj (yoneda.mapCone cVTail) ≅ eConeTail :=
    Cone.ext limRepr (by
      intro j
      change yoneda.map (limLeg j) ≫ (repE.app j).hom = limRepr.hom ≫ eConeTail.π.app j
      rw [hlimLeg, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hcVTailYon : IsLimit (yoneda.mapCone cVTail) :=
    (IsLimit.equivOfNatIsoOfIso repE (yoneda.mapCone cVTail) eConeTail hConeIso).symm heConeTail
  have hcVTailLimit : IsLimit cVTail := isLimitOfReflects yoneda hcVTailYon
  -- The structure morphisms of the tail to the affine chart.
  let stageToU : (j : Tailᵒᵖ) → VTail.obj j ⟶ U := fun j =>
    yoneda.preimage ((repE.app j).hom ≫ sndE (inclOp.obj j))
  have hstageToU : ∀ j : Tailᵒᵖ, yoneda.map (stageToU j) =
      (repE.app j).hom ≫ sndE (inclOp.obj j) := fun _ => yoneda.map_preimage _
  have hcancel : ∀ j : Tailᵒᵖ, (repE.app j).inv ≫ yoneda.map (stageToU j) =
      sndE (inclOp.obj j) := fun j => by rw [hstageToU, Iso.inv_hom_id_assoc]
  have hstageToU_nat : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k), VTail.map g ≫ stageToU k = stageToU j := by
    intro j k g
    refine yoneda.map_injective ?_
    rw [yoneda.map_comp, hstageToU k, ← Category.assoc, hrep, Category.assoc, hETailSnd,
      hstageToU]
  let schemeTail := VTail ⋙ T
  let mapTail : schemeTail ⟶ (Functor.const Tailᵒᵖ).obj (T.obj U) :=
    { app := fun j => T.map (stageToU j)
      naturality := by
        intro j k g
        show T.map (VTail.map g) ≫ T.map (stageToU k) = 𝟙 _ ≫ T.map (stageToU j)
        rw [Category.id_comp, ← T.map_comp, hstageToU_nat g] }
  let coneTail : Cone schemeTail := T.mapCone cVTail
  let limitToU : limObj ⟶ U := yoneda.preimage (limRepr.hom ≫ sndLim)
  have hlimitToU : yoneda.map limitToU = limRepr.hom ≫ sndLim := yoneda.map_preimage _
  let mapLimit : T.obj limObj ⟶ T.obj U := T.map limitToU
  have hkey : ∀ j : Tailᵒᵖ, limLeg j ≫ stageToU j = limitToU := by
    intro j
    refine yoneda.map_injective ?_
    rw [yoneda.map_comp, hlimLeg, Category.assoc, Category.assoc, hcancel,
      heConeTailSnd, hlimitToU]
  have hconeTailComm : coneTail.π ≫ mapTail = (Functor.const Tailᵒᵖ).map mapLimit := by
    ext j
    show T.map (cVTail.π.app j) ≫ T.map (stageToU j) = T.map limitToU
    rw [← T.map_comp]
    exact congrArg T.map (hkey j)
  -- Finite type, closedness, compactness and quasi-separatedness on the scheme side.
  have hmapTailLft : ∀ j : Tailᵒᵖ, LocallyOfFiniteType (mapTail.app j) := by
    intro j
    have hfstEtale : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
          (fstE (inclOp.obj j)) :=
      (MorphismProperty.relative_isStableUnderBaseChange
        (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) T)).of_isPullback
        (IsPullback.of_hasPullback (t.app (inclOp.obj j)) p).flip hpEtaleChart
    have ha : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
          ((repE.app j).hom ≫ fstE (inclOp.obj j)) :=
      MorphismProperty.RespectsIso.precomp _ (repE.app j).hom _ hfstEtale
    have hsquare : yoneda.map (stageToU j) ≫ p =
        ((repE.app j).hom ≫ fstE (inclOp.obj j)) ≫ t.app (inclOp.obj j) := by
      rw [hstageToU, Category.assoc, hcond, Category.assoc]
    exact hFT (inclOp.obj j).unop (VTail.obj j) U
      ((repE.app j).hom ≫ fstE (inclOp.obj j)) p (stageToU j) ha
      hpEtaleChart hsquare
  have hTailClosed : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsClosedImmersion (T.map (VTail.map g)) := by
    intro j k g
    have heq : yoneda.map (VTail.map g) =
        (repE.app j).hom ≫ (ETail.map g ≫ (repE.app k).inv) := by
      rw [hrepInv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hrel : Qc (yoneda.map (VTail.map g)) := by
      rw [heq]
      exact MorphismProperty.RespectsIso.precomp Qc (repE.app j).hom _
        (MorphismProperty.RespectsIso.postcomp Qc (repE.app k).inv _ (hETailClosed g))
    exact (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp hrel
  have hTailCompact : ∀ j : Tailᵒᵖ, CompactSpace (schemeTail.obj j) := by
    intro j
    show CompactSpace (T.obj (VTail.obj j))
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS (repE.app j).symm (hEqc (inclOp.obj j).unop))
  have hTailQsep : ∀ j : Tailᵒᵖ, QuasiSeparatedSpace (schemeTail.obj j) := by
    intro j
    show QuasiSeparatedSpace (T.obj (VTail.obj j))
    have hsnd : IsQuasiSeparated B S hS (sndE (inclOp.obj j)) :=
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
        (hEalg (inclOp.obj j).unop) (hEqs (inclOp.obj j).unop) _
    have hqsIso : IsQuasiSeparated B S hS (repE.app j).hom :=
      isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
        (diagonalProp_quasiCompact_of_isIso B S hS (repE.app j).hom)
    have hqs : IsQuasiSeparated B S hS (yoneda.map (stageToU j)) := by
      rw [hstageToU j]
      exact isQuasiSeparated_comp B S hS
        (isAlgebraicSpace_yoneda B S hS (VTail.obj j)) (hEalg (inclOp.obj j).unop) _ _
        hqsIso hsnd
    have hsch : _root_.AlgebraicGeometry.QuasiSeparated (T.map (stageToU j)) :=
      (isQuasiSeparated_yoneda_map_iff B S hS (stageToU j)).mp hqs
    exact quasiSeparatedSpace_of_quasiSeparated (T.map (stageToU j))
  have hLimitClosed : _root_.AlgebraicGeometry.IsClosedImmersion mapLimit := by
    have hrel : Qc (yoneda.map limitToU) := by
      rw [hlimitToU]
      exact MorphismProperty.RespectsIso.precomp Qc limRepr.hom _ hclosedSnd
    exact (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp hrel
  -- The tail diagram of schemes is a limit, and Stacks 0A0N applies to it.
  let jBase : Tailᵒᵖ := op ⟨i₁, le_rfl⟩
  have hjBase : IsTerminal jBase :=
    IsTerminal.ofUniqueHom (fun j => (homOfLE j.unop.2).op) (fun _ _ => Subsingleton.elim _ _)
  have hconeTailLimit : IsLimit coneTail :=
    isLimit_inclusion_mapCone_of_closed B (VTail ⋙ Over.forget (B.obj hS)) jBase hjBase
      (fun j => hTailClosed (hjBase.from j))
      ((Over.forget (B.obj hS)).mapCone cVTail)
      (isLimitOfPreserves (Over.forget (B.obj hS)) hcVTailLimit)
  have _ : CompactSpace (T.obj U) := hUcompact
  have _ : QuasiSeparatedSpace (T.obj U) := hUqsep
  have _ : ∀ j : Tailᵒᵖ, CompactSpace (schemeTail.obj j) := hTailCompact
  have _ : ∀ j : Tailᵒᵖ, QuasiSeparatedSpace (schemeTail.obj j) := hTailQsep
  have _ : ∀ {j k : Tailᵒᵖ} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsClosedImmersion (schemeTail.map g) :=
    fun {_ _} g => hTailClosed g
  have _ : ∀ j : Tailᵒᵖ, LocallyOfFiniteType (mapTail.app j) := hmapTailLft
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion mapLimit := hLimitClosed
  obtain ⟨jt, hjt⟩ := AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit
    schemeTail mapTail coneTail hconeTailLimit mapLimit hconeTailComm
  -- Transport the conclusion back along the chart, by Stacks 03M4.
  refine Filter.eventually_atTop.2 ⟨jt.unop.1, fun i hi => ?_⟩
  have hiTail : i₁ ≤ i := jt.unop.2.trans hi
  have hj : _root_.AlgebraicGeometry.IsClosedImmersion
      (mapTail.app (op (⟨i, hiTail⟩ : Tail))) :=
    hjt (homOfLE (show jt.unop ≤ (⟨i, hiTail⟩ : Tail) from hi)).op
  have hclosedYoneda : Qc (yoneda.map (stageToU (op (⟨i, hiTail⟩ : Tail)))) :=
    MorphismProperty.relative_map hj
  have hclosedChart : IsClosedImmersion B S hS (pullback.snd (t.app (op i)) p) := by
    have hpre := MorphismProperty.RespectsIso.precomp Qc
      (repE.app (op (⟨i, hiTail⟩ : Tail))).inv _ hclosedYoneda
    rwa [hcancel (op (⟨i, hiTail⟩ : Tail))] at hpre
  have htfae := (isClosedImmersion_tfae B S hS (hD i) hY (t.app (op i))).out 4 1
  exact htfae.mp ⟨U, p, hpSurj, hpEtaleChart, hclosedChart⟩

/-- **The descent-situation step of Stacks 0A0T**, with the appeal to Stacks 07SR as a
parameter.

Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and let `X = lim X_i`
be a directed limit of algebraic spaces over `Y` whose stages are quasi-compact and
quasi-separated, whose transition morphisms are closed immersions, and whose structure
morphisms `X_i ⟶ Y` are locally of finite type. If `X ⟶ Y` is a closed immersion then
`X_i ⟶ Y` is a closed immersion for `i` large enough.

What this declaration contributes is the construction of the
`AlgebraicGeometry.Space.DescentSituation` to which Stacks 07SR — that a stage of a limit
situation is a scheme as soon as the limit is — is applied, together with the verification that
its limit is a scheme. Stacks 07SR itself enters as the parameter `h07SR`, in the form it is
stated in for `AlgebraicGeometry.Space.DescentSituation`, and the rest of the source's argument
is `AlgebraicGeometry.Space.eventually_isClosedImmersion_app_of_isRepresentable_stage`.

`AlgebraicGeometry.Space.eventually_isClosedImmersion_app` is this statement with `h07SR`
substituted away by
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`, and
it is that unconditional theorem which carries the `@[stacks 0A0T]` attribute.

`h07SR` is stated with the two cardinality side conditions that every statement about
an `AlgebraicGeometry.Space.DescentSituation` in this library carries — compare
`AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` for Stacks 07SF and, for Stacks 084T,
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffineSpace`
— so that a Stacks 07SR carrying them fits it, which the Stacks 07SR this library proves does:
it carries exactly `#I < B.cutoff.ord.cof`. A size-free Stacks 07SR fits just as well, by
ignoring the two extra arguments. Only the first of them, `hI`, has to be assumed here: the
second is automatic, the index category of a preorder being thin. `hI` is used for nothing but
this appeal, and the rest of the argument,
`AlgebraicGeometry.Space.eventually_isClosedImmersion_app_of_isRepresentable_stage`, is free
of it. -/
theorem eventually_isClosedImmersion_app_of_h07SR
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ Y)
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS c.pt)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
    (hClosed : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ))
    (hFT : ∀ i, IsLocallyOfFiniteType B S hS (t.app (op i)))
    (hf : IsClosedImmersion B S hS f) (hI : #I < B.cutoff.ord.cof)
    (h07SR : ∀ (J : Type u) [Preorder J] [IsDirected J (· ≤ ·)]
      (E : DescentSituation B S hS hZ J), #J < B.cutoff.ord.cof →
        (∀ a b : Jᵒᵖ, #(a ⟶ b) < B.cutoff.ord.cof) → E.limitCone.pt.IsRepresentable →
          ∃ j : J, (E.system.obj (op j)).IsRepresentable) :
    ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i)) := by
  classical
  have hcomm' : ∀ j, c.π.app j ≫ t.app j = f := fun j => by
    simpa using congrArg (fun α => α.app j) hcomm
  obtain ⟨U, p, hU, hpSurj, hpEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  refine eventually_isClosedImmersion_app_of_isRepresentable_stage B S hS hZ D t c hc f hcomm'
    hY hD hYqs hDqc hDqs hClosed hFT hf U hU p hpSurj hpEtale ?_
  let D₀ : DescentSituation B S hS hZ I :=
    { system := D
      algebraicSpace := hD
      transition_affine := fun {_ _} φ =>
        isAffineHom_of_isClosedImmersion B S hS (D.map φ) (hClosed φ)
      quasiCompact := hDqc
      quasiSeparated := hDqs
      limitCone := c
      isLimit := hc
      limitAlgebraicSpace := hX
      base := Classical.arbitrary I }
  let E : DescentSituation B S hS hZ I :=
    D₀.baseChangeOver B S hS hZ hY hYqs t f hcomm' U hU p
  have _ : HasPullbacks B.Schemes := schemeCutoff_hasPullbacks B
  have _ := MorphismProperty.inverseImage_isStableUnderBaseChange
    (BigFppfOver.toScheme B S hS) @_root_.AlgebraicGeometry.IsClosedImmersion.{u}
  have hlimRep : E.limitCone.pt.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (pullback.snd f p) ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback f p) hf).1
  have hHom : ∀ a b : Iᵒᵖ, #(a ⟶ b) < B.cutoff.ord.cof := fun a b =>
    have : Finite (a ⟶ b) := Finite.of_subsingleton
    (lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff_cof
  exact h07SR I E hI hHom hlimRep

/-- **Stacks 0A0T.** Let `Y` be an algebraic space over `S` and let `X = lim X_i` be a directed
limit of algebraic spaces over `Y` with affine transition morphisms. Assume `Y` is quasi-compact
and quasi-separated, the `X_i` are quasi-compact and quasi-separated, the transition morphisms
`X_{i'} ⟶ X_i` are closed immersions, each `X_i ⟶ Y` is locally of finite type, and `X ⟶ Y` is a
closed immersion. Then `X_i ⟶ Y` is a closed immersion for `i` large enough.

Closed immersions are affine, so the source's assumption that the transition morphisms are
affine is implied by the assumption that they are closed immersions and is not stated
separately.

The proof is `AlgebraicGeometry.Space.eventually_isClosedImmersion_app_of_isRepresentable_stage`,
which is the source's argument down to its appeal to Stacks 07SR, fed with the stage that Stacks
07SR provides: the limit of the system base changed along an affine étale surjective chart of
`Y` is a closed subspace of an affine scheme, hence a scheme, so
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall` makes
some stage of that base changed system a scheme.

The index type is `I : Type u` and its cardinality is asked to be small compared to the
cofinality of the site's size cutoff, as in Situation 084R
(`AlgebraicGeometry.Space.LimitSituation`) and as in every result of that family which this
library proves — Stacks 07SF, Stacks 0827, Stacks 084T, Stacks 086X, Stacks 07SQ and
Stacks 07SR. The bound is used only to invoke Stacks 07SR. -/
@[stacks 0A0T]
theorem eventually_isClosedImmersion_app
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ Y)
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS c.pt)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hDqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hDqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
    (hClosed : ∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ))
    (hFT : ∀ i, IsLocallyOfFiniteType B S hS (t.app (op i)))
    (hf : IsClosedImmersion B S hS f) (hI : #I < B.cutoff.ord.cof) :
    ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i)) :=
  eventually_isClosedImmersion_app_of_h07SR B S hS hZ D t c hc f hcomm hY hX hD hYqc hYqs
    hDqc hDqs (fun {_ _} φ => hClosed φ) hFT hf hI
    fun _ _ _ E hJ _ hrep =>
      E.exists_isRepresentable_system_obj_of_isSiteSmall (.of_lt_cof_op hJ) hrep

end ZeroAZeroT

end Space

end AlgebraicGeometry

end
