module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeLimitQcqs
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# A common refinement of two almost blowup squares

Two almost blowup squares with the same centre `I` in a quasi-compact and quasi-separated scheme
`X` admit a common refinement: there is a third almost blowup square with centre `I` whose
modification factors through both of the given ones by closed immersions over `X`, and whose
exceptional subscheme is the inverse image of the exceptional subscheme of each.

## Main results

* `AlgebraicGeometry.exists_isAlmostBlowUpSquare_closedImmersion_to_both`: two almost blowup
  squares with the same centre are dominated by a common one.

## References

* [Stacks Project, Tag 0EVB](https://stacks.math.columbia.edu/tag/0EVB)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EV9](https://stacks.math.columbia.edu/tag/0EV9)
* [Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

universe u

namespace AlgebraicGeometry

/-- Let `X` be a quasi-compact and quasi-separated scheme, let `I` be a quasi-coherent ideal sheaf
of finite type on `X`, and let `b₁ : X₁ ⟶ X` and `b₂ : X₂ ⟶ X` be the modifications of two almost
blowup squares with centre `I`. Then there is an almost blowup square with centre `I` and
modification `b : X' ⟶ X` together with closed immersions `i₁ : X' ⟶ X₁` and `i₂ : X' ⟶ X₂` over
`X` for which the exceptional subscheme of `b` is the inverse image of the exceptional subscheme
of `b₁` and of `b₂`. -/
@[stacks 0EVB]
public theorem exists_isAlmostBlowUpSquare_closedImmersion_to_both
    {X X₁ X₂ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : Scheme.IdealSheafData.IsFiniteType I)
    (b₁ : X₁ ⟶ X) (b₂ : X₂ ⟶ X)
    (h₁ : IsAlmostBlowUpSquare I b₁) (h₂ : IsAlmostBlowUpSquare I b₂) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (i₁ : X' ⟶ X₁) (i₂ : X' ⟶ X₂),
      IsAlmostBlowUpSquare I b ∧
        IsClosedImmersion i₁ ∧ IsClosedImmersion i₂ ∧
        i₁ ≫ b₁ = b ∧ i₂ ≫ b₂ = b ∧
        I.comap b = (I.comap b₁).comap i₁ ∧
        I.comap b = (I.comap b₂).comap i₂ := by
  classical
  have hcenter : FinitePresentation I.subschemeι :=
    (Stacks.Flatness.finitePresentation_subschemeι_iff I).mpr hI
  let K := supportedSectionsIdeal ((I.comap b₁).support : Set X₁)
  let K₂ := supportedSectionsIdeal ((I.comap b₂).support : Set X₂)
  let C := Stacks.Flatness.FinitePresentationSubscheme K
  let D := Stacks.Flatness.subschemeDiagram K
  have : IsFiltered C := Stacks.Flatness.finitePresentationSubscheme_isFiltered K
  have hdom {Y : Scheme.{u}} {b : Y ⟶ X} (h : IsAlmostBlowUpSquare I b) :
      IsProper b ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y :=
    have := h.proper
    ⟨this, (quasiCompact_iff_compactSpace b).mp inferInstance,
      quasiSeparatedSpace_of_quasiSeparated b⟩
  obtain ⟨_, _, _⟩ := hdom h₁
  let c := Stacks.Flatness.subschemeCone K
  have hc : IsLimit c := Stacks.Flatness.isLimitSubschemeCone K
  let e₁ : Over.mk (K.subschemeι ≫ b₁) ≅ Over.mk (blowUpToBase I) := h₁.blowUp.some
  let e₂ : Over.mk (K₂.subschemeι ≫ b₂) ≅ Over.mk (blowUpToBase I) := h₂.blowUp.some
  let q : Over.mk (K.subschemeι ≫ b₁) ⟶ Over.mk (K₂.subschemeι ≫ b₂) := e₁.hom ≫ e₂.inv
  let qIso : K.subscheme ≅ K₂.subscheme :=
    (Over.forget X).mapIso e₁ ≪≫ ((Over.forget X).mapIso e₂).symm
  have hqleft : q.left = qIso.hom := by dsimp [q, qIso]
  let f₂ : K.subscheme ⟶ X₂ := qIso.hom ≫ K₂.subschemeι
  have hf₂ : f₂ ≫ b₂ = K.subschemeι ≫ b₁ := by
    dsimp only [f₂]
    rw [Category.assoc, ← hqleft]
    exact Over.w q
  let fPB : K.subscheme ⟶ pullback b₁ b₂ := pullback.lift K.subschemeι f₂ hf₂.symm
  let fOver : c.pt ⟶ Over.mk (pullback.fst b₁ b₂) :=
    Over.homMk fPB (by
      change fPB ≫ pullback.fst b₁ b₂ = K.subschemeι
      simp [fPB])
  have hCompactStage (J : C) : CompactSpace J.val.subscheme :=
    (quasiCompact_iff_compactSpace J.val.subschemeι).mp inferInstance
  have hQSStage (J : C) : QuasiSeparatedSpace J.val.subscheme :=
    quasiSeparatedSpace_of_quasiSeparated J.val.subschemeι
  have hCompactObj (j : Cᵒᵖ) : CompactSpace (D.obj j).left := by
    change CompactSpace j.unop.val.subscheme
    infer_instance
  have hQSObj (j : Cᵒᵖ) : QuasiSeparatedSpace (D.obj j).left := by
    change QuasiSeparatedSpace j.unop.val.subscheme
    infer_instance
  have hClosed {i j : Cᵒᵖ} (g : i ⟶ j) : IsClosedImmersion (D.map g).left := by
    dsimp [D, Stacks.Flatness.subschemeDiagram]
    apply IsClosedImmersion.of_comp_isClosedImmersion
      (Scheme.IdealSheafData.inclusion g.unop.le) j.unop.val.subschemeι
  have hfpFst : LocallyOfFinitePresentation (Over.mk (pullback.fst b₁ b₂)).hom := by
    have : LocallyOfFinitePresentation b₂ := h₂.finitePresentation.locallyOfFinitePresentation
    change LocallyOfFinitePresentation (pullback.fst b₁ b₂)
    infer_instance
  obtain ⟨j, p, hp⟩ := Limits.exists_hom_of_preservesColimit_yoneda hc fOver
  let j₀ : C := j.unop
  let g₀ : (D.obj j).left ⟶ X₂ := p.left ≫ pullback.snd b₁ b₂
  have hbase₀ : g₀ ≫ b₂ = (D.obj j).hom ≫ b₁ := by
    dsimp only [g₀]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ b₁) (Over.w p)
  have hg₀ : LocallyOfFiniteType g₀ := by
    have : IsClosedImmersion (D.obj j).hom := by
      dsimp [D, Stacks.Flatness.subschemeDiagram]
      infer_instance
    have : LocallyOfFiniteType (g₀ ≫ b₂) := by
      rw [hbase₀]
      infer_instance
    exact locallyOfFiniteType_of_comp g₀ b₂
  have hpLeft : (c.π.app j).left ≫ p.left = fPB :=
    congrArg (fun z : c.pt ⟶ Over.mk (pullback.fst b₁ b₂) => z.left) hp
  have hlim : (c.π.app j).left ≫ g₀ = f₂ := by
    dsimp [g₀]
    rw [← Category.assoc, hpLeft]
    exact pullback.lift_snd K.subschemeι f₂ hf₂.symm
  let Dsch : Cᵒᵖ ⥤ Scheme := D ⋙ Over.forget X₁
  let csch : Cone Dsch := (Over.forget X₁).mapCone c
  have hcsch : IsLimit csch := isLimitOfPreserves (Over.forget X₁) hc
  let Tail := {J : C // j₀ ≤ J}
  have : IsDirectedOrder C := IsFiltered.isDirectedOrder C
  have : IsDirectedOrder Tail := by
    constructor
    intro a b
    obtain ⟨d, had, hbd⟩ : ∃ d : C, a.val ≤ d ∧ b.val ≤ d := IsDirected.directed a.val b.val
    obtain ⟨e, hde, h₀e⟩ : ∃ e : C, d ≤ e ∧ j₀ ≤ e := IsDirected.directed d j₀
    exact ⟨⟨e, h₀e⟩, had.trans hde, hbd.trans hde⟩
  have : Nonempty Tail := ⟨⟨j₀, le_rfl⟩⟩
  let toC : Tail → C := Subtype.val
  have htoC : Monotone toC := Subtype.mono_coe _
  let F : Tail ⥤ C := htoC.functor
  have hFfinal : F.Final := by
    rw [Monotone.final_functor_iff htoC]
    intro J
    obtain ⟨d, hJd, h₀d⟩ : ∃ d : C, J ≤ d ∧ j₀ ≤ d := IsDirected.directed J j₀
    exact ⟨⟨d, h₀d⟩, hJd⟩
  let FI : Tailᵒᵖ ⥤ Cᵒᵖ := F.op
  have : FI.Initial := Functor.initial_op_of_final F
  let Dtail : Tailᵒᵖ ⥤ Scheme := FI ⋙ Dsch
  let ctail : Cone Dtail := csch.whisker FI
  have hctail : IsLimit ctail := (Functor.Initial.isLimitWhiskerEquiv FI csch).symm hcsch
  let α (k : Tail) : (Opposite.op k.val : Cᵒᵖ) ⟶ Opposite.op j₀ := (homOfLE k.property).op
  let t : Dtail ⟶ (Functor.const Tailᵒᵖ).obj X₂ :=
    { app := fun k => Dsch.map (α k.unop) ≫ g₀
      naturality := by
        intro k l f
        dsimp [Dtail, FI]
        simp only [Category.comp_id]
        rw [← Functor.map_comp_assoc,
          Subsingleton.elim ((F.map f.unop).op ≫ α l.unop) (α k.unop)] }
  have hcomm : ctail.π ≫ t = (Functor.const Tailᵒᵖ).map f₂ := by
    ext k
    dsimp [ctail, t, Dtail, FI, F, htoC, toC]
    rw [← Category.assoc, csch.w (α k.unop)]
    exact hlim
  obtain ⟨_, _, _⟩ := hdom h₂
  have hCompactTail (k : Tailᵒᵖ) : CompactSpace (Dtail.obj k) := by
    change CompactSpace (D.obj (FI.obj k)).left
    infer_instance
  have hQSTail (k : Tailᵒᵖ) : QuasiSeparatedSpace (Dtail.obj k) := by
    change QuasiSeparatedSpace (D.obj (FI.obj k)).left
    infer_instance
  have hClosedTail {k l : Tail} (h : k ≤ l) :
      IsClosedImmersion (Dtail.map (homOfLE h).op) :=
    hClosed (F.map (homOfLE h)).op
  have hftTail (k : Tailᵒᵖ) : LocallyOfFiniteType (t.app k) := by
    dsimp [t]
    have : IsClosedImmersion (Dsch.map (α k.unop)) := hClosed (α k.unop)
    infer_instance
  have hfLim : IsClosedImmersion (show ctail.pt ⟶ X₂ from f₂) :=
    inferInstanceAs (IsClosedImmersion (qIso.hom ≫ K₂.subschemeι))
  have hfLim : IsClosedImmersion (show ctail.pt ⟶ X₂ from f₂) :=
    inferInstanceAs (IsClosedImmersion (qIso.hom ≫ K₂.subschemeι))
  obtain ⟨k, hk⟩ := (eventually_isClosedImmersion Dtail t ctail hctail f₂ hcomm).exists
  let T : Scheme := Dsch.obj (Opposite.op k.val)
  let i₁ : T ⟶ X₁ := (D.obj (Opposite.op k.val)).hom
  let i₂ : T ⟶ X₂ := t.app (Opposite.op k)
  have hbase₂ : i₂ ≫ b₂ = i₁ ≫ b₁ := by
    change (Dsch.map (α k) ≫ g₀) ≫ b₂ = (D.obj (Opposite.op k.val)).hom ≫ b₁
    rw [Category.assoc, hbase₀, ← Category.assoc]
    exact congrArg (fun z => z ≫ b₁) (Over.w (D.map (α k)))
  have hsquare : IsAlmostBlowUpSquare I (i₁ ≫ b₁) := by
    change IsAlmostBlowUpSquare I (k.val.val.subschemeι ≫ b₁)
    exact { (le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare I b₁ h₁ k.val.val
      k.val.property.1).1 k.val.property.2 with center_finitePresentation := hcenter }
  refine ⟨T, i₁ ≫ b₁, i₁, i₂, hsquare, ?_, hk, rfl, hbase₂, ?_, ?_⟩
  · change IsClosedImmersion k.val.val.subschemeι
    infer_instance
  · exact Scheme.IdealSheafData.comap_comp I i₁ b₁
  · rw [← hbase₂]
    exact Scheme.IdealSheafData.comap_comp I i₂ b₂

end AlgebraicGeometry

end
