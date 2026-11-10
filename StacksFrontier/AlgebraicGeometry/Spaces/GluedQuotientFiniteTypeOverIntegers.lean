module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedQuotientLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationStep
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The glued quotients of Stacks 07SU are quasi-separated and of finite type over `ℤ`

In the proof of absolute Noetherian approximation, Stacks 07SU, the stages are the quotients
`X_i = V_i/R_i` of the extended relations `R_i = V_i ⊔_{W_i} (W_i ×_{U_i} W_i)`
(`AlgebraicGeometry.Space.OpenKernelPairExtension.quotient`). The source observes: "As `V_i` is
of finite type over `ℤ` and `R_i` is quasi-compact we see that `X_i` is quasi-separated and of
finite type over `ℤ` (Stacks 07S4, 040W and 040Y)", where `R_i` is quasi-compact "as `U_i` is
quasi-separated and `W_i` quasi-compact". This file proves that observation (step (d) of the
proof), and also that the empty open subspace of an algebraic space over `Spec ℤ` has a
Noetherian approximation, the base case of the descending induction of
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_extendsOverElementaryChart`.

## Main results

All names below lie in the namespace `AlgebraicGeometry.Space`.

* `OpenKernelPairExtension.compactSpace_Q`: `W ×_U W` is quasi-compact (Stacks 0AHR).
* `OpenKernelPairExtension.isAbsolutelyQuasiSeparated_quotient`: the quotient `V/R` is
  quasi-separated (Stacks 07S4).
* `isFiniteType_viewOverIntegers_of_etaleChart`: an algebraic space over `Spec ℤ` with a
  surjective étale chart of finite type over `ℤ` is of finite type over `ℤ` (Stacks 040Y and
  040W).
* `ElementaryChart.LimitStageSystem.hasNoetherianApproximation_of_finiteType`: the conclusion of
  Stacks 07SU from a limit stage system with `V_i` of finite type over `ℤ`, `U_i` quasi-separated
  and `W_i` quasi-compact.
* `hasNoetherianApproximation_sheafify_bot`: the empty open subspace has a Noetherian
  approximation.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_GluedQuotientFiniteTypeOverIntegers :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_GluedQuotientFiniteTypeOverIntegers
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace OpenKernelPairExtension

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : BigFppfOver B S hS}
  (E : OpenKernelPairExtension B S hS X V W)

/-- **The kernel pair `W ×_X W` of an extended relation is quasi-compact** when `W` is
quasi-compact and `X` is a quasi-separated algebraic space, by Stacks 0AHR. -/
theorem compactSpace_Q (hZ : B.Contains (⊤_ Scheme.{u})) (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) [CompactSpace ((F).obj W)] :
    CompactSpace ((F).obj E.Q) := by
  obtain ⟨W', hW', ⟨e⟩⟩ :=
    (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B S hS hZ X hX).mp hXqs W W E.p E.p
      inferInstance inferInstance
  let e' : W' ≅ E.Q := Yoneda.fullyFaithful.preimageIso (e ≪≫ E.isPullback.isoPullback.symm)
  exact ((F).map e'.hom).homeomorph.compactSpace

/-- **The glued relation `R = V ⊔_W Q` is quasi-compact** when `V` and `Q` are: it is covered by
the images of `V` and `Q`. -/
theorem compactSpace_glued [CompactSpace ((F).obj V)] [CompactSpace ((F).obj E.Q)] :
    CompactSpace E.glued := by
  refine ⟨?_⟩
  have h : (Set.univ : Set E.glued) ⊆
      Set.range (pushout.inl ((F).map E.j) ((F).map E.δ)) ∪
        Set.range (pushout.inr ((F).map E.j) ((F).map E.δ)) := by
    intro x _
    rcases AlgebraicGeometry.exists_eq_of_isPushout_of_isOpenImmersion
      (IsPushout.of_hasPushout ((F).map E.j) ((F).map E.δ)) x with ⟨v, hv⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr ⟨q, hq⟩
  exact ((isCompact_range (pushout.inl ((F).map E.j) ((F).map E.δ)).continuous).union
    (isCompact_range (pushout.inr ((F).map E.j) ((F).map E.δ)).continuous)).of_isClosed_subset
    isClosed_univ h

/-- The target map `R ⟶ V` of the glued relation is quasi-compact when `V` and `Q` are
quasi-compact and `V` is quasi-separated. -/
theorem quasiCompact_map_t [CompactSpace ((F).obj V)] [QuasiSeparatedSpace ((F).obj V)]
    [CompactSpace ((F).obj E.Q)] : QuasiCompact ((F).map E.t) := by
  have := E.compactSpace_glued
  change QuasiCompact E.targetScheme
  infer_instance

/-- **Stacks 07S4 for the quotient of an extended relation.** If `V` is quasi-compact and
quasi-separated and the kernel pair `Q = W ×_X W` is quasi-compact, then the quotient `V/R` is a
quasi-separated algebraic space: its chart `V ⟶ V/R` has kernel pair `R`, which is
quasi-compact over `V`. -/
theorem isAbsolutelyQuasiSeparated_quotient (hZ : B.Contains (⊤_ Scheme.{u}))
    [CompactSpace ((F).obj V)] [QuasiSeparatedSpace ((F).obj V)] [CompactSpace ((F).obj E.Q)] :
    IsAbsolutelyQuasiSeparated B S hS hZ E.quotient := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) (F))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  have ht := presheaf_yoneda_map_of_inverseImage B S hS (P := @QuasiCompact.{u}) inferInstance
    E.t E.quasiCompact_map_t
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ E.quotient
    E.isAlgebraicSpace_quotient ⟨V, E.π, inferInstance, E.π_surjective, E.π_etale, Or.inl ?_⟩
  rw [← E.isPullback_π.isoPullback_inv_fst]
  exact MorphismProperty.RespectsIso.precomp _ _ _ ht

end OpenKernelPairExtension

end General

/-! ### Finite type over `Spec ℤ` -/

section OverIntegers

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "F" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

/-- The view over `Spec ℤ` of a presheaf on the big fppf site of `Spec ℤ` is that presheaf: the
structure morphism of the terminal scheme is its identity, and relocalization along an identity
is left adjoint to the identity functor. -/
noncomputable def viewOverIntegersOfTerminalIso
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :
    viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X ≅ X :=
  eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj X)
      (show integersMap B (⊤_ Scheme.{u}) hZ hZ = 𝟙 _ by ext; exact terminal.hom_ext _ _)) ≪≫
    (Adjunction.leftAdjointUniq (OverShriek.relocalizeAdjunction (𝟙 (B.obj hZ)))
      (Adjunction.id.ofNatIsoRight ((Functor.whiskeringLeft _ _ (Type u)).mapIso
        (NatIso.op (Over.mapId (B.obj hZ))).symm).symm)).app X

/-- The structure morphism of the presheaf represented by an object of the site over `Spec ℤ`
is locally of finite type when the underlying scheme is locally of finite type over `ℤ`. -/
theorem isLocallyOfFiniteType_terminal_from_yoneda (V : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [LocallyOfFiniteType (terminal.from ((F).obj V))] :
    IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (yoneda.obj V)) := by
  have h : (F).map (terminal.from V) =
      terminal.from ((F).obj V) ≫ (toSchemeTerminalIso B (⊤_ Scheme.{u}) hZ).inv := by
    rw [Iso.eq_comp_inv]
    exact terminal.hom_ext _ _
  have hV : LocallyOfFiniteType ((F).map (terminal.from V)) := by
    rw [h]
    infer_instance
  exact holdsOnEveryEtaleChart_of_isTerminal B (⊤_ Scheme.{u}) hZ
    (isTerminal_yoneda_obj_terminal B (⊤_ Scheme.{u}) hZ) terminalIsTerminal
    (yoneda.map (terminal.from V)) _
    ((isLocallyOfFiniteType_yoneda_map_iff B (⊤_ Scheme.{u}) hZ _).mpr hV)

/-- **Stacks 040Y and 040W: finite type over `ℤ` from one chart.** An algebraic space over
`Spec ℤ` with a surjective étale chart `V ⟶ X` whose scheme `V` is quasi-compact and locally of
finite type over `ℤ` is of finite type over `ℤ`: local finite type is read on the chart
(Stacks 040Y, condition (6)) and quasi-compactness passes to the image (Stacks 040W, part (2)). -/
theorem isFiniteType_viewOverIntegers_of_etaleChart
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (a : yoneda.obj V ⟶ X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) a)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (F))) a)
    [LocallyOfFiniteType (terminal.from ((F).obj V))] [CompactSpace ((F).obj V)] :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X)) := by
  have hcomp : a ≫ terminal.from X = terminal.from (yoneda.obj V) := terminal.hom_ext _ _
  refine ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B (⊤_ Scheme.{u}) hZ
    (viewOverIntegersOfTerminalIso X)).mpr ?_, ?_⟩
  · refine isLocallyOfFiniteType_of_exists_surjective_etale_source_chart B (⊤_ Scheme.{u}) hZ
      ⟨V, a, hsurj, het, ?_⟩
    rw [hcomp]
    exact isLocallyOfFiniteType_terminal_from_yoneda V
  · have hterm := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
    have hqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ (terminal.from X) :=
      IsQuasiCompact.of_isSurjective_comp B (⊤_ Scheme.{u}) hZ
        (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ V) hX hterm hcomp
        (isSurjective_of_presheafSurjective B (⊤_ Scheme.{u}) hZ a hsurj)
        (isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hterm
          GluedEtaleQuotient.isAbsolutelyQuasiSeparated_terminal
          (isQuasiCompactSpace_yoneda B (⊤_ Scheme.{u}) hZ V inferInstance) _)
    have h : terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X) =
        (viewOverIntegersOfTerminalIso X).hom ≫ terminal.from X := terminal.hom_ext _ _
    rw [h]
    exact isQuasiCompact_of_isIso_comp B (⊤_ Scheme.{u}) hZ (viewOverIntegersOfTerminalIso X).inv
      (by rwa [Iso.inv_hom_id_assoc])

/-- A scheme which is locally of finite type over `ℤ` is quasi-separated: it is locally
Noetherian, `ℤ` being a Noetherian ring. -/
@[ega "IV 1.2.8" "special case"]
theorem quasiSeparatedSpace_of_locallyOfFiniteType_terminal (T : Scheme.{u})
    [LocallyOfFiniteType (terminal.from T)] : QuasiSeparatedSpace T := by
  have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian e.hom
  have := LocallyOfFiniteType.isLocallyNoetherian (terminal.from T)
  infer_instance

namespace OpenKernelPairExtension

variable {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {V W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (E : OpenKernelPairExtension B (⊤_ Scheme.{u}) hZ X V W)

/-- **Step (d) of Stacks 07SU.** If `V` is quasi-compact and locally of finite type over `ℤ`, `W`
is quasi-compact and `X` is a quasi-separated algebraic space, then the quotient `V/R` of the
extended relation is quasi-separated and of finite type over `ℤ`. -/
theorem isAbsolutelyQuasiSeparated_quotient_and_isFiniteType (hX : IsAlgebraicSpace B _ hZ X)
    (hXqs : IsAbsolutelyQuasiSeparated B _ hZ hZ X)
    [LocallyOfFiniteType (terminal.from ((F).obj V))] [CompactSpace ((F).obj V)]
    [CompactSpace ((F).obj W)] :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ E.quotient ∧
      IsFiniteType B (⊤_ Scheme.{u}) hZ
        (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ E.quotient)) := by
  have := E.compactSpace_Q hZ hX hXqs
  have := quasiSeparatedSpace_of_locallyOfFiniteType_terminal ((F).obj V)
  exact ⟨E.isAbsolutelyQuasiSeparated_quotient hZ,
    isFiniteType_viewOverIntegers_of_etaleChart E.isAlgebraicSpace_quotient E.π E.π_surjective
      E.π_etale⟩

end OpenKernelPairExtension

namespace ElementaryChart.LimitStageSystem

variable {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  {C : ElementaryChart X V} {I : Type u} [Preorder I] (D : C.LimitStageSystem I)

/-- **The conclusion of Stacks 07SU from a limit stage system, with step (d) discharged.** If the
chart `f : V ⟶ X` is surjective, every `V_i` is quasi-compact and locally of finite type over
`ℤ`, every `U_i` is a quasi-separated algebraic space and every `W_i` is quasi-compact, then `X`
has a Noetherian approximation, by the system of the quotients `X_i = V_i/R_i`. -/
theorem hasNoetherianApproximation_of_finiteType [Nonempty I] [IsDirected I (· ≤ ·)]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    (hU : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.Ui i))
    (hUqs : ∀ i, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.Ui i))
    (hVft : ∀ i, LocallyOfFiniteType (terminal.from ((F).obj (D.Vi i))))
    (hVc : ∀ i, CompactSpace ((F).obj (D.Vi i)))
    (hWc : ∀ i, CompactSpace ((F).obj (D.Wi i))) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  have h := forall_and.mp fun i ↦
    (D.E i).isAbsolutelyQuasiSeparated_quotient_and_isFiniteType (hU i) (hUqs i)
  D.hasNoetherianApproximation hZ hX hsurj h.1 h.2

end ElementaryChart.LimitStageSystem

/-! ### The empty open subspace -/

/-- An object of the site over which the sheafified bottom subfunctor has a section is empty:
a point of it would give a point of the sheafified bottom subfunctor, which has none. -/
theorem isEmpty_of_hom_sheafify_bot (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    {T : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (x : yoneda.obj T ⟶
      ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor) :
    IsEmpty ((F).obj T) := by
  refine ⟨fun t ↦ ?_⟩
  have := isEmpty_points_sheafify_bot B (⊤_ Scheme.{u}) hZ X
  exact this.false (pointsMap B (⊤_ Scheme.{u}) hZ _ x
    ((schemePointRepresentative B (⊤_ Scheme.{u}) hZ T t).class B (⊤_ Scheme.{u}) hZ _))

/-- **The base case of the descending induction of Stacks 07SU.** The empty open subspace of an
algebraic space over `Spec ℤ` (the sheafified bottom subfunctor) has a Noetherian approximation:
it is quasi-separated and of finite type over `ℤ`, every scheme mapping to it being empty, so it
is its own approximation. -/
theorem hasNoetherianApproximation_sheafify_bot
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ
      ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor := by
  set Y := ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor
  have hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y :=
    (isOpenSubspace_sheafify_bot B (⊤_ Scheme.{u}) hZ X hX).1
  have hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y := by
    refine (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B (⊤_ Scheme.{u}) hZ hZ Y
      hY).mpr fun U V f g _ _ ↦ ?_
    have hrep := hY.diagonal_representable.of_diag f
    have hpb := hrep.isPullback' g
    have := isEmpty_of_hom_sheafify_bot X (yoneda.map (hrep.fst' g) ≫ f)
    exact ⟨hrep.pullback g, inferInstance, ⟨hpb.isoPullback⟩⟩
  obtain ⟨U, a, hsurj, het⟩ := hY.exists_atlas
  have := isEmpty_of_hom_sheafify_bot X a
  exact ⟨NoetherianApproximation.const hY hqs
    (isFiniteType_viewOverIntegers_of_etaleChart hY a hsurj het)⟩

end OverIntegers

end AlgebraicGeometry.Space

end
