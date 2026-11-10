module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartWSystem
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CardinalBound

/-!
# Absolute Noetherian approximation indexed below the cutoff

We bound the size of the index set in absolute Noetherian approximation, Stacks 07SU: provided
the W-systems are given over approximations of the open part indexed below the cutoff
(`AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`), every quasi-compact
quasi-separated algebraic space over `Spec ℤ` has a Noetherian approximation indexed below the
cutoff, whose system is then bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`). We deduce forms of Stacks 0A0X whose inputs
about Stacks 07SU are these W-systems.

The bound is below the cutoff, not below its cofinality: the latter is impossible for the system
of Stacks 07SU, since `Spec F` for a field `F` of size the cofinality of the cutoff is no limit of
a countable system of schemes of finite type over `ℤ`.

## Main definitions

* `AlgebraicGeometry.Space.HasCutoffBoundedNoetherianApproximation`: a Noetherian approximation
  indexed below the cutoff.
* `AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`: the W-systems of the proof
  of Stacks 07SU, over approximations indexed below the cutoff.

## Main results

* `AlgebraicGeometry.Space.induction_on_elementaryChart_strata`: the descending induction over the
  strata of Stacks 07ST, for any property of presheaves invariant under isomorphism.
* `ElementaryChart.LimitStageSystem.exists_noetherianApproximation_card_eq`: the quotients of a
  limit stage system are indexed by its index set.
* `AlgebraicGeometry.Space.ElementaryChart.WSystem.exists_noetherianApproximation_card_le`: the
  approximation built from a W-system is indexed by a set of cardinality at most
  `max #I (size V)`.
* `AlgebraicGeometry.Space.exists_isCutoffBounded_noetherianApproximation`: Stacks 07SU over
  `Spec ℤ` with a system bounded by the cutoff, given the W-systems.
* `exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedWSystems`: Stacks 0A0X
  under the cutoff bound, given the W-systems.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "F" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

/-! ### Noetherian approximations indexed below the cutoff -/

variable (B hZ) in
/-- A presheaf on the big fppf site of `Spec ℤ` *has a Noetherian approximation indexed below the
cutoff* when it has a Noetherian approximation whose index set has fewer elements than the cutoff
of the site. -/
def HasCutoffBoundedNoetherianApproximation
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X, #A.I < B.cutoff

/-- A Noetherian approximation indexed below the cutoff transports along an isomorphism, with
the same index set. -/
theorem HasCutoffBoundedNoetherianApproximation.ofIso
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasCutoffBoundedNoetherianApproximation B hZ X) (e : X ≅ Y) :
    HasCutoffBoundedNoetherianApproximation B hZ Y :=
  h.elim fun A hA ↦ ⟨A.ofIso e, hA⟩

/-- A Noetherian approximation indexed below the cutoff is in particular a Noetherian
approximation. -/
theorem HasCutoffBoundedNoetherianApproximation.hasNoetherianApproximation
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasCutoffBoundedNoetherianApproximation B hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  h.elim fun A _ ↦ ⟨A⟩

/-- The system of a Noetherian approximation indexed below the cutoff is bounded by the cutoff
(`AlgebraicGeometry.Space.NoetherianApproximation.isCutoffBoundedSystem`). -/
theorem HasCutoffBoundedNoetherianApproximation.exists_isCutoffBoundedSystem
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasCutoffBoundedNoetherianApproximation B hZ X) :
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X, letI := A.preorder;
      IsCutoffBoundedSystem B (⊤_ Scheme.{u}) hZ A.diagram :=
  h.elim fun A hA ↦ ⟨A, A.isCutoffBoundedSystem B hA⟩

/-- The empty open subspace of an algebraic space over `Spec ℤ` has a Noetherian approximation
indexed below the cutoff. -/
theorem hasCutoffBoundedNoetherianApproximation_sheafify_bot
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) :
    HasCutoffBoundedNoetherianApproximation B hZ
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
  refine ⟨NoetherianApproximation.const hY hqs
    (isFiniteType_viewOverIntegers_of_etaleChart hY a hsurj het), ?_⟩
  change #PUnit.{u + 1} < B.cutoff
  rw [Cardinal.mk_punit]
  exact one_lt_aleph0.trans B.aleph0_lt_cutoff

/-! ### The descending induction over the strata, for any property -/

/-- The descending induction over the strata of Stacks 07ST. Let `P` be a property of
presheaves on the big fppf site of `Spec ℤ`, invariant under isomorphism, which holds for the
empty open subspace of every algebraic space and which passes from the open part `U` of an
elementary chart `f : V ⟶ X` (`V` quasi-compact and separated, `f` surjective, `X` a
quasi-compact quasi-separated algebraic space) to `X`. Then `P` holds for every quasi-compact
quasi-separated algebraic space over `Spec ℤ`. -/
theorem induction_on_elementaryChart_strata
    (P : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) → Prop)
    (hiso : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, P X → (X ≅ Y) → P Y)
    (hstep : ∀ (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (C : ElementaryChart X V),
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X →
      CompactSpace ((F).obj V) →
      Scheme.IsSeparated ((F).obj V) →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f →
      IsOpenSubspace B (⊤_ Scheme.{u}) hZ C.U →
      P C.U.toFunctor → P X)
    (hempty : ∀ X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
      P ((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)).toFunctor)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) : P X := by
  obtain ⟨n, U, -, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ X hX hqc hqs
  have key : ∀ k, k ≤ n → P (U (n - k)).toFunctor := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, hUn]
      exact hempty X hX
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hp1 : n - (k + 1) + 1 = n - k := by omega
      have hpn : n - (k + 1) < n := by omega
      rw [← hp1] at ih'
      obtain ⟨hTcl, hrange, -, hVc, hVsep, hsurj, het, hiso'⟩ := hdata ⟨n - (k + 1), hpn⟩
      have hle : U (n - (k + 1) + 1) ≤ U (n - (k + 1)) := hUmono _ hpn
      have hU' := isOpenSubspace_preimage_of_le B (⊤_ Scheme.{u}) hZ hle
        (hUopen _ (by omega))
      have hX' := (hUopen (n - (k + 1)) hpn.le).1
      have hqs' := isAbsolutelyQuasiSeparated_of_mono B (⊤_ Scheme.{u}) hZ hZ hX'
        (U (n - (k + 1))).ι inferInstance hqs
      have hqc' := isQuasiCompactSpace_of_isSurjective B (⊤_ Scheme.{u}) hZ
        (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _) hX' _
        (isSurjective_of_presheafSurjective B (⊤_ Scheme.{u}) hZ _ hsurj)
        (isQuasiCompactSpace_yoneda B (⊤_ Scheme.{u}) hZ _ hVc)
      exact hstep _ _ (ElementaryChart.ofStratum _ hsurj het _ _ hU' hTcl
        (range_pointsMap_eq_compl_of_le hle _ hrange) hiso') hX' hqc' hqs' hVc hVsep hsurj hU'
        (hiso ih' (preimageIso_of_le hle).symm)
  have h0 := key n le_rfl
  rw [Nat.sub_self, hU0] at h0
  exact hiso h0 (topSubfunctorIso B (⊤_ Scheme.{u}) hZ)

/-! ### The size of the index through the quotients and through Stacks 07RN -/

namespace ElementaryChart

variable {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}

namespace LimitStageSystem

variable {C : ElementaryChart X V} {I : Type u} [Preorder I] (D : C.LimitStageSystem I)

/-- The quotients of a limit stage system indexed by `I` form a Noetherian approximation
`X = lim V_i/R_i` indexed by a set of the cardinality of `I`. -/
theorem exists_noetherianApproximation_card_eq [Nonempty I] [IsDirected I (· ≤ ·)]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    (hU : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.Ui i))
    (hUqs : ∀ i, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.Ui i))
    (hVft : ∀ i, LocallyOfFiniteType (terminal.from ((F).obj (D.Vi i))))
    (hVc : ∀ i, CompactSpace ((F).obj (D.Vi i)))
    (hWc : ∀ i, CompactSpace ((F).obj (D.Wi i))) :
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X, #A.I = #I := by
  obtain ⟨e, -⟩ := D.exists_iso_limit hX hsurj
  have hq := fun j : Iᵒᵖ ↦
    (D.E j.unop).isAbsolutelyQuasiSeparated_quotient_and_isFiniteType (hU _) (hUqs _)
  refine ⟨(noetherianApproximationLimit B _ hZ hZ D.diagram
    (fun j ↦ (D.E j.unop).isAlgebraicSpace_quotient) (fun {j j'} g ↦ ?_)
    (fun j ↦ (hq j).1) (fun j ↦ (hq j).2)).ofIso e.symm, rfl⟩
  have := D.isAffineHom_v (leOfHom g.unop)
  exact (D.T (leOfHom g.unop)).isAffineHom_φ

end LimitStageSystem

namespace WSystem

variable {C : ElementaryChart X V}
  {A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor} (WS : C.WSystem A)

include WS in
/-- Given a W-system over a Noetherian approximation of the open part indexed by `I`, the space
`X` has a Noetherian approximation indexed by a set of cardinality at most `max #I (size V)`. -/
theorem exists_noetherianApproximation_card_le
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    [CompactSpace ((F).obj V)] [QuasiSeparatedSpace ((F).obj V)] :
    ∃ A' : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X,
      #A'.I ≤ max #A.I ((F).obj V).size := by
  have : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have : ∀ {i j : A.Iᵒᵈ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom (WS.schemeDiagram.map g) :=
    fun g ↦ WS.isAffineHom_map _
  have : ∀ i, LocallyOfFiniteType (terminal.from (WS.schemeDiagram.obj i)) := fun i ↦
    locallyOfFiniteType_terminal_of_etale (A.isAlgebraicSpace _) (A.isFiniteTypeOverIntegers _)
      (WS.p.app _) (WS.etale_p _)
  have : ∀ i, CompactSpace (WS.schemeDiagram.obj i) := fun i ↦ WS.compactSpace _
  have : ∀ i, QuasiCompact (terminal.from (WS.schemeDiagram.obj i)) := fun i ↦ inferInstance
  have := WS.compactSpace_openW
  obtain ⟨Q, hQ, hcard⟩ := exists_finiteTypeApproximation_card_le WS.schemeDiagram
    ((F).obj V) C.openW WS.schemeCone WS.isLimit_schemeCone
  let := Q.indexPreorder
  let := Q.indexNonempty
  let := Q.indexDirected
  obtain ⟨A', hA'⟩ := (WS.stageSystem Q hQ).exists_noetherianApproximation_card_eq hX.isSheaf
    hsurj (fun j ↦ A.isAlgebraicSpace _) (fun j ↦ A.isAbsolutelyQuasiSeparated _)
    (fun j ↦ Q.locallyOfFiniteType _)
    (fun j ↦ @QuasiCompact.compactSpace_of_compactSpace _ _ _
      (Q.quasiCompact (OrderDual.toDual j)) inferInstance)
    (fun j ↦ WS.compactSpace _)
  exact ⟨A', hA'.trans_le hcard⟩

end WSystem

variable (B hZ) in
/-- The W-systems exist over approximations indexed below the cutoff: for every elementary chart
of the problem posed in the proof of Stacks 07SU (the hypotheses of
`AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`) whose open part has
a Noetherian approximation indexed below the cutoff, some Noetherian approximation of the open
part indexed below the cutoff carries a W-system
(`AlgebraicGeometry.Space.ElementaryChart.WSystem`). -/
def HasCutoffBoundedWSystems : Prop :=
  ∀ (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (C : ElementaryChart X V),
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X →
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X →
    CompactSpace ((F).obj V) →
    Scheme.IsSeparated ((F).obj V) →
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f →
    IsOpenSubspace B (⊤_ Scheme.{u}) hZ C.U →
    HasCutoffBoundedNoetherianApproximation B hZ C.U.toFunctor →
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor,
      #A.I < B.cutoff ∧ Nonempty (C.WSystem A)

end ElementaryChart

open ElementaryChart in
/-- Given the W-systems over approximations indexed below the cutoff, an elementary chart of the
problem posed in the proof of Stacks 07SU whose open part has a Noetherian approximation indexed
below the cutoff has a Noetherian approximation of `X` indexed below the cutoff. -/
theorem hasCutoffBoundedNoetherianApproximation_of_elementaryChart
    (hW : HasCutoffBoundedWSystems B hZ) (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (C : ElementaryChart X V)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (hVc : CompactSpace ((F).obj V)) (hVsep : Scheme.IsSeparated ((F).obj V))
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    (hU : IsOpenSubspace B (⊤_ Scheme.{u}) hZ C.U)
    (hUapprox : HasCutoffBoundedNoetherianApproximation B hZ C.U.toFunctor) :
    HasCutoffBoundedNoetherianApproximation B hZ X := by
  obtain ⟨A, hA, ⟨WS⟩⟩ := hW X V C hX hqc hqs hVc hVsep hsurj hU hUapprox
  obtain ⟨A', hA'⟩ := WS.exists_noetherianApproximation_card_le hX hsurj
  exact ⟨A', hA'.trans_lt (max_lt hA V.left.property)⟩

/-- Stacks 07SU over `Spec ℤ`, indexed below the cutoff, given the W-systems. Every
quasi-compact quasi-separated algebraic space over `Spec ℤ` has a Noetherian approximation whose
index set has fewer elements than the cutoff of the site, as soon as the W-systems of the proof
exist over approximations indexed below the cutoff
(`AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`). -/
theorem hasCutoffBoundedNoetherianApproximation_of_hasCutoffBoundedWSystems
    (hW : ElementaryChart.HasCutoffBoundedWSystems B hZ)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    HasCutoffBoundedNoetherianApproximation B hZ X :=
  induction_on_elementaryChart_strata (HasCutoffBoundedNoetherianApproximation B hZ)
    (fun h e ↦ h.ofIso e) (hasCutoffBoundedNoetherianApproximation_of_elementaryChart hW)
    hasCutoffBoundedNoetherianApproximation_sheafify_bot X hX hqc hqs

/-- Stacks 07SU over `Spec ℤ` with a system bounded by the cutoff, given the W-systems. Every
quasi-compact quasi-separated algebraic space `X` over `Spec ℤ` has a Noetherian approximation
whose system is bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`: fewer
stages than the cutoff and uniformly bounded base changes, with no condition on the cofinality of
the cutoff), as soon as the W-systems of the proof exist over approximations indexed below the
cutoff (`AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`). -/
theorem exists_isCutoffBounded_noetherianApproximation
    (hW : ElementaryChart.HasCutoffBoundedWSystems B hZ)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X, letI := A.preorder;
      IsCutoffBoundedSystem B (⊤_ Scheme.{u}) hZ A.diagram :=
  (hasCutoffBoundedNoetherianApproximation_of_hasCutoffBoundedWSystems hW X hX hqc hqs)
    |>.exists_isCutoffBoundedSystem

/-! ### The assembly of Stacks 0A0X from W-systems over bounded approximations -/

variable (hZ) in
/-- Stacks 0A0X under the cutoff bound, given the W-systems over approximations indexed below the
cutoff (`AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`) and the inputs
`h0A0W`, `h07SK` and `h08K1`: a proper morphism `f : X ⟶ Y` of algebraic spaces over `Spec ℤ`,
with `Y` quasi-compact and quasi-separated, is the limit of a directed system of proper morphisms
of finite presentation `X_i ⟶ Y_i` in descent situations, with each `Y_i` of finite presentation
over `Spec ℤ`. There is no bound on the index set of the conclusion. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedWSystems
    (hW : ElementaryChart.HasCutoffBoundedWSystems B hZ)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) := by
  obtain ⟨I, _, _, DX, DY, φ, eX, eY, h₁, h₂, h₃, -, -⟩ :=
    exists_descentSituation_arrow_of_convNoetherianApproximation hZ
      (fun D => IsCutoffBoundedSystem B _ hZ D) (fun _ => True)
      (exists_isCutoffBounded_noetherianApproximation hW)
      h0A0W h07SK h08K1
      (fun {_} _ _ _ _ hD {_ _} G hX => ⟨G.isLimit_imageCone_of_isCutoffBoundedSystem hX hD⟩)
      (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) hX hY f hf hYqc hYqs
  exact ⟨I, inferInstance, inferInstance, DX, DY, φ, eX, eY, h₁, h₂, h₃⟩

variable (hZ) in
/-- Stacks 0A0X over an affine target, given the W-systems over approximations indexed below the
cutoff (`AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`) and the inputs
`h0A0W`, `h07SK` and `h08K1`: a proper morphism `f' : X' ⟶ h_U` with `U` affine is the limit of
a directed system of proper morphisms of finite presentation `X_i ⟶ Y_i` in descent situations,
with each `Y_i` of finite presentation over `Spec ℤ` and both systems bounded by the cutoff. -/
theorem exists_descentSituation_arrow_isCutoffBoundedSystem_of_cutoffBoundedWSystems
    (hW : ElementaryChart.HasCutoffBoundedWSystems B hZ)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        IsCutoffBoundedSystem B _ hZ DX.system ∧ IsCutoffBoundedSystem B _ hZ DY.system := by
  intro U hU X' f' hf'
  have := hU
  exact exists_descentSituation_arrow_of_convNoetherianApproximation hZ
    (fun D => IsCutoffBoundedSystem B _ hZ D) (fun D => IsCutoffBoundedSystem B _ hZ D)
    (exists_isCutoffBounded_noetherianApproximation hW)
    h0A0W h07SK h08K1
    (fun {_} _ _ _ _ hD {_ _} G hX => ⟨G.isLimit_imageCone_of_isCutoffBoundedSystem hX hD⟩)
    (fun {_} _ _ D i₁ hD => isCutoffBoundedSystem_tail B _ hZ D i₁ hD)
    (fun {_} _ _ _ _ {_ _} G hD => G.isCutoffBoundedSystem_imageSystem_tail hD)
    X'.2 (isAlgebraicSpace_yoneda B _ hZ U) f'.hom hf'
    (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ U hU)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ (yoneda.obj U) hZ
      ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩)

end AlgebraicGeometry.Space

end
