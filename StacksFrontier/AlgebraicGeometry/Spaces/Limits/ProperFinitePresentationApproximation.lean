module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperClosedSubspaceStage
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# A proper morphism as a limit of proper morphisms of finite presentation

**Stacks 0A0W.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y`
quasi-compact and quasi-separated. Then `X = lim X_i` is a directed limit of algebraic spaces
`X_i` proper and of finite presentation over `Y`, with closed immersions as transition morphisms
and as morphisms `X ⟶ X_i`.

The source proves this from Proposition 0873 (a closed immersion `X ⟶ X'` into a separated
algebraic space of finite presentation over `Y`) and Lemma 0A0U (the closed subspace `X ⊆ X'`
is a directed limit of closed subspaces `X_i ⊆ X'` of finite presentation), and then shows that
`X_i ⟶ Y` is proper for `i` large. That last claim is
`AlgebraicGeometry.Space.exists_forall_ge_isProper_closedSubspace_comp`, proved here from the
library without hypotheses.

This file assembles the tag from the two inputs. Proposition 0873 and Lemma 0A0U are not
proved here, so both enter the assembly below as hypotheses:
`h0873` is the conclusion of Proposition 0873 for `f`, and `h0A0U` is Lemma 0A0U in the form
`AlgebraicGeometry.Space.exists_isLimit_closedSubspaces_of_isClosedImmersion` states it. The tag is
registered once both are theorems.

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_of_factorization`: the
  conclusion of Stacks 0A0W for `f`, from the conclusions of Stacks 0873 and 0A0U.

## References

* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The proof of Stacks 0A0W, from Stacks 0873 and Stacks 0A0U.** Let `f : X ⟶ Y` be a proper
morphism of algebraic spaces over `S` with `Y` quasi-compact and quasi-separated. Suppose given
`h0873`, a closed immersion `i : X ⟶ X'` over `Y` into an algebraic space `X'` separated and of
finite presentation over `Y` (the conclusion of Stacks 0873 for `f`), and `h0A0U`, Stacks 0A0U.
Then `X` is the limit of a directed inverse system of algebraic spaces `X_i` over `Y`, each proper
and of finite presentation over `Y`, whose transition morphisms and whose projections `X ⟶ X_i` are
closed immersions.

The proof is the source's. Stacks 0A0U writes `X = lim X_i` with `X_i ⊆ X'` closed subspaces of
finite presentation; `X_i ⟶ Y` is proper for `i` large by
`AlgebraicGeometry.Space.exists_forall_ge_isProper_closedSubspace_comp`; the system is restricted
to those `i`, which form a cofinal subset, and `X_i ⟶ Y` is of finite presentation as the
composite of `X_i ⟶ X'` and `X' ⟶ Y` (Stacks 03XQ). -/
theorem exists_isLimit_isProper_isFinitePresentation_of_factorization
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h0873 : ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f)
    (h0A0U : ∀ (Y : AlgebraicSpaces B S hS), IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X → ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B S hS f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
          ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
        (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f)))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
      (∀ i, IsProper B S hS (t.app i) ∧ IsFinitePresentation B S hS (t.app i)) ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B S hS (D.map e)) ∧
      (∀ i, IsClosedImmersion B S hS (π.app i)) ∧
      π ≫ t = (Functor.const Iᵒᵖ).map f ∧
      Nonempty (IsLimit (Cone.mk X π)) := by
  classical
  obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hif⟩ := h0873
  have hX'qc : IsQuasiCompactSpace B S hS X' :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS f' hY hYqc hf'fp
  have hX'qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X' :=
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS B.contains_terminal hX' hYqs hf'fp
  obtain ⟨I, _, _, _, Zc, hanti, hle, -, hfp, hπ, ⟨hlim⟩⟩ := h0A0U ⟨X', hX'⟩ hX'qc hX'qs hX i hi
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  -- The closed subspace `X ⊆ X'`.
  let C : ClosedSubspaces B S hS X' :=
    ⟨Subfunctor.range i, isClosedSubspace_range_of_isClosedImmersion B S hS i hX hi⟩
  have hιC : C.1.ι = inv (Subfunctor.toRange i) ≫ i := by
    rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
  -- The intersection of the stages is `X`.
  have hinf : (⨅ k, (Zc k).1) ≤ C.1 := by
    obtain ⟨k₀⟩ := (inferInstance : Nonempty I)
    let c := closedSubspaceCone B S hS (fun k => (Zc k).1) hanti (⨅ k, (Zc k).1)
      (fun k => iInf_le _ k)
    intro U x hx
    change x ∈ Set.range (i.app U)
    let y : (⨅ k, (Zc k).1).toFunctor.obj U := ⟨x, hx⟩
    refine ⟨(hlim.lift c).app U y, ?_⟩
    have h := congrArg (fun m => (m ≫ (Zc k₀).1.ι).app U y) (hlim.fac c (op k₀))
    simp only [Category.assoc, hπ k₀] at h
    exact h
  have hCp : IsProper B S hS (C.1.ι ≫ f') := by
    rw [hιC, Category.assoc, hif]
    exact (isProper_isIso_comp_iff B S hS _ _).2 hf
  -- Properness of the late stages.
  obtain ⟨k₀, hk₀⟩ := exists_forall_ge_isProper_closedSubspace_comp B S hS hY hYqc hX' f'
    hf'sep (isFiniteType_of_isFinitePresentation B S hS hf'fp) Zc hanti C hle hinf hCp
  -- The tail of the system beyond `k₀`.
  let J := {k : I // k₀ ≤ k}
  have : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  have : Nonempty J := ⟨⟨k₀, le_rfl⟩⟩
  let ZJ : J → Subfunctor X' := fun k => (Zc k.1).1
  have hZJ : ∀ ⦃a b : J⦄, a ≤ b → ZJ b ≤ ZJ a := fun a b h => hanti h
  have hleJ : ∀ k : J, C.1 ≤ ZJ k := fun k => hle k.1
  have hinfJ : (⨅ k, ZJ k) ≤ C.1 := by
    refine le_trans (le_iInf fun a => ?_) hinf
    obtain ⟨c, hac, hk₀c⟩ := directed_of (· ≤ ·) a k₀
    exact (iInf_le ZJ ⟨c, hk₀c⟩).trans (hanti hac)
  let D := closedSubspaceDiagram B S hS ZJ hZJ
  let c₀ := closedSubspaceCone B S hS ZJ hZJ C.1 hleJ
  let c := c₀.extend (Subfunctor.toRange i)
  have hc : IsLimit c :=
    IsLimit.ofIsoLimit (isLimitClosedSubspaceCone B S hS ⟨k₀, le_rfl⟩ ZJ hZJ C.1 hleJ hinfJ)
      (Cone.extendIso c₀ (asIso (Subfunctor.toRange i)).symm)
  let t : D ⟶ (Functor.const Jᵒᵖ).obj Y :=
    { app := fun k => (ZJ k.unop).ι ≫ f'
      naturality := fun a b e => by
        simp [D, closedSubspaceDiagram] }
  have hπt : c.π ≫ t = (Functor.const Jᵒᵖ).map f := by
    ext k : 2
    simp only [c, c₀, t, closedSubspaceCone, ← hif]
    simp only [NatTrans.comp_app, Cone.extend_π, Functor.const_map_app]
    change Subfunctor.toRange i ≫ Subfunctor.homOfLe (hleJ k.unop) ≫ (ZJ k.unop).ι ≫ f' =
      i ≫ f'
    rw [Subfunctor.homOfLe_ι_assoc, ← Category.assoc, Subfunctor.toRange_ι]
  refine ⟨J, inferInstance, inferInstance, inferInstance, D, t, c.π, fun k => (Zc k.unop.1).2.1,
    fun k => ⟨hk₀ k.unop.1 k.unop.2, ?_⟩,
    fun a b e => isClosedImmersion_closedSubspaceDiagram_map B S hS (fun k => Zc k.1) hZJ e,
    fun k => ?_, hπt, ⟨hc⟩⟩
  · exact isFinitePresentation_comp B S hS (Zc k.unop.1).2.1 hX' hY _ _ (hfp k.unop.1).2 hf'fp
  · change IsClosedImmersion B S hS (Subfunctor.toRange i ≫ Subfunctor.homOfLe (hleJ k.unop))
    exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
      (isClosedImmersion_homOfLe B S hS C (hleJ k.unop))

end AlgebraicGeometry.Space

end
