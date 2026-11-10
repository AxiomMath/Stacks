module

public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedFinitePresentationEmbedding
public import StacksCore.Tactic.StacksAttribute

/-!
# A proper morphism as a limit of proper morphisms of finite presentation

A proper morphism `f : X ⟶ S` onto a quasi-compact, quasi-separated scheme writes `X` as the
directed inverse limit of schemes proper and of finite presentation over `S`, with every
transition morphism and every projection `X ⟶ X_i` a closed immersion.

## Main results

* `AlgebraicGeometry.exists_isLimit_isProper_finitePresentation_isClosedImmersion`:
  **Stacks 09ZR**.
* `AlgebraicGeometry.exists_isClosedImmersion_isProper_finitePresentation`: the single-stage
  form, factoring `f` as a closed immersion followed by a proper morphism of finite
  presentation.

## Implementation notes

Finite presentation is `AlgebraicGeometry.FinitePresentation`, and finite type is
`LocallyOfFiniteType` together with `QuasiCompact`, as elsewhere in this development.

The Stacks proof factors `f` as a closed immersion into a separated morphism of finite
presentation `a : Y ⟶ S` ([Stacks, Tag 01ZJ]), takes a Chow modification `π : Y' ⟶ Y` immersed in
`ℙⁿ_S` ([Stacks, Tag 0202]), and writes the closed immersion `X ⟶ Y` as a limit of closed
immersions of finite presentation `X_i ⟶ Y` ([Stacks, Tag 09ZP]). Base changing that system along
`π` gives a system with limit `X ×_Y Y'`, whose morphism to `ℙⁿ_S` is proper, hence a closed
immersion; so the stages map to `ℙⁿ_S` by closed immersions for all sufficiently large indices
([Stacks, Tag 0A0N]), and over those indices `X_i ⟶ S` is proper by [Stacks, Tag 03GN] applied to
the surjection `X_i ×_Y Y' ⟶ X_i`.

The base change of the system is performed in `CategoryTheory.Over Y`, where
`CategoryTheory.Over.pullback` is a right adjoint and so preserves the limiting cone; the
forgetful functor to schemes preserves it because the index category is cofiltered.

## References

* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-- The source of a quasi-compact, quasi-separated morphism to a quasi-compact, quasi-separated
scheme is quasi-compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

/-- **Stacks 09ZR.** A proper morphism onto a quasi-compact, quasi-separated scheme is a directed
inverse limit, over that scheme, of proper morphisms of finite presentation whose transition
morphisms and limit projections are all closed immersions. -/
@[stacks 09ZR]
theorem exists_isLimit_isProper_finitePresentation_isClosedImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, IsProper (t.app i) ∧ FinitePresentation (t.app i)) ∧
        (∀ (i j : Iᵒᵖ) (g : i ⟶ j), IsClosedImmersion (D.map g)) ∧
        (∀ i, IsClosedImmersion (p.app i)) := by
  classical
  -- **Step 1** ([Stacks, Tag 01ZJ]): factor `f` as a closed immersion into a separated morphism
  -- of finite presentation.
  obtain ⟨Y, a, ι, hasep, hafp, hιcl, hιa⟩ :=
    exists_isClosedImmersion_into_isSeparated_finitePresentation f
  have : LocallyOfFinitePresentation a := hafp.1
  have : QuasiCompact a := hafp.2.1
  have : QuasiSeparated a := hafp.2.2
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom a
  -- **Step 2** ([Stacks, Tag 0202], Chow's lemma): a proper surjection onto `Y` immersed in a
  -- projective space over `S`.
  obtain ⟨n, Y', π, jY, hπ, hπsurj, hjY, hπa⟩ :=
    hasChowModification_of_finitePresentation_of_isOneAffineOpenStep
      Scheme.FiniteTypeApproximation.isOneAffineOpenStep a hafp
  -- **Step 3** ([Stacks, Tag 09ZP]): write `ι` as a limit of closed immersions of finite
  -- presentation into `Y`.
  obtain ⟨I, hIpre, hIne, hIdir, D, t, p, hc, hcompat, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation ι
  let _ : Preorder I := hIpre
  have : Nonempty I := hIne
  have : IsDirectedOrder I := ⟨fun x y => hIdir.directed x y⟩
  have hfac : ∀ x, p.app x ≫ t.app x = ι := fun x => by
    simpa using congrArg (fun η => η.app x) hcompat
  have htrans : ∀ {x y : Iᵒᵖ} (g : x ⟶ y), IsClosedImmersion (D.map g) := by
    intro x y g
    have : IsClosedImmersion (t.app y) := (hstage y).1
    have : IsClosedImmersion (D.map g ≫ t.app y) := by simpa using (hstage x).1
    exact IsClosedImmersion.of_comp (D.map g) (t.app y)
  have hproj : ∀ x, IsClosedImmersion (p.app x) := by
    intro x
    have : IsClosedImmersion (t.app x) := (hstage x).1
    have : IsClosedImmersion (p.app x ≫ t.app x) := hfac x ▸ hιcl
    exact IsClosedImmersion.of_comp (p.app x) (t.app x)
  -- **Step 4**: regard the system as a system over `Y` and base change it along `π`.
  let E : Iᵒᵖ ⥤ Over Y :=
    { obj := fun x => Over.mk (t.app x)
      map := fun {x y} g => Over.homMk (D.map g) (by simp)
      map_id := fun x => by ext; simp
      map_comp := fun g h => by ext; simp }
  let cE : Cone E :=
    { pt := Over.mk ι
      π :=
        { app := fun x => Over.homMk (p.app x) (hfac x)
          naturality := fun x y g => by ext; simpa [E] using p.naturality g } }
  have hliftfac : ∀ s : Cone E, hc.lift ((Over.forget Y).mapCone s) ≫ ι = s.pt.hom := by
    intro s
    obtain ⟨x⟩ : Nonempty Iᵒᵖ := inferInstance
    calc hc.lift ((Over.forget Y).mapCone s) ≫ ι
        = hc.lift ((Over.forget Y).mapCone s) ≫ p.app x ≫ t.app x := by rw [hfac x]
      _ = (s.π.app x).left ≫ t.app x := by
        rw [← Category.assoc, hc.fac ((Over.forget Y).mapCone s) x]; rfl
      _ = s.pt.hom := Over.w (s.π.app x)
  have hcE : IsLimit cE :=
    { lift := fun s => Over.homMk (hc.lift ((Over.forget Y).mapCone s)) (hliftfac s)
      fac := fun s x => by
        ext
        exact hc.fac ((Over.forget Y).mapCone s) x
      uniq := fun s m hm => by
        ext
        exact hc.uniq ((Over.forget Y).mapCone s) m.left fun x => by
          simpa [cE, E] using congrArg Over.Hom.left (hm x) }
  have : IsCofiltered Iᵒᵖ := inferInstance
  let E' : Iᵒᵖ ⥤ Over Y' := E ⋙ Over.pullback π
  let cE' : Cone E' := (Over.pullback π).mapCone cE
  have hcE' : IsLimit cE' := isLimitOfPreserves (Over.pullback π) hcE
  let D' : Iᵒᵖ ⥤ Scheme.{u} := E' ⋙ Over.forget Y'
  let c' : Cone D' := (Over.forget Y').mapCone cE'
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget Y') hcE'
  let t' : D' ⟶ (Functor.const Iᵒᵖ).obj (ProjectiveSpace n S) :=
    { app := fun x => (E'.obj x).hom ≫ jY
      naturality := fun x y g => by simp [D'] }
  let f' : c'.pt ⟶ ProjectiveSpace n S := cE'.pt.hom ≫ jY
  have hcomm' : c'.π ≫ t' = (Functor.const Iᵒᵖ).map f' := by
    ext x
    simp [c', t', f']
  -- **Step 5** ([Stacks, Tag 01W3] and [Stacks, Tag 01W6]): the morphism induced on the limit is
  -- proper over `S`, hence a closed immersion into the projective space.
  have hf'eq : f' = pullback.snd ι π ≫ jY := rfl
  have hfacf' : f' ≫ (ProjectiveSpace n S ↘ S) = pullback.fst ι π ≫ f := by
    rw [hf'eq, Category.assoc, ← hπa, ← Category.assoc, ← pullback.condition, Category.assoc,
      hιa]
  have : IsProper (pullback.fst ι π ≫ f) := inferInstance
  have : IsProper (f' ≫ (ProjectiveSpace n S ↘ S)) := by rw [hfacf']; infer_instance
  have : IsProper f' := IsProper.of_comp f' (ProjectiveSpace n S ↘ S)
  have : IsImmersion f' := by rw [hf'eq]; infer_instance
  have hf'closed : IsClosedImmersion f' :=
    IsClosedImmersion.of_isPreimmersion f' f'.isClosedMap.isClosed_range
  -- **Step 6** ([Stacks, Tag 0A0N]): the stages map to the projective space by closed immersions
  -- for all sufficiently large indices.
  have : QuasiSeparatedSpace (ProjectiveSpace n S) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace n S ↘ S)
  have hD : ∀ x : Iᵒᵖ, CompactSpace (D.obj x) ∧ QuasiSeparatedSpace (D.obj x) := fun x =>
    have : QuasiCompact (t.app x) := (hstage x).2.2.1
    have : QuasiSeparated (t.app x) := (hstage x).2.2.2
    compactSpace_and_quasiSeparatedSpace_of_hom (Y := Y) (t.app x)
  have hD' : ∀ i : I,
      CompactSpace (D'.obj (op i)) ∧ QuasiSeparatedSpace (D'.obj (op i)) := fun i =>
    have := (hD (op i)).1
    have := (hD (op i)).2
    compactSpace_and_quasiSeparatedSpace_of_hom (pullback.fst (t.app (op i)) π)
  have : ∀ i : I, CompactSpace (D'.obj (op i)) := fun i => (hD' i).1
  have : ∀ i : I, QuasiSeparatedSpace (D'.obj (op i)) := fun i => (hD' i).2
  have : ∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D'.map (homOfLE h).op) := fun _ _ h =>
    MorphismProperty.overPullbackMap π (E.map (homOfLE h).op) (htrans (homOfLE h).op)
  have ht'eq : ∀ x : Iᵒᵖ, t'.app x = pullback.snd (t.app x) π ≫ jY := fun _ => rfl
  have : ∀ i : I, LocallyOfFiniteType (t'.app (op i)) := by
    intro i
    have : IsClosedImmersion (t.app (op i)) := (hstage (op i)).1
    rw [ht'eq]
    infer_instance
  have hev : ∀ᶠ i in Filter.atTop, IsClosedImmersion (t'.app (op i)) :=
    eventually_isClosedImmersion D' t' c' hc' f' hcomm'
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hev
  -- **Step 7** ([Stacks, Tag 03GN]): restrict to the indices above `k`; there the stages are
  -- proper over `S`.
  let Tail := {x : I // k ≤ x}
  have : Nonempty Tail := ⟨⟨k, le_rfl⟩⟩
  have hTdir : IsDirected Tail (· ≤ ·) := ⟨fun x y ↦ by
    obtain ⟨z, hxz, hyz⟩ := hIdir.directed x.1 y.1
    obtain ⟨w, hzw, hkw⟩ := hIdir.directed z k
    exact ⟨⟨w, hkw⟩, hxz.trans hzw, hyz.trans hzw⟩⟩
  have : IsDirectedOrder Tail := ⟨fun x y => hTdir.directed x y⟩
  have hmono : Monotone (Subtype.val : Tail → I) := Subtype.mono_coe _
  have : hmono.functor.Final := by
    rw [Monotone.final_functor_iff hmono]
    intro x
    obtain ⟨y, hxy, hky⟩ := hIdir.directed x k
    exact ⟨⟨y, hky⟩, hxy⟩
  let FI : Tailᵒᵖ ⥤ Iᵒᵖ := hmono.functor.op
  have : FI.Initial := Functor.initial_op_of_final hmono.functor
  refine ⟨Tail, inferInstance, inferInstance, inferInstance, FI ⋙ D,
    Functor.whiskerLeft FI (t ≫ (Functor.const Iᵒᵖ).map a),
    (Cone.whisker FI (Cone.mk X p)).π,
    (Functor.Initial.isLimitWhiskerEquiv FI (Cone.mk X p)).symm hc, ?_, ?_, ?_, ?_⟩
  · ext x
    change p.app (FI.obj x) ≫ t.app (FI.obj x) ≫ a = f
    rw [← Category.assoc, hfac, hιa]
  · intro x
    change IsProper (t.app (FI.obj x) ≫ a) ∧ FinitePresentation (t.app (FI.obj x) ≫ a)
    have hxk : k ≤ x.unop.1 := x.unop.2
    have : IsClosedImmersion (t'.app (FI.obj x)) := hk x.unop.1 hxk
    have hfactor : pullback.fst (t.app (FI.obj x)) π ≫ (t.app (FI.obj x) ≫ a) =
        t'.app (FI.obj x) ≫ (ProjectiveSpace n S ↘ S) := by
      rw [ht'eq, Category.assoc, ← hπa, ← Category.assoc, pullback.condition, Category.assoc]
    have : IsClosedImmersion (t.app (FI.obj x)) := (hstage (FI.obj x)).1
    have : LocallyOfFinitePresentation (t.app (FI.obj x)) := (hstage (FI.obj x)).2.1
    have : QuasiCompact (t.app (FI.obj x)) := (hstage (FI.obj x)).2.2.1
    have : QuasiSeparated (t.app (FI.obj x)) := (hstage (FI.obj x)).2.2.2
    have : IsSeparated (t.app (FI.obj x) ≫ a) := inferInstance
    have : LocallyOfFinitePresentation (t.app (FI.obj x) ≫ a) :=
      locallyOfFinitePresentation_comp (t.app (FI.obj x)) a
    have : LocallyOfFiniteType (t.app (FI.obj x) ≫ a) := inferInstance
    have : Surjective (pullback.fst (t.app (FI.obj x)) π) := inferInstance
    have : UniversallyClosed (pullback.fst (t.app (FI.obj x)) π ≫ (t.app (FI.obj x) ≫ a)) := by
      rw [hfactor]
      infer_instance
    exact ⟨isProper_of_comp_surjective (pullback.fst (t.app (FI.obj x)) π)
        (t.app (FI.obj x) ≫ a),
      FinitePresentation.mk ‹_› inferInstance inferInstance⟩
  · exact fun x y g ↦ htrans (FI.map g)
  · exact fun x ↦ hproj (FI.obj x)

/-- A proper morphism onto a quasi-compact, quasi-separated scheme factors as a closed immersion
followed by a proper morphism of finite presentation. -/
theorem exists_isClosedImmersion_isProper_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ S) (ι : X ⟶ X') (_ : IsClosedImmersion ι),
      ι ≫ g = f ∧ IsProper g ∧ FinitePresentation g := by
  obtain ⟨I, _, _, _, D, t, p, _, hcompat, hstage, _, hproj⟩ :=
    exists_isLimit_isProper_finitePresentation_isClosedImmersion f
  obtain ⟨i⟩ : Nonempty Iᵒᵖ := inferInstance
  exact ⟨D.obj i, t.app i, p.app i, hproj i,
    by simpa using congrArg (fun η => η.app i) hcompat, (hstage i).1, (hstage i).2⟩

end AlgebraicGeometry

end
