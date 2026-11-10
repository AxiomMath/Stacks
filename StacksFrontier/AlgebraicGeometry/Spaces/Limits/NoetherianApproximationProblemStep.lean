module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleSystemLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RepresentableEtaleModel
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpensSiteSquares

/-!
# The problem step of absolute Noetherian approximation

Let `X` be a quasi-separated algebraic space over `Spec ℤ`, `U ⊆ X` an open subspace with a
presented Noetherian approximation, and `f : V ⟶ X` a surjective étale morphism from a
quasi-compact separated scheme which is an isomorphism over the complement of `U`. Then `X` has
a presented Noetherian approximation. This is the step of the proof of Stacks 07SU which the
induction over the filtration of Stacks 07ST repeats: the inverse image `W ⊆ V` of `U` descends to
a system of étale schemes `W_i ⟶ U_i`, which by Stacks 07RN extends to a system of schemes
`V_i ⊇ W_i` of finite type over `Spec ℤ` with limit `V`; the quotients
`X_i = V_i / (V_i ⊔_{W_i} W_i ×_{U_i} W_i)` approximate `X`.

## Main results

* `AlgebraicGeometry.Space.isPullback_π_of_isLimit_of_isPullback`: in a cofiltered system of
  cartesian squares, the limit of the subsystem is the base change of every stage.
* `AlgebraicGeometry.Space.locallyOfFinitePresentation_of_isLocallyOfFinitePresentation`: an
  object of the site of `Spec ℤ` locally of finite presentation as an algebraic space is so as a
  scheme.
* `AlgebraicGeometry.Space.nonempty_presentedNoetherianApproximation_of_isOpenSubspace`: the
  problem step.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

section Cartesian

variable {C : Type*} [Category* C] [HasPullbacks C] {J : Type u} [Category.{u} J]
  [IsCofiltered J] {A O : J ⥤ C} (ι : O ⟶ A)
  (hι : ∀ {i j : J} (f : i ⟶ j), IsPullback (O.map f) (ι.app i) (ι.app j) (A.map f))

include hι in
/-- **The limit of a cartesian subsystem is the base change of every stage.** Let `O ⟶ A` be a
morphism of cofiltered systems which is cartesian over every transition morphism, with limits
`cO` and `cA`, and `u : cO.pt ⟶ cA.pt` compatible with the projections. Then `cO.pt` is the base
change of `O i ⟶ A i` along the projection `cA.pt ⟶ A i`. -/
theorem isPullback_π_of_isLimit_of_isPullback {cA : Cone A} (hcA : IsLimit cA) {cO : Cone O}
    (hcO : IsLimit cO) (u : cO.pt ⟶ cA.pt) (hu : ∀ i, u ≫ cA.π.app i = cO.π.app i ≫ ι.app i)
    (i : J) : IsPullback (cO.π.app i) u (ι.app i) (cA.π.app i) := by
  let lift : ∀ j : Over i, pullback (cA.π.app i) (ι.app i) ⟶ O.obj j.left := fun j =>
    (hι j.hom).lift (pullback.snd _ _) (pullback.fst _ _ ≫ cA.π.app j.left) (by
      rw [Category.assoc, cA.w, pullback.condition])
  have lift_fst : ∀ j : Over i, lift j ≫ O.map j.hom = pullback.snd _ _ := fun j =>
    (hι j.hom).lift_fst _ _ _
  have lift_snd : ∀ j : Over i, lift j ≫ ι.app j.left = pullback.fst _ _ ≫ cA.π.app j.left :=
    fun j => (hι j.hom).lift_snd _ _ _
  let c : Cone (Over.forget i ⋙ O) :=
    { pt := pullback (cA.π.app i) (ι.app i)
      π :=
        { app := lift
          naturality := fun j k e => by
            refine (Category.id_comp _).trans ((hι k.hom).hom_ext ?_ ?_).symm
            · change (lift j ≫ O.map e.left) ≫ O.map k.hom = lift k ≫ O.map k.hom
              rw [Category.assoc, ← O.map_comp, Over.w e, lift_fst, lift_fst]
            · change (lift j ≫ O.map e.left) ≫ ι.app k.left = lift k ≫ ι.app k.left
              rw [Category.assoc, ι.naturality, ← Category.assoc, lift_snd, lift_snd,
                Category.assoc, cA.w] } }
  have hc : IsLimit c := isLimitOfCartesianCone A cA hcA i (O.obj i) (ι.app i)
    (Over.forget i ⋙ O) c (Functor.whiskerLeft (Over.forget i) ι)
    { app := fun j => O.map j.hom
      naturality := fun j k e => by
        change O.map e.left ≫ O.map k.hom = O.map j.hom ≫ 𝟙 _
        rw [← O.map_comp, Over.w e, Category.comp_id] }
    (fun j => (hι j.hom).flip) (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) lift_snd lift_fst
  have hcO' : IsLimit (cO.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) cO).symm hcO
  have hcA' : IsLimit (cA.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) cA).symm hcA
  let e := hc.conePointUniqueUpToIso hcO'
  have he : ∀ j : Over i, e.hom ≫ cO.π.app j.left = lift j := fun j =>
    IsLimit.conePointUniqueUpToIso_hom_comp hc hcO' j
  refine (IsPullback.of_hasPullback (cA.π.app i) (ι.app i)).flip.of_iso e (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id]
    refine Eq.symm ((he (Over.mk (𝟙 i))).trans ?_)
    simpa using lift_fst (Over.mk (𝟙 i))
  · rw [Iso.refl_hom, Category.comp_id]
    refine (hcA'.hom_ext fun j => ?_)
    change pullback.fst _ _ ≫ cA.π.app j.left = (e.hom ≫ u) ≫ cA.π.app j.left
    rw [Category.assoc, hu, ← Category.assoc, he, lift_snd]

end Cartesian

section Index

variable {α : Type u} [Preorder α]

/-- In a directed preorder, the elements above `a` form a directed preorder. -/
instance isDirected_Ici [IsDirected α (· ≤ ·)] (a : α) : IsDirected (Set.Ici a) (· ≤ ·) :=
  ⟨fun b c => by
    obtain ⟨d, hbd, hcd⟩ := directed_of (· ≤ ·) b.1 c.1
    exact ⟨⟨d, b.2.trans hbd⟩, hbd, hcd⟩⟩

/-- The slice of the opposite of a preorder over `j`, indexed by the order dual of the elements
above `j.unop`. -/
noncomputable def iciDualToOver (j : αᵒᵖ) : (Set.Ici j.unop)ᵒᵈ ⥤ Over j where
  obj b := Over.mk (homOfLE (OrderDual.ofDual b).2).op
  map {b c} h := Over.homMk (homOfLE (show ((OrderDual.ofDual c : Set.Ici j.unop) : α) ≤
    (OrderDual.ofDual b : Set.Ici j.unop) from leOfHom h)).op
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- For a directed preorder `α`, the functor `iciDualToOver j` is initial. -/
instance [IsDirected α (· ≤ ·)] (j : αᵒᵖ) : (iciDualToOver j).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun d => ⟨OrderDual.toDual ⟨d.left.unop, leOfHom d.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Over.OverMorphism.ext (Quiver.Hom.unop_inj (Subsingleton.elim _ _))⟩)

/-- The opposite of the elements above `a`, mapped to the order dual. -/
noncomputable def iciOpToDual (a : α) : (Set.Ici a)ᵒᵖ ⥤ αᵒᵈ where
  obj k := OrderDual.toDual k.unop.1
  map {k l} h := homOfLE (show (l.unop : α) ≤ k.unop from leOfHom h.unop)

/-- For a directed preorder `α`, the functor `iciOpToDual a` is initial. -/
instance [IsDirected α (· ≤ ·)] (a : α) : (iciOpToDual a).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun d => by
      obtain ⟨m, ham, hdm⟩ := directed_of (· ≤ ·) a (OrderDual.ofDual d)
      exact ⟨Opposite.op ⟨m, ham⟩, ⟨homOfLE hdm⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)

end Index

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "𝕋" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

/-- **An object of the site of `Spec ℤ` which is locally of finite presentation over `Spec ℤ` as
an algebraic space is locally of finite presentation over `Spec ℤ` as a scheme.** -/
theorem locallyOfFinitePresentation_of_isLocallyOfFinitePresentation
    (Y : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hY : IsLocallyOfFinitePresentation B _ hZ (terminal.from (yoneda.obj Y))) :
    LocallyOfFinitePresentation (terminal.from ((𝕋).obj Y)) := by
  have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h := hY Y (BigFppfOver.terminalObj B (⊤_ Scheme.{u}) hZ) (𝟙 _)
    (terminalPresheafIso B hZ).hom
    ((Over.mkIdTerminal (X := B.obj hZ)).from Y) (presheaf_inverseImage_of_isIso' B hZ _ _)
    (presheaf_inverseImage_of_isIso' B hZ _ _) (terminal.hom_ext _ _)
  have e : (𝕋).map ((Over.mkIdTerminal (X := B.obj hZ)).from Y) = terminal.from ((𝕋).obj Y) :=
    terminal.hom_ext _ _
  rw [e] at h
  exact h

/-- A system of quasi-compact schemes locally of finite type over `Spec ℤ`, as a system of objects
of the site of `Spec ℤ`. -/
noncomputable abbrev siteSystemOfLocallyOfFiniteType {K : Type*} [Category* K]
    (F : K ⥤ Scheme.{u}) [∀ k, LocallyOfFiniteType (terminal.from (F.obj k))]
    [∀ k, CompactSpace (F.obj k)] : K ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ where
  obj k := siteObjectOfLocallyOfFiniteType (BigFppfOver.terminalObj B (⊤_ Scheme.{u}) hZ)
    (terminal.from (F.obj k))
  map {k l} g := siteObjectOfLocallyOfFiniteType.lift _ _ (F.map g) (terminal.hom_ext _ _)
  map_id k := (BigFppfOver.toScheme B _ hZ).map_injective (by
    change F.map (𝟙 k) = 𝟙 (F.obj k)
    exact F.map_id k)
  map_comp g g' := (BigFppfOver.toScheme B _ hZ).map_injective (by
    change F.map (g ≫ g') = F.map g ≫ F.map g'
    exact F.map_comp g g')

/-- The morphism of schemes underlying `(siteSystemOfLocallyOfFiniteType F).map g` is
`F.map g`. -/
theorem toScheme_map_siteSystemOfLocallyOfFiniteType {K : Type*} [Category* K]
    (F : K ⥤ Scheme.{u}) [∀ k, LocallyOfFiniteType (terminal.from (F.obj k))]
    [∀ k, CompactSpace (F.obj k)] {k l : K} (g : k ⟶ l) :
    (𝕋).map ((siteSystemOfLocallyOfFiniteType (hZ := hZ) F).map g) = F.map g := rfl

section Step

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

/-- **The problem step of absolute Noetherian approximation** (Stacks 07SU). Let `X` be a
quasi-separated algebraic space over `Spec ℤ`, `U ⊆ X` an open subspace with a presented
Noetherian approximation, and `f : V ⟶ X` a surjective étale morphism from a quasi-compact
separated scheme which is an isomorphism over a subspace `T` containing the points outside `U`.
Then `X` has a presented Noetherian approximation. -/
theorem nonempty_presentedNoetherianApproximation_of_isOpenSubspace
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B _ hZ X)
    (hXqs : IsAbsolutelyQuasiSeparated B _ hZ hZ X) {Uo : Subfunctor X}
    (hUo : IsOpenSubspace B _ hZ Uo) (AU : PresentedNoetherianApproximation B hZ Uo.toFunctor)
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} [CompactSpace ((𝕋).obj V)]
    [Scheme.IsSeparated ((𝕋).obj V)] (f : yoneda.obj V ⟶ X)
    (hf_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf f)
    (hf_et : IsEtale B _ hZ f) (Tc : Subfunctor X)
    (hT : ∀ x, x ∉ Set.range (pointsMap B _ hZ Uo.toFunctor Uo.ι) →
      x ∈ Set.range (pointsMap B _ hZ Tc.toFunctor Tc.ι))
    (hiso : IsIso (pullback.fst Tc.ι f)) :
    Nonempty (PresentedNoetherianApproximation B hZ X) := by
  classical
  let P := AU.presentation
  have hTerm := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
  have : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  -- the limit atlas of `U` is quasi-compact and quasi-separated
  have : ∀ i, CompactSpace ((P.atlas ⋙ 𝕋).obj i) := fun i =>
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ (P.isQuasiCompactSpace_atlas i)
  have : ∀ {i i' : AU.Iᵒᵖ} (e : i ⟶ i'),
      _root_.AlgebraicGeometry.IsAffineHom ((P.atlas ⋙ 𝕋).map e) :=
    fun e => P.isAffineHom_atlas e
  have : CompactSpace ((𝕋).obj P.atlasCone.pt) :=
    Scheme.compactSpace_of_isLimit (P.atlas ⋙ 𝕋) _ P.isLimit_atlasCone
  have : QuasiSeparatedSpace ((𝕋).obj P.atlasCone.pt) := by
    have j₀ : AU.Iᵒᵖ := Classical.arbitrary _
    have : _root_.AlgebraicGeometry.IsAffineHom ((𝕋).map (P.atlasCone.π.app j₀)) :=
      isAffineHom_π_app (P.atlas ⋙ 𝕋) _ P.isLimit_atlasCone j₀
    have := P.quasiSeparatedSpace_atlas j₀
    exact quasiSeparatedSpace_of_quasiSeparated ((𝕋).map (P.atlasCone.π.app j₀))
  have hUqc : IsQuasiCompactSpace B _ hZ Uo.toFunctor :=
    ⟨_, P.limitAtlas, inferInstance, P.surjective_limitAtlas,
      (isEtale_iff_presheaf_of_yoneda B _ hZ _).mpr P.etale_limitAtlas⟩
  have hUqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Uo.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hUo.1 hXqs
      (isQuasiSeparated_of_mono B _ hZ Uo.ι inferInstance)
  -- the inverse image `W ⊆ V` of `U`
  let rU := hUo.2.rep
  let W := rU.pullback f
  let jW : W ⟶ V := rU.snd f
  let wU : yoneda.obj W ⟶ Uo.toFunctor := rU.fst f
  have hW : IsPullback (yoneda.map jW) wU f Uo.ι := (rU.isPullback f).flip
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map jW) := hUo.2.property_snd f
  have : Scheme.IsSeparated ((𝕋).obj W) := by
    refine ⟨?_⟩
    have h : terminal.from ((𝕋).obj W) = (𝕋).map jW ≫ terminal.from _ := terminal.hom_ext _ _
    rw [h]
    infer_instance
  have hf_qc := isQuasiCompact_of_isQuasiCompactSpace B _ hZ hZ hX hXqs
    (isQuasiCompact_yoneda_of_compact B _ hZ V inferInstance) f
  have : CompactSpace ((𝕋).obj W) := compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ
    (isQuasiCompactSpace_of_iso B _ hZ (rU.isPullback f).isoPullback.symm
      (hf_qc _ hUo.1 hUqc Uo.ι))
  -- its base change `W'` to the limit atlas of `U`
  have hwU_et :=
    presheaf_of_isPullback B _ hZ hW ((isEtale_iff_presheaf_of_yoneda B _ hZ f).mp hf_et)
  let rW : yoneda.relativelyRepresentable wU := hUo.1.diagonal_representable.of_diag wU
  let w' : rW.pullback P.limitAtlas ⟶ P.atlasCone.pt := rW.snd P.limitAtlas
  have hg : IsPullback (rW.fst P.limitAtlas) (yoneda.map w') wU P.limitAtlas :=
    rW.isPullback P.limitAtlas
  have het : Etale ((𝕋).map w') :=
    (presheaf_yoneda_map_etale_iff B _ hZ w').mp (presheaf_of_isPullback B _ hZ hg hwU_et)
  have hWqs : IsAbsolutelyQuasiSeparated B _ hZ hZ (yoneda.obj W) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ _ hZ
      ⟨W, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩
  have hqs : QuasiSeparated ((𝕋).map w') := (isQuasiSeparated_yoneda_map_iff B _ hZ w').mp
    (isQuasiSeparated_of_isPullback B _ hZ hg
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ
        (isAlgebraicSpace_yoneda B _ hZ W) hWqs wU))
  have : CompactSpace ((𝕋).obj (rW.pullback P.limitAtlas)) := by
    obtain ⟨W'', hW'', ⟨e⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B _ hZ hZ _
      hUo.1).mp hUqs _ _ wU P.limitAtlas inferInstance inferInstance
    let e' : W'' ≅ rW.pullback P.limitAtlas :=
      Yoneda.fullyFaithful.preimageIso (e ≪≫ hg.isoPullback.symm)
    exact Function.Surjective.compactSpace ((𝕋).map e'.hom).continuous
      (fun x => ⟨((𝕋).map e'.inv).base x, by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, e'.inv_hom_id,
          CategoryTheory.Functor.map_id]
        rfl⟩)
  have hqc : QuasiCompact ((𝕋).map w') := inferInstance
  -- the system of étale schemes over the stages of `U` with limit `W`
  obtain ⟨j, Ys, πY, ys, ⟨hlimY⟩, hys_et, hYpb, hYcart, hYc⟩ :=
    P.exists_representable_etale_system AU.isLimit AU.isAlgebraicSpace hUo.1
      AU.toNoetherianApproximation.isLocallyOfFinitePresentation_obj wU w' _ hg het hqc hqs
  -- the system as a system of schemes indexed by a preorder
  let Φ := iciDualToOver j
  let D₀ : (Set.Ici j.unop)ᵒᵈ ⥤ Scheme.{u} := Φ ⋙ Ys ⋙ 𝕋
  have : ∀ {a b : (Set.Ici j.unop)ᵒᵈ} (v : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom (D₀.map v) := fun {a b} v => by
    have h := isAffineHom_of_isPullback' B _ hZ (hYcart (Φ.map v)).flip
      (AU.isAffineHom_map (Φ.map v).left)
    have h' := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B _ hZ
      (isAlgebraicSpace_yoneda B _ hZ _) (isAlgebraicSpace_yoneda B _ hZ _) h).2
    exact (presheaf_yoneda_map_iff B _ hZ inferInstance _).mp h'
  have : ∀ a, LocallyOfFiniteType (terminal.from (D₀.obj a)) := fun a => by
    have h : terminal.from (yoneda.obj (Ys.obj (Φ.obj a))) =
        ys.app (Φ.obj a) ≫ terminal.from (AU.diagram.obj (Φ.obj a).left) := terminal.hom_ext _ _
    have := locallyOfFinitePresentation_of_isLocallyOfFinitePresentation (Ys.obj (Φ.obj a))
      (by
        rw [h]
        exact isLocallyOfFinitePresentation_comp B _ hZ (isAlgebraicSpace_yoneda B _ hZ _)
          (AU.isAlgebraicSpace _) hTerm _ _
          (isLocallyOfFinitePresentation_of_isEtale B _ hZ (hys_et _))
          (AU.toNoetherianApproximation.isLocallyOfFinitePresentation_obj _))
    change LocallyOfFiniteType (terminal.from ((𝕋).obj (Ys.obj (Φ.obj a))))
    infer_instance
  have : ∀ a, CompactSpace (D₀.obj a) := fun a => hYc (Φ.obj a)
  have : ∀ a, QuasiCompact (terminal.from (D₀.obj a)) := fun a => inferInstance
  let Uop : ((𝕋).obj V).Opens := ((𝕋).map jW).opensRange
  let eW := ((𝕋).map jW).isoOpensRange
  have : CompactSpace (Uop : Scheme.{u}) :=
    Function.Surjective.compactSpace eW.hom.continuous (fun x => ⟨eW.inv.base x, by
      rw [← Scheme.Hom.comp_apply, eW.inv_hom_id]
      rfl⟩)
  have : QuasiSeparatedSpace ((𝕋).obj V) := inferInstance
  let p₀ : (Functor.const _).obj (Uop : Scheme.{u}) ⟶ D₀ :=
    { app := fun a => eW.inv ≫ (𝕋).map (πY.app (Φ.obj a))
      naturality := fun a b v => by
        change 𝟙 _ ≫ eW.inv ≫ (𝕋).map (πY.app (Φ.obj b)) =
          (eW.inv ≫ (𝕋).map (πY.app (Φ.obj a))) ≫ (𝕋).map (Ys.map (Φ.map v))
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp, ← πY.naturality,
          Functor.const_obj_map]
        exact congrArg (eW.inv ≫ ·) (congrArg (𝕋).map (Category.id_comp _).symm) }
  have hp₀ : IsLimit (Cone.mk (Uop : Scheme.{u}) p₀) :=
    ((Functor.Initial.isLimitWhiskerEquiv Φ _).symm hlimY).ofIsoLimit
      (Cone.ext eW (fun a => by
        change (𝕋).map (πY.app (Φ.obj a)) = eW.hom ≫ eW.inv ≫ (𝕋).map (πY.app (Φ.obj a))
        rw [Iso.hom_inv_id_assoc]))
  -- Stacks 07RN: the system extends to a system approximating `V`
  let FA := (exists_finiteTypeApproximation D₀ ((𝕋).obj V) Uop p₀ hp₀).some
  let := FA.indexPreorder
  have := FA.indexNonempty
  have := FA.indexDirected
  obtain ⟨i₀⟩ := FA.indexNonempty
  let K := Set.Ici i₀
  let ι₀ := iciOpToDual i₀
  let ρ : Kᵒᵖ ⥤ Over j := ι₀ ⋙ FA.index.monotone.dual.functor ⋙ Φ
  have : ∀ k : Kᵒᵖ, LocallyOfFiniteType (terminal.from ((ι₀ ⋙ FA.ambient).obj k)) :=
    fun k => FA.locallyOfFiniteType _
  have : ∀ k : Kᵒᵖ, CompactSpace ((ι₀ ⋙ FA.ambient).obj k) := fun k => by
    have := FA.quasiCompact (ι₀.obj k)
    exact QuasiCompact.compactSpace_of_compactSpace (terminal.from (FA.ambient.obj (ι₀.obj k)))
  let T₀ := BigFppfOver.terminalObj B (⊤_ Scheme.{u}) hZ
  let Vs : Kᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    siteSystemOfLocallyOfFiniteType (ι₀ ⋙ FA.ambient)
  let jmap : ∀ k : Kᵒᵖ, (ρ ⋙ Ys).obj k ⟶ Vs.obj k := fun k =>
    siteObjectOfLocallyOfFiniteType.lift T₀ _
      (FA.comparison.inv.app (ι₀.obj k) ≫ FA.inclusion.app (ι₀.obj k)) (terminal.hom_ext _ _)
  have hjmap : ∀ k, (𝕋).map (jmap k) =
      FA.comparison.inv.app (ι₀.obj k) ≫ FA.inclusion.app (ι₀.obj k) := fun k => rfl
  have hjpb : ∀ {k l : Kᵒᵖ} (e : k ⟶ l), IsPullback ((𝕋).map ((ρ ⋙ Ys).map e))
      ((𝕋).map (jmap k)) ((𝕋).map (jmap l)) ((𝕋).map (Vs.map e)) := fun {k l} e => by
    rw [hjmap, hjmap]
    change IsPullback ((FA.index.monotone.dual.functor ⋙ D₀).map (ι₀.map e)) _ _
      (FA.ambient.map (ι₀.map e))
    refine (FA.transition_isPullback (ι₀.map e)).of_iso (FA.comparison.app _)
      (FA.comparison.app _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact FA.comparison.hom.naturality (ι₀.map e)
    · simp
    · simp
    · simp
  let G : GluedEtaleSystem B (⊤_ Scheme.{u}) hZ Kᵒᵖ :=
    { U := ρ ⋙ Over.forget j ⋙ AU.diagram
      isAlgebraicSpace_U := fun k => AU.isAlgebraicSpace _
      isAbsolutelyQuasiSeparated_U := fun k => AU.isAbsolutelyQuasiSeparated _
      V := Vs
      Y := ρ ⋙ Ys
      j :=
        { app := jmap
          naturality := fun k l e => (𝕋).map_injective (by
            rw [Functor.map_comp, Functor.map_comp, hjmap, hjmap]
            change (FA.index.monotone.dual.functor ⋙ D₀).map (ι₀.map e) ≫ _ =
              _ ≫ FA.ambient.map (ι₀.map e)
            rw [← Category.assoc, FA.comparison.inv.naturality, Category.assoc,
              FA.inclusion.naturality, Category.assoc]) }
      isOpenImmersion_j := fun k => by
        rw [hjmap]
        have := FA.inclusion_isOpenImmersion (ι₀.obj k)
        infer_instance
      y := Functor.whiskerLeft ρ ys
      isEtale_y := fun k => hys_et _
      isPullback_j := fun e => BigFppfOver.isPullback_of_toScheme B _ hZ (hjpb e)
      isPullback_y := fun e => hYcart (ρ.map e)
      compactSpace_V := fun k => inferInstanceAs (CompactSpace ((ι₀ ⋙ FA.ambient).obj k))
      compactSpace_Y := fun k => hYc _ }
  -- the limit data
  let rf : yoneda.relativelyRepresentable f := hX.diagonal_representable.of_diag f
  let D : GluedKernelDatum B (⊤_ Scheme.{u}) hZ :=
    { X := X
      isAlgebraicSpace_X := hX
      Uo := Uo
      isOpenSubspace := hUo
      V := V
      f := f
      isEtale_f := hf_et
      W := W
      jW := jW
      wU := wU
      isPullback_W := hW
      K := rf.pullback f
      k₁ := rf.fst' f
      k₂ := rf.snd f
      isPullback_K := rf.isPullback' f
      Q := rW.pullback wU
      q₁ := rW.fst' wU
      q₂ := rW.snd wU
      isPullback_Q := rW.isPullback' wU }
  let πVapp : ∀ k : Kᵒᵖ, V ⟶ Vs.obj k := fun k =>
    siteObjectOfLocallyOfFiniteType.lift T₀ _ (FA.ambientCone.app (ι₀.obj k))
      (terminal.hom_ext _ _)
  have hπVapp : ∀ k, (𝕋).map (πVapp k) = FA.ambientCone.app (ι₀.obj k) := fun k => rfl
  let πV : (Functor.const Kᵒᵖ).obj V ⟶ Vs :=
    { app := πVapp
      naturality := fun k l e => (𝕋).map_injective (by
        rw [Functor.map_comp, Functor.map_comp, hπVapp, hπVapp]
        exact FA.ambientCone.naturality (ι₀.map e)) }
  have hlimV : IsLimit ((𝕋).mapCone (Cone.mk V πV)) :=
    ((Functor.Initial.isLimitWhiskerEquiv ι₀ _).symm FA.ambientCone_isLimit).ofIsoLimit
      (Cone.ext (Iso.refl _) (fun k => (Category.id_comp _).symm))
  let πY' : (Functor.const Kᵒᵖ).obj W ⟶ ρ ⋙ Ys :=
    { app := fun k => πY.app (ρ.obj k)
      naturality := fun k l e => πY.naturality (ρ.map e) }
  let πU : (Functor.const Kᵒᵖ).obj Uo.toFunctor ⟶ ρ ⋙ Over.forget j ⋙ AU.diagram :=
    { app := fun k => AU.π.app (ρ.obj k).left
      naturality := fun k l e => AU.π.naturality (ρ.map e).left }
  -- the open part of the extended system is cartesian over the ambient part
  have hcart := isPullback_π_of_isLimit_of_isPullback FA.inclusion FA.transition_isPullback
    FA.ambientCone_isLimit FA.openCone_isLimit Uop.ι FA.inclusion_compatibility
  have hπYs : ∀ k : Kᵒᵖ, (𝕋).map (πY.app (ρ.obj k)) =
      eW.hom ≫ FA.openCone.app (ι₀.obj k) ≫ FA.comparison.hom.app (ι₀.obj k) := fun k => by
    rw [FA.comparison_compatibility]
    change _ = eW.hom ≫ eW.inv ≫ _
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hπYpb : ∀ k : Kᵒᵖ, IsPullback ((𝕋).map (πY.app (ρ.obj k))) ((𝕋).map jW)
      ((𝕋).map (jmap k)) ((𝕋).map (πV.app k)) := fun k => by
    rw [hjmap, hπVapp, hπYs]
    refine (hcart (ι₀.obj k)).of_iso eW.symm (FA.comparison.app _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp [eW, Scheme.Hom.isoOpensRange_inv_comp]
      rfl
    · simp
    · simp
  let L : GluedSystemLimit (B := B) (S := ⊤_ Scheme.{u}) (hS := hZ) Kᵒᵖ :=
    { G := G
      D := D
      πV := πV
      isLimit_V := hlimV
      πY := πY'
      πU := πU
      πY_j := fun k => (𝕋).map_injective (by
        rw [Functor.map_comp, Functor.map_comp]
        exact (hπYpb k).w)
      πY_y := fun k => (hYpb (ρ.obj k)).w
      isPullback_πY_j := fun k => BigFppfOver.isPullback_of_toScheme B _ hZ (hπYpb k)
      isPullback_πY_y := fun k => hYpb (ρ.obj k) }
  exact ⟨L.presentedNoetherianApproximation Tc hT hiso hf_surj
    (fun e => FA.transition_affine (ι₀.map e)) (fun k => FA.locallyOfFiniteType (ι₀.obj k))⟩

end Step

end AlgebraicGeometry.Space

end
