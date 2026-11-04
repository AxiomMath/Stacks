module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRelativeLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# A finite cover of a closed subspace which extends to a finite cover of the ambient space

Let `C ⊆ X` be a closed subspace of a quasi-compact and quasi-separated algebraic space, and
`f : Y ⟶ C` a surjective finite morphism of finite presentation from a scheme which is finite
étale over an open subspace `U ⊆ C` with dense points. Suppose `Y ⟶ C ⟶ X` factors as a closed
immersion `Y ⟶ T` followed by a finite morphism of finite presentation `g : T ⟶ X` from a scheme.
Cutting `T` by a closed subscheme of finite presentation which meets `T ×_X C` exactly in `Y`
(`AlgebraicGeometry.Space.exists_isFinitePresentation_inf_le`) gives a finite morphism of finite
presentation `g' : T' ⟶ X` whose base change to `C` is `f`; it is therefore étale over an open set
of `|X|` meeting `|C|`, and its image contains `|C|`. These are the inputs of the induction step
`AlgebraicGeometry.Space.exists_isCoverStratified_of_spreadCover` of Stacks 0GUP.

## Main results

* `AlgebraicGeometry.Space.exists_isCoverStratified_of_closedImmersion`: the statement above.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category C] {A E F G : C ⥤ Type u}

/-- If `i ≫ g = f` and the range of `f` lies in `Z`, then the range of `i` lies in
`Z.preimage g`. -/
private theorem range_le_preimage_of_fac {i : A ⟶ F} {g : F ⟶ G} {f : A ⟶ G} {Z : Subfunctor G}
    (h : i ≫ g = f) (hf : range f ≤ Z) : range i ≤ Z.preimage g := by
  subst h
  rintro Q _ ⟨a, rfl⟩
  exact hf Q ⟨a, rfl⟩

/-- If `i ≫ g = f ≫ Z.ι`, then the range of `i` lies in `Z.preimage g`. -/
private theorem range_le_preimage_of_comp_eq {Z : Subfunctor G} {i : A ⟶ F} {g : F ⟶ G}
    {f : A ⟶ Z.toFunctor} (h : i ≫ g = f ≫ Z.ι) : range i ≤ Z.preimage g :=
  range_le_preimage_of_fac h (by rintro Q _ ⟨a, rfl⟩; exact (f.app Q a).2)

/-- If `i ≫ g = f ≫ Z.ι`, the lift of `i` to `Z.preimage g` followed by the projection to `Z`
is `f`. -/
private theorem lift_comp_fromPreimage {Z : Subfunctor G} {i : A ⟶ F} {g : F ⟶ G}
    {f : A ⟶ Z.toFunctor} (h : i ≫ g = f ≫ Z.ι) :
    lift i (range_le_preimage_of_comp_eq h) ≫ Z.fromPreimage g = f := by
  rw [← cancel_mono Z.ι, Category.assoc, fromPreimage_ι, ← Category.assoc, lift_ι, h]

/-- The lift of a monomorphism through a subfunctor contained in its range is an isomorphism. -/
private theorem isIso_lift_of_le (j : A ⟶ F) [hj : Mono j] {Z : Subfunctor F} (hle : range j ≤ Z)
    (hge : Z ≤ range j) : IsIso (lift j hle) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Q
  rw [isIso_iff_bijective]
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · exact (NatTrans.mono_iff_mono_app j |>.1 hj Q |> (mono_iff_injective _).1)
      (congrArg Subtype.val hab)
  · obtain ⟨a, ha⟩ := hge Q c.2
    exact ⟨a, Subtype.ext ha⟩

/-- If `i = i' ≫ s` with `s` and `i'` monomorphisms, the range of `i` lies in `D`, and the range
of `s` lies in `T` with `T ⊓ D ≤ range i`, then `i'` is the base change of `D.ι` along `s`. -/
private theorem isPullback_lift_of_inf_le {D T : Subfunctor F} {i : A ⟶ F} {s : E ⟶ F} {i' : A ⟶ E}
    [hs : Mono s] [Mono i'] (hi' : i' ≫ s = i) (hD : range i ≤ D) (hsT : range s ≤ T)
    (hTD : T ⊓ D ≤ range i) : IsPullback (lift i hD) i' D.ι s := by
  let k := lift i' (range_le_preimage_of_fac hi' hD)
  have hk : k ≫ (D.preimage s).ι = i' := lift_ι _ _
  have hiD : lift i hD ≫ D.ι = i := lift_ι _ _
  have : IsIso k := isIso_lift_of_le i' _ fun Q c hc => by
    obtain ⟨a, ha⟩ := hTD Q ⟨hsT Q ⟨c, rfl⟩, hc⟩
    refine ⟨a, (mono_iff_injective _).1 (NatTrans.mono_iff_mono_app _ |>.1 hs Q) ?_⟩
    have h := congrArg (fun φ => φ.app Q a) hi'
    simp only [NatTrans.comp_app, types_comp_apply] at h
    exact h.trans ha
  refine (isPullback_preimage s D).of_iso (asIso k).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
      ← cancel_mono D.ι, Category.assoc, fromPreimage_ι, ← Category.assoc, hk, hi', hiD]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, hk]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

attribute [local instance] pointTopology

/-- A closed immersion `i : Y ⟶ T` over a closed subspace `C` of `X`, with `Y ⟶ C` of finite
presentation, is of finite presentation as a closed subspace of `T ×_X C`. -/
private theorem isFinitePresentation_range_preimage_ι (hX : IsAlgebraicSpace B S hS X)
    {C₀ : Subfunctor X} (hC₀ : IsClosedSubspace B S hS C₀) {Y T : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ C₀.toFunctor} (hffp : IsFinitePresentation B S hS f)
    {g : yoneda.obj T ⟶ X} (hgfp : IsFinitePresentation B S hS g)
    {i : yoneda.obj Y ⟶ yoneda.obj T} (hi : IsClosedImmersion B S hS i)
    (hig : i ≫ g = f ≫ C₀.ι) :
    IsFinitePresentation B S hS ((Subfunctor.range i).preimage (C₀.preimage g).ι).ι := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hY := isAlgebraicSpace_yoneda B S hS Y
  let D : Subfunctor (yoneda.obj T) := C₀.preimage g
  have hD : IsClosedSubspace B S hS D := isClosedSubspace_preimage B S hS g C₀ hX hT hC₀
  let YP : Subfunctor (yoneda.obj T) := Subfunctor.range i
  have hYP : IsClosedSubspace B S hS YP :=
    isClosedSubspace_range_of_isClosedImmersion B S hS i hY hi
  show IsFinitePresentation B S hS (YP.preimage D.ι).ι
  have hYPD : YP ≤ D := Subfunctor.range_le_preimage_of_comp_eq hig
  have hmono_i : Mono i := mono_of_isClosedImmersion B S hS i hi
  let iD : yoneda.obj Y ⟶ D.toFunctor := Subfunctor.lift i hYPD
  have hiD : iD ≫ D.ι = i := Subfunctor.lift_ι _ _
  have hiDf : iD ≫ C₀.fromPreimage g = f := Subfunctor.lift_comp_fromPreimage hig
  have hmono_iD : Mono iD := mono_of_mono_fac hiD
  let k : yoneda.obj Y ⟶ (YP.preimage D.ι).toFunctor :=
    Subfunctor.lift iD (by rintro Q _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
  have hk : k ≫ (YP.preimage D.ι).ι = iD := Subfunctor.lift_ι _ _
  have hkiso : IsIso k :=
    Subfunctor.isIso_lift_of_le iD _ fun Q c ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩
  have hfpD : IsFinitePresentation B S hS (C₀.fromPreimage g) :=
    IsFinitePresentation.of_isPullback B S hS hD.1 hT hC₀.1 hX
      (Subfunctor.isPullback_preimage g C₀).flip hgfp
  have hYD' : IsClosedSubspace B S hS (YP.preimage D.ι) :=
    isClosedSubspace_preimage B S hS D.ι YP hT hD.1 hYP
  refine (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS hYD'.1 hD.1 hC₀.1 _
    (C₀.fromPreimage g) hYD'.2 hfpD).1 ?_
  rw [show (YP.preimage D.ι).ι ≫ C₀.fromPreimage g = inv k ≫ f by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hk, hiDf]]
  exact IsFinitePresentation.of_isPullback B S hS hYD'.1 hY hC₀.1 hC₀.1
    (IsPullback.of_horiz_isIso (fst := inv k) (snd := inv k ≫ f) (f := f) (g := 𝟙 _)
      ⟨by simp⟩) hffp

/-- **Cutting a finite cover of `X` down to a given closed piece over a closed subspace.** If a
closed immersion `i : Y ⟶ T` of schemes over `X` lands, over a closed subspace `C`, in `T ×_X C`
with `Y ⟶ C` of finite presentation, then some closed subscheme `T' ⊆ T` of finite presentation
contains `Y` and satisfies `T' ×_X C = Y`: the square `Y ⟶ T'`, `Y ⟶ C` is cartesian. -/
theorem exists_isPullback_closedImmersion_cut (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) {C₀ : Subfunctor X}
    (hC₀ : IsClosedSubspace B S hS C₀) {Y T : BigFppfOver B S hS}
    {f : yoneda.obj Y ⟶ C₀.toFunctor} (hffp : IsFinitePresentation B S hS f)
    {g : yoneda.obj T ⟶ X} (hgfp : IsFinitePresentation B S hS g)
    {i : yoneda.obj Y ⟶ yoneda.obj T} (hi : IsClosedImmersion B S hS i)
    (hig : i ≫ g = f ≫ C₀.ι) :
    ∃ (T' : BigFppfOver B S hS) (s : T' ⟶ T) (i' : yoneda.obj Y ⟶ yoneda.obj T'),
      IsClosedImmersion B S hS (yoneda.map s) ∧ IsFinitePresentation B S hS (yoneda.map s) ∧
      i' ≫ yoneda.map s = i ∧ IsPullback f i' C₀.ι (yoneda.map s ≫ g) := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  let P : AlgebraicSpaces B S hS := ⟨yoneda.obj T, hT⟩
  have hPqc : IsQuasiCompactSpace B S hS P.1 :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS g hX hXqc hgfp
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hT hXqs hgfp.2.2
  -- `D = T ×_X C` and `Y` inside it
  let D : Subfunctor P.1 := C₀.preimage g
  have hD : IsClosedSubspace B S hS D := isClosedSubspace_preimage B S hS g C₀ hX hT hC₀
  let YP : Subfunctor P.1 := Subfunctor.range i
  have hYP : IsClosedSubspace B S hS YP :=
    isClosedSubspace_range_of_isClosedImmersion B S hS i (isAlgebraicSpace_yoneda B S hS Y) hi
  have hYPD : YP ≤ D := Subfunctor.range_le_preimage_of_comp_eq hig
  have hmono_i : Mono i := mono_of_isClosedImmersion B S hS i hi
  -- `Y` as a subfunctor of `D`
  let iD : yoneda.obj Y ⟶ D.toFunctor := Subfunctor.lift i hYPD
  have hiDf : iD ≫ C₀.fromPreimage g = f := Subfunctor.lift_comp_fromPreimage hig
  -- cut `T` down
  obtain ⟨Ts, hTsfp, hYTs, hTsD⟩ := exists_isFinitePresentation_inf_le hZ P hPqc hPqs ⟨D, hD⟩
    ⟨YP, hYP⟩ hYPD (isFinitePresentation_range_preimage_ι hX hC₀ hffp hgfp hi hig)
  have hTrep := Ts.2.2.1
  let T' := hTrep.pullback (𝟙 (yoneda.obj T))
  let s' : T' ⟶ T := hTrep.snd (𝟙 _)
  let fs : yoneda.obj T' ⟶ Ts.1.toFunctor := hTrep.fst (𝟙 _)
  have sqTs : IsPullback fs (yoneda.map s') Ts.1.ι (𝟙 _) := hTrep.isPullback (𝟙 _)
  have hs'ci : IsClosedImmersion B S hS (yoneda.map s') := by
    have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.of_isPullback sqTs Ts.2.2
  have hs'fp : IsFinitePresentation B S hS (yoneda.map s') :=
    IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS T') Ts.2.1 hT hT
      sqTs hTsfp
  have hmono_s : Mono (yoneda.map s') := mono_of_isClosedImmersion B S hS _ hs'ci
  have hsTs : Subfunctor.range (yoneda.map s') ≤ Ts.1 :=
    Subfunctor.range_le_preimage_of_comp_eq (g := 𝟙 _) sqTs.w.symm
  let i' : yoneda.obj Y ⟶ yoneda.obj T' :=
    sqTs.lift (Subfunctor.lift i hYTs) i (by rw [Subfunctor.lift_ι, Category.comp_id])
  have hi' : i' ≫ yoneda.map s' = i := sqTs.lift_snd _ _ _
  have hmono_i' : Mono i' := mono_of_mono_fac hi'
  -- `Y` is `T' ×_T D`
  have sq2 : IsPullback iD i' D.ι (yoneda.map s') :=
    Subfunctor.isPullback_lift_of_inf_le hi' hYPD hsTs hTsD
  exact ⟨T', s', i', hs'ci, hs'fp, hi',
    hiDf ▸ sq2.paste_horiz (Subfunctor.isPullback_preimage g C₀)⟩

/-- **The induction step of Stacks 0GUP from a cover of the closed piece which extends.** Let
`C ⊆ X` be closed with all proper closed subsets of `|C|` in cover-stratified closed subspaces of
finite presentation, and let `f : Y ⟶ C` be surjective, finite and of finite presentation from a
scheme, étale over an open subspace `U` of `C` with dense points. If `Y ⟶ C ⟶ X` factors through a
closed immersion into a scheme finite and of finite presentation over `X`, then `|C|` lies in a
cover-stratified closed subspace of finite presentation. -/
theorem exists_isCoverStratified_of_closedImmersion (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) {C₀ : Subfunctor X}
    (hC₀ : IsClosedSubspace B S hS C₀)
    (hsmall : ∀ C' : Set (points B S hS X), IsClosed C' → C' ⊂ subspacePointSet B S hS X C₀ →
      ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
        IsCoverStratified B S hS W ∧ C' ⊆ subspacePointSet B S hS X W)
    (hne : (subspacePointSet B S hS X C₀).Nonempty)
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ C₀.toFunctor} {U : Subfunctor C₀.toFunctor}
    (hfs : IsSurjective B S hS f) (hffp : IsFinitePresentation B S hS f)
    (hU : IsOpenSubspace B S hS U) (hUd : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hUe : IsEtale B S hS (pullback.fst U.ι f))
    {T : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X} (hg : IsFinite B S hS g)
    (hgfp : IsFinitePresentation B S hS g) {i : yoneda.obj Y ⟶ yoneda.obj T}
    (hi : IsClosedImmersion B S hS i) (hig : i ≫ g = f ≫ C₀.ι) :
    ∃ W : Subfunctor X, IsClosedSubspace B S hS W ∧ IsFinitePresentation B S hS W.ι ∧
      IsCoverStratified B S hS W ∧ subspacePointSet B S hS X C₀ ⊆ subspacePointSet B S hS X W := by
  obtain ⟨T', s', i', hs'ci, hs'fp, hi', sq⟩ :=
    exists_isPullback_closedImmersion_cut hZ hX hXqc hXqs hC₀ hffp hgfp hi hig
  have hY := isAlgebraicSpace_yoneda B S hS Y
  let g' := yoneda.map s' ≫ g
  have hg' : IsFinite B S hS g' :=
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _ hs'ci) hg
  have hg'fp : IsFinitePresentation B S hS g' :=
    isFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS T')
      (isAlgebraicSpace_yoneda B S hS T) hX _ _ hs'fp hgfp
  -- the open set of `|X|` over which `f` is étale
  have hUo : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  let Zc := reducedClosedSubspace B S hS C₀.toFunctor hC₀.1 _ hUo.isClosed_compl
  have hZc := isClosedSubspace_reducedClosedSubspace B S hS C₀.toFunctor hC₀.1 _ hUo.isClosed_compl
  have hZcpts : Set.range (pointsMap B S hS Zc.toFunctor Zc.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS C₀.toFunctor hC₀.1 _ hUo.isClosed_compl
  let O : Set (points B S hS X) := (Set.range (pointsMap B S hS _ (Zc.ι ≫ C₀.ι)))ᶜ
  have hO : IsOpen O := (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX _
    (isClosedImmersion_comp B S hS _ _ hZc.2 hC₀.2)).isOpen_compl
  have hmemO : ∀ c : points B S hS C₀.toFunctor, pointsMap B S hS _ C₀.ι c ∈ O →
      c ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    intro c hc
    by_contra hcU
    rw [← Set.mem_compl_iff, ← hZcpts] at hcU
    obtain ⟨z, rfl⟩ := hcU
    exact hc ⟨z, by rw [pointsMap_comp_apply]⟩
  refine exists_isCoverStratified_of_spreadCover hZ hX hXqc hXqs hC₀ hsmall hg' hg'fp hO ?_ ?_ ?_
  · obtain ⟨_, ⟨c, rfl⟩⟩ := hne
    have : Nonempty (points B S hS C₀.toFunctor) := ⟨c⟩
    obtain ⟨_, ⟨u, rfl⟩⟩ := hUd.nonempty
    refine ⟨pointsMap B S hS _ C₀.ι (pointsMap B S hS _ U.ι u), ?_, ⟨_, rfl⟩⟩
    rintro ⟨z, hz⟩
    rw [pointsMap_comp_apply] at hz
    have hzK : pointsMap B S hS _ Zc.ι z ∈ (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
      hZcpts ▸ ⟨z, rfl⟩
    exact hzK ⟨u, (pointsMap_injective_of_mono B S hS C₀.ι hz).symm⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨y, rfl⟩ := hfs c
    refine ⟨pointsMap B S hS _ i' y, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← sq.w]
  · intro t ht
    have hfst : pullback.fst C₀.ι g' = sq.isoPullback.inv ≫ f := sq.isoPullback_inv_fst.symm
    have hP : IsAlgebraicSpace B S hS (pullback C₀.ι g') :=
      isAlgebraicSpace_pullback B S hS _ _ hC₀.1 (isAlgebraicSpace_yoneda B S hS T') hX
    rw [hfst]
    refine IsEtaleAt.comp B S hS hP hY (isEtaleAt_of_isEtale B S hS hP _
      (isEtale_of_iso B S hS sq.isoPullback.symm) t) ?_
    refine isEtaleAt_of_isEtale_pullback_fst B S hS hC₀.1 hY U hU f hUe _ (hmemO _ ?_)
    rwa [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← Category.assoc, ← hfst]

end AlgebraicGeometry.Space

end
