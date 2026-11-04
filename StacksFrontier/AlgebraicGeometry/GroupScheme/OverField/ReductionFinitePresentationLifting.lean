module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.Limits.SurjectiveFinitePresentationCriterion
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedImmersionFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation

/-!
# Lifting finite presentation along a nil-thickening of group schemes

Let `G` be a group scheme over a field `k` and `L ⊆ G` a closed subgroup scheme with the same
underlying space (for instance `G_red`). Suppose `Z ⊆ L` is a closed subscheme with `Z → G`
locally of finite presentation, and `π : V ⟶ X` is a flat quasi-compact `k`-morphism on an open
`V ⊆ L` whose fibres are contained in left translates of `Z`: whenever `π x = π y`, the point
`x⁻¹ · y` lies in `Z`. If `π` extends to a `k`-morphism `π'` on an open `U ⊆ G` with
`L ∩ U ⊆ V`, then `L → G` is locally of finite presentation near every point of `U`.

This is the lifting step of Perrin's proof that group schemes over a field of characteristic
zero are reduced (thesis IV 2.3), made elementary.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_locallyOfFinitePresentation`: the lifting lemma.
* `AlgebraicGeometry.exists_stage_comp_eq`: the limit step (a factorization at the limit of the
  finite-presentation closed subschemes containing a closed subscheme happens at a stage).
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_flat_of_surjective` and
  `AlgebraicGeometry.le_ker_of_le_ker_comp_of_flat_of_surjective`: factoring through a closed
  immersion descends along flat surjective quasi-compact morphisms.

## Implementation notes

On an affine open `U' ⊆ U`, `L ∩ U'` is the limit of the finite-presentation closed subschemes
`S_J ⊇ L ∩ U'` of `U'` (Tag 09ZP). As `L` is a nil-thickening, every point of `U'` comes from `V`,
so the base change `W₀ = U' ×_X V → U'` of `π` along `π'` is flat, surjective and quasi-compact;
choose an affine `W` flat and surjective over it. On `S_J ×_{U'} W` both points `x` (from `S_J`)
and `y` (from `V`) are pulled back from `W`, so `x⁻¹ · y` is the pull-back of one map
`ζ : W ⟶ G`. At the limit `x⁻¹ · y` lies in `Z`; as `Z → G` is locally of finite presentation,
it does so on some `S_J ×_{U'} W`, where then `x = y · (x⁻¹ y)⁻¹` lies in `L`. Descending along
the flat surjection `S_J ×_{U'} W → S_J` gives `S_J ⊆ L ∩ U'`, so the ideal of `L ∩ U'` is the
finitely generated ideal of `S_J`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A flat, surjective, quasi-compact morphism is scheme-theoretically dominant: a section
killed by it has zero germs, since each stalk map is faithfully flat, hence injective. -/
theorem isSchemeTheoreticallyDominant_of_flat_of_surjective {W T : Scheme.{u}} (p : W ⟶ T)
    [Flat p] [Surjective p] [QuasiCompact p] : IsSchemeTheoreticallyDominant p := by
  refine ⟨Scheme.IdealSheafData.ext (funext fun U => ?_)⟩
  rw [Scheme.Hom.ker_apply]
  refine (RingHom.injective_iff_ker_eq_bot _).mp fun s s' hss' => ?_
  apply TopCat.Presheaf.section_ext T.sheaf
  intro t ht
  obtain ⟨w, rfl⟩ := p.surjective t
  have hinj : Function.Injective (p.stalkMap w) := by
    algebraize [(p.stalkMap w).hom]
    have : Module.FaithfullyFlat (T.presheaf.stalk (p w)) (W.presheaf.stalk w) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap p w) (p.toLRSHom.prop w)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  show p.stalkMap w (T.presheaf.germ U (p w) ht s) =
    p.stalkMap w (T.presheaf.germ U (p w) ht s')
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, hss']

/-- Factoring through a closed immersion descends along a flat, surjective, quasi-compact
morphism. -/
theorem le_ker_of_le_ker_comp_of_flat_of_surjective {W T Y Z : Scheme.{u}} (i : Z ⟶ Y)
    (g : T ⟶ Y) (p : W ⟶ T) [Flat p] [Surjective p] [QuasiCompact p] (h : i.ker ≤ (p ≫ g).ker) :
    i.ker ≤ g.ker := by
  have := isSchemeTheoreticallyDominant_of_flat_of_surjective p
  rwa [Scheme.Hom.ker_comp, p.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h

/-- A quasi-compact scheme receives a flat surjection from an affine scheme: the disjoint union of
a finite affine open cover. -/
theorem exists_isAffine_flat_surjective (W₀ : Scheme.{u}) [CompactSpace W₀] :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ W₀), Flat p ∧ Surjective p := by
  let 𝒰 := W₀.affineCover.finiteSubcover
  have : ∀ i, IsAffine (𝒰.X i) := fun i => by
    dsimp [𝒰, Scheme.OpenCover.finiteSubcover]
    infer_instance
  refine ⟨∐ 𝒰.X, inferInstance, Sigma.desc 𝒰.f, inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact ⟨Sigma.ι 𝒰.X i y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

open Stacks.Flatness in
/-- If some finite-presentation enlargement of the closed subscheme cut out by a closed immersion
`f` factors through `f`, then `f` is locally of finite presentation: the enlargement is `f`. -/
theorem locallyOfFinitePresentation_of_stage_factors {P Y : Scheme.{u}} (f : P ⟶ Y)
    [IsClosedImmersion f] (J : FinitePresentationSubscheme f.ker) (g : J.1.subscheme ⟶ P)
    (hg : g ≫ f = J.1.subschemeι) : LocallyOfFinitePresentation f := by
  have hle : f.ker ≤ J.1 := by
    have := Scheme.Hom.le_ker_comp g f
    rwa [hg, Scheme.IdealSheafData.ker_subschemeι] at this
  have hJ : J.1 = f.ker := le_antisymm J.2.2 hle
  let e : P ⟶ J.1.subscheme := IsClosedImmersion.lift J.1.subschemeι f
    (by rw [Scheme.IdealSheafData.ker_subschemeι, hJ])
  have he : e ≫ J.1.subschemeι = f := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq f J.1.subschemeι e he
    (by rw [Scheme.IdealSheafData.ker_subschemeι, hJ])
  have : LocallyOfFinitePresentation J.1.subschemeι := J.2.1.1
  rw [← he]
  infer_instance

open Stacks.Flatness in
/-- **The limit step.** Let `f : P ⟶ Y` be a closed immersion into an affine scheme, `w : W ⟶ Y`
a morphism from an affine scheme, and `ζ : W ⟶ G` a morphism. If the composite
`P ×_Y W ⟶ W ⟶ G` factors through a morphism `i : Z ⟶ G` locally of finite presentation, then
so does `S ×_Y W ⟶ W ⟶ G` for some finite-presentation closed subscheme `S ⊇ P` of `Y`:
`P ×_Y W` is the limit of the `S ×_Y W` (Tag 09ZP, base changed along `w`). -/
theorem exists_stage_comp_eq {Y P W G Z : Scheme.{u}} [IsAffine Y] [IsAffine W] (f : P ⟶ Y)
    [IsClosedImmersion f] (w : W ⟶ Y) (ζ : W ⟶ G) (i : Z ⟶ G) [LocallyOfFinitePresentation i]
    (a : pullback f w ⟶ Z) (ha : a ≫ i = pullback.snd f w ≫ ζ) :
    ∃ (J : FinitePresentationSubscheme f.ker) (b : pullback J.1.subschemeι w ⟶ Z),
      b ≫ i = pullback.snd J.1.subschemeι w ≫ ζ := by
  have : IsCofiltered (FinitePresentationSubscheme f.ker)ᵒᵖ :=
    isCofiltered_finitePresentationSubscheme_op f.ker
  let F : Over Y ⥤ Scheme.{u} := Over.pullback w ⋙ Over.forget W
  let D := subschemeDiagram f.ker ⋙ F
  let c : Cone D := F.mapCone (finitePresentationCone f (le_refl f.ker))
  have hc : IsLimit c := isLimitOfPreserves F (isLimit_finitePresentationCone_of_isAffine f)
  have : ∀ J, IsAffine (D.obj J) := fun J => by
    have : IsAffine J.unop.1.subscheme := isAffine_of_isAffineHom J.unop.1.subschemeι
    show IsAffine (pullback J.unop.1.subschemeι w)
    exact isAffine_of_isAffineHom (pullback.snd J.unop.1.subschemeι w)
  have hDmap : ∀ {J J'} (e : J ⟶ J'), IsAffineHom (D.map e) := fun e => inferInstance
  let t : D ⟶ (Functor.const _).obj G :=
    { app J := pullback.snd J.unop.1.subschemeι w ≫ ζ
      naturality J J' e := by
        simp only [Functor.const_obj_map]
        exact Over.w_assoc ((Over.pullback w).map ((subschemeDiagram f.ker).map e)) ζ }
  have hct : c.π ≫ t = (Functor.const _).map (a ≫ i) := by
    ext J
    rw [NatTrans.comp_app, Functor.const_map_app]
    show ((Over.pullback w).map ((finitePresentationCone f (le_refl f.ker)).π.app J)).left ≫
      pullback.snd J.unop.1.subschemeι w ≫ ζ = a ≫ i
    rw [ha]
    exact Over.w_assoc
      ((Over.pullback w).map ((finitePresentationCone f (le_refl f.ker)).π.app J)) ζ
  obtain ⟨J, b, -, hb⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t i c hc a hct
  exact ⟨J.unop, b, hb⟩

section Points

open CategoryTheory.MonObj CategoryTheory.GrpObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {H G : Grp C}

/-- If `a⁻¹ · φ(b) = φ(c)` for a homomorphism `φ` of group objects, then `a = φ(b · c⁻¹)`. -/
theorem eq_mul_inv_comp_of_inv_mul_eq_comp (φ : H ⟶ G) {T : C} (a : T ⟶ G.X)
    (b c : T ⟶ H.X) :
    letI := Hom.group (X := T) (G := G.X)
    letI := Hom.group (X := T) (G := H.X)
    a⁻¹ * (b ≫ φ.hom.hom) = c ≫ φ.hom.hom → a = (b * c⁻¹) ≫ φ.hom.hom := by
  let := Hom.group (X := T) (G := G.X)
  let := Hom.group (X := T) (G := H.X)
  intro h
  rw [MonObj.mul_comp, GrpObj.inv_comp, ← h]
  group

end Points

/-- When `ι` is surjective and `π' ∘ (ι ∣_ U) = π ∘ (inclusion)`, the base change of `π` along
`U' → U → X` is surjective onto `U'`: every point of `U'` is `ι` of a point of `V`. -/
theorem surjective_pullback_fst_of_surjective {L G X : Scheme.{u}} (ι : L ⟶ G) [Surjective ι]
    (V : L.Opens) (π : V.toScheme ⟶ X) (U : G.Opens) (hUV : ι ⁻¹ᵁ U ≤ V)
    (π' : U.toScheme ⟶ X) (hπ' : (ι ∣_ U) ≫ π' = L.homOfLE hUV ≫ π) (U' : G.Opens)
    (hU'U : U' ≤ U) : Surjective (pullback.fst (G.homOfLE hU'U ≫ π') π) := by
  refine ⟨fun u => ?_⟩
  obtain ⟨l, hl⟩ := ι.surjective u.1
  have hlU : l ∈ ι ⁻¹ᵁ U := by
    show ι l ∈ U
    rw [hl]
    exact hU'U u.2
  let l₁ : (ι ⁻¹ᵁ U).toScheme := ⟨l, hlU⟩
  have hres : (ι ∣_ U) l₁ = G.homOfLE hU'U u := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hl.trans (Scheme.homOfLE_apply hU'U u).symm
  have hcomm : (G.homOfLE hU'U ≫ π') u = π (L.homOfLE hUV l₁) := by
    rw [Scheme.Hom.comp_apply, ← hres, ← Scheme.Hom.comp_apply, hπ', Scheme.Hom.comp_apply]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback u (L.homOfLE hUV l₁) hcomm
  exact ⟨z, hz⟩

/-- In the setting of `surjective_pullback_fst_of_surjective`, with `π` flat and quasi-compact and
`U'` affine, some affine `W` is flat and surjective over `U'` and maps to `V` compatibly. -/
theorem exists_isAffine_flat_surjective_pullback_cover {L G X : Scheme.{u}} (ι : L ⟶ G)
    [Surjective ι] (V : L.Opens) (π : V.toScheme ⟶ X) [QuasiCompact π] [Flat π] (U : G.Opens)
    (hUV : ι ⁻¹ᵁ U ≤ V) (π' : U.toScheme ⟶ X) (hπ' : (ι ∣_ U) ≫ π' = L.homOfLE hUV ≫ π)
    (U' : G.Opens) [IsAffine U'.toScheme] (hU'U : U' ≤ U) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (w : W ⟶ U'.toScheme) (y : W ⟶ V.toScheme),
      Flat w ∧ Surjective w ∧ w ≫ G.homOfLE hU'U ≫ π' = y ≫ π := by
  have := surjective_pullback_fst_of_surjective ι V π U hUV π' hπ' U' hU'U
  have : CompactSpace (pullback (G.homOfLE hU'U ≫ π') π : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (G.homOfLE hU'U ≫ π') π)
  obtain ⟨W, hW, q, _, _⟩ := exists_isAffine_flat_surjective (pullback (G.homOfLE hU'U ≫ π') π)
  exact ⟨W, hW, q ≫ pullback.fst _ _, q ≫ pullback.snd _ _, inferInstance, inferInstance,
    by simp only [Category.assoc, pullback.condition]⟩

open Stacks.Flatness CategoryTheory.MonObj CategoryTheory.GrpObj in
/-- **The descent step.** Let `w : W ⟶ U'` be a flat surjection of affine schemes onto an open of
`G`, and `x`, `y` points of `G` and `L` over `W` with `x` the inclusion `w`. If `x⁻¹ · y` factors
through `Z` on `(L ∩ U') ×_{U'} W`, then `L ∩ U' → U'` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_restrict_of_inv_mul_factors (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme G) {Z : Scheme.{u}}
    (iZ : Z ⟶ L.carrier.X.left) [LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left)]
    {U' : G.X.left.Opens} [IsAffine U'.toScheme] {W : Scheme.{u}} [IsAffine W]
    (w : W ⟶ U'.toScheme) [Flat w] [Surjective w] (σ : W ⟶ Spec (.of k))
    (x : Over.mk σ ⟶ G.X) (hx : x.left = w ≫ U'.ι) (y : Over.mk σ ⟶ L.carrier.X)
    (a : pullback (L.ι.hom.hom.left ∣_ U') w ⟶ Z)
    (ha : letI := Hom.group (X := Over.mk σ) (G := G.X)
      a ≫ iZ ≫ L.ι.hom.hom.left = pullback.snd _ w ≫ (x⁻¹ * (y ≫ L.ι.hom.hom)).left) :
    LocallyOfFinitePresentation (L.ι.hom.hom.left ∣_ U') := by
  let iL := L.ι.hom.hom.left
  have : IsClosedImmersion iL := L.isClosedImmersion
  let := Hom.group (X := Over.mk σ) (G := G.X)
  have hζG : (x⁻¹ * (y ≫ L.ι.hom.hom)).left ≫ G.X.hom = σ := Over.w (x⁻¹ * (y ≫ L.ι.hom.hom))
  obtain ⟨J, b, hb⟩ :=
    exists_stage_comp_eq (iL ∣_ U') w (x⁻¹ * (y ≫ L.ι.hom.hom)).left (iZ ≫ iL) a ha
  -- at the stage `J`: the structure map of `S_J` factors through `L`, after a flat surjection
  let TE : Over (Spec (.of k)) := Over.mk (pullback.snd J.1.subschemeι w ≫ σ)
  let shE : TE ⟶ Over.mk σ := Over.homMk (pullback.snd J.1.subschemeι w) rfl
  let := Hom.group (X := TE) (G := G.X)
  let := Hom.group (X := TE) (G := L.carrier.X)
  let bh : TE ⟶ L.carrier.X := Over.homMk (b ≫ iZ) (by
    show (b ≫ iZ) ≫ L.carrier.X.hom = pullback.snd J.1.subschemeι w ≫ σ
    rw [← Over.w L.ι.hom.hom, ← hζG]
    simpa only [Category.assoc] using congrArg (· ≫ G.X.hom) hb)
  have hb' : (shE ≫ x)⁻¹ * ((shE ≫ y) ≫ L.ι.hom.hom) = bh ≫ L.ι.hom.hom := by
    rw [Category.assoc, ← GrpObj.comp_inv, ← MonObj.comp_mul]
    ext
    simpa [bh, shE, Category.assoc] using hb.symm
  have hfac' : pullback.fst J.1.subschemeι w ≫ J.1.subschemeι ≫ U'.ι =
      ((shE ≫ y) * bh⁻¹).left ≫ iL := by
    have := congrArg Over.Hom.left
      (eq_mul_inv_comp_of_inv_mul_eq_comp L.ι (shE ≫ x) (shE ≫ y) bh hb')
    simp only [Over.comp_left, hx] at this
    rw [pullback.condition_assoc]
    exact this
  have hker : iL.ker ≤ (J.1.subschemeι ≫ U'.ι).ker :=
    le_ker_of_le_ker_comp_of_flat_of_surjective iL _ (pullback.fst J.1.subschemeι w)
      (by rw [hfac']; exact Scheme.Hom.le_ker_comp _ _)
  let g₀ := IsClosedImmersion.lift iL (J.1.subschemeι ≫ U'.ι) hker
  have hg₀ : g₀ ≫ iL = J.1.subschemeι ≫ U'.ι := IsClosedImmersion.lift_fac _ _ _
  exact locallyOfFinitePresentation_of_stage_factors (iL ∣_ U') J
    ((isPullback_morphismRestrict iL U').lift J.1.subschemeι g₀ hg₀.symm)
    ((isPullback_morphismRestrict iL U').lift_fst _ _ _)

open Stacks.Flatness CategoryTheory.MonObj CategoryTheory.GrpObj in
/-- **The lifting lemma over an affine open.** See
`AlgebraicGeometry.exists_mem_and_locallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_restrict_of_isAffineOpen (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left]
    {Z : Scheme.{u}} (iZ : Z ⟶ L.carrier.X.left)
    [LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left)]
    (V : L.carrier.X.left.Opens) (X : Over (Spec (.of k)))
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ L.carrier.X.hom) [QuasiCompact π] [Flat π]
    (U : G.X.left.Opens) (hUV : L.ι.hom.hom.left ⁻¹ᵁ U ≤ V) (π' : U.toScheme ⟶ X.left)
    (hπ'k : π' ≫ X.hom = U.ι ≫ G.X.hom)
    (hπ' : (L.ι.hom.hom.left ∣_ U) ≫ π' = L.carrier.X.left.homOfLE hUV ≫ π)
    (h : ∀ (T : Over (Spec (.of k))) (x y : T ⟶ L.carrier.X) (x' y' : T.left ⟶ V.toScheme),
      x' ≫ V.ι = x.left → y' ≫ V.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := L.carrier.X)
      ∃ z : T.left ⟶ Z, z ≫ iZ = (x⁻¹ * y).left)
    (U' : G.X.left.Opens) (hU' : IsAffineOpen U') (hU'U : U' ≤ U) :
    LocallyOfFinitePresentation (L.ι.hom.hom.left ∣_ U') := by
  let iL := L.ι.hom.hom.left
  have : IsClosedImmersion iL := L.isClosedImmersion
  have : IsAffine U'.toScheme := hU'
  let f := iL ∣_ U'
  have hU'V : iL ⁻¹ᵁ U' ≤ V := (Scheme.Hom.preimage_mono iL hU'U).trans hUV
  obtain ⟨W, hW, w, yW', _, _, hw⟩ :=
    exists_isAffine_flat_surjective_pullback_cover iL V π U hUV π' hπ' U' hU'U
  have hfι : f ≫ U'.ι = (iL ⁻¹ᵁ U').ι ≫ iL := morphismRestrict_ι iL U'
  -- the points on `W`
  let σW : W ⟶ Spec (.of k) := w ≫ U'.ι ≫ G.X.hom
  let TW : Over (Spec (.of k)) := Over.mk σW
  let xW : TW ⟶ G.X := Over.homMk (w ≫ U'.ι) (by simp [TW, σW])
  have hyW : (yW' ≫ V.ι) ≫ L.carrier.X.hom = σW := by
    simp only [σW, Category.assoc, ← hπ]
    rw [← reassoc_of% hw]
    simp only [hπ'k, Scheme.homOfLE_ι_assoc]
  let yW : TW ⟶ L.carrier.X := Over.homMk (yW' ≫ V.ι) hyW
  let := Hom.group (X := TW) (G := G.X)
  let ζ : W ⟶ G.X.left := (xW⁻¹ * (yW ≫ L.ι.hom.hom)).left
  have hζG : ζ ≫ G.X.hom = σW := Over.w (xW⁻¹ * (yW ≫ L.ι.hom.hom))
  -- the points at the limit `P ×_{U'} W`
  let T' : Over (Spec (.of k)) := Over.mk (pullback.snd f w ≫ σW)
  let sh : T' ⟶ TW := Over.homMk (pullback.snd f w) rfl
  let x' : pullback f w ⟶ V.toScheme := pullback.fst f w ≫ L.carrier.X.left.homOfLE hU'V
  have hx'ι : x' ≫ V.ι ≫ iL = pullback.snd f w ≫ w ≫ U'.ι := by
    simp only [x', Category.assoc, Scheme.homOfLE_ι_assoc, ← hfι, pullback.condition_assoc]
  let xh : T' ⟶ L.carrier.X := Over.homMk (x' ≫ V.ι) (by
    show (x' ≫ V.ι) ≫ L.carrier.X.hom = pullback.snd f w ≫ w ≫ U'.ι ≫ G.X.hom
    rw [← Over.w L.ι.hom.hom, Category.assoc, reassoc_of% hx'ι])
  let yh : T' ⟶ L.carrier.X := sh ≫ yW
  have hπeq : x' ≫ π = (pullback.snd f w ≫ yW') ≫ π := by
    simp only [x', Category.assoc]
    rw [← Scheme.homOfLE_homOfLE L.carrier.X.left (Scheme.Hom.preimage_mono iL hU'U) hUV,
      Category.assoc, ← hπ', ← Category.assoc (L.carrier.X.left.homOfLE _),
      ← morphismRestrict_homOfLE iL _ _ hU'U, Category.assoc, pullback.condition_assoc, hw]
  obtain ⟨z, hz⟩ := h T' xh yh x' (pullback.snd f w ≫ yW') rfl (by simp [yh, sh, yW]) hπeq
  let := Hom.group (X := T') (G := G.X)
  let := Hom.group (X := T') (G := L.carrier.X)
  have hxh : xh ≫ L.ι.hom.hom = sh ≫ xW := by
    ext
    simpa [xh, sh, xW, Category.assoc] using hx'ι
  have ha : z ≫ iZ ≫ iL = pullback.snd f w ≫ ζ := by
    have h1 : z ≫ iZ ≫ iL = ((xh⁻¹ * yh) ≫ L.ι.hom.hom).left := by
      rw [← Category.assoc, hz]
      rfl
    have h2 : pullback.snd f w ≫ ζ = (sh ≫ (xW⁻¹ * (yW ≫ L.ι.hom.hom))).left := rfl
    rw [h1, h2, MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv, hxh]
    rfl
  exact locallyOfFinitePresentation_restrict_of_inv_mul_factors k G L iZ w σW xW rfl yW z ha

open CategoryTheory.MonObj CategoryTheory.GrpObj in
/-- **The lifting lemma (Perrin IV 2.3, local form).** Let `G` be a group scheme over a field `k`
and `L ⊆ G` a closed subgroup scheme which is a nil-thickening (`L → G` surjective), `Z ⊆ L` a
closed subscheme with `Z → G` locally of finite presentation, and `π : V ⟶ X` a flat
quasi-compact `k`-morphism on an open `V ⊆ L` such that `x⁻¹ · y` factors through `Z` whenever
`x, y` are points of `V` with `π x = π y`. Suppose `π` extends, on an open `U` of `G` with
`L ∩ U ⊆ V`, to a `k`-morphism `π' : U ⟶ X`. Then every point of `U` has an affine open
neighbourhood `U' ⊆ U` over which `L ⊆ G` is locally of finite presentation. -/
theorem exists_isAffineOpen_locallyOfFinitePresentation (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left]
    {Z : Scheme.{u}} (iZ : Z ⟶ L.carrier.X.left)
    [LocallyOfFinitePresentation (iZ ≫ L.ι.hom.hom.left)]
    (V : L.carrier.X.left.Opens) (X : Over (Spec (.of k)))
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ L.carrier.X.hom) [QuasiCompact π] [Flat π]
    (U : G.X.left.Opens) (hUV : L.ι.hom.hom.left ⁻¹ᵁ U ≤ V) (π' : U.toScheme ⟶ X.left)
    (hπ'k : π' ≫ X.hom = U.ι ≫ G.X.hom)
    (hπ' : (L.ι.hom.hom.left ∣_ U) ≫ π' = L.carrier.X.left.homOfLE hUV ≫ π)
    (h : ∀ (T : Over (Spec (.of k))) (x y : T ⟶ L.carrier.X) (x' y' : T.left ⟶ V.toScheme),
      x' ≫ V.ι = x.left → y' ≫ V.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := L.carrier.X)
      ∃ z : T.left ⟶ Z, z ≫ iZ = (x⁻¹ * y).left)
    (e : G.X.left) (he : e ∈ U) :
    ∃ U' : G.X.left.Opens, e ∈ U' ∧ U' ≤ U ∧ IsAffineOpen U' ∧
      LocallyOfFinitePresentation (L.ι.hom.hom.left ∣_ U') := by
  obtain ⟨U', hU', heU', hU'U⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.X.left.isBasis_affineOpens) he
  exact ⟨U', heU', hU'U, hU',
    locallyOfFinitePresentation_restrict_of_isAffineOpen k G L iZ V X π hπ U hUV π' hπ'k hπ' h
      U' hU' hU'U⟩

end AlgebraicGeometry

end
