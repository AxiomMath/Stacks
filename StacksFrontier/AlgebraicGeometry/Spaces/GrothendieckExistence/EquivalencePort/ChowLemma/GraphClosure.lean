module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Morphisms.OpenImmersionOfFlatClosure
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.FlattenedGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flattened closure of the graph of a dense open of an algebraic space

Let `X` be an algebraic space separated and locally of finite type over `S`, let
`u : h_D ⟶ X` be an open immersion from a scheme, and let `D ⟶ Z` be a quasi-compact open
immersion into a Noetherian scheme `Z` separated over `S`. Choose an étale atlas `φ : h_V ⟶ X`.
On the chart, the graph of `D ×_X V ⟶ D ⟶ Z` has a scheme-theoretic closure in `V ×_S Z`, and the
flattening of Stacks 0815 provides a `D`-admissible blowup `Z₂ ⟶ Z` such that the strict
transform of that closure is flat over `Z₂`. By Stacks 0879 the scheme-theoretic closure `T₀` of
`D` in `X ×_S Z₂` is then an open subscheme of `Z₂`, isomorphic to `D` over `D` (Stacks 0CP3).

## Main results

* `CategoryTheory.Limits.C1573.isPullback_lift_diagonal`: the comparison `V ×_X D ⟶ V ×_Y D` is a
  base change of the diagonal of `X ⟶ Y`.
* `AlgebraicGeometry.Space.C1573.isPullback_toSchemeTheoreticImage_of_isOpenImmersion`: Stacks 0CP3
  over a representable quasi-compact open.
* `AlgebraicGeometry.Space.C1573.isClosedImmersion_toScheme_lift_of_isSeparated`: for `X` separated
  over `S`, the scheme `V ×_X D` is closed in `V ×_S D`.
* `AlgebraicGeometry.Space.C1573.exists_flattenedGraphClosure`: the statement above.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
-/

namespace CategoryTheory.Limits.C1573
end CategoryTheory.Limits.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace CategoryTheory.Limits

open _root_.CategoryTheory.Limits.C1573 _root_.AlgebraicGeometry.C1573
/-- **The graph of a fibre product is a base change of the diagonal.** For `φ : V ⟶ X`,
`u : D ⟶ X` and `f : X ⟶ Y`, the comparison `V ×_X D ⟶ V ×_Y D`, read through any two pullback
squares, is the base change of the diagonal of `f`. -/
@[ega "I 5.3.7" "more general", sga "3 VIIB 1.6.1" "partial", sga "4 IV 5.11.1" "special case"]
theorem C1573.isPullback_lift_diagonal {C : Type*} [Category C] [HasPullbacks C] {X Y V D P Q : C}
    (f : X ⟶ Y) (φ : V ⟶ X) (u : D ⟶ X) {a : P ⟶ V} {b : P ⟶ D} (h : IsPullback a b φ u)
    {a' : Q ⟶ V} {b' : Q ⟶ D} (h' : IsPullback a' b' (φ ≫ f) (u ≫ f)) :
    IsPullback (a ≫ φ) (h'.lift a b (by rw [reassoc_of% h.w]))
      (pullback.diagonal f) (pullback.lift (a' ≫ φ) (b' ≫ u) (by simpa using h'.w)) := by
  refine (pullback_map_diagonal_isPullback φ u f).of_iso h.isoPullback.symm (Iso.refl _)
    h'.isoPullback.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · apply h'.hom_ext <;> simp
  · simp
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Iso.refl_hom, Category.comp_id,
        Iso.symm_hom]
      rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
    · simp only [Category.assoc, pullback.lift_snd, Iso.refl_hom, Category.comp_id,
        Iso.symm_hom]
      rw [← Category.assoc, IsPullback.isoPullback_inv_snd]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The scheme of a fibre product of the site is the fibre product of the schemes. -/
theorem C1573.exists_iso_toScheme_pullback {A A' C : BigFppfOver B S hS} (x : A ⟶ C) (y : A' ⟶ C)
    {Y Y' T : Scheme.{u}} (hA : (BigFppfOver.toScheme B S hS).obj A = Y)
    (hA' : (BigFppfOver.toScheme B S hS).obj A' = Y') (gx : Y ⟶ T) (gy : Y' ⟶ T)
    (hT : (BigFppfOver.toScheme B S hS).obj C = T)
    (hx : eqToHom hA.symm ≫ (BigFppfOver.toScheme B S hS).map x ≫ eqToHom hT = gx)
    (hy : eqToHom hA'.symm ≫ (BigFppfOver.toScheme B S hS).map y ≫ eqToHom hT = gy) :
    ∃ e : (BigFppfOver.toScheme B S hS).obj (pullback x y) ≅ pullback gx gy,
      e.inv ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst x y) =
        pullback.fst gx gy ≫ eqToHom hA.symm ∧
      e.inv ≫ (BigFppfOver.toScheme B S hS).map (pullback.snd x y) =
        pullback.snd gx gy ≫ eqToHom hA'.symm := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  subst hA hA' hT hx hy
  simp only [eqToHom_refl, Category.comp_id]
  exact ⟨PreservesPullback.iso _ x y, PreservesPullback.iso_inv_fst _ _ _,
    PreservesPullback.iso_inv_snd _ _ _⟩

/-- **Stacks 0CP3, for a representable open.** Let `f : X ⟶ Y` be a separated morphism of
algebraic spaces, `u : h_W ⟶ Y` a quasi-compact open immersion from a scheme and `s : h_W ⟶ X` a
section of `f` over it. Then the scheme-theoretic image `X'` of `s` is, over `W`, the scheme `W`:
the square `h_W ⟶ X' ⟶ Y`, `h_W = h_W ⟶ Y` is cartesian. -/
theorem C1573.isPullback_toSchemeTheoreticImage_of_isOpenImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSeparated B S hS f) {W : BigFppfOver B S hS} (u : yoneda.obj W ⟶ Y)
    (hu : IsOpenImmersion B S hS u) (huqc : IsQuasiCompact B S hS u) (s : yoneda.obj W ⟶ X)
    (hs : s ≫ f = u) :
    IsPullback (toSchemeTheoreticImage B S hS s) (𝟙 _)
      ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) u := by
  set V := Subfunctor.range u with hVdef
  set e := rangeIsoOfIsOpenImmersion W u hu with hedef
  have heu : e.hom ≫ V.ι = u := Subfunctor.toRange_ι u
  have hV := isOpenSubspace_range_of_isOpenImmersion W u hu
  have hVι : V.ι = e.inv ≫ u :=
    calc V.ι = e.inv ≫ e.hom ≫ V.ι := by simp
      _ = e.inv ≫ u := by rw [heu]
  have hVqc : IsQuasiCompact B S hS V.ι := by
    rw [hVι]; exact isQuasiCompact_isIso_comp B S hS e.inv huqc
  have hs' : (e.inv ≫ s) ≫ f = V.ι := by rw [Category.assoc, hs, hVι]
  have hiso := isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS hX hY
    f hf V hV hVqc (e.inv ≫ s) hs'
  have hT : schemeTheoreticImageSubfunctor B S hS (e.inv ≫ s) =
      schemeTheoreticImageSubfunctor B S hS s :=
    schemeTheoreticImageSubfunctor_congr_range' B S hS _ _ hX (by
      have : Epi e.inv := IsIso.epi_of_iso e.inv
      rw [Subfunctor.range_comp, Subfunctor.range_eq_top e.inv, Subfunctor.image_top])
  rw [hT] at hiso
  set T := schemeTheoreticImageSubfunctor B S hS s with hTdef
  have hw : (e.inv ≫ toSchemeTheoreticImage B S hS s) ≫ T.ι ≫ f = 𝟙 V.toFunctor ≫ V.ι := by
    rw [Category.assoc, ← Category.assoc (toSchemeTheoreticImage B S hS s),
      toSchemeTheoreticImage_ι, ← Category.assoc, hs', Category.id_comp]
  have hl : pullback.lift _ _ hw ≫ pullback.snd (T.ι ≫ f) V.ι = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsIso (pullback.lift _ _ hw ≫ pullback.snd (T.ι ≫ f) V.ι) := by
    rw [hl]; infer_instance
  have : IsIso (pullback.lift _ _ hw) :=
    IsIso.of_isIso_comp_right _ (pullback.snd (T.ι ≫ f) V.ι)
  have sq1 : IsPullback (e.inv ≫ toSchemeTheoreticImage B S hS s) (𝟙 V.toFunctor) (T.ι ≫ f)
      V.ι :=
    IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift _ _ hw)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  refine sq1.of_iso e.symm (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact Category.id_comp _
  · rfl
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, hVι]

/-- **The comparison of a fibre product over a separated space with the product over the base
is a closed immersion.** For `φ : h_V ⟶ X`, `u : h_D ⟶ X` over a separated `X ⟶ h_S` and a
pullback square `h_P = h_V ×_X h_D`, the morphism of schemes `P ⟶ V ×_S D` is a closed
immersion: it is the base change of the diagonal of `X`. -/
theorem C1573.isClosedImmersion_toScheme_lift_of_isSeparated (X : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (hsep : IsSeparated B S hS f)
    {D V P : BigFppfOver B S hS} (u : yoneda.obj D ⟶ X.1) (φ : yoneda.obj V ⟶ X.1)
    (a : P ⟶ V) (b : P ⟶ D) (h : IsPullback (yoneda.map a) (yoneda.map b) φ u)
    (w : (BigFppfOver.toScheme B S hS).map a ≫ B.inclusion.map V.hom =
      (BigFppfOver.toScheme B S hS).map b ≫ B.inclusion.map D.hom) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.lift ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
        w) := by
  set F := BigFppfOver.toScheme B S hS with hF
  set pV := B.inclusion.map V.hom
  set pD := B.inclusion.map D.hom
  have hφf0 : ∀ (W : BigFppfOver B S hS) (x y : yoneda.obj W ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))),
      x = y := fun W x y => (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  have tS : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have hcVD : B.Contains (pullback pV pD) :=
    Scheme.size_pullback_lt _ _ V.left.property D.left.property
  let VD := BigFppfOver.mk B S hS hcVD (pullback.fst pV pD ≫ pV)
  let prV₁ : VD ⟶ V := BigFppfOver.homMk B S hS V.left.property _ (pullback.fst pV pD) rfl
  let prD₁ : VD ⟶ D := BigFppfOver.homMk B S hS D.left.property _ (pullback.snd pV pD)
    (pullback.condition (f := pV) (g := pD)).symm
  let v₁ : V ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk V.hom (by simp)
  let d₁ : D ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk D.hom (by simp)
  have hVDsite : IsPullback prV₁ prD₁ v₁ d₁ :=
    IsPullback.of_map F (tS.hom_ext _ _) (IsPullback.of_hasPullback pV pD)
  have hVD := hVDsite.map yoneda
  have h' : IsPullback (yoneda.map prV₁) (yoneda.map prD₁) (φ ≫ f) (u ≫ f) := by
    rw [hφf0 _ (φ ≫ f) (yoneda.map v₁), hφf0 _ (u ≫ f) (yoneda.map d₁)]
    exact hVD
  have sq := CategoryTheory.Limits.C1573.isPullback_lift_diagonal f φ u h h'
  set l₁ : P ⟶ VD := hVDsite.lift a b (tS.hom_ext _ _) with hl₁
  have hl : h'.lift (yoneda.map a) (yoneda.map b)
      (by rw [reassoc_of% h.w]) = yoneda.map l₁ := by
    apply h'.hom_ext
    · rw [IsPullback.lift_fst, ← yoneda.map_comp, hVDsite.lift_fst]
    · rw [IsPullback.lift_snd, ← yoneda.map_comp, hVDsite.lift_snd]
  rw [hl] at sq
  have hbc : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hci := hbc.of_isPullback sq hsep
  have hci' : _root_.AlgebraicGeometry.IsClosedImmersion (F.map l₁) :=
    (presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance l₁).1 hci
  have hFl : F.map l₁ = pullback.lift (F.map a) (F.map b) w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      show F.map l₁ ≫ F.map prV₁ = _
      rw [← F.map_comp, hVDsite.lift_fst]
    · rw [pullback.lift_snd]
      show F.map l₁ ≫ F.map prD₁ = _
      rw [← F.map_comp, hVDsite.lift_snd]
  rw [← hFl]
  exact hci'

/-- **The flattened closure of a graph.** Let `X ⟶ h_S` be separated and locally of finite type,
`u : h_D ⟶ X` a quasi-compact open immersion, `j₀ : D ⟶ Z` a quasi-compact open immersion into a
Noetherian scheme separated over `S`, and `φ : h_V ⟶ X` surjective and étale. Then there are a
blowup `b : Z₂ ⟶ Z` in a finitely presented ideal `K` whose support is the complement of `D`, an
open subscheme `o : T₀ ⟶ Z₂` with a morphism `τ : h_{T₀} ⟶ X` and a lift `σ : D ⟶ T₀` of `j₀`
such that `h_D ≅ h_{T₀} ×_X h_D`, and the chart `h_{TV} = h_{T₀} ×_X h_V` of `T₀` is closed in
`V ×_S Z₂`. -/
theorem C1573.exists_flattenedGraphClosure (X : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hsep : IsSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    {D Z V : BigFppfOver B S hS} (u : yoneda.obj D ⟶ X.1) (hu : IsOpenImmersion B S hS u)
    (j₀ : D ⟶ Z) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j₀)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map j₀)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj D)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj Z)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z)]
    [_root_.AlgebraicGeometry.IsSeparated (B.inclusion.map Z.hom)]
    (huqc : IsQuasiCompact B S hS u)
    (φ : yoneda.obj V ⟶ X.1)
    (hφs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hφe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    [CompactSpace ↥(pullback (B.inclusion.map V.hom) (B.inclusion.map Z.hom))]
    [LocallyOfFiniteType (B.inclusion.map V.hom)] :
    ∃ (K : ((BigFppfOver.toScheme B S hS).obj Z).IdealSheafData)
      (_ : FinitePresentation K.subschemeι)
      (_ : K.supportSet = ((BigFppfOver.toScheme B S hS).map j₀).opensRange.carrierᶜ)
      (Z₂ T₀ TV : BigFppfOver B S hS) (b : Z₂ ⟶ Z)
      (eZ₂ : (BigFppfOver.toScheme B S hS).obj Z₂ ≅ AlgebraicGeometry.blowUp K)
      (o : T₀ ⟶ Z₂) (τ : yoneda.obj T₀ ⟶ X.1) (σ : D ⟶ T₀) (pT : TV ⟶ T₀) (tV : TV ⟶ V)
      (c : (BigFppfOver.toScheme B S hS).obj TV ⟶
        pullback (B.inclusion.map V.hom) (B.inclusion.map Z₂.hom)),
      eZ₂.hom ≫ AlgebraicGeometry.blowUpToBase K = (BigFppfOver.toScheme B S hS).map b ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map o) ∧
      σ ≫ o ≫ b = j₀ ∧ yoneda.map σ ≫ τ = u ∧
      IsPullback (yoneda.map σ) (𝟙 _) τ u ∧
      IsPullback (yoneda.map pT) (yoneda.map tV) τ φ ∧
      AlgebraicGeometry.IsClosedImmersion c ∧
      c ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV ∧
      c ≫ pullback.snd _ _ = (BigFppfOver.toScheme B S hS).map (pT ≫ o) := by
  classical
  set F := BigFppfOver.toScheme B S hS with hF
  set pV := B.inclusion.map V.hom with hpV
  set pD := B.inclusion.map D.hom with hpD
  set pZ := B.inclusion.map Z.hom with hpZ
  set ι := F.map j₀ with hιdef
  have hι : ι ≫ pZ = pD := by
    show B.inclusion.map j₀.left ≫ _ = _
    rw [← Functor.map_comp, Over.w j₀]
  have hrep := hu.rep
  set UV := hrep.pullback φ with hUVdef
  set prD : UV ⟶ D := hrep.fst' φ with hprD
  set prV : UV ⟶ V := hrep.snd φ with hprV
  have hUV : IsPullback (yoneda.map prD) (yoneda.map prV) u φ := hrep.isPullback' φ
  set p := F.map prV with hp
  set q := F.map prD with hq
  have hpq : p ≫ pV = q ≫ pD := by
    rw [hp, hq, hpV, hpD]
    show B.inclusion.map prV.left ≫ _ = B.inclusion.map prD.left ≫ _
    rw [← Functor.map_comp, ← Functor.map_comp, Over.w prV, Over.w prD]
  have hgraph : AlgebraicGeometry.IsClosedImmersion
      (Stacks.FlattenedGraph.C1573.graph pV pD p q hpq) :=
    isClosedImmersion_toScheme_lift_of_isSeparated X f hsep u φ prV prD hUV.flip hpq
  have hqflat : Flat q := by
    have hbc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have := (presheaf_yoneda_map_etale_iff B S hS prD).1 (hbc.of_isPullback hUV.flip hφe)
    show Flat (F.map prD)
    infer_instance
  have : AlgebraicGeometry.IsOpenImmersion ι := ‹_›
  have : QuasiCompact ι := ‹_›
  have hγqc : QuasiCompact (Stacks.FlattenedGraph.C1573.graphZ pV pD pZ ι hι p q hpq) := by
    have : QuasiCompact (Stacks.FlattenedGraph.C1573.graphOpen pV pD pZ ι hι) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (Stacks.FlattenedGraph.C1573.isPullback_graphOpen pV pD pZ ι hι).flip inferInstance
    exact inferInstance
  have hlfp :
      LocallyOfFinitePresentation (Stacks.FlattenedGraph.C1573.imageToZ pV pD pZ ι hι p q hpq) := by
    have : LocallyOfFiniteType pV := ‹LocallyOfFiniteType (B.inclusion.map V.hom)›
    have : IsLocallyNoetherian (B.inclusion.obj Z.left) := ‹IsLocallyNoetherian (F.obj Z)›
    rw [LocallyOfFinitePresentation.iff_locallyOfFiniteType]
    exact inferInstance
  have hDc : IsCompact (ι.opensRange : Set (F.obj Z)) := by
    rw [Scheme.Hom.coe_opensRange]; exact isCompact_range ι.base.hom.continuous
  have : CompactSpace (B.inclusion.obj Z.left) := ‹CompactSpace (F.obj Z)›
  have : QuasiSeparatedSpace (B.inclusion.obj Z.left) := ‹QuasiSeparatedSpace (F.obj Z)›
  obtain ⟨K, hK, hKfp, Tc, jc, hjc, hjcflat, hjcker⟩ :=
    Stacks.FlattenedGraph.C1573.exists_flat_closure_graph pV pD pZ ι hι p q hpq hDc
  have hKft : K.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType K).mp hKfp
  have : _root_.AlgebraicGeometry.IsProper (AlgebraicGeometry.blowUpToBase K) :=
    isProper_blowUpToBase_of_fg K hKft
  have hcZ₂ : B.Contains (AlgebraicGeometry.blowUp K) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (AlgebraicGeometry.blowUpToBase K)
      Z.left.property
  set Z₂ := BigFppfOver.mk B S hS hcZ₂ (AlgebraicGeometry.blowUpToBase K ≫ pZ) with hZ₂def
  set b : Z₂ ⟶ Z := BigFppfOver.homMk B S hS Z.left.property pZ
    (AlgebraicGeometry.blowUpToBase K) rfl with hbdef
  set jD : F.obj D ⟶ AlgebraicGeometry.blowUp K :=
    ι.isoOpensRange.hom ≫ Stacks.Blowup.C1573.sectionOver ι.opensRange K hK with hjD
  have hjDb : jD ≫ AlgebraicGeometry.blowUpToBase K = ι := by
    rw [hjD, Category.assoc, Stacks.Blowup.C1573.sectionOver_comp, Scheme.Hom.isoOpensRange_hom_ι]
  set j₂ : D ⟶ Z₂ := BigFppfOver.homMk B S hS hcZ₂ _ jD (by
    rw [← Category.assoc, hjDb, hι]) with hj₂def
  have hFj₂ : F.map j₂ = jD := rfl
  have tS : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  set v : V ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk V.hom (by simp) with hvdef
  set z : Z₂ ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk Z₂.hom (by simp) with hzdef
  have hcVZ : B.Contains (pullback pV (AlgebraicGeometry.blowUpToBase K ≫ pZ)) :=
    Scheme.size_pullback_lt _ _ V.left.property hcZ₂
  set VZ := BigFppfOver.mk B S hS hcVZ
    (pullback.fst pV (AlgebraicGeometry.blowUpToBase K ≫ pZ) ≫ pV) with hVZdef
  set prV' : VZ ⟶ V := BigFppfOver.homMk B S hS V.left.property _
    (pullback.fst pV (AlgebraicGeometry.blowUpToBase K ≫ pZ)) rfl with hprV'
  set prZ : VZ ⟶ Z₂ := BigFppfOver.homMk B S hS hcZ₂ _
    (pullback.snd pV (AlgebraicGeometry.blowUpToBase K ≫ pZ))
      (pullback.condition (f := pV) (g := AlgebraicGeometry.blowUpToBase K ≫ pZ)).symm
    with hprZ
  have hVZsite : IsPullback prV' prZ v z := by
    refine IsPullback.of_map F (tS.hom_ext _ _) ?_
    exact IsPullback.of_hasPullback pV (AlgebraicGeometry.blowUpToBase K ≫ pZ)
  set gZ : yoneda.obj Z₂ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) := yoneda.map z with hgZ
  have hφf : φ ≫ f = yoneda.map v := (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  have hVZ : IsPullback (yoneda.map prV') (yoneda.map prZ) (yoneda.map v) (yoneda.map z) :=
    hVZsite.map yoneda
  set β : yoneda.obj VZ ⟶ pullback f gZ :=
    pullback.lift (yoneda.map prV' ≫ φ) (yoneda.map prZ) (by
      rw [Category.assoc, hφf]; exact hVZ.w)
    with hβdef
  have hβ : IsPullback β (yoneda.map prV') (pullback.fst f gZ) φ := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f gZ).flip
    rw [pullback.lift_snd, hφf]
    exact hVZ.flip
  have hβZ : β ≫ pullback.snd f gZ = yoneda.map prZ := pullback.lift_snd _ _ _
  have := hjc
  have : Mono jc :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono (f := jc)).mp hjc |>.2
  have hcTc : B.Contains Tc :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact jc) hcVZ
  set Tc' := BigFppfOver.mk B S hS hcTc
    (jc ≫ pullback.fst pV (AlgebraicGeometry.blowUpToBase K ≫ pZ) ≫ pV) with hTc'
  set k : Tc' ⟶ VZ := BigFppfOver.homMk B S hS hcVZ _ jc rfl with hkdef
  have hFk : F.map k = jc := rfl
  have : Mono k := by
    have hm : Mono jc := inferInstance
    have : Mono (F.map k) := hm
    exact F.mono_of_mono_map this
  set h : UV ⟶ VZ := hVZsite.lift prV (prD ≫ j₂) (tS.hom_ext _ _) with hhdef
  have hFh : F.map h = pullback.lift p (q ≫ jD) (by
      rw [hpq, ← hι, ← hjDb]; simp only [Category.assoc]) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      show F.map h ≫ F.map prV' = _
      rw [← F.map_comp, hVZsite.lift_fst]
    · rw [pullback.lift_snd]
      show F.map h ≫ F.map prZ = _
      rw [← F.map_comp, hVZsite.lift_snd, F.map_comp, hFj₂]; rfl
  have hker : (F.map k).ker = (F.map h).ker := by
    rw [hFk, hFh]; exact hjcker
  set s : yoneda.obj D ⟶ pullback f gZ :=
    pullback.lift u (yoneda.map j₂) ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) with hsdef
  have hsq_h : IsPullback (yoneda.map prD) (yoneda.map h) s β := by
    refine IsPullback.of_bot ?_ ?_ hβ
    · rw [← yoneda.map_comp, hVZsite.lift_fst, pullback.lift_fst]
      exact hUV
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
          ← yoneda.map_comp, hVZsite.lift_fst]
        exact hUV.w
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← yoneda.map_comp,
          ← yoneda.map_comp, hVZsite.lift_snd]
  have hk : Subfunctor.range (yoneda.map k) = schemeTheoreticImageSubfunctor B S hS
      (pullback.snd s β) := by
    have : AlgebraicGeometry.IsClosedImmersion (F.map k) := hjc
    have hX2 : IsAlgebraicSpace B S hS (yoneda.obj VZ) := isAlgebraicSpace_yoneda B S hS VZ
    rw [schemeTheoreticImageSubfunctor_congr_range' B S hS (pullback.snd s β) (yoneda.map h) hX2
      (by
        have : Epi hsq_h.isoPullback.hom := IsIso.epi_of_iso hsq_h.isoPullback.hom
        rw [← hsq_h.isoPullback_hom_snd, Subfunctor.range_comp,
          Subfunctor.range_eq_top hsq_h.isoPullback.hom, Subfunctor.image_top]),
      schemeTheoreticImageSubfunctor_yoneda_map_eq_range h k hker]
  have hjDo : AlgebraicGeometry.IsOpenImmersion jD := by
    rw [hjD]
    have :
        AlgebraicGeometry.IsOpenImmersion (Stacks.Blowup.C1573.sectionOver ι.opensRange K hK) := by
      rw [Stacks.Blowup.C1573.sectionOver]; infer_instance
    have : AlgebraicGeometry.IsOpenImmersion ι.isoOpensRange.hom :=
      AlgebraicGeometry.IsOpenImmersion.of_isIso _
    infer_instance
  have hj₂o : AlgebraicGeometry.IsOpenImmersion (F.map j₂) := hjDo
  have hj₂qc : QuasiCompact (F.map j₂) := by
    rw [hFj₂]
    have : QuasiCompact (jD ≫ AlgebraicGeometry.blowUpToBase K) := by rw [hjDb]; infer_instance
    exact QuasiCompact.of_comp jD (AlgebraicGeometry.blowUpToBase K)
  have hj₂dom : IsSchemeTheoreticallyDominant (F.map j₂) := by
    show IsSchemeTheoreticallyDominant jD
    rw [hjD]
    obtain ⟨hcart, -⟩ := Stacks.Blowup.isTerminal_blowUp K
    have hcart' : Stacks.Divisors.IsEffectiveCartierDivisor
        (K.comap (AlgebraicGeometry.blowUpToBase K)) := hcart
    have heq : AlgebraicGeometry.blowUpToBase K ⁻¹ᵁ ι.opensRange =
        (K.comap (AlgebraicGeometry.blowUpToBase K)).support.compl := by
      ext y
      show AlgebraicGeometry.blowUpToBase K y ∈ ι.opensRange ↔
        y ∉ (K.comap (AlgebraicGeometry.blowUpToBase K)).support
      rw [Scheme.IdealSheafData.support_comap]
      show _ ↔ ¬ AlgebraicGeometry.blowUpToBase K y ∈ K.supportSet
      rw [hK]
      simp only [Set.mem_compl_iff, not_not]
      rfl
    have hd := Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _
      hcart'
    rw [← heq] at hd
    have h1 := Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense _ hd
    rw [Stacks.Blowup.C1573.sectionOver]
    have hiso := Stacks.Blowup.C1573.isIso_blowUpToBase_restrict ι.opensRange K hK
    have h4 : IsIso (ι.isoOpensRange.hom ≫
        @inv _ _ _ _ (AlgebraicGeometry.blowUpToBase K ∣_ ι.opensRange) hiso) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.inv_isIso _ _ _ _ _ hiso)
    have key : ∀ {A A' C : Scheme.{u}} (e : A ⟶ A') [IsIso e] (g : A' ⟶ C)
        [IsSchemeTheoreticallyDominant g], IsSchemeTheoreticallyDominant (e ≫ g) :=
      fun _ _ _ _ => inferInstance
    rw [← Category.assoc]
    exact @key _ _ _ _ h4 _ h1
  have hsqc : IsQuasiCompact B S hS s := by
    refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS s (pullback.snd f gZ)
      (isAlgebraicSpace_yoneda B S hS D) (isAlgebraicSpace_yoneda B S hS Z₂) ?_
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_pullback B S hS f gZ hsep))
    rw [hsdef, pullback.lift_snd]
    exact isQuasiCompact_yoneda_map B S hS j₂ hj₂qc
  have hTcflat : AlgebraicGeometry.Flat (F.map (k ≫ prZ)) := by
    rw [F.map_comp, hFk]
    exact hjcflat
  have hTopen := isOpenImmersion_schemeTheoreticImage_of_flat_chart X f hsep hlft gZ u j₂ hj₂o
    hj₂qc hj₂dom hsqc φ hφs hφe β prV' prZ hβ hβZ k hk hTcflat
  set T := schemeTheoreticImageSubfunctor B S hS s with hTdef
  have hrepT := hTopen.rep
  set T₀ := hrepT.pullback (𝟙 (yoneda.obj Z₂)) with hT₀def
  set o : T₀ ⟶ Z₂ := hrepT.snd (𝟙 (yoneda.obj Z₂)) with hodef
  have hpullT := hrepT.isPullback (𝟙 (yoneda.obj Z₂))
  have : IsIso (hrepT.fst (𝟙 (yoneda.obj Z₂))) := hpullT.isIso_fst_of_isIso
  set eT : yoneda.obj T₀ ≅ T.toFunctor := asIso (hrepT.fst (𝟙 (yoneda.obj Z₂))) with heTdef
  have heTo : eT.hom ≫ T.ι ≫ pullback.snd f gZ = yoneda.map o := by
    rw [heTdef, asIso_hom, hpullT.w, Category.comp_id]
  have hoopen : AlgebraicGeometry.IsOpenImmersion (F.map o) :=
    hTopen.property (𝟙 (yoneda.obj Z₂)) _ _ hpullT
  set τ : yoneda.obj T₀ ⟶ X.1 := eT.hom ≫ T.ι ≫ pullback.fst f gZ with hτdef
  set σ : D ⟶ T₀ := yoneda.preimage (toSchemeTheoreticImage B S hS s ≫ eT.inv) with hσdef
  have hσy : yoneda.map σ = toSchemeTheoreticImage B S hS s ≫ eT.inv := Functor.map_preimage _ _
  have hσu : yoneda.map σ ≫ τ = u := by
    rw [hσy, hτdef, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      toSchemeTheoreticImage_ι, pullback.lift_fst]
  have hσo : σ ≫ o = j₂ := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hσy, ← heTo, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      toSchemeTheoreticImage_ι, pullback.lift_snd]
  have hj₂b : j₂ ≫ b = j₀ := by
    apply F.map_injective
    rw [F.map_comp, hFj₂]
    exact hjDb
  have hY := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  have hXZ : IsAlgebraicSpace B S hS (pullback f gZ) :=
    isAlgebraicSpace_pullback B S hS f gZ X.2 (isAlgebraicSpace_yoneda B S hS Z₂) hY
  have hgZsep : IsSeparated B S hS gZ := by
    rw [hgZ, isSeparated_yoneda_map_iff]
    show _root_.AlgebraicGeometry.IsSeparated (AlgebraicGeometry.blowUpToBase K ≫ pZ)
    infer_instance
  have hfstsep : IsSeparated B S hS (pullback.fst f gZ) := by
    have h' := isSeparated_comp B S hS (pullbackSymmetry f gZ).hom (pullback.snd gZ f)
      (isSeparated_of_isIso B S hS _) (isSeparated_pullback B S hS gZ f hgZsep)
    rwa [pullbackSymmetry_hom_comp_snd] at h'
  have hsu : s ≫ pullback.fst f gZ = u := pullback.lift_fst _ _ _
  have hpbD := isPullback_toSchemeTheoreticImage_of_isOpenImmersion hXZ X.2 _ hfstsep u hu huqc
    s hsu
  have hτpb : ∀ {A Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ T.toFunctor} {r : A ⟶ Q}
      {g : Q ⟶ X.1}, IsPullback m r (T.ι ≫ pullback.fst f gZ) g →
      IsPullback (m ≫ eT.inv) r τ g := fun h =>
    h.of_iso (Iso.refl _) eT.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hτdef])
      (by simp)
  have hσpb : IsPullback (yoneda.map σ) (𝟙 _) τ u := hσy ▸ hτpb hpbD
  obtain ⟨χ, -, -, hχι, hχpb⟩ :=
    exists_chart_schemeTheoreticImage X f gZ s hsqc φ hφs hφe β prV' hβ k hk
  set pT : Tc' ⟶ T₀ := yoneda.preimage (χ ≫ eT.inv) with hpTdef
  have hpTy : yoneda.map pT = χ ≫ eT.inv := Functor.map_preimage _ _
  have hpTo : pT ≫ o = k ≫ prZ := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hpTy, ← heTo, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc, hχι, Category.assoc, hβZ]
  refine ⟨K, hKfp, hK, Z₂, T₀, Tc', b, Iso.refl _, o, τ, σ, pT, k ≫ prV', F.map k, rfl, hoopen,
    ?_, hσu, hσpb, ?_, hjc, ?_, ?_⟩
  · rw [← Category.assoc, hσo, hj₂b]
  · exact hpTy ▸ hτpb hχpb
  · rw [F.map_comp]; rfl
  · rw [hpTo, F.map_comp]; rfl

end AlgebraicGeometry.Space

end
