module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CompletelyDecomposed.FiniteCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Complete decomposition descends to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
locally finitely presented morphism over one stage whose target is quasi-compact and
quasi-separated, and which becomes completely decomposed after base change to the limit, is
already completely decomposed after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_isCompletelyDecomposed_baseChange_of_limitBaseChange` descends
  complete decomposition from the inverse limit to a finite stage.

## Implementation notes

Schemes over the chosen stage and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` expresses that `i` is a stage later than
`i₀` in the cofiltered indexing category. This is the categorical form of the source's directed
indexing set.

Over the limit, the morphism admits a finite surjective cover of its target by finitely presented
immersions along each of which it has a section. Every member of that cover is the base change of
a finitely presented scheme over some stage; each member is an immersion already at some stage,
and carries its section at some stage. Since the indexing category is cofiltered and the cover is
finite, one later stage realizes all of this at once, and surjectivity of the resulting finite
family of immersions descends too. A surjective family of immersions admitting sections forces
complete decomposition, because an immersion induces isomorphisms on residue fields.

Diagrams indexed by the slice category over a stage are used throughout: the schemes at the stages
later than a fixed one, together with the transition morphisms between them, form such a diagram,
and the slice category over the stage is again cofiltered.

## References

* [Stacks Project, Tag 0GTM](https://stacks.math.columbia.edu/tag/0GTM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is completely decomposed as soon as its target is covered by a finite
surjective family of immersions along each of which the morphism admits a section. The section
lifts a point of the target to a point of the source, and the residue field extension there is
trivial because it is a retract of the trivial extension induced by the immersion. -/
private lemma isCompletelyDecomposed_of_surjective_family_with_sections
    {n : ℕ} {W : Fin n → Scheme.{u}} {X Y : Scheme.{u}}
    (g : ∀ i, W i ⟶ Y) (f : X ⟶ Y)
    (hcover : Surjective (Sigma.desc g))
    (himm : ∀ i, IsImmersion (g i))
    (hsections : ∀ i, ∃ s : W i ⟶ pullback f (g i),
      s ≫ pullback.snd f (g i) = 𝟙 (W i)) :
    IsCompletelyDecomposed f := by
  intro y
  obtain ⟨z, hz⟩ := (Sigma.desc g).surjective y
  obtain ⟨i, x, hzx⟩ : ∃ i, ∃ x : W i, Sigma.ι W i x = z := by
    have hcov := (sigmaOpenCover W).exists_eq z
    dsimp only [sigmaOpenCover, Scheme.Cover.copy] at hcov
    exact hcov
  obtain ⟨s, hs⟩ := hsections i
  let t : W i ⟶ X := s ≫ pullback.fst f (g i)
  have hz' : g i x = y := by
    rw [← hzx] at hz
    simpa [← Scheme.Hom.comp_apply] using hz
  have hfg : t ≫ f = g i := by
    show s ≫ pullback.fst f (g i) ≫ f = g i
    rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hty : f (t x) = y := by
    show (t ≫ f) x = y
    rwa [hfg]
  have hcomp : IsIso ((t ≫ f).residueFieldMap x) := by
    have : IsImmersion (g i) := himm i
    rw [hfg]
    exact isIso_residueFieldMap_of_isPreimmersion (g i) x
  rw [Scheme.residueFieldMap_comp] at hcomp
  let α := f.residueFieldMap (t x)
  let β := t.residueFieldMap x
  have hαβ : IsIso (α ≫ β) := hcomp
  have hbij := (ConcreteCategory.isIso_iff_bijective (α ≫ β)).mp hαβ
  have hβsurj : Function.Surjective β.hom := by
    intro z
    obtain ⟨w, hw⟩ := hbij.2 z
    exact ⟨α.hom w, by simpa [α, β, Function.comp_apply] using hw⟩
  have hβinj : Function.Injective β.hom := RingHom.injective _
  have : IsIso β := (ConcreteCategory.isIso_iff_bijective β).2 ⟨hβinj, hβsurj⟩
  exact ⟨t x, hty, (isIso_comp_right_iff α β).mp hαβ⟩

/-- The underlying topological space of a finite coproduct of schemes is the disjoint union of
the underlying spaces. -/
private noncomputable def finiteSigmaHomeomorph {n : ℕ} (f : Fin n → Scheme.{u}) :
    (Σ i, f i) ≃ₜ (∐ f :) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

/-- A disjoint union of finitely many quasi-separated spaces is quasi-separated. -/
private lemma quasiSeparatedSpace_finite_sigma
    {ι : Type*} [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, QuasiSeparatedSpace (X i)] : QuasiSeparatedSpace (Σ i, X i) := by
  constructor
  intro U V hU hUc hV hVc
  have h (i : ι) : IsCompact (Sigma.mk i ⁻¹' (U ∩ V)) := by
    rw [Set.preimage_inter]
    exact QuasiSeparatedSpace.inter_isCompact _ _
      (isOpen_sigma_iff.mp hU i)
      (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc)
      (isOpen_sigma_iff.mp hV i)
      (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hVc)
  have hc := Set.isCompact_sigma (s := Set.univ) (t := fun i => Sigma.mk i ⁻¹' (U ∩ V))
    Set.finite_univ (fun i _ => h i)
  convert hc using 1
  ext x
  simp

/-- A property of morphisms stable under isomorphism holds for the structure morphism of an
object of a slice category exactly when it holds for that of an isomorphic object. -/
private lemma property_over_iso_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y : Scheme.{u}} {A B : Over Y} (e : A ≅ B) : P A.hom ↔ P B.hom := by
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget Y) e.hom
  rw [← e.hom.w]
  exact P.cancel_left_of_respectsIso e.hom.left B.hom

/-- Base change along a composite agrees with the two successive base changes. -/
private lemma property_pullback_comp_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    P ((Over.pullback (f ≫ g)).obj W).hom ↔
      P ((Over.pullback f).obj ((Over.pullback g).obj W)).hom :=
  property_over_iso_iff P ((Over.pullbackComp f g).app W)

/-- Base changing the morphism from an object of a slice category to the terminal object of that
slice category gives, up to isomorphism, the structure morphism of the base-changed object. -/
private lemma property_baseChange_to_identity_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (W : Over X) :
    P (((Over.pullback f).map
      (Over.homMk W.hom (by simp) : W ⟶ Over.mk (𝟙 X))).left) ↔
      P ((Over.pullback f).obj W).hom := by
  let q := (Over.pullback f).map
    (Over.homMk W.hom (by simp) : W ⟶ Over.mk (𝟙 X))
  have : IsIso ((Over.pullback f).obj (Over.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) f))
  rw [← q.w]
  exact (P.cancel_right_of_respectsIso q.left _).symm

/-- Base change preserves morphisms of finite presentation. -/
private lemma finitePresentation_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : FinitePresentation f) : FinitePresentation (pullback.snd f g) := by
  have := hf.1
  have := hf.2.1
  have := hf.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Base change preserves morphisms of finite presentation. -/
private lemma finitePresentation_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hg : FinitePresentation g) : FinitePresentation (pullback.fst f g) := by
  have := hg.1
  have := hg.2.1
  have := hg.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The source of a morphism of finite presentation to a quasi-compact scheme is quasi-compact. -/
private lemma compactSpace_of_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    (hf : FinitePresentation f) : CompactSpace X :=
  have := hf.2.1
  QuasiCompact.compactSpace_of_compactSpace f

/-- The source of a morphism of finite presentation to a quasi-separated scheme is
quasi-separated. -/
private lemma quasiSeparatedSpace_of_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiSeparatedSpace Y] (hf : FinitePresentation f) : QuasiSeparatedSpace X :=
  have := hf.2.2
  quasiSeparatedSpace_of_quasiSeparated f

/-- A finitely presented scheme over a stage of a cofiltered system of quasi-compact and
quasi-separated schemes with affine transition morphisms whose base change to the limit is
surjective over the limit is already surjective over some later stage. -/
private lemma exists_surjective_pullback_snd
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (W : Over (D.obj i)) (hW : FinitePresentation W.hom)
    (h : Surjective ((Over.pullback (c.π.app i)).obj W).hom) :
    ∃ (j : I) (g : j ⟶ i), Surjective ((Over.pullback (D.map g)).obj W).hom := by
  let D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  let c' : Cone D' := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have : ∀ {j k : Over i} (g : j ⟶ k), IsAffineHom (D'.map g) :=
    fun g => inferInstanceAs (IsAffineHom (D.map g.left))
  have : ∀ j : Over i, CompactSpace (D'.obj j) :=
    fun j => inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace (D'.obj j) :=
    fun j => inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  obtain ⟨a⟩ := IsCofiltered.nonempty (C := Over i)
  let W' := (Over.pullback (D.map a.hom)).obj W
  have hW' : FinitePresentation W'.hom := finitePresentation_pullback_snd _ _ hW
  have : CompactSpace W'.left := compactSpace_of_finitePresentation W'.hom hW'
  have : QuasiSeparatedSpace W'.left := quasiSeparatedSpace_of_finitePresentation W'.hom hW'
  let f' : W' ⟶ Over.mk (𝟙 (D'.obj a)) := Over.homMk W'.hom (by simp)
  have : LocallyOfFinitePresentation f'.left := hW'.1
  have hlim : Surjective ((Over.pullback (c'.π.app a)).obj W').hom := by
    apply (property_pullback_comp_iff @Surjective.{u} _ _ W).mp
    show Surjective ((Over.pullback (c.π.app a.left ≫ D.map a.hom)).obj W).hom
    rwa [c.w]
  have : Surjective ((Over.pullback (c'.π.app a)).map f').left :=
    (property_baseChange_to_identity_iff @Surjective.{u} _ W').mpr hlim
  have : CompactSpace (Over.mk (𝟙 (D'.obj a))).left :=
    inferInstanceAs (CompactSpace (D'.obj a))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D'.obj a))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D'.obj a))
  obtain ⟨j, g, hg⟩ :=
    exists_surjective_baseChange_of_surjective_limitBaseChange
      D' c' hc' a W' (Over.mk (𝟙 (D'.obj a))) f'
  refine ⟨j.left, g.left ≫ a.hom, ?_⟩
  rw [D.map_comp]
  exact (property_pullback_comp_iff @Surjective.{u} _ _ W).mpr
    ((property_baseChange_to_identity_iff @Surjective.{u} (D'.map g) W').mp hg)

/-- **Stacks Project, Tag 0GTM.** Let a scheme be the limit of a cofiltered inverse system of
schemes with affine transition morphisms, and let a locally finitely presented morphism over one
stage have quasi-compact, quasi-separated target. If its base change to the limit is completely
decomposed, then its base change to some later stage is completely decomposed. -/
@[stacks 0GTM]
theorem exists_isCompletelyDecomposed_baseChange_of_limitBaseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hf : IsCompletelyDecomposed ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀),
      IsCompletelyDecomposed ((Over.pullback (S.map g)).map f₀).left := by
  classical
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app S c hc i₀
  have : MorphismProperty.IsStableUnderBaseChange @IsAffineHom.{u} :=
    isAffineHom_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom.{u}) Y₀.hom :=
    ⟨fun pb h => isAffineHom_isStableUnderBaseChange.of_isPullback pb h⟩
  have : IsAffineHom (pullback.fst Y₀.hom (c.π.app i₀)) :=
    MorphismProperty.pullback_fst _ _ (isAffineHom_π_app S c hc i₀)
  have : CompactSpace ((Over.pullback (c.π.app i₀)).obj Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst Y₀.hom (c.π.app i₀))
  have : MorphismProperty.IsStableUnderBaseChange @QuasiSeparated.{u} :=
    quasiSeparated_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiSeparated.{u}) Y₀.hom :=
    ⟨fun pb h => quasiSeparated_isStableUnderBaseChange.of_isPullback pb h⟩
  have : QuasiSeparated (pullback.fst Y₀.hom (c.π.app i₀)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparatedSpace ((Over.pullback (c.π.app i₀)).obj Y₀).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst Y₀.hom (c.π.app i₀))
  let fLim := ((Over.pullback (c.π.app i₀)).map f₀).left
  have : MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation.{u} :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have : LocallyOfFinitePresentation fLim :=
    MorphismProperty.overPullbackMap (c.π.app i₀) f₀ (by infer_instance)
  -- The inverse system of base changes of `Y₀` to the stages later than `i₀`.
  let D : Over i₀ ⥤ Scheme.{u} :=
    Over.post S ⋙ Over.pullback Y₀.hom ⋙ Over.forget Y₀.left
  let pD (a : Over i₀) : D.obj a ⟶ Y₀.left :=
    pullback.snd (S.map a.hom) Y₀.hom
  have hpD {a b : Over i₀} (q : a ⟶ b) : D.map q ≫ pD b = pD a :=
    Over.w ((Over.pullback Y₀.hom).map ((Over.post S).map q))
  let cD : Cone D :=
    (Over.pullback Y₀.hom ⋙ Over.forget Y₀.left).mapCone
      ((Over.conePost S i₀).obj c)
  have hcD : IsLimit cD :=
    isLimitOfPreserves (Over.pullback Y₀.hom ⋙ Over.forget Y₀.left)
      (Over.isLimitConePost i₀ hc)
  have hDaff (a : Over i₀) :
      IsAffineHom ((Over.pullback Y₀.hom).obj ((Over.post S).obj a)).hom := by
    apply MorphismProperty.pullback_snd
    show IsAffineHom (S.map a.hom)
    infer_instance
  have hDcompact : ∀ a : Over i₀, CompactSpace (D.obj a) := fun a =>
    have := hDaff a
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback Y₀.hom).obj ((Over.post S).obj a)).hom
  have hDqs : ∀ a : Over i₀, QuasiSeparatedSpace (D.obj a) := fun a =>
    have := hDaff a
    quasiSeparatedSpace_of_quasiSeparated ((Over.pullback Y₀.hom).obj ((Over.post S).obj a)).hom
  have hDaffine {a b : Over i₀} (q : a ⟶ b) : IsAffineHom (D.map q) := by
    dsimp [D]
    have hq : IsAffineHom ((Over.post S).map q).left := by
      show IsAffineHom (S.map q.left)
      infer_instance
    exact MorphismProperty.overPullbackMap (P := @IsAffineHom.{u}) Y₀.hom
      ((Over.post S).map q) hq
  have : ∀ a : Over i₀, CompactSpace (D.obj a) := hDcompact
  have : ∀ a : Over i₀, QuasiSeparatedSpace (D.obj a) := hDqs
  have : ∀ {a b : Over i₀} (q : a ⟶ b), IsAffineHom (D.map q) := hDaffine
  -- Tag 0GTL: a finite surjective cover of the limit target by finitely presented immersions
  -- along each of which the base change to the limit has a section.
  obtain ⟨n, Z, g, hsurj, himm, hfp, hsections⟩ :=
    exists_finite_immersion_cover_with_sections fLim hf
  let β : cD.pt ≅ ((Over.pullback (c.π.app i₀)).obj Y₀).left :=
    pullbackSymmetry (c.π.app i₀) Y₀.hom
  -- Tag 01ZM: each member of the cover is the base change of a finitely presented scheme over
  -- some stage.
  have hmodel (k : Fin n) :
      ∃ (a : Over i₀) (W : Over (D.obj a)),
        FinitePresentation W.hom ∧
          Nonempty ((Over.mk (g k ≫ β.inv) : Over cD.pt) ≅
            (Over.pullback (cD.π.app a)).obj W) :=
    let Zobj : Over cD.pt := Over.mk (g k ≫ β.inv)
    have hZfp : FinitePresentation Zobj.hom := by
      show FinitePresentation (g k ≫ β.inv)
      refine ⟨?_, ?_, ?_⟩
      · have : LocallyOfFinitePresentation (g k) := (hfp k).1
        infer_instance
      · have : QuasiCompact (g k) := (hfp k).2.1
        infer_instance
      · have : QuasiSeparated (g k) := (hfp k).2.2
        infer_instance
    LimitFPObjectDescent.exists_model_of_finitePresentation D cD hcD Zobj hZfp
  choose a W hWfp hWiso using hmodel
  let Yk (k : Fin n) : Over (D.obj (a k)) := Over.mk (𝟙 (D.obj (a k)))
  let fStage (k : Fin n) : W k ⟶ Yk k := Over.homMk (W k).hom (by simp [Yk])
  let Wdiagram (k : Fin n) : Over (a k) ⥤ Scheme.{u} :=
    Over.post D ⋙ Over.pullback (W k).hom ⋙ Over.forget (W k).left
  let pY (k : Fin n) : D.obj (a k) ⟶ Y₀.left :=
    ((Over.pullback Y₀.hom).obj ((Over.post S).obj (a k))).hom
  let tW (k : Fin n) : Wdiagram k ⟶ (Functor.const (Over (a k))).obj Y₀.left :=
    { app b := pullback.snd (D.map b.hom) (W k).hom ≫ (W k).hom ≫ pY k
      naturality := by
        intro b₁ b₂ q
        let φ := (Over.pullback (W k).hom).map ((Over.post D).map q)
        let U₁ := (Over.pullback (W k).hom).obj ((Over.post D).obj b₁)
        let U₂ := (Over.pullback (W k).hom).obj ((Over.post D).obj b₂)
        show φ.left ≫ U₂.hom ≫ (W k).hom ≫ pY k =
          U₁.hom ≫ (W k).hom ≫ pY k
        exact congrArg (fun z => z ≫ (W k).hom ≫ pY k) (Over.w φ) }
  have hWcompact (k : Fin n) : CompactSpace (W k).left :=
    compactSpace_of_finitePresentation (W k).hom (hWfp k)
  have hWqs (k : Fin n) : QuasiSeparatedSpace (W k).left :=
    quasiSeparatedSpace_of_finitePresentation (W k).hom (hWfp k)
  -- Tag 01ZC: the section over the limit descends to a morphism to `X₀` over `Y₀` at a stage.
  have hsectionStage (k : Fin n) :
      ∃ (b : Over (a k)) (r : (Wdiagram k).obj b ⟶ X₀.left),
        r ≫ f₀.left = (tW k).app b := by
    let Jk := Over (a k)
    let cW : Cone (Wdiagram k) :=
      (Over.pullback (W k).hom ⋙ Over.forget (W k).left).mapCone
        ((Over.conePost D (a k)).obj cD)
    have hcW : IsLimit cW :=
      isLimitOfPreserves (Over.pullback (W k).hom ⋙ Over.forget (W k).left)
        (Over.isLimitConePost (a k) hcD)
    let v := pullbackSymmetry (cD.π.app (a k)) (W k).hom
    let e := Classical.choice (hWiso k)
    let s := Classical.choose (hsections k)
    have hs : s ≫ pullback.snd fLim (g k) = 𝟙 (Z k) :=
      Classical.choose_spec (hsections k)
    let aW : cW.pt ⟶ X₀.left :=
      v.hom ≫ e.inv.left ≫ s ≫ pullback.fst fLim (g k) ≫
        pullback.fst X₀.hom (c.π.app i₀)
    have hsbase : s ≫ pullback.fst fLim (g k) ≫ fLim = g k := by
      calc
        s ≫ pullback.fst fLim (g k) ≫ fLim =
            s ≫ (pullback.fst fLim (g k) ≫ fLim) := rfl
        _ = s ≫ (pullback.snd fLim (g k) ≫ g k) := by rw [pullback.condition]
        _ = g k := by simp [← Category.assoc, hs]
    have hbase : fLim ≫ pullback.fst Y₀.hom (c.π.app i₀) =
        pullback.fst X₀.hom (c.π.app i₀) ≫ f₀.left := by
      dsimp [fLim]
      exact pullback.lift_fst _ _ _
    have he : e.inv.left ≫ (g k ≫ β.inv) =
        pullback.snd (W k).hom (cD.π.app (a k)) := Over.w e.inv
    have heY : e.inv.left ≫ g k =
        pullback.snd (W k).hom (cD.π.app (a k)) ≫ β.hom := by
      calc
        e.inv.left ≫ g k = (e.inv.left ≫ g k ≫ β.inv) ≫ β.hom := by
          simp [Category.assoc]
        _ = pullback.snd (W k).hom (cD.π.app (a k)) ≫ β.hom := by rw [he]
    have hpYlim : cD.π.app (a k) ≫ pY k =
        pullback.snd (c.π.app i₀) Y₀.hom := by
      dsimp [pY, cD]
      dsimp [Over.conePost, Over.pullback]
      exact pullback.lift_snd _ _ _
    have hβfst : β.hom ≫ pullback.fst Y₀.hom (c.π.app i₀) =
        pullback.snd (c.π.app i₀) Y₀.hom := by
      show (pullbackSymmetry (c.π.app i₀) Y₀.hom).hom ≫ _ = _
      exact pullbackSymmetry_hom_comp_fst _ _
    let top : Over (a k) := Over.mk (𝟙 (a k))
    have htopL : (cW.π.app top) ≫ (tW k).app top =
        pullback.fst (cD.π.app (a k)) (W k).hom ≫ cD.π.app (a k) ≫ pY k := by
      let φ := (Over.pullback (W k).hom).map
        (((Over.conePost D (a k)).obj cD).π.app top)
      have hφ : φ.left ≫ pullback.snd (D.map (𝟙 (a k))) (W k).hom =
          pullback.snd (cD.π.app (a k)) (W k).hom := Over.w φ
      show (φ.left ≫ pullback.snd (D.map (𝟙 (a k))) (W k).hom) ≫
          ((W k).hom ≫ pY k) =
        (pullback.fst (cD.π.app (a k)) (W k).hom ≫ cD.π.app (a k)) ≫ pY k
      rw [hφ]
      exact congrArg (fun q => q ≫ pY k)
        (pullback.condition (f := cD.π.app (a k)) (g := (W k).hom)).symm
    have htopR : v.hom ≫ e.inv.left ≫ g k ≫ pullback.fst Y₀.hom (c.π.app i₀) =
        pullback.fst (cD.π.app (a k)) (W k).hom ≫ cD.π.app (a k) ≫ pY k := by
      show (v.hom ≫ (e.inv.left ≫ g k)) ≫ pullback.fst Y₀.hom (c.π.app i₀) =
        (pullback.fst (cD.π.app (a k)) (W k).hom ≫ cD.π.app (a k)) ≫ pY k
      rw [heY]
      show (v.hom ≫ pullback.snd (W k).hom (cD.π.app (a k))) ≫
          (β.hom ≫ pullback.fst Y₀.hom (c.π.app i₀)) =
        (pullback.fst (cD.π.app (a k)) (W k).hom ≫ cD.π.app (a k)) ≫ pY k
      rw [pullbackSymmetry_hom_comp_snd, hβfst, ← hpYlim]
      cat_disch
    have htop : (cW.π.app top) ≫ (tW k).app top =
        v.hom ≫ e.inv.left ≫ g k ≫ pullback.fst Y₀.hom (c.π.app i₀) :=
      htopL.trans htopR.symm
    have haW : cW.π ≫ tW k = (Functor.const _).map (aW ≫ f₀.left) := by
      ext b
      have htop' : (cW.π.app top) ≫ (tW k).app top = aW ≫ f₀.left := by
        rw [htop]
        have haux : e.inv.left ≫ g k ≫ pullback.fst Y₀.hom (c.π.app i₀) =
            e.inv.left ≫ s ≫ pullback.fst fLim (g k) ≫
              pullback.fst X₀.hom (c.π.app i₀) ≫ f₀.left := by
          calc
            e.inv.left ≫ g k ≫ pullback.fst Y₀.hom (c.π.app i₀) =
                e.inv.left ≫ (s ≫ pullback.fst fLim (g k) ≫ fLim) ≫
                  pullback.fst Y₀.hom (c.π.app i₀) := by rw [hsbase]
            _ = e.inv.left ≫ s ≫ pullback.fst fLim (g k) ≫
                  (fLim ≫ pullback.fst Y₀.hom (c.π.app i₀)) := by simp [Category.assoc]
            _ = e.inv.left ≫ s ≫ pullback.fst fLim (g k) ≫
                  (pullback.fst X₀.hom (c.π.app i₀) ≫ f₀.left) := by rw [hbase]
            _ = e.inv.left ≫ s ≫ pullback.fst fLim (g k) ≫
                  pullback.fst X₀.hom (c.π.app i₀) ≫ f₀.left := rfl
        rw [haux]
        dsimp [aW]
        cat_disch
      have hbt : b ⟶ top := Over.homMk b.hom (by simp [top])
      have hnat : (Wdiagram k).map hbt ≫ (tW k).app top = (tW k).app b :=
        ((tW k).naturality hbt).trans (Category.comp_id _)
      calc
        cW.π.app b ≫ (tW k).app b =
            cW.π.app b ≫ (Wdiagram k).map hbt ≫ (tW k).app top := by
              rw [← hnat]
        _ = cW.π.app top ≫ (tW k).app top := by
              rw [← Category.assoc, cW.w hbt]
        _ = aW ≫ f₀.left := htop'
    have hWdiagramFP (b : Jk) : FinitePresentation (pullback.fst (D.map b.hom) (W k).hom) :=
      finitePresentation_pullback_fst _ _ (hWfp k)
    have : ∀ b : Jk, CompactSpace ((Wdiagram k).obj b) := fun b =>
      compactSpace_of_finitePresentation (pullback.fst (D.map b.hom) (W k).hom) (hWdiagramFP b)
    have : ∀ b : Jk, QuasiSeparatedSpace ((Wdiagram k).obj b) := fun b =>
      quasiSeparatedSpace_of_finitePresentation (pullback.fst (D.map b.hom) (W k).hom)
        (hWdiagramFP b)
    have : ∀ {b₁ b₂ : Jk} (q : b₁ ⟶ b₂), IsAffineHom ((Wdiagram k).map q) := by
      intro b₁ b₂ q
      have hq : IsAffineHom ((Over.post D).map q).left := hDaffine q.left
      exact MorphismProperty.overPullbackMap (P := @IsAffineHom.{u}) (W k).hom
        ((Over.post D).map q) hq
    obtain ⟨b, r, -, hr⟩ :=
      Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        (Wdiagram k) (tW k) f₀.left cW hcW aW haW
    exact ⟨b, r, hr⟩
  -- Tag 0GTB: each member of the cover is already an immersion at some stage.
  have hImmStage (k : Fin n) :
      ∃ (b : Over (a k)),
        IsImmersion (((Over.pullback (D.map b.hom)).map (fStage k))).left := by
    let Jk := Over (a k)
    let Dk : Jk ⥤ Scheme.{u} := Over.post D ⋙ Over.forget (D.obj (a k))
    let ck : Cone Dk :=
      (Over.forget (D.obj (a k))).mapCone ((Over.conePost D (a k)).obj cD)
    have hck : IsLimit ck :=
      isLimitOfPreserves (Over.forget (D.obj (a k)))
        (Over.isLimitConePost (a k) hcD)
    have : ∀ b : Jk, CompactSpace (Dk.obj b) := fun b => hDcompact b.left
    have : ∀ b : Jk, QuasiSeparatedSpace (Dk.obj b) := fun b => hDqs b.left
    have : ∀ {b₁ b₂ : Jk} (q : b₁ ⟶ b₂), IsAffineHom (Dk.map q) :=
      fun q => hDaffine q.left
    have : CompactSpace (Yk k).left := hDcompact (a k)
    have : QuasiSeparatedSpace (Yk k).left := hDqs (a k)
    have : LocallyOfFiniteType (fStage k).left := by
      have : LocallyOfFinitePresentation (W k).hom := (hWfp k).1
      show LocallyOfFiniteType (W k).hom
      infer_instance
    have hlim : IsImmersion ((Over.pullback (ck.π.app (Over.mk (𝟙 (a k))))).map
        (fStage k)).left := by
      let e := Classical.choice (hWiso k)
      let hGD : IsImmersion (g k ≫ β.inv) := by
        have : IsImmersion (g k) := himm k
        infer_instance
      let fLimStage := (Over.pullback (cD.π.app (a k))).map (fStage k)
      let targetMap := pullback.snd (𝟙 (D.obj (a k))) (cD.π.app (a k))
      have : IsIso e.hom.left := Functor.map_isIso (Over.forget cD.pt) e.hom
      have : IsIso targetMap := inferInstance
      have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      have hrel : g k ≫ β.inv = e.hom.left ≫ fLimStage.left ≫ targetMap := by
        calc
          g k ≫ β.inv = e.hom.left ≫ ((Over.pullback (cD.π.app (a k))).obj (W k)).hom :=
            e.hom.w.symm
          _ = e.hom.left ≫ fLimStage.left ≫
              ((Over.pullback (cD.π.app (a k))).obj (Yk k)).hom := by
            rw [← fLimStage.w]
          _ = e.hom.left ≫ fLimStage.left ≫ targetMap := rfl
      have hComp : IsImmersion (e.hom.left ≫ fLimStage.left ≫ targetMap) := by
        rw [← hrel]
        exact hGD
      have hlim1 : IsImmersion (fLimStage.left ≫ targetMap) :=
        (MorphismProperty.cancel_left_of_respectsIso
          (P := @IsImmersion.{u}) e.hom.left _).mp hComp
      have hlim' : IsImmersion fLimStage.left :=
        (MorphismProperty.cancel_right_of_respectsIso
          (P := @IsImmersion.{u}) fLimStage.left targetMap).mp hlim1
      have hleg : ck.π.app (Over.mk (𝟙 (a k))) = cD.π.app (a k) := by
        dsimp [ck, Over.conePost]
        rfl
      rw [hleg]
      exact hlim'
    obtain ⟨b, hi, hb⟩ :=
      exists_isImmersion_baseChange_of_isLimit
        Dk ck hck (Over.mk (𝟙 (a k))) (W k) (Yk k) (fStage k)
    have hiEq : Over.Hom.left hi = b.hom := by simpa using hi.w
    have hmap : Dk.map hi = D.map b.hom := by
      show D.map (Over.Hom.left hi) = D.map b.hom
      rw [hiEq]
    exact ⟨b, by
      rw [← hmap]
      exact hb⟩
  have : MorphismProperty.RespectsIso (@IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- A single stage over which a given member of the cover is both an immersion and carries its
  -- section.
  have hBothStage (k : Fin n) :
      ∃ (b : Over (a k)),
        IsImmersion (((Over.pullback (D.map b.hom)).map (fStage k))).left ∧
        ∃ r : ((Over.pullback (D.map b.hom)).obj (W k)).left ⟶ X₀.left,
          r ≫ f₀.left = ((Over.pullback (D.map b.hom)).obj (W k)).hom ≫
            D.map b.hom ≫ pY k := by
    obtain ⟨bi, hbi⟩ := hImmStage k
    obtain ⟨bs, rs, hrs⟩ := hsectionStage k
    let b := IsCofiltered.min bi bs
    let qi := IsCofiltered.minToLeft bi bs
    let qs := IsCofiltered.minToRight bi bs
    have hbi' := (property_baseChange_to_identity_iff @IsImmersion.{u} _ _).mp hbi
    have hi : IsImmersion ((Over.pullback (D.map b.hom)).obj (W k)).hom := by
      have heq : D.map b.hom = D.map qi.left ≫ D.map bi.hom := by
        rw [← D.map_comp, Over.w qi]
      rw [heq]
      apply (property_pullback_comp_iff @IsImmersion.{u} _ _ _).mpr
      have := hbi'
      exact inferInstanceAs (IsImmersion (pullback.snd _ (D.map qi.left)))
    refine ⟨b, (property_baseChange_to_identity_iff @IsImmersion.{u} _ _).mpr hi,
      (pullbackSymmetry (W k).hom (D.map b.hom)).hom ≫
        (Wdiagram k).map qs ≫ rs, ?_⟩
    have hcomp : ((Wdiagram k).map qs ≫ rs) ≫ f₀.left =
        (Wdiagram k).map qs ≫ (tW k).app bs :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f : (Wdiagram k).obj bs ⟶ Y₀.left =>
          (Wdiagram k).map qs ≫ f) hrs)
    have hstep :
        ((pullbackSymmetry (W k).hom (D.map b.hom)).hom ≫
          ((Wdiagram k).map qs ≫ rs)) ≫ f₀.left =
        (pullbackSymmetry (W k).hom (D.map b.hom)).hom ≫
          ((Wdiagram k).map qs ≫ (tW k).app bs) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => (pullbackSymmetry (W k).hom (D.map b.hom)).hom ≫ f) hcomp)
    rw [hstep]
    have hnat : (Wdiagram k).map qs ≫ (tW k).app bs = (tW k).app b :=
      ((tW k).naturality qs).trans (Category.comp_id _)
    refine (congrArg (fun f =>
      (pullbackSymmetry (W k).hom (D.map b.hom)).hom ≫ f) hnat).trans ?_
    dsimp [tW, Wdiagram, Over.post]
    simp only [pullbackSymmetry_hom_comp_snd_assoc]
    rw [pullback.condition_assoc]
  choose b hb rB hrB using hBothStage
  -- One stage dominating all the finitely many stages just produced.
  let top : Over i₀ := Over.mk (𝟙 i₀)
  let toTop (k : Fin n) : (b k).left ⟶ top :=
    Over.homMk (b k).left.hom (by cat_disch)
  obtain ⟨m, -, q, -⟩ := IsCofiltered.wideCospan toTop
  let Wb (k : Fin n) : Over (D.obj (b k).left) :=
    (Over.pullback (D.map (b k).hom)).obj (W k)
  let Wm (k : Fin n) : Over (D.obj m) :=
    (Over.pullback (D.map (q k))).obj (Wb k)
  have hImmWb (k : Fin n) : IsImmersion (Wb k).hom :=
    (property_baseChange_to_identity_iff @IsImmersion.{u} _ _).mp (hb k)
  have hImmWm (k : Fin n) : IsImmersion (Wm k).hom := by
    have := hImmWb k
    exact inferInstanceAs (IsImmersion (pullback.snd (Wb k).hom (D.map (q k))))
  have hWmFP (k : Fin n) : FinitePresentation (Wm k).hom :=
    finitePresentation_pullback_snd _ _ (finitePresentation_pullback_snd _ _ (hWfp k))
  let rM (k : Fin n) : (Wm k).left ⟶ X₀.left :=
    pullback.fst (Wb k).hom (D.map (q k)) ≫ rB k
  have hrM (k : Fin n) : rM k ≫ f₀.left = (Wm k).hom ≫ pD m := by
    dsimp [rM]
    rw [Category.assoc, hrB]
    show pullback.fst (Wb k).hom (D.map (q k)) ≫
        (Wb k).hom ≫ D.map (b k).hom ≫ pD (a k) = _
    rw [pullback.condition_assoc, hpD, hpD]
    rfl
  let zM (k : Fin n) : Z k ⟶ (Wm k).left := by
    let e := Classical.choice (hWiso k)
    let zW := e.hom.left ≫ pullback.fst (W k).hom (cD.π.app (a k))
    have hzW : zW ≫ (W k).hom = (g k ≫ β.inv) ≫ cD.π.app (a k) := by
      dsimp [zW]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun t => t ≫ cD.π.app (a k)) (Over.w e.hom)
    let zB : Z k ⟶ (Wb k).left := pullback.lift zW
      ((g k ≫ β.inv) ≫ cD.π.app (b k).left) (by
        simpa only [Category.assoc, cD.w] using hzW)
    exact pullback.lift zB ((g k ≫ β.inv) ≫ cD.π.app m) (by
      dsimp [zB, Wb]
      simp only [pullback.lift_snd, Category.assoc, cD.w])
  have hzM (k : Fin n) : zM k ≫ (Wm k).hom = (g k ≫ β.inv) ≫ cD.π.app m :=
    pullback.lift_snd _ _ _
  let F : (∐ fun k => (Wm k).left) ⟶ D.obj m := Sigma.desc (fun k => (Wm k).hom)
  have hFlim : Surjective (pullback.snd F (cD.π.app m)) := by
    let l (k : Fin n) : Z k ⟶ pullback F (cD.π.app m) :=
      pullback.lift (zM k ≫ Sigma.ι (fun k => (Wm k).left) k) (g k ≫ β.inv) (by
        simpa [F, Category.assoc] using hzM k)
    have heq : Sigma.desc l ≫ pullback.snd F (cD.π.app m) = Sigma.desc g ≫ β.inv := by
      apply Sigma.hom_ext
      intro k
      simp only [Sigma.ι_desc_assoc]
      exact pullback.lift_snd _ _ _
    have : Surjective (Sigma.desc g) := hsurj
    have : Surjective (Sigma.desc l ≫ pullback.snd F (cD.π.app m)) := by
      rw [heq]
      infer_instance
    exact Surjective.of_comp (Sigma.desc l) _
  have hcompact (k : Fin n) : CompactSpace (Wm k).left :=
    compactSpace_of_finitePresentation (Wm k).hom (hWmFP k)
  have hqs (k : Fin n) : QuasiSeparatedSpace (Wm k).left :=
    quasiSeparatedSpace_of_finitePresentation (Wm k).hom (hWmFP k)
  have : CompactSpace (∐ fun k => (Wm k).left : Scheme.{u}) :=
    (finiteSigmaHomeomorph (fun k => (Wm k).left)).compactSpace
  have : QuasiSeparatedSpace (Σ k, (Wm k).left) := quasiSeparatedSpace_finite_sigma
  have : QuasiSeparatedSpace (∐ fun k => (Wm k).left : Scheme.{u}) :=
    (quasiSeparatedSpace_congr (finiteSigmaHomeomorph (fun k => (Wm k).left))).mp inferInstance
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have hFfp : FinitePresentation F :=
    ⟨IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation.{u})
      (f := fun k => (Wm k).hom) (fun k => (hWmFP k).1), inferInstance, inferInstance⟩
  -- Tag 07RR: the finite family is already surjective at some stage.
  obtain ⟨j, e, he⟩ := exists_surjective_pullback_snd D cD hcD m (Over.mk F) hFfp hFlim
  let V (k : Fin n) := pullback (Wm k).hom (D.map e)
  let v (k : Fin n) : V k ⟶ D.obj j := pullback.snd (Wm k).hom (D.map e)
  have hv : Surjective (Sigma.desc v) := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := (@Scheme.Hom.surjective _ _ (pullback.snd F (D.map e)) he) y
    obtain ⟨k, x, hx⟩ := (sigmaOpenCover (fun k => (Wm k).left)).exists_eq
      (pullback.fst F (D.map e) z)
    have hxy : (Wm k).hom x = D.map e y := by
      have hh := congrArg (fun t : pullback F (D.map e) ⟶ D.obj m => t z)
        (pullback.condition (f := F) (g := D.map e))
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz, ← hx] at hh
      change F (Sigma.ι (fun k => (Wm k).left) k x) = D.map e y at hh
      have hι : Sigma.ι (fun k => (Wm k).left) k ≫ F = (Wm k).hom := Sigma.ι_desc _ _
      have hιx := congrArg (fun f : (Wm k).left ⟶ D.obj m => f x) hι
      change F (Sigma.ι (fun k => (Wm k).left) k x) = (Wm k).hom x at hιx
      exact hιx.symm.trans hh
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    refine ⟨Sigma.ι V k w, ?_⟩
    have hι : Sigma.ι V k ≫ Sigma.desc v = v k := Sigma.ι_desc _ _
    exact (congrArg (fun f : V k ⟶ D.obj j => f w) hι).trans hw
  let δ : D.obj j ≅ ((Over.pullback (S.map j.hom)).obj Y₀).left :=
    pullbackSymmetry (S.map j.hom) Y₀.hom
  let v' (k : Fin n) := v k ≫ δ.hom
  let r (k : Fin n) : V k ⟶ X₀.left := pullback.fst (Wm k).hom (D.map e) ≫ rM k
  have hr (k : Fin n) : r k ≫ f₀.left = v k ≫ pD j := by
    dsimp [r]
    rw [Category.assoc, hrM, pullback.condition_assoc, hpD]
  let t (k : Fin n) : V k ⟶ ((Over.pullback (S.map j.hom)).obj X₀).left :=
    pullback.lift (r k) (v k ≫ pullback.fst (S.map j.hom) Y₀.hom) (by
      rw [← f₀.w, ← Category.assoc, hr]
      have hcond : pD j ≫ Y₀.hom =
          pullback.fst (S.map j.hom) Y₀.hom ≫ S.map j.hom := by
        show pullback.snd (S.map j.hom) Y₀.hom ≫ Y₀.hom =
          pullback.fst (S.map j.hom) Y₀.hom ≫ S.map j.hom
        exact (pullback.condition).symm
      calc
        _ = v k ≫ (pD j ≫ Y₀.hom) := Category.assoc _ _ _
        _ = v k ≫ (pullback.fst (S.map j.hom) Y₀.hom ≫ S.map j.hom) :=
          congrArg (fun f : D.obj j ⟶ S.obj i₀ => v k ≫ f) hcond
        _ = (v k ≫ pullback.fst (S.map j.hom) Y₀.hom) ≫ S.map j.hom :=
          (Category.assoc _ _ _).symm)
  let fj := ((Over.pullback (S.map j.hom)).map f₀).left
  have hpDδ : pD j = δ.hom ≫ pullback.fst Y₀.hom (S.map j.hom) :=
    (pullbackSymmetry_hom_comp_fst (S.map j.hom) Y₀.hom).symm
  have ht (k : Fin n) : t k ≫ fj = v' k := by
    apply pullback.hom_ext
    · simpa only [fj, Over.pullback_map_left, t, v', δ, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_fst]
        using (hr k).trans (congrArg (fun f : D.obj j ⟶ Y₀.left => v k ≫ f) hpDδ)
    · simp only [fj, Over.pullback_map_left, t, v', δ, Category.assoc,
        pullback.lift_snd]
      exact (congrArg (fun f : D.obj j ⟶ S.obj j.left => v k ≫ f)
        (pullbackSymmetry_hom_comp_snd (S.map j.hom) Y₀.hom)).symm
  refine ⟨j.left, j.hom, isCompletelyDecomposed_of_surjective_family_with_sections v' fj
    ?_ ?_ ?_⟩
  · have : Surjective (Sigma.desc v) := hv
    have heq : Sigma.desc v' = Sigma.desc v ≫ δ.hom := by
      apply Sigma.hom_ext
      intro k
      simp [v']
    rw [heq]
    infer_instance
  · intro k
    have : IsImmersion (Wm k).hom := hImmWm k
    have : IsImmersion (v k) := inferInstanceAs
      (IsImmersion (pullback.snd (Wm k).hom (D.map e)))
    dsimp [v']
    infer_instance
  · intro k
    exact ⟨pullback.lift (t k) (𝟙 _) (by simpa using ht k), pullback.lift_snd _ _ _⟩

end AlgebraicGeometry
