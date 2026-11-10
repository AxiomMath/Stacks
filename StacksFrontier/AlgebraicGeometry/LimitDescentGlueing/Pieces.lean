module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending the affine pieces of a scheme of finite presentation over a limit

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact, quasi-separated schemes with affine
transition morphisms, and let `X` be a quasi-compact scheme locally of finite presentation over
`S`.  This file descends the *affine pieces* of `X`: it produces a single stage `Sᵢ`, a finite
affine open cover of `X`, and for every member of that cover an affine scheme of finite
presentation over an affine open of `Sᵢ` whose base change to `S` is that member.

This is the first half of the source's proof of the essential-surjectivity half of Stacks Tag 0EY1,
equivalently of Stacks Tag 01ZM part (1).  The second half — descending the intersections of the
members of the cover, the identifications between the two descents of each intersection, and the
glueing itself — is not in this file, so neither tag is attached here; it is carried out in
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing`, which proves both tags.

Only quasi-separatedness of the stages is used, not their quasi-compactness: the source deduces
that `X` is quasi-compact from the quasi-compactness of `S`, while here quasi-compactness of `X` is
a hypothesis.

## Main results

* `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isAffineOpen`: the affine case of Tag 01ZM
  part (1) over **quasi-separated** stages: an affine scheme locally of finite presentation over
  `S` whose image lies in an affine open of `S` is the base change of an affine scheme of finite
  presentation over an affine open of a stage.  This removes the affineness of the stages, the
  hypothesis `∀ i, IsAffine (D.obj i)` of
  `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit`.
* `AlgebraicGeometry.exists_finite_isAffineOpen_cover`: a morphism with quasi-compact source
  admits a finite affine open cover of its source each member of which maps into an affine open of
  its target, as a family of `AlgebraicGeometry.Scheme.Opens`.
* `AlgebraicGeometry.exists_isPullback_baseChange_of_isAffineOpen`: a model over an affine open of
  a stage can be transported to any later stage.
* `AlgebraicGeometry.LimitDescent.exists_stage_isAffineModels`: the main result, as described
  above: all the affine pieces of `X` descend to **one** stage.
* `AlgebraicGeometry.exists_isPullback_of_isOpen_baseChange`: a quasi-compact open of a base
  change `S ×_{Sᵢ} Z` is itself the base change of a quasi-compact open of `S_j ×_{Sᵢ} Z` for some
  later stage `j`.  This is Tag 01Z4 (1) in the relative form the glueing step needs.
* `AlgebraicGeometry.baseChangeTransition_fst_isPullback`: the square comparing the base changes
  of a scheme over `S` to two stages is a pullback square over the transition morphism of the
  stages; a companion of `AlgebraicGeometry.baseChangeTransition_isPullback`.

## Implementation notes

The affine case over quasi-separated stages is obtained from the affine case over affine stages by
running the latter on Mathlib's `AlgebraicGeometry.opensDiagram`, the diagram of the preimages of
an affine open `Vᵢ ⊆ Sᵢ` in the later stages, whose limit is the preimage of `Vᵢ` in `S` by
`AlgebraicGeometry.isLimitOpensCone`.  Its index category is `CategoryTheory.Over i`, which is in
the scheme universe exactly when the index category is, so the result is stated for `I : Type u`
with `Category.{u} I`; that is also the shape in which it is used by
`AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`.

Each model is produced over an affine open `Vᵢ` of its stage rather than over the stage itself.
This is what makes the models transportable: the base change of the model along a transition
morphism `D.map a` is a pullback of affine schemes over the affine scheme `Vᵢ`, because `D.map a`
is affine and so `D.map a ⁻¹ᵁ Vᵢ` is affine again.  Over the stage itself the same base change
need not be affine.

## What the glueing adds

The source glues the whole cover at once, against a glueing datum indexed by pairs.  Two Mathlib
results make glueing *two* pieces at a time cheaper, and reduce Tag 01ZM part (1) to an induction
on the size of the cover:

* `CategoryTheory.Limits.HasPushout` holds for any two open immersions out of a common scheme, and
  the two maps into the pushout are open immersions covering it — this is Mathlib's
  `AlgebraicGeometry.Scheme.IsLocallyDirected` colimit, which applies to `span i₁ i₂` as soon as
  `i₁` and `i₂` are open immersions.  So no glueing datum, no `t'` and no cocycle condition is
  needed: the glued scheme is `pushout i₁ i₂`.
* `AlgebraicGeometry.Scheme.isPullback_of_openCover` says that a commuting square of schemes is a
  pullback square as soon as it is one after restricting along an open cover of its upper-right
  corner.  Applied to the cover of the glued scheme by its two pieces, this identifies the base
  change of the glued scheme with `X` without any statement that base change preserves the glueing
  colimit — which is just as well, since base change is a right adjoint and the library says
  nothing of the kind.

The induction is on the number of members of the cover, over the statement "a quasi-compact,
quasi-separated `X` of finite presentation over `S` covered by `n` opens each of which is the base
change of a scheme of finite presentation over a stage is itself such a base change".  The step
splits `X` as `A ∪ B` with `A` the union of the first `n - 1` members and `B` the last; `A ⊓ B` is
a quasi-compact open of `B`, so it descends by
`AlgebraicGeometry.exists_isPullback_of_isOpen_baseChange` — which is why the count does not grow
and the induction closes, where an induction over *affine* covers would not.  The uniqueness of a
descent up to a later stage, which identifies the two descents of `A ⊓ B`, is
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`, obtained from Tag 01ZM part (2) and
Tag 081E.

All of this is carried out in `StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing`.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01YZ](https://stacks.math.columbia.edu/tag/01YZ)
-/

@[expose] public section

universe u uI v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-! ### Two squares of base changes -/

/-- The square comparing the base changes of `X` to two stages `T` and `T'` over `S` is a pullback
square over the transition morphism `h : T' ⟶ T`: that is, `T' ×_S X = T' ×_T (T ×_S X)`.

This is the companion of `AlgebraicGeometry.baseChangeTransition_isPullback`, which compares the
base changes of a *morphism* over `S`. -/
public lemma baseChangeTransition_fst_isPullback {S T T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ S)
    (h : T' ⟶ T) (hg : h ≫ g = g') (X : Over S) :
    IsPullback (baseChangeTransition g g' h hg X) (pullback.fst g' X.hom)
      (pullback.fst g X.hom) h := by
  refine IsPullback.of_right (h₁₂ := pullback.snd g X.hom) ?_ (by simp)
    (IsPullback.of_hasPullback g X.hom).flip
  rw [baseChangeTransition_snd, hg]
  exact (IsPullback.of_hasPullback g' X.hom).flip

/-! ### Descending an open of the source to a later stage -/

section Opens

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]

namespace LimitDescent

/-- **Stacks Tag 01Z4 (1), relative to a model.**  A quasi-compact open of a scheme `X`
presented as the base change of `p : Y ⟶ Sᵢ` is cut out by a quasi-compact open of the base
change of `Y` to a later stage.  Nothing is assumed of the stages, and the index universes are
independent of the scheme universe. -/
public lemma exists_isOpen_model_of_initiallySmall {i : I} (hc : IsLimit c) {Y : Scheme.{u}}
    (p : Y ⟶ D.obj i) {X : Scheme.{u}} (f : X ⟶ c.pt) (g : X ⟶ Y)
    (hpb : IsPullback g f p (c.π.app i)) (U : X.Opens) (hU : IsCompact U.1) :
    ∃ (m : I) (a : m ⟶ i) (g' : X ⟶ pullback (D.map a) p) (V : (pullback (D.map a) p).Opens),
      IsPullback g' f (pullback.fst (D.map a) p) (c.π.app m) ∧
        g' ≫ pullback.snd (D.map a) p = g ∧ IsCompact V.1 ∧ g' ⁻¹ᵁ V = U := by
  have haff : ∀ {a b : Over i} (e : a ⟶ b),
      IsAffineHom ((baseChangeDiagram D i (Over.mk p)).map e) :=
    fun e => isAffineHom_baseChangeDiagram_map D i (Over.mk p) e
  set e := hpb.flip.isoPullback with he
  have hUe : ((e.inv ⁻¹ᵁ U : (pullback (c.π.app i) p).Opens) : Set _) = e.hom.base '' U.1 := by
    rw [Scheme.Hom.coe_preimage]
    ext y
    refine ⟨fun hy => ⟨e.inv.base y, hy, ?_⟩, ?_⟩
    · rw [← Scheme.Hom.comp_apply]
      simp
    · rintro ⟨x, hx, rfl⟩
      change e.inv.base (e.hom.base x) ∈ U.1
      rw [← Scheme.Hom.comp_apply]
      simpa using hx
  have key : ∃ (a : Over i) (V : (pullback (D.map a.hom) p).Opens)
      (t : pullback (c.π.app i) p ⟶ pullback (D.map a.hom) p), IsCompact V.1 ∧
        t ⁻¹ᵁ V = e.inv ⁻¹ᵁ U ∧ t ≫ pullback.snd (D.map a.hom) p = pullback.snd (c.π.app i) p ∧
          IsPullback t (pullback.fst (c.π.app i) p) (pullback.fst (D.map a.hom) p)
            (c.π.app a.left) := by
    obtain ⟨a, V, hVc, hVe⟩ := exists_preimage_eq_of_initiallySmall
      (baseChangeDiagram D i (Over.mk p)) (baseChangeCone D c i (Over.mk p))
      (baseChangeConeIsLimit D hc i (Over.mk p)) (e.inv ⁻¹ᵁ U) (hUe ▸ hU.image e.hom.continuous)
    exact ⟨a, V, baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp)
      (Over.mk p), hVc, hVe, baseChangeTransition_snd _ _ _ _ _,
      baseChangeTransition_fst_isPullback _ _ _ _ _⟩
  obtain ⟨a, V, t, hVc, hVe, hts, hbc⟩ := key
  refine ⟨a.left, a.hom, e.hom ≫ t, V, ?_, ?_, hVc, ?_⟩
  · refine hbc.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Category.comp_id _).symm ?_ (by simp) (by simp)
    rw [Iso.refl_hom, Category.comp_id, he]
    exact hpb.flip.isoPullback_hom_fst
  · rw [Category.assoc, hts, he]
    exact hpb.flip.isoPullback_hom_snd
  · rw [Scheme.Hom.comp_preimage, hVe, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
    simp

end LimitDescent

end Opens

/-! ### The affine case over quasi-separated stages -/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- **The affine case of Stacks Tag 01ZM part (1) over quasi-separated stages.**

Let `S = lim Sᵢ` be a cofiltered limit of quasi-separated schemes with affine transition morphisms
and let `X` be an affine scheme locally of finite presentation over `S` whose image lies in an
affine open `V ⊆ S`.  Then `X` is the base change of an affine scheme locally of finite
presentation over an affine open `Vᵢ` of one of the stages, and `V` is the preimage of `Vᵢ`.

The stages themselves are *not* assumed affine, which is what distinguishes this from
`AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit`; the affine open `V` of the limit is
descended first, by Tag 01Z4 (1), and the affine case over affine stages is then applied to the
diagram of its preimages in the later stages. -/
@[ega "IV 8.8.2" "special case"]
public theorem exists_isPullback_of_isAffine_of_isAffineOpen [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f]
    (V : c.pt.Opens) (hV : IsAffineOpen V) (hfV : Set.range f.base ⊆ V) :
    ∃ (i : I) (Vᵢ : (D.obj i).Opens) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ Vᵢ.toScheme) (g : X ⟶ Xᵢ),
      IsAffineOpen Vᵢ ∧ c.π.app i ⁻¹ᵁ Vᵢ = V ∧ IsAffine Xᵢ ∧
        LocallyOfFinitePresentation fᵢ ∧ IsPullback g f (fᵢ ≫ Vᵢ.ι) (c.π.app i) := by
  obtain ⟨i, Vi, hVi, hVie⟩ := exists_isAffineOpen_preimage_eq D c hc V hV
  subst hVie
  have hlim := isLimitOpensCone D c hc i Vi
  have h1 : ∀ j : Over i, IsAffine ((opensDiagram D i Vi).obj j) := fun j => hVi.preimage _
  have : IsAffine (opensCone D c i Vi).pt := hV
  obtain ⟨f', hpb0⟩ : ∃ f' : X ⟶ (opensCone D c i Vi).pt,
      IsPullback (𝟙 X) f' f (c.π.app i ⁻¹ᵁ Vi).ι := by
    have hr : Set.range f.base ⊆ Set.range (c.π.app i ⁻¹ᵁ Vi).ι.base := by simpa using hfV
    exact ⟨_, (IsOpenImmersion.isPullback_lift_id f (c.π.app i ⁻¹ᵁ Vi).ι hr).flip⟩
  have hf' : f' ≫ (c.π.app i ⁻¹ᵁ Vi).ι = f := by simpa using hpb0.w.symm
  have hfp' : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb0 inferInstance
  obtain ⟨j, Xj, fj, g, haff, hfp, hpb⟩ :=
    exists_isPullback_of_isAffine_of_isLimit (opensDiagram D i Vi) (opensCone D c i Vi) hlim f'
  have hr' : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ Vi) = c.π.app i ⁻¹ᵁ Vi := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hpb2 : IsPullback
      ((c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ Vi) (c.π.app i ⁻¹ᵁ Vi) hr'.ge)
      (c.π.app i ⁻¹ᵁ Vi).ι (D.map j.hom ⁻¹ᵁ Vi).ι (c.π.app j.left) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [hr'])
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ Vi, Xj, fj, g, hVi.preimage _, hr', haff, hfp, ?_⟩
  have h := hpb.paste_vert hpb2
  rwa [hf'] at h

/-! ### Affine charts as opens -/

/-- A morphism with quasi-compact source admits a finite affine open cover of its source each
member of which maps into an affine open of its target.

This is `AlgebraicGeometry.exists_finite_affine_charts` phrased with
`AlgebraicGeometry.Scheme.Opens` and `AlgebraicGeometry.IsAffineOpen`, which is the form that
Tag 01Z4 (1) consumes. -/
public theorem exists_finite_isAffineOpen_cover {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens) (V : J → S.Opens), IsOpenCover U ∧
      ∀ k, IsAffineOpen (U k) ∧ IsAffineOpen (V k) ∧
        Set.range ((U k).ι ≫ f).base ⊆ (V k : Set S) := by
  obtain ⟨C, hCfin, hCaff, V, b, p, hVaff, hbimm, hw⟩ := exists_finite_affine_charts f
  refine ⟨C.I₀, hCfin, fun k => (C.f k).opensRange, fun k => (b k).opensRange,
    C.isOpenCover_opensRange, fun k => ⟨isAffineOpen_opensRange _, isAffineOpen_opensRange _, ?_⟩⟩
  have h1 : Set.range ((C.f k).opensRange.ι ≫ f).base = Set.range ((C.f k) ≫ f).base := by
    simp [Scheme.Hom.comp_base, Set.range_comp]
  rw [h1, ← hw k]
  rintro x ⟨y, rfl⟩
  exact ⟨(p k).base y, by simp⟩

/-! ### Transporting a model to a later stage -/

/-- A model over an affine open of a stage transports to any later stage: if `X` is the base change
to `S` of an affine scheme `Xᵢ` of finite presentation over an affine open `Vᵢ` of the stage
`D.obj i`, then for every `a : m ⟶ i` it is also the base change of an affine scheme of finite
presentation over the affine open `D.map a ⁻¹ᵁ Vᵢ` of `D.obj m`.

Affineness is preserved because `D.map a` is an affine morphism, so `D.map a ⁻¹ᵁ Vᵢ` is affine and
the transported model is a pullback of affine schemes over the affine scheme `Vᵢ`. -/
public theorem exists_isPullback_baseChange_of_isAffineOpen
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i m : I} (a : m ⟶ i) {Vᵢ : (D.obj i).Opens} (hVᵢ : IsAffineOpen Vᵢ)
    {Xᵢ : Scheme.{u}} (hXᵢ : IsAffine Xᵢ) (fᵢ : Xᵢ ⟶ Vᵢ.toScheme)
    (hfᵢ : LocallyOfFinitePresentation fᵢ)
    {X : Scheme.{u}} (f : X ⟶ c.pt) (g : X ⟶ Xᵢ)
    (hpb : IsPullback g f (fᵢ ≫ Vᵢ.ι) (c.π.app i)) :
    ∃ (Xₘ : Scheme.{u}) (fₘ : Xₘ ⟶ (D.map a ⁻¹ᵁ Vᵢ).toScheme) (g' : X ⟶ Xₘ),
      IsAffine Xₘ ∧ LocallyOfFinitePresentation fₘ ∧
        IsPullback g' f (fₘ ≫ (D.map a ⁻¹ᵁ Vᵢ).ι) (c.π.app m) := by
  have := hXᵢ
  have := hfᵢ
  have hVm : IsAffineOpen (D.map a ⁻¹ᵁ Vᵢ) := hVᵢ.preimage _
  have : IsAffine Vᵢ.toScheme := hVᵢ
  have : IsAffine (D.map a ⁻¹ᵁ Vᵢ).toScheme := hVm
  set ρ := (D.map a).resLE Vᵢ (D.map a ⁻¹ᵁ Vᵢ) le_rfl with hρ
  have hO : IsPullback ρ (D.map a ⁻¹ᵁ Vᵢ).ι Vᵢ.ι (D.map a) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp [hρ]) (by simp)
  have hR : IsPullback (pullback.fst fᵢ ρ) (pullback.snd fᵢ ρ) fᵢ ρ := .of_hasPullback _ _
  have hs : IsPullback g f (fᵢ ≫ Vᵢ.ι) (c.π.app m ≫ D.map a) := by rwa [c.w a]
  exact ⟨pullback fᵢ ρ, pullback.snd fᵢ ρ, _, inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hR inferInstance,
    hs.of_right' (hR.paste_vert hO)⟩

/-! ### Descending a quasi-compact open of a base change -/

/-- **Stacks Tag 01Z4 (1), relative to a stage.**  A quasi-compact open of the base change
`S ×_{Sᵢ} Z` of a scheme `Z` over a stage is the base change of a quasi-compact open of
`S_j ×_{Sᵢ} Z` for some later stage `j`, compatibly with the structure morphisms to the stages.

This is Mathlib's `AlgebraicGeometry.exists_preimage_eq` applied to the diagram of base changes of
`Z` to the later stages, whose limit is `S ×_{Sᵢ} Z` by Tag 01YZ
(`AlgebraicGeometry.baseChangeConeIsLimit`). -/
public theorem exists_isPullback_of_isOpen_baseChange [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) (Z : Over (D.obj i)) (W : (pullback (c.π.app i) Z.hom).Opens) (hW : IsCompact W.1) :
    ∃ (a : Over i) (W' : (pullback (D.map a.hom) Z.hom).Opens) (g : W.toScheme ⟶ W'.toScheme),
      IsCompact W'.1 ∧
        IsPullback g (W.ι ≫ pullback.fst (c.π.app i) Z.hom)
          (W'.ι ≫ pullback.fst (D.map a.hom) Z.hom) (c.π.app a.left) := by
  have haff : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i Z).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i Z g
  obtain ⟨a, W', hW'c, hW'e⟩ := exists_preimage_eq (baseChangeDiagram D i Z)
    (baseChangeCone D c i Z) (baseChangeConeIsLimit D hc i Z) W hW
  subst hW'e
  have hbc : IsPullback ((baseChangeCone D c i Z).π.app a) (pullback.fst (c.π.app i) Z.hom)
      (pullback.fst (D.map a.hom) Z.hom) (c.π.app a.left) :=
    baseChangeTransition_fst_isPullback (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Z
  exact ⟨a, W', _, hW'c,
    (isPullback_morphismRestrict ((baseChangeCone D c i Z).π.app a) W').paste_vert hbc⟩

namespace LimitDescent

/-! ### All the affine pieces at one stage -/

/-- **The affine pieces of a scheme of finite presentation over a cofiltered limit descend to a
single stage.**

Let `S = lim Sᵢ` be a cofiltered limit of quasi-separated schemes with affine transition
morphisms, and let `X` be a quasi-compact scheme locally of finite presentation over `S`.  Then
there is one stage `i`, a finite affine open cover `U` of `X`, affine opens `V k ⊆ S` and
`Vᵢ k ⊆ Sᵢ` with `V k` the preimage of `Vᵢ k`, and affine schemes `Xᵢ k` locally of finite
presentation over `Vᵢ k`, such that each `U k` is the base change of `Xᵢ k` to `S`.

This is the first half of the source's proof of the essential-surjectivity half of Stacks Tag 0EY1
(equivalently of Tag 01ZM part (1)); the glueing of the pieces is carried out in
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing`, where the tag is attached. -/
public theorem exists_stage_isAffineModels [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (J : Type u) (_ : Finite J) (U : J → X.Opens) (V : J → c.pt.Opens)
      (Vᵢ : J → (D.obj i).Opens) (Xᵢ : J → Scheme.{u})
      (fᵢ : ∀ k, Xᵢ k ⟶ (Vᵢ k).toScheme) (g : ∀ k, (U k).toScheme ⟶ Xᵢ k),
      IsOpenCover U ∧ ∀ k, IsAffineOpen (U k) ∧ IsAffineOpen (V k) ∧ IsAffineOpen (Vᵢ k) ∧
        IsAffine (Xᵢ k) ∧ c.π.app i ⁻¹ᵁ Vᵢ k = V k ∧ LocallyOfFinitePresentation (fᵢ k) ∧
        IsPullback (g k) ((U k).ι ≫ f) (fᵢ k ≫ (Vᵢ k).ι) (c.π.app i) := by
  classical
  obtain ⟨J, hJ, U, V, hcov, hUV⟩ := exists_finite_isAffineOpen_cover f
  have : Finite J := hJ
  have : Fintype J := Fintype.ofFinite J
  have step : ∀ k, ∃ (i : I) (Vᵢ : (D.obj i).Opens) (Xᵢ : Scheme.{u})
      (fᵢ : Xᵢ ⟶ Vᵢ.toScheme) (g : (U k).toScheme ⟶ Xᵢ),
      IsAffineOpen Vᵢ ∧ c.π.app i ⁻¹ᵁ Vᵢ = V k ∧ IsAffine Xᵢ ∧
        LocallyOfFinitePresentation fᵢ ∧
        IsPullback g ((U k).ι ≫ f) (fᵢ ≫ Vᵢ.ι) (c.π.app i) := by
    intro k
    have : IsAffine (U k).toScheme := (hUV k).1
    have : LocallyOfFinitePresentation ((U k).ι ≫ f) :=
      MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    exact exists_isPullback_of_isAffine_of_isAffineOpen D c hc ((U k).ι ≫ f) (V k)
      (hUV k).2.1 (hUV k).2.2
  choose ix Vx Xx fx gx hVx hVex hXx hfx hpx using step
  obtain ⟨m, am⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image ix)
  replace am : ∀ k, m ⟶ ix k := fun k => (am (by simp)).some
  have step2 : ∀ k, ∃ (Xₘ : Scheme.{u}) (fₘ : Xₘ ⟶ (D.map (am k) ⁻¹ᵁ Vx k).toScheme)
      (g' : (U k).toScheme ⟶ Xₘ), IsAffine Xₘ ∧ LocallyOfFinitePresentation fₘ ∧
        IsPullback g' ((U k).ι ≫ f) (fₘ ≫ (D.map (am k) ⁻¹ᵁ Vx k).ι) (c.π.app m) := fun k =>
    exists_isPullback_baseChange_of_isAffineOpen D c (am k) (hVx k) (hXx k) (fx k) (hfx k)
      ((U k).ι ≫ f) (gx k) (hpx k)
  choose Xm fm gm hXm hfm hpm using step2
  refine ⟨m, J, hJ, U, V, fun k => D.map (am k) ⁻¹ᵁ Vx k, Xm, fm, gm, hcov, fun k =>
    ⟨(hUV k).1, (hUV k).2.1, (hVx k).preimage _, hXm k, ?_, hfm k, hpm k⟩⟩
  rw [← Scheme.Hom.comp_preimage, c.w, hVex k]

end LimitDescent

end AlgebraicGeometry
