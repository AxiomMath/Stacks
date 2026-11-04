module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed subschemes of a cofiltered limit descend to a finite stage

Let `D` be a cofiltered diagram of quasi-compact, quasi-separated schemes with affine transition
morphisms and let `S' = lim D`. A closed subscheme of `S'` whose structure morphism is of finite
presentation is the base change of a closed subscheme of some `D i`.

Also recorded here is that the scheme-theoretic image of a quasi-compact morphism out of an
integral scheme is integral, and that a closed subscheme obtained as a base change may be
replaced by the scheme-theoretic image of the given closed subscheme without changing the base
change.

## Main definitions

* `AlgebraicGeometry.baseChangeImageIso` — the identification of a closed subscheme `Z ⊆ X'`,
  known to be the base change along `q : X' ⟶ X` of a closed subscheme of `X`, with the base
  change of the scheme-theoretic image of `Z ⟶ X' ⟶ X`.

## Main results

* `AlgebraicGeometry.isIntegral_image_of_isIntegral` — the scheme-theoretic image of a
  quasi-compact morphism out of an integral scheme is integral.
* `AlgebraicGeometry.exists_closedImmersion_model_of_isLimit` — a closed subscheme of finite
  presentation of a cofiltered limit is the base change of a closed subscheme of a stage.

## Implementation notes

The descent of the closed subscheme combines the descent of the scheme itself, Stacks 01ZM part
(1), with the fact that a morphism becoming a closed immersion over the limit is already a
closed immersion at a later stage, Stacks 01ZP. The latter is about a morphism between two
objects over a stage, so the closed immersion `Z_i ⟶ D i` is read as a morphism from `Z_i` to
the terminal object `D i` of the category of schemes over `D i`, whose base changes are
isomorphisms.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

/-! ### The scheme-theoretic image of a morphism out of an integral scheme -/

/-- The scheme-theoretic image of a quasi-compact morphism out of an integral scheme is reduced:
on an affine open of the image the ring of functions injects into a ring of functions on the
source, which is a domain when the open is met and is subsingleton otherwise. -/
@[ega "I 9.5.9" "(i), (ii)"]
theorem isReduced_image_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] : IsReduced f.image := by
  have hcov : TopologicalSpace.IsOpenCover (fun U : Y.affineOpens => f.imageι ⁻¹ᵁ U.1) :=
    f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  refine (IsReduced.iff_of_openCover f.image (f.image.openCoverOfIsOpenCover _ hcov)).2 fun U ↦ ?_
  show IsReduced (((f.imageι ⁻¹ᵁ U.1 : f.image.Opens) : Scheme))
  let V : f.image.Opens := f.imageι ⁻¹ᵁ U.1
  have hVaff : IsAffine V.toScheme := U.2.preimage f.imageι
  have hred : _root_.IsReduced Γ(f.image, V) := by
    by_cases hV : Nonempty V
    · have hW : Nonempty (f.toImage ⁻¹ᵁ V) := by
        have hdense : Dense (Set.range f.toImage.base) := f.toImage.denseRange
        obtain ⟨_, ⟨x, rfl⟩, hxV⟩ := hdense.exists_mem_open V.2 (Set.nonempty_coe_sort.mp hV)
        exact ⟨⟨x, hxV⟩⟩
      have : _root_.IsDomain Γ(X, f.toImage ⁻¹ᵁ V) := inferInstance
      exact isReduced_of_injective (f.toImage.app V).hom (f.toImage_app_injective U)
    · have hVbot : V = ⊥ := by
        ext x
        exact ⟨fun hx ↦ (hV ⟨⟨x, hx⟩⟩).elim, fun hx ↦ False.elim hx⟩
      have hsub : Subsingleton Γ(f.image, V) := by
        rw [hVbot]
        exact CommRingCat.subsingleton_of_isTerminal (f.image.sheaf.isTerminalOfEqEmpty rfl)
      infer_instance
  have hredtop : _root_.IsReduced Γ(V.toScheme, ⊤) :=
    isReduced_of_injective (Scheme.Opens.topIso V).hom.hom
      (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced V.toScheme

/-- The scheme-theoretic image of a quasi-compact morphism out of an integral scheme is
irreducible: its underlying space is the closure of the image of an irreducible space. -/
@[ega "I 9.5.9" "partial"]
theorem irreducibleSpace_image_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] : IrreducibleSpace f.image := by
  have hrange : IsIrreducible (Set.range f.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image f.base f.continuous.continuousOn
  have hr : IsIrreducible (Set.range f.imageι.base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
    exact hrange.closure
  let e : f.image ≃ₜ Set.range f.imageι.base :=
    (IsPreimmersion.isEmbedding f.imageι).toHomeomorph
  have : IrreducibleSpace (Set.range f.imageι.base) := isIrreducible_iff_irreducibleSpace.mp hr
  exact e.symm.surjective.irreducibleSpace e.symm.continuous

/-- The scheme-theoretic image of a quasi-compact morphism out of an integral scheme is
integral. -/
theorem isIntegral_image_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] : IsIntegral f.image := by
  have := isReduced_image_of_isIntegral f
  have := irreducibleSpace_image_of_isIntegral f
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

/-! ### Replacing a model by a scheme-theoretic image -/

/-- Let `q : X' ⟶ X` be a morphism, let `Z ⊆ X'` be a closed subscheme which is the base change
along `q` of a closed subscheme `W ⊆ X`, and let `V ⊆ X` be the scheme-theoretic image of
`Z ⟶ X' ⟶ X`. Then `Z` is also the base change of `V`.

Indeed `V ⊆ W`, since `Z ⟶ X' ⟶ X` factors through `W`, so the base change of `V` sits between
`Z` and the base change of `W`, which is `Z`. -/
def baseChangeImageIso {X X' : Scheme.{u}} (q : X' ⟶ X) (Z : Over X') [IsClosedImmersion Z.hom]
    (W : Over X) [IsClosedImmersion W.hom] (e : Z ≅ (Over.pullback q).obj W) :
    Z ≅ (Over.pullback q).obj (Over.mk (Z.hom ≫ q).imageι) := by
  have hk : W.hom.ker ≤ (Z.hom ≫ q).imageι.ker := by
    change W.hom.ker ≤ (Z.hom ≫ q).ker.subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    have hg : (e.hom.left ≫ pullback.fst W.hom q) ≫ W.hom = Z.hom ≫ q := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact e.hom.w =≫ q
    rw [← hg]
    exact Scheme.Hom.le_ker_comp _ _
  let V : Over X := Over.mk (Z.hom ≫ q).imageι
  let i : V ⟶ W := Over.homMk (IsClosedImmersion.lift W.hom (Z.hom ≫ q).imageι hk)
    (IsClosedImmersion.lift_fac _ _ _)
  let a : Z ⟶ (Over.pullback q).obj V :=
    Over.homMk (pullback.lift (Z.hom ≫ q).toImage Z.hom (Z.hom ≫ q).toImage_imageι)
      (pullback.lift_snd _ _ _)
  let b : (Over.pullback q).obj V ⟶ Z := (Over.pullback q).map i ≫ e.inv
  refine { hom := a, inv := b, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply Over.OverMorphism.ext
    exact (cancel_mono Z.hom).1 <| (a ≫ b).w.trans (Over.w (𝟙 Z)).symm
  · apply Over.OverMorphism.ext
    have : Mono ((Over.pullback q).obj V).hom := by
      change Mono (pullback.snd (Z.hom ≫ q).imageι q)
      infer_instance
    exact (cancel_mono ((Over.pullback q).obj V).hom).1 <|
      (b ≫ a).w.trans (Over.w (𝟙 ((Over.pullback q).obj V))).symm

/-! ### Descent of a closed subscheme -/

/-- **Descent of a closed subscheme to a finite stage.** A closed subscheme of finite
presentation of a cofiltered limit of quasi-compact, quasi-separated schemes with affine
transition morphisms is the base change of a closed subscheme of some stage.

The underlying scheme descends by Stacks 01ZM part (1); the resulting morphism to the stage is
locally of finite type and becomes a closed immersion over the limit, hence is a closed
immersion at a later stage by Stacks 01ZP. -/
theorem exists_closedImmersion_model_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (Z : Over c.pt) [IsClosedImmersion Z.hom] (hZ : FinitePresentation Z.hom) :
    ∃ (i : I) (Y : Over (D.obj i)), IsClosedImmersion Y.hom ∧
      Nonempty (Z ≅ (Over.pullback (c.π.app i)).obj Y) := by
  obtain ⟨i, Y, hY, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc Z hZ
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated Y.hom := hY.2.2
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let T : Over (D.obj i) := Over.mk (𝟙 _)
  have : CompactSpace T.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace T.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have hT {V : Scheme.{u}} (q : V ⟶ D.obj i) : IsIso ((Over.pullback q).obj T).hom := by
    show IsIso (pullback.snd (𝟙 (D.obj i)) q)
    infer_instance
  let f : Y ⟶ T := Over.homMk Y.hom (by simp [T])
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType Y.hom)
  have hlim : IsClosedImmersion ((Over.pullback (c.π.app i)).obj Y).hom := by
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget c.pt).map e.inv))
    rw [show ((Over.pullback (c.π.app i)).obj Y).hom = e.inv.left ≫ Z.hom from e.inv.w.symm]
    infer_instance
  have : IsClosedImmersion ((Over.pullback (c.π.app i)).map f).left := by
    have := hT (c.π.app i)
    have : IsClosedImmersion (((Over.pullback (c.π.app i)).map f).left ≫
        ((Over.pullback (c.π.app i)).obj T).hom) := by
      rw [((Over.pullback (c.π.app i)).map f).w]
      exact hlim
    exact IsClosedImmersion.of_comp _ ((Over.pullback (c.π.app i)).obj T).hom
  obtain ⟨j, g, hg⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit D c hc i Y T f
  have hclosed : IsClosedImmersion ((Over.pullback (D.map g)).obj Y).hom := by
    have := hT (D.map g)
    rw [← ((Over.pullback (D.map g)).map f).w]
    infer_instance
  exact ⟨j, (Over.pullback (D.map g)).obj Y, hclosed,
    ⟨e ≪≫ eqToIso (congrArg (fun h ↦ (Over.pullback h).obj Y) (c.w g).symm) ≪≫
      (Over.pullbackComp (c.π.app j) (D.map g)).app Y⟩⟩

end AlgebraicGeometry

end
