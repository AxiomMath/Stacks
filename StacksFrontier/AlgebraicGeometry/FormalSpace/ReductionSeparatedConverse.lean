module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Thickenings.MonoClosedImmersion

/-!
# Separatedness of the reduction gives the affine-intersection condition

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. This file proves the implication (1) ⟹ (2) of **Stacks 0AJ6**, the converse of the
implication proved in `StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated`, and
assembles the two into the equivalence the tag asserts, for the reduction that Stacks 0AIN
produces.

The argument is the one of the source. Let `U`, `V` be objects of the site with affine
underlying scheme, let `h_U ⟶ X`, `h_V ⟶ X` be two morphisms and let `Q` be an object of the
site representing the fibre product. Replacing `U` and `V` by their reductions, which map to the
reduction of `X` by its universal property, produces an object `P` of the site representing
`U_red ×_{X_red} V_red = U_red ×_X V_red`, and `P ⟶ Q` is a thickening of schemes, being a
composition of two base changes of the thickenings `U_red ⟶ U` and `V_red ⟶ V`. The
affine-intersection condition for the reduction says exactly that `P ⟶ U_red ×_{Spec ℤ} V_red`
is a closed immersion, hence so is `P ⟶ U ×_{Spec ℤ} V`, the two thickenings being closed
immersions of affine schemes.

What remains is the implication for schemes: a monomorphism locally of finite type into an
affine scheme which is a closed immersion on a thickening of its source is a closed immersion.
That is `AlgebraicGeometry.isClosedImmersion_of_isThickening_of_mono`, and the two properties it
needs of `Q ⟶ U ×_{Spec ℤ} V` come from Stacks 0AIP for an arbitrary formal algebraic space: the
morphism `Q ⟶ U ×_S V` of the site assembled from the two projections is a represented base
change of the diagonal of `X`, so it is a monomorphism and locally of finite type, and the
canonical morphism `U ×_S V ⟶ U ×_{Spec ℤ} V` is an immersion, being a base change of the
diagonal of the base (Stacks 01KR).

## Main results

* `AlgebraicGeometry.surjective_globalSectionsTensorLift_comp`: the map on global sections
  attached to a pair of morphisms stays surjective after composing both of them with morphisms
  surjective on global sections.
* `AlgebraicGeometry.FormalSpace.hasAffineIntersectionsULift_of_isReduction`: **Stacks 0AJ6, the
  implication (1) ⟹ (2)** at the level of the test data: the affine-intersection condition
  passes from a reduction of a formal algebraic space to the space itself.
* `AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift`:
  both directions of **Stacks 0AJ6**, read against a reduction of `X` and a presentation of it
  by a presheaf of `Type u`.
* `…exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift`:
  **Stacks 0AJ6**. The reduction and its presentation are produced, from Stacks 0AIN and from
  the pointwise `u`-smallness of an algebraic space.

## References

* [Stacks Project, Tag 01KR](https://stacks.math.columbia.edu/tag/01KR)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The global-sections map of a pair of morphisms is surjective after enlarging the two
targets along maps surjective on global sections.** If `Γ(U, ⊤) ⊗_ℤ Γ(V, ⊤) ⟶ Γ(P, ⊤)` is
surjective and `iu : U ⟶ U'`, `iv : V ⟶ V'` are surjective on global sections, then
`Γ(U', ⊤) ⊗_ℤ Γ(V', ⊤) ⟶ Γ(P, ⊤)` is surjective.

Every element of `Γ(P, ⊤)` is the image of a tensor, and a pure tensor `x ⊗ y` is the image of
any pair of preimages of `x` and `y`; the range of the second map is closed under addition, so
the induction over tensors goes through. -/
theorem surjective_globalSectionsTensorLift_comp {U V U' V' P : Scheme.{u}}
    (p : P ⟶ U) (q : P ⟶ V) (iu : U ⟶ U') (iv : V ⟶ V')
    (hsurj : Function.Surjective (globalSectionsTensorLift p q))
    (hu : Function.Surjective iu.appTop.hom) (hv : Function.Surjective iv.appTop.hom) :
    Function.Surjective (globalSectionsTensorLift (p ≫ iu) (q ≫ iv)) := by
  have key : ∀ s : Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤),
      globalSectionsTensorLift p q s ∈
        Set.range (globalSectionsTensorLift (p ≫ iu) (q ≫ iv)) := by
    intro s
    induction s using TensorProduct.inductionOn with
    | tmul x y =>
        obtain ⟨x', hx'⟩ := hu x
        obtain ⟨y', hy'⟩ := hv y
        refine ⟨x' ⊗ₜ[ℤ] y', ?_⟩
        have e₁ : (p ≫ iu).appTop.hom x' = p.appTop.hom (iu.appTop.hom x') := by
          rw [Scheme.Hom.comp_appTop]; rfl
        have e₂ : (q ≫ iv).appTop.hom y' = q.appTop.hom (iv.appTop.hom y') := by
          rw [Scheme.Hom.comp_appTop]; rfl
        rw [globalSectionsTensorLift_tmul, globalSectionsTensorLift_tmul, e₁, e₂, hx', hy']
    | add s₁ s₂ h₁ h₂ =>
        obtain ⟨w₁, hw₁⟩ := h₁
        obtain ⟨w₂, hw₂⟩ := h₂
        exact ⟨w₁ + w₂, by rw [map_add, map_add, hw₁, hw₂]⟩
  intro z
  obtain ⟨s, hs⟩ := hsurj z
  obtain ⟨w, hw⟩ := key s
  exact ⟨w, by rw [hw, hs]⟩

/-- **The canonical morphism from a fibre product to the product over the terminal scheme is an
immersion.** This is Stacks 01KR: the morphism is a base change of the diagonal of the base. -/
private theorem isImmersion_pullbackMapTerminal {W₁ W₂ Z : Scheme.{u}}
    (f : W₁ ⟶ Z) (g : W₂ ⟶ Z) {f' : W₁ ⟶ ⊤_ Scheme.{u}} {g' : W₂ ⟶ ⊤_ Scheme.{u}}
    (h₁ : f ≫ terminal.from Z = 𝟙 W₁ ≫ f') (h₂ : g ≫ terminal.from Z = 𝟙 W₂ ≫ g') :
    IsImmersion (pullback.map f g f' g' (𝟙 W₁) (𝟙 W₂) (terminal.from Z) h₁ h₂) := by
  obtain rfl : f ≫ terminal.from Z = f' := by simpa using h₁
  obtain rfl : g ≫ terminal.from Z = g' := by simpa using h₂
  exact inferInstanceAs (IsImmersion (pullback.mapDesc f g (terminal.from Z)))

/-- A thickening with affine target has affine source and is surjective on global sections. -/
private theorem isAffine_and_surjective_appTop_of_isThickening {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (hf : Stacks.Thickenings.IsThickening f) :
    IsAffine X ∧ Function.Surjective f.appTop.hom :=
  have _ : IsClosedImmersion f := hf.1
  IsClosedImmersion.isAffine_surjective_of_isAffine f

/-- Precomposing `pullback.lift` into the product over the terminal scheme with a morphism. -/
private theorem comp_pullback_lift_terminal {T W U V : Scheme.{u}} (h : T ⟶ W) (a : W ⟶ U)
    (b : W ⟶ V) : h ≫ (pullback.lift a b (terminal.hom_ext _ _) :
        W ⟶ pullback (terminal.from U) (terminal.from V)) =
      pullback.lift (h ≫ a) (h ≫ b) (terminal.hom_ext _ _) :=
  pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd])

/-- **The affine-intersection conclusion for a scheme carrying a thickening on which it
holds.** Let `U'`, `V'` be affine schemes, let `p' : Q' ⟶ U'`, `q' : Q' ⟶ V'` assemble a
monomorphism locally of finite type into `U' ×_{Spec ℤ} V'`, let `u' : Ur' ⟶ U'` and
`v' : Vr' ⟶ V'` be thickenings and let `j' : PP' ⟶ Q'` be a thickening compatible with a pair
`pP'`, `qP'` over `u'` and `v'`. If `PP'` is affine and
`Γ(Ur', ⊤) ⊗_ℤ Γ(Vr', ⊤) ⟶ Γ(PP', ⊤)` is surjective then `Q'` is affine and
`Γ(U', ⊤) ⊗_ℤ Γ(V', ⊤) ⟶ Γ(Q', ⊤)` is surjective.

The hypothesis says that `PP' ⟶ Ur' ×_{Spec ℤ} Vr'` is a closed immersion; composing with the
two thickenings, which are closed immersions of affine schemes, makes `PP' ⟶ U' ×_{Spec ℤ} V'`
a closed immersion, and `AlgebraicGeometry.isClosedImmersion_of_isThickening_of_mono` transfers
that to `Q' ⟶ U' ×_{Spec ℤ} V'`. -/
private theorem isAffine_and_surjective_globalSectionsTensorLift_of_isThickening
    {U' V' Q' PP' Ur' Vr' : Scheme.{u}} [IsAffine U'] [IsAffine V']
    (p' : Q' ⟶ U') (q' : Q' ⟶ V') (u' : Ur' ⟶ U') (v' : Vr' ⟶ V')
    (pP' : PP' ⟶ Ur') (qP' : PP' ⟶ Vr') (j' : PP' ⟶ Q')
    (hu : Stacks.Thickenings.IsThickening u') (hv : Stacks.Thickenings.IsThickening v')
    (hj : Stacks.Thickenings.IsThickening j')
    (hjp : j' ≫ p' = pP' ≫ u') (hjq : j' ≫ q' = qP' ≫ v')
    (hmono : Mono (pullback.lift p' q' (terminal.hom_ext _ _) :
      Q' ⟶ pullback (terminal.from U') (terminal.from V')))
    (hlft : LocallyOfFiniteType (pullback.lift p' q' (terminal.hom_ext _ _) :
      Q' ⟶ pullback (terminal.from U') (terminal.from V')))
    (hPaff : IsAffine PP')
    (hPsurj : Function.Surjective (globalSectionsTensorLift pP' qP')) :
    IsAffine Q' ∧ Function.Surjective (globalSectionsTensorLift p' q') := by
  have _ := hPaff
  obtain ⟨-, hUsurj⟩ := isAffine_and_surjective_appTop_of_isThickening u' hu
  obtain ⟨-, hVsurj⟩ := isAffine_and_surjective_appTop_of_isThickening v' hv
  have hsurj' : Function.Surjective (globalSectionsTensorLift (pP' ≫ u') (qP' ≫ v')) :=
    surjective_globalSectionsTensorLift_comp pP' qP' u' v' hPsurj hUsurj hVsurj
  have hci : IsClosedImmersion
      (pullback.lift (pP' ≫ u') (qP' ≫ v') (terminal.hom_ext _ _) :
        PP' ⟶ pullback (terminal.from U') (terminal.from V')) :=
    (isClosedImmersion_pullbackLift_terminal_iff _ _).mpr ⟨hPaff, hsurj'⟩
  have _ := hmono
  have _ := hlft
  have hci' : IsClosedImmersion
      (j' ≫ (pullback.lift p' q' (terminal.hom_ext _ _) :
        Q' ⟶ pullback (terminal.from U') (terminal.from V'))) := by
    rw [comp_pullback_lift_terminal, hjp, hjq]; exact hci
  exact (isClosedImmersion_pullbackLift_terminal_iff p' q').mp
    (isClosedImmersion_of_isThickening_of_mono
      (pullback.lift p' q' (terminal.hom_ext _ _) :
        Q' ⟶ pullback (terminal.from U') (terminal.from V')) hj hci')

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A cartesian square of two morphisms out of universe-lifted Yoneda presheaves is a base
change of the absolute diagonal.** This is `Stacks.Spaces.isPullback_diag_prodMap` with the
presheaf product of the two representables replaced by the presheaf represented by the product,
along the comparison isomorphism of `CategoryTheory.Limits.PreservesLimitPair.iso`. -/
private theorem isPullback_diag_uliftYoneda_prodLift
    [HasBinaryProducts (BigFppfOver B S hS)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {A A' P : BigFppfOver B S hS}
    {a : (uliftYoneda.{u + 1}).obj A ⟶ F} {b : (uliftYoneda.{u + 1}).obj A' ⟶ F}
    {p : P ⟶ A} {q : P ⟶ A'}
    (h : IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b) :
    IsPullback ((uliftYoneda.{u + 1}).map p ≫ a)
      ((uliftYoneda.{u + 1}).map (prod.lift p q)) (diag F)
      (prodComparison (uliftYoneda.{u + 1}) A A' ≫ prod.map a b) := by
  have he : (uliftYoneda.{u + 1}).map (prod.lift p q) ≫
      prodComparison (uliftYoneda.{u + 1}) A A' =
      prod.lift ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) := by
    refine prod.hom_ext ?_ ?_ <;> simp [← Functor.map_comp]
  refine (Stacks.Spaces.isPullback_diag_prodMap h).of_iso (Iso.refl _) (Iso.refl _)
    (PreservesLimitPair.iso (uliftYoneda.{u + 1}) A A').symm (Iso.refl _) (by simp) ?_
    (by simp) ?_
  · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp, ← he, Category.assoc,
      ← PreservesLimitPair.iso_hom, Iso.hom_inv_id, Category.comp_id]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      ← PreservesLimitPair.iso_hom, Iso.inv_hom_id, Category.id_comp]

/-- **The canonical morphism from the underlying scheme of a product in the big fppf site of `S`
to the product over the terminal scheme is an immersion.** The product in the site is a fibre
product over the site's terminal object, which the structure functor to schemes preserves, and
the morphism from a fibre product to the product over the terminal scheme is an immersion. -/
private theorem isImmersion_toScheme_prodLiftTerminal
    [HasBinaryProducts (BigFppfOver B S hS)] (U V : BigFppfOver B S hS) :
    IsImmersion (pullback.lift
      ((BigFppfOver.toScheme B S hS).map (prod.fst : U ⨯ V ⟶ U))
      ((BigFppfOver.toScheme B S hS).map (prod.snd : U ⨯ V ⟶ V))
      (terminal.hom_ext _ _) :
        (BigFppfOver.toScheme B S hS).obj (U ⨯ V) ⟶
          pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj U))
            (terminal.from ((BigFppfOver.toScheme B S hS).obj V))) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have h0 : IsPullback (prod.fst : U ⨯ V ⟶ U) (prod.snd : U ⨯ V ⟶ V)
      (terminal.from U) (terminal.from V) :=
    IsPullback.of_iso_pullback ⟨terminal.hom_ext _ _⟩ (prodIsoPullback U V)
      (prodIsoPullback_hom_fst _ _) (prodIsoPullback_hom_snd _ _)
  have h1 := h0.map (BigFppfOver.toScheme B S hS)
  have hm := isImmersion_pullbackMapTerminal
    ((BigFppfOver.toScheme B S hS).map (terminal.from U))
    ((BigFppfOver.toScheme B S hS).map (terminal.from V))
    (f' := terminal.from ((BigFppfOver.toScheme B S hS).obj U))
    (g' := terminal.from ((BigFppfOver.toScheme B S hS).obj V))
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  have hfac : pullback.lift
      ((BigFppfOver.toScheme B S hS).map (prod.fst : U ⨯ V ⟶ U))
      ((BigFppfOver.toScheme B S hS).map (prod.snd : U ⨯ V ⟶ V))
      (terminal.hom_ext _ _) =
      h1.isoPullback.hom ≫ pullback.map
        ((BigFppfOver.toScheme B S hS).map (terminal.from U))
        ((BigFppfOver.toScheme B S hS).map (terminal.from V))
        (terminal.from ((BigFppfOver.toScheme B S hS).obj U))
        (terminal.from ((BigFppfOver.toScheme B S hS).obj V)) (𝟙 _) (𝟙 _)
        (terminal.from ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))))
        (terminal.hom_ext _ _) (terminal.hom_ext _ _) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id, h1.isoPullback_hom_fst]
    · simp only [pullback.lift_snd, Category.assoc, Category.comp_id, h1.isoPullback_hom_snd]
  rw [hfac]
  have _ := hm
  infer_instance

/-- **Stacks 0AJ6, the implication (1) ⟹ (2), at the level of the test data.** The
affine-intersection condition passes from a reduction of a formal algebraic space to the space
itself.

The two test objects are replaced by their reductions, which map to the reduction of the space
by its universal property; the fibre product of the reductions over the reduction of the space
is the fibre product over the space itself, the inclusion of a reduction being a monomorphism,
and it maps to the original fibre product by a composition of two base changes of the
thickenings `U_red ⟶ U` and `V_red ⟶ V`, hence by a thickening. The condition for the reduction
makes the morphism from that fibre product into `U ×_{Spec ℤ} V` a closed immersion, and
`AlgebraicGeometry.isClosedImmersion_of_isThickening_of_mono` upgrades that to the original
fibre product, the morphism `Q ⟶ U ×_{Spec ℤ} V` being a monomorphism locally of finite type by
Stacks 0AIP and Stacks 01KR. -/
theorem hasAffineIntersectionsULift_of_isReduction
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    (h : HasAffineIntersectionsULift B S hS Xr.obj) :
    HasAffineIntersectionsULift B S hS X.obj := by
  classical
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : Mono i.hom := mono_hom_of_isReduction B S hS hi
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hlft := relative_locallyOfFiniteType_diag_hom_of_isFormalAlgebraicSpace B S hS hX
  intro U V Q a b p q hU hV sq
  have _ := hU
  have _ := hV
  -- the reductions of the two test objects
  obtain ⟨a₁, ha₁, -⟩ := hi.existsUnique_comp_eq (siteReduction B S hS U)
    (isReduced_toScheme_obj_siteReduction B S hS U)
    (uliftYonedaEquiv.{u + 1}
      ((uliftYoneda.{u + 1}).map (siteReductionMap B S hS U) ≫ a))
  obtain ⟨b₁, hb₁, -⟩ := hi.existsUnique_comp_eq (siteReduction B S hS V)
    (isReduced_toScheme_obj_siteReduction B S hS V)
    (uliftYonedaEquiv.{u + 1}
      ((uliftYoneda.{u + 1}).map (siteReductionMap B S hS V) ≫ b))
  rw [Equiv.symm_apply_apply] at ha₁ hb₁
  -- the two site-level fibre products cutting `Q` down to the two reductions
  have sq₁ : IsPullback (pullback.fst (siteReductionMap B S hS U) p)
      (pullback.snd (siteReductionMap B S hS U) p) (siteReductionMap B S hS U) p :=
    IsPullback.of_hasPullback _ _
  have sq₂ : IsPullback
      (pullback.fst (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q))
      (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q))
      (siteReductionMap B S hS V)
      (pullback.snd (siteReductionMap B S hS U) p ≫ q) :=
    IsPullback.of_hasPullback _ _
  have sqY₁ := sq₁.map (uliftYoneda.{u + 1})
  have sqY₂ := sq₂.map (uliftYoneda.{u + 1})
  rw [Functor.map_comp] at sqY₂
  have paste := (sqY₂.paste_vert (sqY₁.paste_vert sq).flip).flip
  rw [← ha₁, ← hb₁, ← Functor.map_comp] at paste
  obtain ⟨hUr, -⟩ := isAffine_and_surjective_appTop_of_isThickening _
    (isThickening_toScheme_map_siteReductionMap B S hS U)
  obtain ⟨hVr, -⟩ := isAffine_and_surjective_appTop_of_isThickening _
    (isThickening_toScheme_map_siteReductionMap B S hS V)
  obtain ⟨hPaff, hPsurj⟩ := h (siteReduction B S hS U) (siteReduction B S hS V) _ a₁ b₁ _ _
    hUr hVr ((isPullback_comp_mono_iff i.hom).mp paste)
  -- the comparison from the fibre product of the reductions to `Q` is a thickening
  have hth₂ : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q))) :=
    Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback
      (sq₂.map (BigFppfOver.toScheme B S hS))
      (isThickening_toScheme_map_siteReductionMap B S hS V)
  have hth₁ : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (siteReductionMap B S hS U) p)) :=
    Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback
      (sq₁.map (BigFppfOver.toScheme B S hS))
      (isThickening_toScheme_map_siteReductionMap B S hS U)
  have hthj : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (siteReductionMap B S hS V)
          (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫
        pullback.snd (siteReductionMap B S hS U) p)) := by
    rw [Functor.map_comp]
    exact Stacks.Thickenings.isThickening_comp hth₂ hth₁
  -- the two compatibilities of the comparison with the two projections
  have hjp0 : (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫
      pullback.snd (siteReductionMap B S hS U) p) ≫ p =
      (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫
      pullback.fst (siteReductionMap B S hS U) p) ≫ siteReductionMap B S hS U := by
    rw [Category.assoc, Category.assoc, sq₁.w]
  have hjq0 : (pullback.snd (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫
      pullback.snd (siteReductionMap B S hS U) p) ≫ q =
      pullback.fst (siteReductionMap B S hS V)
        (pullback.snd (siteReductionMap B S hS U) p ≫ q) ≫ siteReductionMap B S hS V := by
    rw [Category.assoc]
    exact sq₂.w.symm
  -- `Q ⟶ U ×_S V` is a monomorphism locally of finite type by Stacks 0AIP
  have hprod := isPullback_diag_uliftYoneda_prodLift B S hS sq
  have hdiag : MorphismProperty.monomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
      (diag X.obj) := inferInstanceAs (Mono (diag X.obj))
  have hmono0 : Mono ((uliftYoneda.{u + 1}).map (prod.lift p q)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hprod hdiag
  have hmono1 : Mono (prod.lift p q) := (uliftYoneda.{u + 1}).mono_of_mono_map hmono0
  have hmono2 : Mono ((BigFppfOver.toScheme B S hS).map (prod.lift p q)) :=
    preserves_mono_of_preservesLimit _ _
  have hlft2 : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (prod.lift p q)) :=
    hlft.property _ _ (prod.lift p q) hprod
  have himm := isImmersion_toScheme_prodLiftTerminal B S hS U V
  have hfac2 : (pullback.lift ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map q) (terminal.hom_ext _ _) :
        (BigFppfOver.toScheme B S hS).obj Q ⟶
          pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj U))
            (terminal.from ((BigFppfOver.toScheme B S hS).obj V))) =
      (BigFppfOver.toScheme B S hS).map (prod.lift p q) ≫
        pullback.lift ((BigFppfOver.toScheme B S hS).map (prod.fst : U ⨯ V ⟶ U))
          ((BigFppfOver.toScheme B S hS).map (prod.snd : U ⨯ V ⟶ V))
          (terminal.hom_ext _ _) := by
    rw [comp_pullback_lift_terminal, ← Functor.map_comp, ← Functor.map_comp, prod.lift_fst,
      prod.lift_snd]
  have _ := hmono2
  have _ := hlft2
  have _ := himm
  refine isAffine_and_surjective_globalSectionsTensorLift_of_isThickening
    ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map q)
    ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS U))
    ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS V)) _ _ _
    (isThickening_toScheme_map_siteReductionMap B S hS U)
    (isThickening_toScheme_map_siteReductionMap B S hS V) hthj ?_ ?_
    (by rw [hfac2]; infer_instance) (by rw [hfac2]; infer_instance) hPaff hPsurj
  · rw [← Functor.map_comp, ← Functor.map_comp, hjp0]
  · rw [← Functor.map_comp, ← Functor.map_comp, hjq0]

/-! ### Stacks 0AJ6 -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0AJ6.** Let `X` be a formal algebraic space over `S` and let `i : X_red ⟶ X` be a
reduction of `X`, presented by a presheaf `Xred` of `Type u` together with an isomorphism from
its universe lift. Then `Xred` is a separated algebraic space if and only if for every pair of
objects of the big fppf site of `S` with affine underlying scheme and every pair of morphisms
from their universe-lifted Yoneda presheaves into `X` every object of the site representing the
fibre product has affine underlying scheme and the canonical map from the tensor product over
`ℤ` of the two rings of global sections to its ring of global sections is surjective.

The implication from the condition to separatedness is
`AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_of_hasAffineIntersectionsULift`:
the inclusion of a reduction is a monomorphism, so the condition restricts from `X` to the
reduction, where it is separatedness by Stacks 0AHS. The converse is
`AlgebraicGeometry.FormalSpace.hasAffineIntersectionsULift_of_isReduction`, the argument of the
source through the thickening comparison of the two fibre products. -/
@[stacks 0AJ6 "both implications, read against a reduction of X, in the sense of \
AlgebraicGeometry.FormalSpace.IsReduction, and a presentation of it by a presheaf of Type u \
together with an isomorphism from its universe lift -- an algebraic space over S being a \
presheaf of Type u while a formal algebraic space is a sheaf of Type (u + 1). Clause (2) \
quantifies over the objects of the site representing the fibre product, as the carrier of \
Stacks 0AHS does for the identical clause, rather than asserting that it is representable, \
which is Stacks 0AIP. The tag itself, which produces the reduction and its presentation, is \
AlgebraicGeometry.FormalSpace.\
exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift",
  ega "I 10.15.7" "more general"]
theorem isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    Space.IsAbsolutelySeparated B S hS hZ Xred ↔
      HasAffineIntersectionsULift B S hS X.obj := by
  have halg : IsAlgebraicSpace B S hS Xred :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Xred).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hi.algebraic)
  refine ⟨fun hsep ↦ ?_,
    isAbsolutelySeparated_reduction_of_hasAffineIntersectionsULift B S hS hZ hX hi e⟩
  refine hasAffineIntersectionsULift_of_isReduction B S hS hX hi ?_
  refine hasAffineIntersectionsULift_of_mono B S hS e.inv ?_
  exact (hasAffineIntersectionsULift_comp_uliftFunctor_iff B S hS Xred).mpr
    ((Space.isAbsolutelySeparated_iff_hasAffineIntersections B S hS hZ Xred halg).mp hsep)

/-- **Stacks 0AJ6.** Let `S` be a scheme contained in a big fppf site `B` and let `X` be a
formal algebraic space over `S`. The reduction of `X` exists — a reduced algebraic space
`X_red` and a representable thickening `i : X_red ⟶ X` through which every morphism to `X`
from a reduced algebraic space factors uniquely — it is presented by a presheaf `Xred` of
`Type u` together with an isomorphism from its universe lift, and the following are
equivalent:

1. `Xred` is a separated algebraic space;
2. for every pair of objects of the big fppf site of `S` with affine underlying scheme and
   every pair of morphisms from their universe-lifted Yoneda presheaves into `X`, every
   object of the site representing the fibre product has affine underlying scheme and the
   canonical map from the tensor product over `ℤ` of the two rings of global sections to its
   ring of global sections is surjective.

The reduction comes from Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`; its presentation
by a presheaf of `Type u` from the pointwise `u`-smallness of an algebraic space,
`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`; and the
equivalence from
`AlgebraicGeometry.FormalSpace.isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift`,
which reads it against any reduction and any presentation of it. -/
@[stacks 0AJ6, ega "I 10.15.7" "more general"]
theorem exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (Xr : FppfSheaf B S hS) (i : Xr ⟶ X) (Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj),
      IsReduction B S hS X Xr i ∧
        (Space.IsAbsolutelySeparated B S hS hZ Xred ↔
          HasAffineIntersectionsULift B S hS X.obj) := by
  obtain ⟨Xr, i, hi⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX
  obtain ⟨Xred, -, ⟨e⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hi.algebraic
  exact ⟨Xr, i, Xred, e, hi,
    isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift B S hS hZ hX hi e⟩

end FormalSpace

end AlgebraicGeometry

end
