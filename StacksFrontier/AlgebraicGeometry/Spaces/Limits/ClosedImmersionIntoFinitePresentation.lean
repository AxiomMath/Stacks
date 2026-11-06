module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EventualMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationApproximationOfNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentationOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite

/-!
# A morphism of finite type is closed in one of finite presentation

Stacks 0872: let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite
type, with `X` and `Y` quasi-compact and quasi-separated. Then `f` factors as a closed immersion
`X ⟶ X'` followed by a morphism `X' ⟶ Y` of finite presentation.

## Main results

* Stacks 0872, assuming absolute Noetherian approximation over `Spec ℤ` (Stacks 07SU), is
`exists_isFinitePresentation_isClosedImmersion_of_isLocallyOfFiniteType_of_noetherianApproximation`
  in the namespace `AlgebraicGeometry.Space`.

## Implementation notes

Viewed over `Spec ℤ` along the lower-shriek extension of Stacks 03I5, `X` is the limit of an
absolute Noetherian approximation `X = lim X_i` (Stacks 07SU); the limit of the spaces `Y × X_i` is
`Y × X`, into which `X` embeds by `(f, 1)`, so `X ⟶ Y × X_i` is a monomorphism for `i` large
(Stacks 0828, part (4), `AlgebraicGeometry.Space.eventually_mono_comp_limitπ`). Brought back over
`S` by the equivalence of Stacks 04SG, `Y × X_i` is of finite presentation over `Y` (Stacks 06G4,
03XR), the monomorphism `X ⟶ Y × X_i` is locally of finite type (Stacks 0462), hence separated and
locally quasi-finite (Stacks 0463), and quasi-compact, hence quasi-affine by Zariski's main theorem
(`AlgebraicGeometry.Space.isQuasiAffineHom_of_isQuasiFinite_isSeparated`, Stacks 0418 and 02LR);
Stacks 0871 then gives the closed immersion into a space of finite presentation over `Y × X_i`,
hence over `Y` (Stacks 03XQ).

Absolute Noetherian approximation over `Spec ℤ` (Stacks 07SU) enters as the hypothesis `h07SU`.

## References

* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The product with a fixed object on the left, of a morphism `a`, is a base change of `a`. -/
theorem isPullback_prod_snd_map {𝒞 : Type*} [Category 𝒞] [HasBinaryProducts 𝒞] (Y : 𝒞)
    {A A' : 𝒞} (a : A ⟶ A') :
    IsPullback prod.snd (prod.map (𝟙 Y) a) a prod.snd :=
  (IsPullback.of_prod_fst_with_id a Y).of_iso (prod.braiding A Y) (Iso.refl _)
    (prod.braiding A' Y) (Iso.refl _) (by simp) (by ext <;> simp) (by simp) (by simp)

/-- Over `Spec ℤ`, the projection `Y ⨯ Z ⟶ Y` is of finite presentation when `Z` is a
quasi-separated algebraic space of finite type over `Spec ℤ`. -/
private theorem isFinitePresentation_prod_fst_of_isFiniteType (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y) (hZa : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z)
    (hYZ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Y ⨯ Z))
    (hZft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ Z)))
    (hZqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z) :
    IsFinitePresentation B (⊤_ Scheme.{u}) hZ (prod.fst : Y ⨯ Z ⟶ Y) :=
  IsFinitePresentation.of_isPullback B (⊤_ Scheme.{u}) hZ hYZ hZa hY
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) (IsPullback.of_hasBinaryProduct' Y Z).flip
    ⟨isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers B hZ hZa
      hZft.1, isQuasiCompact_terminal_of_isFiniteTypeOverIntegers B hZ hZft,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ hZa hZqs _⟩

/-- Over `Spec ℤ`, a morphism `f : X ⟶ Y` of algebraic spaces, locally of finite type, with `X`
quasi-compact with a Noetherian approximation (Stacks 07SU) and `Y` quasi-separated, factors as a
monomorphism followed by a morphism of finite presentation (Stacks 0828, part (4)). -/
private theorem exists_mono_isFinitePresentation_fac_of_noetherianApproximation
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hft : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hYqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y)
    (hA : HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X) :
    ∃ (W : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (q : X ⟶ W) (p : W ⟶ Y),
      Mono q ∧ IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ W ∧
        IsFinitePresentation B (⊤_ Scheme.{u}) hZ p ∧ q ≫ p = f := by
  classical
  obtain ⟨A⟩ := hA
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  have : IsConnected A.Iᵒᵖ := IsCofiltered.isConnected _
  let P := prod.functor.obj Y
  let W : A.Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u := A.diagram ⋙ P
  let cW : Cone W := P.mapCone (Cone.mk X A.π)
  have hcW : IsLimit cW := by
    let e : A.Iᵒᵖ ≌ AsSmall.{u + 1} A.Iᵒᵖ := AsSmall.equiv
    have : IsConnected (AsSmall.{u + 1} A.Iᵒᵖ) := isConnected_of_equivalent e
    have := prod_preservesConnectedLimits (J := AsSmall.{u + 1} A.Iᵒᵖ) Y
    exact IsLimit.ofWhiskerEquivalence e.symm
      (isLimitOfPreserves P (A.isLimit.whiskerEquivalence e.symm))
  let tW : W ⟶ (Functor.const A.Iᵒᵖ).obj Y :=
    { app := fun _ => prod.fst
      naturality := fun _ _ _ => prod.map_fst _ _ }
  have hcommW : cW.π ≫ tW = (Functor.const A.Iᵒᵖ).map prod.fst :=
    NatTrans.ext (funext fun _ => prod.map_fst _ _)
  have hXi : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) := A.isAlgebraicSpace
  have hW : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (W.obj j) := fun j =>
    isAlgebraicSpace_prod B (⊤_ Scheme.{u}) hZ hY (hXi j)
  have hWfp : ∀ j, IsFinitePresentation B (⊤_ Scheme.{u}) hZ (prod.fst : W.obj j ⟶ Y) := fun j =>
    isFinitePresentation_prod_fst_of_isFiniteType B hZ hY (hXi j) (hW j)
      (A.isFiniteTypeOverIntegers j) (A.isAbsolutelyQuasiSeparated j)
  have hWaff : ∀ ⦃i k : A.I⦄ (h : i ≤ k),
      IsAffineHom B (⊤_ Scheme.{u}) hZ (W.map (homOfLE h).op) := fun i k h =>
    IsAffineHom.of_isPullback (isPullback_prod_snd_map Y (A.diagram.map (homOfLE h).op))
      (A.isAffineHom_map _)
  let f' : X ⟶ cW.pt := prod.lift f (𝟙 _)
  have : Mono f' := mono_of_mono_fac (prod.lift_snd f (𝟙 _))
  obtain ⟨i, hi⟩ := (eventually_mono_comp_limitπ B (⊤_ Scheme.{u}) hZ Y hY W (fun _ => hW _) tW
    cW hcW prod.fst hcommW X hX hXqc f' hWaff
    (fun _ => isAbsolutelyQuasiSeparated_of_isFinitePresentation B (⊤_ Scheme.{u}) hZ hZ (hW _)
      hYqs (hWfp _))
    (by rwa [show f' ≫ prod.fst = f from prod.lift_fst _ _])).exists
  have h₁ : (prod.map (𝟙 Y) (A.π.app (op i)) : cW.pt ⟶ W.obj (op i)) ≫ prod.fst =
      prod.fst := (prod.map_fst _ _).trans (Category.comp_id _)
  exact ⟨W.obj (op i), f' ≫ cW.π.app (op i), tW.app (op i), hi, hW _, hWfp _,
    (Category.assoc _ _ _).trans ((congrArg (f' ≫ ·) h₁).trans (prod.lift_fst _ _))⟩

/-- A factorization of the lower-shriek extension to `Spec ℤ` of `f : X ⟶ Y` as a monomorphism
followed by a morphism of finite presentation descends to such a factorization of `f` over `S`,
through the equivalence of Stacks 04SG. -/
private theorem exists_mono_isFinitePresentation_fac_of_relocalize
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {W : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (q : (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)).obj X ⟶ W) [Mono q]
    (p : W ⟶ (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)).obj Y)
    (hqp : q ≫ p = (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)).map f)
    (hW : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ W)
    (hp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ p) :
    ∃ (W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q' : X ⟶ W') (p' : W' ⟶ Y),
      Mono q' ∧ IsAlgebraicSpace B S hS W' ∧ IsFinitePresentation B S hS p' ∧ q' ≫ p' = f := by
  let g := integersMap B S hS hZ
  let E' := smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ g
  let ι := smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ g
  have hιf : ι.hom.app X ≫ (OverShriek.relocalizePresheafFunctor g).map f ≫ ι.inv.app Y =
      (E'.functor.map f).left := by
    rw [← Category.assoc, ← ι.hom.naturality f]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  let Wov : Over (yoneda.obj (Over.mk g)) := Over.mk (p ≫ ι.inv.app Y ≫ (E'.functor.obj Y).hom)
  let qov : E'.functor.obj X ⟶ Wov := Over.homMk (ι.hom.app X ≫ q) (by
    show (ι.hom.app X ≫ q) ≫ p ≫ ι.inv.app Y ≫ (E'.functor.obj Y).hom =
      (E'.functor.obj X).hom
    rw [← Over.w (E'.functor.map f), ← hιf, ← hqp]
    simp only [Category.assoc])
  let pov : Wov ⟶ E'.functor.obj Y := Over.homMk (p ≫ ι.inv.app Y) (Category.assoc _ _ _)
  have hqp' : qov ≫ pov = E'.functor.map f := by
    apply Over.OverMorphism.ext
    show (ι.hom.app X ≫ q) ≫ p ≫ ι.inv.app Y = (E'.functor.map f).left
    rw [← hιf, ← hqp]
    simp only [Category.assoc]
  let qS : X ⟶ E'.inverse.obj Wov := E'.unitIso.hom.app X ≫ E'.inverse.map qov
  let pS : E'.inverse.obj Wov ⟶ Y := E'.inverse.map pov ≫ E'.unitIso.inv.app Y
  have hqpS : qS ≫ pS = f := by
    show (E'.unitIso.hom.app X ≫ E'.inverse.map qov) ≫ E'.inverse.map pov ≫
      E'.unitIso.inv.app Y = f
    rw [Category.assoc, ← Category.assoc (E'.inverse.map qov), ← Functor.map_comp, hqp',
      Equivalence.inv_fun_map]
    simp
  have hpSfp : IsFinitePresentation B S hS pS := by
    refine isFinitePresentation_of_relocalizeMap B S (⊤_ Scheme.{u}) hS hZ g pS ?_
    let e := (counitArrowIso B S hS hZ pov).symm ≪≫ (unitInvArrowIso B S hS hZ pov).symm ≪≫
      (relocalizeArrowIso B S hS hZ pS).symm
    exact isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ _ _ e.hom.left e.hom.right
      (Arrow.w e.hom) (isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ p pov.left (𝟙 _)
        (ι.inv.app Y) (Category.id_comp _) hp)
  have : Mono qov.left := show Mono (ι.hom.app X ≫ q) from
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ (ι.app X).hom (Iso.isIso_hom _)) ‹Mono q›
  have : Mono qov := (Over.forget _).mono_of_mono_map ‹_›
  have : Mono qS := show Mono (E'.unitIso.hom.app X ≫ E'.inverse.map qov) from
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ (E'.unitIso.app X).hom (Iso.isIso_hom _))
      ((Functor.preservesMonomorphisms_of_adjunction E'.toAdjunction).preserves qov)
  exact ⟨_, qS, pS, ‹Mono qS›,
    isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S (⊤_ Scheme.{u}) hS hZ g Wov hW,
    hpSfp, hqpS⟩

/-- A monomorphism `q : X ⟶ W` followed by a morphism `p : W ⟶ Y` of finite presentation, with
composite `f` locally of finite type, `X` quasi-compact and `Y` quasi-compact and quasi-separated,
yields a factorization of `f` as a closed immersion followed by a morphism of finite presentation,
granted absolute Noetherian approximation over `Spec ℤ` (`h07SU`), by Stacks 0871. -/
private theorem exists_isFinitePresentation_isClosedImmersion_of_mono_of_noetherianApproximation
    {X W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : X ⟶ W) [Mono q] (p : W ⟶ Y) (f : X ⟶ Y)
    (hqp : q ≫ p = f) (hX : IsAlgebraicSpace B S hS X) (hW : IsAlgebraicSpace B S hS W)
    (hY : IsAlgebraicSpace B S hS Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hp : IsFinitePresentation B S hS p) (hXqc : IsQuasiCompactSpace B S hS X)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  have hlft : IsLocallyOfFiniteType B S hS q :=
    isLocallyOfFiniteType_of_comp B S hS hX hW hY q p (by rwa [hqp])
  obtain ⟨hsep, hlqf⟩ :=
    isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS q ⟨hlft, inferInstance⟩
  have hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W :=
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS B.contains_terminal hW hYqs hp
  have hqa : IsQuasiAffineHom B S hS q := isQuasiAffineHom_of_isQuasiFinite_isSeparated hX hW
    ⟨hlqf, isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hW hWqs hXqc q⟩ hsep
  obtain ⟨X', f', i, hX', hf', hi, hfac⟩ :=
    exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_noetherianApproximation
      B S hS q hX hW hlft hqa (isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hp.2.1)
      hWqs h07SU
  exact ⟨X', f' ≫ p, i, hX', isFinitePresentation_comp B S hS hX' hW hY _ _ hf' hp, hi,
    by rw [← Category.assoc, hfac, hqp]⟩

/-- **Stacks 0872**. Assume every quasi-compact, quasi-separated algebraic space over `Spec ℤ` has
an absolute Noetherian approximation (`h07SU`, also the one input of the staged Stacks 0871). Then
a morphism `f : X ⟶ Y` of algebraic spaces over `S`, locally of finite type, with `X` and `Y`
quasi-compact and quasi-separated, factors as a closed immersion `i : X ⟶ X'` followed by a
morphism `f' : X' ⟶ Y` of finite presentation. -/
theorem exists_isFinitePresentation_isClosedImmersion_of_isLocallyOfFiniteType_of_noetherianApproximation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let g := integersMap B S hS hZ
  let Λ := OverShriek.relocalizePresheafFunctor g
  have hΛX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Λ.obj X) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g X hX
  have hΛXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (Λ.obj X) :=
    isQuasiCompactSpace_relocalizePresheafFunctor_obj B S (⊤_ Scheme.{u}) hS hZ g X hXqc
  obtain ⟨W, q, p, hq, hW, hp, hqp⟩ :=
    exists_mono_isFinitePresentation_fac_of_noetherianApproximation B hZ (Λ.map f) hΛX
      (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY)
      ((holdsOnEveryEtaleChart_relocalizeMap_iff B S (⊤_ Scheme.{u}) hS hZ g _ f).2 hft) hΛXqc
      (isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs)
      (h07SU _ hΛX hΛXqc (isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X hXqs))
  obtain ⟨W', q', p', hq', hW', hp', hqp'⟩ :=
    exists_mono_isFinitePresentation_fac_of_relocalize B S hS hZ f q p hqp hW hp
  exact exists_isFinitePresentation_isClosedImmersion_of_mono_of_noetherianApproximation B S hS
    q' p' f hqp' hX hW' hY hft hp' hXqc hYqc hYqs h07SU

end AlgebraicGeometry.Space
