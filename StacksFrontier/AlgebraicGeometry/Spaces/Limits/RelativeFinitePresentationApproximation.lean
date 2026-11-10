module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SmallApproximationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLimitArrowSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType

/-!
# Approximating a morphism by morphisms of finite presentation, from a relative approximation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` quasi-separated, and let `V`
be a quasi-compact open subspace of the view of `Y` over `Spec ℤ` through which the view of `f`
factors. If the factorization `X ⟶ V` is the limit of a system of morphisms of quasi-separated
algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms (the conclusion of
Stacks 0GS3), then `X` is a directed limit of algebraic spaces of finite presentation over `Y`
with affine transition morphisms (the conclusion of Stacks 09NS).

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_finitePresentation_of_hasRelativeApproximation`: the
  conclusion of Stacks 09NS from a relative approximation of the view over `Spec ℤ`.
* `AlgebraicGeometry.Space.isAffineHom_pullbackMap`: the comparison of two fibre products along a
  morphism of cospans with affine left-hand component and separated bottom component is affine.
* `AlgebraicGeometry.Space.isFinitePresentation_of_isFiniteType_terminal`: a morphism between
  quasi-separated algebraic spaces of finite type over `Spec ℤ` is of finite presentation.

## References

* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_relativeFinitePresentationApproximation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance (priority := high) hasProducts_presheaf_relativeFinitePresentationApproximation
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  @functorCategoryHasLimitsOfShape _ _ _ _ _ _
    (Types.hasLimitsOfShape : HasLimitsOfShape (Discrete J) (Type u))

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance (priority := high) hasPullback_presheaf_relativeFinitePresentationApproximation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The comparison of two fibre products along a morphism of cospans is affine** when the
morphism of the left-hand corners is affine and that of the bottom corners is separated. -/
theorem isAffineHom_pullbackMap
    {X X' Z Z' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (f' : X' ⟶ Z') (a : X ⟶ X') (b : Z ⟶ Z') (q : Y ⟶ Z) (q' : Y ⟶ Z')
    (ha : f ≫ b = a ≫ f') (hb : q ≫ b = q') (haff : IsAffineHom B S hS a)
    (hsep : IsSeparated B S hS b) :
    IsAffineHom B S hS (pullback.map f q f' q' a (𝟙 _) b ha (by simpa using hb)) := by
  let m := pullback.map (f ≫ b) (q ≫ b) f' q' a (𝟙 _) (𝟙 _)
    (by simpa using ha) (by simpa using hb)
  have hm : IsPullback (pullback.fst (f ≫ b) (q ≫ b)) m a (pullback.fst f' q') := by
    have outer : IsPullback (pullback.fst (f ≫ b) (q ≫ b))
        (m ≫ pullback.snd f' q') (a ≫ f') q' := by
      simpa only [m, pullback.map, pullback.lift_snd, Category.comp_id, ← ha, ← hb] using
        (IsPullback.of_hasPullback (f ≫ b) (q ≫ b))
    exact outer.of_bot (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f' q')
  have hmAff : IsAffineHom B S hS m := isAffineHom_of_isPullback hm haff
  have hd : IsAffineHom B S hS (pullback.mapDesc f q b) :=
    isAffineHom_of_isClosedImmersion B S hS _ (isClosedImmersion_mapDesc B S hS f q b hsep)
  have heq : pullback.map f q f' q' a (𝟙 _) b ha (by simpa using hb) =
      pullback.mapDesc f q b ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.mapDesc]
  rw [heq]
  exact isAffineHom_comp B S hS _ _ hd hmAff

/-- The terminal presheaf over `Spec ℤ` is locally Noetherian, in the étale-local sense of
Stacks 03E6. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_terminal (hZ : B.Contains (⊤_ Scheme.{u})) :
    HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hZ))) :
      (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
    (Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _
  let e := hterm.uniqueUpToIso terminalIsTerminal
  refine ⟨Over.mk (𝟙 (B.obj hZ)), e.hom, ?_, ?_, ?_⟩
  · exact presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => by
        change Surjective ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 U))
        rw [CategoryTheory.Functor.map_id]
        infer_instance) _
  · exact presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => by
        change Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 U))
        rw [CategoryTheory.Functor.map_id]
        infer_instance) _
  · exact inferInstanceAs (IsLocallyNoetherian (⊤_ Scheme.{u}))

/-- A morphism between quasi-separated algebraic spaces of finite type over `Spec ℤ` is of
finite presentation. -/
theorem isFinitePresentation_of_isFiniteType_terminal (hZ : B.Contains (⊤_ Scheme.{u}))
    {F G : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F) (hG : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ G)
    (hFft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F))
    (hGft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from G))
    (hFqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ F)
    (hGqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ G) (k : F ⟶ G) :
    IsFinitePresentation B (⊤_ Scheme.{u}) hZ k := by
  have hT := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
  have hFlfp : IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (k ≫ terminal.from G) := by
    rw [terminal.hom_ext (k ≫ terminal.from G) (terminal.from F)]
    exact isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ hF hT _
      (hasEtaleLocalProperty_isLocallyNoetherian_terminal B hZ) hFft.1
  exact ⟨isLocallyOfFinitePresentation_of_comp B (⊤_ Scheme.{u}) hZ hF hG hT k _ hFlfp hGft.1,
    isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hG hGqs
      (isQuasiCompactSpace_of_isFiniteType_terminal B hZ hFft) k,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ hF hFqs k⟩

/-- **Approximation of a morphism of algebraic spaces by morphisms of finite presentation, from a
relative approximation of its view over `Spec ℤ`.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` with `Y` quasi-separated, let `V` be a quasi-compact open subspace of the view of
`Y` over `Spec ℤ` through which the view of `f` factors as `f_V`, and suppose `f_V` is the limit of
an inverse system of morphisms of quasi-separated algebraic spaces of finite type over `Spec ℤ`
with affine transition morphisms (the conclusion of Stacks 0GS3). Then `X` is the limit of a
directed inverse system of algebraic spaces of finite presentation over `Y` with affine transition
morphisms over `Y`. -/
theorem exists_isLimit_finitePresentation_of_hasRelativeApproximation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (V : Subfunctor (viewOverIntegers B S hS B.contains_terminal Y))
    (hV : IsOpenSubspace B (⊤_ Scheme.{u}) B.contains_terminal V)
    (hVqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal V.toFunctor)
    (fV : viewOverIntegers B S hS B.contains_terminal X ⟶ V.toFunctor)
    (hfV : fV ≫ V.ι = (OverShriek.relocalizePresheafFunctor
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj B.contains_terminal)).map f)
    (hR : HasRelativeApproximation B B.contains_terminal fV) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
        (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (D.map g)) := by
  classical
  let hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let L := OverShriek.relocalizePresheafFunctor g
  obtain ⟨R⟩ := hR
  let := R.preorder
  let := R.nonempty
  let := R.isDirected
  have hT := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
  have hYZ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (L.obj Y) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY
  have hYZqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (L.obj Y) :=
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  let c : Cone R.diagram := Cone.mk (Arrow.mk fV) R.π
  let e : c.pt ≅ Arrow.mk fV := Iso.refl _
  let E := arrowPullbackSystem fV c e
  let s := arrowPullbackCone fV c e
  have hs : IsLimit s := isLimit_arrowPullbackCone fV c e R.isLimit
  have hLft : ∀ i, IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (R.diagram.obj i).left) :=
    fun i => isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ
      (R.isFiniteTypeOverIntegers_left i)
  have hRft : ∀ i, IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (R.diagram.obj i).right) :=
    fun i => isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ
      (R.isFiniteTypeOverIntegers_right i)
  have hstage : ∀ i, IsFinitePresentation B (⊤_ Scheme.{u}) hZ (R.diagram.obj i).hom := fun i =>
    isFinitePresentation_of_isFiniteType_terminal B hZ (R.isAlgebraicSpace_left i)
      (R.isAlgebraicSpace_right i) (hLft i) (hRft i) (R.isAbsolutelyQuasiSeparated_left i)
      (R.isAbsolutelyQuasiSeparated_right i) _
  have hE : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (E.obj i) := fun i =>
    isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ _ _ (R.isAlgebraicSpace_left i) hV.1
      (R.isAlgebraicSpace_right i)
  have hVfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ V.ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B (⊤_ Scheme.{u}) hZ hV.2,
      isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hYZ hYZqs hVqc V.ι,
      isQuasiSeparated_of_mono B (⊤_ Scheme.{u}) hZ V.ι inferInstance⟩
  let q : ∀ i, E.obj i ⟶ L.obj Y := fun i => arrowPullbackSystemSnd fV c e i ≫ V.ι
  have hq : ∀ i, IsFinitePresentation B (⊤_ Scheme.{u}) hZ (q i) := fun i =>
    isFinitePresentation_comp B (⊤_ Scheme.{u}) hZ (hE i) hV.1 hYZ _ _
      (isFinitePresentation_pullback_snd B (⊤_ Scheme.{u}) hZ _ _ (R.isAlgebraicSpace_left i)
        (R.isAlgebraicSpace_right i) hV.1 (hstage i)) hVfp
  have hqnat : ∀ {i j : R.Iᵒᵖ} (a : i ⟶ j), E.map a ≫ q j = q i := fun a => by
    simp only [q, ← Category.assoc]
    rw [arrowPullbackSystem_map_snd]
  have hsq : ∀ i, s.π.app i ≫ q i = L.map f := fun i =>
    (congrArg (· ≫ V.ι) (arrowPullbackProj_snd fV c e i)).trans hfV
  have hEaff : ∀ {i j : R.Iᵒᵖ} (a : i ⟶ j), IsAffineHom B (⊤_ Scheme.{u}) hZ (E.map a) :=
    fun {i j} a => isAffineHom_pullbackMap B (⊤_ Scheme.{u}) hZ _ _ _ _ _ _
      (R.diagram.map a).w.symm (arrowBaseMap_comp_right fV c e a) (R.isAffineHom_left a)
      (isSeparated_of_isAffineHom B (⊤_ Scheme.{u}) hZ _ (R.isAlgebraicSpace_right i)
        (R.isAlgebraicSpace_right j) (R.isAffineHom_right a))
  let YS : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u := yoneda.obj (Over.mk g)
  let σY : L.obj Y ⟶ YS := OverShriek.relocalizeToYoneda g Y
  let Aov : R.Iᵒᵖ ⥤ Over YS :=
    { obj := fun i => Over.mk (q i ≫ σY)
      map := fun {i j} a => Over.homMk (E.map a) (by
        change E.map a ≫ q j ≫ σY = q i ≫ σY
        rw [← Category.assoc, hqnat])
      map_id := fun i => Over.OverMorphism.ext (E.map_id i)
      map_comp := fun a b => Over.OverMorphism.ext (E.map_comp a b) }
  let cOv : Cone Aov :=
    { pt := Over.mk (OverShriek.relocalizeToYoneda g X)
      π :=
        { app := fun i => Over.homMk (s.π.app i) (by
            change s.π.app i ≫ q i ≫ σY = OverShriek.relocalizeToYoneda g X
            rw [← Category.assoc, hsq]
            exact relocalizeToYoneda_naturality B S _ hS hZ g f)
          naturality := fun i j a => Over.OverMorphism.ext (s.π.naturality a) } }
  let : CategoryTheory.IsConnected R.Iᵒᵖ := IsCofiltered.isConnected R.Iᵒᵖ
  let : CreatesLimitsOfShape R.Iᵒᵖ (Over.forget YS) :=
    Over.createsLimitsOfShapeForgetOfIsConnected
  have hcOv : IsLimit cOv := isLimitOfReflects (Over.forget YS) hs
  let eqv := smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ g
  let α := smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ g
  have hrel : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      α.hom.app F ≫ OverShriek.relocalizeToYoneda g F = (eqv.functor.obj F).hom := by
    intro F
    ext W x
    exact Over.OverMorphism.ext rfl
  let D := Aov ⋙ eqv.inverse
  have hD : IsLimit (eqv.inverse.mapCone cOv) := isLimitOfPreserves eqv.inverse hcOv
  let eFunX : eqv.functor.obj X ≅ Over.mk (OverShriek.relocalizeToYoneda g X) :=
    Over.isoMk (α.app X) (hrel X)
  let eFunY : eqv.functor.obj Y ≅ Over.mk σY := Over.isoMk (α.app Y) (hrel Y)
  let eX : X ≅ eqv.inverse.obj (Over.mk (OverShriek.relocalizeToYoneda g X)) :=
    eqv.unitIso.app X ≪≫ eqv.inverse.mapIso eFunX
  let eY : Y ≅ eqv.inverse.obj (Over.mk σY) := eqv.unitIso.app Y ≪≫ eqv.inverse.mapIso eFunY
  let p : (Functor.const R.Iᵒᵖ).obj X ⟶ D :=
    (Functor.const R.Iᵒᵖ).map eX.hom ≫ (eqv.inverse.mapCone cOv).π
  have hp : IsLimit (Cone.mk X p) :=
    IsLimit.ofIsoLimit hD (Cone.ext eX.symm (fun x => by simp [p]))
  let mOv : ∀ i, Aov.obj i ⟶ Over.mk σY := fun i => Over.homMk (q i) rfl
  let t : D ⟶ (Functor.const R.Iᵒᵖ).obj Y :=
    { app := fun i => eqv.inverse.map (mOv i) ≫ eY.inv
      naturality := fun i j a => by
        change eqv.inverse.map (Aov.map a) ≫ eqv.inverse.map (mOv j) ≫ eY.inv =
          (eqv.inverse.map (mOv i) ≫ eY.inv) ≫ 𝟙 Y
        rw [Category.comp_id, ← Category.assoc, ← eqv.inverse.map_comp]
        congr 2
        ext1
        exact hqnat a }
  let φ : Over.mk (OverShriek.relocalizeToYoneda g X) ⟶ Over.mk σY :=
    Over.homMk (L.map f) (relocalizeToYoneda_naturality B S _ hS hZ g f)
  have hfun : eFunX.hom ≫ φ = eqv.functor.map f ≫ eFunY.hom :=
    Over.OverMorphism.ext (α.hom.naturality f).symm
  have hnat : ∀ {A B : Over YS} (u : A ⟶ B), L.map (eqv.inverse.map u) =
      α.inv.app (eqv.inverse.obj A) ≫ (eqv.functor.map (eqv.inverse.map u)).left ≫
        α.hom.app (eqv.inverse.obj B) := fun u => (NatIso.naturality_1 α _).symm
  have hcounit : ∀ A : Over YS, IsIso (eqv.counit.app A).left := fun A =>
    (Over.forget YS).map_isIso (eqv.counit.app A)
  have hcounitInv : ∀ A : Over YS, IsIso (eqv.counitInv.app A).left := fun A =>
    (Over.forget YS).map_isIso (eqv.counitInv.app A)
  refine ⟨R.I, inferInstance, inferInstance, inferInstance, D, t, p, hp, ?_, fun i => ?_,
    fun i => ?_, fun {i j} a => ?_⟩
  · apply NatTrans.ext
    funext i
    change (eX.hom ≫ eqv.inverse.map (cOv.π.app i)) ≫ eqv.inverse.map (mOv i) ≫ eY.inv = f
    have h1 : cOv.π.app i ≫ mOv i = φ := Over.OverMorphism.ext (hsq i)
    have key : eX.hom ≫ eqv.inverse.map φ = f ≫ eY.hom := by
      simp only [eX, eY, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
        ← eqv.inverse.map_comp, hfun]
      rw [eqv.inverse.map_comp, ← Category.assoc, ← Category.assoc]
      congr 1
      exact (eqv.unit.naturality f).symm
    rw [Category.assoc, ← Category.assoc (eqv.inverse.map _), ← eqv.inverse.map_comp, h1,
      ← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S (⊤_ Scheme.{u}) hS hZ g
      (Aov.obj i) (hE i)
  · have hL : L.map (t.app i) = (α.inv.app (D.obj i) ≫ (eqv.counit.app (Aov.obj i)).left) ≫
        q i ≫ ((eqv.counitInv.app (Over.mk σY)).left ≫ α.hom.app _ ≫ L.map eY.inv) := by
      change L.map (eqv.inverse.map (mOv i) ≫ eY.inv) = _
      rw [L.map_comp, hnat, eqv.fun_inv_map]
      simp only [Over.comp_left]
      simp only [Category.assoc]
      rfl
    have hfp := isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ (q i) (L.map (t.app i))
      (inv (α.inv.app (D.obj i) ≫ (eqv.counit.app (Aov.obj i)).left))
      ((eqv.counitInv.app (Over.mk σY)).left ≫ α.hom.app _ ≫ L.map eY.inv)
      (by rw [hL, IsIso.inv_hom_id_assoc]) (hq i)
    exact ⟨(Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S (⊤_ Scheme.{u}) hS hZ g _
        (t.app i)).1 hfp.1,
      (isQuasiCompact_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g (t.app i)).1 hfp.2.1,
      (isQuasiSeparated_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g (t.app i)).1 hfp.2.2⟩
  · apply isAffineHom_of_isAffineHom_relocalizeMap B S (⊤_ Scheme.{u}) hS hZ g
    change IsAffineHom B (⊤_ Scheme.{u}) hZ (L.map (eqv.inverse.map (Aov.map a)))
    rw [hnat, eqv.fun_inv_map]
    simp only [Over.comp_left, Category.assoc]
    apply isAffineHom_iso_comp
    apply isAffineHom_iso_comp
    rw [← Category.assoc]
    apply isAffineHom_comp_iso
    apply isAffineHom_comp_iso
    exact hEaff a

end AlgebraicGeometry.Space

end
