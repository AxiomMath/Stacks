module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The diagonal of the stack of polarized schemes is separated and of finite presentation

**Stacks 0DPT**: the diagonal `Δ : 𝒫olarized ⟶ 𝒫olarized × 𝒫olarized` of the stack of polarized
proper flat families of finite presentation is separated and of finite presentation. Both
properties are read as in Properties of Stacks, Section 04XB: the diagonal is representable by
algebraic spaces (Stacks 0D42), and every algebraic space representing its base change along a
scheme-valued point has the property over the scheme.

## The argument

The base change of `Δ` along a scheme-valued point `(x, y)` of `𝒫olarized × 𝒫olarized` over a
scheme `U` is the isomorphism sheaf `Isom(x, y)` on the big fppf site of `U`
(`CategoryTheory.TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff` and
`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfPoint`).

* *Separatedness, quasi-compactness and quasi-separatedness.* `Isom(x, y)` is **affine** over `U`
  (`AlgebraicGeometry.isAffineHom_toYonedaId_polarizedIsomPresheaf`): for an affine scheme
  `W₀ ⟶ U`, the isomorphisms of the pullbacks of `x` and `y` to affine test schemes over `W₀`
  are corepresented by a ring `H` over `Γ(W₀, 𝒪)`
  (`AlgebraicGeometry.PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection`,
  the affine core of Stacks 0D42), so `Spec H` and `Isom(x, y) ×_U W₀` agree on affine test
  objects (`AlgebraicGeometry.exists_bijective_polarizedIsomPresheaf_specAlgebraObj`); both are
  fppf sheaves, so they are isomorphic, and the base change of `Isom(x, y) ⟶ U` to `W₀` is the
  affine scheme `Spec H`. An affine morphism of algebraic spaces is separated and quasi-compact.
  This replaces the source's comparison of `Isom(x, y)` with `Isom_U(Y, X)` and `Mor_U(Y, X)`
  (Stacks 0DPN, 0DPP, 0DPQ, 0DPR, 0DLW and the Hilbert polynomial bound through 0BEM, 0B9T), whose
  only output is that `Isom(x, y)` is separated and quasi-compact over a Noetherian affine `U`.
* *Local finite presentation.* As in the source, this comes from `𝒫olarized` being limit
  preserving (Stacks 0D43): a section of `Isom(x, y)` over an affine inverse limit descends to a
  finite stage (the fullness half of Stacks 07XL), which is the surjectivity criterion of
  Stacks 0CM6 for `Isom(x, y) ⟶ U`. This is the argument of Stacks 0CXI
  (`AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal`), stopped at local finite
  presentation.

## Main results

* `AlgebraicGeometry.isAffineHom_toYonedaId_polarizedIsomPresheaf`: `Isom(x, y) ⟶ U` is affine.
* `AlgebraicGeometry.isAffineHom_diagonal_polarizedStackUnconditional`: the diagonal of
  `𝒫olarized` is affine in the sense of Stacks 04XB.
* `AlgebraicGeometry.isLocallyOfFinitePresentation_diagonal_polarizedStackUnconditional`: it is
  locally of finite presentation in that sense.
* `AlgebraicGeometry.diagonal_polarizedStackUnconditional_isSeparated_isFinitePresentation`:
  **Stacks 0DPT**.

## References

* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_polarizedDiagonalUnconditional
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_polarizedDiagonalUnconditional
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ R) (b : Q ⟶ R) :
    HasLimit (cospan a b) :=
  (hasPullbacks_presheaf_polarizedDiagonalUnconditional (B := B) (S := S) (hS := hS)).has_limit _

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **The isomorphism sheaf of two polarized families is affine over the base.** For objects `x`,
`y` of `𝒫olarized` over `U`, the structure morphism of `Isom(x, y)` to the terminal object of
the big fppf site of `U` is affine (Stacks 03WF): its base change along an affine `W₀ ⟶ U` is
represented by `Spec H`, for `H` the ring corepresenting the isomorphisms of the pullbacks of `x`
and `y` over affine test schemes over `W₀`. -/
theorem isAffineHom_toYonedaId_polarizedIsomPresheaf (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    Space.IsAffineHom B U.left.obj U.left.property
      (Space.toYonedaId B U.left.obj U.left.property (polarizedIsomPresheaf B hS hT U x y)) := by
  intro Z g
  let W₀ := (BigAffineFppf.inclusion B U.left.obj U.left.property).obj Z
  have hW₀ : IsAffine ((BigFppfOver.toScheme B U.left.obj U.left.property).obj W₀) := Z.property
  have : IsAffine (B.inclusion.obj (polarizedRestriction B hS hT U x W₀).1.base) :=
    isAffine_polarizedRestriction_base B hS hT U x W₀ hW₀
  obtain ⟨H, _, ι, hcard, hrep⟩ :=
    PolarizedFamily.exists_corepresentation_isoOverBase_of_sectionBijection
      Stacks.AlgebraicGeometry.ProjectiveDeformation.polarizedIsoSectionBijection _ _
      (polarizedRestriction_base_eq_base B hS hT U x y W₀)
  have hsize : (Spec (CommRingCat.of H)).size ≤ W₀.left.obj.size := by
    rw [Scheme.size_Spec]
    refine max_le W₀.left.obj.aleph0_le_size
      (hcard.trans (max_le W₀.left.obj.aleph0_le_size ?_))
    refine ((B.inclusion.obj _).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans ?_
    exact (Scheme.size_congr (eqToIso (congrArg B.inclusion.obj
      (polarizedRestriction_base B hS hT U x W₀)))).le
  have hH : B.Contains (Spec (CommRingCat.of H)) := hsize.trans_lt W₀.left.property
  obtain ⟨p, hp⟩ := exists_bijective_polarizedIsomPresheaf_specAlgebraObj B hS hT U x y W₀ H ι
    hH hrep
  let top : BigFppfOver B U.left.obj U.left.property := Over.mk (𝟙 (B.obj U.left.property))
  have hterm : IsTerminal top := Over.mkIdTerminal
  let q := BigFppfOver.specAlgebraHom B U.left.property
    (polarizedRestriction_base B hS hT U x W₀) ι hH
  let h := Space.toYonedaId B U.left.obj U.left.property (polarizedIsomPresheaf B hS hT U x y)
  refine ⟨⟨BigFppfOver.specAlgebraObj B U.left.property
    (polarizedRestriction_base B hS hT U x W₀) ι hH,
      (show IsAffine (Spec (CommRingCat.of H)) from inferInstance)⟩, p, q, ?_⟩
  have hw : p ≫ h = yoneda.map q ≫ g := by
    ext T s
    exact hterm.hom_ext _ _
  let l := pullback.lift p (yoneda.map q) hw
  have hl : IsIso l := by
    refine Space.isIso_of_bijective_app_of_isAffine
      (BigFppfOver.isSheaf_yoneda_obj B U.left.obj U.left.property _)
      (BigFppfOver.isSheaf_pullback_yoneda_obj h g (isSheaf_polarizedIsomPresheaf B hS hT U x y)
        (BigFppfOver.isSheaf_yoneda_obj B U.left.obj U.left.property top)) l fun T hTa => ?_
    have hsq := (IsPullback.of_hasPullback h g).map
      ((evaluation (BigFppfOver B U.left.obj U.left.property)ᵒᵖ (Type u)).obj (op T))
    have e1 : ∀ z, (pullback.fst h g).app (op T) (l.app (op T) z) = p.app (op T) z :=
      fun z => congrArg (fun φ => φ.app (op T) z) (pullback.lift_fst _ _ hw)
    have e2 : ∀ z, (pullback.snd h g).app (op T) (l.app (op T) z) = z ≫ q :=
      fun z => congrArg (fun φ => φ.app (op T) z) (pullback.lift_snd _ _ hw)
    refine ⟨fun a b hab => (hp T hTa).1 ?_, fun z => ?_⟩
    · exact Prod.ext ((e1 a).symm.trans ((congrArg _ hab).trans (e1 b)))
        ((e2 a).symm.trans ((congrArg _ hab).trans (e2 b)))
    · obtain ⟨a, ha⟩ := (hp T hTa).2
        ((pullback.fst h g).app (op T) z, (pullback.snd h g).app (op T) z)
      exact ⟨a, Types.ext_of_isPullback hsq ((e1 a).trans (congrArg Prod.fst ha))
        ((e2 a).trans (congrArg Prod.snd ha))⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso l) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- **The diagonal of `𝒫olarized` is affine**, in the sense of Stacks 04XB: every algebraic
space representing a base change of `Δ : 𝒫olarized ⟶ 𝒫olarized × 𝒫olarized` along a
scheme-valued point over `U` is affine over `U`, read over `S` (Stacks 04SG). The base change is
`Isom(x, y)`, which is affine by
`AlgebraicGeometry.isAffineHom_toYonedaId_polarizedIsomPresheaf`. -/
theorem isAffineHom_diagonal_polarizedStackUnconditional :
    Stack.IsAffineHom B S hS
      (Stack.diagonal.{u, u, u + 1} B S hS (polarizedStackUnconditional B hS hT)) := by
  intro U y hy F hF hE
  have hp := (polarizedStackUnconditional B hS hT).isFiberedInGroupoids
  obtain ⟨e⟩ := (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp hy F).mp hE
  let iI : F ≅ polarizedIsomPresheaf B hS hT U _ _ :=
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e).symm ≪≫
      Functor.vertHomPresheafIsoIsomPresheafOfPoint _ hp U y hy
  refine (Stack.prop_algebraicSpaceMap_iff B S hS
    (fun _ _ f => Space.IsAffineHom B S hS f.hom) U F hF).2 ?_
  show Space.IsAffineHom B S hS (OverShriek.relocalizeToYoneda U.hom F)
  have _ := isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom F]
  refine Space.isAffineHom_comp_iso _
    (Space.isAffineHom_relocalize B U.left.1 U.left.2 hS U.hom ?_)
  have hfac : Space.toYonedaId B U.left.1 U.left.2 F =
      iI.hom ≫ Space.toYonedaId B U.left.1 U.left.2 (polarizedIsomPresheaf B hS hT U _ _) := by
    ext T s
    exact Over.mkIdTerminal.hom_ext _ _
  rw [hfac]
  exact Space.isAffineHom_iso_comp _ (isAffineHom_toYonedaId_polarizedIsomPresheaf B hS hT U _ _)

/-- **The diagonal of `𝒫olarized` is locally of finite presentation**, in the sense of Stacks
04XB: every algebraic space representing a base change of `Δ : 𝒫olarized ⟶ 𝒫olarized × 𝒫olarized`
along a scheme-valued point over `U` is locally of finite presentation over `U`, read over `S`. -/
theorem isLocallyOfFinitePresentation_diagonal_polarizedStackUnconditional
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
        (polarizedStackUnconditional B hS hT)).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
        (polarizedStackUnconditional B hS hT)).val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (polarizedStackUnconditional B hS hT).val.p
        (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
          (polarizedStackUnconditional B hS hT)).val.p y
        (CatFiberedInGroupoids.homFunctor
          (Stack.diagonal.{u, u, u + 1} B S hS (polarizedStackUnconditional B hS hT))))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Space.IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  classical
  let 𝒳 := polarizedStackUnconditional B hS hT
  have h𝒳 := isLimitPreservingPolarizedUnconditional B hS hT
  let Ppre : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g
  have _ : Ppre.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  let Q : MorphismProperty (AlgebraicSpaces B S hS) := Ppre.inverseImage (ObjectProperty.ι _)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine (Stack.prop_algebraicSpaceMap_iff B S hS Q U F hF).2 ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) F).mpr ?_
  refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B U.left.1 U.left.2 hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  intro I _ _ D c hc hDaff hcaff x yy _hxy
  have : Nonempty I := IsCofiltered.nonempty
  have hp := 𝒳.isFiberedInGroupoids
  have hfib : 𝒳.val.p.IsFibered := hp.isFibered
  obtain ⟨e⟩ := (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp hy F).mp hE
  let pe := PresheafOfCategories.PointwiseEquiv.ofUliftIso e
  have haff : ∀ i, IsAffineOver B S hS ((D ⋙ Over.map U.hom).obj i) := fun i => hDaff i
  have hcaff' : IsAffineOver B S hS ((Over.map U.hom).obj c.pt) := hcaff
  set D' : I ⥤ BigAffineFppf B S hS :=
    (IsAffineOver B S hS).lift (D ⋙ Over.map U.hom) haff with hD'def
  set c' : Cone D' :=
    { pt := ⟨(Over.map U.hom).obj c.pt, hcaff'⟩
      π :=
        { app := fun i => ObjectProperty.homMk ((Over.map U.hom).map (c.π.app i))
          naturality := fun i j f => by
            apply ObjectProperty.hom_ext
            show 𝟙 _ ≫ (Over.map U.hom).map (c.π.app j) =
              (Over.map U.hom).map (c.π.app i) ≫ (Over.map U.hom).map (D.map f)
            rw [Category.id_comp, ← Functor.map_comp, c.w f] } } with hc'def
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
  have : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')).Full := (h𝒳 I D' c' hc').full
  have hdesc : Deformation.Artin.DescentHom 𝒳.val.p (D ⋙ Over.map U.hom)
      ((Over.map U.hom).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒳.val.p hp
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')
  obtain ⟨k, χ, hχ⟩ :=
    TwoFibreProductOver.DiagonalFibre.VertHom.exists_restrict_eq_of_descentHom hp
      (TwoFibreProductOver.DiagonalFibre.h1' hy) (TwoFibreProductOver.DiagonalFibre.h2' hy)
      D c hdesc ((pe.equiv (op c.pt)).symm x)
  refine ⟨colimit.ι (D.op ⋙ F) (op k) (pe.equiv (op (D.obj k)) χ), ?_, ?_⟩
  · rw [colimit.ι_desc_apply]
    refine Eq.trans ?_ ((pe.equiv (op c.pt)).apply_symm_apply x)
    rw [← hχ, ← TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_map]
    exact (pe.naturality (c.π.app k).op χ).symm
  · have : Subsingleton (colimit (D.op ⋙ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) := by
      refine Stack.subsingleton_colimit_of_subsingleton _ (fun j => ?_)
      exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩
    exact this.elim _ _

/-- An affine morphism of algebraic spaces which is locally of finite presentation is separated
and of finite presentation (Stacks 03XP part (3)). -/
private theorem isSeparated_isFinitePresentation_of_isAffineHom (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (ha : Space.IsAffineHom B S hS f.hom) (hl : Space.IsLocallyOfFinitePresentation B S hS f.hom) :
    Space.IsSeparated B S hS f.hom ∧ Space.IsFinitePresentation B S hS f.hom := by
  have hsep := Space.isSeparated_of_isAffineHom B S hS f.hom X.2 Y.2 ha
  exact ⟨hsep, hl, Space.isQuasiCompact_of_isAffineHom' B S hS f.hom X.2 Y.2 ha,
    Space.isQuasiSeparated_of_isSeparated B S hS hsep⟩

/-- **Stacks 0DPT.** The diagonal `Δ : 𝒫olarized ⟶ 𝒫olarized × 𝒫olarized` of the stack of
polarized proper flat families of finite presentation, over the big fppf site of a terminal base
scheme, is separated and of finite presentation, both read as in Properties of Stacks,
Section 04XB: `Δ` is representable by algebraic spaces (Stacks 0D42), and every algebraic space
representing its base change along a scheme-valued point over a scheme `U` is separated (Stacks
03HL) and of finite presentation (Stacks 03XP, part (3)) over `U`, read over the base (Stacks
04SG). -/
@[stacks 0DPT]
theorem diagonal_polarizedStackUnconditional_isSeparated_isFinitePresentation :
    Stack.HasRepresentableDiagonal B S hS (polarizedStackUnconditional B hS hT) ∧
      Stack.IsSeparated B S hS
        (Stack.diagonal.{u, u, u + 1} B S hS (polarizedStackUnconditional B hS hT)) ∧
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
            (polarizedStackUnconditional B hS hT)).val.obj)
        (_hy : y ⋙ (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
            (polarizedStackUnconditional B hS hT)).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (polarizedStackUnconditional B hS hT).val.p
            (CatFiberedInGroupoids.product (polarizedStackUnconditional B hS hT)
              (polarizedStackUnconditional B hS hT)).val.p y
            (CatFiberedInGroupoids.homFunctor
              (Stack.diagonal.{u, u, u + 1} B S hS (polarizedStackUnconditional B hS hT))))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsFinitePresentation B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  refine ⟨hasRepresentableDiagonal_polarizedStackUnconditional B hS hT, fun U y hy F hF hE => ?_,
    fun U y hy F hF hE => ?_⟩ <;>
  · have h := isSeparated_isFinitePresentation_of_isAffineHom B S hS _
      (isAffineHom_diagonal_polarizedStackUnconditional B hS hT U y hy F hF hE)
      (isLocallyOfFinitePresentation_diagonal_polarizedStackUnconditional B hS hT U y hy F hF
        hE)
    first | exact h.1 | exact h.2

end AlgebraicGeometry

end
