module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSquareGlueing
import all StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.FlatOver
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatCompositionUnassumed
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceComposition

/-!
# Flattening a morphism of finite type by blowing up: the induction

Let `Y` be a quasi-compact and quasi-separated algebraic space.  We say that `Y` *flattens over
its blowups* when for every blowup `Y₁ ⟶ Y` in a finitely presented centre, every quasi-compact
open `Ω ⊆ Y₁` and every `f : X ⟶ Y₁` of finite type and quasi-separated which is flat and
locally of finite presentation over `Ω`, there is an `Ω`-admissible blowup of `Y₁` along which
the strict transform of `X` is flat and locally of finite presentation.

If `(U ⊆ Y, V ⟶ Y)` is an elementary distinguished square with `U` quasi-compact and `V` affine,
and `U` and `V` flatten over their blowups, then so does `Y`.  Hence every quasi-compact and
quasi-separated algebraic space flattens over its blowups as soon as the affine ones do.

## Main definitions

* `AlgebraicGeometry.Space.FlattensOverBlowups`: the property above.

## Main results

* `AlgebraicGeometry.Space.flattensOverBlowups_of_isElementaryDistinguishedSquare`: the property
  passes from the members of an elementary distinguished square to the space.
* `AlgebraicGeometry.Space.flattensOverBlowups_of_isQuasiCompactSpace`: every quasi-compact and
  quasi-separated algebraic space flattens over its blowups as soon as the affine ones do.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0865](https://stacks.math.columbia.edu/tag/0865)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Blowups and strict transforms -/

/-- A pullback square of the underlying functors is a pullback square of algebraic spaces. -/
private theorem isPullback_of_isPullback_hom {W X Y Z : AlgebraicSpaces B S hS} {a : W ⟶ Z}
    {b : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback a.hom b.hom g.hom f.hom) :
    IsPullback a b g f :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq

/-- Precomposing a flat and locally finitely presented morphism with an étale one keeps it so. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_comp_of_isEtale
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H) {f : F ⟶ G} {g : G ⟶ H}
    (hf : IsEtale B S hS f) (hg : IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g) :
    IsFlat B S hS (f ≫ g) ∧ IsLocallyOfFinitePresentation B S hS (f ≫ g) :=
  ⟨isFlat_comp B S hS hF hG hH _ _ (isFlat_of_isEtale B S hS hf) hg.1,
    isLocallyOfFinitePresentation_comp B S hS hF hG hH _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS hf) hg.2⟩

/-- Finite type and quasi-separatedness pass to base changes. -/
theorem isFiniteType_and_isQuasiSeparated_of_isPullback
    {W X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ Z'} {b : W ⟶ X'} {g : Z' ⟶ Y'} {f : X' ⟶ Y'}
    (sq : IsPullback a b g f) (hW : IsAlgebraicSpace B S hS W) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (hZ' : IsAlgebraicSpace B S hS Z')
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsFiniteType B S hS a ∧ IsQuasiSeparated B S hS a := by
  let Wa : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Xa : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Ya : AlgebraicSpaces B S hS := ⟨Y', hY'⟩
  let Za : AlgebraicSpaces B S hS := ⟨Z', hZ'⟩
  have sqa : IsPullback (ObjectProperty.homMk b : Wa ⟶ Xa) (ObjectProperty.homMk a : Wa ⟶ Za)
      (ObjectProperty.homMk f : Xa ⟶ Ya) (ObjectProperty.homMk g : Za ⟶ Ya) :=
    isPullback_of_isPullback_hom sq.flip
  exact ⟨⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sqa hft.1,
      isQuasiCompact_of_isPullback B S hS sq.flip hft.2⟩,
    isQuasiSeparated_of_isPullback B S hS sq.flip hqs⟩

/-- The strict transform of a morphism of finite type and quasi-separated is of finite type and
quasi-separated over the blowup. -/
theorem isFiniteType_and_isQuasiSeparated_strictTransformSpaceToBlowUp
    {A A' X : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1)
    (hft : IsFiniteType B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) :
    IsFiniteType B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom ∧
      IsQuasiSeparated B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom := by
  have hcl := strictTransformSubfunctor_isClosedSubspace B S hS f b E
  have hP := (strictTransformPullback B S hS f b).2
  obtain ⟨hft', hqs'⟩ := isFiniteType_and_isQuasiSeparated_of_isPullback
    (IsPullback.of_hasPullback f.hom b.hom).flip hP X.2 A.2 A'.2 hft hqs
  exact ⟨⟨isLocallyOfFiniteType_comp B S hS hcl.1 hP A'.2 _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _ hcl.2) hft'.1,
    isQuasiCompact_comp B S hS hP A'.2 _ _ (isQuasiCompact_of_isClosedImmersion' B S hS hcl.2)
      hft'.2⟩,
    isQuasiSeparated_comp B S hS hcl.1 hP _ _ (isQuasiSeparated_of_isClosedImmersion B S hS hcl.2)
      hqs'⟩

/-- **A flat chart needs no blowup**: the strict transform of a flat and locally finitely
presented `w : X ⟶ V` along any blowup `v' : V' ⟶ V` is the whole base change (Stacks 0865,
part (1)), hence flat and locally of finite presentation over `V'`. -/
theorem isFlat_strictTransformSpaceToBlowUp_of_isFlat {V V' X : AlgebraicSpaces B S hS}
    (w : X ⟶ V) (hw : IsFlat B S hS w.hom) (hwl : IsLocallyOfFinitePresentation B S hS w.hom)
    {Z : ClosedSubspaces B S hS V.1} {v' : V' ⟶ V} (hv' : IsBlowupAlong B S hS Z v') :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS w v' (Z.1.preimage v'.hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS w v' (Z.1.preimage v'.hom)).hom := by
  have hT := strictTransformSubfunctor_eq_top_of_isFlatAt_unconditional B S hS w v' Z hv'
    (fun x _ => (isFlat_iff_forall_isFlatAt B S hS w.hom).1 hw x)
  have hP := (strictTransformPullback B S hS w v').2
  have key : ∀ T : Subfunctor (pullback w.hom v'.hom), T = ⊤ →
      IsFlat B S hS (T.ι ≫ pullback.snd w.hom v'.hom) ∧
        IsLocallyOfFinitePresentation B S hS (T.ι ≫ pullback.snd w.hom v'.hom) := by
    rintro T rfl
    have hsq := (IsPullback.of_hasPullback w.hom v'.hom).flip
    have hT : IsAlgebraicSpace B S hS (⊤ : Subfunctor (pullback w.hom v'.hom)).toFunctor :=
      isAlgebraicSpace_of_iso B S hS (asIso (⊤ : Subfunctor (pullback w.hom v'.hom)).ι).symm
        (isAlgebraicSpace_pullback B S hS w.hom v'.hom X.2 V'.2 V.2)
    have hι := isEtale_of_isIso B S hS (⊤ : Subfunctor (pullback w.hom v'.hom)).ι
    exact isFlat_and_isLocallyOfFinitePresentation_comp_of_isEtale hT hP V'.2 hι
      ⟨isFlat_of_isPullback_of_isAlgebraicSpace B S hS hsq X.2 V.2 hw,
        isLocallyOfFinitePresentation_of_isPullback_of_isAlgebraicSpace hsq hP X.2 V.2 V'.2 hwl⟩
  exact key _ hT

/-- **The flatness of a strict transform does not depend on the choice of the blowup**: if the
strict transform of `f` along one blowup of `A` in `Z` is flat and locally of finite
presentation, so is its strict transform along any other. -/
theorem isFlat_strictTransformSpaceToBlowUp_of_isBlowupAlong {A A' A'' X : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A} {b' : A'' ⟶ A} (hb : IsBlowupAlong B S hS Z b)
    (hb' : IsBlowupAlong B S hS Z b') (f : X ⟶ A)
    (h : IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom) :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b' (Z.1.preimage b'.hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS f b' (Z.1.preimage b'.hom)).hom := by
  have hpre : preimageClosedSubspace (𝟙 A) Z = Z := Subtype.ext (Subfunctor.preimage_id Z.1)
  obtain ⟨m, hm⟩ := (hb.existsUnique_lift b' hb'.isPullbackDefined).exists
  have hb'' : IsBlowupAlong B S hS (preimageClosedSubspace (𝟙 A) Z) b' := by rwa [hpre]
  have hex := exists_isPullback_strictTransformSpaceToBlowUp_of_isEtale hb f (v := 𝟙 A)
    (isEtale_of_isIso B S hS (𝟙 A.1)) (u := 𝟙 X) (w := f) (isEtale_of_isIso B S hS (𝟙 X.1))
    IsPullback.of_id_fst hb'' m (by rw [Category.comp_id, hm])
  rw [hpre] at hex
  obtain ⟨a, -, hsq⟩ := hex
  exact ⟨isFlat_of_isPullback_of_isAlgebraicSpace B S hS hsq.flip
      (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2 A'.2 h.1,
    isLocallyOfFinitePresentation_of_isPullback_of_isAlgebraicSpace hsq.flip
      (strictTransformSpace B S hS f b' (Z.1.preimage b'.hom)).2
      (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2 A'.2 A''.2 h.2⟩

/-- The inverse image of a finitely presented closed subspace is finitely presented. -/
theorem isFinitePresentation_preimageClosedSubspace {X Y : AlgebraicSpaces B S hS} (v : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsFinitePresentation B S hS Z.1.ι) :
    IsFinitePresentation B S hS (preimageClosedSubspace v Z).1.ι :=
  isFinitePresentation_of_isPullback B S hS (preimageClosedSubspace v Z).2.1 Z.2.1 Y.2 X.2
    (Subfunctor.isPullback_preimage v.hom Z.1) hZ

/-- The inverse image of an open subspace, as an algebraic space with its inclusion. -/
abbrev openPreimage {X Y : AlgebraicSpaces B S hS} (v : Y ⟶ X) (N : Subfunctor X.1)
    (hN : IsOpenSubspace B S hS N) : AlgebraicSpaces B S hS :=
  ⟨(N.preimage v.hom).toFunctor, (isOpenSubspace_preimage B S hS v.hom N X.2 Y.2 hN).1⟩

/-- **A blowup restricted over an open subspace**: for an open subspace `N ⊆ A` and a blowup
`b : A' ⟶ A` in `Z`, the morphism `b⁻¹(N) ⟶ N` is the blowup of `N` in `N ∩ Z`. -/
theorem isBlowupAlong_fromPreimage {A A' : AlgebraicSpaces B S hS} (N : Subfunctor A.1)
    (hN : IsOpenSubspace B S hS N) {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) :
    IsBlowupAlong B S hS
      (preimageClosedSubspace (ObjectProperty.homMk N.ι : (⟨N.toFunctor, hN.1⟩ :
        AlgebraicSpaces B S hS) ⟶ A) Z)
      (ObjectProperty.homMk (N.fromPreimage b.hom) :
        openPreimage b N hN ⟶ ⟨N.toFunctor, hN.1⟩) := by
  let NA : AlgebraicSpaces B S hS := ⟨N.toFunctor, hN.1⟩
  let ιN : NA ⟶ A := ObjectProperty.homMk N.ι
  have hsq : IsPullback (ObjectProperty.homMk (N.fromPreimage b.hom) : openPreimage b N hN ⟶ NA)
      (ObjectProperty.homMk (N.preimage b.hom).ι : openPreimage b N hN ⟶ A') ιN b :=
    isPullback_of_isPullback_hom (Subfunctor.isPullback_preimage b.hom N)
  have hg : IsFlat B S hS ιN.hom :=
    isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS hN.2)
  exact isBlowupAlong_preimage_of_isPullback_of_isFlat hg hb hsq

/-- **Flatness of the strict transform over an open subspace of the blowup, read on the open
subspace of the base.**  Let `b : A' ⟶ A` be a blowup in `Z` and `N ⊆ A` open.  If the strict
transform of `f⁻¹(N) ⟶ N` along `b⁻¹(N) ⟶ N` is flat and locally of finite presentation, then
the strict transform of `X` along `b` is flat and locally of finite presentation over
`b⁻¹(N)`. -/
theorem flatOver_strictTransformSpaceToBlowUp_preimage {A A' X : AlgebraicSpaces B S hS}
    (f : X ⟶ A) {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A} (hb : IsBlowupAlong B S hS Z b)
    (N : Subfunctor A.1) (hN : IsOpenSubspace B S hS N)
    (h : IsFlat B S hS (strictTransformSpaceToBlowUp B S hS
        (ObjectProperty.homMk (N.fromPreimage f.hom) : openPreimage f N hN ⟶ ⟨N.toFunctor, hN.1⟩)
        (ObjectProperty.homMk (N.fromPreimage b.hom) : openPreimage b N hN ⟶ ⟨N.toFunctor, hN.1⟩)
        ((preimageClosedSubspace (ObjectProperty.homMk N.ι : (⟨N.toFunctor, hN.1⟩ :
          AlgebraicSpaces B S hS) ⟶ A) Z).1.preimage (N.fromPreimage b.hom))).hom ∧
      IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
        (ObjectProperty.homMk (N.fromPreimage f.hom) : openPreimage f N hN ⟶ ⟨N.toFunctor, hN.1⟩)
        (ObjectProperty.homMk (N.fromPreimage b.hom) : openPreimage b N hN ⟶ ⟨N.toFunctor, hN.1⟩)
        ((preimageClosedSubspace (ObjectProperty.homMk N.ι : (⟨N.toFunctor, hN.1⟩ :
          AlgebraicSpaces B S hS) ⟶ A) Z).1.preimage (N.fromPreimage b.hom))).hom) :
    FlatOver (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) (N.preimage b.hom) := by
  have hN' := isOpenSubspace_preimage B S hS b.hom N A.2 A'.2 hN
  let NA : AlgebraicSpaces B S hS := ⟨N.toFunctor, hN.1⟩
  let v : NA ⟶ A := ObjectProperty.homMk N.ι
  let u : openPreimage f N hN ⟶ X := ObjectProperty.homMk (N.preimage f.hom).ι
  let w : openPreimage f N hN ⟶ NA := ObjectProperty.homMk (N.fromPreimage f.hom)
  let v' : openPreimage b N hN ⟶ NA := ObjectProperty.homMk (N.fromPreimage b.hom)
  let m : openPreimage b N hN ⟶ A' := ObjectProperty.homMk (N.preimage b.hom).ι
  have hv : IsEtale B S hS v.hom := isEtale_of_isOpenImmersion B S hS hN.2
  have hu : IsEtale B S hS u.hom :=
    isEtale_of_isOpenImmersion B S hS (isOpenSubspace_preimage B S hS f.hom N A.2 X.2 hN).2
  have hU : IsPullback u.hom w.hom f.hom v.hom := (Subfunctor.isPullback_preimage f.hom N).flip
  have hm : m ≫ b = v' ≫ v := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι N b.hom).symm
  obtain ⟨a, -, hsq⟩ := exists_isPullback_strictTransformSpaceToBlowUp_of_isEtale hb f hv hu hU
    (isBlowupAlong_fromPreimage N hN hb) m hm
  exact (flatOver_iff_of_isPullback hN' (strictTransformSpace B S hS w v' _).2 hsq).2 h

/-- **A flat chart over an open subspace needs no blowup**: if `f` is flat and locally of finite
presentation over an open `N`, so is its strict transform along a blowup, over `b⁻¹(N)`. -/
private theorem flatOver_strictTransformSpaceToBlowUp_preimage_of_flatOver
    {A A' X : AlgebraicSpaces B S hS} (f : X ⟶ A) {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) {N : Subfunctor A.1} (hN : IsOpenSubspace B S hS N)
    (hfo : FlatOver f N) :
    FlatOver (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) (N.preimage b.hom) :=
  flatOver_strictTransformSpaceToBlowUp_preimage f hb N hN
    (isFlat_strictTransformSpaceToBlowUp_of_isFlat _ hfo.1 hfo.2
      (isBlowupAlong_fromPreimage N hN hb))

/-! ### The property, and flattening over the open member of a square -/

/-- `Y` **flattens over its blowups**: for every blowup `c : Y₁ ⟶ Y` in a finitely presented
centre, every quasi-compact open `Ω ⊆ Y₁` and every `f : X ⟶ Y₁` of finite type and
quasi-separated which is flat and locally of finite presentation over `Ω`, there is an
`Ω`-admissible blowup of `Y₁` along which the strict transform of `X` is flat and locally of
finite presentation. -/
def FlattensOverBlowups (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ ⦃Y₁ : AlgebraicSpaces B S hS⦄ (c : Y₁ ⟶ Y) (Zc : ClosedSubspaces B S hS Y.1),
    IsFinitePresentation B S hS Zc.1.ι → IsBlowupAlong B S hS Zc c →
    ∀ (Ω : OpenSubspaces B S hS Y₁.1), IsQuasiCompactSpace B S hS Ω.1.toFunctor →
    ∀ ⦃X : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y₁), IsFiniteType B S hS f.hom →
      IsQuasiSeparated B S hS f.hom → FlatOver f Ω.1 → FlattensByBlowup f Ω

/-- **Flattening over the open member.** Let `U ⊆ Y` be a quasi-compact open subspace of a
quasi-compact and quasi-separated `Y` which flattens over its blowups, let `c : Y₁ ⟶ Y` be a blowup
in a finitely presented centre, `Ω ⊆ Y₁` a quasi-compact open subspace and `f : X ⟶ Y₁` of finite
type and quasi-separated, flat and locally of finite presentation over `Ω`. Then there is an
`Ω`-admissible blowup `b₁ : Y₂ ⟶ Y₁` along which the strict transform of `X` is flat and locally of
finite presentation over `b₁⁻¹(c⁻¹U)` and over `b₁⁻¹Ω`. -/
theorem exists_isBlowupAlong_flatOver_of_flattensOverBlowups_open
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y Y₁ : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (U : Subfunctor Y.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hQU : FlattensOverBlowups (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS))
    {c : Y₁ ⟶ Y} {Zc : ClosedSubspaces B S hS Y.1} (hZcfp : IsFinitePresentation B S hS Zc.1.ι)
    (hc : IsBlowupAlong B S hS Zc c) (Ω : Subfunctor Y₁.1) (hΩ : IsOpenSubspace B S hS Ω)
    (hΩqc : IsQuasiCompactSpace B S hS Ω.toFunctor) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ Y₁) (hft : IsFiniteType B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (hfo : FlatOver f Ω) :
    ∃ (Y₂ : AlgebraicSpaces B S hS) (b₁ : Y₂ ⟶ Y₁) (Z₁ : ClosedSubspaces B S hS Y₁.1),
      IsFinitePresentation B S hS Z₁.1.ι ∧
        Disjoint (subspacePointSet B S hS Y₁.1 Ω) (subspacePointSet B S hS Y₁.1 Z₁.1) ∧
        IsBlowupAlong B S hS Z₁ b₁ ∧
        FlatOver (strictTransformSpaceToBlowUp B S hS f b₁ (Z₁.1.preimage b₁.hom))
          ((U.preimage c.hom).preimage b₁.hom) ∧
        FlatOver (strictTransformSpaceToBlowUp B S hS f b₁ (Z₁.1.preimage b₁.hom))
          (Ω.preimage b₁.hom) := by
  obtain ⟨hY₁qc, hY₁qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hYqc hYqs hZcfp hc
  set U₁ := U.preimage c.hom with hU₁def
  have hU₁ : IsOpenSubspace B S hS U₁ := isOpenSubspace_preimage B S hS c.hom U Y.2 Y₁.2 hU
  have hU₁qc : IsQuasiCompactSpace B S hS U₁.toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y.2 hYqs Y₁.2 hY₁qc U hUqc c.hom
  let UA : AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  let ιU : UA ⟶ Y := ObjectProperty.homMk U.ι
  let U₁A : AlgebraicSpaces B S hS := ⟨U₁.toFunctor, hU₁.1⟩
  let cU : U₁A ⟶ UA := ObjectProperty.homMk (U.fromPreimage c.hom)
  have hcU : IsBlowupAlong B S hS (preimageClosedSubspace ιU Zc) cU :=
    isBlowupAlong_fromPreimage U hU hc
  have hZcUfp := isFinitePresentation_preimageClosedSubspace ιU Zc hZcfp
  have hΩU : IsOpenSubspace B S hS (Ω.preimage U₁.ι) :=
    isOpenSubspace_preimage B S hS U₁.ι Ω Y₁.2 hU₁.1 hΩ
  have hΩUqc : IsQuasiCompactSpace B S hS (Ω.preimage U₁.ι).toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y₁.2 hY₁qs hU₁.1 hU₁qc Ω hΩqc U₁.ι
  let fU : openPreimage f U₁ hU₁ ⟶ U₁A := ObjectProperty.homMk (U₁.fromPreimage f.hom)
  let ιXU : openPreimage f U₁ hU₁ ⟶ X := ObjectProperty.homMk (U₁.preimage f.hom).ι
  let ιU₁ : U₁A ⟶ Y₁ := ObjectProperty.homMk U₁.ι
  have hsqXU : IsPullback ιXU.hom fU.hom f.hom ιU₁.hom :=
    (Subfunctor.isPullback_preimage f.hom U₁).flip
  obtain ⟨hftU, hqsU⟩ := isFiniteType_and_isQuasiSeparated_of_isPullback hsqXU.flip
    (openPreimage f U₁ hU₁).2 X.2 Y₁.2 hU₁.1 hft hqs
  have hfoU : FlatOver fU (Ω.preimage U₁.ι) := hfo.baseChange hΩ hsqXU
  obtain ⟨U₂, bU, ZA, hZAfp, hZAdisj, hbU, hstU⟩ :=
    hQU cU (preimageClosedSubspace ιU Zc) hZcUfp hcU ⟨Ω.preimage U₁.ι, hΩU⟩ hΩUqc fU hftU hqsU
      hfoU
  obtain ⟨Z₁, hZ₁c, hZ₁fp, hZ₁disj, hZ₁U⟩ := exists_closedSubspace_extension_disjoint hZ hY₁qc
    hY₁qs Ω U₁ hΩ hU₁ hΩqc hU₁qc ZA.1 ZA.2 hZAfp hZAdisj
  obtain ⟨Y₂, b₁, hb₁⟩ := exists_isBlowupAlong_of_isFinitePresentation (⟨Z₁, hZ₁c⟩ :
    ClosedSubspaces B S hS Y₁.1) hZ₁fp
  refine ⟨Y₂, b₁, ⟨Z₁, hZ₁c⟩, hZ₁fp, hZ₁disj, hb₁, ?_, ?_⟩
  · have hpre : preimageClosedSubspace ιU₁ (⟨Z₁, hZ₁c⟩ : ClosedSubspaces B S hS Y₁.1) = ZA :=
      Subtype.ext hZ₁U
    have hb' := isBlowupAlong_fromPreimage U₁ hU₁ hb₁
    rw [hpre] at hb'
    have h := isFlat_strictTransformSpaceToBlowUp_of_isBlowupAlong hbU hb' fU hstU
    refine flatOver_strictTransformSpaceToBlowUp_preimage f hb₁ U₁ hU₁ ?_
    rwa [hpre]
  · exact flatOver_strictTransformSpaceToBlowUp_preimage_of_flatOver f hb₁ hΩ hfo

/-! ### Flattening over the étale member of a square -/

/-- A section over an object covered by the empty sieve lies in every subsheaf. -/
theorem mem_of_bot_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {G : Subfunctor F}
    (hG : IsAlgebraicSpace B S hS G.toFunctor) {Y : BigFppfOver B S hS} (x : F.obj (Opposite.op Y))
    (hY : (⊥ : Sieve Y) ∈ BigFppfOver.topology B S hS Y) : x ∈ G.obj (Opposite.op Y) := by
  have hle := Subfunctor.sheafify_le (J := BigFppfOver.topology B S hS) (G := ⊥) (G' := G) bot_le
    ((isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf)
    ((isSheaf_iff_isSheaf_of_type _ _).1 hG.isSheaf)
  refine hle _ ?_
  change (⊥ : Subfunctor F).sieveOfSection x ∈ BigFppfOver.topology B S hS Y
  have : (⊥ : Subfunctor F).sieveOfSection x = ⊥ := le_antisymm (fun _ _ h => h) bot_le
  rwa [this]

/-- A section of the sheafified bottom subfunctor lives over an object covered by the empty
sieve. -/
theorem bot_mem_topology_of_mem_sheafify_bot {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y : BigFppfOver B S hS} {x : F.obj (Opposite.op Y)}
    (hx : x ∈ ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).obj (Opposite.op Y)) :
    (⊥ : Sieve Y) ∈ BigFppfOver.topology B S hS Y := by
  have : (⊥ : Subfunctor F).sieveOfSection x = ⊥ := le_antisymm (fun _ _ h => h) bot_le
  change (⊥ : Subfunctor F).sieveOfSection x ∈ BigFppfOver.topology B S hS Y at hx
  rwa [this] at hx

/-- **Flattening over the étale member.** Let `(U₂ ⊆ Y₂, φ₂ : V₂ ⟶ Y₂)` be an elementary
distinguished square with `Y₂` quasi-compact and quasi-separated, `V₂` quasi-compact, over which
every morphism of finite type and quasi-separated which is flat and locally of finite presentation
over a quasi-compact open is flattened by an admissible blowup. Let `g₂ : X₂ ⟶ Y₂` be of finite
type and quasi-separated, flat and locally of finite presentation over a quasi-compact open
`N ⊇ U₂`. Then there is an `N`-admissible blowup of `Y₂` along which the strict transform of `X₂`
is flat and locally of finite presentation. -/
theorem exists_isBlowupAlong_isFlat_of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y₂ V₂ : AlgebraicSpaces B S hS}
    (hY₂qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₂.1)
    (U₂ : Subfunctor Y₂.1) (φ₂ : V₂ ⟶ Y₂)
    (hsq : IsElementaryDistinguishedSquare B S hS Y₂.2 U₂ φ₂.hom)
    (hV₂qc : IsQuasiCompactSpace B S hS V₂.1)
    (hV : ∀ (Ω : OpenSubspaces B S hS V₂.1), IsQuasiCompactSpace B S hS Ω.1.toFunctor →
      ∀ ⦃X : AlgebraicSpaces B S hS⦄ (f : X ⟶ V₂), IsFiniteType B S hS f.hom →
        IsQuasiSeparated B S hS f.hom → FlatOver f Ω.1 → FlattensByBlowup f Ω)
    (N : Subfunctor Y₂.1) (hN : IsOpenSubspace B S hS N)
    (hNqc : IsQuasiCompactSpace B S hS N.toFunctor) (hUN : U₂ ≤ N) {X₂ : AlgebraicSpaces B S hS}
    (g₂ : X₂ ⟶ Y₂) (hft : IsFiniteType B S hS g₂.hom) (hqs : IsQuasiSeparated B S hS g₂.hom)
    (hfo : FlatOver g₂ N) :
    ∃ (Y₃ : AlgebraicSpaces B S hS) (b₂ : Y₃ ⟶ Y₂) (Z' : ClosedSubspaces B S hS Y₂.1),
      IsFinitePresentation B S hS Z'.1.ι ∧
        Disjoint (subspacePointSet B S hS Y₂.1 N) (subspacePointSet B S hS Y₂.1 Z'.1) ∧
        IsBlowupAlong B S hS Z' b₂ ∧
        IsFlat B S hS (strictTransformSpaceToBlowUp B S hS g₂ b₂ (Z'.1.preimage b₂.hom)).hom ∧
        IsLocallyOfFinitePresentation B S hS
          (strictTransformSpaceToBlowUp B S hS g₂ b₂ (Z'.1.preimage b₂.hom)).hom := by
  have hU₂ : IsOpenSubspace B S hS U₂ := hsq.isOpenSubspace
  have hφ₂ : IsEtale B S hS φ₂.hom := hsq.isEtale
  set ΩV := N.preimage φ₂.hom with hΩVdef
  have hΩV : IsOpenSubspace B S hS ΩV := isOpenSubspace_preimage B S hS φ₂.hom N Y₂.2 V₂.2 hN
  have hΩVqc : IsQuasiCompactSpace B S hS ΩV.toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y₂.2 hY₂qs V₂.2 hV₂qc N hNqc φ₂.hom
  let XV : AlgebraicSpaces B S hS :=
    ⟨pullback g₂.hom φ₂.hom, isAlgebraicSpace_pullback B S hS g₂.hom φ₂.hom X₂.2 V₂.2 Y₂.2⟩
  let uV : XV ⟶ X₂ := ObjectProperty.homMk (pullback.fst g₂.hom φ₂.hom)
  let fV : XV ⟶ V₂ := ObjectProperty.homMk (pullback.snd g₂.hom φ₂.hom)
  have hsqV : IsPullback uV.hom fV.hom g₂.hom φ₂.hom := IsPullback.of_hasPullback g₂.hom φ₂.hom
  obtain ⟨hftV, hqsV⟩ := isFiniteType_and_isQuasiSeparated_of_isPullback hsqV.flip XV.2 X₂.2
    Y₂.2 V₂.2 hft hqs
  have hfoV : FlatOver fV ΩV := hfo.baseChange hN hsqV
  obtain ⟨V₃, bV, ZB, hZBfp, hZBdisj, hbV, hstV⟩ := hV ⟨ΩV, hΩV⟩ hΩVqc fV hftV hqsV hfoV
  have hUΩ : subspacePointSet B S hS V₂.1 (U₂.preimage φ₂.hom) ⊆
      subspacePointSet B S hS V₂.1 ΩV := by
    change Set.range (pointsMap B S hS _ (U₂.preimage φ₂.hom).ι) ⊆
      Set.range (pointsMap B S hS _ (N.preimage φ₂.hom).ι)
    rw [range_pointsMap_preimage_ι, range_pointsMap_preimage_ι]
    refine Set.preimage_mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨pointsMap B S hS _ (Subfunctor.homOfLe hUN) y, by
      rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
  set T₀ : Subfunctor U₂.toFunctor :=
    (⊥ : Subfunctor U₂.toFunctor).sheafify (BigFppfOver.topology B S hS) with hT₀def
  have hT₀c : IsClosedSubspace B S hS T₀ := isClosedSubspace_sheafify_bot B S hS hU₂.1
  have hT₀o : IsOpenSubspace B S hS T₀ := isOpenSubspace_sheafify_bot B S hS U₂.toFunctor hU₂.1
  have hT₀fp : IsFinitePresentation B S hS T₀.ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hT₀o.2,
      isQuasiCompact_of_isClosedImmersion' B S hS hT₀c.2,
      isQuasiSeparated_of_mono B S hS _ inferInstance⟩
  have hcompat : ∀ (Y : BigFppfOver B S hS) (a : U₂.toFunctor.obj (Opposite.op Y))
      (v : V₂.1.obj (Opposite.op Y)), U₂.ι.app (Opposite.op Y) a = φ₂.hom.app (Opposite.op Y) v →
      (a ∈ T₀.obj (Opposite.op Y) ↔ v ∈ ZB.1.obj (Opposite.op Y)) := by
    intro Y a v hav
    refine ⟨fun ha => mem_of_bot_mem_topology V₂.2 ZB.2.1 v
      (bot_mem_topology_of_mem_sheafify_bot ha), fun hv => ?_⟩
    set K : Subfunctor ZB.1.toFunctor := (U₂.preimage φ₂.hom).preimage ZB.1.ι with hKdef
    have hKo : IsOpenSubspace B S hS K := isOpenSubspace_preimage B S hS ZB.1.ι _ V₂.2 ZB.2.1
      (isOpenSubspace_preimage B S hS φ₂.hom U₂ Y₂.2 V₂.2 hU₂)
    have hKpts : Set.range (pointsMap B S hS K.toFunctor K.ι) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro _ ⟨k, rfl⟩
      have h1 : pointsMap B S hS _ (K.ι ≫ ZB.1.ι) k ∈ subspacePointSet B S hS V₂.1 ZB.1 := by
        rw [pointsMap_comp_apply]; exact ⟨_, rfl⟩
      have h2 : pointsMap B S hS _ (K.ι ≫ ZB.1.ι) k ∈
          subspacePointSet B S hS V₂.1 (U₂.preimage φ₂.hom) := by
        rw [← Subfunctor.fromPreimage_ι, pointsMap_comp_apply]; exact ⟨_, rfl⟩
      exact Set.disjoint_left.1 hZBdisj (hUΩ h2) h1
    have hKeq := eq_sheafify_bot_of_range_pointsMap_ι_eq_empty B S hS ZB.1.toFunctor ZB.2.1
      hKo hKpts
    have hvK : (⟨v, hv⟩ : ZB.1.toFunctor.obj (Opposite.op Y)) ∈ K.obj (Opposite.op Y) := by
      change φ₂.hom.app (Opposite.op Y) v ∈ U₂.obj (Opposite.op Y)
      rw [← hav]
      exact a.2
    rw [hKeq] at hvK
    exact mem_of_bot_mem_topology hU₂.1 hT₀c.1 a (bot_mem_topology_of_mem_sheafify_bot hvK)
  set Z' := squareGlue B S hS U₂ φ₂.hom T₀ ZB.1 with hZ'def
  have hZ'c : IsClosedSubspace B S hS Z' := isClosedSubspace_squareGlue Y₂.2 hsq hT₀c ZB.2 hcompat
  have hZ'fp : IsFinitePresentation B S hS Z'.ι :=
    isFinitePresentation_squareGlue Y₂.2 hsq hT₀c ZB.2 hcompat hT₀fp hZBfp
  have hZ'V : Z'.preimage φ₂.hom = ZB.1 := preimage_squareGlue Y₂.2 hsq ZB.2 hcompat
  have hZ'U : Z'.preimage U₂.ι = T₀ := preimage_ι_squareGlue Y₂.2 hsq ZB.2 hcompat
  have hZ'disj : Disjoint (subspacePointSet B S hS Y₂.1 N) (subspacePointSet B S hS Y₂.1 Z') := by
    refine Set.disjoint_left.2 ?_
    rintro y hyN ⟨z, rfl⟩
    rcases points_covered_by_open_or_etale B S hS Y₂.2 U₂ φ₂.hom hsq
        (pointsMap B S hS _ Z'.ι z) with ⟨t, ht⟩ | ⟨v, hv⟩
    · have : t ∈ Set.range
          (pointsMap B S hS (Z'.preimage U₂.ι).toFunctor (Z'.preimage U₂.ι).ι) := by
        rw [range_pointsMap_preimage_ι, Set.mem_preimage, ht]; exact ⟨z, rfl⟩
      rwa [hZ'U, range_pointsMap_ι_sheafify_bot] at this
    · have hvZ : v ∈ subspacePointSet B S hS V₂.1 ZB.1 := by
        change v ∈ Set.range (pointsMap B S hS ZB.1.toFunctor ZB.1.ι)
        rw [← hZ'V, range_pointsMap_preimage_ι, Set.mem_preimage, hv]; exact ⟨z, rfl⟩
      have hvN : v ∈ subspacePointSet B S hS V₂.1 ΩV := by
        change v ∈ Set.range (pointsMap B S hS (N.preimage φ₂.hom).toFunctor _)
        rw [range_pointsMap_preimage_ι, Set.mem_preimage, hv]; exact hyN
      exact Set.disjoint_left.1 hZBdisj hvN hvZ
  obtain ⟨Y₃, b₂, hb₂⟩ := exists_isBlowupAlong_of_isFinitePresentation (⟨Z', hZ'c⟩ :
    ClosedSubspaces B S hS Y₂.1) hZ'fp
  refine ⟨Y₃, b₂, ⟨Z', hZ'c⟩, hZ'fp, hZ'disj, hb₂, ?_⟩
  have hsq₃ := isElementaryDistinguishedSquare_preimage B S hS Y₂.2 Y₃.2 U₂ φ₂.hom hsq b₂.hom
  have hcov := isFppfCovering_elementaryDistinguishedSquare B S hS Y₃.2 _ _ hsq₃
  refine isFlat_and_isLocallyOfFinitePresentation_of_boolCovering _ _ _ hcov ?_
  rintro (_ | _)
  · have hfoU := hfo.mono hN hU₂ hUN
    have hFO := flatOver_strictTransformSpaceToBlowUp_preimage_of_flatOver g₂ hb₂ hU₂ hfoU
    have hP := (strictTransformSpace B S hS g₂ b₂ (Z'.preimage b₂.hom)).2
    have hU₃ := isOpenSubspace_preimage B S hS b₂.hom U₂ Y₂.2 Y₃.2 hU₂
    exact ⟨_, (isOpenSubspace_preimage B S hS _ (U₂.preimage b₂.hom) Y₃.2 hP hU₃).1, _, _,
      (Subfunctor.isPullback_preimage _ (U₂.preimage b₂.hom)).flip, hFO⟩
  · let V₃' : AlgebraicSpaces B S hS :=
      ⟨pullback φ₂.hom b₂.hom, isAlgebraicSpace_pullback B S hS φ₂.hom b₂.hom V₂.2 Y₃.2 Y₂.2⟩
    let v' : V₃' ⟶ V₂ := ObjectProperty.homMk (pullback.fst φ₂.hom b₂.hom)
    let m : V₃' ⟶ Y₃ := ObjectProperty.homMk (pullback.snd φ₂.hom b₂.hom)
    have hsqm : IsPullback v' m φ₂ b₂ :=
      isPullback_of_isPullback_hom (IsPullback.of_hasPullback φ₂.hom b₂.hom)
    have hv' := isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS hφ₂)
      hb₂ hsqm
    have hpre : preimageClosedSubspace φ₂ (⟨Z', hZ'c⟩ : ClosedSubspaces B S hS Y₂.1) = ZB :=
      Subtype.ext hZ'V
    have hu : IsEtale B S hS uV.hom :=
      isEtale_of_isPullback B S hS fV uV φ₂ g₂ (isPullback_of_isPullback_hom hsqV.flip) hφ₂
    have hex := exists_isPullback_strictTransformSpaceToBlowUp_of_isEtale hb₂ g₂ hφ₂ hu hsqV hv' m
      hsqm.w.symm
    rw [hpre] at hv' hex
    obtain ⟨a, -, hsqa⟩ := hex
    exact ⟨_, (strictTransformSpace B S hS fV v' _).2, a, _, hsqa,
      isFlat_strictTransformSpaceToBlowUp_of_isBlowupAlong hbV hv' fV hstV⟩

/-! ### Composite blowups, and the induction -/

/-- **The strict transform under a composite of two blowups** (Stacks 0868): if the strict
transform of the strict transform is flat and locally of finite presentation over the second
blowup, so is the strict transform along the composite, for the composite centre of
Stacks 0860. -/
theorem isFlat_strictTransformSpaceToBlowUp_comp {A A' A'' X : AlgebraicSpaces B S hS}
    (f : X ⟶ A) {b : A' ⟶ A} {c : A'' ⟶ A'} {Z : ClosedSubspaces B S hS A.1}
    {Z' : ClosedSubspaces B S hS A'.1} {Y : ClosedSubspaces B S hS A.1}
    (hb : IsBlowupAlong B S hS Z b) (hc : IsBlowupAlong B S hS Z' c)
    (hY : IsCompositeCentre B S hS b Z Z' Y) (hd : IsBlowupAlong B S hS Y (c ≫ b))
    (h : IsFlat B S hS (strictTransformSpaceToBlowUp B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c
          (Z'.1.preimage c.hom)).hom) :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)).hom := by
  obtain ⟨j, hj⟩ := exists_iteratedStrictTransformSpace_iso B S hS f b c Z Z' Y hb hc hY hd
  have he : j.inv ≫ strictTransformSpaceToBlowUp B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c (Z'.1.preimage c.hom) =
      strictTransformSpaceToBlowUp B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) := by
    rw [Iso.inv_comp_eq]
    change _ = j.hom ≫ (strictTransformSpaceι B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom) ≫
      strictTransformPullbackToBlowUp B S hS f (c ≫ b))
    rw [← Category.assoc, hj, Category.assoc, iteratedStrictTransformSpaceMap_toBlowUp]
  rw [← he]
  have hP := (strictTransformSpace B S hS f (c ≫ b) (Y.1.preimage (c ≫ b).hom)).2
  have hP' := (strictTransformSpace B S hS
    (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) c (Z'.1.preimage c.hom)).2
  have hι := isEtale_of_isIso B S hS j.inv.hom
  exact isFlat_and_isLocallyOfFinitePresentation_comp_of_isEtale hP hP' A''.2 hι h

/-- **Flattening over the members of a square**: a quasi-compact and quasi-separated algebraic
space `Y` with an elementary distinguished square `(U ⊆ Y, φ : V ⟶ Y)`, `U` quasi-compact and
`V` affine, flattens over its blowups as soon as `U` and `V` do. -/
theorem flattensOverBlowups_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y V : AlgebraicSpaces B S hS} (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (U : Subfunctor Y.1) (φ : V ⟶ Y)
    (hsq : IsElementaryDistinguishedSquare B S hS Y.2 U φ.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hVaff : IsAffineSpace B S hS V.1)
    (hQU : FlattensOverBlowups (⟨U.toFunctor, hsq.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS))
    (hQV : FlattensOverBlowups V) : FlattensOverBlowups Y := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  intro Y₁ c Zc hZcfp hc Ω hΩqc X f hft hqs hfo
  have hU : IsOpenSubspace B S hS U := hsq.isOpenSubspace
  obtain ⟨hY₁qc, hY₁qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hYqc hYqs hZcfp hc
  obtain ⟨Y₂, b₁, Z₁, hZ₁fp, hZ₁disj, hb₁, hFOU, hFOΩ⟩ :=
    exists_isBlowupAlong_flatOver_of_flattensOverBlowups_open hZ hYqc hYqs U hU hUqc hQU hZcfp
      hc Ω.1 Ω.2 hΩqc f hft hqs hfo
  obtain ⟨hY₂qc, hY₂qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hY₁qc hY₁qs hZ₁fp hb₁
  set g₂ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₁.1.preimage b₁.hom) with hg₂
  obtain ⟨hft₂, hqs₂⟩ := isFiniteType_and_isQuasiSeparated_strictTransformSpaceToBlowUp f b₁
    (Z₁.1.preimage b₁.hom) hft hqs
  obtain ⟨Zc₂, hZc₂fp, -, hbc⟩ :=
    exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace hZ hYqc hYqs hc hZcfp hb₁ hZ₁fp
  set U₂ := (U.preimage c.hom).preimage b₁.hom with hU₂def
  have hU₂eq : U.preimage (b₁ ≫ c).hom = U₂ := Subfunctor.preimage_comp U b₁.hom c.hom
  have hsq₂ := isElementaryDistinguishedSquare_preimage B S hS Y.2 Y₂.2 U φ.hom hsq (b₁ ≫ c).hom
  rw [hU₂eq] at hsq₂
  let V₂ : AlgebraicSpaces B S hS :=
    ⟨pullback φ.hom (b₁ ≫ c).hom, isAlgebraicSpace_pullback B S hS φ.hom (b₁ ≫ c).hom V.2 Y₂.2 Y.2⟩
  let φ₂ : V₂ ⟶ Y₂ := ObjectProperty.homMk (pullback.snd φ.hom (b₁ ≫ c).hom)
  let cV : V₂ ⟶ V := ObjectProperty.homMk (pullback.fst φ.hom (b₁ ≫ c).hom)
  have hsqV : IsPullback cV φ₂ φ (b₁ ≫ c) :=
    isPullback_of_isPullback_hom (IsPullback.of_hasPullback φ.hom (b₁ ≫ c).hom)
  have hcV : IsBlowupAlong B S hS (preimageClosedSubspace φ Zc₂) cV :=
    isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS hsq.isEtale) hbc hsqV
  have hZcVfp := isFinitePresentation_preimageClosedSubspace φ Zc₂ hZc₂fp
  have hV₂qc : IsQuasiCompactSpace B S hS V₂.1 :=
    (isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ
      hVaff.isQuasiCompactSpace (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVaff)
      hZcVfp hcV).1
  have hΩ₂ : IsOpenSubspace B S hS (Ω.1.preimage b₁.hom) :=
    isOpenSubspace_preimage B S hS b₁.hom Ω.1 Y₁.2 Y₂.2 Ω.2
  have hΩ₂qc : IsQuasiCompactSpace B S hS (Ω.1.preimage b₁.hom).toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y₁.2 hY₁qs Y₂.2 hY₂qc Ω.1 hΩqc b₁.hom
  have hU₂ : IsOpenSubspace B S hS U₂ := hsq₂.isOpenSubspace
  have hU₂qc : IsQuasiCompactSpace B S hS U₂.toFunctor := by
    rw [← hU₂eq]
    exact isQuasiCompactSpace_preimage_toFunctor B S hS hZ Y.2 hYqs Y₂.2 hY₂qc U hUqc _
  obtain ⟨N, hN, hle₁, hle₂, hNpts⟩ := exists_openSubspace_range_eq_union B S hS Y₂.2 hΩ₂ hU₂
  have hNqc : IsQuasiCompactSpace B S hS N.toFunctor := by
    refine isQuasiCompactSpace_of_isCompact_range B S hS Y₂.2 hN ?_
    rw [hNpts]
    exact (isCompact_range_of_isQuasiCompactSpace B S hS hΩ₂ hΩ₂qc).union
      (isCompact_range_of_isQuasiCompactSpace B S hS hU₂ hU₂qc)
  have hFON : FlatOver g₂ N := FlatOver.of_cover hN hΩ₂ hU₂ hle₁ hle₂ hNpts.le hFOΩ hFOU
  obtain ⟨Y₃, b₂, Z', hZ'fp, hZ'disj, hb₂, hfl⟩ :=
    exists_isBlowupAlong_isFlat_of_isElementaryDistinguishedSquare hZ hY₂qs U₂ φ₂ hsq₂ hV₂qc
      (fun Ω' hΩ'qc X' f' hft' hqs' hfo' =>
        hQV cV (preimageClosedSubspace φ Zc₂) hZcVfp hcV Ω' hΩ'qc f' hft' hqs' hfo')
      N hN hNqc hle₂ g₂ hft₂ hqs₂ hFON
  obtain ⟨Y'', hY''fp, hY'', hbb⟩ :=
    exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace hZ hY₁qc hY₁qs hb₁ hZ₁fp hb₂ hZ'fp
  refine ⟨Y₃, b₂ ≫ b₁, Y'', hY''fp, ?_, hbb,
    isFlat_strictTransformSpaceToBlowUp_comp f hb₁ hb₂ hY'' hbb hfl⟩
  refine Set.disjoint_left.2 fun x hxΩ hxY => ?_
  change x ∈ Set.range (pointsMap B S hS Y''.1.toFunctor Y''.1.ι) at hxY
  rw [hY''] at hxY
  rcases hxY with hx | ⟨z, hz, rfl⟩
  · exact Set.disjoint_left.1 hZ₁disj hxΩ hx
  · have hzΩ : z ∈ subspacePointSet B S hS Y₂.1 (Ω.1.preimage b₁.hom) := by
      change z ∈ Set.range (pointsMap B S hS _ (Ω.1.preimage b₁.hom).ι)
      rwa [range_pointsMap_preimage_ι]
    have hzN : z ∈ subspacePointSet B S hS Y₂.1 N := by
      change z ∈ Set.range (pointsMap B S hS N.toFunctor N.ι)
      rw [hNpts]
      exact Or.inl hzΩ
    exact Set.disjoint_left.1 hZ'disj hzN hz

/-- **Every quasi-compact and quasi-separated algebraic space flattens over its blowups**, as
soon as the affine ones do. -/
theorem flattensOverBlowups_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (hbase : ∀ V : AlgebraicSpaces B S hS, IsAffineSpace B S hS V.1 → FlattensOverBlowups V)
    (Y : AlgebraicSpaces B S hS) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) : FlattensOverBlowups Y := by
  exact qcqs_induction_on_self B S hS hZ Y hYqc hYqs
    (fun W _ => ∀ hW : IsAlgebraicSpace B S hS W,
      FlattensOverBlowups (⟨W, hW⟩ : AlgebraicSpaces B S hS))
    (fun V hV hW => hbase ⟨_, hW⟩ hV)
    (fun W V U f _ hsq hWqc hWqs hUqc hVaff hPU hPV _ hW =>
      flattensOverBlowups_of_isElementaryDistinguishedSquare hZ (Y := ⟨W.1.left.1, hW⟩)
        (V := ⟨V.1.left.1, hsq.isAlgebraicSpace⟩) hWqc hWqs U (ObjectProperty.homMk f) hsq hUqc
        hVaff (hPU hsq.isOpenSubspace.1) (hPV hsq.isAlgebraicSpace)) Y.2

end AlgebraicGeometry.Space

end
