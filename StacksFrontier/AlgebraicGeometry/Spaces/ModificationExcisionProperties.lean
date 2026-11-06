module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Excision preserves the standard properties of a modification

Let `f : V ⟶ W` be an étale morphism of algebraic spaces over a scheme `S` and let `T ⊆ W` be
a closed subspace whose preimage is carried isomorphically onto `T` by `f`. Writing `W⁰` for
the open complement of `T`, the base change along `f` of Stacks 0BGY carries a modification
`g : X ⟶ W` of `W` outside `W⁰` to a modification `h : Y ⟶ V` of `V` outside `f⁻¹W⁰`. This
file proves **Stacks 0BGZ**: `g` has each of ten standard properties exactly when `h` does.

## Main results

One theorem per property, each an "if and only if":

* `AlgebraicGeometry.Space.isQuasiCompact_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isSeparated_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isFinitePresentation_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isFiniteType_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isProper_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isIntegralHom_iff_baseChangeFunctor_obj`,
* `AlgebraicGeometry.Space.isFinite_iff_baseChangeFunctor_obj`.

## Implementation notes

Lemma 0BGY also assumes that `f` is separated. That hypothesis is what makes the base-change
functor an equivalence; the comparison of properties does not use it, so it is absent here and
the statements are correspondingly stronger.

## References

* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BGZ](https://stacks.math.columbia.edu/tag/0BGZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transporting a property between base changes -/

/-- Stability of a property of morphisms of presheaves under base change along a Cartesian
square all of whose corners are algebraic spaces over `S`. -/
def StableUnderAlgebraicBaseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) : Prop :=
  ∀ {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : F ⟶ G} {p : G' ⟶ G}
    {m : F' ⟶ F} {k' : F' ⟶ G'}, IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
      IsAlgebraicSpace B S hS F' → IsAlgebraicSpace B S hS G' →
      IsPullback m k' k p → P k → P k'

variable {B S hS}

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ModificationExcisionProperties :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ModificationExcisionProperties
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_ModificationExcisionProperties.has_limit _

/-- A base-change stable property is unchanged by precomposition with an isomorphism. -/
theorem prop_comp_iso {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P)
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hF' : IsAlgebraicSpace B S hS F') (hG : IsAlgebraicSpace B S hS G)
    (e : F ≅ F') (k : F' ⟶ G) (hk : P k) : P (e.hom ≫ k) := by
  have sq : IsPullback e.hom (e.hom ≫ k) k (𝟙 G) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hbc hF' hG hF hG sq hk

/-- A base-change stable property holds for one base change of a morphism exactly when it holds
for any other base change of it along the same morphism. -/
theorem prop_of_isPullback_of_isPullback
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P)
    {F G G' Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : F ⟶ G} {p : G' ⟶ G}
    {w : Z ⟶ F} {z : Z ⟶ G'} {w' : Z' ⟶ F} {z' : Z' ⟶ G'}
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    (hG' : IsAlgebraicSpace B S hS G')
    (sq : IsPullback w z k p) (sq' : IsPullback w' z' k p) (h : P z) : P z' := by
  rw [← sq'.isoIsPullback_hom_snd _ _ sq]
  exact prop_comp_iso hbc hZ' hZ hG' _ z h

/-- The second projection and the first projection of the two orders of the chosen fibre
product carry a base-change stable property to each other. -/
theorem prop_pullback_fst_of_snd
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P)
    {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G) (p : G' ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hG' : IsAlgebraicSpace B S hS G') (h : P (pullback.snd k p)) :
    P (pullback.fst p k) :=
  prop_of_isPullback_of_isPullback hbc
    (isAlgebraicSpace_pullback B S hS k p hF hG' hG)
    (isAlgebraicSpace_pullback B S hS p k hG' hF hG) hG'
    (IsPullback.of_hasPullback k p) (IsPullback.of_hasPullback p k).flip h

variable (B S hS)

/-- A property of morphisms of presheaves whose restriction to algebraic spaces is stable under
base change is stable under base change along Cartesian squares of algebraic spaces. -/
private theorem stableUnderAlgebraicBaseChange_of_isStableUnderBaseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (φ : X ⟶ Y) => P φ.hom)) :
    StableUnderAlgebraicBaseChange B S hS P :=
  fun hF hG hF' hG' sq hk => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (φ : X ⟶ Y) => P φ.hom)
    (isPullback_homMk B S hS hF hG' hG hF' sq) hk

/-! ### The common argument -/

variable {V W : AlgebraicSpaces B S hS}

/-- **Stacks 0BGZ, for an arbitrary property.** Let `f : V ⟶ W` be étale, let
`T` be a closed subspace of `W` whose preimage is carried isomorphically onto `T`, and let `g`
be a modification of `W` outside the open complement of `T`. A property of morphisms of
presheaves which is stable under base change, holds for isomorphisms, can be checked on a
surjective étale scheme chart of the target and is Zariski local on the target holds for `g`
exactly when it holds for the image of `g` under the base-change functor of Stacks 0BGY. -/
private theorem prop_iff_prop_baseChangeFunctor_obj
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P)
    (hiso : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsIso k → P k)
    (hchart : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
      ∀ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ G), IsSurjective B S hS q →
        IsEtale B S hS q → P (pullback.snd k q) → P k)
    (hzar : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
      ∀ (J : Type u) (Uj : J → Subfunctor G), IsZariskiCover B S hS J Uj →
        (∀ j, P (pullback.snd k (Uj j).ι)) → P k)
    (f : V ⟶ W) (T : Subfunctor W.obj) (hT : IsClosedSubspace B S hS T)
    (hfT : IsIso (T.fromPreimage f.hom)) (hf : IsEtale B S hS f.hom)
    (g : Modification B S hS (openComplement B S hS T)) :
    P g.obj.hom ↔ P ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  refine ⟨fun hg => hbc g.property.1 W.property
    ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).property.1 V.property
    (isPullback_baseChangeFunctor_obj B S hS f _ g) hg, fun hh => ?_⟩
  obtain ⟨I, hI, U, a, q, hq, hqs, hqe, hcover⟩ :=
    exists_openImage_isZariskiCover_openComplement B S hS f T hT hfT hf
  have hW₀ : IsOpenSubspace B S hS (openComplement B S hS T) :=
    isOpenSubspace_openComplement B S hS W.property T hT
  have hX : IsAlgebraicSpace B S hS g.obj.left := g.property.1
  have hoverW₀ : P (pullback.snd g.obj.hom (openComplement B S hS T).ι) :=
    hiso _ (isAlgebraicSpace_pullback B S hS g.obj.hom (openComplement B S hS T).ι hX
      hW₀.1 W.property) hW₀.1 g.property.2
  have hoverI : P (pullback.snd g.obj.hom I.ι) := by
    refine hchart _ (isAlgebraicSpace_pullback B S hS g.obj.hom I.ι hX hI.1 W.property)
      hI.1 U q hqs hqe ?_
    have hbig : IsPullback
        (pullback.fst (pullback.snd g.obj.hom I.ι) q ≫ pullback.fst g.obj.hom I.ι)
        (pullback.snd (pullback.snd g.obj.hom I.ι) q) g.obj.hom (q ≫ I.ι) :=
      (IsPullback.of_hasPullback (pullback.snd g.obj.hom I.ι) q).paste_horiz
        (IsPullback.of_hasPullback g.obj.hom I.ι)
    rw [hq] at hbig
    refine hbc ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).property.1
      V.property ?_ (isAlgebraicSpace_yoneda B S hS U)
      (hbig.of_right' (isPullback_baseChangeFunctor_obj B S hS f _ g)) hh
    exact isAlgebraicSpace_pullback B S hS (pullback.snd g.obj.hom I.ι) q
      (isAlgebraicSpace_pullback B S hS g.obj.hom I.ι hX hI.1 W.property)
      (isAlgebraicSpace_yoneda B S hS U) hI.1
  refine hzar _ hX W.property (ULift.{u} Bool) _ hcover ?_
  rintro ⟨b⟩
  cases b
  · simpa using hoverI
  · simpa using hoverW₀

/-! ### The ten properties of Stacks 0BGZ -/

variable (f : V ⟶ W) (T : Subfunctor W.obj) (hT : IsClosedSubspace B S hS T)
  (hfT : IsIso (T.fromPreimage f.hom)) (hf : IsEtale B S hS f.hom)
  (g : Modification B S hS (openComplement B S hS T))

include hT hfT hf

/-- A modification of `W` outside the complement of `T` is
quasi-compact exactly when its base change to `V` is. -/
@[stacks 0BGZ "quasi-compactness"]
theorem isQuasiCompact_iff_baseChangeFunctor_obj :
    IsQuasiCompact B S hS g.obj.hom ↔
      IsQuasiCompact B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsQuasiCompact B S hS k) :=
    fun _ _ _ _ sq hk => IsQuasiCompact.of_isPullback B S hS sq hk
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ _ hk
    have := hk
    exact isQuasiCompact_of_isClosedImmersion' B S hS (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isQuasiCompact_tfae B S hS hF hG k).out 4 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isQuasiCompact_tfae B S hS hF hG k).out 6 1).mp (by
      exact ⟨J, Uj, hU,
        fun j => prop_pullback_fst_of_snd hbc k (Uj j).ι hF hG (hU.1 j).1 (h j)⟩)

/-- A modification of `W` outside the complement of `T`
is quasi-separated exactly when its base change to `V` is. -/
@[stacks 0BGZ "quasi-separatedness"]
theorem isQuasiSeparated_iff_baseChangeFunctor_obj :
    IsQuasiSeparated B S hS g.obj.hom ↔
      IsQuasiSeparated B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsQuasiSeparated B S hS k) :=
    fun _ _ _ _ sq hk => (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := quasiCompactPresheafProperty B S hS)).of_isPullback sq hk
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ _ hk
    have := hk
    have : IsIso (pullback.diagonal k) := (pullback.isIso_diagonal_iff k).2 (IsIso.mono_of_iso k)
    exact isQuasiCompact_of_isClosedImmersion' B S hS
      (isClosedImmersion_of_isIso B S hS (pullback.diagonal k))
  · intro F G k hF hG U q hqs hqe h
    exact isQuasiSeparated_of_etaleChart B S hS hF
      ((presheafSurjective_iff_isSurjective_yoneda B S hS G hG U q).mpr hqs)
      (presheaf_etale_of_isEtale B S hS hqe) h
  · intro F G k hF _ J Uj hU h
    exact isQuasiSeparated_of_zariskiCover B S hS hF hU h

/-- A modification of `W` outside the complement of `T` is
separated exactly when its base change to `V` is. -/
@[stacks 0BGZ "separatedness"]
theorem isSeparated_iff_baseChangeFunctor_obj :
    IsSeparated B S hS g.obj.hom ↔
      IsSeparated B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have _hci : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsSeparated B S hS k) :=
    fun _ _ _ _ sq hk => (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))).of_isPullback sq hk
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ _ hk
    have := hk
    exact isSeparated_of_isIso B S hS k
  · intro F G k hF hG U q hqs hqe h
    exact isSeparated_of_etaleChart B S hS hF
      ((presheafSurjective_iff_isSurjective_yoneda B S hS G hG U q).mpr hqs)
      (presheaf_etale_of_isEtale B S hS hqe) h
  · intro F G k hF _ J Uj hU h
    exact isSeparated_of_zariskiCover B S hS hF hU h

/-- A modification of `W` outside the complement of
`T` is locally of finite presentation exactly when its base change to `V` is. -/
@[stacks 0BGZ "local finite presentation"]
theorem isLocallyOfFinitePresentation_iff_baseChangeFunctor_obj :
    IsLocallyOfFinitePresentation B S hS g.obj.hom ↔
      IsLocallyOfFinitePresentation B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have _hsb := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hbc : StableUnderAlgebraicBaseChange B S hS
      (fun _ _ k => IsLocallyOfFinitePresentation B S hS k) :=
    stableUnderAlgebraicBaseChange_of_isStableUnderBaseChange B S hS _ inferInstance
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ hG hk
    have := hk
    exact isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isLocallyOfFinitePresentation_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    have hPB : ∀ j, IsAlgebraicSpace B S hS (pullback k (Uj j).ι) := fun j =>
      isAlgebraicSpace_pullback B S hS k (Uj j).ι hF (hU.1 j).1 hG
    refine ((isLocallyOfFinitePresentation_tfae B S hS hF hG k).out 9 1).mp (by
      refine ⟨J, Uj, fun _ => PUnit.{u + 1}, fun _ _ => ⊤, hU,
        fun j => isZariskiCover_top (hPB j), fun j _ => ?_⟩
      exact isLocallyOfFinitePresentation_comp B S hS (isOpenSubspace_top (hPB j)).1 (hPB j)
        (hU.1 j).1 _ _
        (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS _))
        (h j))

/-- A modification of `W` outside the complement of `T` is
locally of finite type exactly when its base change to `V` is. -/
@[stacks 0BGZ "local finite type"]
theorem isLocallyOfFiniteType_iff_baseChangeFunctor_obj :
    IsLocallyOfFiniteType B S hS g.obj.hom ↔
      IsLocallyOfFiniteType B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have _hsb := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsLocallyOfFiniteType B S hS k) :=
    stableUnderAlgebraicBaseChange_of_isStableUnderBaseChange B S hS _ inferInstance
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ hG hk
    have := hk
    exact isLocallyOfFiniteType_of_isEtale B S hS hG (isEtale_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isLocallyOfFiniteType_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isLocallyOfFiniteType_tfae B S hS hF hG k).out 9 1).mp (by
      refine ⟨J, Uj, hU, fun j => ?_⟩
      have hsq := Subfunctor.isPullback_preimage k (Uj j)
      have hP : IsAlgebraicSpace B S hS ((Uj j).preimage k).toFunctor :=
        (isAlgebraicSpace_pullback B S hS (Uj j).ι k (hU.1 j).1 hF hG).of_iso
          hsq.isoPullback.symm
      refine ⟨PUnit.{u + 1}, fun _ => ⊤, isZariskiCover_top hP, fun _ => ?_⟩
      refine isLocallyOfFiniteType_comp B S hS (isOpenSubspace_top hP).1 hP (hU.1 j).1 _ _
        (isLocallyOfFiniteType_of_isEtale B S hS hP (isEtale_of_isIso B S hS _)) ?_
      exact prop_of_isPullback_of_isPullback hbc
        (isAlgebraicSpace_pullback B S hS k (Uj j).ι hF (hU.1 j).1 hG) hP (hU.1 j).1
        (IsPullback.of_hasPullback k (Uj j).ι) hsq.flip (h j))

/-- A modification of `W` outside the complement of `T` is of
finite type exactly when its base change to `V` is. -/
@[stacks 0BGZ "finite type"]
theorem isFiniteType_iff_baseChangeFunctor_obj :
    IsFiniteType B S hS g.obj.hom ↔
      IsFiniteType B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hlft := isLocallyOfFiniteType_iff_baseChangeFunctor_obj B S hS f T hT hfT hf g
  have hqc := isQuasiCompact_iff_baseChangeFunctor_obj B S hS f T hT hfT hf g
  exact ⟨fun hg => ⟨hlft.mp hg.1, hqc.mp hg.2⟩, fun hh => ⟨hlft.mpr hh.1, hqc.mpr hh.2⟩⟩

/-- A modification of `W` outside the complement of `T`
is of finite presentation exactly when its base change to `V` is. -/
@[stacks 0BGZ "finite presentation"]
theorem isFinitePresentation_iff_baseChangeFunctor_obj :
    IsFinitePresentation B S hS g.obj.hom ↔
      IsFinitePresentation B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hlfp := isLocallyOfFinitePresentation_iff_baseChangeFunctor_obj B S hS f T hT hfT hf g
  have hqc := isQuasiCompact_iff_baseChangeFunctor_obj B S hS f T hT hfT hf g
  have hqs := isQuasiSeparated_iff_baseChangeFunctor_obj B S hS f T hT hfT hf g
  exact ⟨fun hg => ⟨hlfp.mp hg.1, hqc.mp hg.2.1, hqs.mp hg.2.2⟩,
    fun hh => ⟨hlfp.mpr hh.1, hqc.mpr hh.2.1, hqs.mpr hh.2.2⟩⟩

/-- A modification of `W` outside the complement of `T` is proper
exactly when its base change to `V` is. -/
@[stacks 0BGZ "properness"]
theorem isProper_iff_baseChangeFunctor_obj :
    IsProper B S hS g.obj.hom ↔
      IsProper B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsProper B S hS k) :=
    stableUnderAlgebraicBaseChange_of_isStableUnderBaseChange B S hS _ inferInstance
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k hF hG hk
    have := hk
    exact isProper_of_isClosedImmersion B S hS hF hG k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isProper_tfae B S hS hF hG k).out 4 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isProper_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨J, Uj, hU,
        fun j => prop_pullback_fst_of_snd hbc k (Uj j).ι hF hG (hU.1 j).1 (h j)⟩)

/-- A modification of `W` outside the complement of `T` is
integral exactly when its base change to `V` is. -/
@[stacks 0BGZ "integrality"]
theorem isIntegralHom_iff_baseChangeFunctor_obj :
    IsIntegralHom B S hS g.obj.hom ↔
      IsIntegralHom B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsIntegralHom B S hS k) :=
    fun _ _ _ _ sq hk => isIntegralHom_of_isPullback B S hS sq hk
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ _ hk
    have := hk
    exact isIntegralHom_of_isClosedImmersion B S hS k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    exact isIntegralHom_of_surjectiveEtaleChart B S hS hF hG k hqs hqe h
  · intro F G k hF hG J Uj hU h
    exact (isIntegralHom_iff_zariskiCover B S hS k hF hG).mpr ⟨J, Uj, hU, h⟩

/-- A modification of `W` outside the complement of `T` is finite
exactly when its base change to `V` is. -/
@[stacks 0BGZ "finiteness"]
theorem isFinite_iff_baseChangeFunctor_obj :
    IsFinite B S hS g.obj.hom ↔
      IsFinite B S hS
        ((baseChangeFunctor B S hS f (openComplement B S hS T)).1.obj g).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsFinite B S hS k) :=
    fun _ _ _ _ sq hk => isFinite_of_isPullback B S hS sq hk
  refine prop_iff_prop_baseChangeFunctor_obj B S hS hbc ?_ ?_ ?_ f T hT hfT hf g
  · intro F G k _ _ hk
    have := hk
    exact isFinite_of_isClosedImmersion B S hS k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    exact isFinite_of_surjectiveEtaleChart B S hS hF hG k hqs hqe h
  · intro F G k hF hG J Uj hU h
    exact (isFinite_iff_zariskiCover B S hS k hF hG).mpr ⟨J, Uj, hU, h⟩

end AlgebraicGeometry.Space

end
