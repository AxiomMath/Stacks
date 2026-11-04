module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformCartierCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections

/-!
# The strict transform is the blowup of the inverse-image centre

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed subspace,
let `b : A' ⟶ A` be the blowup of `A` in `Z` and let `f : X ⟶ A` be an algebraic space over `A`.
Stacks 0864, clause (1) asserts that the strict transform `X'` of `X` — the closed subspace of
`X ×_A A'` of Stacks 0862, clause (2) — **is** the blowup of `X` in the inverse image `f⁻¹Z`.

This file proves it, with no hypothesis beyond `b` being the blowup of `A` in `Z`.

## Main results

* `AlgebraicGeometry.Space.supportedSectionsSubmodule_unit_le_kernelIdealSheaf_of_isEtale`: for
  an étale morphism `g : Y ⟶ X` no point of whose source lies over a set `T` of points of `X`,
  the ideal of sections of `𝒪_X` supported on `T` lies in the kernel ideal sheaf of `g`.
* `AlgebraicGeometry.Space.supportedSectionsSubmodule_unit_le_kernelIdealSheaf`: **for an
  arbitrary `g : Y ⟶ X` whose source has no nonzero local section of its structure sheaf
  supported over `T`, the ideal of sections of `𝒪_X` supported on `T` lies in the kernel ideal
  sheaf of `g`.**  This is the ideal-sheaf form of "a section supported on `T` pulls back to
  zero".
* `AlgebraicGeometry.Space.exists_comp_eq_strictTransformSpaceι`: **a morphism to `X ×_A A'`
  along which the exceptional preimage pulls back to an effective Cartier divisor factors
  through the strict transform**, for `b` a blowup.
* `AlgebraicGeometry.Space.isBlowupAlong_strictTransform`: **Stacks 0864, clause (1).**  The
  strict transform `X'`, with its morphism `X' ⟶ X ×_A A' ⟶ X`, is the blowup of `X` in `f⁻¹Z`.
* `AlgebraicGeometry.Space.exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison`
  and `AlgebraicGeometry.Space.isClosedImmersion_strictTransformBlowUpComparison`: the reading of
  clause (1) that the source's proof gives — for a blowup `b'' : X'' ⟶ X` of `X` in `f⁻¹Z` the
  canonical comparison `i : X'' ⟶ X ×_A A'` of
  `AlgebraicGeometry.Space.strictTransformBlowUpComparison` is an isomorphism `X'' ≅ X'` followed
  by the closed immersion of the strict transform, and is therefore itself a closed immersion;
  and `AlgebraicGeometry.Space.range_strictTransformBlowUpComparison`, that its image is the
  strict transform.

## Implementation notes

The two halves of the universal property of Stacks 085U are proved separately and neither
mentions a second blowup.

*Membership in the category `𝒞`* — that `f⁻¹Z` pulls back to an effective Cartier divisor on
`X'` — is `AlgebraicGeometry.Space.isPullbackDefined_strictTransform_of_isBlowupAlong`, already
available.

*Finality in `𝒞`* is proved here.  Uniqueness is the fibre product read backwards, exactly as in
`AlgebraicGeometry.Space.existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong`: a
morphism `Y ⟶ X'` over `X` is determined by its composite with the closed immersion
`X' ⟶ X ×_A A'`, which is in turn determined by its two projections, and the projection to `A'`
is the classifying morphism of `b`, unique by the universal property of `b`.  Existence is the
content: an object `y : Y ⟶ X` of `𝒞` gives a morphism `g : Y ⟶ X ×_A A'` with components `y`
and the classifying morphism, and `g` has to be *factored through the closed subspace `X'`*.

That factorization is Stacks 03MB in the form
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le`, so what has to
be seen is that the defining ideal of `X'` lies in the kernel ideal sheaf of `g`.  The defining
ideal of `X'` is the ideal of sections of `𝒪_{X ×_A A'}` supported on the exceptional preimage,
by `AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`; and the
inverse image of the exceptional preimage along `g` is the inverse image of `f⁻¹Z` along `y`
(`AlgebraicGeometry.Space.preimage_exceptionalPreimage_eq_preimage_centre`), an effective
Cartier divisor on `Y` because `Y` is an object of `𝒞`.  So `𝒪_Y` has no nonzero local section
supported over the exceptional preimage, by Stacks 083S in the form
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor`,
and `AlgebraicGeometry.Space.supportedSectionsSubmodule_unit_le_kernelIdealSheaf` turns that
into the required inclusion of ideal sheaves.

**Why the inclusion of ideal sheaves needs the open complement.**  The kernel ideal sheaf of `g`
over a chart `V` of `X ×_A A'` is cut out by vanishing of the pullbacks of a function along the
chart diagrams of `g` (`AlgebraicGeometry.Space.mem_ker_structureSharp_iff`), and the vertical
morphism of a chart diagram is *not* étale, so a supported section cannot be restricted along
it inside the small étale site of `X ×_A A'`.  The argument therefore goes the other way round:
the pullback of the section to a chart `W` of `Y` is shown to be supported over the exceptional
preimage by checking it on the subcharts of `W` lying outside it, and each such check is a
pullback along a morphism which lifts to the *open complement* of the exceptional preimage —
where `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift` applies to the inclusion of that
complement, whose kernel ideal sheaf contains the supported sections by
`AlgebraicGeometry.Space.supportedSectionsSubmodule_unit_le_kernelIdealSheaf_of_isEtale`.  That
inclusion is where étaleness is used: a chart of an étale `Y` over `X` is a chart of `X`, so the
supported section really can be restricted there.

## References

* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology SheafOfModules.Submodule.instCompleteLattice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Supported sections and kernel ideal sheaves -/

/-- **Sections supported on `T` are killed by an étale morphism missing `T`.**  Let `T` be a set
of points of an algebraic space `X` and let `g : Y ⟶ X` be an étale morphism no point of whose
source lies over `T`.  Then every section of `𝒪_X` supported on `T` lies in the kernel ideal
sheaf of `g`.

A chart of `Y` becomes a chart of `X` by postcomposition with `g`
(`AlgebraicGeometry.Space.smallEtalePostcomp`, Stacks 03LP), and the vertical morphism of a
chart diagram of `g` becomes a morphism of charts of `X` whose source lies over the complement
of `T`; so a section supported on `T` restricts to zero along it. -/
theorem supportedSectionsSubmodule_unit_le_kernelIdealSheaf_of_isEtale
    (X Y : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hmiss : ∀ v : points B S hS Y.1, pointsMap B S hS Y.1 g.hom v ∉ T)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    (supportedSectionsSubmodule B S hS X.1 X.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS X))).toSubmodule.obj V ≤
      (kernelIdealSheaf B S hS g).obj V := by
  intro s hs
  refine (mem_ker_structureSharp_iff B S hS g V.unop s).2 fun j => ?_
  set W : SmallEtale B S hS Y.1 := j.right.unop with hW
  set h := chartBaseChangeMap B S hS g V.unop j with hh
  have hcomm : W.1.hom ≫ g.hom = yoneda.map h ≫ V.unop.1.hom :=
    (chartDiagramOfIndex B S hS g V.unop j).comm
  set W' : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS g hg).obj W with hW'
  set m : W' ⟶ V.unop := ObjectProperty.homMk (CostructuredArrow.homMk h hcomm.symm) with hm
  have himage : ImageInOpen B S hS X.1
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V.unop))
        V.unop.1.hom ⁻¹' Tᶜ) m := by
    intro v
    exact (congrArg (· ∉ T) (pointsMap_apply_comm B S hS hcomm.symm v)).mpr (hmiss _)
  exact restrict_eq_zero_of_sectionSupportedIn_of_imageInOpen B S hS X T
    (SheafOfModules.unit (structureRingSheaf B S hS X)) V.unop s hs W' m himage

/-- **Sections supported on `T` are killed by any morphism whose source has no sections
supported over `T`.**  Let `T` be a closed set of points of an algebraic space `X`, let
`g : Y ⟶ X` be an arbitrary morphism of algebraic spaces over `S`, and suppose that `𝒪_Y` has
no nonzero local section supported on the inverse image of `T`.  Then every section of `𝒪_X`
supported on `T` lies in the kernel ideal sheaf of `g`.

The pullback of such a section to a chart `W` of `Y` is supported on the inverse image of `T`,
by the maximality of the open zero locus
(`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`): a subchart of
`W` lying over the complement of that inverse image maps to the open complement of `T` in `X`,
along which the section is killed by
`AlgebraicGeometry.Space.supportedSectionsSubmodule_unit_le_kernelIdealSheaf_of_isEtale` and
`AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift`.  The hypothesis on `𝒪_Y` then makes
the pullback itself zero. -/
theorem supportedSectionsSubmodule_unit_le_kernelIdealSheaf
    (X Y : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (g : Y ⟶ X) (hTY : IsClosed (pointsMap B S hS Y.1 g.hom ⁻¹' T))
    (hY : HasNoSectionsSupportedIn B S hS Y (pointsMap B S hS Y.1 g.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS Y)))
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    (supportedSectionsSubmodule B S hS X.1 X.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS X))).toSubmodule.obj V ≤
      (kernelIdealSheaf B S hS g).obj V := by
  -- The open complement of `T` in `X`, and the inclusion of supported sections in its kernel.
  set Csub : Subfunctor X.1 := openSubspaceOfPoints B S hS X.1 Tᶜ with hCsub
  have hCopen : IsOpenSubspace B S hS Csub :=
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl
  have hCrange : Set.range (pointsMap B S hS Csub.toFunctor Csub.ι) = Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ
  set C : AlgebraicSpaces B S hS := ⟨Csub.toFunctor, hCopen.1⟩ with hC
  set c : C ⟶ X := ObjectProperty.homMk Csub.ι with hc
  have hcE : IsEtale B S hS c.hom := isEtale_ι_of_isOpenSubspace hCopen
  have hcmiss : ∀ v : points B S hS C.1, pointsMap B S hS C.1 c.hom v ∉ T := by
    intro v hv
    exact (hCrange.le (Set.mem_range_self v)) hv
  have hJc := supportedSectionsSubmodule_unit_le_kernelIdealSheaf_of_isEtale B S hS X C T c hcE
    hcmiss
  -- A morphism from a scheme chart to `X` landing outside `T` factors through the complement.
  have hfac : ∀ (a : BigFppfOver B S hS) (φ : yoneda.obj a ⟶ X.1),
      Set.range (pointsMap B S hS (yoneda.obj a) φ) ⊆ Tᶜ → ∃ ψ, ψ ≫ c.hom = φ := by
    intro a φ hφ
    exact (factorsThrough_openSubspace_iff_points B S hS X.2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS a) Csub hCopen φ).2
      (by rw [hCrange]; exact hφ)
  intro s hs
  refine (mem_ker_structureSharp_iff B S hS g V.unop s).2 fun j => ?_
  set W : SmallEtale B S hS Y.1 := j.right.unop with hW
  set h := chartBaseChangeMap B S hS g V.unop j with hh
  have hcomm : W.1.hom ≫ g.hom = yoneda.map h ≫ V.unop.1.hom :=
    (chartDiagramOfIndex B S hS g V.unop j).comm
  -- The pullback of `s` to the chart `W` of `Y`.
  set t : ToType ((structureRingSheaf B S hS Y).obj.obj (op W)) :=
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom s with ht
  have hsupp : SectionSupportedIn B S hS Y.1 Y.2 (pointsMap B S hS Y.1 g.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS Y)) W t := by
    refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS Y
      (pointsMap B S hS Y.1 g.hom ⁻¹' T) hTY
      (SheafOfModules.unit (structureRingSheaf B S hS Y)) W t ?_
    intro U i hi
    -- The composite morphism of schemes `U ⟶ W ⟶ V`.
    set k : (SmallEtale.toOver B S hS Y.1).obj U ⟶
        (SmallEtale.toOver B S hS X.1).obj V.unop :=
      (SmallEtale.toOver B S hS Y.1).map i ≫ h with hk
    have hUhom : yoneda.map ((SmallEtale.toOver B S hS Y.1).map i) ≫ W.1.hom = U.1.hom :=
      CostructuredArrow.w i.hom
    have hkcomm : yoneda.map k ≫ V.unop.1.hom = U.1.hom ≫ g.hom := by
      rw [hk, Functor.map_comp, Category.assoc, ← hcomm, ← Category.assoc, hUhom]
    -- The chart `U` lies over the complement of `T`, hence maps to it.
    have hrange : Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj U)) (U.1.hom ≫ g.hom)) ⊆ Tᶜ := by
      rintro _ ⟨v, rfl⟩
      rw [← hUhom, pointsMap_comp_apply, pointsMap_comp_apply]
      exact hi v
    obtain ⟨ψ, hψ⟩ := hfac _ (U.1.hom ≫ g.hom) hrange
    -- Hence the section is killed there.
    have hker := kernelIdealSheaf_le_ker_of_lift B S hS c V.unop k ψ
      (by rw [hkcomm, ← hψ]) (hJc V hs)
    have hzero : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom s = 0 :=
      RingHom.mem_ker.mp hker
    have hfactor : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom s =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS Y.1).map i)).op).hom t := by
      rw [ht, hk, Functor.map_comp, op_comp, Functor.map_comp]
      rfl
    exact hfactor.symm.trans hzero
  exact RingHom.mem_ker.mpr (hY W t hsupp)

/-! ### Factoring through the strict transform -/

section StrictTransform

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1)

/-- The inverse image of `Z` along `Y ⟶ X ⟶ A` is an effective Cartier divisor as soon as the
inverse image of `f⁻¹Z` along `Y ⟶ X` is: the two closed subspaces of `Y` have the same
underlying subfunctor. -/
@[ega "IV 21.4.4" "(D)"]
theorem isPullbackDefined_comp_of_isPullbackDefined_preimage {Y : AlgebraicSpaces B S hS}
    (y : Y ⟶ X) (hy : IsPullbackDefined B S hS y (preimageClosedSubspace f Z)) :
    IsPullbackDefined B S hS (y ≫ f) Z := by
  refine isEffectiveCartierDivisor_of_subfunctor_eq
    (D' := preimageClosedSubspace y (preimageClosedSubspace f Z)) ?_ hy
  exact Subfunctor.preimage_comp Z.1 y.hom f.hom

/-- **A morphism to `X ×_A A'` over an object of the category `𝒞` of Stacks 085U factors through
the strict transform.**  Let `b` be the blowup of `A` in `Z` and let `g : Y ⟶ X ×_A A'` be a
morphism whose composite with the projection to `X` pulls `f⁻¹Z` back to an effective Cartier
divisor on `Y`.  Then `g` factors through the closed subspace `X' ⊆ X ×_A A'`.

The defining ideal of `X'` is the ideal of sections of `𝒪_{X ×_A A'}` supported on the
exceptional preimage, and `𝒪_Y` has no nonzero local section supported over it: the inverse
image of the exceptional preimage along `g` is the effective Cartier divisor assumed, and
Stacks 083S makes the structure sheaf have no sections supported on an effective Cartier
divisor. -/
theorem exists_comp_eq_strictTransformSpaceι (hb : IsBlowupAlong B S hS Z b)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ strictTransformPullback B S hS f b)
    (hg : IsPullbackDefined B S hS (g ≫ strictTransformPullbackToSource B S hS f b)
      (preimageClosedSubspace f Z)) :
    ∃ l : Y ⟶ strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1,
      l ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 = g := by
  -- The inverse image of the exceptional preimage along `g` is the assumed divisor.
  have hpre : (exceptionalPreimageClosedSubspace B S hS f b Z).1.preimage g.hom =
      (preimageClosedSubspace (g ≫ strictTransformPullbackToSource B S hS f b)
        (preimageClosedSubspace f Z)).1 := by
    rw [preimage_exceptionalPreimage_eq_preimage_centre B S hS f b Z g.hom,
      ← preimage_preimageClosedSubspace_comp_toSource B S hS f b Z g.hom]
    rfl
  have hsets : pointsMap B S hS Y.1 g.hom ⁻¹'
        exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1 =
      subspacePointSet B S hS Y.1
        (preimageClosedSubspace (g ≫ strictTransformPullbackToSource B S hS f b)
          (preimageClosedSubspace f Z)).1 := by
    rw [← hpre]
    exact (range_pointsMap_preimage_ι B S hS g.hom
      (exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1)).symm
  -- `𝒪_Y` has no sections supported there, by Stacks 083S.
  have hYno : HasNoSectionsSupportedIn B S hS Y
      (pointsMap B S hS Y.1 g.hom ⁻¹'
        exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)
      (SheafOfModules.unit (structureRingSheaf B S hS Y)) := by
    rw [hsets]
    exact hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor B S hS Y _ hg
  have hTclosed : IsClosed
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2 _
      (exceptionalPreimage_isClosedSubspace B S hS f b (preimageClosedSubspace b Z).1
        (preimageClosedSubspace b Z).2).2
  have hTYclosed : IsClosed (pointsMap B S hS Y.1 g.hom ⁻¹'
      exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) := by
    rw [hsets]
    exact isClosed_range_pointsMap_of_isClosedImmersion B S hS Y.2 _
      (preimageClosedSubspace (g ≫ strictTransformPullbackToSource B S hS f b)
        (preimageClosedSubspace f Z)).2.2
  have hJ := supportedSectionsSubmodule_unit_le_kernelIdealSheaf B S hS
    (strictTransformPullback B S hS f b) Y
    (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) hTclosed g
    hTYclosed hYno
  -- Stacks 03MB: the defining ideal of `X'` lies in the kernel ideal sheaf of `g`.
  refine (exists_comp_eq_iff_forall_isAffine_definingIdealAt_le B S hS
    (strictTransformPullback B S hS f b) Y
    (strictTransform B S hS f b (preimageClosedSubspace b Z).1) g).2 ?_
  intro U _ a k y hy
  refine le_trans ?_ (kernelIdealSheaf_le_ker_of_lift B S hS g U k y hy)
  intro s hs
  refine hJ (op U) ?_
  have hid : definingIdealAt B S hS (strictTransformPullback B S hS f b)
      (strictTransform B S hS f b (preimageClosedSubspace b Z).1) (op U) =
      (strictTransformIdealSubmodule B S hS f b
        (preimageClosedSubspace b Z).1).toSubmodule.obj (op U) :=
    congrArg (fun N : (SheafOfModules.unit
          (structureRingSheaf B S hS (strictTransformPullback B S hS f b))).Submodule =>
        N.toSubmodule.obj (op U))
      (definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS f b Z hb)
  rw [hid] at hs
  exact hs

/-! ### Stacks 0864, clause (1) -/

/-- **Stacks 0864, clause (1).**  Let `S` be a scheme, let `A` be an algebraic space over `S`,
let `Z ⊆ A` be a closed subspace, let `b : A' ⟶ A` be the blowup of `A` in `Z` and let
`f : X ⟶ A` be an algebraic space over `A`.  Then the strict transform `X'` of `X` — the closed
subspace of `X ×_A A'` of Stacks 0862, clause (2) — with its morphism
`X' ⟶ X ×_A A' ⟶ X`, **is the blowup of `X` in the inverse image `f⁻¹Z`.**

No hypothesis beyond `b` being the blowup of `A` in `Z` is carried: in particular no second
blowup is assumed to exist, and nothing is assumed of `f`.

Both halves of the universal property of Stacks 085U are checked.  Membership in the category
`𝒞` is `AlgebraicGeometry.Space.isPullbackDefined_strictTransform_of_isBlowupAlong`.  For
finality, an object `y : Y ⟶ X` of `𝒞` gives a morphism `Y ⟶ X ×_A A'` with components `y` and
the classifying morphism of `b`, which factors through `X'` by
`AlgebraicGeometry.Space.exists_comp_eq_strictTransformSpaceι`; and the factorization is unique
because `X' ⟶ X ×_A A'` is a monomorphism, `X ×_A A'` is a fibre product and the classifying
morphism of `b` is unique. -/
@[stacks 0864 "part (1): the strict transform of X is the blowup of X in the inverse image of \
the centre, for an arbitrary blowup of the base and with no assumed inputs"]
theorem isBlowupAlong_strictTransform (hb : IsBlowupAlong B S hS Z b) :
    IsBlowupAlong B S hS (preimageClosedSubspace f Z)
      (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
        strictTransformPullbackToSource B S hS f b) := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  refine isBlowupAlong_of_existsUnique_lift
    (isPullbackDefined_strictTransform_of_isBlowupAlong B S hS f b Z hb) ?_
  intro Y y hy
  have hZy : IsPullbackDefined B S hS (y ≫ f) Z :=
    isPullbackDefined_comp_of_isPullbackDefined_preimage B S hS f Z y hy
  obtain ⟨cl, hcl, hcluniq⟩ := hb.existsUnique_lift (y ≫ f) hZy
  have hgfst : sq.lift y cl hcl.symm ≫ strictTransformPullbackToSource B S hS f b = y :=
    sq.lift_fst _ _ _
  obtain ⟨l, hl⟩ := exists_comp_eq_strictTransformSpaceι B S hS f b Z hb
    (sq.lift y cl hcl.symm) (by rw [hgfst]; exact hy)
  -- The projection to `A'` of any morphism to `X ×_A A'` over `y` is the classifying morphism.
  have hsnd : ∀ φ : Y ⟶ strictTransformPullback B S hS f b,
      φ ≫ strictTransformPullbackToSource B S hS f b = y →
      φ ≫ strictTransformPullbackToBlowUp B S hS f b = cl := by
    intro φ hφ
    refine hcluniq _ ?_
    show (φ ≫ strictTransformPullbackToBlowUp B S hS f b) ≫ b = y ≫ f
    rw [Category.assoc, ← sq.w, ← Category.assoc, hφ]
  have hltop : l ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
      strictTransformPullbackToSource B S hS f b = y := by
    rw [← Category.assoc, hl, hgfst]
  refine ⟨l, hltop, ?_⟩
  intro l' hl'
  have hl'top : l' ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
      strictTransformPullbackToSource B S hS f b = y := hl'
  -- Two lifts agree: `X ×_A A'` is cartesian and the closed immersion of `X'` is a monomorphism.
  have hcomp : l' ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 =
      l ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 := by
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hl'top, hltop]
    · rw [hsnd _ (by rw [← Category.assoc] at hl'top; exact hl'top),
        hsnd _ (by rw [← Category.assoc] at hltop; exact hltop)]
  refine ObjectProperty.hom_ext _ ?_
  refine (cancel_mono (strictTransform B S hS f b (preimageClosedSubspace b Z).1).1.ι).1 ?_
  exact congrArg (fun ψ : Y ⟶ strictTransformPullback B S hS f b => ψ.hom) hcomp

/-- **The canonical comparison of Stacks 0864 is an isomorphism onto the strict transform.**  Let
`b'' : X'' ⟶ X` be a blowup of `X` in `f⁻¹Z`.  The comparison
`i : X'' ⟶ X ×_A A'` of
`AlgebraicGeometry.Space.strictTransformBlowUpComparison` factors as an isomorphism
`X'' ≅ X'` followed by the closed immersion of the strict transform.

This is the reading of Stacks 0864, clause (1) the source's proof gives — "`i` is a closed
immersion with image `X'`" — and it follows from
`AlgebraicGeometry.Space.isBlowupAlong_strictTransform`: both `X''` and `X'` are blowups of `X`
in `f⁻¹Z`, hence isomorphic over `X` by
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, and the isomorphism composed with the closed
immersion of `X'` is the comparison by the uniqueness of the latter. -/
theorem exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison
    {X'' : AlgebraicSpaces B S hS} (b'' : X'' ⟶ X) (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    ∃ e : X'' ≅ strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1,
      e.hom ≫ strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 =
        strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' := by
  obtain ⟨e, he⟩ := hb''.exists_iso (isBlowupAlong_strictTransform B S hS f b Z hb)
  refine ⟨e, (existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong
    B S hS f b Z b'' hb hb'').unique ?_
    (strictTransformBlowUpComparison_comp_toSource B S hS f b Z b'' hb hb'')⟩
  rw [Category.assoc]
  exact he

/-- **The canonical comparison of Stacks 0864 is a closed immersion.**  This is the first half
of the reading of clause (1) that the source's proof gives, and follows from
`AlgebraicGeometry.Space.exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison`
because being a closed immersion is invariant under precomposition with an isomorphism. -/
theorem isClosedImmersion_strictTransformBlowUpComparison
    {X'' : AlgebraicSpaces B S hS} (b'' : X'' ⟶ X) (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    IsClosedImmersion B S hS
      (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom := by
  obtain ⟨e, he⟩ := exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison
    B S hS f b Z b'' hb hb''
  have hrespects : (closedImmersionPresheafProperty B S hS).RespectsIso :=
    MorphismProperty.relative_respectsIso _
  have hiso : IsIso e.hom.hom :=
    ⟨⟨e.inv.hom, congrArg (fun ψ : X'' ⟶ X'' => ψ.hom) e.hom_inv_id,
      congrArg (fun ψ : strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1 ⟶
        strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1 => ψ.hom)
        e.inv_hom_id⟩⟩
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp _ e.hom.hom _
    (strictTransform B S hS f b (preimageClosedSubspace b Z).1).2.2

/-- **The image of the canonical comparison of Stacks 0864 is the strict transform.**  This is
the second half of the reading of clause (1) that the source's proof gives: the range of
`i : X'' ⟶ X ×_A A'` is `AlgebraicGeometry.Space.strictTransformSubfunctor` of Stacks 0862,
clause (2).  It follows from
`AlgebraicGeometry.Space.exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison`,
the range of an isomorphism followed by the inclusion of a subfunctor being that
subfunctor. -/
theorem range_strictTransformBlowUpComparison
    {X'' : AlgebraicSpaces B S hS} (b'' : X'' ⟶ X) (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    Subfunctor.range (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom =
      strictTransformSubfunctor B S hS f b (preimageClosedSubspace b Z).1 := by
  obtain ⟨e, he⟩ := exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison
    B S hS f b Z b'' hb hb''
  rw [← he]
  refine le_antisymm (fun T x hx => ?_) (fun T x hx => ?_)
  · obtain ⟨w, rfl⟩ := hx
    exact (e.hom.hom.app T w).2
  · refine ⟨e.inv.hom.app T ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val
      (congrArg (fun ψ : strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1 ⟶
          strictTransformSpace B S hS f b (preimageClosedSubspace b Z).1 =>
        ψ.hom.app T ⟨x, hx⟩) e.inv_hom_id)

end StrictTransform

end AlgebraicGeometry.Space

end
