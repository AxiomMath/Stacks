module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.RingEquivTransport
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# The relative spectrum of a finite algebra is finite over the base

Let `Z` be an algebraic space over a scheme `S`.  An algebraic space `W` affine over `Z` is finite
over `Z` as soon as its direct-image algebra `W_* 𝒪_W` is a finite `𝒪_Z`-algebra, and of finite
presentation over `Z` as soon as that algebra is of finite presentation.  Applied to the relative
spectrum `\underline{Spec}_Z(A)`, whose direct image is `A`, this is the assertion of Stacks 081W
that the relative spectrum of a finite, respectively finitely presented, quasi-coherent algebra is
finite, respectively of finite presentation, over the base.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.IsFinite.of_iso` and
  `AlgebraicGeometry.Space.AlgebraSheaf.IsFinitePresentation.of_iso`: the two conditions are
  invariant under isomorphism of algebra sheaves.
* `AlgebraicGeometry.Space.holdsOnAffineBaseChange_of_etaleChart_affineOpens`: a property of
  scheme morphisms which is Zariski-local at the target, stable under base change and
  effectively descended along surjective étale morphisms holds on every affine base change of a
  relatively representable morphism as soon as it holds on the represented base changes along
  the affine opens of one surjective étale chart of the target.
* `AlgebraicGeometry.Space.isFinite_affineOver_of_isFinite_pushforwardAlgebra`: an algebraic
  space affine over the base whose direct-image algebra is finite is finite over the base.
* `AlgebraicGeometry.Space.isIntegralHom_of_isIntegral_pushforwardAlgebra`: an algebraic space
  affine over the base whose direct-image algebra is integral is integral over the base.
* `isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra`: an algebraic
  space affine over the base whose direct-image algebra is of finite presentation is of finite
  presentation over the base.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **Finiteness is invariant under isomorphism of algebra sheaves.** -/
theorem IsFinite.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (hA : A.IsFinite) : C.IsFinite :=
  (isFinite_iff_isIntegral_and_isFiniteType C).2
    ⟨IsIntegral.of_iso e hA.isIntegral, IsFiniteType.of_iso e hA.isFiniteType⟩

/-- **Finite presentation is invariant under isomorphism of algebra sheaves.** -/
theorem IsFinitePresentation.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (hA : A.IsFinitePresentation) : C.IsFinitePresentation := by
  intro U hU
  rw [← comp_algebraMap e.hom (.op U)]
  exact RingHom.FinitePresentation.comp
    (RingEquiv.finitePresentation
      (RingEquiv.ofBijective _ (bijective_iso_right_app e (op U)))) (hA U hU)

end AlgebraSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine opens of an étale chart are étale charts -/

/-- **An open subobject of an étale chart is an étale chart**: for an étale chart `q` of `Y` with
source `U` and an open `O` of the scheme of `U`, the composite of the inclusion of `O` with `q` is
an étale chart. -/
theorem presheaf_etale_openObjHom_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Y}
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (openObjHom B S hS U O) ≫ q) := by
  have := isMultiplicative_presheaf_etale B S hS
  refine MorphismProperty.comp_mem _ _ _ ?_ hqe
  refine (presheaf_yoneda_map_etale_iff B S hS (openObjHom B S hS U O)).2 ?_
  have h : _root_.AlgebraicGeometry.Etale O.ι := inferInstance
  rw [toScheme_map_openObjHom B S hS U O]
  exact h

/-! ### The passage from the affine opens of one étale chart to every affine base change -/

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_affinePushforwardAlgebraFinite
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `Q` be Zariski-local at the target.  If the represented base changes of `f` along the
composites of `g : yoneda.obj a ⟶ Y` with the inclusions of the affine opens of the scheme of `a`
have `Q`, then so has the represented base change of `f` along `g`. -/
theorem property_snd_of_property_snd_affineOpens
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    {f : X ⟶ Y} (hrep : yoneda.relativelyRepresentable f) {a : BigFppfOver B S hS}
    (g : yoneda.obj a ⟶ Y)
    (hQ : ∀ V : ((BigFppfOver.toScheme B S hS).obj a).affineOpens,
      Q ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openObjHom B S hS a V.1) ≫ g)))) :
    Q ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
  property_snd_of_affineOpens Q hrep g fun V =>
    ⟨_, hrep.snd _, hrep.fst _, hQ V, hrep.isPullback _⟩

/-- Let `Q` be a property of morphisms of schemes which is Zariski-local at
the target, stable under base change, whose source is affine over an affine target, and which
descends effectively along the surjective étale morphisms of the site.  A relatively
representable morphism of algebraic spaces whose represented base changes along the affine opens
of *one* surjective étale chart of its target have `Q` has `Q` on *every* affine base change. -/
theorem holdsOnAffineBaseChange_of_etaleChart_affineOpens
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    [MorphismProperty.IsStableUnderBaseChange Q] [IsZariskiLocalAtTarget Q]
    (hQaff : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → IsAffine Z → IsAffine W)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hrep : yoneda.relativelyRepresentable f)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Y}
    (hqs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hQ : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      Q ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q)))) :
    HoldsOnAffineBaseChange B S hS Q f := by
  have hchart : Q ((BigFppfOver.toScheme B S hS).map (hrep.snd q)) :=
    property_snd_of_property_snd_affineOpens B S hS Q hrep q hQ
  have _ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hbase : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd f q) := by
    refine MorphismProperty.relative.of_exists fun {a} g => ?_
    obtain ⟨t, rfl⟩ : ∃ t : a ⟶ U, yoneda.map t = g := ⟨yoneda.preimage g, by simp⟩
    have hsq := IsPullback.of_right' (hrep.isPullback (yoneda.map t ≫ q))
      (IsPullback.of_hasPullback f q)
    exact ⟨_, _, _, hsq, property_snd_comp B S hS hrep q t _ rfl hchart⟩
  exact HoldsOnAffineBaseChange.of_etaleChart B S hS inferInstance hQaff hdesc hX hY hqs hqe
    (HoldsOnAffineBaseChange.of_presheaf hQaff hbase)

/-- A relatively representable morphism of algebraic spaces over `S` whose represented base
changes along the affine opens of one surjective étale chart of its target are finite morphisms of
schemes is finite. -/
theorem isFinite_of_etaleChart_affineOpens
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hrep : yoneda.relativelyRepresentable f)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Y}
    (hqs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hfin : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q)))) :
    IsFinite B S hS f := by
  have _ := Stacks.Morphisms.isFinite_respectsIso.{u}
  have _ := isZariskiLocalAtTarget_isFinite.{u}
  refine (isFinite_iff_holdsOnAffineBaseChange f).2 ?_
  exact holdsOnAffineBaseChange_of_etaleChart_affineOpens B S hS
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (fun p hp hZ => isAffine_of_isFinite p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isFinite B S hS) hX hY hrep hqs hqe hfin

/-- A relatively representable morphism of algebraic spaces over `S` whose represented base
changes along the affine opens of one surjective étale chart of its target are integral morphisms
of schemes is integral. -/
theorem isIntegralHom_of_etaleChart_affineOpens
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hrep : yoneda.relativelyRepresentable f)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Y}
    (hqs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hint : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q)))) :
    IsIntegralHom B S hS f := by
  have _ := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have _ := isZariskiLocalAtTarget_isIntegralHom.{u}
  refine (isIntegralHom_iff_holdsOnAffineBaseChange f).2 ?_
  exact holdsOnAffineBaseChange_of_etaleChart_affineOpens B S hS
    (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
    (fun p hp hZ => isAffine_of_isIntegralHom p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom B S hS) hX hY hrep hqs hqe hint

/-! ### Affine criteria -/

/-- **A morphism of affine schemes with finite sections map is finite.** -/
theorem isFinite_of_isAffine_of_finite_appTop {V W : Scheme.{u}} (p : W ⟶ V) [IsAffine V]
    [IsAffine W] (h : RingHom.Finite (p.appTop).hom) :
    _root_.AlgebraicGeometry.IsFinite p :=
  (_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType p).mpr
    ⟨(@HasAffineProperty.iff_of_isAffine @_root_.AlgebraicGeometry.IsIntegralHom _
        _root_.AlgebraicGeometry.IsIntegralHom.hasAffineProperty _ _ p _).mpr
      ⟨inferInstance, RingHom.IsIntegral.of_finite h⟩,
      (HasRingHomProperty.iff_of_isAffine
        (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType)).mpr (RingHom.FiniteType.of_finite h)⟩

/-- **A morphism of affine schemes whose sections map is of finite presentation is locally of
finite presentation.** -/
theorem locallyOfFinitePresentation_of_isAffine_of_finitePresentation_appTop {V W : Scheme.{u}}
    (p : W ⟶ V) [IsAffine V] [IsAffine W] (h : RingHom.FinitePresentation (p.appTop).hom) :
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation p :=
  (HasRingHomProperty.iff_of_isAffine
    (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation)).mpr h

/-- Being locally of finite presentation is Zariski-local at the target. -/
theorem isZariskiLocalAtTarget_locallyOfFinitePresentation :
    IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    (@HasRingHomProperty.HasAffineProperty _ _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation)

/-! ### The relative spectrum of a finite algebra -/

variable {Z : AlgebraicSpaces B S hS}

/-- The explicit chart-base-change algebra of an algebraic space `g` affine over the base, over
an affine étale chart of the base, has the global-sections map of the represented base change of
`g`'s structure morphism as its structure-algebra map. -/
theorem algebraMap_smallBaseChangeSharpCommRingCat (g : Over Z)
    (hrep : yoneda.relativelyRepresentable g.hom.hom) (C : SmallEtale B S hS Z.1) :
    (AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS g.hom hrep)).algebraMap (op C) =
      ((BigFppfOver.toScheme B S hS).map (hrep.snd C.1.hom)).appTop.hom := by
  rw [← Scheme.Γ_map_op]
  rfl

/-- The represented base change of an affine morphism along an affine open of an étale chart has
affine source. -/
private theorem isAffine_pullback_openObjHom_comp {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ Y)
    (haff : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (yoneda.map (openObjHom B S hS U V.1) ≫ q))) :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U V.1)) := V.2
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q))) := haff.property_snd _
  isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map
    (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q)))

/-- **An algebraic space affine over the base whose direct-image algebra is finite is finite over
the base.** -/
theorem isFinite_affineOver_of_isFinite_pushforwardAlgebra (W : AffineOver B S hS Z)
    (hW : (pushforwardAlgebra B S hS W.obj).IsFinite) :
    IsFinite B S hS W.obj.hom.hom := by
  have hrep : yoneda.relativelyRepresentable W.obj.hom.hom :=
    relativelyRepresentable_hom_of_isAffineHom B S hS W.obj.hom W.property
  have hexp : (AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS
      W.obj.hom hrep)).IsFinite :=
    AlgebraSheaf.IsFinite.of_iso (chartSharpAlgebraIso B S hS W.obj hrep) hW
  have haff := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    W.obj.left.2 Z.2 W.property).2
  obtain ⟨U, q, hqs, hqe⟩ := Z.2.exists_atlas
  refine isFinite_of_etaleChart_affineOpens B S hS W.obj.left.2 Z.2 hrep hqs hqe fun V => ?_
  have hfin := hexp ⟨CostructuredArrow.mk (yoneda.map (openObjHom B S hS U V.1) ≫ q),
    presheaf_etale_openObjHom_comp B S hS hqe V.1⟩ V.2
  rw [algebraMap_smallBaseChangeSharpCommRingCat B S hS W.obj hrep] at hfin
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U V.1)) := V.2
  have := isAffine_pullback_openObjHom_comp B S hS hrep q haff V
  exact isFinite_of_isAffine_of_finite_appTop ((BigFppfOver.toScheme B S hS).map
    (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q))) hfin

/-- **An algebraic space affine over the base is integral over the base as soon as its
direct-image algebra is integral over the affine opens of one surjective étale chart.** -/
theorem isIntegralHom_of_isIntegral_pushforwardAlgebra_affineOpens (W : AffineOver B S hS Z)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Z.1}
    (hqs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hW : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      RingHom.IsIntegral ((pushforwardAlgebra B S hS W.obj).algebraMap
        (op ⟨CostructuredArrow.mk (yoneda.map (openObjHom B S hS U V.1) ≫ q),
          presheaf_etale_openObjHom_comp B S hS hqe V.1⟩))) :
    IsIntegralHom B S hS W.obj.hom.hom := by
  have hrep : yoneda.relativelyRepresentable W.obj.hom.hom :=
    relativelyRepresentable_hom_of_isAffineHom B S hS W.obj.hom W.property
  have haff := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    W.obj.left.2 Z.2 W.property).2
  refine isIntegralHom_of_etaleChart_affineOpens B S hS W.obj.left.2 Z.2 hrep hqs hqe fun V => ?_
  let C : SmallEtale B S hS Z.1 :=
    ⟨CostructuredArrow.mk (yoneda.map (openObjHom B S hS U V.1) ≫ q),
      presheaf_etale_openObjHom_comp B S hS hqe V.1⟩
  have hint : RingHom.IsIntegral
      ((AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS
        W.obj.hom hrep)).algebraMap (op C)) := by
    have e := chartSharpAlgebraIso B S hS W.obj hrep
    have hcomp : (AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS
        W.obj.hom hrep)).algebraMap (op C) =
        (e.hom.right.hom.app (op C)).hom.comp
          ((pushforwardAlgebra B S hS W.obj).algebraMap (op C)) :=
      RingHom.ext fun r => (e.hom.comm (op C) r).symm
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (hW V)
      (RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _
        (AlgebraSheaf.bijective_iso_right_app e (op C)).2))
  rw [algebraMap_smallBaseChangeSharpCommRingCat B S hS W.obj hrep] at hint
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U V.1)) := V.2
  have := isAffine_pullback_openObjHom_comp B S hS hrep q haff V
  exact (@HasAffineProperty.iff_of_isAffine @_root_.AlgebraicGeometry.IsIntegralHom _
    _root_.AlgebraicGeometry.IsIntegralHom.hasAffineProperty _ _ _ _).mpr ⟨inferInstance, hint⟩

/-- **An algebraic space affine over the base whose direct-image algebra is integral is integral
over the base.** -/
theorem isIntegralHom_of_isIntegral_pushforwardAlgebra (W : AffineOver B S hS Z)
    (hW : (pushforwardAlgebra B S hS W.obj).IsIntegral) :
    IsIntegralHom B S hS W.obj.hom.hom := by
  obtain ⟨U, q, hqs, hqe⟩ := Z.2.exists_atlas
  exact isIntegralHom_of_isIntegral_pushforwardAlgebra_affineOpens B S hS W hqs hqe
    fun V => hW _ V.2

/-- **An algebraic space affine over the base whose direct-image algebra is of finite presentation
is of finite presentation over the base.** -/
theorem isFinitePresentation_affineOver_of_isFinitePresentation_pushforwardAlgebra
    (W : AffineOver B S hS Z)
    (hW : (pushforwardAlgebra B S hS W.obj).IsFinitePresentation) :
    IsFinitePresentation B S hS W.obj.hom.hom := by
  have hrep : yoneda.relativelyRepresentable W.obj.hom.hom :=
    relativelyRepresentable_hom_of_isAffineHom B S hS W.obj.hom W.property
  have hexp : (AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS
      W.obj.hom hrep)).IsFinitePresentation :=
    AlgebraSheaf.IsFinitePresentation.of_iso (chartSharpAlgebraIso B S hS W.obj hrep) hW
  have haff := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    W.obj.left.2 Z.2 W.property).2
  obtain ⟨U, q, hqs, hqe⟩ := Z.2.exists_atlas
  have _ := isZariskiLocalAtTarget_locallyOfFinitePresentation.{u}
  have hlfp : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hrep.snd q)) := by
    refine property_snd_of_property_snd_affineOpens B S hS
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) hrep q fun V => ?_
    have hfp := hexp ⟨CostructuredArrow.mk (yoneda.map (openObjHom B S hS U V.1) ≫ q),
      presheaf_etale_openObjHom_comp B S hS hqe V.1⟩ V.2
    rw [algebraMap_smallBaseChangeSharpCommRingCat B S hS W.obj hrep] at hfp
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U V.1)) := V.2
    have := isAffine_pullback_openObjHom_comp B S hS hrep q haff V
    exact locallyOfFinitePresentation_of_isAffine_of_finitePresentation_appTop
      ((BigFppfOver.toScheme B S hS).map
        (hrep.snd (yoneda.map (openObjHom B S hS U V.1) ≫ q))) hfp
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hpe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst q) :=
    MorphismProperty.of_isPullback (hrep.isPullback q).flip hqe
  have hps : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst q) :=
    MorphismProperty.of_isPullback (hrep.isPullback q).flip hqs
  refine ⟨?_, isQuasiCompact_of_isAffineHom' B S hS _ W.obj.left.2 Z.2 W.property,
    isQuasiSeparated_of_isAffineHom B S hS _ W.obj.left.2 Z.2 W.property⟩
  have hiff := (isLocallyOfFinitePresentation_tfae B S hS W.obj.left.2 Z.2 W.obj.hom.hom).out 8 1
  exact hiff.mp
    ⟨hrep.pullback q, U, hrep.fst q, q, hrep.snd q,
      isEtale_of_presheaf_etale B S hS hpe, isEtale_of_presheaf_etale B S hS hqe,
      (presheafSurjective_iff_isSurjective_yoneda B S hS _ W.obj.left.2 _ _).mp hps,
      hrep.w q, isLocallyOfFinitePresentation_yoneda_map B S hS _ hlfp⟩

end AlgebraicGeometry.Space

end
