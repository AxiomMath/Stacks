module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfDescentConverse
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeOpenCoverLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentableDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Relative pseudo-coherence on the étale charts of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, locally of finite type, let
`m` be an integer and let `E` be an object of `D_QCoh(𝒪_X)`.  Stacks 0CSX compares three tests of
relative `m`-pseudo-coherence of `E` over `Y`, all read on commuting squares of étale scheme
charts `U ⟶ X`, `V ⟶ Y`:

1. on every such square, `E|_U` is `m`-pseudo-coherent relative to `V`;
2. on some such square with `U ⟶ X` surjective, `E|_U` is `m`-pseudo-coherent relative to `V`;
3. on every such square with `U` and `V` affine, `RΓ(U, E)` is `m`-pseudo-coherent relative to
   `𝒪_Y(V)`.

The phrase "`E|_U` is `m`-pseudo-coherent relative to `V`" is the convention of Remark 0CSW,
`AlgebraicGeometry.Space.IsRepresentablyRelativelyPseudoCoherentFrom`, and `RΓ(U, E)` is the
complex of derived sections of the object `E₀` of Remark 0CSW,
`AlgebraicGeometry.Space.representableDerivedDescent`.

## Main definitions

* `AlgebraicGeometry.Space.IsPseudoCoherentFromOnEtaleSquare`: condition (1)/(2) on one square.
* `AlgebraicGeometry.Space.DerivedSectionsPseudoCoherentOnEtaleSquare`: condition (3) on one
  square of affine charts.

## Main results

* `AlgebraicGeometry.Space.relativePseudoCoherence_etaleSquare_tfae`: **Stacks 0CSX**, the three
  tests are equivalent.
* `AlgebraicGeometry.Space.isPseudoCoherentFromOnEtaleSquare_iff` and
  `AlgebraicGeometry.Space.derivedSectionsPseudoCoherentOnEtaleSquare_iff`: both conditions read
  on the complex `E|_U` of `AlgebraicGeometry.Space.chartComplex` attached to the comparison
  `AlgebraicGeometry.Space.representedZariskiComparison` of Remark 0CSW.
* `AlgebraicGeometry.Space.exists_surjective_isPseudoCoherentFromOnEtaleSquare`: (1) ⟹ (2).
* `AlgebraicGeometry.Space.derivedSectionsPseudoCoherentOnEtaleSquare_of_forall`: (1) ⟹ (3), by
  Stacks 09VF.
* `AlgebraicGeometry.Space.isPseudoCoherentFromOnEtaleSquare_of_forall_derivedSections`:
  (3) ⟹ (1), by Stacks 09VF, Stacks 0CSP, the compatibility of `E|_U` with finer charts and the
  locality of relative pseudo-coherence on the source.
* `AlgebraicGeometry.Space.exists_surjective_etale_isPseudoCoherentFrom_derivedPullback`: the
  part of (2) ⟹ (1) that precedes descent: the condition on one square with surjective source
  chart gives, on any second square, relative `m`-pseudo-coherence of the derived pullback of
  `E|_{U'}` along a surjective étale morphism to the scheme underlying `U'`.

## Implementation notes

The source's step from (2) to (1) ends by descending relative pseudo-coherence along that
surjective étale morphism.  A surjective étale morphism alone is an fppf covering, so this is
Stacks 0CSN, `Scheme.Hom.isPseudoCoherentFrom_iff_forall_derivedPullback_of_mem_fppfPrecoverage`,
applied to a covering with one member.

## References

* [Stacks Project, Tag 0CSX](https://stacks.math.columbia.edu/tag/0CSX)
* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
* [Stacks Project, Tag 0CSN](https://stacks.math.columbia.edu/tag/0CSN)
* [Stacks Project, Tag 0CSP](https://stacks.math.columbia.edu/tag/0CSP)
* [Stacks Project, Tag 09US](https://stacks.math.columbia.edu/tag/09US)
* [Stacks Project, Tag 09VF](https://stacks.math.columbia.edu/tag/09VF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe w u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The pullback of Remark 0CSW at a represented algebraic space -/

section Represented

variable (U : BigFppfOver B S hS)
  [HasDerivedCategory.{w}
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))]

/-- The transport of complexes along the identity identification `h_U = h_U` is the identity. -/
def derivedEtaleModulePullbackEquivalenceOfIsoReflObjIso
    (Y : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))) :
    (derivedEtaleModulePullbackEquivalenceOfIso B S hS
      (representableSpaceIso B S hS (isAlgebraicSpace_yoneda B S hS U)
        (Iso.refl (yoneda.obj U)))).functor.obj Y ≅ Y :=
  let e := representableSpaceIso B S hS (isAlgebraicSpace_yoneda B S hS U) (Iso.refl (yoneda.obj U))
  have he : e.hom = 𝟙 _ := ObjectProperty.hom_ext _ rfl
  have := etaleModulePullback_additive.{u, u} B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)
  have := preservesFiniteLimits_etaleModulePullback B S hS e.hom
    (isEtale_hom_of_isIso B S hS e.hom)
  have := preservesFiniteColimits_etaleModulePullback B S hS e.hom
    (isEtale_hom_of_isIso B S hS e.hom)
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      (etaleModulePullback.{u, u} B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)) (𝟭 _)
      (eqToIso (etaleModulePullback_congr B S hS _ (isEtale_hom_of_isIso B S hS (𝟙 _)) he) ≪≫
        etaleModulePullbackIdIso B S hS _)).app Y ≪≫
    StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso.app Y

end Represented

/-! The rest of the file works in `D_QCoh(𝒪_X)`,
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, with the complexes `E|_U` of
`AlgebraicGeometry.Space.chartComplex` and with the derived sections condition
`AlgebraicGeometry.Scheme.Hom.DerivedSectionsPseudoCoherentOn'`, all of which are constructed
at the standard derived categories. -/

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The condition on one square of étale charts -/

section Chart

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
  (hf : IsLocallyOfFiniteType B S hS f) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
  (m : ℤ)

/-- **The condition of Stacks 0CSX on one square of étale charts**, in the notation of Remark
0CSW: for a commuting square of étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y` over `f`, with
`g : U ⟶ V`, the complex `E|_U` is `m`-pseudo-coherent relative to `V`.  Here `E|_U` is the
derived pullback of `E` to the algebraic space represented by `U`, and the phrase is the convention
of Remark 0CSW, `AlgebraicGeometry.Space.IsRepresentablyRelativelyPseudoCoherentFrom`, for the
morphism `yoneda.map g` of represented algebraic spaces and the morphism of schemes underlying
`g`. -/
abbrev IsPseudoCoherentFromOnEtaleSquare (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f) : Prop :=
  IsRepresentablyRelativelyPseudoCoherentFrom B S hS (isAlgebraicSpace_yoneda B S hS U)
    (yoneda.map g) ((isLocallyOfFiniteType_yoneda_map_iff B S hS g).2 (hf U V a b g ha hb hc))
    g (Iso.refl _) (Iso.refl _) (by simp) (chartDerivedPullback B S hS hX E ha) m

/-- The pullback of Remark 0CSW of the complex `E|_U` read through
`AlgebraicGeometry.Space.representedZariskiComparison` is the derived pullback of `E` to the
chart. -/
def representableDerivedPullbackChartComplexIso {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a) :
    (representableDerivedPullback B S hS (isAlgebraicSpace_yoneda B S hS U)
        (Iso.refl (yoneda.obj U))).obj
        (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).obj ≅
      (chartDerivedPullback B S hS hX E ha).obj :=
  (derivedEtaleModulePullbackEquivalenceOfIso B S hS
      (representableSpaceIso B S hS (isAlgebraicSpace_yoneda B S hS U)
        (Iso.refl (yoneda.obj U)))).functor.mapIso
      (representedDerivedAssociatedModuleChartComplexIso hX E ha) ≪≫
    derivedEtaleModulePullbackEquivalenceOfIsoReflObjIso U _

/-- **The condition on one square, through the comparison of Remark 0CSW.**  The convention of
Remark 0CSW holds on a square exactly when the complex `E|_U`, read on the scheme underlying `U`
through `AlgebraicGeometry.Space.representedZariskiComparison`, is `m`-pseudo-coherent relative to
the scheme underlying `V`: the convention does not depend on the choice of `E₀`. -/
theorem isPseudoCoherentFromOnEtaleSquare_iff (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f) :
    IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc ↔
      haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
      ((BigFppfOver.toScheme B S hS).map g).IsPseudoCoherentFrom
        (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).obj m := by
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  let K := chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)
  have eK := representableDerivedPullbackChartComplexIso hX E ha
  rw [IsPseudoCoherentFromOnEtaleSquare, isRepresentablyRelativelyPseudoCoherentFrom_iff]
  refine ⟨fun h => h K.obj K.property ⟨eK⟩, fun h E₀ hE₀ ⟨e⟩ => ?_⟩
  obtain ⟨e₀⟩ := nonempty_iso_of_representableDerivedPullback_iso B S hS
    (isAlgebraicSpace_yoneda B S hS U) (Iso.refl _) E₀ K.obj hE₀ K.property (e ≪≫ eK.symm)
  exact Scheme.Hom.IsPseudoCoherentFrom.of_iso _ h e₀.symm

/-- The derived sections condition of Stacks 09VF depends on the complex only through its
isomorphism class. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.derivedSectionsPseudoCoherentOn'_iff_of_iso
    {Z T : Scheme.{u}} (q : Z ⟶ T) [LocallyOfFiniteType q] {K K' : DerivedCategory Z.Modules}
    (e : K ≅ K') (m : ℤ) {U : Z.Opens} (hU : IsAffineOpen U) {V : T.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ q ⁻¹ᵁ V) :
    q.DerivedSectionsPseudoCoherentOn' K m hU hV hUV ↔
      q.DerivedSectionsPseudoCoherentOn' K' m hU hV hUV :=
  let : Algebra Γ(T, V) Γ(Z, U) := (q.appLE V U hUV).hom.toAlgebra
  let : Algebra.FiniteType Γ(T, V) Γ(Z, U) := algebraFiniteType_appLE q U hU V hV hUV
  ⟨RingHom.isRelativelyPseudoCoherentFrom_of_iso (R := Γ(T, V))
      ((derivedSectionsUnbounded Z U).mapIso e) m,
    RingHom.isRelativelyPseudoCoherentFrom_of_iso (R := Γ(T, V))
      ((derivedSectionsUnbounded Z U).mapIso e).symm m⟩

/-- **The condition of Stacks 0CSX on one square of affine étale charts**: the complex
`RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent relative to `𝒪_Y(V)`.  It is the complex of
derived sections over the scheme underlying `U` of the object `E₀` of Remark 0CSW whose pullback to
the algebraic space represented by `U` is `E|_U`. -/
abbrev DerivedSectionsPseudoCoherentOnEtaleSquare (U V : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) : Prop :=
  haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  ((BigFppfOver.toScheme B S hS).map g).DerivedSectionsPseudoCoherentOn'
    (representableDerivedDescent B S hS (isAlgebraicSpace_yoneda B S hS U)
      (Iso.refl (yoneda.obj U)) (chartDerivedPullback B S hS hX E ha)) m
    (isAffineOpen_top _) (isAffineOpen_top _) (by simp)

/-- The derived sections condition read on `E₀` is the one read on the complex `E|_U` of
`AlgebraicGeometry.Space.representedZariskiComparison`, the two being isomorphic. -/
theorem derivedSectionsPseudoCoherentOnEtaleSquare_iff (U V : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    DerivedSectionsPseudoCoherentOnEtaleSquare hX f hf E m U V a b g ha hb hc hU hV ↔
      haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
      ((BigFppfOver.toScheme B S hS).map g).DerivedSectionsPseudoCoherentOn'
        (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).obj m
        (isAffineOpen_top _) (isAffineOpen_top _) (by simp) := by
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  obtain ⟨e⟩ := nonempty_iso_representableDerivedDescent B S hS
    (isAlgebraicSpace_yoneda B S hS U) (Iso.refl _) (chartDerivedPullback B S hS hX E ha)
    _ (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).property
    (representableDerivedPullbackChartComplexIso hX E ha)
  exact Scheme.Hom.derivedSectionsPseudoCoherentOn'_iff_of_iso _ e.symm m _ _ _

end Chart

/-! ### The implications of Stacks 0CSX -/

section Implications

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
  (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)

include hY in
/-- **Stacks 0CSX, (1) ⟹ (2).**  An algebraic space has a surjective étale chart, and such a
chart of the target lifts to one of the source by Stacks 02X1, so a square as in (2) exists. -/
theorem exists_surjective_isPseudoCoherentFromOnEtaleSquare
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f),
      IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc) :
    ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
      (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b),
      IsSurjective B S hS a ∧ ∃ hc : yoneda.map g ≫ b = a ≫ f,
        IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc := by
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, g, hc, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurjective hbEtale
  exact ⟨U, V, a, b, g, haEtale, hbEtale,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurjective, hc.symm,
    hall U V a b g haEtale hbEtale hc.symm⟩

/-- **Stacks 0CSX, (1) ⟹ (3).**  On a square of affine charts the condition on `E|_U` is the
condition on the complex of derived sections `RΓ(U, E)`, by Stacks 09VF. -/
theorem derivedSectionsPseudoCoherentOnEtaleSquare_of_forall
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f),
      IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    DerivedSectionsPseudoCoherentOnEtaleSquare hX f hf E m U V a b g ha hb hc hU hV := by
  have := hU
  have := hV
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  rw [derivedSectionsPseudoCoherentOnEtaleSquare_iff]
  have hiff := (derivedSectionsPseudoCoherentComparison' ((BigFppfOver.toScheme B S hS).map g)
    (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).obj
    (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).property m).out 1 3
  exact hiff.mp ((isPseudoCoherentFromOnEtaleSquare_iff hX f hf E m U V a b g ha hb hc).mp
    (hall U V a b g ha hb hc)) ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) (by simp)

/-- **Stacks 0CSX, (3) ⟹ (1).**  A square of étale charts is covered by squares of affine
charts: choose an affine open of `V` around the image of a point of `U` and an affine open of `U`
around the point inside its inverse image.  On each the condition is the one of (3), by Stacks
09VF and Stacks 0CSP, the complex `E|_U` restricts to the complex of the smaller chart by the
compatibility of `E|_U` with finer charts, and relative pseudo-coherence is local on the source. -/
theorem isPseudoCoherentFromOnEtaleSquare_of_forall_derivedSections
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f)
      (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)),
      DerivedSectionsPseudoCoherentOnEtaleSquare hX f hf E m U V a b g ha hb hc hU hV)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f) :
    IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc := by
  let T := BigFppfOver.toScheme B S hS
  have := hf U V a b g ha hb hc
  have : LocallyOfFiniteType (T.map g) := hf U V a b g ha hb hc
  rw [isPseudoCoherentFromOnEtaleSquare_iff]
  let K := chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)
  refine Scheme.Hom.isPseudoCoherentFrom_of_forall_exists_opens (T.map g) K.obj m fun x => ?_
  obtain ⟨Vx, hVxAffine, hxVx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := T.obj V) (U := ⊤) (x := (T.map g).base x) (by trivial)
  obtain ⟨Ux, hUxAffine, hxUx, hUxV'⟩ := exists_isAffineOpen_mem_and_subset
    (X := T.obj U) (U := T.map g ⁻¹ᵁ Vx) (x := x) hxVx
  have hUxV : Ux ≤ T.map g ⁻¹ᵁ Vx := hUxV'
  refine ⟨Ux, hxUx, ?_⟩
  let sIncl := openChartMap B S hS U Ux
  let tIncl := openChartMap B S hS V Vx
  have hsEtale : AlgebraicGeometry.Etale (T.map sIncl) := etale_openChartMap B S hS U Ux
  have htEtale : AlgebraicGeometry.Etale (T.map tIncl) := etale_openChartMap B S hS V Vx
  have : IsAffine (T.obj (openChartObject B S hS U Ux)) := hUxAffine
  have : IsAffine (T.obj (openChartObject B S hS V Vx)) := hVxAffine
  let rmap : openChartObject B S hS U Ux ⟶ openChartObject B S hS V Vx :=
    Over.homMk ⟨(T.map g).resLE Vx Ux hUxV⟩ (by
      apply ObjectProperty.hom_ext
      change (T.map g).resLE Vx Ux hUxV ≫ (Vx.ι ≫ V.hom.hom) = Ux.ι ≫ U.hom.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι]
      exact congrArg (fun φ ↦ Ux.ι ≫ φ) (congrArg (fun φ ↦ φ.hom) g.w))
  have hsquare : rmap ≫ tIncl = sIncl ≫ g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Scheme.Hom.resLE_comp_ι _ _
  have hse : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map sIncl ≫ a) :=
    etale_comp_of_scheme B S hS sIncl a hsEtale ha
  have hte : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map tIncl ≫ b) :=
    etale_comp_of_scheme B S hS tIncl b htEtale hb
  have hcomm : yoneda.map rmap ≫ (yoneda.map tIncl ≫ b) = (yoneda.map sIncl ≫ a) ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, hsquare, Functor.map_comp]
    simp only [Category.assoc, hc]
  have := hf _ _ _ _ rmap hse hte hcomm
  let K' := chartComplex B S hS hX E hse (representedZariskiComparison B S hS _)
  have haffine : (T.map rmap).IsPseudoCoherentFrom K'.obj m := by
    refine ((derivedSectionsPseudoCoherentComparison' (T.map rmap) K'.obj K'.property m).out 2
      1).mp ?_
    refine ⟨PUnit.{u + 1}, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ ↦ ?_⟩
    refine ⟨PUnit.{u + 1}, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ ↦ ?_⟩
    exact ⟨by simp, (derivedSectionsPseudoCoherentOnEtaleSquare_iff hX f hf E m _ _ _ _ rmap hse
      hte hcomm inferInstance inferInstance).mp
        (hall _ _ _ _ rmap hse hte hcomm inferInstance inferInstance)⟩
  have hover := (Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map rmap) (T.map tIncl)
    K'.obj m).mpr haffine
  have hmapEq : Ux.ι ≫ T.map g = T.map rmap ≫ T.map tIncl := by
    have hT : T.map (sIncl ≫ g) = T.map (rmap ≫ tIncl) := congrArg T.map hsquare.symm
    rw [T.map_comp, T.map_comp] at hT
    exact hT
  have hUxType : LocallyOfFiniteType (Ux.ι ≫ T.map g) := inferInstance
  have honOpen : (Ux.ι ≫ T.map g).IsPseudoCoherentFrom K'.obj m :=
    (@Scheme.Hom.isPseudoCoherentFrom_congr_hom _ _ _ _ hmapEq.symm inferInstance hUxType _
      m).mp hover
  obtain ⟨iso⟩ := nonempty_chartComplex_iso_derivedPullback hX E sIncl hsEtale ha hse
  exact Scheme.Hom.IsPseudoCoherentFrom.of_iso _ honOpen
    (iso ≪≫ (Scheme.Modules.derivedPullbackIsoMapDerivedCategoryRestrict Ux.ι).app K.obj)

/-- **Stacks 0CSX, (2) ⟹ (1), up to descent.**  Let the condition hold on one square whose chart
`a` of the source is surjective, and let a second square be given.  The fibre product
`U'' = U ×_X U'` is surjective étale over `U'` and maps to `V'' = V' ×_Y V`, which is étale over
`V'`.  By Stacks 09US, the pseudo-coherence of an étale morphism (Stacks 0695), Stacks 0CSP and the
compatibility of `E|_U` with finer charts, the derived pullback of `E|_{U'}` to `U''` is
`m`-pseudo-coherent relative to `V'`.  What is left of the source's argument is descent along the
surjective étale morphism `U'' ⟶ U'`. -/
theorem exists_surjective_etale_isPseudoCoherentFrom_derivedPullback
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hsurj : IsSurjective B S hS a) (hc : yoneda.map g ≫ b = a ≫ f)
    (hcond : IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc)
    (U' V' : BigFppfOver B S hS) (a' : yoneda.obj U' ⟶ X) (b' : yoneda.obj V' ⟶ Y) (g' : U' ⟶ V')
    (ha' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a')
    (hb' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b')
    (hc' : yoneda.map g' ≫ b' = a' ≫ f) :
    haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g') :=
      hf U' V' a' b' g' ha' hb' hc'
    ∃ (W : Scheme.{u}) (p : W ⟶ (BigFppfOver.toScheme B S hS).obj U')
      (_ : AlgebraicGeometry.Surjective p) (_ : AlgebraicGeometry.Etale p),
      (p ≫ (BigFppfOver.toScheme B S hS).map g').IsPseudoCoherentFrom
        ((derivedPullback p.toLRSHom.toShHom).obj
          (chartComplex B S hS hX E ha' (representedZariskiComparison B S hS U')).obj) m := by
  let T := BigFppfOver.toScheme B S hS
  have := hf U V a b g ha hb hc
  have hcond' := (isPseudoCoherentFromOnEtaleSquare_iff hX f hf E m U V a b g ha hb hc).mp hcond
  let W := ha.rep.pullback a'
  let left : W ⟶ U := ha.rep.fst' a'
  let right : W ⟶ U' := ha.rep.snd a'
  let tleft : hb.rep.pullback b' ⟶ V := hb.rep.fst' b'
  let tright : hb.rep.pullback b' ⟶ V' := hb.rep.snd b'
  have sq : IsPullback (yoneda.map left) (yoneda.map right) a a' := ha.rep.isPullback' a'
  have tsq : IsPullback (yoneda.map tleft) (yoneda.map tright) b b' := hb.rep.isPullback' b'
  have hleft : AlgebraicGeometry.Etale (T.map left) :=
    ha'.property a (yoneda.map right) left sq.flip
  have hright : AlgebraicGeometry.Etale (T.map right) := ha.property_snd a'
  have htleft : AlgebraicGeometry.Etale (T.map tleft) :=
    hb'.property b (yoneda.map tright) tleft tsq.flip
  have htright : AlgebraicGeometry.Etale (T.map tright) := hb.property_snd b'
  have hrightSurjective : AlgebraicGeometry.Surjective (T.map right) :=
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mpr hsurj).property
      a' (yoneda.map left) right sq
  have := hf U' V' a' b' g' ha' hb' hc'
  have hcomm : yoneda.map (left ≫ g) ≫ b = yoneda.map (right ≫ g') ≫ b' := by
    simp only [Functor.map_comp, Category.assoc, hc, hc']
    rw [← Category.assoc, ← Category.assoc, sq.w]
  let lift := hb.rep.lift' (left ≫ g) (right ≫ g') hcomm
  have hliftLeft : lift ≫ tleft = left ≫ g := hb.rep.lift'_fst _ _ _
  have hliftRight : lift ≫ tright = right ≫ g' := hb.rep.lift'_snd _ _ _
  have hleftEq : T.map lift ≫ T.map tleft = T.map left ≫ T.map g := by
    rw [← T.map_comp, hliftLeft, T.map_comp]
  have hrightEq : T.map lift ≫ T.map tright = T.map right ≫ T.map g' := by
    rw [← T.map_comp, hliftRight, T.map_comp]
  have hliftType : LocallyOfFiniteType (T.map lift) := by
    have : LocallyOfFiniteType (T.map lift ≫ T.map tleft) := by
      rw [hleftEq]
      infer_instance
    exact locallyOfFiniteType_of_comp (T.map lift) (T.map tleft)
  have hga : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map left ≫ a) :=
    etale_comp_of_scheme B S hS left a hleft ha
  have hga' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map right ≫ a') :=
    etale_comp_of_scheme B S hS right a' hright ha'
  let K := chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)
  let K' := chartComplex B S hS hX E ha' (representedZariskiComparison B S hS U')
  have hpulled : (T.map left ≫ T.map g).IsPseudoCoherentFrom
      ((derivedPullback (T.map left).toLRSHom.toShHom).obj K.obj) m :=
    Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback (T.map left) (T.map g) _ m hcond'
  have hoverLeft : (T.map lift ≫ T.map tleft).IsPseudoCoherentFrom
      ((derivedPullback (T.map left).toLRSHom.toShHom).obj K.obj) m :=
    (Scheme.Hom.isPseudoCoherentFrom_congr_hom hleftEq.symm _ m).mp hpulled
  have hoverRight := (Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map lift)
      (T.map tright) _ m).mpr
    ((Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map lift) (T.map tleft) _ m).mp
      hoverLeft)
  obtain ⟨isoLeft⟩ := nonempty_chartComplex_iso_derivedPullback hX E left hleft ha hga
  obtain ⟨isoRight⟩ := nonempty_chartComplex_iso_derivedPullback hX E right hright ha' hga'
  let chartIso :
      (derivedPullback (T.map left).toLRSHom.toShHom).obj K.obj ≅
        (derivedPullback (T.map right).toLRSHom.toShHom).obj K'.obj :=
    isoLeft.symm ≪≫
      eqToIso (chartComplex_congr B S hS hX E sq.w hga hga'
        (representedZariskiComparison B S hS W)) ≪≫ isoRight
  exact ⟨T.obj W, T.map right, hrightSurjective, hright,
    Scheme.Hom.IsPseudoCoherentFrom.of_iso _
      ((Scheme.Hom.isPseudoCoherentFrom_congr_hom hrightEq _ m).mp hoverRight) chartIso⟩

include hY in
/-- **Stacks 0CSX.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally
of finite type, let `m` be an integer and let `E` be an object of `D_QCoh(𝒪_X)`.  With the
notation of Remark 0CSW the following are equivalent:

1. for every commutative square `U ⟶ V` over `f` of schemes `U`, `V` with étale charts
   `U ⟶ X`, `V ⟶ Y`, the complex `E|_U` is `m`-pseudo-coherent relative to `V`;
2. for some such square with `U ⟶ X` surjective, `E|_U` is `m`-pseudo-coherent relative to `V`;
3. for every such square with `U` and `V` affine, the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is
   `m`-pseudo-coherent relative to `𝒪_Y(V)`.

(1) ⟹ (2) and (1) ⟹ (3) and (3) ⟹ (1) are
`AlgebraicGeometry.Space.exists_surjective_isPseudoCoherentFromOnEtaleSquare`,
`AlgebraicGeometry.Space.derivedSectionsPseudoCoherentOnEtaleSquare_of_forall` and
`AlgebraicGeometry.Space.isPseudoCoherentFromOnEtaleSquare_of_forall_derivedSections`.  For
(2) ⟹ (1), `AlgebraicGeometry.Space.exists_surjective_etale_isPseudoCoherentFrom_derivedPullback`
gives, on a second square, relative `m`-pseudo-coherence of the pullback of `E|_{U'}` along a
surjective étale morphism `W ⟶ U'`; that morphism alone is an fppf covering, and Stacks 0CSN
descends the property to `E|_{U'}`. -/
@[stacks 0CSX "all three conditions and their equivalence, at the source's hypotheses: f a \
morphism of algebraic spaces over S locally of finite type, E in D_QCoh(O_X), any m; the phrase \
'E|_U is m-pseudo-coherent relative to V' is the convention of Remark 0CSW"]
theorem relativePseudoCoherence_etaleSquare_tfae :
    List.TFAE
      [∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
          (hc : yoneda.map g ≫ b = a ≫ f),
          IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc,
       ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b),
          IsSurjective B S hS a ∧ ∃ hc : yoneda.map g ≫ b = a ≫ f,
            IsPseudoCoherentFromOnEtaleSquare hX f hf E m U V a b g ha hb hc,
       ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
          (hc : yoneda.map g ≫ b = a ≫ f)
          (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
          (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)),
          DerivedSectionsPseudoCoherentOnEtaleSquare hX f hf E m U V a b g ha hb hc hU hV] := by
  tfae_have 1 → 2 := exists_surjective_isPseudoCoherentFromOnEtaleSquare hX hY f hf E m
  tfae_have 1 → 3 := derivedSectionsPseudoCoherentOnEtaleSquare_of_forall hX f hf E m
  tfae_have 3 → 1 := isPseudoCoherentFromOnEtaleSquare_of_forall_derivedSections hX f hf E m
  tfae_have 2 → 1 := by
    rintro ⟨U, V, a, b, g, ha, hb, hsurj, hc, hcond⟩ U' V' a' b' g' ha' hb' hc'
    have := hf U' V' a' b' g' ha' hb' hc'
    rw [isPseudoCoherentFromOnEtaleSquare_iff]
    obtain ⟨W, p, hp, hpe, hW⟩ := exists_surjective_etale_isPseudoCoherentFrom_derivedPullback
      hX f hf E m U V a b g ha hb hsurj hc hcond U' V' a' b' g' ha' hb' hc'
    have hcover : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ W) (fun _ ↦ p) ∈
        Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj U') :=
      (Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ ⟨PUnit.unit, hp.surj x⟩, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
    exact (Scheme.Hom.isPseudoCoherentFrom_iff_forall_derivedPullback_of_mem_fppfPrecoverage
      (fun _ : PUnit.{u + 1} ↦ W) (fun _ ↦ p) _ hcover _
      (chartComplex B S hS hX E ha' (representedZariskiComparison B S hS U')).property m).mpr
      fun _ ↦ hW
  tfae_finish

end Implications

end StandardModel

end AlgebraicGeometry.Space

end
