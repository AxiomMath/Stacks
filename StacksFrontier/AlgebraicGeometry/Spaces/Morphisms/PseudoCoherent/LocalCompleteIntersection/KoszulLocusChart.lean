module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.KoszulLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocus

/-!
# The Koszul locus of a morphism of algebraic spaces read on an étale chart

Being Koszul at a point of the source of a morphism of algebraic spaces over `S` is the
condition on the morphism of schemes induced by any one pointed étale chart square through that
point.

## Main results

* `AlgebraicGeometry.koszulAt_iff_exists_opens`: for morphisms of schemes, being Koszul at a
  point is having an open neighbourhood of the point on which the morphism is a local complete
  intersection morphism.
* `AlgebraicGeometry.MorphismOfGerms.hasRepresentativeWithProperty_ofSchemeHom_iff`: the germ
  property induced by a property of morphisms of schemes which is étale local on the source and
  target holds at a point exactly when the property holds on some open neighbourhood of it.
* `AlgebraicGeometry.Space.koszulAt_iff_koszulAt_chart`: the chart dictionary. A morphism of
  algebraic spaces is Koszul at a point of its source exactly when the morphism of schemes
  underlying a pointed étale chart square at that point is Koszul at the selected point of the
  chart.

## Implementation notes

The dictionary is assembled from three steps, each of which is already available.

Part (2) of Tag 04RF, `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_exists_open`,
says that the every-pointed-chart condition for the germ property induced by `P` is the
existence of an open subspace of the source through the point on which the morphism has the
every-étale-chart property of `P`. For `P` the Koszul property of morphisms of schemes the
right-hand side is `AlgebraicGeometry.Space.KoszulAt` verbatim.

Tag 04NC, `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart`, evaluates the
every-pointed-chart condition on one chart; the chart is data, so this step needs no hypothesis
on the source or target.

The remaining step compares the induced germ property with the Koszul property of morphisms of
schemes at a point. Both are "the property holds near the point": a representative of the germ
with the property restricts to an open neighbourhood on which `P` holds, and conversely, while
Stacks 069F read through the openness of the Koszul locus (Stacks 06B8) says that a morphism of
schemes is Koszul at a point exactly when it is a local complete intersection morphism on an
open neighbourhood of it.

All three steps need the Koszul property of morphisms of schemes to be local on the source for
the étale topology, which is Stacks 069P restricted to étale coverings. The results of this file
keep it as the hypothesis `hsrc`.

## References

* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 06B8](https://stacks.math.columbia.edu/tag/06B8)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Being Koszul at a point as a property of a neighbourhood -/

/-- **Being Koszul at a point is a condition on a neighbourhood.** A morphism of schemes locally
of finite type is Koszul at a point of its source exactly when it restricts to a local complete
intersection morphism on some open neighbourhood of that point.

The forward direction takes the neighbourhood to be the Koszul locus, which is open by Stacks
06B8, and uses that the Koszul property at a point restricts to an open subscheme. The converse
is the elimination form of Stacks 069F, part (2), followed by the same restriction read
backwards along the open immersion. -/
theorem koszulAt_iff_exists_opens {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) :
    KoszulAt f x ↔ ∃ U : X.Opens, x ∈ U ∧ IsLocalCompleteIntersectionMorphism (U.ι ≫ f) := by
  constructor
  · intro hx
    refine ⟨⟨{z : X | KoszulAt f z}, isOpen_koszulAt f⟩, hx, fun z => ?_⟩
    exact koszulAt_precomp_openImmersion f _ z z.2
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨-, V, hzV, P, i, π, hi, hK, hπ, hfac⟩ := hU ⟨x, hxU⟩
    have : IsImmersion i := hi
    have hio : (U.ι ''ᵁ V).ι = (Scheme.Hom.isoImage U.ι V).inv ≫ (V.ι ≫ U.ι) := by
      rw [← Scheme.Hom.isoImage_hom_ι U.ι V, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType f x, U.ι ''ᵁ V,
      ⟨⟨x, hxU⟩, hzV, rfl⟩, P,
      (Scheme.Hom.isoImage U.ι V).inv ≫ i, π, inferInstance,
      Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isOpenImmersion _)
        hK, hπ, ?_⟩
    rw [hio]
    simp only [Category.assoc]
    rw [hfac]

/-! ### Transport of the Koszul property at a point along isomorphisms -/

/-- Postcomposition with an étale morphism preserves the Koszul property at a point: a
factorization of `f` near the point through a Koszul-regular immersion and a smooth morphism
factorizes `f ≫ i` through the same immersion and the smooth morphism followed by `i`. -/
theorem koszulAt_comp_etale {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (i : Y ⟶ Y') [Etale i] (x : X) (hx : KoszulAt f x) : KoszulAt (f ≫ i) x := by
  obtain ⟨-, U, hxU, P, j, π, hj, hK, hπ, hfac⟩ := hx
  have : IsImmersion j := hj
  have : Smooth π := hπ
  exact ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType (f ≫ i) x, U, hxU, P, j, π ≫ i,
    hj, hK, inferInstance, by rw [← Category.assoc, hfac, Category.assoc]⟩

/-- Being Koszul at a point is insensitive to an isomorphism of the target. -/
theorem koszulAt_comp_iso_iff {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (i : Y ⟶ Y') [IsIso i] (x : X) : KoszulAt (f ≫ i) x ↔ KoszulAt f x := by
  refine ⟨fun h => ?_, fun h => koszulAt_comp_etale f i x h⟩
  have := koszulAt_comp_etale (f ≫ i) (inv i) x h
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this

/-- Being Koszul at a point is insensitive to an isomorphism of the source. -/
theorem koszulAt_iso_comp_iff {X X' Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x' : X') : KoszulAt (e ≫ f) x' ↔ KoszulAt f (e x') := by
  refine ⟨fun h => ?_, fun h => koszulAt_precomp_openImmersion f e x' h⟩
  have hpt : (inv e).base (e.base x') = x' := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have h2 : KoszulAt (e ≫ f) ((inv e).base (e.base x')) := by rw [hpt]; exact h
  have h3 := koszulAt_precomp_openImmersion (e ≫ f) (inv e) (e.base x') h2
  rwa [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h3

/-- If a composite is locally of finite presentation, its first factor is locally of finite
type. -/
private theorem locallyOfFiniteType_of_comp_of_locallyOfFinitePresentation {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (p : Y ⟶ Z) [LocallyOfFinitePresentation (a ≫ p)] : LocallyOfFiniteType a :=
  locallyOfFiniteType_of_comp a p

/-- **Formation of the Koszul locus commutes with base change, for an arbitrary cartesian
square.** This is Tag 06B8 transported from Mathlib's chosen pullback: in a cartesian square of
schemes over a base `W` along `g : W' ⟶ W`, with the sources of `a` and its base change both
flat and locally of finite presentation over their bases, the base change of `a` is Koszul at a
point exactly when `a` is Koszul at its image. -/
theorem koszulAt_iff_of_isPullback {U V U' V' W W' : Scheme.{u}}
    (a : U ⟶ V) (pU : U ⟶ W) (pV : V ⟶ W) (hcomm : a ≫ pV = pU)
    [Flat pU] [Flat pV] [LocallyOfFinitePresentation pU] [LocallyOfFinitePresentation pV]
    (g : W' ⟶ W) (a' : U' ⟶ V') {rU : U' ⟶ U} {rV : V' ⟶ V} {pU' : U' ⟶ W'} {pV' : V' ⟶ W'}
    (sqU : IsPullback rU pU' pU g) (sqV : IsPullback rV pV' pV g)
    (hcU : a' ≫ rV = rU ≫ a) (hcV : a' ≫ pV' = pU') (x' : U') :
    KoszulAt a' x' ↔ KoszulAt a (rU.base x') := by
  have hlftA : LocallyOfFiniteType a := by
    have : LocallyOfFinitePresentation (a ≫ pV) := by rw [hcomm]; infer_instance
    exact locallyOfFiniteType_of_comp_of_locallyOfFinitePresentation a pV
  have _ : Flat pU' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat.{u}) sqU inferInstance
  have _ : Flat pV' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat.{u}) sqV inferInstance
  have _ : LocallyOfFinitePresentation pU' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFinitePresentation.{u}) sqU inferInstance
  have _ : LocallyOfFinitePresentation pV' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFinitePresentation.{u}) sqV inferInstance
  have hlftA' : LocallyOfFiniteType a' := by
    have : LocallyOfFinitePresentation (a' ≫ pV') := by rw [hcV]; infer_instance
    exact locallyOfFiniteType_of_comp_of_locallyOfFinitePresentation a' pV'
  set m : (Limits.pullback pU g : Scheme.{u}) ⟶ (Limits.pullback pV g : Scheme.{u}) :=
    Limits.pullback.map pU g pV g a (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hcomm.symm) (by simp) with hm
  have hmlft : LocallyOfFiniteType m := by
    have hms : m ≫ Limits.pullback.snd pV g = Limits.pullback.snd pU g := by
      rw [hm, Limits.pullback.lift_snd, Category.comp_id]
    have : LocallyOfFinitePresentation (m ≫ Limits.pullback.snd pV g) := by
      rw [hms]; infer_instance
    exact locallyOfFiniteType_of_comp_of_locallyOfFinitePresentation m (Limits.pullback.snd pV g)
  have hUa : sqU.isoPullback.hom ≫ Limits.pullback.fst pU g = rU := sqU.isoPullback_hom_fst
  have hUb : sqU.isoPullback.hom ≫ Limits.pullback.snd pU g = pU' := sqU.isoPullback_hom_snd
  have hVa : sqV.isoPullback.hom ≫ Limits.pullback.fst pV g = rV := sqV.isoPullback_hom_fst
  have hVb : sqV.isoPullback.hom ≫ Limits.pullback.snd pV g = pV' := sqV.isoPullback_hom_snd
  have hsq : a' ≫ sqV.isoPullback.hom = sqU.isoPullback.hom ≫ m := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hVa, hcU, Category.assoc]
      simp only [hm, Limits.pullback.lift_fst, ← Category.assoc, hUa]
    · rw [Category.assoc, hVb, hcV, Category.assoc]
      simp only [hm, Limits.pullback.lift_snd, Category.comp_id, hUb]
  have ha' : a' = sqU.isoPullback.hom ≫ m ≫ sqV.isoPullback.inv := by
    rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [ha', koszulAt_iso_comp_iff, koszulAt_comp_iso_iff, koszulAt_baseChange_iff a pU pV hcomm g,
    ← Scheme.Hom.comp_apply, hUa]

namespace MorphismOfGerms

/-- **The induced germ property is a property of a neighbourhood.** For a property `P` of
morphisms of schemes which is étale local on the source and target, the germ property induced by
`P` holds for the germ of `g` at `x` exactly when `P` holds on some open neighbourhood of `x`.

A representative of the germ with `P` agrees with `g` on an open neighbourhood of `x`, and `P` is
preserved by precomposition with the open immersion of that neighbourhood; conversely such a
neighbourhood is itself a representative with `P`. -/
theorem hasRepresentativeWithProperty_ofSchemeHom_iff (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (x : X) :
    HasRepresentativeWithProperty P (ofSchemeHom g x) ↔
      ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ g) := by
  have htop : ∀ U : X.Opens, X.homOfLE (le_top (a := U)) ≫ X.topIso.hom ≫ g = U.ι ≫ g := by
    intro U
    rw [← Category.assoc, show X.homOfLE (le_top (a := U)) ≫ X.topIso.hom = U.ι by simp]
  constructor
  · rintro ⟨r, hr, hPr⟩
    obtain ⟨U, hxU, hUr, hUtop, heq⟩ := mk_eq_mk_iff.mp hr
    refine ⟨U, hxU, ?_⟩
    have hPU : P (X.homOfLE hUr ≫ r.hom) :=
      hP.precomp.precomp (X.homOfLE hUr) inferInstance _ hPr
    rw [heq] at hPU
    rwa [show X.homOfLE hUtop = X.homOfLE (le_top (a := U)) from rfl, htop U] at hPU
  · rintro ⟨U, hxU, hPU⟩
    refine ⟨{ source := U
              mem_source := hxU
              hom := U.ι ≫ g
              map_point := rfl }, mk_eq_mk_iff.mpr ⟨U, hxU, le_rfl, le_top, ?_⟩, hPU⟩
    change X.homOfLE (le_refl U) ≫ U.ι ≫ g = X.homOfLE (le_top (a := U)) ≫ X.topIso.hom ≫ g
    rw [htop U, show X.homOfLE (le_refl U) = 𝟙 _ by simp, Category.id_comp]

end MorphismOfGerms

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being Koszul at a point of the source of a morphism of algebraic spaces over `S` is the
pointed-chart condition of Tag 04NC for the germ property induced by the Koszul property of
morphisms of schemes.

The two sides are the same existential statement, read with the point condition written as
membership in a range or as a witness: part (2) of Tag 04RF turns the pointed-chart condition
into an open subspace of the source through the point on which the morphism is a local complete
intersection morphism, which is `AlgebraicGeometry.Space.KoszulAt`. -/
theorem koszulAt_iff_holdsOnEveryEtaleChartAtPoint
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    KoszulAt B S hS f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (MorphismOfGerms.HasRepresentativeWithProperty
          (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
            MorphismProperty Scheme.{u})) f x := by
  rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u})
    (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism hsrc) hX hY f x]
  constructor
  · rintro ⟨U, hU, y, hy, hlci⟩
    exact ⟨U, hU, ⟨y, hy⟩, hlci⟩
  · rintro ⟨U, hU, ⟨y, hy⟩, hlci⟩
    exact ⟨U, hU, y, hy, hlci⟩

/-- **The Koszul locus read on a chart.** A morphism of algebraic spaces over `S` is Koszul at a
point of its source exactly when the morphism of schemes underlying a pointed étale chart square
at that point is Koszul at the selected point of the chart.

This is the dictionary the base-change half of Tag 06CA is proved through: it turns the
space-level condition into the scheme-level one, where Tag 06B8 applies. The chart is data, so
only one chart has to be produced; part (2) of Tag 04RF supplies the open subspace of the source
and Tag 04NC the independence of the chart. -/
theorem koszulAt_iff_koszulAt_chart
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (c : EtaleChartAtPoint B S hS f x)
    (hlft : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map c.h)) :
    KoszulAt B S hS f x ↔
      _root_.AlgebraicGeometry.KoszulAt ((BigFppfOver.toScheme B S hS).map c.h)
        (c.sourcePoint B S hS) := by
  have hP := isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism hsrc
  rw [koszulAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hsrc hX hY f x,
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
      (MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _ hP) f x c,
    MorphismOfGerms.hasRepresentativeWithProperty_ofSchemeHom_iff _ hP,
    _root_.AlgebraicGeometry.koszulAt_iff_exists_opens]

end Space

end AlgebraicGeometry

end
