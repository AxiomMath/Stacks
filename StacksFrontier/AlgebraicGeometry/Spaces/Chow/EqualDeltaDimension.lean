module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre

/-!
# Equal δ-dimension forces a proper closed image or a finite extension of function fields

Over the fixed base of the theory of cycles let `X` and `Y` be good integral algebraic spaces
of the same δ-dimension and let `f : X ⟶ Y` be a morphism over the base. Either the image of
`|X|` is not dense in `|Y|`, in which case `f` factors through the integral closed subspace of
`Y` on the closure of that image, a closed subspace whose set of points is strictly smaller
than `|Y|`; or `f` is dominant, and then the extension of function fields `R(X)/R(Y)` it
induces is finite.

## Main results

* **Stacks 0ENY**, the alternative, is the theorem named
  `factorsThrough_properIntegralClosedSubspace_or_isDominant_and_finite_functionField`
  in the namespace `AlgebraicGeometry.Space`.
* `AlgebraicGeometry.Space.finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero`:
  **Stacks 0AD5**, that condition (1) implies condition (2) — for a dominant morphism locally
  of finite type of integral algebraic spaces, vanishing of the relative transcendence degree
  at the generic point makes the induced extension of residue fields there finite.
* `AlgebraicGeometry.Space.exists_bijective_residueFieldHom_of_mono`: a monomorphic
  field-valued representative of a point of a decent algebraic space has, for its field, the
  residue field at that point, through a bijective homomorphism sitting in the square over the
  space.
* `AlgebraicGeometry.Space.finite_residueFieldHom_of_hasTranscendenceDegreeAt_zero`: a
  morphism locally of finite type between decent algebraic spaces which is read on a pair of
  *open* charts at a point, and whose relative transcendence degree there is zero, induces a
  finite extension of residue fields at that point.
* `AlgebraicGeometry.Space.exists_openImmersion_chart_of_mem_range`: the pair of open charts
  the previous result consumes exists at the generic point of an integral algebraic space,
  as soon as the image of that point lies in a representable open subspace of the target.
* `AlgebraicGeometry.Space.pointsMap_genericPoint_of_isDominant`: a dominant morphism of
  integral algebraic spaces carries the generic point to the generic point.
* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint` and
  `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_genericPoint_eq_zero`: the δ-dimension of a
  good integral space is the induced dimension function at its generic point, and equality of
  the two δ-dimensions forces the relative transcendence degree at the generic point to vanish.

## Implementation notes

The function field `R(X)` of an integral algebraic space is its residue field at the generic
point: that identification is Stacks 0END, `AlgebraicGeometry.Space.rationalFunctionsRingEquiv`,
and the extension `R(X)/R(Y)` is accordingly the one induced on residue fields by `f`, namely
`AlgebraicGeometry.Space.residueFieldHom`. Finiteness is `Module.Finite` for the algebra
structure that homomorphism defines, which is `RingHom.Finite` of it.

The δ-dimension of the whole space is `AlgebraicGeometry.Space.deltaDimensionClosed` at the
closed subset `Set.univ`; on an integral space that is the induced dimension function at the
generic point, by `AlgebraicGeometry.Space.deltaDimensionClosed_eq_deltaDimensionIrreducible`
and `AlgebraicGeometry.Space.deltaDimensionIrreducible_eq_of_isGenericPoint`.

Being *dominant* is `AlgebraicGeometry.Space.IsDominant`, density of the range of the map on
points. The source's "proper closed subspace of `Y`" is produced here as the integral closed
subspace on the closure of the image of `|X|`, and properness is recorded in the strong form
that its *set of points* is not all of `|Y|`, which also gives that the subfunctor is not the
whole of `Y`.

The finiteness of the function field extension is the content of Spaces over Fields,
Lemma 0AD5, at the generic point; the library has no other statement of that tag, so the
implication from condition (1) to condition (2) is proved here and carries the tag. The route
is to read both residue fields on schemes. An open subspace
of an algebraic space is a monomorphism, so the residue field of a representable open chart at
a point over `x` is a monomorphic field-valued representative of `x`, hence the residue field
of the space at `x` by the uniqueness clause of Stacks 0EMW. A representable open chart of `X`
whose image lands inside a given representable open chart of `Y` exists at the generic point
by Stacks 086U — every dense open subspace of an integral space contains a representable one —
together with Stacks 03IE for the factorization. On that pair of charts the morphism becomes a
morphism of schemes locally of finite type, so the residue field extension is essentially of
finite type; vanishing of the transcendence degree makes it algebraic, and an algebraic
extension essentially of finite type is finite.

The vanishing of the relative transcendence degree at the generic point is the dimension
bookkeeping of Situation 0EDT: the induced dimension function of Stacks 0EDN at the generic
point of `X` is `δ` at the image in the base plus the transcendence degree over the base, the
same holds on `Y`, and the transcendence degree over the base is additive along `X ⟶ Y ⟶ B` by
Stacks 04NR. Equality of the two δ-dimensions therefore forces the relative degree of `f` to
be zero.

## References

* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENY](https://stacks.math.columbia.edu/tag/0ENY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Two composites in `C` agree when their Yoneda images, followed by a monomorphism, fit in
squares over a common morphism of presheaves. -/
theorem comp_eq_comp_of_yoneda_squares.{v, w} {C : Type w} [Category.{v} C] {P Q R T U V : C}
    {F G : Cᵒᵖ ⥤ Type v} (gX : P ⟶ R) (g₀ : R ⟶ T) (gh : P ⟶ Q) (gY : Q ⟶ T) (s : P ⟶ U)
    (t : Q ⟶ V) (k : U ⟶ V) (mX : yoneda.obj R ⟶ F) (mY : yoneda.obj T ⟶ G) [Mono mY]
    (α : yoneda.obj U ⟶ F) (β : yoneda.obj V ⟶ G) (f : F ⟶ G)
    (hX : yoneda.map gX ≫ mX = yoneda.map s ≫ α) (hY : yoneda.map gY ≫ mY = yoneda.map t ≫ β)
    (h₀ : yoneda.map g₀ ≫ mY = mX ≫ f) (hk : gh ≫ t = s ≫ k)
    (hc : yoneda.map k ≫ β = α ≫ f) :
    gX ≫ g₀ = gh ≫ gY :=
  yoneda.map_injective <| (cancel_mono mY).1 <| by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₀, hY,
      reassoc_of% hX, ← Functor.map_comp_assoc, hk, Functor.map_comp, Category.assoc, hc]

/-- A ring homomorphism is finite if, after composing with a bijection on the target, it agrees
with a finite homomorphism precomposed with a surjection on the source. -/
theorem _root_.RingHom.Finite.of_comp_eq_of_bijective_of_surjective {R T R' T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T'] {f : R →+* T} {φ : T →+* T'}
    {φ' : R →+* R'} {ψ : R' →+* T'} (hφ : Function.Bijective φ) (hφ' : Function.Surjective φ')
    (hψ : ψ.Finite) (h : ∀ a, φ (f a) = ψ (φ' a)) : f.Finite := by
  let e : T ≃+* T' := RingEquiv.ofBijective φ hφ
  have hf : f = e.symm.toRingHom.comp (ψ.comp φ') :=
    RingHom.ext fun a ↦ (e.symm_apply_apply (f a)).symm.trans (congrArg e.symm (h a))
  rw [hf]
  exact (RingEquiv.finite e.symm).comp (hψ.comp (RingHom.Finite.of_surjective φ' hφ'))

/-- A morphism of schemes locally of finite type whose residue field extension at a point has
transcendence degree zero induces a finite extension of residue fields there. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.finite_residueFieldMap_of_trdeg_eq_zero
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [LocallyOfFiniteType φ] (x : X)
    (h : letI := (φ.residueFieldMap x).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg (Y.residueField (φ x)) (X.residueField x)) = 0) :
    (φ.residueFieldMap x).hom.Finite := by
  let _ : Algebra (Y.residueField (φ x)) (X.residueField x) :=
    (φ.residueFieldMap x).hom.toAlgebra
  have := residueField_essFiniteType_of_locallyOfFiniteType φ x
  have : Algebra.IsAlgebraic (Y.residueField (φ x)) (X.residueField x) :=
    trdeg_eq_zero_iff.mp (Cardinal.toENat_eq_zero.mp h)
  have : Module.Finite (Y.residueField (φ x)) (X.residueField x) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact this

section Bridge

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EMW at an arbitrary monomorphic representative.** The field of a monomorphic
field-valued representative of a point of a decent algebraic space is the residue field there,
through a bijective homomorphism whose spectrum is a morphism of the site fitting in the square
over the space.

The chosen representative and the given one are uniquely isomorphic over the space, and an
isomorphism of field spectra is the spectrum of a bijective ring homomorphism. -/
theorem exists_bijective_residueFieldHom_of_mono (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (x : points B S hS X) (q : FieldValuedPoint B S hS X)
    (hq : q.class B S hS X = x) (hmono : Mono (fieldMorphism B S hS X q)) :
    ∃ (φ : residueField B S hS X hXdec x →+* q.carrier)
      (g : q.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS X hXdec x).1.siteObject B S hS X),
      Function.Bijective φ ∧
        B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
          yoneda.map g ≫ residueFieldMorphism B S hS X hXdec x = fieldMorphism B S hS X q := by
  classical
  obtain ⟨e, he, -⟩ := residueFieldRepresentative_unique B S hS X hX hXdec x q hq hmono
  set g := yoneda.preimage e.inv with hgDef
  have hg : yoneda.map g = e.inv := yoneda.map_preimage _
  have hgIsoMap : IsIso (yoneda.map g) := by rw [hg]; infer_instance
  have hgIso : IsIso g := isIso_of_fully_faithful yoneda g
  set φ := ((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom with hφDef
  have hspec : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφDef]; simp
  have hleftIso : IsIso (B.inclusion.map g.left) := by
    show IsIso ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  have hφiso : IsIso (Spec.map (CommRingCat.ofHom φ)) := by rw [← hspec]; infer_instance
  have hSpecIso : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := hφiso
  have hopIso : IsIso (CommRingCat.ofHom φ).op := Spec.fullyFaithful.isIso_of_isIso_map _
  have hofIso : IsIso (CommRingCat.ofHom φ) := isIso_of_op _
  refine ⟨φ, g, ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom φ), hspec, ?_⟩
  rw [hg, ← he, Iso.inv_hom_id_assoc]

/-- The point of a represented presheaf carried by the canonical representative of a point of
the representing scheme is the one lying over that point. -/
private theorem pointsToScheme_class_schemePointRepresentative (U : BigFppfOver B S hS)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    pointsToScheme B S hS U
        ((schemePointRepresentative B S hS U u).class B S hS (yoneda.obj U)) = u :=
  schemePointRepresentative_point B S hS U u

/-- The class of the canonical representative above a point of a chart, pushed along a
morphism of charts, is the class of the canonical representative above the image point. -/
theorem pointsMap_yoneda_map_schemePointRepresentative_class {CX CY : BigFppfOver B S hS}
    (h : CX ⟶ CY) (u : (BigFppfOver.toScheme B S hS).obj CX) :
    pointsMap B S hS (yoneda.obj CX) (yoneda.map h)
        ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) =
      (schemePointRepresentative B S hS CY ((BigFppfOver.toScheme B S hS).map h u)).class
        B S hS (yoneda.obj CY) := by
  refine injective_pointsToScheme B S hS CY ?_
  rw [pointsToScheme_pointsMap, pointsToScheme_class_schemePointRepresentative B S hS CX u,
    pointsToScheme_class_schemePointRepresentative B S hS CY]

/-- The canonical representative above a point of an open chart, pushed into the space,
presents it by a monomorphism. -/
theorem mono_fieldMorphism_map_schemePointRepresentative {CX : BigFppfOver B S hS}
    (α : yoneda.obj CX ⟶ X) (hα : IsOpenImmersion B S hS α)
    (u : (BigFppfOver.toScheme B S hS).obj CX) :
    Mono (fieldMorphism B S hS X
      (FieldValuedPoint.map B S hS (yoneda.obj CX) α (schemePointRepresentative B S hS CX u))) := by
  rw [fieldMorphism_map_yoneda,
    ← fieldMorphism_yoneda B S hS (schemePointRepresentative B S hS CX u)]
  exact mono_comp' (mono_fieldMorphism_schemePointRepresentative B S hS CX u)
    (mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hα))

/-- A morphism of the site between the canonical representatives above `u` and above its image
under a morphism of charts `h` is the spectrum of the residue field map of `h` at `u`. -/
theorem inclusion_map_left_eq_spec_residueFieldMap {CX CY : BigFppfOver B S hS} (h : CX ⟶ CY)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (gh : (schemePointRepresentative B S hS CX u).siteObject B S hS (yoneda.obj CX) ⟶
      (schemePointRepresentative B S hS CY ((BigFppfOver.toScheme B S hS).map h u)).siteObject
        B S hS (yoneda.obj CY))
    (hgh : gh ≫ (schemePointRepresentative B S hS CY
        ((BigFppfOver.toScheme B S hS).map h u)).siteHom =
      (schemePointRepresentative B S hS CX u).siteHom ≫ h) :
    B.inclusion.map gh.left =
      Spec.map (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u) := by
  have k1 : (BigFppfOver.toScheme B S hS).map gh ≫ (BigFppfOver.toScheme B S hS).map
        (schemePointRepresentative B S hS CY ((BigFppfOver.toScheme B S hS).map h u)).siteHom =
      (BigFppfOver.toScheme B S hS).map (schemePointRepresentative B S hS CX u).siteHom ≫
        (BigFppfOver.toScheme B S hS).map h := by
    rw [← Functor.map_comp, hgh, Functor.map_comp]
  have hcan : (BigFppfOver.toScheme B S hS).map gh ≫
        ((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField
          ((BigFppfOver.toScheme B S hS).map h u) =
      ((BigFppfOver.toScheme B S hS).obj CX).fromSpecResidueField u ≫
        (BigFppfOver.toScheme B S hS).map h := by
    rw [← toScheme_map_siteHom_schemePointRepresentative B S hS CY,
      ← toScheme_map_siteHom_schemePointRepresentative B S hS CX u]
    exact k1
  show (BigFppfOver.toScheme B S hS).map gh = _
  exact (cancel_mono (((BigFppfOver.toScheme B S hS).obj CY).fromSpecResidueField
    ((BigFppfOver.toScheme B S hS).map h u))).1
    (hcan.trans (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ u).symm)

/-- Let `f : X ⟶ Y` be a morphism of decent algebraic spaces read on a pair of representable
*open* charts at a point `x` through a morphism `h` of the site, and let `u` be a point of the
source chart over `x`. If the residue field map of `h` at `u` is finite, so is the extension of
residue fields `f` induces at `x`.

Both chart residue fields are the residue fields of the two spaces, because an open immersion
is a monomorphism, so the residue-field point of a chart is a monomorphic field-valued
representative of the point below. -/
theorem finite_residueFieldHom_of_finite_residueFieldMap
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (hu : pointsMap B S hS (yoneda.obj CX) α
      ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) = x)
    (hψ : (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom.Finite) :
    (residueFieldHom B S hS X Y hY hXdec hYdec f x).Finite := by
  set v := (BigFppfOver.toScheme B S hS).map h u
  set qu := schemePointRepresentative B S hS CX u
  set qv := schemePointRepresentative B S hS CY v
  have hvclass := pointsMap_yoneda_map_schemePointRepresentative_class B S hS h u
  have hqYclass : (FieldValuedPoint.map B S hS (yoneda.obj CY) β qv).class B S hS Y =
      pointsMap B S hS X f x := by
    have h1 : pointsMap B S hS X f x =
        pointsMap B S hS (yoneda.obj CX) (α ≫ f) (qu.class B S hS (yoneda.obj CX)) := by
      rw [pointsMap_comp, Function.comp_apply, hu]
    rw [h1, ← hcomm, pointsMap_comp, Function.comp_apply, hvclass]
    rfl
  obtain ⟨φX, gX, hφXbij, hgXspec, hgXsq⟩ := exists_bijective_residueFieldHom_of_mono B S hS hX
    hXdec x _ hu (mono_fieldMorphism_map_schemePointRepresentative B S hS α hα u)
  obtain ⟨φY, gY, hφYbij, hgYspec, hgYsq⟩ := exists_bijective_residueFieldHom_of_mono B S hS hY
    hYdec _ _ hqYclass (mono_fieldMorphism_map_schemePointRepresentative B S hS β hβ v)
  rw [fieldMorphism_map_yoneda] at hgXsq hgYsq
  have : Mono (yonedaEquiv.symm qv.value) :=
    mono_fieldMorphism_schemePointRepresentative B S hS CY v
  obtain ⟨gh, hgh, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS
    (yoneda.obj CY) (isAlgebraicSpace_yoneda B S hS CY) qv
    (FieldValuedPoint.map B S hS (yoneda.obj CX) (yoneda.map h) qu) hvclass.symm
  have hghsq : gh ≫ qv.siteHom = qu.siteHom ≫ h := hgh
  obtain ⟨g₀, hg₀spec, hg₀sq⟩ :
      ∃ g : _, _ ∧ _ := residueFieldHom_spec B S hS X Y hY hXdec hYdec f x
  have : Mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) :=
    (residueFieldRepresentative B S hS Y hYdec (pointsMap B S hS X f x)).2.2
  have hm := comp_eq_comp_of_yoneda_squares gX g₀ gh gY qu.siteHom qv.siteHom h _ _ α β f
    hgXsq hgYsq hg₀sq hghsq hcomm
  have hA : B.inclusion.map gX.left ≫ B.inclusion.map g₀.left =
      B.inclusion.map gh.left ≫ B.inclusion.map gY.left :=
    ((B.inclusion.map_comp gX.left g₀.left).symm.trans
      (congrArg (fun k ↦ B.inclusion.map k.left) hm)).trans
      (B.inclusion.map_comp gh.left gY.left)
  have eL : Spec.map (CommRingCat.ofHom φX) ≫
      Spec.map (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)) =
      B.inclusion.map gX.left ≫ B.inclusion.map g₀.left := by
    rw [hgXspec, hg₀spec]
  have eR : Spec.map (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u) ≫
      Spec.map (CommRingCat.ofHom φY) = B.inclusion.map gh.left ≫ B.inclusion.map gY.left :=
    (congrArg (fun k ↦ Spec.map
        (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u) ≫ k) hgYspec.symm).trans
      (congrArg (fun k ↦ k ≫ B.inclusion.map gY.left)
        (inclusion_map_left_eq_spec_residueFieldMap B S hS h u gh hghsq).symm)
  have h0 : CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x) ≫
      CommRingCat.ofHom φX =
      CommRingCat.ofHom φY ≫ ((BigFppfOver.toScheme B S hS).map h).residueFieldMap u :=
    Spec.map_injective ((Spec.map_comp _ _).trans
      (((eL.trans hA).trans eR.symm).trans (Spec.map_comp _ _).symm))
  exact RingHom.Finite.of_comp_eq_of_bijective_of_surjective hφXbij hφYbij.2 hψ
    fun a ↦ RingHom.congr_fun (congrArg CommRingCat.Hom.hom h0) a

/-- **Spaces over Fields, Lemma 0AD5, conditions (1) and (2), at a point with open charts.**
Let `f : X ⟶ Y` be a morphism of decent algebraic spaces over `S` which is locally of finite
type, let `α` and `β` be representable *open* charts of `X` and `Y` through which `f` is
induced by a morphism `h` of the site, and let `u` be a point of the source chart lying over
`x`. If the relative transcendence degree of `f` at `x` vanishes, then the extension of
residue fields `f` induces at `x` is finite.

On the charts the morphism becomes a morphism of schemes locally of finite type, so the
extension of residue fields at `u` is essentially of finite type; vanishing of the
transcendence degree makes it algebraic, and an algebraic extension essentially of finite type
is finite. Both chart residue fields are the residue fields of the two spaces, because an open
immersion is a monomorphism, so the residue-field point of a chart is a monomorphic
field-valued representative of the point below. -/
theorem finite_residueFieldHom_of_hasTranscendenceDegreeAt_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X)
    (CX CY : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (β : yoneda.obj CY ⟶ Y)
    (hα : IsOpenImmersion B S hS α) (hβ : IsOpenImmersion B S hS β) (h : CX ⟶ CY)
    (hcomm : yoneda.map h ≫ β = α ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj CX)
    (hu : pointsMap B S hS (yoneda.obj CX) α
      ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) = x)
    (htr : HasTranscendenceDegreeAt B S hS f x 0) :
    (residueFieldHom B S hS X Y hY hXdec hYdec f x).Finite := by
  have haEt := presheaf_etale_of_isOpenImmersion B S hS hα
  have hbEt := presheaf_etale_of_isOpenImmersion B S hS hβ
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hf CX CY α β h haEt hbEt hcomm
  let c : EtaleChartAtPoint B S hS f x :=
    { U := CX
      V := CY
      a := α
      b := β
      h := h
      a_etale := haEt
      b_etale := hbEt
      comm := hcomm
      representative := schemePointRepresentative B S hS CX u
      point := IsLocalRing.closedPoint (schemePointRepresentative B S hS CX u).carrier
      maps_to := hu }
  have hc := htr c
  rw [show c.sourcePoint B S hS = u from schemePointRepresentative_point B S hS CX u] at hc
  exact finite_residueFieldHom_of_finite_residueFieldMap B S hS hX hY hXdec hYdec f x CX CY α β
    hα hβ h hcomm u hu (Scheme.Hom.finite_residueFieldMap_of_trdeg_eq_zero _ u
      ((MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff _ u 0).mp hc))

/-- Under a dominant morphism of integral algebraic spaces the generic point of the source
goes to the generic point of the target.

The image of the point space of the source lies in the closure of the image of the generic
point, and is dense by dominance, so that closure is everything; the point space of a decent
algebraic space is Kolmogorov, so there is only one such point. -/
theorem pointsMap_genericPoint_of_isDominant (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXInt : IsIntegralSpace B S hS X)
    (hYInt : IsIntegralSpace B S hS Y) (f : X ⟶ Y) (hdom : IsDominant B S hS f) :
    pointsMap B S hS X f (genericPoint B S hS hX hXInt) = genericPoint B S hS hY hYInt := by
  have ht0 : T0Space (points B S hS Y) :=
    t0Space_points_of_isDecentSpace B S hS hY hYInt.2.1
  have hgen : IsGenericPoint (pointsMap B S hS X f (genericPoint B S hS hX hXInt))
      (Set.univ : Set (points B S hS Y)) := by
    have h2 : pointsMap B S hS X f '' closure {genericPoint B S hS hX hXInt} ⊆
        closure (pointsMap B S hS X f '' {genericPoint B S hS hX hXInt}) :=
      image_closure_subset_closure_image (continuous_pointsMap B S hS f)
    rw [isGenericPoint_genericPoint B S hS hX hXInt, Set.image_univ,
      Set.image_singleton] at h2
    have h3 : closure (Set.range (pointsMap B S hS X f)) ⊆
        closure {pointsMap B S hS X f (genericPoint B S hS hX hXInt)} :=
      closure_minimal h2 isClosed_closure
    rw [hdom.closure_range] at h3
    exact Set.eq_univ_of_univ_subset h3
  exact hgen.eq (isGenericPoint_genericPoint B S hS hY hYInt)

/-- A representable open chart of an integral algebraic space `X` through its generic point
whose image under `f` lands inside a given representable open chart of `Y`, together with the
induced morphism of the site and the point of the chart above the generic point.

The preimage of the point set of the chart of `Y` is an open set of points of `X` containing
the generic point, hence dense; by Stacks 086U the open subspace it cuts out contains a
representable dense open subspace, which is the required chart, and the composite morphism
factors through the chart of `Y` by Stacks 03IE. -/
theorem exists_openImmersion_chart_of_mem_range (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXInt : IsIntegralSpace B S hS X) (f : X ⟶ Y)
    (CY : BigFppfOver B S hS) (β : yoneda.obj CY ⟶ Y) (hβ : IsOpenImmersion B S hS β)
    (hmem : pointsMap B S hS X f (genericPoint B S hS hX hXInt) ∈
      Set.range (pointsMap B S hS (yoneda.obj CY) β)) :
    ∃ (CX : BigFppfOver B S hS) (α : yoneda.obj CX ⟶ X) (h : CX ⟶ CY)
      (u : (BigFppfOver.toScheme B S hS).obj CX),
      IsOpenImmersion B S hS α ∧ yoneda.map h ≫ β = α ≫ f ∧
        pointsMap B S hS (yoneda.obj CX) α
            ((schemePointRepresentative B S hS CX u).class B S hS (yoneda.obj CX)) =
          genericPoint B S hS hX hXInt := by
  classical
  have hWopen : IsOpen (pointsMap B S hS X f ⁻¹'
      Set.range (pointsMap B S hS (yoneda.obj CY) β)) :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS β hβ).preimage
      (continuous_pointsMap B S hS f)
  have hWdense : IsDenseOpenSubspace B S hS hX (openSubspaceOfPoints B S hS X
      (pointsMap B S hS X f ⁻¹' Set.range (pointsMap B S hS (yoneda.obj CY) β))) := by
    refine ⟨isOpenSubspace_openSubspaceOfPoints B S hS hX _ hWopen, ?_⟩
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact dense_of_genericPoint_mem B S hS hX hXInt hmem
  obtain ⟨H, hHdense, hHle, hHrep⟩ :=
    exists_isDenseOpenSubspace_isRepresentable_le B S hS hX hXInt hWdense
  have hrep : H.toFunctor.IsRepresentable := hHrep
  have hαopen : IsOpenImmersion B S hS (H.toFunctor.reprW.hom ≫ H.ι) :=
    MorphismProperty.RespectsIso.precomp _ H.toFunctor.reprW.hom H.ι hHdense.1.2
  obtain ⟨y, hy⟩ := genericPoint_mem_range_pointsMap_ι B S hS hX hXInt hHdense
  have hgenmem : genericPoint B S hS hX hXInt ∈
      Set.range (pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
        (H.toFunctor.reprW.hom ≫ H.ι)) := by
    refine ⟨pointsMap B S hS H.toFunctor H.toFunctor.reprW.inv y, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS _ _), ← pointsMap_comp,
      Iso.inv_hom_id_assoc]
    exact hy
  have hsub : Set.range (pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
      ((H.toFunctor.reprW.hom ≫ H.ι) ≫ f)) ⊆
      Set.range (pointsMap B S hS (yoneda.obj CY) β) := by
    rintro z ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    have hmemW : pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
        (H.toFunctor.reprW.hom ≫ H.ι) w ∈
        Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS X
          (pointsMap B S hS X f ⁻¹' Set.range (pointsMap B S hS (yoneda.obj CY) β))).toFunctor
          (openSubspaceOfPoints B S hS X
            (pointsMap B S hS X f ⁻¹'
              Set.range (pointsMap B S hS (yoneda.obj CY) β))).ι) := by
      refine ⟨pointsMap B S hS (yoneda.obj H.toFunctor.reprX)
        (H.toFunctor.reprW.hom ≫ Subfunctor.homOfLe hHle) w, ?_⟩
      rw [← Function.comp_apply (f := pointsMap B S hS _ _), ← pointsMap_comp,
        Category.assoc, Subfunctor.homOfLe_ι]
    rwa [range_pointsMap_ι_openSubspaceOfPoints] at hmemW
  obtain ⟨k, hk⟩ := exists_factor_through_chart B S hS hY
    (isAlgebraicSpace_yoneda B S hS H.toFunctor.reprX) CY β hβ
    ((H.toFunctor.reprW.hom ≫ H.ι) ≫ f) hsub
  obtain ⟨p, hp⟩ := hgenmem
  refine ⟨H.toFunctor.reprX, H.toFunctor.reprW.hom ≫ H.ι, yoneda.preimage k,
    pointsToScheme B S hS H.toFunctor.reprX p, hαopen, ?_, ?_⟩
  · rw [yoneda.map_preimage]
    exact hk
  · rw [class_schemePointRepresentative_pointsToScheme B S hS H.toFunctor.reprX p]
    exact hp

/-- **Spaces over Fields, Lemma 0AD5, (1) implies (2).** Let `f : X ⟶ Y` be a dominant
morphism of integral algebraic spaces over `S` which is locally of finite type. If the
transcendence degree of the generic point of `X` over the generic point of `Y` is zero, then
the induced extension of residue fields at the generic point is finite.

Both residue fields are read on a pair of representable open charts through the generic point,
which exist by Stacks 086U and Stacks 03IE. -/
@[stacks 0AD5 "condition (1) implies condition (2): finiteness of the residue field extension \
  at the generic point, from vanishing of the relative transcendence degree there"]
theorem finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXInt : IsIntegralSpace B S hS X) (hYInt : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) (hdom : IsDominant B S hS f)
    (htr : HasTranscendenceDegreeAt B S hS f (genericPoint B S hS hX hXInt) 0) :
    letI := (residueFieldHom B S hS X Y hY hXInt.2.1 hYInt.2.1 f
      (genericPoint B S hS hX hXInt)).toAlgebra
    Module.Finite
      (residueField B S hS Y hYInt.2.1
        (pointsMap B S hS X f (genericPoint B S hS hX hXInt)))
      (residueField B S hS X hXInt.2.1 (genericPoint B S hS hX hXInt)) := by
  obtain ⟨CY, β, hβ, hmemY⟩ := exists_chart B S hS hY hYInt
  have hmem : pointsMap B S hS X f (genericPoint B S hS hX hXInt) ∈
      Set.range (pointsMap B S hS (yoneda.obj CY) β) := by
    rw [pointsMap_genericPoint_of_isDominant B S hS hX hY hXInt hYInt f hdom]
    exact hmemY
  obtain ⟨CX, α, h, u, hα, hcomm, hu⟩ :=
    exists_openImmersion_chart_of_mem_range B S hS hX hY hXInt f CY β hβ hmem
  exact finite_residueFieldHom_of_hasTranscendenceDegreeAt_zero B S hS hX hY hXInt.2.1
    hYInt.2.1 f hf (genericPoint B S hS hX hXInt) CX CY α β hα hβ h hcomm u hu htr

end Bridge

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EDX for the whole of an integral good space.** The δ-dimension of a good
integral algebraic space over the fixed base is the induced dimension function at its generic
point: the whole point space is irreducible and closed, and the generic point is its generic
point. -/
theorem deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint (pX : X ⟶ D.space)
    (hX : D.IsGood pX) (hXInt : IsIntegralSpace D.site D.base D.base_mem X) :
    deltaDimensionClosed D pX hX Set.univ isClosed_univ =
      (inducedDimensionValue D.site D.base D.base_mem D.delta pX
        (genericPoint D.site D.base D.base_mem hX.1 hXInt) : EInt) := by
  have hirr : IrreducibleSpace (points D.site D.base D.base_mem X) := hXInt.2.2
  have h1 : deltaDimensionClosed D pX hX Set.univ isClosed_univ =
      (deltaDimensionIrreducible D pX hX
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ : EInt) :=
    deltaDimensionClosed_eq_deltaDimensionIrreducible D pX hX
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  rw [h1, deltaDimensionIrreducible_eq_of_isGenericPoint D pX hX
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    (isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hXInt)]

/-- **The relative transcendence degree at the generic point vanishes.** In Situation 0EDT,
for good integral `X` and `Y` of the same δ-dimension and a morphism `f : X ⟶ Y` over the base
carrying the generic point of `X` to the generic point of `Y`, the relative transcendence
degree of `f` at the generic point of `X` is zero.

The induced dimension function of Stacks 0EDN at the generic point of `X` is `δ` at the image
in the base plus the transcendence degree over the base, and likewise on `Y`; the two base
images agree, and the degree over the base is additive along `X ⟶ Y ⟶ B` by Stacks 04NR. -/
theorem hasTranscendenceDegreeAt_genericPoint_eq_zero (pX : X ⟶ D.space) (pY : Y ⟶ D.space)
    (hX : D.IsGood pX) (hY : D.IsGood pY)
    (hXInt : IsIntegralSpace D.site D.base D.base_mem X)
    (hYInt : IsIntegralSpace D.site D.base D.base_mem Y) (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hgen : pointsMap D.site D.base D.base_mem X f
        (genericPoint D.site D.base D.base_mem hX.1 hXInt) =
      genericPoint D.site D.base D.base_mem hY.1 hYInt)
    (hdim : deltaDimensionClosed D pX hX Set.univ isClosed_univ =
      deltaDimensionClosed D pY hY Set.univ isClosed_univ) :
    HasTranscendenceDegreeAt D.site D.base D.base_mem f
      (genericPoint D.site D.base D.base_mem hX.1 hXInt) 0 := by
  have hflft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f pY
      (by rw [hf]; exact hX.2.2)
  obtain ⟨nX, hnX⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem pX hX.2.2
    (genericPoint D.site D.base D.base_mem hX.1 hXInt)
  obtain ⟨nY, hnY⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem pY hY.2.2
    (genericPoint D.site D.base D.base_mem hY.1 hYInt)
  obtain ⟨nF, hnF⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem f hflft
    (genericPoint D.site D.base D.base_mem hX.1 hXInt)
  have hnYimg : HasTranscendenceDegreeAt D.site D.base D.base_mem pY
      (pointsMap D.site D.base D.base_mem X f
        (genericPoint D.site D.base D.base_mem hX.1 hXInt)) (nY : ℕ∞) := by
    rw [hgen]; exact hnY
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem pX
      (genericPoint D.site D.base D.base_mem hX.1 hXInt) ((nF : ℕ∞) + (nY : ℕ∞)) := by
    have h0 := hasTranscendenceDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1
      D.isAlgebraicSpace f pY (genericPoint D.site D.base D.base_mem hX.1 hXInt)
      (nF : ℕ∞) (nY : ℕ∞) hnF hnYimg
    rwa [hf] at h0
  have hbase : pointsMap D.site D.base D.base_mem X pX
        (genericPoint D.site D.base D.base_mem hX.1 hXInt) =
      pointsMap D.site D.base D.base_mem Y pY
        (genericPoint D.site D.base D.base_mem hY.1 hYInt) := by
    have h0 : pointsMap D.site D.base D.base_mem X (f ≫ pY)
          (genericPoint D.site D.base D.base_mem hX.1 hXInt) =
        pointsMap D.site D.base D.base_mem Y pY
          (genericPoint D.site D.base D.base_mem hY.1 hYInt) := by
      rw [pointsMap_comp, Function.comp_apply, hgen]
    rwa [hf] at h0
  have hvX := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta pX hX.2.2 (genericPoint D.site D.base D.base_mem hX.1 hXInt) (nX : ℕ∞) hnX
  have hvY := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta pY hY.2.2 (genericPoint D.site D.base D.base_mem hY.1 hYInt) (nY : ℕ∞) hnY
  have hvC := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta pX hX.2.2 (genericPoint D.site D.base D.base_mem hX.1 hXInt)
    ((nF : ℕ∞) + (nY : ℕ∞)) hcomp
  have hdimInt : inducedDimensionValue D.site D.base D.base_mem D.delta pX
        (genericPoint D.site D.base D.base_mem hX.1 hXInt) =
      inducedDimensionValue D.site D.base D.base_mem D.delta pY
        (genericPoint D.site D.base D.base_mem hY.1 hYInt) :=
    WithBotTop.coe_injective
      ((deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D pX hX hXInt).symm.trans
        (hdim.trans
          (deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D pY hY hYInt)))
  have hcast : ((nF : ℕ∞) + (nY : ℕ∞)).toNat = nF + nY := by
    rw [← Nat.cast_add, ENat.toNat_natCast]
  rw [ENat.toNat_natCast] at hvX hvY
  rw [hcast] at hvC
  have e1 : (nX : ℤ) = ((nF + nY : ℕ) : ℤ) := add_left_cancel (hvX.symm.trans hvC)
  rw [hbase] at hvX
  have e2 : (nX : ℤ) = (nY : ℤ) := add_left_cancel (hvX.symm.trans (hdimInt.trans hvY))
  have hzero : nF = 0 := by
    have e1' : nX = nF + nY := by exact_mod_cast e1
    have e2' : nX = nY := by exact_mod_cast e2
    omega
  rw [hzero] at hnF
  simpa using hnF

/-- **Stacks 0ENY.** In Situation 0EDT let `X` and `Y` be good integral algebraic spaces over
the fixed base with `dim_δ(X) = dim_δ(Y)`, and let `f : X ⟶ Y` be a morphism over the base.
Then **either** `f` factors through a proper closed subspace of `Y` — namely the integral
closed subspace of `Y` on the closure of the image of `|X|`, whose set of points is strictly
smaller than `|Y|` — **or** `f` is dominant, carries the generic point of `X` to the generic
point of `Y`, and the extension of function fields `R(X)/R(Y)` it induces is finite.

The function fields are the residue fields at the generic points, by Stacks 0END, and the
extension is the homomorphism `f` induces on them; finiteness is finiteness as a module.

If the image of `|X|` is not dense its closure is an irreducible closed proper subset of
`|Y|`, and `X` is reduced, so `f` factors through the integral closed subspace on it by
Stacks 03IQ and Stacks 03JJ. If the image is dense, then `f` is dominant and carries the
generic point to the generic point; equality of the δ-dimensions makes the relative
transcendence degree at the generic point vanish, and then Spaces over Fields, Lemma 0AD5
gives finiteness. -/
@[stacks 0ENY]
theorem factorsThrough_properIntegralClosedSubspace_or_isDominant_and_finite_functionField
    (pX : X ⟶ D.space) (pY : Y ⟶ D.space) (hX : D.IsGood pX) (hY : D.IsGood pY)
    (hXInt : IsIntegralSpace D.site D.base D.base_mem X)
    (hYInt : IsIntegralSpace D.site D.base D.base_mem Y) (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hdim : deltaDimensionClosed D pX hX Set.univ isClosed_univ =
      deltaDimensionClosed D pY hY Set.univ isClosed_univ) :
    (∃ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
        subspacePointSet D.site D.base D.base_mem Y Z.subspace ≠ Set.univ ∧
          ∃ g : X ⟶ Z.subspace.toFunctor, g ≫ Z.subspace.ι = f) ∨
      (IsDominant D.site D.base D.base_mem f ∧
        pointsMap D.site D.base D.base_mem X f
            (genericPoint D.site D.base D.base_mem hX.1 hXInt) =
          genericPoint D.site D.base D.base_mem hY.1 hYInt ∧
        letI := (residueFieldHom D.site D.base D.base_mem X Y hY.1 hXInt.2.1 hYInt.2.1 f
          (genericPoint D.site D.base D.base_mem hX.1 hXInt)).toAlgebra
        Module.Finite
          (residueField D.site D.base D.base_mem Y hYInt.2.1
            (pointsMap D.site D.base D.base_mem X f
              (genericPoint D.site D.base D.base_mem hX.1 hXInt)))
          (residueField D.site D.base D.base_mem X hXInt.2.1
            (genericPoint D.site D.base D.base_mem hX.1 hXInt))) := by
  classical
  have hflft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f pY
      (by rw [hf]; exact hX.2.2)
  by_cases hdense : Dense (Set.range (pointsMap D.site D.base D.base_mem X f))
  · have hdom : IsDominant D.site D.base D.base_mem f := hdense
    have hgen := pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1
      hXInt hYInt f hdom
    exact Or.inr ⟨hdom, hgen,
      finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero D.site D.base
        D.base_mem hX.1 hY.1 hXInt hYInt f hflft hdom
        (hasTranscendenceDegreeAt_genericPoint_eq_zero D pX pY hX hY hXInt hYInt f hf
          hgen hdim)⟩
  · have hirrX : IrreducibleSpace (points D.site D.base D.base_mem X) := hXInt.2.2
    have hirr : IsIrreducible
        (closure (Set.range (pointsMap D.site D.base D.base_mem X f))) := by
      have h1 := (IrreducibleSpace.isIrreducible_univ
        (points D.site D.base D.base_mem X)).image
        (pointsMap D.site D.base D.base_mem X f)
        (continuous_pointsMap D.site D.base D.base_mem f).continuousOn
      rw [Set.image_univ] at h1
      exact h1.closure
    set Z := integralClosedSubspaceOfPoints D.site D.base D.base_mem hY.1 hYInt.2.1
      ⟨closure (Set.range (pointsMap D.site D.base D.base_mem X f)), hirr, isClosed_closure⟩
    have hZ : subspacePointSet D.site D.base D.base_mem Y Z.subspace =
        closure (Set.range (pointsMap D.site D.base D.base_mem X f)) :=
      subspacePointSet_integralClosedSubspaceOfPoints D.site D.base D.base_mem hY.1 hYInt.2.1 _
    refine Or.inl ⟨Z, ?_, ?_⟩
    · rw [hZ]
      exact fun hcontra ↦ hdense (dense_iff_closure_eq.mpr hcontra)
    · refine (exists_lift_closedSubspace_iff_pointsMap_range_subset D.site D.base D.base_mem
        hY.1 hX.1 _ Z.isClosedSubspace hXInt.1 f).2 ?_
      exact subset_closure.trans hZ.ge

end Situation

end AlgebraicGeometry.Space

end
