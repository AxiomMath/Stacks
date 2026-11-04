module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Chart
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence

/-!
# The order of vanishing along a prime divisor, read on an open chart which is a scheme

Let `X` be a decent, locally Noetherian, integral algebraic space and let `β : h_V ⟶ X` be an
open immersion out of the presheaf represented by an object `V` of the site, so that the scheme
`V` is an open subspace of `X`. A rational function `f` of `X` is a rational function of the
scheme `V`, and for every prime divisor `Z` of `X` whose generic point is the image of a point
`v ∈ V`, the order of vanishing `ord_Z(f)` of Definition 0ENL is the order of vanishing of that
rational function at `v`, in the sense of Divisors, Definition 02RJ.

This is Stacks 0ENM read on a fixed open chart: the point is that the rational function of `V`
does not depend on the prime divisor, so that all the orders of vanishing along prime divisors
meeting `V` are computed by one rational function of one scheme.

## Main definitions

* `AlgebraicGeometry.Space.openChartObject`: the object of the site given by an open of `V`.
* `AlgebraicGeometry.Space.openChartRationalFunction`: the reading of the rational functions of
  `X` in the function field of an affine open of `V`.

## Main results

* `AlgebraicGeometry.Space.openChartRationalFunction_homOfLE`: the reading is compatible with
  restriction to a smaller affine open.
* `AlgebraicGeometry.Space.exists_functionField_forall_openChartRationalFunction`: there is one
  rational function `g` of the scheme `V` whose restriction to every affine open is the reading
  of `f` there.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord_of_isOpenImmersion`: **Stacks 0ENM on
  an open chart**, `ord_Z(f) = ord_v(g)`.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory Order Stacks.Chow
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- The image in the function field of the germ at any point of a global section of an integral
scheme is the germ of that section at the generic point. -/
theorem Scheme.algebraMap_germ_top_eq_germToFunctionField (X : Scheme.{u}) [IsIntegral X]
    (x : X) (a : Γ(X, ⊤)) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ ⊤ x trivial a) =
      X.germToFunctionField ⊤ a := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  unfold Scheme.germToFunctionField
  rw [← TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (y := x) trivial
    ((genericPoint_spec X).specializes trivial)]
  rfl

/-- The extension of function fields of a dominant morphism of integral schemes, read on the
germs of global sections. -/
theorem dominantFunctionFieldMap_germToFunctionField_top {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (a : Γ(Y, ⊤)) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
    dominantFunctionFieldMap f (Y.germToFunctionField ⊤ a) =
      X.germToFunctionField ⊤ (f.appTop a) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  rw [dominantFunctionFieldMap_germToFunctionField_of_mem f (genericPoint X) ⊤ trivial ⊤ trivial
    le_top a]
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : BigFppfOver B S hS} (β : yoneda.obj V ⟶ X) (hβ : IsOpenImmersion B S hS β)

/-! ### Opens of an open chart -/

/-- The morphism of schemes underlying `openChartMap` at an open `U` is the inclusion `U.ι`. -/
theorem toScheme_map_openChartMap (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) = U.ι :=
  rfl

/-- The open chart of `X` given by an open `U` of the scheme of an open chart `β : h_V ⟶ X`. -/
abbrev openChartToSpace (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    yoneda.obj (openChartObject B S hS V U) ⟶ X :=
  yoneda.map (openChartMap B S hS V U) ≫ β

include hβ in
/-- The open chart `openChartToSpace β U` of `X` is an open immersion. -/
theorem isOpenImmersion_openChartToSpace (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsOpenImmersion B S hS (openChartToSpace B S hS β U) :=
  isOpenImmersion_comp B S hS _ _
    (isOpenImmersion_yoneda_map B S hS (openChartMap B S hS V U)
      (show AlgebraicGeometry.IsOpenImmersion U.ι from inferInstance)) hβ

include hβ in
/-- The open chart `openChartToSpace β U` of `X` is étale. -/
theorem isEtale_openChartToSpace (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsEtale B S hS (openChartToSpace B S hS β U) :=
  isEtale_of_isOpenImmersion B S hS (isOpenImmersion_openChartToSpace B S hS β hβ U)

/-- The inclusion of the open chart object of a smaller open into that of a larger one. -/
def openChartObjectHom {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U) :
    openChartObject B S hS V U' ⟶ openChartObject B S hS V U :=
  Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj V).homOfLE h)) (by
    apply B.inclusion.map_injective
    dsimp [ObjectProperty.homMk, openChartObject]
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The morphism of schemes underlying `openChartObjectHom h` is the inclusion `homOfLE h`. -/
theorem toScheme_map_openChartObjectHom
    {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U) :
    (BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h) =
      ((BigFppfOver.toScheme B S hS).obj V).homOfLE h :=
  rfl

/-- For opens `U' ≤ U`, the inclusion `openChartObjectHom h` followed by `openChartMap` at `U` is
`openChartMap` at `U'`. -/
theorem openChartObjectHom_comp_openChartMap
    {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U) :
    openChartObjectHom B S hS h ≫ openChartMap B S hS V U = openChartMap B S hS V U' := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  dsimp [openChartObjectHom, openChartMap, ObjectProperty.homMk, openChartObject]
  exact Scheme.homOfLE_ι _ h

/-- For opens `U' ≤ U`, the open chart at `U'` is the open chart at `U` precomposed with the
inclusion `openChartObjectHom h`. -/
theorem yoneda_map_openChartObjectHom_comp_openChartToSpace
    {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U) :
    yoneda.map (openChartObjectHom B S hS h) ≫ openChartToSpace B S hS β U =
      openChartToSpace B S hS β U' := by
  rw [openChartToSpace, ← Category.assoc, ← Functor.map_comp,
    openChartObjectHom_comp_openChartMap]

/-! ### The reading of a rational function on an affine open of an open chart -/

variable [IsIntegral ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]

section Instances

variable (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)

/-- The morphism of schemes underlying `openChartMap` at `U` is an open immersion. -/
instance isOpenImmersion_toScheme_map_openChartMap :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U)) :=
  show AlgebraicGeometry.IsOpenImmersion U.ι from inferInstance

/-- The scheme of the open chart object of `U` is locally Noetherian. -/
instance isLocallyNoetherian_toScheme_obj_openChartObject :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) :=
  show IsLocallyNoetherian U.toScheme from inferInstance

/-- The underlying scheme of the open chart object of `U` is locally Noetherian. -/
instance isLocallyNoetherian_left_openChartObject :
    IsLocallyNoetherian (openChartObject B S hS V U).left.1 :=
  show IsLocallyNoetherian U.toScheme from inferInstance

omit [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The scheme of the open chart object of a nonempty open `U` is integral. -/
theorem isIntegral_toScheme_obj_openChartObject
    [Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U))] :
    IsIntegral ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) :=
  _root_.AlgebraicGeometry.isIntegral_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U))

omit [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] in
/-- For a nonempty open `U`, the morphism of schemes underlying `openChartMap` at `U` is
dominant. -/
theorem isDominant_toScheme_map_openChartMap
    [Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U))] :
    IsDominant ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U)) :=
  Stacks.Chow.isDominant_of_isOpenImmersion _

/-- For opens `U' ≤ U`, the morphism of schemes underlying `openChartObjectHom h` is an open
immersion. -/
instance isOpenImmersion_toScheme_map_openChartObjectHom
    {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h)) :=
  show AlgebraicGeometry.IsOpenImmersion (((BigFppfOver.toScheme B S hS).obj V).homOfLE h) from
    inferInstance

end Instances

/-- **The reading of the rational functions of `X` on an affine open `U` of an open chart.** It
is `AlgebraicGeometry.Space.rationalFunctionsToFunctionField` at the chart `U ⟶ V ⟶ X`. -/
def openChartRationalFunction (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hU : IsAffineOpen U) (w : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) :
    haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
    haveI := isIntegral_toScheme_obj_openChartObject B S hS U
    rationalFunctions B S hS hX →+*
      ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)).functionField :=
  haveI : IsAffine (openChartObject B S hS V U).left.1 := hU
  haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
  haveI : IsIntegral (openChartObject B S hS V U).left.1 :=
    isIntegral_toScheme_obj_openChartObject B S hS U
  haveI : IsLocallyNoetherian (openChartObject B S hS V U).left.1 :=
    isLocallyNoetherian_toScheme_obj_openChartObject B S hS U
  rationalFunctionsToFunctionField B S hS hX (openChartObject B S hS V U) w
    (openChartToSpace B S hS β U) (isEtale_openChartToSpace B S hS β hβ U)

/-- **Compatibility of the reading with restriction.** For affine opens `U' ≤ U` of an open
chart, the reading of a rational function on `U'` is the restriction of its reading on `U`. -/
theorem openChartRationalFunction_homOfLE
    {U U' : ((BigFppfOver.toScheme B S hS).obj V).Opens} (h : U' ≤ U)
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (w : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U))
    (w' : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U'))
    (f : rationalFunctions B S hS hX) :
    haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
    haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U')) := ⟨w'⟩
    haveI := isIntegral_toScheme_obj_openChartObject B S hS U
    haveI := isIntegral_toScheme_obj_openChartObject B S hS U'
    haveI : IsDominant ((BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h)) :=
      Stacks.Chow.isDominant_of_isOpenImmersion _
    openChartRationalFunction B S hS hX β hβ U' hU' w' f =
      dominantFunctionFieldMap ((BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h))
        (openChartRationalFunction B S hS hX β hβ U hU w f) := by
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U')) := ⟨w'⟩
  have := isIntegral_toScheme_obj_openChartObject B S hS U
  have := isIntegral_toScheme_obj_openChartObject B S hS U'
  have : IsAffine (openChartObject B S hS V U).left.1 := hU
  have : IsAffine (openChartObject B S hS V U').left.1 := hU'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U')) := hU'
  set g := openChartObjectHom B S hS h
  set i := (BigFppfOver.toScheme B S hS).map g
  have : IsDominant i := Stacks.Chow.isDominant_of_isOpenImmersion _
  have : IsIntegral (openChartObject B S hS V U).left.1 :=
    isIntegral_toScheme_obj_openChartObject B S hS U
  have : IsIntegral (openChartObject B S hS V U').left.1 :=
    isIntegral_toScheme_obj_openChartObject B S hS U'
  have hc : IsEtale B S hS (openChartToSpace B S hS β U) := isEtale_openChartToSpace B S hS β hβ U
  have hcc : yoneda.map g ≫ openChartToSpace B S hS β U = openChartToSpace B S hS β U' :=
    yoneda_map_openChartObjectHom_comp_openChartToSpace B S hS β h
  have hc' : IsEtale B S hS (yoneda.map g ≫ openChartToSpace B S hS β U) := by
    rw [hcc]
    exact isEtale_openChartToSpace B S hS β hβ U'
  have key := rationalFunctionsToTotalFractionRing_comp_eq B S hS hX g hc hc'
    ((dominantFunctionFieldMap i).comp
      ((openChartObject B S hS V U).left.1.totalFractionRingToFunctionField w))
    ((openChartObject B S hS V U').left.1.totalFractionRingToFunctionField w')
    (fun a ↦ by
      rw [RingHom.comp_apply, Scheme.totalFractionRingToFunctionField_algebraMap,
        Scheme.totalFractionRingToFunctionField_algebraMap,
        Scheme.algebraMap_germ_top_eq_germToFunctionField,
        Scheme.algebraMap_germ_top_eq_germToFunctionField]
      exact dominantFunctionFieldMap_germToFunctionField_top i a) f
  rw [RingHom.comp_apply] at key
  have hcongr : ∀ (c₁ c₂ : yoneda.obj (openChartObject B S hS V U') ⟶ X) (_ : c₁ = c₂)
      (h₁ : IsEtale B S hS c₁) (h₂ : IsEtale B S hS c₂),
      rationalFunctionsToTotalFractionRing B S hS hX (openChartObject B S hS V U') c₁ h₁ =
        rationalFunctionsToTotalFractionRing B S hS hX (openChartObject B S hS V U') c₂ h₂ := by
    intro c₁ c₂ hc₁₂ _ _
    subst hc₁₂
    rfl
  rwa [hcongr _ _ hcc hc' (isEtale_openChartToSpace B S hS β hβ U')] at key

/-- The function field maps of dominant morphisms of integral schemes compose along a commuting
triangle. -/
private theorem dominantFunctionFieldMap_apply_of_comp_eq {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (ι : Y ⟶ Z) (ι' : X ⟶ Z) [IsDominant f]
    [IsDominant ι] [IsDominant ι'] (h : f ≫ ι = ι') (a : Z.functionField) :
    dominantFunctionFieldMap f (dominantFunctionFieldMap ι a) = dominantFunctionFieldMap ι' a := by
  subst h
  rw [dominantFunctionFieldMap_comp]
  rfl

include hβ in
/-- **One rational function of the open chart reads `f` on every affine open.** -/
theorem exists_functionField_forall_openChartRationalFunction
    (f : rationalFunctions B S hS hX) :
    ∃ g : ((BigFppfOver.toScheme B S hS).obj V).functionField,
      ∀ (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) (hU : IsAffineOpen U)
        (w : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)),
        haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
        haveI := isIntegral_toScheme_obj_openChartObject B S hS U
        haveI := isDominant_toScheme_map_openChartMap B S hS U
        openChartRationalFunction B S hS hX β hβ U hU w f =
          dominantFunctionFieldMap ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U))
            g := by
  set T := (BigFppfOver.toScheme B S hS).obj V
  have hgen : ∀ (U : T.Opens), Nonempty U → _root_.genericPoint T ∈ U := fun U ⟨w⟩ ↦
    ((genericPoint_spec T).mem_open_set_iff U.2).2 ⟨w.1, trivial, w.2⟩
  obtain ⟨U₀, hU₀, hηU₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := _root_.genericPoint T) (U := (⊤ : T.Opens)) trivial
  set w₀ : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U₀) :=
    (⟨_root_.genericPoint T, hηU₀⟩ : U₀)
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U₀)) := ⟨w₀⟩
  have := isIntegral_toScheme_obj_openChartObject B S hS U₀
  have := isDominant_toScheme_map_openChartMap B S hS U₀
  set ι₀ := (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U₀) with hι₀
  refine ⟨(functionFieldEquiv_openImmersion ι₀).symm
    (openChartRationalFunction B S hS hX β hβ U₀ hU₀ w₀ f), fun U hU w ↦ ?_⟩
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
  have := isIntegral_toScheme_obj_openChartObject B S hS U
  have := isDominant_toScheme_map_openChartMap B S hS U
  set ιU := (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) with hιU
  have hηU : _root_.genericPoint T ∈ U := hgen U ⟨⟨w.1, w.2⟩⟩
  obtain ⟨U', hU', hηU', hU'le⟩ :=
    exists_isAffineOpen_mem_and_subset (show _root_.genericPoint T ∈ U ⊓ U₀ from ⟨hηU, hηU₀⟩)
  set w' : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U') :=
    (⟨_root_.genericPoint T, hηU'⟩ : U')
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U')) := ⟨w'⟩
  have := isIntegral_toScheme_obj_openChartObject B S hS U'
  have := isDominant_toScheme_map_openChartMap B S hS U'
  have h₁ : U' ≤ U := fun x hx ↦ (hU'le hx).1
  have h₀ : U' ≤ U₀ := fun x hx ↦ (hU'le hx).2
  set i₁ := (BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h₁) with hi₁
  set i₀ := (BigFppfOver.toScheme B S hS).map (openChartObjectHom B S hS h₀) with hi₀
  have : IsDominant i₁ := Stacks.Chow.isDominant_of_isOpenImmersion _
  have : IsDominant i₀ := Stacks.Chow.isDominant_of_isOpenImmersion _
  have e₁ := openChartRationalFunction_homOfLE B S hS hX β hβ h₁ hU hU' w w' f
  have e₀ := openChartRationalFunction_homOfLE B S hS hX β hβ h₀ hU₀ hU' w₀ w' f
  apply (dominantFunctionFieldMap i₁).injective
  rw [← e₁, e₀]
  have hm₀ : i₀ ≫ ι₀ = (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U') := by
    rw [hi₀, hι₀, ← Functor.map_comp, openChartObjectHom_comp_openChartMap]
  have hm₁ : i₁ ≫ ιU = (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U') := by
    rw [hi₁, hιU, ← Functor.map_comp, openChartObjectHom_comp_openChartMap]
  have hsymm : dominantFunctionFieldMap ι₀ ((functionFieldEquiv_openImmersion ι₀).symm
      (openChartRationalFunction B S hS hX β hβ U₀ hU₀ w₀ f)) =
      openChartRationalFunction B S hS hX β hβ U₀ hU₀ w₀ f :=
    (functionFieldEquiv_openImmersion ι₀).apply_symm_apply _
  set g := (functionFieldEquiv_openImmersion ι₀).symm
    (openChartRationalFunction B S hS hX β hβ U₀ hU₀ w₀ f)
  rw [← hsymm, dominantFunctionFieldMap_apply_of_comp_eq _ _ _ hm₀,
    dominantFunctionFieldMap_apply_of_comp_eq _ _ _ hm₁]

/-! ### The elementary étale neighbourhood given by an open of an open chart -/

include hβ in
/-- **The elementary étale neighbourhood given by an open of an open chart.** For an open `U` of
the scheme of an open chart `β : h_V ⟶ X` and a point `v ∈ U` over `x ∈ |X|`, the chart
`U ⟶ V ⟶ X` with the point `v` is an elementary étale neighbourhood of `x`. -/
def openChartNeighborhood (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (u : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) (x : points B S hS X)
    (hx : pointsMap B S hS (yoneda.obj V) β ((pointsEquivScheme B S hS V).symm
      ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) u)) = x) :
    ElementaryEtaleNeighborhood B S hS X hX x where
  scheme := openChartObject B S hS V U
  point := u
  residueField_contained :=
    B.residueField_spec_contains (openChartObject B S hS V U).left.property u
  toSpace := openChartToSpace B S hS β U
  etale_toSpace := isEtale_openChartToSpace B S hS β hβ U
  map_point := by
    set hk := B.residueField_spec_contains (openChartObject B S hS V U).left.property u
    have hp : presheafPoint B S hS (openChartObject B S hS V U) u hk =
        (pointsEquivScheme B S hS (openChartObject B S hS V U)).symm u := by
      refine (pointsEquivScheme B S hS (openChartObject B S hS V U)).injective ?_
      rw [Equiv.apply_symm_apply]
      exact pointsToScheme_presheafPoint B S hS (openChartObject B S hS V U) u hk
    have hq : pointsMap B S hS _ (yoneda.map (openChartMap B S hS V U))
        ((pointsEquivScheme B S hS (openChartObject B S hS V U)).symm u) =
        (pointsEquivScheme B S hS V).symm
          ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) u) := by
      refine (pointsEquivScheme B S hS V).injective ?_
      rw [Equiv.apply_symm_apply]
      change pointsToScheme B S hS V _ = _
      rw [pointsToScheme_pointsMap_yoneda]
      congr 1
      exact (pointsEquivScheme B S hS (openChartObject B S hS V U)).apply_symm_apply u
    rw [hp, openChartToSpace, pointsMap_comp_apply, hq, hx]
  mono_residueField := by
    set hk := B.residueField_spec_contains (openChartObject B S hS V U).left.property u
    have _ : Mono (residueFieldMap B S hS (openChartObject B S hS V U) u hk) := by
      apply (BigFppfOver.toScheme B S hS).mono_of_mono_map
      change Mono (((BigFppfOver.toScheme B S hS).obj
        (openChartObject B S hS V U)).fromSpecResidueField u)
      infer_instance
    have _ : Mono (openChartToSpace B S hS β U) :=
      mono_of_isOpenImmersion B S hS _ (isOpenImmersion_openChartToSpace B S hS β hβ U)
    infer_instance

/-! ### Stacks 0ENM on an open chart -/

include hβ in
/-- **Stacks 0ENM on an open chart.** Let `X` be a decent, locally Noetherian, integral
algebraic space, `β : h_V ⟶ X` an open chart, `f` an invertible rational function of `X` and `g`
a rational function of the scheme `V` whose restriction to every affine open of `V` is the
reading of `f` there. If the generic point of a prime divisor `Z` of `X` is the image of a point
`v` of codimension one of `V`, then `ord_Z(f) = ord_v(g)`. -/
theorem PrimeDivisor.ord_eq_scheme_ord_of_isOpenImmersion (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : pointsMap B S hS (yoneda.obj V) β ((pointsEquivScheme B S hS V).symm v) =
      Z.genericPoint B S hS X)
    (hcoh : coheight v = 1) (f : (rationalFunctions B S hS hX)ˣ)
    (g : ((BigFppfOver.toScheme B S hS).obj V).functionField)
    (hg : ∀ (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) (hU : IsAffineOpen U)
        (w : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)),
        haveI : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨w⟩
        haveI := isIntegral_toScheme_obj_openChartObject B S hS U
        haveI := isDominant_toScheme_map_openChartMap B S hS U
        openChartRationalFunction B S hS hX β hβ U hU w (f : rationalFunctions B S hS hX) =
          dominantFunctionFieldMap ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U))
            g) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z =
      ((BigFppfOver.toScheme B S hS).obj V).ord g v := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (x := v)
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj V).Opens)) trivial
  obtain ⟨u, hιu⟩ : ∃ u : (BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U),
      (BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) u = v :=
    ⟨(⟨v, hvU⟩ : U), rfl⟩
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj (openChartObject B S hS V U)) := ⟨u⟩
  have := isIntegral_toScheme_obj_openChartObject B S hS U
  have := isDominant_toScheme_map_openChartMap B S hS U
  have hu : pointsMap B S hS (yoneda.obj V) β ((pointsEquivScheme B S hS V).symm
      ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U) u)) =
      Z.genericPoint B S hS X := by
    rwa [hιu]
  let N := openChartNeighborhood B S hS hX β hβ U u _ hu
  have : IsAffine N.scheme.left.1 := hU
  have : IsIntegral N.scheme.left.1 :=
    isIntegral_toScheme_obj_openChartObject B S hS U
  have : IsLocallyNoetherian N.scheme.left.1 :=
    isLocallyNoetherian_toScheme_obj_openChartObject B S hS U
  have hcohN : coheight N.point = 1 := by
    have h1 : coheight (U.ι u) = coheight u := Scheme.coheight_opens U u
    rw [show U.ι u = v from hιu] at h1
    exact h1.symm.trans hcoh
  rw [PrimeDivisor.ord_eq_scheme_ord_of_chart B S hS hX hInt hN Z hdec N hcohN f]
  have hread : rationalFunctionsToFunctionField B S hS hX N.scheme N.point N.toSpace
      N.etale_toSpace (f : rationalFunctions B S hS hX) =
      openChartRationalFunction B S hS hX β hβ U hU u (f : rationalFunctions B S hS hX) :=
    rfl
  rw [hread, hg U hU u]
  have hord := ord_dominantFunctionFieldMap_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS V U)) g u
  rwa [hιu] at hord

end Space

end AlgebraicGeometry

end
