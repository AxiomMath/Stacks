module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesFibreProduct
public import StacksFrontier.Topology.Dimension.CodimensionHomeomorph
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericPointChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence

/-!
# The order of vanishing on a represented integral space

Let `R` be an integral scheme of the big fppf site of `S` and `h_R` the algebraic space it
represents; `h_R` is an integral algebraic space. A rational function `f` of `h_R`, Stacks 0EMP,
read on an affine open `W ⊆ R` as an étale chart, Stacks 0ENK, is an element of the function
field of `W`, which is the function field of `R`. This element does not depend on `W`: for
`W' ⊆ W` the two readings agree because the pullback of rational functions to affine charts is
compatible with restriction, and two nonempty affine opens of the irreducible scheme `R` contain
a common one. This gives the reading `R(h_R) → R(R)` of rational functions on the representing
scheme, `AlgebraicGeometry.Space.representedFunctionFieldMap`.

The order of vanishing of Stacks 0ENL along a prime divisor `Z ⊆ h_R` is then the order of
vanishing of Divisors, Definition 02RJ, of this reading at the generic point `ξ` of `Z` in `R`:
the whole of `h_R` is its schematic locus, so Stacks 0ENM applies on an affine open `W ∋ ξ`, and
restriction to `W` does not change the order of vanishing on the scheme side.

## Main definitions

* `AlgebraicGeometry.Space.affineOpenChartReading`: the reading of a rational function of `h_R`
  in the function field of `R` through an affine open `W`, regarded as an étale chart
  `h_W → h_R` through `AlgebraicGeometry.Space.opensObject`.
* `AlgebraicGeometry.Space.representedFunctionFieldMap`: the reading `R(h_R) → R(R)`, and
  `AlgebraicGeometry.Space.representedFunctionFieldEquiv` the same as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_yoneda`: `h_R` is integral.
* `AlgebraicGeometry.Space.affineOpenChartReading_eq`: the reading does not depend on the affine
  open.
* `AlgebraicGeometry.Space.bijective_representedFunctionFieldMap`: the reading is bijective; read
  through an affine open and followed by the residue map at its generic point it is the
  evaluation of Stacks 0END along a monomorphism from the spectrum of a field.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_representedFunctionFieldMap`: the order of
  vanishing along a prime divisor of `h_R` is the order of vanishing on `R` at its generic point.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (R : BigFppfOver B S hS)

/-- The algebraic space represented by an integral scheme is integral: it is reduced and decent,
and its point space is homeomorphic to that of the scheme. -/
theorem isIntegralSpace_yoneda [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)] :
    IsIntegralSpace B S hS (yoneda.obj R) :=
  ⟨hasEtaleLocalProperty_of_representable B S hS _ (fun Y : Scheme.{u} => IsReduced Y) R
      (Iso.refl _) (inferInstance : IsReduced ((BigFppfOver.toScheme B S hS).obj R)),
    isDecentSpace_yoneda B S hS R,
    (schemePointsHomeomorph B S hS R).irreducibleSpace_iff.2 inferInstance⟩

/-- The open immersion of an open, as a morphism of the represented spaces, is étale. -/
theorem isEtale_yoneda_map_opensObjectι (W : ((BigFppfOver.toScheme B S hS).obj R).Opens) :
    IsEtale B S hS (yoneda.map (opensObjectι B S hS R W)) :=
  etale_yoneda B S hS _ (by change Etale W.ι; infer_instance)

/-- On an integral affine scheme, the reading of a global function in the function field
through the total ring of fractions at any point is its germ at the generic point. -/
theorem _root_.AlgebraicGeometry.Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ
    (T : Scheme.{u}) [IsAffine T] [AlgebraicGeometry.IsIntegral T] (t : T) (a : Γ(T, ⊤)) :
    T.totalFractionRingToFunctionField t (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)) a) =
      (T.presheaf.germ ⊤ (_root_.genericPoint T) trivial).hom a := by
  rw [Scheme.totalFractionRingToFunctionField_algebraMap]
  exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes T.presheaf
    (U := ⊤) trivial ((genericPoint_spec T).specializes trivial)) a

/-- The reading of a rational function through the total ring of fractions of an affine chart
is the same at every point of the chart: both are the germ at the generic point. -/
theorem _root_.AlgebraicGeometry.Scheme.totalFractionRingToFunctionField_congr
    (T : Scheme.{u}) [IsAffine T] [AlgebraicGeometry.IsIntegral T] (t t' : T) :
    T.totalFractionRingToFunctionField t = T.totalFractionRingToFunctionField t' :=
  IsLocalization.ringHom_ext (Γ(T, ⊤))⁰ (RingHom.ext fun a => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ,
      Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ])

/-- On an integral affine scheme, the reading of the total ring of fractions in the residue field
at the generic point is the reading in the function field followed by the residue map. -/
theorem _root_.AlgebraicGeometry.Scheme.totalFractionRingToResidueField_genericPoint
    (T : Scheme.{u}) [IsAffine T] [AlgebraicGeometry.IsIntegral T]
    (ht : IsField (T.presheaf.stalk (_root_.genericPoint T))) :
    Scheme.totalFractionRingToResidueField (T := T) (_root_.genericPoint T) ht =
      (T.residue (_root_.genericPoint T)).hom.comp
        (T.totalFractionRingToFunctionField (_root_.genericPoint T)) :=
  IsLocalization.ringHom_ext (Γ(T, ⊤))⁰ (RingHom.ext fun a => by
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      Scheme.totalFractionRingToResidueField_algebraMap,
      Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ])

variable [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)]

/-- **The reading of a rational function of `h_R` through an affine open `W` of `R`**: pull it
back to the total ring of fractions of `Γ(W, 𝒪_W)` along the chart `W → R`, Stacks 0ENK, read
it in the function field of `W`, and identify that with the function field of `R`. -/
def affineOpenChartReading (W : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (hW : IsAffineOpen W) [Nonempty W]
    (f : rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R)) :
    ((BigFppfOver.toScheme B S hS).obj R).functionField :=
  haveI : IsAffine (opensObject B S hS R W).left.1 := hW
  haveI : IsReduced (opensObject B S hS R W).left.1 := inferInstanceAs (IsReduced W.toScheme)
  haveI : IsLocallyNoetherian (opensObject B S hS R W).left.1 :=
    inferInstanceAs (IsLocallyNoetherian W.toScheme)
  haveI : IsAffine W.toScheme := hW
  haveI := Stacks.Chow.isDominant_of_isOpenImmersion W.ι
  (Stacks.Chow.functionFieldEquiv_openImmersion W.ι).symm
    (W.toScheme.totalFractionRingToFunctionField (Nonempty.some ‹Nonempty W›)
      (rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R)
        (opensObject B S hS R W) (yoneda.map (opensObjectι B S hS R W))
        (isEtale_yoneda_map_opensObjectι B S hS R W) f))

/-- The extension of function fields along a composite of dominant morphisms, read on a morphism
which is that composite. -/
private theorem dominantFunctionFieldMap_eq_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z) [_root_.AlgebraicGeometry.IsDominant f]
    [_root_.AlgebraicGeometry.IsDominant g] (j : X ⟶ Z)
    [_root_.AlgebraicGeometry.IsDominant j] (hj : j = f ≫ g) :
    dominantFunctionFieldMap j =
      (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) := by
  subst hj
  exact Stacks.Chow.dominantFunctionFieldMap_comp f g

/-- **The reading through an affine open does not change on a smaller affine open.** For
nonempty affine opens `W' ⊆ W` of `R`, a rational function of `h_R` has the same reading in the
function field of `R` through `W'` as through `W`: the pullbacks to the two charts are compatible
with restriction, Stacks 0ENK. -/
theorem affineOpenChartReading_eq_of_le {W W' : ((BigFppfOver.toScheme B S hS).obj R).Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') [Nonempty W] [Nonempty W'] (h : W' ≤ W)
    (f : rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R)) :
    affineOpenChartReading B S hS R W' hW' f = affineOpenChartReading B S hS R W hW f := by
  have : IsAffine (opensObject B S hS R W).left.1 := hW
  have : IsReduced (opensObject B S hS R W).left.1 := inferInstanceAs (IsReduced W.toScheme)
  have : IsLocallyNoetherian (opensObject B S hS R W).left.1 :=
    inferInstanceAs (IsLocallyNoetherian W.toScheme)
  have : IsAffine (opensObject B S hS R W').left.1 := hW'
  have : IsReduced (opensObject B S hS R W').left.1 :=
    inferInstanceAs (IsReduced W'.toScheme)
  have : IsLocallyNoetherian (opensObject B S hS R W').left.1 :=
    inferInstanceAs (IsLocallyNoetherian W'.toScheme)
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have := Stacks.Chow.isDominant_of_isOpenImmersion W.ι
  have := Stacks.Chow.isDominant_of_isOpenImmersion W'.ι
  have :=
    Stacks.Chow.isDominant_of_isOpenImmersion (((BigFppfOver.toScheme B S hS).obj R).homOfLE h)
  set g := GradedAlgebraRestriction.opensObjectHomOfLE R h
  set ι₀ := ((BigFppfOver.toScheme B S hS).obj R).homOfLE h
  set t := Nonempty.some ‹Nonempty W›
  set t' := Nonempty.some ‹Nonempty W'›
  have : Nonempty (⊤ : W.toScheme.Opens) := ⟨⟨t, trivial⟩⟩
  have : Nonempty (⊤ : W'.toScheme.Opens) := ⟨⟨t', trivial⟩⟩
  have happ : ι₀.appLE ⊤ ⊤ le_top = ι₀.appTop := by simp [Scheme.Hom.appLE]; rfl
  have hcc : yoneda.map g ≫ yoneda.map (opensObjectι B S hS R W) =
      yoneda.map (opensObjectι B S hS R W') := by
    rw [← Functor.map_comp, GradedAlgebraRestriction.opensObjectHomOfLE_ι R h]
  have hc' : IsEtale B S hS (yoneda.map g ≫ yoneda.map (opensObjectι B S hS R W)) := by
    rw [hcc]; exact isEtale_yoneda_map_opensObjectι B S hS R W'
  have hconv : ∀ (c₁ c₂ : yoneda.obj (opensObject B S hS R W') ⟶ yoneda.obj R)
      (_ : c₁ = c₂) (h₁ : IsEtale B S hS c₁) (h₂ : IsEtale B S hS c₂),
      rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R) _ c₁ h₁ f =
        rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R) _ c₂ h₂
          f := by
    rintro _ _ rfl _ _; rfl
  have key := rationalFunctionsToTotalFractionRing_comp_eq B S hS
    (isAlgebraicSpace_yoneda B S hS R) g (isEtale_yoneda_map_opensObjectι B S hS R W) hc'
    ((dominantFunctionFieldMap ι₀).comp (W.toScheme.totalFractionRingToFunctionField t))
    (W'.toScheme.totalFractionRingToFunctionField t') (fun (a : Γ(W.toScheme, ⊤)) => by
      change dominantFunctionFieldMap ι₀ (W.toScheme.totalFractionRingToFunctionField t
          (algebraMap Γ(W.toScheme, ⊤) (FractionRing Γ(W.toScheme, ⊤)) a)) =
        W'.toScheme.totalFractionRingToFunctionField t'
          (algebraMap Γ(W'.toScheme, ⊤) (FractionRing Γ(W'.toScheme, ⊤)) (ι₀.appTop a))
      rw [ Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ,
        Scheme.totalFractionRingToFunctionField_algebraMap_eq_germ]
      have := dominantFunctionFieldMap_germToFunctionField_of_mem ι₀ t' ⊤ trivial ⊤ trivial
        le_top a
      rw [happ] at this
      exact this) f
  rw [hconv _ _ hcc hc' (isEtale_yoneda_map_opensObjectι B S hS R W')] at key
  unfold affineOpenChartReading
  unfold opensObject at key ⊢
  rw [key, RingHom.comp_apply, RingEquiv.symm_apply_eq,
    Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap,
    dominantFunctionFieldMap_eq_comp ι₀ W.ι W'.ι (Scheme.homOfLE_ι _ h).symm, RingHom.comp_apply,
    ← Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap W.ι,
    RingEquiv.apply_symm_apply]

/-- Every point of a scheme lies in an affine open. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_le (X : Scheme.{u}) {U : X.Opens}
    {x : X} (hx : x ∈ U) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨W, hW, hxW, hWU⟩

/-- **The reading through an affine open does not depend on the affine open.** Two nonempty
affine opens of the irreducible scheme `R` meet, their intersection contains a nonempty affine
open, and the reading does not change on passing to it. -/
theorem affineOpenChartReading_eq {W W' : ((BigFppfOver.toScheme B S hS).obj R).Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') [Nonempty W] [Nonempty W']
    (f : rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R)) :
    affineOpenChartReading B S hS R W' hW' f = affineOpenChartReading B S hS R W hW f := by
  obtain ⟨x, hxW, hxW'⟩ : ((W : Set ((BigFppfOver.toScheme B S hS).obj R)) ∩ W').Nonempty :=
    nonempty_preirreducible_inter W.2 W'.2
      ⟨(Nonempty.some ‹Nonempty W›).1, (Nonempty.some ‹Nonempty W›).2⟩
      ⟨(Nonempty.some ‹Nonempty W'›).1, (Nonempty.some ‹Nonempty W'›).2⟩
  obtain ⟨V, hV, hxV, hVle⟩ := Scheme.exists_isAffineOpen_mem_le _
    (show x ∈ W ⊓ W' from ⟨hxW, hxW'⟩)
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  rw [← affineOpenChartReading_eq_of_le B S hS R hW' hV (hVle.trans inf_le_right),
    affineOpenChartReading_eq_of_le B S hS R hW hV (hVle.trans inf_le_left)]

omit [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The integral scheme `R` has a nonempty affine open. -/
theorem exists_isAffineOpen_nonempty :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj R).Opens, IsAffineOpen W ∧ Nonempty W := by
  obtain ⟨x⟩ := (inferInstance : Nonempty ((BigFppfOver.toScheme B S hS).obj R))
  obtain ⟨W, hW, hxW, -⟩ :=
    Scheme.exists_isAffineOpen_mem_le _ (show x ∈ (⊤ : Opens _) from trivial)
  exact ⟨W, hW, ⟨⟨x, hxW⟩⟩⟩

/-- **The reading of the rational functions of `h_R` on the representing scheme**, the ring
homomorphism `R(h_R) → R(R)`: the reading through any nonempty affine open of `R`, which does not
depend on the affine open by `AlgebraicGeometry.Space.affineOpenChartReading_eq`. -/
def representedFunctionFieldMap :
    rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R) →+*
      ((BigFppfOver.toScheme B S hS).obj R).functionField :=
  haveI := (exists_isAffineOpen_nonempty B S hS R).choose_spec.2
  haveI : IsAffine (opensObject B S hS R (exists_isAffineOpen_nonempty B S hS R).choose).left.1 :=
    (exists_isAffineOpen_nonempty B S hS R).choose_spec.1
  haveI : IsReduced (opensObject B S hS R
      (exists_isAffineOpen_nonempty B S hS R).choose).left.1 :=
    inferInstanceAs (IsReduced (exists_isAffineOpen_nonempty B S hS R).choose.toScheme)
  haveI : IsLocallyNoetherian (opensObject B S hS R
      (exists_isAffineOpen_nonempty B S hS R).choose).left.1 :=
    inferInstanceAs (IsLocallyNoetherian (exists_isAffineOpen_nonempty B S hS R).choose.toScheme)
  haveI : IsAffine (exists_isAffineOpen_nonempty B S hS R).choose.toScheme :=
    (exists_isAffineOpen_nonempty B S hS R).choose_spec.1
  haveI :=
    Stacks.Chow.isDominant_of_isOpenImmersion (exists_isAffineOpen_nonempty B S hS R).choose.ι
  (Stacks.Chow.functionFieldEquiv_openImmersion
      (exists_isAffineOpen_nonempty B S hS R).choose.ι).symm.toRingHom.comp
    (((exists_isAffineOpen_nonempty B S hS R).choose.toScheme.totalFractionRingToFunctionField
      (Nonempty.some (exists_isAffineOpen_nonempty B S hS R).choose_spec.2)).comp
      (rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R)
        (opensObject B S hS R (exists_isAffineOpen_nonempty B S hS R).choose)
        (yoneda.map (opensObjectι B S hS R (exists_isAffineOpen_nonempty B S hS R).choose))
        (isEtale_yoneda_map_opensObjectι B S hS R _)))

/-- The reading of a rational function of `h_R` on `R` is its reading through any nonempty affine
open. -/
theorem representedFunctionFieldMap_eq (W : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (hW : IsAffineOpen W) [Nonempty W]
    (f : rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R)) :
    representedFunctionFieldMap B S hS R f = affineOpenChartReading B S hS R W hW f := by
  have := (exists_isAffineOpen_nonempty B S hS R).choose_spec.2
  exact affineOpenChartReading_eq B S hS R hW
    (exists_isAffineOpen_nonempty B S hS R).choose_spec.1 f

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The point of `R` below the generic point of a prime divisor of `h_R` has codimension one. -/
theorem PrimeDivisor.coheight_pointsToScheme_genericPoint
    (Z : PrimeDivisor B S hS (yoneda.obj R)) :
    coheight (pointsToScheme B S hS R (Z.genericPoint B S hS _)) = 1 := by
  have hcod := (Classical.choose_spec Z.codimension_one).2
  change codimension (IrreducibleCloseds.closureSingleton (Z.genericPoint B S hS _)) = 1 at hcod
  rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, ← hcod,
    ← codimension_orderIsoOfHomeomorph (schemePointsHomeomorph B S hS R)]
  congr 1
  apply IrreducibleCloseds.ext
  rw [IrreducibleCloseds.coe_orderIsoOfHomeomorph]
  change closure {schemePointsHomeomorph B S hS R (Z.genericPoint B S hS _)} =
    schemePointsHomeomorph B S hS R '' closure {Z.genericPoint B S hS _}
  rw [Homeomorph.image_closure, Set.image_singleton]

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The morphism presented by the image in `h_R` of the canonical field point of an open `W` of
`R` at a point of `W` is a monomorphism. -/
theorem mono_fieldMorphism_map_canonicalSiteFieldPoint_opensObject
    (W : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (a : (BigFppfOver.toScheme B S hS).obj (opensObject B S hS R W)) :
    Mono (fieldMorphism B S hS (yoneda.obj R) (FieldValuedPoint.map B S hS _
      (yoneda.map (opensObjectι B S hS R W)) (canonicalSiteFieldPoint B S hS _ a))) := by
  rw [fieldMorphism_map_yoneda]
  have h := mono_fieldMorphism_canonicalSiteFieldPoint B S hS (opensObject B S hS R W) a
  rw [fieldMorphism_yoneda] at h
  exact mono_comp' h (mono_yoneda_map_of_mono_toScheme_map B S hS _ (inferInstanceAs (Mono W.ι)))

/-- **Stacks 0ENM on a represented space.** The order of vanishing of Stacks 0ENL of a nonzero
rational function `f` of `h_R` along a prime divisor `Z` is the order of vanishing, Divisors,
Definition 02RJ, of its reading on `R` at the point of `R` below the generic point of `Z`.

Read `f` on an affine open `W` of `R` containing that point: `W` is an affine elementary étale
neighbourhood of the generic point of `Z` whose scheme is integral, locally Noetherian and of
codimension one at the marked point, so Stacks 0ENM computes the order of vanishing on `W`, and
the order of vanishing on `W` is the one on `R`. -/
theorem PrimeDivisor.ord_eq_ord_representedFunctionFieldMap
    (hN : HasEtaleLocalProperty B S hS (yoneda.obj R) (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS (yoneda.obj R))
    (f : (rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R))ˣ) :
    (genericFractionEmbedding B S hS (isAlgebraicSpace_yoneda B S hS R)
        (isDecentSpace_yoneda B S hS R) (isIntegralSpace_yoneda B S hS R) hN).ord f Z =
      ((BigFppfOver.toScheme B S hS).obj R).ord (representedFunctionFieldMap B S hS R f)
        (pointsToScheme B S hS R (Z.genericPoint B S hS _)) := by
  set ξ := pointsToScheme B S hS R (Z.genericPoint B S hS _)
  obtain ⟨W, hW, hξW, -⟩ :=
    Scheme.exists_isAffineOpen_mem_le _ (show ξ ∈ (⊤ : Opens _) from trivial)
  have : Nonempty W := ⟨⟨ξ, hξW⟩⟩
  have : IsAffine (opensObject B S hS R W).left.1 := hW
  have : IsReduced (opensObject B S hS R W).left.1 := inferInstanceAs (IsReduced W.toScheme)
  have : IsLocallyNoetherian (opensObject B S hS R W).left.1 :=
    inferInstanceAs (IsLocallyNoetherian W.toScheme)
  have : AlgebraicGeometry.IsIntegral (opensObject B S hS R W).left.1 :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral W.toScheme)
  have : IsAffine W.toScheme := hW
  have := Stacks.Chow.isDominant_of_isOpenImmersion W.ι
  set c := yoneda.map (opensObjectι B S hS R W)
  set t := canonicalSiteFieldPoint B S hS (opensObject B S hS R W) ⟨ξ, hξW⟩
  have hmono : Mono (fieldMorphism B S hS _ t ≫ c) := by
    have := mono_fieldMorphism_map_canonicalSiteFieldPoint_opensObject B S hS R W ⟨ξ, hξW⟩
    rwa [fieldMorphism_map_yoneda, ← fieldMorphism_yoneda] at this
  have htpt : pointsToScheme B S hS _ (t.class B S hS _) = ⟨ξ, hξW⟩ :=
    pointsToScheme_class_canonicalSiteFieldPoint B S hS _ _
  have hx : pointsMap B S hS _ c (t.class B S hS _) = Z.genericPoint B S hS _ := by
    apply injective_pointsToScheme B S hS R
    rw [pointsToScheme_pointsMap, htpt]
    rfl
  let U := elementaryEtaleNeighborhoodOfMono B S hS (isAlgebraicSpace_yoneda B S hS R)
    (opensObject B S hS R W) c (isEtale_yoneda_map_opensObjectι B S hS R W) t hmono _ hx
  have : IsAffine U.scheme.left.1 := hW
  have : IsLocallyNoetherian U.scheme.left.1 := inferInstanceAs (IsLocallyNoetherian W.toScheme)
  have : AlgebraicGeometry.IsIntegral U.scheme.left.1 :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral W.toScheme)
  have hUpt : U.point = ⟨ξ, hξW⟩ := htpt
  have hcoh : coheight U.point = 1 := by
    rw [hUpt, ← PrimeDivisor.coheight_pointsToScheme_genericPoint B S hS R Z]
    exact (coheight_eq_of_isOpenImmersion W.ι (x := (⟨ξ, hξW⟩ : W.toScheme))).symm
  rw [ord_eq_scheme_ord_of_chart B S hS (isAlgebraicSpace_yoneda B S hS R)
    (isIntegralSpace_yoneda B S hS R) hN Z (isDecentSpace_yoneda B S hS R) U hcoh f,
    representedFunctionFieldMap_eq B S hS R W hW, affineOpenChartReading]
  change W.toScheme.ord (W.toScheme.totalFractionRingToFunctionField U.point _) U.point = _
  rw [Scheme.totalFractionRingToFunctionField_congr W.toScheme U.point (Nonempty.some ‹_›), hUpt]
  have h2 := Stacks.Chow.ord_functionFieldEquiv_openImmersion W.ι
    ((Stacks.Chow.functionFieldEquiv_openImmersion W.ι).symm
      (W.toScheme.totalFractionRingToFunctionField (Nonempty.some ‹_›)
        (rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R)
          (opensObject B S hS R W) c (isEtale_yoneda_map_opensObjectι B S hS R W) f)))
    (⟨ξ, hξW⟩ : W.toScheme)
  rwa [RingEquiv.apply_symm_apply] at h2

omit [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The point of `R` below the generic point of `h_R` is the generic point of `R`. -/
theorem pointsToScheme_genericPoint :
    pointsToScheme B S hS R (genericPoint B S hS (isAlgebraicSpace_yoneda B S hS R)
      (isIntegralSpace_yoneda B S hS R)) =
      _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) := by
  have h := (isGenericPoint_genericPoint B S hS (isAlgebraicSpace_yoneda B S hS R)
    (isIntegralSpace_yoneda B S hS R)).image (schemePointsHomeomorph B S hS R).continuous
  rw [Set.image_univ_of_surjective (schemePointsHomeomorph B S hS R).surjective,
    closure_univ] at h
  exact h.eq (genericPoint_spec _)

omit [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The image in `h_R` of the canonical field point of a nonempty open `W` of `R` at the generic
point of `W` represents the generic point of `h_R`. -/
theorem class_map_canonicalSiteFieldPoint_genericPoint
    (W : ((BigFppfOver.toScheme B S hS).obj R).Opens) [Nonempty W] :
    (FieldValuedPoint.map B S hS _ (yoneda.map (opensObjectι B S hS R W))
      (canonicalSiteFieldPoint B S hS (opensObject B S hS R W)
        (show (opensObject B S hS R W).left.1 from _root_.genericPoint W.toScheme))).class
      B S hS (yoneda.obj R) =
      genericPoint B S hS (isAlgebraicSpace_yoneda B S hS R) (isIntegralSpace_yoneda B S hS R) := by
  have := Stacks.Chow.isDominant_of_isOpenImmersion W.ι
  apply injective_pointsToScheme B S hS R
  rw [pointsToScheme_genericPoint, ← pointsMap_class, pointsToScheme_pointsMap,
    pointsToScheme_class_canonicalSiteFieldPoint]
  exact ((_root_.AlgebraicGeometry.tfae_isDominant_of_isIntegral W.ι).out 1 2).mp
    (inferInstance : _root_.AlgebraicGeometry.IsDominant W.ι)

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The canonical field point of an affine open `W` of `R` at a point `w` with field stalk,
pushed into `h_R`, factors through the spectrum of the total ring of fractions of `Γ(W, 𝒪_W)`
along the reading `Q(Γ(W, 𝒪_W)) → κ(w)`. -/
theorem exists_hom_totalFractionObject_canonicalSiteFieldPoint
    (W : ((BigFppfOver.toScheme B S hS).obj R).Opens) [IsAffine W.toScheme]
    [IsAffine (opensObject B S hS R W).left.1] (w : W.toScheme)
    (ht : IsField (W.toScheme.presheaf.stalk w)) :
    ∃ g : (FieldValuedPoint.map B S hS _ (yoneda.map (opensObjectι B S hS R W))
        (canonicalSiteFieldPoint B S hS (opensObject B S hS R W)
          (show (opensObject B S hS R W).left.1 from w))).siteObject B S hS (yoneda.obj R) ⟶
        totalFractionObject B S hS (opensObject B S hS R W),
      (BigFppfOver.toScheme B S hS).map g =
        Spec.map (CommRingCat.ofHom (Scheme.totalFractionRingToResidueField w ht :
          FractionRing Γ(W.toScheme, ⊤) →+* (FieldValuedPoint.map B S hS _
            (yoneda.map (opensObjectι B S hS R W)) (canonicalSiteFieldPoint B S hS
              (opensObject B S hS R W) (show (opensObject B S hS R W).left.1 from w))).carrier)) ∧
      g ≫ totalFractionObjectMap B S hS (opensObject B S hS R W) =
        (canonicalSiteFieldPoint B S hS (opensObject B S hS R W)
          (show (opensObject B S hS R W).left.1 from w)).siteHom B S hS := by
  set q := canonicalSiteFieldPoint B S hS (opensObject B S hS R W)
    (show (opensObject B S hS R W).left.1 from w)
  set p := FieldValuedPoint.map B S hS _ (yoneda.map (opensObjectι B S hS R W)) q
  set ρ : FractionRing Γ(W.toScheme, ⊤) →+* p.carrier :=
    Scheme.totalFractionRingToResidueField w ht
  have hq : B.inclusion.map (q.siteHom B S hS).left = W.toScheme.fromSpecResidueField w :=
    map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _
  have hfac : W.toScheme.fromSpecResidueField w =
      Spec.map (CommRingCat.ofHom ρ) ≫ W.toScheme.fromSpecTotalFractionRing :=
    Scheme.fromSpecResidueField_eq_SpecMap_comp_fromSpecTotalFractionRing w ht
  refine ⟨Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ρ))) ?_, rfl, ?_⟩
  · apply ObjectProperty.hom_ext
    have hw := congrArg (fun k => k.hom) (Over.w (q.siteHom B S hS))
    change B.inclusion.map (q.siteHom B S hS).left ≫ _ = _ at hw
    rw [hq] at hw
    unfold opensObject at hw ⊢
    change Spec.map (CommRingCat.ofHom ρ) ≫ W.toScheme.fromSpecTotalFractionRing ≫ _ = _
    rwa [← Category.assoc, ← hfac]
  · apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom ρ) ≫ W.toScheme.fromSpecTotalFractionRing = _
    exact hfac.symm.trans hq.symm

/-- **The reading of rational functions of `h_R` on `R` is an isomorphism.** Read through an
affine open `W`, the reading followed by the residue map at the generic point of `W` is the
evaluation of Stacks 0END at the generic point of `h_R` along the monomorphism
`Spec κ(η) → W → R`, and that evaluation is bijective. -/
theorem bijective_representedFunctionFieldMap :
    Function.Bijective (representedFunctionFieldMap B S hS R) := by
  obtain ⟨W, hW, hne⟩ := exists_isAffineOpen_nonempty B S hS R
  have := hne
  have heq : ⇑(representedFunctionFieldMap B S hS R) = affineOpenChartReading B S hS R W hW :=
    funext (representedFunctionFieldMap_eq B S hS R W hW)
  rw [heq]
  have : IsAffine (opensObject B S hS R W).left.1 := hW
  have : IsReduced (opensObject B S hS R W).left.1 := inferInstanceAs (IsReduced W.toScheme)
  have : IsLocallyNoetherian (opensObject B S hS R W).left.1 :=
    inferInstanceAs (IsLocallyNoetherian W.toScheme)
  have : IsAffine W.toScheme := hW
  have := Stacks.Chow.isDominant_of_isOpenImmersion W.ι
  set w₀ : W.toScheme := _root_.genericPoint W.toScheme
  have ht : IsField (W.toScheme.presheaf.stalk w₀) := Field.toIsField W.toScheme.functionField
  set c := yoneda.map (opensObjectι B S hS R W)
  set q := canonicalSiteFieldPoint B S hS (opensObject B S hS R W)
    (show (opensObject B S hS R W).left.1 from w₀)
  set p := FieldValuedPoint.map B S hS _ c q
  set ρ : FractionRing Γ(W.toScheme, ⊤) →+* p.carrier :=
    Scheme.totalFractionRingToResidueField w₀ ht
  obtain ⟨g, hgS, hgq⟩ :=
    exists_hom_totalFractionObject_canonicalSiteFieldPoint B S hS R W w₀ ht
  have hmono := mono_fieldMorphism_map_canonicalSiteFieldPoint_opensObject B S hS R W
    (show (opensObject B S hS R W).left.1 from w₀)
  have hp := class_map_canonicalSiteFieldPoint_genericPoint B S hS R W
  have key := evalRingHom_eq_rationalFunctionsToTotalFractionRing B S hS
    (isAlgebraicSpace_yoneda B S hS R) (isIntegralSpace_yoneda B S hS R)
    (opensObject B S hS R W) c (isEtale_yoneda_map_opensObjectι B S hS R W) p hp ρ g
    hgS (by rw [hgq]; exact (fieldMorphism_map_yoneda B S hS _ c q).symm)
  have hρ : ∀ x, ρ x = (W.toScheme.residue w₀).hom
      (W.toScheme.totalFractionRingToFunctionField (Nonempty.some ‹Nonempty W›) x) := by
    intro x
    rw [Scheme.totalFractionRingToFunctionField_congr W.toScheme _ w₀]
    exact RingHom.congr_fun (Scheme.totalFractionRingToResidueField_genericPoint W.toScheme ht) x
  unfold affineOpenChartReading
  refine (RingEquiv.bijective _).comp ?_
  refine (Function.Bijective.of_comp_iff'
    (Scheme.bijective_residue_of_isField (T := W.toScheme) (z := w₀) ht) _).1 ?_
  have hfun : ⇑(W.toScheme.residue w₀).hom ∘
      (fun x => W.toScheme.totalFractionRingToFunctionField (Nonempty.some ‹Nonempty W›)
        (rationalFunctionsToTotalFractionRing B S hS (isAlgebraicSpace_yoneda B S hS R)
          (opensObject B S hS R W) c (isEtale_yoneda_map_opensObjectι B S hS R W) x)) =
      ⇑(evalRingHom B S hS (isAlgebraicSpace_yoneda B S hS R) (isIntegralSpace_yoneda B S hS R)
        p hp) := by
    funext x
    rw [Function.comp_apply, key]
    exact (hρ _).symm
  rw [hfun]
  exact evalRingHom_bijective B S hS (isAlgebraicSpace_yoneda B S hS R)
    (isIntegralSpace_yoneda B S hS R) p hp hmono

/-- **`R(h_R) ≅ R(R)`.** The ring of rational functions of the algebraic space represented by an
integral, locally Noetherian scheme `R` is the function field of `R`, by the reading through an
affine open. -/
def representedFunctionFieldEquiv :
    rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R) ≃+*
      ((BigFppfOver.toScheme B S hS).obj R).functionField :=
  RingEquiv.ofBijective _ (bijective_representedFunctionFieldMap B S hS R)

/-- The equivalence `representedFunctionFieldEquiv` agrees with `representedFunctionFieldMap`. -/
@[simp]
theorem representedFunctionFieldEquiv_apply
    (f : rationalFunctions B S hS (isAlgebraicSpace_yoneda B S hS R)) :
    representedFunctionFieldEquiv B S hS R f = representedFunctionFieldMap B S hS R f :=
  rfl

end AlgebraicGeometry.Space

end
