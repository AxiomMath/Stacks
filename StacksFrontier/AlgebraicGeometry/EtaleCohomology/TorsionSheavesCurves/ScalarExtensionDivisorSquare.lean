module

public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreOrdBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionSmoothCurve

/-!
# The divisor sequence of a smooth curve under extension of the base field

Let `X` be a smooth curve over an algebraically closed field `k`, `k'/k` an algebraically closed
extension, `X' = X_{k'}` and `p : X' ⟶ X` the projection. The orders of vanishing on étale
`X`-schemes and on their base changes to `X'` are compared pointwise: at a point of `U ×_X X'`
over a closed point of `X` the order of vanishing of a pulled back function is that of the
function (the maximal ideal is unchanged, `map_maximalIdeal_stalk_pullback_scalarExtensionFst`),
and at a point over the generic point of `X` it is zero (the local ring downstairs is a field).

## Main results

* `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint_scalarExtension`
* `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint_scalarExtension_eq_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order IsLocalRing AlgebraicGeometry
  TopologicalSpace AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

/-! ### Instances on the scalar extension -/

/-- A curve over `k`, extended to `k'`, is integral. -/
instance isIntegral_scalarExtension' [IsCurve k g] : IsIntegral (scalarExtension k k' g) :=
  isIntegral_scalarExtension k k' g

/-- The extension `X_{k'} ⟶ Spec k'` of a curve over `k` is a curve over `k'`. -/
instance isCurve_scalarExtensionSnd : IsCurve k' (scalarExtensionSnd k k' g) :=
  isCurve_scalarExtension k k' g

/-- The extension `X_{k'} ⟶ Spec k'` of a smooth curve over `k` is smooth. -/
instance smooth_scalarExtensionSnd : Smooth (scalarExtensionSnd k k' g) :=
  smooth_scalarExtension k k' g

/-- The projection `X_{k'} ⟶ X` is flat. -/
instance flat_scalarExtensionFst : Flat (scalarExtensionFst k k' g) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  infer_instance

/-- A smooth curve over `k`, extended to `k'`, is normal. -/
instance isNormal_scalarExtension : IsNormal (scalarExtension k k' g) :=
  isNormal_of_isCurve_of_smooth (scalarExtensionSnd k k' g)

/-- A curve over `k`, extended to `k'`, is locally Noetherian. -/
instance isLocallyNoetherian_scalarExtension :
    IsLocallyNoetherian (scalarExtension k k' g) :=
  isLocallyNoetherian_of_isCurve (scalarExtensionSnd k k' g)

/-- An étale scheme over a locally Noetherian scheme is locally Noetherian. -/
local instance isLocallyNoetherian_etale_left' {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (U : Y.Etale) : IsLocallyNoetherian U.left :=
  isLocallyNoetherian_etale_left Y U

include g in
/-- The generic point of a curve is not closed. -/
theorem genericPoint_ne_of_isClosed {x : X} (hx : IsClosed ({x} : Set X)) :
    x ≠ genericPoint X := by
  rintro rfl
  have h1 := IsCurve.topologicalKrullDim_eq_one g
  have : ∀ y : X, y = genericPoint X := fun y =>
    (hx.closure_subset_iff.2 le_rfl) ((genericPoint_spec X).def ▸ Set.mem_univ y)
  have : Subsingleton X := ⟨fun a b => (this a).trans (this b).symm⟩
  have hu : Subsingleton (TopologicalSpace.IrreducibleCloseds X) := ⟨fun A B => by
    ext y
    have hA : A.carrier = Set.univ := Set.eq_univ_of_forall fun z =>
      (Subsingleton.elim z (A.isIrreducible.nonempty.some)) ▸ A.isIrreducible.nonempty.some_mem
    have hB : B.carrier = Set.univ := Set.eq_univ_of_forall fun z =>
      (Subsingleton.elim z (B.isIrreducible.nonempty.some)) ▸ B.isIrreducible.nonempty.some_mem
    show y ∈ A.carrier ↔ y ∈ B.carrier
    rw [hA, hB]⟩
  have : Unique (TopologicalSpace.IrreducibleCloseds X) :=
    { default := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩,
      uniq := fun _ => hu.elim _ _ }
  have h0 : topologicalKrullDim X = 0 := Order.krullDim_eq_zero_of_unique
  rw [h0] at h1
  exact zero_ne_one h1

/-! ### The pointwise comparison -/

variable [IsNormal X] [IsLocallyNoetherian X]

/-- The generic point square of the projection `X_{k'} ⟶ X`. -/
theorem genericPointSquare_scalarExtension :
    genericPointInclusion (scalarExtension k k' g) ≫ scalarExtensionFst k k' g =
      genericPointMap (scalarExtensionFst k k' g) ≫ genericPointInclusion X :=
  genericPointInclusion_comp_eq_genericPointMap_comp _

/-- **The restriction map of generic fibres** `(U ×_X X') ×_{X'} η' ⟶ U ×_X η` along which the
morphism `i_* 𝐆_{m,η} ⟶ p_* i'_* 𝐆_{m,η'}` restricts invertible functions. -/
abbrev genericFibreScalarExtensionMap (U : X.Etale) :
    pullback ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom
        (genericPointInclusion (scalarExtension k k' g)) ⟶
      pullback U.hom (genericPointInclusion X) :=
  smallEtaleBaseChangeSquareLeft (genericPointSquare_scalarExtension g k') U ≫ pullback.fst _ _

/-- The restriction map of generic fibres, followed by the projection to `U`, is the projection
`(U ×_X X') ×_{X'} η' ⟶ U ×_X X'` followed by the projection to `U`. -/
theorem genericFibreScalarExtensionMap_fst (U : X.Etale) :
    genericFibreScalarExtensionMap g k' U ≫ pullback.fst U.hom (genericPointInclusion X) =
      pullback.fst _ _ ≫ pullback.fst U.hom (scalarExtensionFst k k' g) :=
  (Category.assoc _ _ _).trans
    (smallEtaleBaseChangeSquareLeft_fst_fst (genericPointSquare_scalarExtension g k') U)

/-- **Orders of vanishing over a closed point are unchanged by extension of the base field**: at a
point `y` of `U ×_X X'` over a closed point of `X`, the order of vanishing of the restriction of an
invertible function on the generic fibre of `U` is its order of vanishing at the image of `y`. -/
theorem etaleGenericFibreOrdOfPoint_scalarExtension (U : X.Etale)
    (y : ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left)
    (hx : IsClosed ({U.hom.base ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y)} :
      Set X))
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    etaleGenericFibreOrdOfPoint ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U) y
        (Additive.ofMul
          (Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom a)) =
      etaleGenericFibreOrdOfPoint U ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y)
        (Additive.ofMul a) := by
  have : Etale U.hom := U.prop
  have : @Flat _ ((Functor.fromPUnit X).obj U.right) (scalarExtensionFst k k' g) :=
    flat_scalarExtensionFst g k'
  have : @Flat ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left U.left
      (pullback.fst U.hom (scalarExtensionFst k k' g)) :=
    inferInstanceAs (Flat (pullback.fst U.hom (scalarExtensionFst k k' g)))
  have : IsLocallyNoetherian
      ((𝟭 Scheme).obj ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left) :=
    isLocallyNoetherian_etale_left _ _
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) := isLocallyNoetherian_etale_left _ _
  have : Etale ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom :=
    ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).prop
  have : LocallyOfFiniteType (U.hom ≫ g) := inferInstance
  have hres : Function.Surjective
      (U.hom.residueFieldMap ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y)) :=
    (Stacks.Curves.residueFieldMap_bijective_of_etale_closed g (U.hom ≫ g) U.hom
      ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y) hx).2
  have hmax := map_maximalIdeal_stalk_pullback_scalarExtensionFst g k' U.hom y hx hres
  have hy' : ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom.base y ≠
      genericPoint (scalarExtension k k' g) := by
    refine genericPoint_ne_of_isClosed (scalarExtensionSnd k k' g)
      (isClosed_singleton_of_scalarExtensionFst_eq g k' hx ?_)
    exact congrArg (fun φ : ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left ⟶ X =>
      φ.base y) pullback.condition.symm
  have hcoh : coheight ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y) = coheight y :=
    (coheight_eq_one_of_etale_of_isCurve g U.hom (genericPoint_ne_of_isClosed g hx)).trans
      (coheight_eq_one_of_etale_of_isCurve (scalarExtensionSnd k k' g)
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom hy').symm
  exact genericFibreOrdOfPoint_appTop_of_square (X := X) (X' := scalarExtension k k' g)
    ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom U.hom
    (pullback.fst U.hom (scalarExtensionFst k k' g)) (genericFibreScalarExtensionMap g k' U)
    (genericFibreScalarExtensionMap_fst g k' U) y hmax hcoh a

/-- **Orders of vanishing over the generic point vanish**: at a point `y` of `U ×_X X'` over the
generic point of `X` the restriction of an invertible function on the generic fibre of `U` has
order zero, the local ring of `U` at the image of `y` being a field. -/
theorem etaleGenericFibreOrdOfPoint_scalarExtension_eq_zero (U : X.Etale)
    (y : ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left)
    (hx : U.hom.base ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y) = genericPoint X)
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    etaleGenericFibreOrdOfPoint ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U) y
        (Additive.ofMul
          (Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom a)) =
      0 := by
  have : Etale U.hom := U.prop
  have : @Flat _ ((Functor.fromPUnit X).obj U.right) (scalarExtensionFst k k' g) :=
    flat_scalarExtensionFst g k'
  have : @Flat ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left U.left
      (pullback.fst U.hom (scalarExtensionFst k k' g)) :=
    inferInstanceAs (Flat (pullback.fst U.hom (scalarExtensionFst k k' g)))
  have : IsLocallyNoetherian
      ((𝟭 Scheme).obj ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left) :=
    isLocallyNoetherian_etale_left _ _
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) := isLocallyNoetherian_etale_left _ _
  have : Etale ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom :=
    ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).prop
  have hetale :=
    ((etaleAt_tfae U.hom ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y)).out 1 7).mp
      ((etale_iff_forall_etaleAt U.hom).mp inferInstance _)
  have hη : ∀ z : X, z = genericPoint X → maximalIdeal (X.presheaf.stalk z) = ⊥ := by
    rintro _ rfl
    exact IsLocalRing.maximalIdeal_eq_bot
  have hbot : maximalIdeal (((𝟭 Scheme).obj U.left).presheaf.stalk
      ((pullback.fst U.hom (scalarExtensionFst k k' g)).base y)) = ⊥ := by
    rw [← hetale.2.1]
    exact (congrArg (Ideal.map _) (hη _ hx)).trans Ideal.map_bot
  exact genericFibreOrdOfPoint_appTop_eq_zero_of_square (X := X) (X' := scalarExtension k k' g)
    ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).hom U.hom
    (pullback.fst U.hom (scalarExtensionFst k k' g)) (genericFibreScalarExtensionMap g k' U)
    (genericFibreScalarExtensionMap_fst g k' U) y hbot a

/-! ### The comparison on the summands -/

/-- The divisor at `x`, read as a locally constant function on the fibre over `x`. -/
theorem integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint
    {Y : Scheme.{u}} [IsIntegral Y] [IsNormal Y] (V : Y.Etale) [IsLocallyNoetherian V.left]
    (y : Y) (a : Additive ((Γ(pullback V.hom (genericPointInclusion Y), ⊤))ˣ)) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y V).hom
        (integerSkyscraperDivisorOfPoint.{u, v} V y a) = residueFibreOrdOfPoint.{u, v} V y a := by
  rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply, ← ConcreteCategory.comp_apply,
    Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- A point of the fibre of `U ×_Y X'` over `x'` maps, through `U`, to the image of `x'` in `Y`. -/
private theorem base_pullback_fst_fromSpecResidueField_comp_hom {Y X' : Scheme.{u}} (f : X' ⟶ Y)
    (U : Y.Etale) (x' : X')
    (y : ↥(pullback ((smallEtaleBaseChange f).obj U).hom (X'.fromSpecResidueField x'))) :
    U.hom.base ((pullback.fst U.hom f).base
      ((pullback.fst ((smallEtaleBaseChange f).obj U).hom (X'.fromSpecResidueField x')).base y)) =
      f.base x' :=
  (congrArg (fun φ : pullback U.hom f ⟶ Y =>
    φ.base ((pullback.fst ((smallEtaleBaseChange f).obj U).hom
      (X'.fromSpecResidueField x')).base y)) pullback.condition).trans
    (congrArg f.base
      (hom_base_pullback_fst_fromSpecResidueField x' ((smallEtaleBaseChange f).obj U) y))

/-- **On the summand at a closed point, the third component matches the divisors**: for `x'` over
a closed point of `X`, pulling back the divisor at `p x'` of an invertible function on the generic
fibre of `U` gives the divisor at `x'` of its restriction to the generic fibre of `U ×_X X'`. -/
theorem integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint (U : X.Etale)
    (x' : scalarExtension k k' g) (hx : IsClosed ({(scalarExtensionFst k k' g).base x'} : Set X))
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    (integerSkyscraperDirectImageMap.{u, v} (scalarExtensionFst k k' g) x').hom.app (op U)
        (integerSkyscraperDivisorOfPoint.{u, v} U ((scalarExtensionFst k k' g).base x')
          (Additive.ofMul a)) =
      integerSkyscraperDivisorOfPoint.{u, v}
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U) x'
        (Additive.ofMul
          (Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom a)) := by
  refine (ConcreteCategory.bijective_of_isIso
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} (scalarExtension k k' g) x'
      ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)).hom).1 ?_
  rw [integerSkyscraperDirectImageMap_app,
    integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint,
    integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint]
  refine LocallyConstant.ext fun y => ?_
  rw [LocallyConstant.coe_comap_apply, residueFibreOrdOfPoint_apply, residueFibreOrdOfPoint_apply]
  have hpt := congrArg (fun φ => φ.base y) (smallEtaleBaseChangeSquareLeft_fst_fst
    ((scalarExtensionFst k k' g).SpecMap_residueFieldMap_fromSpecResidueField x').symm U)
  have hx' := (base_pullback_fst_fromSpecResidueField_comp_hom _ U x' y).symm ▸ hx
  refine congrArg ULift.up (Eq.trans ?_
    (etaleGenericFibreOrdOfPoint_scalarExtension g k' U _ hx' a).symm)
  refine congrArg (fun z => etaleGenericFibreOrdOfPoint U z (Additive.ofMul a)) ?_
  refine Eq.trans ?_ (hpt.trans ?_)
  · rfl
  · rfl

/-- **On the summand at a point over the generic point, the divisor of a restricted function
vanishes.** -/
theorem integerSkyscraperDivisorOfPoint_scalarExtension_eq_zero (U : X.Etale)
    (x' : scalarExtension k k' g) (hx : (scalarExtensionFst k k' g).base x' = genericPoint X)
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    integerSkyscraperDivisorOfPoint.{u, v}
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U) x'
        (Additive.ofMul
          (Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom a)) =
      0 := by
  refine (ConcreteCategory.bijective_of_isIso
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} (scalarExtension k k' g) x'
      ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)).hom).1 ?_
  rw [integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint, map_zero]
  refine LocallyConstant.ext fun y => ?_
  rw [residueFibreOrdOfPoint_apply]
  exact congrArg ULift.up (etaleGenericFibreOrdOfPoint_scalarExtension_eq_zero g k' U _
    ((base_pullback_fst_fromSpecResidueField_comp_hom _ U x' y).trans hx) a)

/-! ### The third component on sections -/

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- The third component of the comparison on sections, summand by summand: the summand at `x` goes
to the summand at `σ x` by pullback of locally constant functions. -/
def closedPointDivisorDirectImageSummandMap (U : X.Etale) (x : closedPoints X) :
    (closedPointSkyscraper.{u, v} X x).obj.obj (op U) →+
      (closedPointSkyscraper.{u, v} (scalarExtension k k' g)
        (scalarExtensionClosedPoint g k' x)).obj.obj
          (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)) :=
  ((eqToHom (by rw [closedPointSkyscraper, scalarExtensionFst_scalarExtensionClosedPoint]) ≫
    integerSkyscraperDirectImageMap.{u, v} (scalarExtensionFst k k' g)
      (scalarExtensionClosedPoint g k' x).1).hom.app (op U)).hom

/-- The third component of the comparison on families of sections of the summands. -/
def closedPointDivisorDirectImageDirectSum (U : X.Etale) :
    DirectSum ↥(closedPoints X)
        (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U)) →+
      DirectSum ↥(closedPoints (scalarExtension k k' g))
        (fun x' ↦ (closedPointSkyscraper.{u, v} (scalarExtension k k' g) x').obj.obj
          (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U))) :=
  letI : DecidableEq ↥(closedPoints X) := Classical.decEq _
  letI : DecidableEq ↥(closedPoints (scalarExtension k k' g)) := Classical.decEq _
  DirectSum.toAddMonoid fun x =>
    (DirectSum.of _ (scalarExtensionClosedPoint g k' x)).comp
      (closedPointDivisorDirectImageSummandMap g k' U x)

/-- **The third component on sections is the summandwise map.** -/
theorem closedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum (U : X.Etale)
    (f : DirectSum ↥(closedPoints X)
      (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U))) :
    ((closedPointDivisorDirectImageMap.{u, v} (scalarExtensionFst k k' g)
        (scalarExtensionClosedPoint g k')
        (scalarExtensionFst_scalarExtensionClosedPoint g k')).hom.app
          (op U)).hom (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U f) =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} (scalarExtension k k' g)
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)
        (closedPointDivisorDirectImageDirectSum g k' U f) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let : DecidableEq ↥(closedPoints (scalarExtension k k' g)) := Classical.decEq _
  have key : (((closedPointDivisorDirectImageMap.{u, v} (scalarExtensionFst k k' g)
        (scalarExtensionClosedPoint g k')
        (scalarExtensionFst_scalarExtensionClosedPoint g k')).hom.app
          (op U)).hom).comp (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U) =
      (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} (scalarExtension k k' g)
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)).comp
        (closedPointDivisorDirectImageDirectSum g k' U) := by
    refine DirectSum.addHom_ext fun x t => ?_
    have l1 : closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U
        (DirectSum.of _ x t) = ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U)).hom t := by
      rw [closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
    have r1 : closedPointDivisorDirectImageDirectSum g k' U (DirectSum.of _ x t) =
        DirectSum.of _ (scalarExtensionClosedPoint g k' x)
          (closedPointDivisorDirectImageSummandMap g k' U x t) := by
      rw [closedPointDivisorDirectImageDirectSum, DirectSum.toAddMonoid_of]
      rfl
    have r2 : ∀ s, closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} (scalarExtension k k' g)
        ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)
          (DirectSum.of _ (scalarExtensionClosedPoint g k' x) s) =
        ((closedPointDivisorSheaf.ι.{u, v} (scalarExtension k k' g)
          (scalarExtensionClosedPoint g k' x)).hom.app
            (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U))).hom s := fun s => by
      rw [closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
    have main := congrArg (fun φ => (φ.hom.app (op U)).hom t)
      (ι_closedPointDivisorDirectImageMap.{u, v} (scalarExtensionFst k k' g)
        (scalarExtensionClosedPoint g k') (scalarExtensionFst_scalarExtensionClosedPoint g k') x)
    refine (AddMonoidHom.comp_apply _ _ _).trans ((congrArg _ l1).trans ?_)
    refine Eq.trans ?_ (AddMonoidHom.comp_apply _ _ _).symm
    rw [r1]
    exact main.trans (r2 _).symm
  exact DFunLike.congr_fun key f

/-- Transport of the divisor at a point along an equality of points. -/
theorem eqToHom_app_integerSkyscraperDivisorOfPoint {Y : Scheme.{u}} [IsIntegral Y] [IsNormal Y]
    (U : Y.Etale) [IsLocallyNoetherian U.left] {x₁ x₂ : Y} (h : x₁ = x₂)
    (E : integerSkyscraper.{u, v} Y x₁ = integerSkyscraper.{u, v} Y x₂)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ)) :
    ((eqToHom E).hom.app (op U)).hom (integerSkyscraperDivisorOfPoint.{u, v} U x₁ a) =
      integerSkyscraperDivisorOfPoint.{u, v} U x₂ a := by
  subst h
  rfl

/-- **The third component carries the divisor of a function to the divisor of its restriction.** -/
theorem closedPointDivisorDirectImageDirectSum_closedPointDivisorSections (U : X.Etale)
    [NoetherianSpace U.left]
    [NoetherianSpace ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left]
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    closedPointDivisorDirectImageDirectSum g k' U
        (closedPointDivisorSections.{u, v} U (Additive.ofMul a)) =
      closedPointDivisorSections.{u, v} ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)
        (Additive.ofMul
          (Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom a)) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let : DecidableEq ↥(closedPoints (scalarExtension k k' g)) := Classical.decEq _
  let : ∀ (x : closedPoints X) (v : (closedPointSkyscraper.{u, v} X x).obj.obj (op U)),
    Decidable (v ≠ 0) := fun _ _ => Classical.propDecidable _
  have hΦ : ∀ (f : DirectSum ↥(closedPoints X)
      (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U)))
      (x' : closedPoints (scalarExtension k k' g)),
      closedPointDivisorDirectImageDirectSum g k' U f x' =
        f.sum (fun x v => DirectSum.of (fun x' ↦ (closedPointSkyscraper.{u, v}
          (scalarExtension k k' g) x').obj.obj
            (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)))
            (scalarExtensionClosedPoint g k' x)
            (closedPointDivisorDirectImageSummandMap g k' U x v) x') := by
    intro f x'
    rw [closedPointDivisorDirectImageDirectSum, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply,
      DFinsupp.sumAddHom_apply, DFinsupp.sum_apply]
    rfl
  refine DFinsupp.ext fun x' =>
    (hΦ _ x').trans (Eq.trans ?_ (closedPointDivisorSections_apply _ _ x').symm)
  by_cases hx' : ∃ x, scalarExtensionClosedPoint g k' x = x'
  · obtain ⟨x₀, rfl⟩ := hx'
    unfold DFinsupp.sum
    rw [Finset.sum_eq_single x₀]
    · refine (DirectSum.of_eq_same _ _).trans ?_
      have hf : closedPointDivisorSections.{u, v} U (Additive.ofMul a) x₀ =
          integerSkyscraperDivisorOfPoint.{u, v} U x₀.1 (Additive.ofMul a) :=
        closedPointDivisorSections_apply _ _ x₀
      refine (congrArg (closedPointDivisorDirectImageSummandMap g k' U x₀) hf).trans ?_
      refine Eq.trans ?_ (integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint g k' U
        (scalarExtensionClosedPoint g k' x₀).1 ?_ a)
      · refine congrArg (fun t => ((integerSkyscraperDirectImageMap.{u, v}
          (scalarExtensionFst k k' g)
          (scalarExtensionClosedPoint g k' x₀).1).hom.app (op U)).hom t) ?_
        exact eqToHom_app_integerSkyscraperDivisorOfPoint (U := U)
          (h := (scalarExtensionFst_scalarExtensionClosedPoint g k' x₀).symm) (E := _) (a := _)
      · rw [scalarExtensionFst_scalarExtensionClosedPoint]
        exact x₀.2
    · intro x _ hx
      exact DirectSum.of_eq_of_ne _ _ _
        (fun h => hx (injective_scalarExtensionClosedPoint g k' h).symm)
    · intro hx
      have h0 := DFinsupp.notMem_support_iff.mp hx
      have e1 : closedPointDivisorDirectImageSummandMap g k' U x₀ 0 = 0 := map_zero _
      refine (congrArg (fun v => DirectSum.of (fun x' ↦ (closedPointSkyscraper.{u, v}
        (scalarExtension k k' g) x').obj.obj
          (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)))
          (scalarExtensionClosedPoint g k' x₀) (closedPointDivisorDirectImageSummandMap g k' U x₀ v)
            (scalarExtensionClosedPoint g k' x₀)) h0).trans ?_
      refine (congrArg (fun v => DirectSum.of (fun x' ↦ (closedPointSkyscraper.{u, v}
        (scalarExtension k k' g) x').obj.obj
          (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U)))
          (scalarExtensionClosedPoint g k' x₀) v (scalarExtensionClosedPoint g k' x₀)) e1).trans ?_
      exact DirectSum.of_eq_same _ _
  · unfold DFinsupp.sum
    rw [Finset.sum_eq_zero fun x _ => by
      beta_reduce
      exact DirectSum.of_eq_of_ne _ _ _ (fun h => hx' ⟨x, by first | exact h | exact h.symm⟩)]
    refine (integerSkyscraperDivisorOfPoint_scalarExtension_eq_zero g k' U x'.1 ?_ a).symm
    by_contra hne
    have hcl := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X
      (IsCurve.topologicalKrullDim_eq_one g) hne
    exact hx' ⟨⟨_, hcl⟩, (Subtype.ext (eq_scalarExtensionClosedPoint g k' ⟨_, hcl⟩ rfl)).symm⟩

/-! ### The second commuting square -/

omit [IsNormal X] [IsLocallyNoetherian X] in
/-- **On sections over an étale `X`-scheme with Noetherian space, the second map of Stacks 03RI is
the family of orders of vanishing.** -/
theorem divisorSequenceSecondMap_app_of_noetherianSpace {Y : Scheme.{u}} [IsIntegral Y]
    [IsNormal Y] [IsLocallyNoetherian Y] (V : Y.Etale) [NoetherianSpace V.left]
    (z : ToType (((genericPointDirectImage.{u, v} Y).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec Y.functionField))).obj.obj (op V))) :
    ((divisorSequenceSecondMap.{u, v} Y).hom.app (op V)).hom z =
      closedPointDivisorSheafSection.{u, v} V z.down := by
  refine Functor.IsCoverDense.ext (G := Scheme.AffineEtale.Spec Y)
    ((sheafCompose _ (forget AddCommGrpCat.{max (u + 1) v})).obj
      (closedPointDivisorSheaf.{u, v} Y)) _ fun W f => ?_
  have : IsLocallyNoetherian ((Scheme.AffineEtale.Spec Y).obj W).left :=
    isLocallyNoetherian_etale_left Y _
  have : NoetherianSpace ((Scheme.AffineEtale.Spec Y).obj W).left :=
    noetherianSpace_affineEtale_left Y W
  show ((closedPointDivisorSheaf.{u, v} Y).obj.map f.op).hom _ =
    ((closedPointDivisorSheaf.{u, v} Y).obj.map f.op).hom _
  rw [← ConcreteCategory.comp_apply, ← (divisorSequenceSecondMap.{u, v} Y).hom.naturality,
    ConcreteCategory.comp_apply]
  refine (DFunLike.congr_fun (congrArg (fun φ => ConcreteCategory.hom φ)
    (divisorSequenceSecondMap_hom_app.{u, v} Y W)) _).trans ?_
  refine (affineEtaleDivisorApp_apply.{u, v} Y W _).trans ?_
  refine (congrArg (closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec Y).obj W))
    (genericPointDirectImage_multiplicativeSheaf_map_down.{u, v} Y f z)).trans ?_
  exact (closedPointDivisorSheafSection_map.{u, v} f (Additive.toMul z.down)).symm

omit [IsNormal X] [IsLocallyNoetherian X] in
/-- **The base change to `X_{k'}` of a quasi-compact étale `X`-scheme has a Noetherian space.** -/
theorem noetherianSpace_smallEtaleBaseChange_scalarExtension (U : X.Etale) [CompactSpace U.left] :
    NoetherianSpace ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left := by
  have : IsLocallyNoetherian ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left :=
    isLocallyNoetherian_etale_left _ _
  have : @QuasiCompact _ ((Functor.fromPUnit X).obj U.right) (scalarExtensionFst k k' g) := by
    have : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := inferInstance
    exact inferInstanceAs (QuasiCompact (pullback.fst g _))
  have : @QuasiCompact ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left U.left
      (pullback.fst U.hom (scalarExtensionFst k k' g)) :=
    inferInstanceAs (QuasiCompact (pullback.fst U.hom (scalarExtensionFst k k' g)))
  have : CompactSpace ((𝟭 Scheme).obj U.left) := inferInstanceAs (CompactSpace U.left)
  have : CompactSpace ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst U.hom (scalarExtensionFst k k' g))
  have : AlgebraicGeometry.IsNoetherian
      ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left := ⟨⟩
  infer_instance

end Stacks.EtaleCohomology

end
