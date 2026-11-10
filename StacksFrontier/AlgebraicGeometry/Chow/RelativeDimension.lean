module

public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A dimension function propagates along a locally finite-type morphism

Let `S` be a locally Noetherian, universally catenary scheme carrying a dimension function
`δ`, and let `f : X ⟶ S` be locally of finite type. Then

  `x ↦ δ (f x) + trdeg_{κ(f x)} κ(x)`

— the function `Stacks.Chow.relativeDimension` — is again a dimension function, on `X` this
time. This is Stacks 02JW, the hypothesis under which the whole of chapter 42 assigns a
delta-dimension to the integral closed subschemes of a scheme over `S`.

The two clauses to check are local along a specialization `x ⤳ y`. Restricting to the integral
closed subscheme `T = closure {x}` of `X` and to `U = closure {f x}` of `S` turns `f` into a
dominant morphism `g : T ⟶ U` of integral schemes with `x` the generic point of `T`, and leaves
both the relative dimension and the dimension function unchanged; the dimension formula
(Stacks 02JU) over the universally catenary `U` then identifies the drop
`relativeDimension x - relativeDimension y` with `dim 𝒪_{T,y}`, which is positive for `y ≠ x`
and equal to one when the specialization is immediate.

## Main results

* `Stacks.Chow.relativeDimension_isDimensionFunction` — Stacks 02JW: `relativeDimension` is the
  underlying function of a dimension function on `X`.

## Implementation notes

`Stacks.Chow.relativeDimension` is the definition already used throughout
`StacksFrontier.AlgebraicGeometry.Chow.Vocabulary`; being a dimension function is expressed by
exhibiting a `TopologicalSpace.DimensionFunction` with that underlying function, which is what
the statements there take as a hypothesis. The closure of a point is realised as the subscheme
cut out by `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, which is integral because
it is reduced with irreducible underlying space.

## References

* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Chow

/-- A closed embedding pulls a dimension function back to a dimension function: it is injective
and a homeomorphism onto its closed image, so it reflects specializations and immediate
specializations. -/
public def pullbackDimensionFunctionClosed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e : Y → X} (he : Topology.IsClosedEmbedding e)
    (d : DimensionFunction X) : DimensionFunction Y where
  toFun y := d (e y)
  strictAnti_specializes := by
    intro x y hxy hne
    apply d.strictAnti_specializes (he.isInducing.specializes_iff.mpr hxy)
    intro h
    exact hne (he.injective h)
  step_immediate := by
    intro x y hxy
    apply d.step_immediate
    refine ⟨he.isInducing.specializes_iff.mpr hxy.1,
      fun h => hxy.2.1 (he.injective h), ?_⟩
    intro z hxz hzy
    obtain ⟨w, rfl⟩ : z ∈ Set.range e :=
      hxz.mem_closed he.isClosed_range (Set.mem_range_self _)
    rcases hxy.2.2 w (he.isInducing.specializes_iff.mp hxz)
        (he.isInducing.specializes_iff.mp hzy) with h | h
    · exact Or.inl (congrArg e h)
    · exact Or.inr (congrArg e h)

/-- The residue-field map of a morphism which is surjective on stalks is bijective: it is
injective as a map of fields, and surjective because the stalk map is. -/
private lemma schemeResidueFieldMap_bijective {X Y : Scheme.{u}}
    (i : X ⟶ Y) [SurjectiveOnStalks i] (x : X) :
    Function.Bijective (i.residueFieldMap x).hom := by
  have hs : Function.Surjective (i.residueFieldMap x).hom := by
    have hstalk : Function.Surjective (i.stalkMap x).hom := i.stalkMap_surjective x
    have hres : Function.Surjective (X.residue x).hom := X.residue_surjective x
    have h : Function.Surjective (i.stalkMap x ≫ X.residue x).hom := by
      rw [CommRingCat.hom_comp, RingHom.coe_comp]
      exact hres.comp hstalk
    rw [← Scheme.residue_residueFieldMap i x] at h
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
    exact Function.Surjective.of_comp h
  exact ⟨(i.residueFieldMap x).hom.injective, hs⟩

/-- The ideal sheaf of the closure of a point pushes forward to the ideal sheaf of the closure
of its image. -/
private lemma vanishingIdeal_closure_singleton_map {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X))).map f =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({f x} : Set Y)) := by
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure (f '' closure ({x} : Set X)) = closure ({f x} : Set Y)
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    simpa using image_closure_subset_closure_image (s := ({x} : Set X)) f.continuous
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)

/-- The closure of a point, as a closed subscheme, is integral: it is reduced and its
underlying space is irreducible. -/
lemma pointClosureSubscheme_isIntegral {X : Scheme.{u}} (x : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X))).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({x} : Set X))
  let : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X))
  let : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact isIrreducible_singleton.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- The underlying space of a scheme is sober: it is quasi-sober and every generic point is
unique. -/
@[sga "4 IV 4.2.1" "partial"]
public lemma scheme_stacksSober (T : Scheme.{u}) : StacksSober T :=
  stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩

/-- On a sober `T0` space the coheight of the closure of a point, in the poset of irreducible
closed subsets, is its coheight in the specialization order. -/
public lemma coheight_closureSingleton_eq_coheight_point {T : Type*}
    [TopologicalSpace T] [QuasiSober T] [T0Space T] (x : T) :
    Order.coheight (closureSingleton x) =
      @Order.coheight T (specializationOrder T).toPreorder x := by
  let : PartialOrder T := specializationOrder T
  let e := irreducibleSetEquivPoints (α := T)
  have h : closureSingleton x = e.symm x := IrreducibleCloseds.ext rfl
  rw [h]
  calc
    Order.coheight (e.symm x) = Order.coheight (e (e.symm x)) :=
      (Order.coheight_orderIso e (e.symm x)).symm
    _ = Order.coheight x := congrArg Order.coheight (e.apply_symm_apply x)

/-- On an integral scheme with a dimension function `d`, the dimension of the local ring at `y`
is the drop of `d` from the generic point to `y`. -/
private lemma relativeDelta_eq_stalkDimension_of_generic
    {T : Scheme.{u}} [IsIntegral T] (d : DimensionFunction T) (y : T) :
    let η := genericPoint T
    ringKrullDim (T.presheaf.stalk y) = ↑((d η - d y).toNat : ℕ∞) := by
  classical
  let : PartialOrder T := specializationOrder T
  let η := genericPoint T
  have hη : closure ({η} : Set T) = Set.univ := (genericPoint_spec T).def
  have hmax : ∀ z : IrreducibleCloseds T, z ≤ closureSingleton η := by
    intro z
    change (z : Set T) ⊆ closure ({η} : Set T)
    rw [hη]
    exact Set.subset_univ _
  have hcod := codim_closure_singleton_eq_delta_diff
    (scheme_stacksSober T) d (TopologicalSpace.DimensionFunction.isDimensionFunctionForCatenary d)
    η y (genericPoint_specializes y)
  have hcod' : IrreducibleClosedsCodim.topCodim
      (closureSingleton y) (closureSingleton η) = Order.coheight y := by
    rw [topCodim_eq_coheight_of_isMax _ _ hmax,
      coheight_closureSingleton_eq_coheight_point]
  have hcoe : (↑(Order.coheight y) : WithBot ℕ∞) = ↑((d η - d y).toNat : ℕ∞) :=
    congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (hcod'.symm.trans hcod)
  exact (ringKrullDim_stalk_eq_coheight y).trans hcoe

/-- The relative dimension is unchanged by precomposing with a closed immersion. -/
private theorem relativeDimension_precomp_closedImmersion
    {X Y S : Scheme.{u}} (δ : DimensionFunction S) (f : X ⟶ S)
    (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) :
    relativeDimension δ f (i y) = relativeDimension δ (i ≫ f) y := by
  let K := S.residueField (f (i y))
  let A := Y.residueField y
  let B := X.residueField (i y)
  let : Algebra K A := ((i ≫ f).residueFieldMap y).hom.toAlgebra
  let : Algebra K B := (f.residueFieldMap (i y)).hom.toAlgebra
  have hmap : ((i ≫ f).residueFieldMap y).hom =
      (i.residueFieldMap y).hom.comp (f.residueFieldMap (i y)).hom := by
    simp [Scheme.residueFieldMap_comp]
    rfl
  let φ : B →ₐ[K] A :=
    { toRingHom := (i.residueFieldMap y).hom
      commutes' := fun a => (congrArg (fun g => g a) hmap).symm }
  have hbij : Function.Bijective φ := by
    simpa [φ] using schemeResidueFieldMap_bijective i y
  have ht : Algebra.trdeg K B = Algebra.trdeg K A :=
    (AlgEquiv.ofBijective φ hbij).trdeg_eq
  simp only [relativeDimension]
  change δ (f (i y)) + (Cardinal.toNat (Algebra.trdeg K B) : ℤ) =
    δ ((i ≫ f) y) + (Cardinal.toNat (Algebra.trdeg K A) : ℤ)
  simp [ht]

/-- The relative dimension over the base is the relative dimension over a closed subscheme of
the base, for the pulled-back dimension function. -/
public theorem relativeDimension_postcomp_closedImmersion
    {X Y S : Scheme.{u}} (δ : DimensionFunction S) (i : Y ⟶ S)
    [IsClosedImmersion i] (f : X ⟶ Y) (x : X) :
    relativeDimension δ (f ≫ i) x =
      relativeDimension (pullbackDimensionFunctionClosed i.isClosedEmbedding δ) f x := by
  let K := S.residueField (i (f x))
  let K' := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra K L := ((f ≫ i).residueFieldMap x).hom.toAlgebra
  let : Algebra K' L := (f.residueFieldMap x).hom.toAlgebra
  let eK : K ≃+* K' :=
    RingEquiv.ofBijective (i.residueFieldMap (f x)).hom
      (schemeResidueFieldMap_bijective i (f x))
  let : Algebra K K' := eK.toRingHom.toAlgebra
  have hmap : ((f ≫ i).residueFieldMap x).hom =
      (f.residueFieldMap x).hom.comp (i.residueFieldMap (f x)).hom := by
    simp [Scheme.residueFieldMap_comp]
    rfl
  have hcompat : ∀ a, (RingEquiv.refl L) (algebraMap K L a) = algebraMap K' L (eK a) :=
    fun a => congrArg (fun g => g a) hmap
  have ht : Algebra.trdeg K L = Algebra.trdeg K' L :=
    Algebra.trdeg_eq_of_ringEquiv eK (RingEquiv.refl L) hcompat
  simp only [relativeDimension, pullbackDimensionFunctionClosed]
  change δ (i (f x)) + (Cardinal.toNat (Algebra.trdeg K L) : ℤ) =
    δ (i (f x)) + (Cardinal.toNat (Algebra.trdeg K' L) : ℤ)
  simp [ht]

/-- The function field of an integral scheme is the stalk at the generic point, hence of Krull
dimension zero. -/
public lemma ringKrullDim_genericPoint_eq_zero (T : Scheme.{u}) [IsIntegral T] :
    ringKrullDim (T.presheaf.stalk (genericPoint T)) = 0 :=
  ringKrullDim_eq_zero_of_isField (Field.toIsField T.functionField)

/-- For a dominant locally finite-type morphism of integral schemes over a universally catenary
locally Noetherian base, the drop of the relative dimension from the generic point to `x` is
the dimension of the local ring at `x`. This is the dimension formula of Stacks 02JU, with the
function-field term cancelled against its value at the generic point. -/
@[sga "6 X 1.5" "special case"]
public theorem relativeDimension_drop_eq_localDimension
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (δ : DimensionFunction S)
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsDominant f] (x : X) :
    ∃ n : ℕ,
      relativeDimension δ f (genericPoint X) - relativeDimension δ f x = n ∧
      ringKrullDim (X.presheaf.stalk x) = (n : ℕ∞) := by
  classical
  let η := genericPoint X
  let ηS := genericPoint S
  have hη : f η = ηS :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  let : Algebra S.functionField X.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : ∀ z : X, Algebra (S.residueField (f z)) (X.residueField z) := fun z =>
    (f.residueFieldMap z).hom.toAlgebra
  have hfin : ∀ z : X, Algebra.trdeg (S.residueField (f z)) (X.residueField z) < Cardinal.aleph0 :=
    fun z => by
      let : Algebra.EssFiniteType (S.residueField (f z)) (X.residueField z) :=
        residueField_essFiniteType_of_locallyOfFiniteType f z
      exact trdeg_lt_aleph0 _ _
  have htrdegX := hfin x
  have htrdegη := hfin η
  have hformulaη :
      ringKrullDim (X.presheaf.stalk η) +
          (Cardinal.toENat (Algebra.trdeg (S.residueField (f η)) (X.residueField η)) :
            WithBot ℕ∞) =
        ringKrullDim (S.presheaf.stalk (f η)) +
          (Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) :=
    localDimension_add_trdeg_eq f hS η
  have hgenericFun :
      Cardinal.toENat (Algebra.trdeg (S.residueField (f η)) (X.residueField η)) =
        Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) := by
    have hXη : ringKrullDim (X.presheaf.stalk η) = 0 :=
      ringKrullDim_genericPoint_eq_zero X
    have hSη : ringKrullDim (S.presheaf.stalk (f η)) = 0 := by
      rw [hη]
      exact ringKrullDim_genericPoint_eq_zero S
    rw [hXη, hSη, zero_add, zero_add] at hformulaη
    exact WithBot.coe_inj.mp hformulaη
  have htrdegFun : Algebra.trdeg S.functionField X.functionField < Cardinal.aleph0 := by
    refine Cardinal.toENat_lt_top.mp ?_
    rw [← hgenericFun]
    exact Cardinal.toENat_lt_top.mpr htrdegη
  have htrdegηCard := Cardinal.toENat_eq_toNat_of_lt_aleph0 htrdegη
  have htrdegXCard := Cardinal.toENat_eq_toNat_of_lt_aleph0 htrdegX
  have htrdegFunCard := Cardinal.toENat_eq_toNat_of_lt_aleph0 htrdegFun
  have hgenericNat :
      Cardinal.toNat (Algebra.trdeg (S.residueField (f η)) (X.residueField η)) =
        Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) := by
    have h := hgenericFun
    rw [htrdegηCard, htrdegFunCard] at h
    exact_mod_cast h
  have hformulaX :
      ringKrullDim (X.presheaf.stalk x) +
          (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
            WithBot ℕ∞) =
        ringKrullDim (S.presheaf.stalk (f x)) +
          (Cardinal.toENat (Algebra.trdeg S.functionField X.functionField) : WithBot ℕ∞) :=
    localDimension_add_trdeg_eq f hS x
  have hbaseDim := relativeDelta_eq_stalkDimension_of_generic δ (f x)
  have hbaseNonneg : 0 ≤ δ ηS - δ (f x) := by
    by_cases h : ηS = f x
    · simp [h]
    · have hlt := δ.strictAnti_specializes (genericPoint_specializes (f x)) h
      simpa [ηS] using (sub_nonneg.mpr hlt.le)
  have hformulaNat :
      ringKrullDim (X.presheaf.stalk x) +
          (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℕ∞) =
        (Int.toNat (δ ηS - δ (f x)) : ℕ∞) +
          (Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) : ℕ∞) := by
    rw [htrdegXCard, htrdegFunCard] at hformulaX
    simpa [hbaseDim] using hformulaX
  cases hdimX : ringKrullDim (X.presheaf.stalk x) with
  | bot =>
      rw [hdimX] at hformulaNat
      norm_cast at hformulaNat
  | coe d =>
      cases d with
      | top =>
          rw [hdimX] at hformulaNat
          norm_cast at hformulaNat
      | coe n =>
          rw [hdimX] at hformulaNat
          norm_cast at hformulaNat
          have hn := hformulaNat
          refine ⟨n, ?_, rfl⟩
          dsimp [relativeDimension]
          conv_lhs => arg 1; arg 1; rw [hη]
          have hn' := congrArg (fun k : ℕ => (k : ℤ)) hn
          have hbaseInt : (Int.toNat (δ ηS - δ (f x)) : ℤ) = δ ηS - δ (f x) :=
            Int.toNat_of_nonneg hbaseNonneg
          have hgenericNat' :
              Cardinal.toNat
                  (Algebra.trdeg (S.residueField (f (genericPoint X)))
                    (X.residueField (genericPoint X))) =
                Cardinal.toNat (Algebra.trdeg S.functionField X.functionField) := by
            simpa [η] using hgenericNat
          omega

/-- On an integral scheme the local ring at a point other than the generic point has positive
dimension. -/
private lemma ringKrullDim_pos_of_specializes_generic
    {T : Scheme.{u}} [IsIntegral T] {y : T}
    (hηy : genericPoint T ⤳ y) (hne : genericPoint T ≠ y) :
    0 < ringKrullDim (T.presheaf.stalk y) := by
  let : PartialOrder T := specializationOrder T
  have hle : y ≤ genericPoint T := specializes_iff_nhds.mp hηy
  have hlt : y < genericPoint T := lt_of_le_of_ne hle (Ne.symm hne)
  rw [ringKrullDim_stalk_eq_coheight]
  have hlow : (1 : ℕ∞) ≤ Order.coheight y := by
    have h := Order.coheight_add_one_le hlt
    simpa [show genericPoint T = (⊤ : T) from rfl] using h
  exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) hlow

/-- On an integral scheme the local ring at a point to which the generic point specializes
immediately has dimension one. -/
public lemma ringKrullDim_eq_one_of_immediate_generic
    {T : Scheme.{u}} [IsIntegral T] {y : T}
    (hηy : genericPoint T ⤳ y) (hηyimm : IsImmediateSpecialization (genericPoint T) y) :
    ringKrullDim (T.presheaf.stalk y) = 1 := by
  let : PartialOrder T := specializationOrder T
  have hupper : Order.coheight y ≤ 1 := by
    refine Order.coheight_le_coe_iff.mpr fun z hyz => ?_
    have hηz : genericPoint T ⤳ z := specializes_iff_nhds.mpr (OrderTop.le_top z)
    have hzy : z ⤳ y := specializes_iff_nhds.mpr hyz.le
    rcases hηyimm.2.2 z hηz hzy with hzη | hzy'
    · subst z
      simp [show genericPoint T = (⊤ : T) from rfl, Order.coheight_top]
    · exact False.elim (hyz.ne hzy'.symm)
  have hlower : (1 : ℕ∞) ≤ Order.coheight y := by
    have hpos := ringKrullDim_pos_of_specializes_generic hηy hηyimm.2.1
    rw [ringKrullDim_stalk_eq_coheight] at hpos
    exact Order.one_le_iff_pos.mpr (by exact_mod_cast hpos)
  rw [ringKrullDim_stalk_eq_coheight]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (le_antisymm hupper hlower)

/-- The point `x` is the generic point of the closed subscheme cut out by the closure of
`{x}`. -/
private lemma pointClosure_genericPoint_eq {X : Scheme.{u}} (x : X) :
    let I := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X))
    let T := I.subscheme
    letI : IsIntegral T := pointClosureSubscheme_isIntegral x
    genericPoint T = (⟨x, subset_closure (Set.mem_singleton x)⟩ : T) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({x} : Set X))
  let T := I.subscheme
  let : IsIntegral T := pointClosureSubscheme_isIntegral x
  let i : T ⟶ X := I.subschemeι
  let tx : T := ⟨x, subset_closure (Set.mem_singleton x)⟩
  have htxgen : IsGenericPoint tx (Set.univ : Set T) := by
    refine isGenericPoint_iff_specializes.mpr fun z => ?_
    have hzsupport : z.1 ∈ (I.support : Set X) := z.property
    have hzmem : z.1 ∈ TopologicalSpace.Closeds.closure ({x} : Set X) := by
      simpa [I, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hzsupport
    have hixz : i tx ⤳ i z := by
      have hix : i tx = x := by simpa [i, tx] using I.subschemeι_apply tx
      rw [hix]
      exact specializes_iff_mem_closure.mpr hzmem
    exact iff_of_true (i.isClosedEmbedding.isInducing.specializes_iff.mp hixz)
      (Set.mem_univ z)
  exact (htxgen.eq (genericPoint_spec T)).symm

/-- A closed embedding reflects immediate specializations. -/
public lemma immediate_pullback_closedEmbedding {A X : Type*}
    [TopologicalSpace A] [TopologicalSpace X] {e : A → X}
    (he : Topology.IsClosedEmbedding e) {a b : A}
    (h : IsImmediateSpecialization (e a) (e b)) : IsImmediateSpecialization a b := by
  refine ⟨he.isInducing.specializes_iff.mp h.1, fun h' => h.2.1 (congrArg e h'), ?_⟩
  intro z haz hzb
  rcases h.2.2 (e z) (he.isInducing.specializes_iff.mpr haz)
      (he.isInducing.specializes_iff.mpr hzb) with hz | hz
  · exact Or.inl (he.injective hz)
  · exact Or.inr (he.injective hz)

/-- Along any specialization `x ⤳ y` in `X`, the relative dimension drops by the dimension of
the local ring at `y` of the closed subscheme `closure {x}`. Restricting `f` to the closures of
`x` and of `f x` makes it a dominant morphism of integral schemes over a universally catenary
base, where `relativeDimension_drop_eq_localDimension` applies. -/
public theorem relativeDimension_drop_of_specialization
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (δ : DimensionFunction S)
    (f : X ⟶ S) [LocallyOfFiniteType f] {x y : X} (hxy : x ⤳ y) :
    ∃ n : ℕ,
      relativeDimension δ f x - relativeDimension δ f y = n ∧
      ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk
        ⟨y, specializes_iff_mem_closure.mp hxy⟩) = (n : ℕ∞) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({x} : Set X))
  let J := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({f x} : Set S))
  let T := I.subscheme
  let U := J.subscheme
  let i : T ⟶ X := I.subschemeι
  let j : U ⟶ S := J.subschemeι
  have hyI : y ∈ I.support := specializes_iff_mem_closure.mp hxy
  let tx : T := ⟨x, subset_closure (Set.mem_singleton x)⟩
  let ty : T := ⟨y, hyI⟩
  let ux : U := ⟨f x, subset_closure (Set.mem_singleton (f x))⟩
  have hix : i tx = x := by simpa [i, tx] using I.subschemeι_apply tx
  have hiy : i ty = y := by simpa [i, ty] using I.subschemeι_apply ty
  have hjx : j ux = f x := by simpa [j, ux] using J.subschemeι_apply ux
  have hIJ : J ≤ I.map f := by rw [vanishingIdeal_closure_singleton_map]
  let g : T ⟶ U := Scheme.IdealSheafData.subschemeMap I J f hIJ
  have hcomp : g ≫ j = i ≫ f := by simp [g, i, j]
  have hjg : ∀ t : T, j (g t) = f (i t) := fun t => congrArg (fun k : T ⟶ S => k t) hcomp
  have hgtx : g tx = ux := j.isClosedEmbedding.injective (by rw [hjg, hix, hjx])
  let : IsIntegral T := pointClosureSubscheme_isIntegral x
  let : IsIntegral U := pointClosureSubscheme_isIntegral (f x)
  have hUgen : genericPoint U = ux := by
    simpa [J, U, ux] using pointClosure_genericPoint_eq (f x)
  have hTgen : genericPoint T = tx := by
    simpa [I, T, tx] using pointClosure_genericPoint_eq x
  have hDense : DenseRange g := by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    intro z _
    have huxz : ux ⤳ z := hUgen ▸ genericPoint_specializes z
    have huxrange : ux ∈ Set.range g := ⟨tx, hgtx⟩
    exact closure_mono (Set.singleton_subset_iff.mpr huxrange)
      (specializes_iff_mem_closure.mp huxz)
  let : IsDominant g := ⟨hDense⟩
  let : LocallyOfFiniteType (g ≫ j) := by
    rw [hcomp]
    infer_instance
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g j
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have hUcat : Scheme.IsUniversallyCatenary U := fun Z q hq =>
    have : LocallyOfFiniteType q := hq
    have : LocallyOfFiniteType (q ≫ j) := locallyOfFiniteType_comp q j
    hS Z (q ≫ j)
  let δU := pullbackDimensionFunctionClosed j.isClosedEmbedding δ
  have hdim : ∀ t : T, relativeDimension δ f (i t) = relativeDimension δU g t := fun t =>
    calc
      relativeDimension δ f (i t) = relativeDimension δ (i ≫ f) t :=
        relativeDimension_precomp_closedImmersion δ f i t
      _ = relativeDimension δ (g ≫ j) t :=
        congrArg (fun k : T ⟶ S => relativeDimension δ k t) hcomp.symm
      _ = relativeDimension δU g t := relativeDimension_postcomp_closedImmersion δ j g t
  obtain ⟨n, hdrop, hlocal⟩ :=
    relativeDimension_drop_eq_localDimension hUcat δU g ty
  refine ⟨n, ?_, hlocal⟩
  rw [← hix, ← hiy, hdim, hdim, ← hTgen]
  exact hdrop

/-- The local ring of `closure {x}` at a point `y` of it has positive dimension when `y ≠ x`,
and dimension one when `x` specializes immediately to `y`. -/
private lemma closureStalk_dimension {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y) :
    let T := (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X))).subscheme
    (x ≠ y → 0 < ringKrullDim (T.presheaf.stalk
      ⟨y, specializes_iff_mem_closure.mp hxy⟩)) ∧
    (IsImmediateSpecialization x y → ringKrullDim (T.presheaf.stalk
      ⟨y, specializes_iff_mem_closure.mp hxy⟩) = 1) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({x} : Set X))
  let T := I.subscheme
  let i : T ⟶ X := I.subschemeι
  let tx : T := ⟨x, subset_closure (Set.mem_singleton x)⟩
  let ty : T := ⟨y, specializes_iff_mem_closure.mp hxy⟩
  let : IsIntegral T := pointClosureSubscheme_isIntegral x
  have hix : i tx = x := by simpa [i, tx] using I.subschemeι_apply tx
  have hiy : i ty = y := by simpa [i, ty] using I.subschemeι_apply ty
  have hTgen : genericPoint T = tx := by
    simpa [I, T, tx] using pointClosure_genericPoint_eq x
  have hηy : genericPoint T ⤳ ty := by
    rw [hTgen]
    apply i.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa [hix, hiy] using hxy
  constructor
  · intro hne
    apply ringKrullDim_pos_of_specializes_generic hηy
    intro h
    apply hne
    calc
      x = i tx := hix.symm
      _ = i ty := congrArg i (hTgen.symm.trans h)
      _ = y := hiy
  · intro himm
    apply ringKrullDim_eq_one_of_immediate_generic hηy
    rw [hTgen]
    apply immediate_pullback_closedEmbedding i.isClosedEmbedding
    simpa [hix, hiy] using himm

/-- **Stacks 02JW.** A dimension function on a locally Noetherian universally catenary scheme
propagates along every locally finite-type morphism by adding the transcendence degree of the
residue-field extension: `relativeDimension δ f` is the underlying function of a dimension
function on the source. -/
@[stacks 02JW, sga "6 X 1.5" "special case"]
theorem relativeDimension_isDimensionFunction {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (hS : Scheme.IsUniversallyCatenary S)
    (δ : DimensionFunction S) (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ d : DimensionFunction X, ∀ x, d x = relativeDimension δ f x :=
  (TopologicalSpace.exists_dimensionFunction_iff (relativeDimension δ f)).2 ⟨by
    intro x y hxy hne
    obtain ⟨n, hdrop, hlocal⟩ := relativeDimension_drop_of_specialization hS δ f hxy
    have hnpos : 0 < n := by
      have hpos := (closureStalk_dimension hxy).1 hne
      rw [hlocal] at hpos
      exact_mod_cast hpos
    omega
  , by
    intro x y hxy
    obtain ⟨n, hdrop, hlocal⟩ :=
      relativeDimension_drop_of_specialization hS δ f hxy.1
    have hlocalOne := (closureStalk_dimension hxy.1).2 hxy
    have hnOne : n = 1 := by
      rw [hlocal] at hlocalOne
      exact_mod_cast hlocalOne
    omega⟩

end Stacks.Chow
