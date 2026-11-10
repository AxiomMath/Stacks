module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RamifiedDivisorDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDivisorSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The divisor square of a ramified morphism of curves

Let `π : X ⟶ Y` be a flat morphism of integral normal locally Noetherian schemes. The third
component of the morphism of divisor sequences along `π` is the ramification-weighted map
`Stacks.EtaleCohomology.ramifiedClosedPointDivisorDirectImageMap`, which sends the summand at a
closed point `y` of `Y` to the sum, over the points of a finite family above `y`, of the local
multiplicity times the skyscraper direct image map. This file constructs the finite family and
proves the local multiplicity identity for the third square on sections.

## Main definitions

* `Stacks.EtaleCohomology.closedPointFibreFinset`: the closed points of `X` above a closed point
  of `Y`, as a `Finset`, built from finiteness of the set-theoretic fibre.
* `Stacks.EtaleCohomology.sheafHomEval`: evaluation of a morphism of sheaves of abelian groups at
  a section, as a homomorphism in the morphism.
* `Stacks.EtaleCohomology.ramifiedSummandMap` and
  `Stacks.EtaleCohomology.ramifiedDirectImageDirectSum`: the weighted third component read on a
  single summand and on a finitely supported family of sections of the summands.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationLength_of_comp_eq_of_etale`: **the local multiplicity
  is unchanged by étale base change.**
* `Stacks.EtaleCohomology.mem_closedPointFibreFinset`: the members of the finite family are the
  closed points above `y`, all of them.
* `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint_ramified`: **the order of vanishing of a
  restricted function at a point of `U ×_Y X` is the local multiplicity of `π` at the image of
  that point in `X` times the order of vanishing downstairs**, for `U` an étale `Y`-scheme. This
  is the third square of the divisor sequences read at one point.
* `Stacks.EtaleCohomology.integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint_ramified`
  — **the same identity on the sections of a single skyscraper**, which is the third square read
  on one summand.
* `Stacks.EtaleCohomology.ramifiedClosedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum`:
  the weighted third component applied to the section of `⨁_x (i_x)_* 𝐙` attached to a family of
  sections of the summands is the section attached to the weighted family.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1): the length identity for
  a flat local homomorphism.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the divisor sequence
  whose third term the weighted map compares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order IsLocalRing TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry

/-- **The local multiplicity of a morphism is unchanged by étale base change**: if `f ≫ j = i ≫ f'`
with `i` and `j` étale, the local multiplicity of `f` at `z` is that of `f'` at `i z`. -/
@[ega "IV 4.7.3" "(i), special case"]
theorem Scheme.Hom.ramificationLength_of_comp_eq_of_etale {A B C D : Scheme.{u}} {f : A ⟶ B}
    {f' : C ⟶ D} {i : A ⟶ C} {j : B ⟶ D} [Etale i] [Etale j] (hsq : f ≫ j = i ≫ f') (z : A) :
    f.ramificationLength z = f'.ramificationLength (i.base z) := by
  have hjcrit := ((etaleAt_tfae j (f.base z)).out 1 7).mp
    ((etale_iff_forall_etaleAt j).mp ‹Etale j› (f.base z))
  have hjmax : Ideal.map (j.stalkMap (f.base z)).hom
      (maximalIdeal (D.presheaf.stalk (j.base (f.base z)))) =
      maximalIdeal (B.presheaf.stalk (f.base z)) := hjcrit.2.1
  have key : ∀ I : Ideal (C.presheaf.stalk (i.base z)),
      Module.length (A.presheaf.stalk z)
          (A.presheaf.stalk z ⧸ I.map (i.stalkMap z).hom) =
        Module.length (C.presheaf.stalk (i.base z)) (C.presheaf.stalk (i.base z) ⧸ I) := by
    intro I
    algebraize [(i.stalkMap z).hom]
    have hloc : IsLocalHom (algebraMap (C.presheaf.stalk (i.base z)) (A.presheaf.stalk z)) :=
      inferInstanceAs (IsLocalHom (i.stalkMap z).hom)
    have hflat : Module.Flat (C.presheaf.stalk (i.base z)) (A.presheaf.stalk z) :=
      RingHom.flat_algebraMap_iff.mp (Flat.stalkMap i z)
    have hicrit := ((etaleAt_tfae i z).out 1 7).mp ((etale_iff_forall_etaleAt i).mp ‹Etale i› z)
    have himax : extendedMaximalIdeal (C.presheaf.stalk (i.base z)) (A.presheaf.stalk z) =
      maximalIdeal (A.presheaf.stalk z) := hicrit.2.1
    have hone : Module.length (A.presheaf.stalk z)
        (A.presheaf.stalk z ⧸
          extendedMaximalIdeal (C.presheaf.stalk (i.base z)) (A.presheaf.stalk z)) = 1 := by
      rw [himax]
      exact Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
        ⟨maximalIdeal (A.presheaf.stalk z), maximalIdeal.isMaximal (A.presheaf.stalk z),
          ⟨LinearEquiv.refl _ _⟩⟩)
    rw [show I.map (i.stalkMap z).hom =
        Ideal.map (algebraMap (C.presheaf.stalk (i.base z)) (A.presheaf.stalk z)) I from rfl,
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A.presheaf.stalk z)
        I).toLinearEquiv.length_eq,
      ← length_baseChange_eq_length_mul_length_quotient (C.presheaf.stalk (i.base z))
        (A.presheaf.stalk z) (C.presheaf.stalk (i.base z) ⧸ I), hone, mul_one]
  have e1 := Stacks.EtaleCohomology.map_maximalIdeal_stalkMap_congr hsq z
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e1
  have e2 : (maximalIdeal (D.presheaf.stalk ((f ≫ j).base z))).map
      (j.stalkMap (f.base z) ≫ f.stalkMap z).hom =
      (maximalIdeal (B.presheaf.stalk (f.base z))).map (f.stalkMap z).hom := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (j.stalkMap (f.base z)).hom (f.stalkMap z).hom).symm.trans
      (congrArg (Ideal.map (f.stalkMap z).hom) hjmax)
  have e3 : (maximalIdeal (D.presheaf.stalk ((i ≫ f').base z))).map
      (f'.stalkMap (i.base z) ≫ i.stalkMap z).hom =
      ((maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map
        (f'.stalkMap (i.base z)).hom).map (i.stalkMap z).hom := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (f'.stalkMap (i.base z)).hom (i.stalkMap z).hom).symm
  rw [Scheme.Hom.ramificationLength_eq, Scheme.Hom.ramificationLength_eq,
    show (maximalIdeal (B.presheaf.stalk (f.base z))).map (f.stalkMap z).hom =
      ((maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map
        (f'.stalkMap (i.base z)).hom).map (i.stalkMap z).hom from e2.symm.trans (e1.trans e3),
    key ((maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map
      (f'.stalkMap (i.base z)).hom)]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-! ### The fibre of a morphism over a closed point, as a finite set -/

section Fibre

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- **The closed points of `X` above a closed point `y` of `Y`, as a `Finset`**, given that each
such fibre is finite. -/
def closedPointFibreFinset (hfin : ∀ y : closedPoints Y, (π.base ⁻¹' {y.1}).Finite)
    (y : closedPoints Y) : Finset ↥(closedPoints X) :=
  ((hfin y).preimage Subtype.val_injective.injOn).toFinset

/-- **The finite family above `y` consists of the closed points of `X` over `y`, all of them.** -/
theorem mem_closedPointFibreFinset (hfin : ∀ y : closedPoints Y, (π.base ⁻¹' {y.1}).Finite)
    (y : closedPoints Y) (x : closedPoints X) :
    x ∈ closedPointFibreFinset π hfin y ↔ π.base x.1 = y.1 :=
  Set.Finite.mem_toFinset _

/-- **The fibre of a quasi-compact morphism locally of finite type over a point that is not the
generic point is finite**, when the source is integral of dimension one and the morphism is
dominant. -/
theorem finite_preimage_singleton_of_topologicalKrullDim_eq_one [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType π] [QuasiCompact π] [IsDominant π] (hdim : topologicalKrullDim X = 1)
    {y : Y} (hy : y ≠ genericPoint Y) : (π.base ⁻¹' {y}).Finite := by
  have hgen : π.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral π).out 1 2).mp (inferInstance : IsDominant π)
  have hclosed : ∀ x : X, π.base x = y → IsClosed ({x} : Set X) := by
    intro x hx
    refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X
      hdim fun hxg => hy ?_
    rw [← hx, hxg, hgen]
  refine Stacks.Chow.finite_preimage_singleton_of_specializes_imp_eq π y
    fun x x' hx hx' hxx' => ?_
  have hmem : x' ∈ closure ({x} : Set X) := hxx'.mem_closure
  rw [(hclosed x hx).closure_eq] at hmem
  exact hmem.symm

end Fibre

/-! ### The order of vanishing across the square of generic fibres -/

section Pointwise

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsIntegral Y] [IsNormal Y]
  (π : X ⟶ Y) [Flat π]

omit [IsNormal X] [IsNormal Y] in
/-- **The generic point square of `π`**: `j_X ≫ π = (Spec K(X) ⟶ Spec K(Y)) ≫ j_Y`. -/
theorem genericPointSquare_ramified :
    genericPointInclusion X ≫ π = genericPointMap π ≫ genericPointInclusion Y :=
  genericPointInclusion_comp_eq_genericPointMap_comp π

/-- **The restriction map of generic fibres** `(U ×_Y X) ×_X η_X ⟶ U ×_Y η_Y` induced by `π`,
for `U` an étale `Y`-scheme. -/
abbrev genericFibreRamifiedMap (U : Y.Etale) :
    pullback ((smallEtaleBaseChange π).obj U).hom (genericPointInclusion X) ⟶
      pullback U.hom (genericPointInclusion Y) :=
  smallEtaleBaseChangeSquareLeft (genericPointSquare_ramified π) U ≫ pullback.fst _ _

omit [IsNormal X] [IsNormal Y] in
/-- The restriction map of generic fibres followed by the projection to `U` is the projection to
`U ×_Y X` followed by the projection to `U`. -/
theorem genericFibreRamifiedMap_fst (U : Y.Etale) :
    genericFibreRamifiedMap π U ≫ pullback.fst U.hom (genericPointInclusion Y) =
      pullback.fst _ _ ≫ pullback.fst U.hom π :=
  (Category.assoc _ _ _).trans
    (smallEtaleBaseChangeSquareLeft_fst_fst (genericPointSquare_ramified π) U)

omit [IsIntegral X] [IsNormal X] [IsIntegral Y] [IsNormal Y] [Flat π] in
/-- **The local multiplicity of `π` is that of its base change to an étale `Y`-scheme**: at a
point `z` of `U ×_Y X` the local multiplicity of `U ×_Y X ⟶ U` is the local multiplicity of `π`
at the image of `z` in `X`. -/
theorem ramificationLength_pullback_fst_eq (U : Y.Etale)
    (z : ((smallEtaleBaseChange π).obj U).left) :
    (pullback.fst U.hom π).ramificationLength z =
      π.ramificationLength (((smallEtaleBaseChange π).obj U).hom.base z) :=
  @Scheme.Hom.ramificationLength_of_comp_eq_of_etale ((smallEtaleBaseChange π).obj U).left U.left
    X Y (pullback.fst U.hom π) π ((smallEtaleBaseChange π).obj U).hom U.hom
    ((smallEtaleBaseChange π).obj U).prop U.prop pullback.condition z

/-- **The order of vanishing of a restricted function is the local multiplicity of `π` times the
order of vanishing downstairs**, at a point `z` of `U ×_Y X` where the codimension of the image in
`U` agrees with that of `z`. -/
theorem etaleGenericFibreOrdOfPoint_ramified (U : Y.Etale)
    [IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left] [IsLocallyNoetherian U.left]
    (z : ((smallEtaleBaseChange π).obj U).left)
    (hcoh : coheight ((pullback.fst U.hom π).base z) = coheight z)
    (a : (Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ) :
    etaleGenericFibreOrdOfPoint ((smallEtaleBaseChange π).obj U) z
        (Additive.ofMul (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a)) =
      (π.ramificationLength (((smallEtaleBaseChange π).obj U).hom.base z) : ℤ) *
        etaleGenericFibreOrdOfPoint U ((pullback.fst U.hom π).base z) (Additive.ofMul a) := by
  have : @Flat ((smallEtaleBaseChange π).obj U).left U.left (pullback.fst U.hom π) :=
    inferInstanceAs (Flat (pullback.fst U.hom π))
  have : IsLocallyNoetherian ((𝟭 Scheme).obj ((smallEtaleBaseChange π).obj U).left) :=
    inferInstanceAs (IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left)
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  rw [← ramificationLength_pullback_fst_eq π U z]
  exact genericFibreOrdOfPoint_appTop_eq_ramificationLength_mul_of_square (X := Y) (X' := X)
    ((smallEtaleBaseChange π).obj U).hom U.hom (pullback.fst U.hom π)
    (genericFibreRamifiedMap π U) (genericFibreRamifiedMap_fst π U) z hcoh a

omit [IsIntegral X] [IsNormal X] [IsIntegral Y] [IsNormal Y] [Flat π] in
/-- **A morphism preserving codimension preserves it after étale base change**: at a point `z` of
`U ×_Y X` the codimension of the image in `U` is the codimension of `z`. -/
theorem coheight_pullback_fst_eq (hcoh : ∀ x : X, coheight (π.base x) = coheight x) (U : Y.Etale)
    (z : ((smallEtaleBaseChange π).obj U).left) :
    coheight ((pullback.fst U.hom π).base z) = coheight z := by
  have h1 : coheight (U.hom.base ((pullback.fst U.hom π).base z)) =
    coheight ((pullback.fst U.hom π).base z) := coheight_eq_of_etale U.hom _
  have h2 : coheight (((smallEtaleBaseChange π).obj U).hom.base z) = coheight z :=
    coheight_eq_of_etale ((smallEtaleBaseChange π).obj U).hom z
  have hsq : U.hom.base ((pullback.fst U.hom π).base z) =
      π.base (((smallEtaleBaseChange π).obj U).hom.base z) :=
    congrArg (fun φ : ((smallEtaleBaseChange π).obj U).left ⟶ Y => φ.base z) pullback.condition
  rw [← h1, hsq, hcoh, h2]

/-- **The map from the fibre of `U ×_Y X` over a point `x` of `X` to the fibre of `U` over
`π x`**, for `U` an étale `Y`-scheme. -/
abbrev ramifiedResidueFibreMap (U : Y.Etale) (x : X) :
    ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj
        ((smallEtaleBaseChange π).obj U)).left ⟶
      ((smallEtaleBaseChange (Y.fromSpecResidueField (π.base x))).obj U).left :=
  smallEtaleBaseChangeSquareLeft (π.SpecMap_residueFieldMap_fromSpecResidueField x).symm U ≫
    pullback.fst _ _

/-- **On the fibre over a closed point, the order of vanishing of a restricted function is the
local multiplicity of `π` times the order of vanishing downstairs.** -/
theorem residueFibreOrdOfPoint_apply_ramified
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x) (U : Y.Etale)
    [IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left] [IsLocallyNoetherian U.left]
    (x : X) (a : (Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ)
    (w : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj
      ((smallEtaleBaseChange π).obj U)).left) :
    (residueFibreOrdOfPoint.{u, v} ((smallEtaleBaseChange π).obj U) x
        (Additive.ofMul
          (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a)) w).down =
      (π.ramificationLength x : ℤ) *
        (residueFibreOrdOfPoint.{u, v} U (π.base x) (Additive.ofMul a)
          ((ramifiedResidueFibreMap π U x).base w)).down := by
  set z := (pullback.fst ((smallEtaleBaseChange π).obj U).hom
    (X.fromSpecResidueField x)).base w with hz
  have hxz : ((smallEtaleBaseChange π).obj U).hom.base z = x :=
    hom_base_pullback_fst_fromSpecResidueField x ((smallEtaleBaseChange π).obj U) w
  have hpt : (pullback.fst U.hom (Y.fromSpecResidueField (π.base x))).base
      ((ramifiedResidueFibreMap π U x).base w) = (pullback.fst U.hom π).base z :=
    congrArg (fun φ : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj
      ((smallEtaleBaseChange π).obj U)).left ⟶ U.left => φ.base w)
      (smallEtaleBaseChangeSquareLeft_fst_fst
        (π.SpecMap_residueFieldMap_fromSpecResidueField x).symm U)
  have key := etaleGenericFibreOrdOfPoint_ramified π U z (coheight_pullback_fst_eq π hcoh U z) a
  rw [hxz] at key
  rw [residueFibreOrdOfPoint_apply, residueFibreOrdOfPoint_apply, hpt]
  exact key

/-- **On the summand at a point of `X`, the weighted third component matches the divisors**: the
local multiplicity of `π` times the image under the skyscraper direct image map of the divisor at
`π x` of an invertible function on the generic fibre of `U` is the divisor at `x` of its
restriction to the generic fibre of `U ×_Y X`. -/
theorem integerSkyscraperDirectImageMap_integerSkyscraperDivisorOfPoint_ramified
    (hcoh : ∀ x : X, coheight (π.base x) = coheight x) (U : Y.Etale)
    [IsLocallyNoetherian ((smallEtaleBaseChange π).obj U).left] [IsLocallyNoetherian U.left]
    (x : X) (a : (Γ(pullback U.hom (genericPointInclusion Y), ⊤))ˣ) :
    (π.ramificationLength x : ℤ) •
        ((integerSkyscraperDirectImageMap.{u, v} π x).hom.app (op U)).hom
          (integerSkyscraperDivisorOfPoint.{u, v} U (π.base x) (Additive.ofMul a)) =
      integerSkyscraperDivisorOfPoint.{u, v} ((smallEtaleBaseChange π).obj U) x
        (Additive.ofMul (Units.map (genericFibreRamifiedMap π U).appTop.hom.toMonoidHom a)) := by
  refine (ConcreteCategory.bijective_of_isIso
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x
      ((smallEtaleBaseChange π).obj U)).hom).1 ((map_zsmul _ _ _).trans ?_)
  rw [integerSkyscraperDirectImageMap_app,
    integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint,
    integerSkyscraperSectionsIsoLocallyConstantMaps_integerSkyscraperDivisorOfPoint]
  refine LocallyConstant.ext fun w => ULift.ext ?_
  rw [LocallyConstant.coe_smul, Pi.smul_apply, LocallyConstant.coe_comap_apply, ULift.smul_down]
  simp only [smul_eq_mul]
  exact (residueFibreOrdOfPoint_apply_ramified.{u, v} π hcoh U x a w).symm

end Pointwise

/-! ### The third component on families of sections -/

section Sections

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]
  [AlgebraicGeometry.IsIntegral Y] [IsNormal Y] (π : X ⟶ Y) [Flat π]

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **Evaluation of a morphism of sheaves of abelian groups at a fixed section**, as a
homomorphism of abelian groups in the morphism. -/
def sheafHomEval {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (U : Y.Etale)
    (t : ToType (A.obj.obj (op U))) : (A ⟶ B) →+ ToType (B.obj.obj (op U)) where
  toFun φ := (φ.hom.app (op U)).hom t
  map_zero' := by simp
  map_add' _ _ := by simp

omit [AlgebraicGeometry.IsIntegral Y] [IsNormal Y] in
/-- `sheafHomEval U t φ` is the value of `φ` on the section `t` over `U`. -/
@[simp]
theorem sheafHomEval_apply
    {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (U : Y.Etale)
    (t : ToType (A.obj.obj (op U))) (φ : A ⟶ B) :
    sheafHomEval.{u, v} U t φ = (φ.hom.app (op U)).hom t :=
  rfl

/-- The third component on a single summand, from the sections of the skyscraper at a closed point
`y` of `Y` to the sections of the skyscraper at a closed point `x` above it, over the base change
of the étale `Y`-scheme. -/
def ramifiedSummandMap (U : Y.Etale) (x : closedPoints X) (y : closedPoints Y)
    (hxy : π.base x.1 = y.1) :
    (closedPointSkyscraper.{u, v} Y y).obj.obj (op U) →+
      (closedPointSkyscraper.{u, v} X x).obj.obj (op ((smallEtaleBaseChange π).obj U)) :=
  ((eqToHom (by rw [closedPointSkyscraper, hxy]) ≫
    integerSkyscraperDirectImageMap.{u, v} π x.1).hom.app (op U)).hom

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
  [Flat π] in
/-- **The weighted third component on sections of a summand** is the summand map scaled by the
local multiplicity, followed by the inclusion of the summand at `x`. -/
theorem weightedIntegerSkyscraperDirectImageMap_app (U : Y.Etale) (x : closedPoints X)
    (y : closedPoints Y) (hxy : π.base x.1 = y.1) (e : ℤ)
    (t : ToType ((closedPointSkyscraper.{u, v} Y y).obj.obj (op U))) :
    ((weightedIntegerSkyscraperDirectImageMap.{u, v} π x y hxy e).hom.app (op U)).hom t =
      e • ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app
        (op ((smallEtaleBaseChange π).obj U))).hom (ramifiedSummandMap.{u, v} π U x y hxy t) := by
  rw [weightedIntegerSkyscraperDirectImageMap, ← sheafHomEval_apply.{u, v} U t,
    map_zsmul, sheafHomEval_apply]
  rfl

/-- **The third component on families of sections of the summands**: the family at a closed point
`y` of `Y` contributes, at each closed point `x` of the finite family above `y`, the local
multiplicity at `x` times the summand map. -/
def ramifiedDirectImageDirectSum (U : Y.Etale) (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1) :
    DirectSum ↥(closedPoints Y)
        (fun y : closedPoints Y ↦ (closedPointSkyscraper.{u, v} Y y).obj.obj (op U)) →+
      DirectSum ↥(closedPoints X)
        (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj
          (op ((smallEtaleBaseChange π).obj U))) :=
  letI : DecidableEq ↥(closedPoints X) := Classical.decEq _
  letI : DecidableEq ↥(closedPoints Y) := Classical.decEq _
  DirectSum.toAddMonoid fun y => ∑ x ∈ (F y).attach,
    (DirectSum.of _ x.1).comp
      ((π.ramificationLength x.1.1 : ℤ) • ramifiedSummandMap.{u, v} π U x.1 y (hF y x.1 x.2))

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
  [Flat π] in
/-- **The weighted third component on a section coming from a family of sections of the
summands.** -/
theorem ramifiedClosedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum (U : Y.Etale)
    (F : closedPoints Y → Finset ↥(closedPoints X))
    (hF : ∀ (y : closedPoints Y) (x : closedPoints X), x ∈ F y → π.base x.1 = y.1)
    (f : DirectSum ↥(closedPoints Y)
      fun y : closedPoints Y ↦ (closedPointSkyscraper.{u, v} Y y).obj.obj (op U)) :
    ((ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF).hom.app (op U)).hom
        (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} Y U f) =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X
        ((smallEtaleBaseChange π).obj U) (ramifiedDirectImageDirectSum.{u, v} π U F hF f) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let : DecidableEq ↥(closedPoints Y) := Classical.decEq _
  induction f using DirectSum.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero, map_zero]
    rfl
  | add g₁ g₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, map_add, h₁, h₂]
    rfl
  | of y t =>
    have l1 : closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} Y U (DirectSum.of _ y t) =
        ((closedPointDivisorSheaf.ι.{u, v} Y y).hom.app (op U)).hom t := by
      rw [closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
    have l2 : sheafHomEval.{u, v} U t
          (closedPointDivisorSheaf.ι.{u, v} Y y ≫
            ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF) =
        ∑ x ∈ (F y).attach, sheafHomEval.{u, v} U t
          (weightedIntegerSkyscraperDirectImageMap.{u, v} π x.1 y (hF y x.1 x.2)
            (π.ramificationLength x.1.1)) := by
      rw [ι_ramifiedClosedPointDivisorDirectImageMap, map_sum]
    have r1 : ramifiedDirectImageDirectSum.{u, v} π U F hF (DirectSum.of _ y t) =
        ∑ x ∈ (F y).attach, DirectSum.of _ x.1
          ((π.ramificationLength x.1.1 : ℤ) •
            ramifiedSummandMap.{u, v} π U x.1 y (hF y x.1 x.2) t) := by
      rw [ramifiedDirectImageDirectSum, DirectSum.toAddMonoid_of,
        AddMonoidHom.finsetSum_apply]
      exact Finset.sum_congr rfl fun x _ => rfl
    have h0 : ((closedPointDivisorSheaf.ι.{u, v} Y y ≫
        ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF).hom.app (op U)).hom t =
        ((ramifiedClosedPointDivisorDirectImageMap.{u, v} π F hF).hom.app (op U)).hom
          (((closedPointDivisorSheaf.ι.{u, v} Y y).hom.app (op U)).hom t) := rfl
    rw [l1, r1, map_sum (closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X
      ((smallEtaleBaseChange π).obj U))]
    refine (h0.symm.trans l2).trans (Finset.sum_congr rfl fun x _ => ?_)
    rw [sheafHomEval_apply, weightedIntegerSkyscraperDirectImageMap_app,
      closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of, map_zsmul]

end Sections

end Stacks.EtaleCohomology

end
