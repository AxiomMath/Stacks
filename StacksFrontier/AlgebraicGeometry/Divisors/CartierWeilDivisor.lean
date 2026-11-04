module

public import StacksFrontier.AlgebraicGeometry.Divisors.CartierDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Weil divisor of a Cartier divisor

Let `X` be a Noetherian integral scheme and let `τ` be a Cartier divisor on `X`, that is a global
section of the quotient sheaf `𝒦_X^* / 𝒪_X^*`.  The *Weil divisor of `τ`* is the formal sum
`Σ v_Z(τ) [Z]` over the prime divisors of `X`, where the coefficient at `Z` with generic point `ξ`
is

* `v_Z(τ) = 0` when the germ of `τ` at `ξ` is zero, and
* `v_Z(τ) = length (𝒪_{X, ξ} / (a)) - length (𝒪_{X, ξ} / (b))` when `τ` is represented near `ξ`
  on an affine open `U` by the fraction `a / b` of two regular functions on `U`.

Both clauses are instances of one formula: the stalk of `𝒦_X^* / 𝒪_X^*` at `ξ` maps to `ℤ` by the
order of vanishing of the function field, and the coefficient is the image of the germ of `τ`
under that map.  The coefficient family is finitely supported, so it is a Weil divisor.

## Main definitions

* `AlgebraicGeometry.cartierMultiplicity` is the order `v_Z(τ)`, as an integer.
* `AlgebraicGeometry.cartierWeilDivisor` is the Weil divisor of a Cartier divisor.
* `AlgebraicGeometry.rawUnitGroupQuotientMap` is the projection of the unit-group presheaf of a
  sheaf of commutative rings onto the quotient sheaf, before sheafifying the source.
* `AlgebraicGeometry.totalQuotientStalkToFunctionField` identifies the stalk of the sheaf of
  total quotient rings with the function field.

## Main results

* `AlgebraicGeometry.exists_affineOpen_local_representation`: near any point a Cartier divisor is
  the image of a unit of the sheaf of total quotient rings over an affine open, and that unit is
  a fraction of two regular functions.
* `AlgebraicGeometry.cartierWeilDivisor_apply`,
  `AlgebraicGeometry.cartierWeilDivisor_apply_of_germ_eq_zero` and
  `AlgebraicGeometry.cartierWeilDivisor_apply_of_local_eq` identify the coefficients of `[τ]`,
  the last two being the two clauses of the definition.
* `AlgebraicGeometry.PrimeDivisor.finite_setOf_genericPoint_mem`: on a Noetherian integral scheme
  only finitely many prime divisors have their generic point in a given proper closed subset.
* `AlgebraicGeometry.finite_cartierMultiplicity_support`: the coefficient family of a Cartier
  divisor is finitely supported.

## Implementation notes

The order function `v_Z` of Tag 02AR part (8) is the order of vanishing of an element of the
function field at a codimension-one point, which is Mathlib's `AlgebraicGeometry.Scheme.ord`,
built on `Ring.ordFrac`.  It is *not* the order function of part (5), which is `Ring.ord` of
Tag 02MD applied to a principal stalk ideal, nor
`AlgebraicGeometry.orderOfVanishingAtPrimeDivisor`, which is the order of a section of an
invertible sheaf along a prime divisor.  The bridge between the two descriptions of `v_Z` at a
single point is `AlgebraicGeometry.ord_algebraMap_stalk`, which is Tag 02MD read at a point.

The map from the stalk of `𝒦_X^* / 𝒪_X^*` to `ℤ` is assembled by descent: the stalk functor
preserves cokernels, the unit-group presheaf of the sheaf of total quotient rings maps to the
units of the function field, and the order of a unit of the structure sheaf is zero, so the order
factors through the cokernel.  The comparison between the stalk of a presheaf and the stalk of
its sheafification is the existing `stalkSheafifyIso`, which is reused rather than
re-coined, together with the description of its forward map added beside it; the provider
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` is a theorem rather than an instance, so
`inv` cannot synthesize it and a local instance over a `let`-bound morphism does not match.
Having the isomorphism and its forward map under names is what lets the cancellations in
`AlgebraicGeometry.totalQuotientStalkToFunctionField_comp` and
`AlgebraicGeometry.rawUnitGroupQuotientMap_stalk_order` be supplied as terms.

Finite support needs no hypothesis beyond `X` being Noetherian and integral.  A prime divisor with
a nonzero coefficient has its generic point outside the intersection of the nonvanishing loci of a
local numerator and denominator; that intersection is a nonempty open of an irreducible space, so
its complement is a proper closed subset, and
`AlgebraicGeometry.PrimeDivisor.finite_setOf_genericPoint_mem` bounds the prime divisors whose
generic point lies in such a subset.  That lemma generalises the corresponding step for effective
Cartier divisors in
`AlgebraicGeometry.effectiveCartierMultiplicity_support_finite`, which could be derived from it.

A Weil divisor is the library's `AlgebraicGeometry.WeilDivisor`, a locally finite coefficient family;
`AlgebraicGeometry.weilDivisorEquivFinsupp` identifies it with the finite formal linear
combinations, and `weilDivisorEquivFinsupp_cartierWeilDivisor` reads the construction below in
that form.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02OV](https://stacks.math.columbia.edu/tag/02OV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.Generators (unitsAddCommGrpFunctor)
open TopCat.Presheaf.ExtensionByInitial (stalkSheafifyIso stalkSheafifyIso_hom)

universe u

namespace AlgebraicGeometry

attribute [local instance] hasSheafifyAddCommGrpCat

section UnitGroupStalk

variable {X : TopCat.{u}}

/-! ### The stalks of the unit-group presheaves -/

/-- The stalk of the unit-group presheaf maps to the unit group of the stalk. -/
def unitGroupStalkMap (F : TopCat.Sheaf CommRingCat.{u} X) (x : X) :
    TopCat.Presheaf.stalk (unitGroupPresheaf F) x ⟶
      unitsAddCommGrpFunctor.obj (F.presheaf.stalk x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ unitGroupPresheaf F)
    { pt := unitsAddCommGrpFunctor.obj (F.presheaf.stalk x)
      ι :=
        { app := fun U => unitsAddCommGrpFunctor.map (F.presheaf.germ U.unop.1 x U.unop.2)
          naturality := by
            intro U V i
            change unitsAddCommGrpFunctor.map
                (F.presheaf.map ((OpenNhds.inclusion x).op.map i)) ≫
              unitsAddCommGrpFunctor.map (F.presheaf.germ V.unop.1 x V.unop.2) = _
            exact (unitsAddCommGrpFunctor.map_comp _ _).symm.trans
              (congrArg unitsAddCommGrpFunctor.map
                (F.presheaf.germ_res' ((OpenNhds.inclusion x).op.map i) x V.unop.2)) } }

/-- `AlgebraicGeometry.unitGroupStalkMap` sends the germ of a unit of the sections over `U` to
the unit of the stalk it determines. -/
@[reassoc] theorem unitGroupStalkMap_germ (F : TopCat.Sheaf CommRingCat.{u} X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (unitGroupPresheaf F) U x hx ≫ unitGroupStalkMap F x =
      unitsAddCommGrpFunctor.map (F.presheaf.germ U x hx) :=
  colimit.ι_desc _ _

/-- The map induced on the stalks of the unit-group presheaves by a morphism of sheaves of
commutative rings, with its source and target written as stalks. -/
def unitGroupMapStalk {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalk (unitGroupPresheaf F) x ⟶
      TopCat.Presheaf.stalk (unitGroupPresheaf G) x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unitGroupMap f)

/-- On sections over `U`, the map of unit-group presheaves induced by a morphism of sheaves of
commutative rings is the map of unit groups induced by that morphism on sections. -/
theorem unitGroupMap_app {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G)
    (U : (Opens X)ᵒᵖ) :
    (unitGroupMap f).app U = unitsAddCommGrpFunctor.map (f.hom.app U) := rfl

/-- `AlgebraicGeometry.unitGroupMapStalk` is compatible with germs: taking the germ and then the
induced map on stalks is taking the induced map on sections and then the germ. -/
@[reassoc] theorem unitGroupMapStalk_germ {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G)
    (x : X) (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (unitGroupPresheaf F) U x hx ≫ unitGroupMapStalk f x =
      (unitGroupMap f).app (op U) ≫ TopCat.Presheaf.germ (unitGroupPresheaf G) U x hx :=
  TopCat.Presheaf.stalkFunctor_map_germ U x hx (unitGroupMap f)

/-- The projection of the unit-group *presheaf* of the target onto the quotient *sheaf*: the
sectionwise cokernel projection followed by the sheafification unit. -/
def rawUnitGroupQuotientMap {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    unitGroupPresheaf G ⟶ (unitGroupQuotientSheaf f).presheaf :=
  cokernel.π (unitGroupMap f) ≫
    toSheafify (Opens.grothendieckTopology X) (cokernel (unitGroupMap f))

/-- `rawUnitGroupQuotientMap` factors through the unit-group sheaf of the target. -/
theorem rawUnitGroupQuotientMap_eq {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G) :
    rawUnitGroupQuotientMap f =
      toSheafify (Opens.grothendieckTopology X) (unitGroupPresheaf G) ≫
        (unitGroupQuotientMap f).hom :=
  toSheafify_naturality _ (cokernel.π (unitGroupMap f))

/-! ### The local presentation of a Cartier divisor -/

/-- The sheafification unit of a presheaf of abelian groups on a topological space is locally
surjective: it is surjective on stalks. -/
theorem isLocallySurjective_toSheafify_addCommGrpCat (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf.IsLocallySurjective (toSheafify (Opens.grothendieckTopology X) F) :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr fun y => by
    have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y AddCommGrpCat.{u} F
    have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (toSheafify (Opens.grothendieckTopology X) F)) := by
      have := hiso
      infer_instance
    exact (AddCommGrpCat.epi_iff_surjective _).mp hepi

/-- The sheafification unit of a presheaf of commutative rings on a topological space is locally
surjective: it is surjective on stalks. -/
theorem isLocallySurjective_toSheafify_commRingCat (F : TopCat.Presheaf CommRingCat.{u} X) :
    TopCat.Presheaf.IsLocallySurjective (toSheafify (Opens.grothendieckTopology X) F) :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr fun y => by
    have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y CommRingCat.{u} F
    have := hiso
    exact (ConcreteCategory.bijective_of_isIso _).2

end UnitGroupStalk

section Order

variable {X : Scheme.{u}}

/-! ### The order of vanishing on the stalks -/

/-- The stalk of the sheaf of total quotient rings of a locally Noetherian integral scheme is
the function field. -/
def totalQuotientStalkToFunctionField [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    X.totalQuotientSheaf.presheaf.stalk x ⟶ X.functionField := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
  let := stalk_totalQuotientPresheaf_isFractionRing_of_isLocallyNoetherian X x
  exact (stalkSheafifyIso X.presheaf.totalQuotientPresheaf x).inv ≫
    CommRingCat.ofHom
      (IsLocalization.algEquiv (nonZeroDivisors (X.presheaf.stalk x))
        (X.presheaf.totalQuotientPresheaf.stalk x) X.functionField).toRingHom

/-- Composing the map on stalks induced by `𝒪_X ⟶ 𝒦_X` with the identification of the stalk of
`𝒦_X` with the function field gives the canonical map from the local ring to the function
field. -/
theorem totalQuotientStalkToFunctionField_comp [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map X.toTotalQuotientSheaf.hom ≫
      totalQuotientStalkToFunctionField x =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
  let := stalk_totalQuotientPresheaf_isFractionRing_of_isLocallyNoetherian X x
  dsimp only [totalQuotientStalkToFunctionField]
  have hmc : (TopCat.Presheaf.stalkFunctor CommRingCat x).map X.toTotalQuotientSheaf.hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf ≫
      (stalkSheafifyIso X.presheaf.totalQuotientPresheaf x).hom := by
    rw [stalkSheafifyIso_hom, X.toTotalQuotientSheaf_hom]
    exact (TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp _ _
  rw [hmc]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.presheaf.toTotalQuotientPresheaf ≫ t)
    ((stalkSheafifyIso X.presheaf.totalQuotientPresheaf x).hom_inv_id_assoc
      _)).trans ?_
  ext a
  exact (IsLocalization.algEquiv (nonZeroDivisors (X.presheaf.stalk x))
      (X.presheaf.totalQuotientPresheaf.stalk x) X.functionField).commutes a

/-- The germ at `x` of a regular function on `U`, read in the function field through the sheaf of
total quotient rings, is its image under the canonical map from the local ring. -/
theorem totalQuotientStalkToFunctionField_germ [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (U : X.Opens) (hx : x ∈ U) :
    X.toTotalQuotientSheaf.hom.app (op U) ≫
      TopCat.Presheaf.germ X.totalQuotientSheaf.obj U x hx ≫
        totalQuotientStalkToFunctionField x =
    TopCat.Presheaf.germ X.sheaf.obj U x hx ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) :=
  ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ totalQuotientStalkToFunctionField x)
        (TopCat.Presheaf.stalkFunctor_map_germ U x hx X.toTotalQuotientSheaf.hom).symm)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun t => TopCat.Presheaf.germ X.sheaf.obj U x hx ≫ t)
        (totalQuotientStalkToFunctionField_comp x)))

/-- `AlgebraicGeometry.totalQuotientStalkToFunctionField_germ`, read on a section. -/
theorem totalQuotientStalkToFunctionField_germ_apply [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (U : X.Opens) (hx : x ∈ U) (c : Γ(X, U)) :
    (totalQuotientStalkToFunctionField x)
        (TopCat.Presheaf.germ X.totalQuotientSheaf.obj U x hx
          (X.toTotalQuotientSheaf.hom.app (op U) c)) =
      (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
        (X.presheaf.germ U x hx c) :=
  ((CategoryTheory.comp_apply _ _ c).trans (CategoryTheory.comp_apply _ _ _)).symm.trans
    ((ConcreteCategory.congr_hom (totalQuotientStalkToFunctionField_germ x U hx) c).trans
      (CategoryTheory.comp_apply _ _ c))

/-- The order of vanishing at a point, as an additive map on the units of the function field. -/
def functionFieldUnitOrder [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    Additive X.functionFieldˣ →+ ℤ where
  toFun v := X.ord v.toMul.val x
  map_zero' := by
    have h := X.ord_mul (x := x) (f := 1) (g := 1) one_ne_zero one_ne_zero
    simp only [mul_one] at h
    change X.ord 1 x = 0
    omega
  map_add' a b := X.ord_mul a.toMul.ne_zero b.toMul.ne_zero

/-- The order of vanishing, read on the stalk of the unit-group presheaf of the sheaf of total
quotient rings. -/
def totalQuotientUnitOrder [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    TopCat.Presheaf.stalk (unitGroupPresheaf X.totalQuotientSheaf) x ⟶
      AddCommGrpCat.of (ULift.{u} ℤ) :=
  unitGroupStalkMap X.totalQuotientSheaf x ≫
    unitsAddCommGrpFunctor.map (totalQuotientStalkToFunctionField x) ≫
    AddCommGrpCat.ofHom ((AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp
      (functionFieldUnitOrder x))

/-- `AlgebraicGeometry.totalQuotientUnitOrder` is the comparison with the unit group of the
stalk, followed by the order of vanishing of the function field. -/
theorem totalQuotientUnitOrder_eq [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    totalQuotientUnitOrder x = unitGroupStalkMap X.totalQuotientSheaf x ≫
      unitsAddCommGrpFunctor.map (totalQuotientStalkToFunctionField x) ≫
      AddCommGrpCat.ofHom ((AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp
        (functionFieldUnitOrder x)) :=
  rfl

/-- The order of vanishing kills the units of the structure sheaf: a unit of the sections of
`𝒪_X` has order zero in the function field at every point of its domain. -/
theorem totalQuotientUnitOrder_kills_units [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    unitGroupMapStalk X.toTotalQuotientSheaf x ≫ totalQuotientUnitOrder x = 0 := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [unitGroupMapStalk_germ_assoc, totalQuotientUnitOrder_eq,
    unitGroupStalkMap_germ_assoc, unitGroupMap_app, comp_zero]
  ext v
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have hge : ∀ c, (totalQuotientStalkToFunctionField x)
        (TopCat.Presheaf.germ X.totalQuotientSheaf.obj U x hx
          (X.toTotalQuotientSheaf.hom.app (op U) c)) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx c) := fun c =>
    totalQuotientStalkToFunctionField_germ_apply x U hx c
  show X.ord ((totalQuotientStalkToFunctionField x)
      (TopCat.Presheaf.germ X.totalQuotientSheaf.obj U x hx
        (X.toTotalQuotientSheaf.hom.app (op U) (Additive.toMul v).val))) x = 0
  rw [hge]
  exact (congrArg (fun t => X.ord t x)
      (X.algebraMap_germ_eq_germToFunctionField hx (Additive.toMul v).val)).trans
    (X.ord_of_isUnit (Additive.toMul v).isUnit hx)

/-! ### The order on the stalk of the quotient sheaf -/

/-- The order of vanishing, read on the stalk of the quotient sheaf `𝒦_Xˣ / 𝒪_Xˣ`. -/
def cartierStalkOrder [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.stalk x ⟶
      AddCommGrpCat.of (ULift.{u} ℤ) :=
  (stalkSheafifyIso
        (cokernel (unitGroupMap X.toTotalQuotientSheaf)) x).inv ≫
    (PreservesCokernel.iso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        (unitGroupMap X.toTotalQuotientSheaf)).hom ≫
    cokernel.desc _ (totalQuotientUnitOrder x) (totalQuotientUnitOrder_kills_units x)

/-- The order on the stalk of the quotient sheaf is compatible with the projection from the
unit-group presheaf of the sheaf of total quotient rings. -/
@[reassoc] theorem rawUnitGroupQuotientMap_stalk_order [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (rawUnitGroupQuotientMap X.toTotalQuotientSheaf) ≫ cartierStalkOrder x =
      totalQuotientUnitOrder x := by
  refine (congrArg (fun t => t ≫ cartierStalkOrder x)
    (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (cokernel.π (unitGroupMap X.toTotalQuotientSheaf))
      (toSheafify (Opens.grothendieckTopology X)
        (cokernel (unitGroupMap X.toTotalQuotientSheaf))))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (cokernel.π (unitGroupMap X.toTotalQuotientSheaf)) ≫ t)
    ((stalkSheafifyIso
      (cokernel (unitGroupMap X.toTotalQuotientSheaf)) x).hom_inv_id_assoc
        ((PreservesCokernel.iso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
            (unitGroupMap X.toTotalQuotientSheaf)).hom ≫
          cokernel.desc _ (totalQuotientUnitOrder x)
            (totalQuotientUnitOrder_kills_units x)))).trans ?_
  exact (PreservesCokernel.π_iso_hom_assoc _ _ _).trans (cokernel.π_desc _ _ _)

/-! ### The coefficient of a Cartier divisor at a point -/

/-- **The order `v_Z(τ)` of Tag 02AR part (8).** The coefficient of a Cartier divisor at a point
of codimension one: the order of vanishing of a local representative. -/
@[ega "IV 21.6.7" "special case"]
def cartierMultiplicity [IsIntegral X] [IsLocallyNoetherian X] (τ : X.CartierDivisor) (x : X) :
    ℤ :=
  ((cartierStalkOrder x)
    ((unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.Γgerm x τ)).down

/-- The germ of the projection of a unit, followed by the order on the stalk of the quotient
sheaf, is the germ followed by the order on the unit-group stalk. -/
@[reassoc] theorem germ_cartierStalkOrder [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (U : X.Opens) (hx : x ∈ U) :
    (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) ≫
        (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.germ U x hx ≫
        cartierStalkOrder x =
      TopCat.Presheaf.germ (unitGroupPresheaf X.totalQuotientSheaf) U x hx ≫
        totalQuotientUnitOrder x :=
  ((((congrArg
          (fun t => TopCat.Presheaf.germ (unitGroupPresheaf X.totalQuotientSheaf) U x hx ≫ t)
          (rawUnitGroupQuotientMap_stalk_order x).symm).trans
        (Category.assoc _ _ _).symm).trans
      (congrArg (fun t => t ≫ cartierStalkOrder x)
        (TopCat.Presheaf.stalkFunctor_map_germ U x hx
          (rawUnitGroupQuotientMap X.toTotalQuotientSheaf)))).trans
    (Category.assoc _ _ _)).symm

/-- A Cartier divisor whose germ at a point vanishes has coefficient zero there. -/
theorem cartierMultiplicity_eq_zero_of_germ_eq_zero [IsIntegral X] [IsLocallyNoetherian X]
    (τ : X.CartierDivisor) (x : X)
    (hτ : (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.Γgerm x τ = 0) :
    cartierMultiplicity τ x = 0 := by
  show ((cartierStalkOrder x)
    ((unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.Γgerm x τ)).down = 0
  rw [hτ]
  simp

/-- The coefficient of a Cartier divisor at a point, computed from a local representative in the
unit-group presheaf of the sheaf of total quotient rings. -/
theorem cartierMultiplicity_local [IsIntegral X] [IsLocallyNoetherian X] (τ : X.CartierDivisor)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U))
    (hτ : (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map (homOfLE le_top).op τ =
      (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) v) :
    cartierMultiplicity τ x =
      X.ord ((totalQuotientStalkToFunctionField x)
        (X.totalQuotientSheaf.presheaf.germ U x hx (Additive.toMul v).val)) x := by
  have h1 := TopCat.Presheaf.Γgerm_res_apply
    (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf (i := homOfLE le_top) x hx τ
  have h2 := ConcreteCategory.congr_hom (germ_cartierStalkOrder x U hx) v
  have h3 := ConcreteCategory.congr_hom (unitGroupStalkMap_germ X.totalQuotientSheaf x U hx) v
  have h2' : (cartierStalkOrder x)
        ((unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.germ U x hx
          ((rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) v)) =
      (totalQuotientUnitOrder x)
        (TopCat.Presheaf.germ (unitGroupPresheaf X.totalQuotientSheaf) U x hx v) := h2
  have h3' : (unitGroupStalkMap X.totalQuotientSheaf x)
        (TopCat.Presheaf.germ (unitGroupPresheaf X.totalQuotientSheaf) U x hx v) =
      (unitsAddCommGrpFunctor.map (X.totalQuotientSheaf.presheaf.germ U x hx)) v := h3
  show ((cartierStalkOrder x)
    ((unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.Γgerm x τ)).down = _
  rw [← h1, hτ, h2']
  show ((AddCommGrpCat.ofHom ((AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp
        (functionFieldUnitOrder x)))
      ((unitsAddCommGrpFunctor.map (totalQuotientStalkToFunctionField x))
        ((unitGroupStalkMap X.totalQuotientSheaf x)
          (TopCat.Presheaf.germ (unitGroupPresheaf X.totalQuotientSheaf) U x hx v)))).down = _
  rw [h3']
  rfl

/-! ### The order of a germ of a regular function -/

/-- **Tag 02MD at a codimension-one point.** The order of vanishing of the image in the function
field of an element of the local ring is the length of the quotient of the local ring by the
ideal it generates. -/
theorem ord_algebraMap_stalk [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hx : Order.coheight x = 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {a})).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha' := mem_nonZeroDivisors_iff_ne_zero.mpr ha
  rw [X.ord_eq_iff hx ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha)]
  show Ring.ordFrac (X.presheaf.stalk x) (algebraMap _ _ a) = _
  rw [Ring.ordFrac_eq_ord (X.presheaf.stalk x) ha]
  exact Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk x) ha'
    (ENat.natCast_toNat (Ring.ord_ne_top ha')).symm

/-- If a Cartier divisor is represented near a point by `a / b` with `b` nonzero, then in the
function field the germs of `b` and of the representing unit are nonzero and the germs satisfy the
relation `v * b = a`. -/
private theorem germ_nonzero_and_mul_of_local_representation [IsIntegral X]
    [IsLocallyNoetherian X] {U : X.Opens} {x : X} (hx : x ∈ U) {a b : Γ(X, U)} (hb : b ≠ 0)
    (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U))
    (hab : (Additive.toMul v).val * X.toTotalQuotientSheaf.hom.app (op U) b =
      X.toTotalQuotientSheaf.hom.app (op U) a) :
    X.presheaf.germ U x hx b ≠ 0 ∧
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx b) ≠ 0 ∧
    (totalQuotientStalkToFunctionField x)
      (X.totalQuotientSheaf.presheaf.germ U x hx (Additive.toMul v).val) ≠ 0 ∧
    (totalQuotientStalkToFunctionField x)
        (X.totalQuotientSheaf.presheaf.germ U x hx (Additive.toMul v).val) *
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx b) =
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) := by
  let g := X.totalQuotientSheaf.presheaf.germ U x hx ≫ totalQuotientStalkToFunctionField x
  have hg : ∀ c : Γ(X, U), g (X.toTotalQuotientSheaf.hom.app (op U) c) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx c) := fun c =>
    totalQuotientStalkToFunctionField_germ_apply x U hx c
  have hmul := ConcreteCategory.congr_arg g hab
  rw [map_mul, hg, hg] at hmul
  have hbO : X.presheaf.germ U x hx b ≠ 0 := fun h =>
    hb (germ_injective_of_isIntegral X x hx (by simpa using h))
  exact ⟨hbO, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hbO,
    (((Additive.toMul v).isUnit).map (ConcreteCategory.hom g)).ne_zero, hmul⟩

/-- If a Cartier divisor is represented near a point by the fraction `a / b` of two regular
functions with `b` nonzero, then `a` is nonzero: in the function field the representing unit is
nonzero and so is the image of `b`. -/
theorem ne_zero_of_local_representation [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens}
    {x : X} (hx : x ∈ U) {a b : Γ(X, U)} (hb : b ≠ 0)
    (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U))
    (hab : (Additive.toMul v).val * X.toTotalQuotientSheaf.hom.app (op U) b =
      X.toTotalQuotientSheaf.hom.app (op U) a) :
    a ≠ 0 := by
  intro h0
  obtain ⟨-, hbK, hvK, hmul⟩ := germ_nonzero_and_mul_of_local_representation hx hb v hab
  rw [h0, map_zero, map_zero] at hmul
  exact mul_ne_zero hvK hbK hmul

/-- **Tag 02AR part (8), clause (b).** When a Cartier divisor is represented near a
codimension-one point `x` by a fraction `a / b` of regular functions on an open neighbourhood,
its coefficient at `x` is the difference of the lengths of the quotients of the local ring by the
germs of the numerator and the denominator. -/
@[ega "IV 21.6.7" "partial"]
theorem cartierMultiplicity_eq_sub_of_local [IsIntegral X] [IsLocallyNoetherian X]
    (τ : X.CartierDivisor) (x : X) (hcoh : Order.coheight x = 1)
    (U : X.Opens) (hx : x ∈ U) (a b : Γ(X, U)) (hb : b ≠ 0)
    (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U))
    (hab : (Additive.toMul v).val * (X.toTotalQuotientSheaf.hom.app (op U) b) =
      X.toTotalQuotientSheaf.hom.app (op U) a)
    (hτ : (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map (homOfLE le_top).op τ =
      (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) v) :
    cartierMultiplicity τ x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx a})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx b})).toNat : ℤ) := by
  rw [cartierMultiplicity_local τ x U hx v hτ]
  obtain ⟨hbO, hbK, hvK, hmul⟩ := germ_nonzero_and_mul_of_local_representation hx hb v hab
  have haO : X.presheaf.germ U x hx a ≠ 0 := fun ha =>
    ne_zero_of_local_representation hx hb v hab
      (germ_injective_of_isIntegral X x hx (by simpa using ha))
  have hord := X.ord_mul (x := x) hvK hbK
  rw [hmul, ord_algebraMap_stalk x hcoh _ haO, ord_algebraMap_stalk x hcoh _ hbO] at hord
  exact eq_sub_iff_add_eq.mpr hord.symm

/-- The sheafification unit of the presheaf of total quotient rings commutes with restriction:
if a section `r` over `W` sheafifies to the restriction of `s` from `V ⊇ W`, then the restriction
of `r` to `U ⊆ W` sheafifies to the restriction of `s` to `U`. -/
theorem toSheafify_totalQuotientPresheaf_map_eq {U W V : X.Opens} (hUW : U ≤ W) (hWV : W ≤ V)
    {r : X.presheaf.totalQuotientPresheaf.obj (op W)} {s : X.totalQuotientSheaf.presheaf.obj (op V)}
    (hr : (toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op W) r =
      X.totalQuotientSheaf.presheaf.map (homOfLE hWV).op s) :
    (toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf).app (op U)
        (X.presheaf.totalQuotientPresheaf.map (homOfLE hUW).op r) =
      X.totalQuotientSheaf.presheaf.map (homOfLE (hUW.trans hWV)).op s := by
  have hnat : (toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)
          (X.presheaf.totalQuotientPresheaf.map (homOfLE hUW).op r) =
      X.totalQuotientSheaf.presheaf.map (homOfLE hUW).op
        ((toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf).app (op W) r) :=
    ConcreteCategory.congr_hom ((toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).naturality (homOfLE hUW).op) r
  have hcomp : (homOfLE hWV).op ≫ (homOfLE hUW).op = (homOfLE (hUW.trans hWV)).op :=
    Subsingleton.elim _ _
  have h : X.totalQuotientSheaf.presheaf.map (homOfLE hUW).op
        (X.totalQuotientSheaf.presheaf.map (homOfLE hWV).op s) =
      X.totalQuotientSheaf.presheaf.map ((homOfLE hWV).op ≫ (homOfLE hUW).op) s :=
    (ConcreteCategory.congr_hom
      (X.totalQuotientSheaf.presheaf.map_comp (homOfLE hWV).op (homOfLE hUW).op) s).symm
  rw [hnat, hr, h, hcomp]

/-- Restricting a unit of the sheaf of total quotient rings whose image in the quotient sheaf is
the restriction of a Cartier divisor `τ` gives a unit whose image is again the restriction of
`τ`. -/
theorem rawUnitGroupQuotientMap_app_map_eq {U V : X.Opens} (hUV : U ≤ V) (τ : X.CartierDivisor)
    {v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op V)}
    (hv : (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op V) v =
      (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op τ) :
    (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U)
        ((unitGroupPresheaf X.totalQuotientSheaf).map (homOfLE hUV).op v) =
      (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op τ := by
  have hnat : (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U)
        ((unitGroupPresheaf X.totalQuotientSheaf).map (homOfLE hUV).op v) =
      (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map (homOfLE hUV).op
        ((rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op V) v) :=
    ConcreteCategory.congr_hom
      ((rawUnitGroupQuotientMap X.toTotalQuotientSheaf).naturality (homOfLE hUV).op) v
  have hcomp : (homOfLE (show V ≤ ⊤ from le_top)).op ≫ (homOfLE hUV).op =
      (homOfLE (show U ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  have hmc := ConcreteCategory.congr_hom
    ((unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map_comp
      (homOfLE (show V ≤ ⊤ from le_top)).op (homOfLE hUV).op) τ
  rw [hnat, hv]
  exact (((congrArg (fun m => (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map m τ)
    hcomp).symm.trans hmc).trans (CategoryTheory.comp_apply _ _ τ)).symm

/-- **Tag 02AR part (8), the local presentation of clause (b).** Near any point of a locally
Noetherian integral scheme, a Cartier divisor is the image of a unit of the sheaf of total
quotient rings over an affine open neighbourhood, and that unit is the fraction `a / b` of two
regular functions on that neighbourhood with `b` nonzero. -/
@[stacks 02AR "cartier_weil_divisor"]
theorem exists_affineOpen_local_representation [IsIntegral X] [IsLocallyNoetherian X]
    (τ : X.CartierDivisor) (x : X) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (a b : Γ(X, U)) (_ : b ≠ 0)
      (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U)),
      (Additive.toMul v).val * X.toTotalQuotientSheaf.hom.app (op U) b =
          X.toTotalQuotientSheaf.hom.app (op U) a ∧
        (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map (homOfLE le_top).op τ =
          (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) v := by
  classical
  obtain ⟨V, hVle, ⟨c, hc⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp
      (isLocallySurjective_toSheafify_addCommGrpCat
        (cokernel (unitGroupMap X.toTotalQuotientSheaf))) ⊤ τ x (by simp)
  obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V))).mp inferInstance c
  obtain ⟨W, hWV, ⟨r, hr⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp
      (isLocallySurjective_toSheafify_commRingCat X.presheaf.totalQuotientPresheaf)
      V (Additive.toMul v).val x hxV
  let V' : X.Opens := ⟨V.1, V.2⟩
  let W' : X.Opens := ⟨W.1, W.2⟩
  have hWV' : W' ≤ V' := hWV
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W' from hxW)
  let vU := (unitGroupPresheaf X.totalQuotientSheaf).map (homOfLE (hUW.trans hWV')).op v
  let rU := X.presheaf.totalQuotientPresheaf.map (homOfLE hUW).op r
  have hrU : (toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op U) rU = (Additive.toMul vU).val :=
    toSheafify_totalQuotientPresheaf_map_eq hUW hWV' hr
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let _ : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom.toAlgebra
  have _ : IsLocalization (nonZeroDivisors Γ(X, U))
      (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) rU
  refine ⟨U, hU, hxU, a, b, nonZeroDivisors.ne_zero b.2, vU, ?_, ?_⟩
  · have hm := ConcreteCategory.congr_arg
      ((toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)) hab
    rwa [map_mul, hrU] at hm
  · have hv' : (cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V') v = c := hv
    refine (rawUnitGroupQuotientMap_app_map_eq (hUW.trans hWV') τ ?_).symm
    show (toSheafify (Opens.grothendieckTopology X)
        (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op V')
      ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V') v) = _
    rw [hv']
    exact hc

/-! ### Finiteness of the support -/

/-- The generic point of a prime divisor has coheight one in the specialization order. -/
theorem PrimeDivisor.coheight_genericPoint_eq_one (Z : PrimeDivisor X) :
    Order.coheight Z.genericPoint = 1 := by
  have h : ringKrullDim (X.presheaf.stalk Z.genericPoint) = 1 :=
    Z.ringKrullDim_stalk_genericPoint_eq_one
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- On a Noetherian integral scheme only finitely many prime divisors have their generic point
in a given proper closed subset: the underlying closed subset of such a prime divisor is an
irreducible component of that subset, and a prime divisor is determined by its underlying closed
subset. -/
theorem PrimeDivisor.finite_setOf_genericPoint_mem [IsNoetherian X] [IsIntegral X] {D : Set X}
    (hDclosed : IsClosed D) (hDproper : D ≠ Set.univ) :
    {Z : PrimeDivisor X | Z.genericPoint ∈ D}.Finite := by
  classical
  have : NoetherianSpace D := NoetherianSpace.of_subset (Set.subset_univ D)
  have : Finite (irreducibleComponents D) := NoetherianSpace.finite_irreducibleComponents
  set S : Type u := {Z : PrimeDivisor X // Z.genericPoint ∈ D} with hS
  have key (Z : S) : ∃ C : irreducibleComponents D,
      Subtype.val '' (C.1 : Set D) = (Z.1.support : Set X) := by
    obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({(⟨Z.1.genericPoint, Z.2⟩ : D)} : Set D))
      (isIrreducible_iff_closure.mpr isIrreducible_singleton)
    have hCclosed : IsClosed C := isClosed_of_mem_irreducibleComponents _ hC
    have hiClosed := hDclosed.isClosedEmbedding_subtypeVal
    refine ⟨⟨C, hC⟩, (Z.1.support_eq_of_isIrreducible (hiClosed.isClosedMap _ hCclosed)
      (IsIrreducible.image hC.1 _ hiClosed.continuous.continuousOn)
      (D := D) (fun y hy => by obtain ⟨z, -, rfl⟩ := hy; exact z.property)
      ⟨_, hyC (subset_closure rfl), rfl⟩ hDproper)⟩
  choose c hc using key
  have hinj : Function.Injective c := fun Z W hZW =>
    Subtype.ext (PrimeDivisor.eq_of_support_eq ((hc Z).symm.trans (hZW ▸ hc W)))
  have : Finite S := Finite.of_injective c hinj
  exact Set.Finite.subset (Set.finite_range (Subtype.val : S → PrimeDivisor X))
    fun Z hZ => ⟨⟨Z, hZ⟩, rfl⟩

/-- Where a regular function is invertible, the quotient of the local ring by the ideal its germ
generates is trivial, so that quotient has length zero. -/
theorem length_quotient_span_germ_eq_zero_of_mem_basicOpen {U : X.Opens} (a : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hx : x ∈ X.basicOpen a) :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU a}) = 0 := by
  have hu : IsUnit (X.presheaf.germ U x hxU a) := (X.mem_basicOpen a x hxU).mp hx
  rw [Ideal.span_singleton_eq_top.mpr hu]
  have : Subsingleton ((X.presheaf.stalk x) ⧸ (⊤ : Ideal (X.presheaf.stalk x))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

/-- **Tag 02AR part (8), finite support.** The coefficient family of a Cartier divisor on a
Noetherian integral scheme is finitely supported, so it is a finite formal linear combination of
prime divisors.  A prime divisor with nonzero coefficient has its generic point outside the
intersection of the nonvanishing loci of a local numerator and denominator, which is a proper
closed subset, and only finitely many prime divisors have their generic point in such a
subset. -/
theorem finite_cartierMultiplicity_support [IsNoetherian X] [IsIntegral X]
    (τ : X.CartierDivisor) :
    (Function.support fun Z : PrimeDivisor X => cartierMultiplicity τ Z.genericPoint).Finite := by
  classical
  choose U hU hxU a b hb v hab hτ using exists_affineOpen_local_representation τ
  have hay : ∀ y : X, a y ≠ 0 := fun y =>
    ne_zero_of_local_representation (hxU y) (hb y) (v y) (hab y)
  have hproper : ∀ y : X,
      (((X.basicOpen (a y) ⊓ X.basicOpen (b y) : X.Opens) : Set X)ᶜ) ≠ Set.univ := by
    intro y h
    have hna := (TopologicalSpace.Opens.ne_bot_iff_nonempty (X.basicOpen (a y))).mp
      fun hh => hay y ((basicOpen_eq_bot_iff _).mp hh)
    have hnb := (TopologicalSpace.Opens.ne_bot_iff_nonempty (X.basicOpen (b y))).mp
      fun hh => hb y ((basicOpen_eq_bot_iff _).mp hh)
    obtain ⟨z, -, hz⟩ := (IrreducibleSpace.isIrreducible_univ X).2 _ _
      (X.basicOpen (a y)).isOpen (X.basicOpen (b y)).isOpen
      (by simpa using hna) (by simpa using hnb)
    have hzc : z ∈ (((X.basicOpen (a y) ⊓ X.basicOpen (b y) : X.Opens) : Set X)ᶜ) :=
      h ▸ Set.mem_univ z
    exact hzc (by simpa using hz)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : X => ((U y : X.Opens) : Set X))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hxU y⟩)
  apply Set.Finite.subset (t.finite_toSet.biUnion fun y _ =>
    PrimeDivisor.finite_setOf_genericPoint_mem
      (X.basicOpen (a y) ⊓ X.basicOpen (b y) : X.Opens).isOpen.isClosed_compl (hproper y))
  intro Z hZ
  obtain ⟨y, hyt, hyZ⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ Z.genericPoint))
  refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  show Z.genericPoint ∈ (((X.basicOpen (a y) ⊓ X.basicOpen (b y) : X.Opens) : Set X)ᶜ)
  intro hmem
  apply hZ
  show cartierMultiplicity τ Z.genericPoint = 0
  rw [cartierMultiplicity_eq_sub_of_local τ Z.genericPoint
      Z.coheight_genericPoint_eq_one (U y) hyZ (a y) (b y) (hb y) (v y) (hab y) (hτ y),
    length_quotient_span_germ_eq_zero_of_mem_basicOpen (a y) hyZ hmem.1,
    length_quotient_span_germ_eq_zero_of_mem_basicOpen (b y) hyZ hmem.2]
  simp

/-! ### The Weil divisor of a Cartier divisor -/

/-- **Stacks 02AR part (8).** The Weil divisor `[τ] = Σ v_Z(τ) [Z]` of a Cartier divisor on a
Noetherian integral scheme. -/
@[stacks 02AR "cartier_weil_divisor"]
def cartierWeilDivisor [IsNoetherian X] [IsIntegral X] (τ : X.CartierDivisor) : WeilDivisor X :=
  ⟨fun Z => cartierMultiplicity τ Z.genericPoint,
    (mem_weilDivisor_iff_finite_support _).mpr (finite_cartierMultiplicity_support τ)⟩

/-- **Stacks 02AR part (8).** The coefficient of `[τ]` at a prime divisor is the order
`v_Z(τ)`. -/
@[stacks 02AR "cartier_weil_divisor"]
theorem cartierWeilDivisor_apply [IsNoetherian X] [IsIntegral X] (τ : X.CartierDivisor)
    (Z : PrimeDivisor X) :
    (cartierWeilDivisor τ).1 Z = cartierMultiplicity τ Z.genericPoint :=
  rfl

/-- **Stacks 02AR part (8), clause (a).** The coefficient of `[τ]` vanishes at a prime divisor at
whose generic point the germ of `τ` is zero. -/
@[stacks 02AR "cartier_weil_divisor"]
theorem cartierWeilDivisor_apply_of_germ_eq_zero [IsNoetherian X] [IsIntegral X]
    (τ : X.CartierDivisor) (Z : PrimeDivisor X)
    (hτ : (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.Γgerm Z.genericPoint τ = 0) :
    (cartierWeilDivisor τ).1 Z = 0 :=
  cartierMultiplicity_eq_zero_of_germ_eq_zero τ Z.genericPoint hτ

/-- **Stacks 02AR part (8), clause (b).** The coefficient of `[τ]` at a prime divisor computed
from a local presentation `a / b` of `τ` on an open neighbourhood of its generic point. -/
@[stacks 02AR "cartier_weil_divisor"]
theorem cartierWeilDivisor_apply_of_local_eq [IsNoetherian X] [IsIntegral X]
    (τ : X.CartierDivisor) (Z : PrimeDivisor X) (U : X.Opens) (hξ : Z.genericPoint ∈ U)
    (a b : Γ(X, U)) (hb : b ≠ 0)
    (v : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U))
    (hab : (Additive.toMul v).val * X.toTotalQuotientSheaf.hom.app (op U) b =
      X.toTotalQuotientSheaf.hom.app (op U) a)
    (hτ : (unitGroupQuotientSheaf X.toTotalQuotientSheaf).presheaf.map (homOfLE le_top).op τ =
      (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U) v) :
    (cartierWeilDivisor τ).1 Z =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸
          Ideal.span {X.presheaf.germ U Z.genericPoint hξ a})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸
          Ideal.span {X.presheaf.germ U Z.genericPoint hξ b})).toNat : ℤ) :=
  cartierMultiplicity_eq_sub_of_local τ Z.genericPoint Z.coheight_genericPoint_eq_one U hξ a b hb
    v hab hτ

/-- The Weil divisor of a Cartier divisor, read as a finite formal linear combination of prime
divisors through `AlgebraicGeometry.weilDivisorEquivFinsupp`. -/
theorem weilDivisorEquivFinsupp_cartierWeilDivisor [IsNoetherian X] [IsIntegral X]
    (τ : X.CartierDivisor) :
    weilDivisorEquivFinsupp (cartierWeilDivisor τ) =
      Finsupp.ofSupportFinite (fun Z : PrimeDivisor X => cartierMultiplicity τ Z.genericPoint)
        (finite_cartierMultiplicity_support τ) := by
  ext Z
  rfl

end Order

end AlgebraicGeometry

end
