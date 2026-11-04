module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerHomotopyGerm
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeMap
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiCokernel

/-!
# The stalk of the null homotopy inside the canonical map of Stacks 0E1Y

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a topological
space `T` and let `z` be a point of `T`.  The composite
`c₁ ≫ g : NL_{B/A} ⊗_B C ⟶ NL_{C/A} ⟶ NL_{C/B}` is null homotopic, the homotopy being
`Stacks.SheafOfModules.baseChangeRelativeNullHomotopy`, concentrated in bidegree `(0, -1)`; its
single component `h` is what the canonical map `c` of Stacks 0E1Y contributes to the shifted cone
(`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`).

This file identifies the stalk at `z` of that component with
`NaiveCotangent.towerNullHomotopyBaseChange`, the base change to `C_z` of the homotopy of
Stacks 07VC for the tower of stalk rings `A_z → B_z → C_z`, the two sides being compared through
the identification `Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivZero` of the
stalk of the source and the degree `-1` leg of Stacks 0D09
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear`) on the target.

## The proof

`h` is the extension of scalars along `b` of the explicit homotopy
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy` of the tower, followed by the counit of
extension and restriction of scalars
(`Stacks.SheafOfModules.baseChangeRelativeNullHomotopy_hom_zero_negOne`), so its stalk splits
into the same three legs as the stalk of the canonical map `c₁` in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeComparison`.  On a pure tensor
`t ⊗ κ`:

* the interchange of extension of scalars with taking stalks turns the first leg into
  `t ⊗ (stalk of the homotopy) κ`, by `Opens.stalkTowerExtendScalarsObj_map_inv_tmul` — the
  object-level form of that naturality, which is what a homotopy component needs, a bare morphism
  out of the degree `0` term not being a chain map;
* the second leg multiplies out, by `Opens.stalkFunctor_map_towerCounit_apply`,
  `Opens.restrictScalarsStalkFunctorIso_hom_app_apply` and
  `ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul`, exactly as for `c₁`;
* the scalar crosses the leg of Stacks 0D09 by
  `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_smul_fiber`, and the leg carries the
  stalk of the homotopy to `NaiveCotangent.towerNullHomotopy` on a basis element, which is
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_cotangentSpaceBasis`.

That computes the two sides on `t ⊗ d[s]` for every `t` and every basis element `d[s]` of
`Ω_{A_z[B_z]/A_z} ⊗ B_z`, which is all that the ring-level description of the homotopy supplies.
It is however enough: `Stacks.NaiveCotangentStalkBaseChange.tmul_basis_ext` says that two
*additive* maps out of `C_z ⊗_{B_z} M`, for `M` free over `B_z`, which agree on every
`t ⊗ (basis element)` are equal, because the coefficients of a general element of `M` move into
the left-hand factor of the tensor.  No linearity over `B_z` of the stalk legs is needed, and
none is available: the project's linear legs are linear over the `RingCat`-valued stalk while the
ring-level homotopy is linear over the `CommRingCat`-valued stalk `B_z`, and an action of the
latter on these stalks cannot be elaborated within the heartbeat ceiling (recorded at
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsLinear`).

## Main results

* `Stacks.NaiveCotangentStalkBaseChange.tmul_basis_ext`: two additive maps out of a base change
  along a free module which agree on the pure tensors with a basis element on the right agree.
* `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_eqToHom_negOne`: the degree `-1`
  leg of Stacks 0D09 absorbs the transport `eqToHom` between the degree `-1` term of `NL_{C/B}`
  and the conormal sheaf of the canonical presentation.
* `Stacks.NaiveCotangentStalkBaseChange.stalkFunctor_map_towerHomotopyWithTransport`: the stalk
  of the explicit homotopy of the tower, preceded by that transport in degree `0`, is
  `Stacks.SheafOfModules.naiveCotangentTowerHomotopyStalk`.
* `Stacks.NaiveCotangentStalkBaseChange.stalkFunctor_map_baseChangeRelativeNullHomotopy_apply`:
  the stalk of `h`, split into its three legs.
* `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_tmul`:
  **the stalk of `h` on a pure tensor with a basis element.**
* `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeRelativeNullHomotopy`:
  **the stalk of `h` is `NaiveCotangent.towerNullHomotopyBaseChange`.**

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map and
  the homotopy of its proof.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the null homotopy of a
  tower over a ring.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension and
  restriction of scalars for sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkBaseChange

open Stacks.SheafOfModules Stacks.NaiveCotangentAffineStalkLegs
open Stacks.RelativeDifferentialStalk (algebraStalk)

/-! ### Additive maps out of a base change along a free module -/

/-- **Extensionality for additive maps out of a base change along a free module.**  Two additive
maps out of `S ⊗[R] M`, for `M` an `R`-module with basis `β`, which agree on every pure tensor
`s ⊗ β i`, are equal.

A pure tensor `s ⊗ m` is the finite sum of the pure tensors `(r • s) ⊗ β i` over the basis
expansion `m = ∑ r • β i`, the coefficients moving into the left-hand factor by
`TensorProduct.smul_tmul`; so additivity and the hypothesis determine the map on pure tensors,
and `TensorProduct.induction_on` finishes.  This is what makes a description of a map on basis
elements enough, with no linearity of either side over `R`. -/
theorem tmul_basis_ext {R S M P : Type*} {ι : Type*} [CommSemiring R] [AddCommMonoid S]
    [AddCommMonoid M] [Module R S] [Module R M] [AddCommMonoid P] (β : Module.Basis ι R M)
    (F G : TensorProduct R S M →+ P)
    (h : ∀ (s : S) (i : ι), F (s ⊗ₜ[R] β i) = G (s ⊗ₜ[R] β i)) (x : TensorProduct R S M) :
    F x = G x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s m =>
      rw [← β.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum,
        TensorProduct.tmul_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← TensorProduct.smul_tmul]
      exact h _ i
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-! ### The two transports of Stacks 0D09 -/

/-- **The degree `-1` leg of Stacks 0D09 absorbs the transport out of the conormal sheaf.**  The
degree `-1` term of `NL_{C/B}` *is* the conormal sheaf of the canonical presentation of `C` over
`B` (`Stacks.SheafOfModules.naiveCotangentComplex_X_negOne`); the leg of Stacks 0D09 is the
identification `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` of the stalk of that
conormal sheaf preceded by the transport, so composing with the transport in the other direction
leaves the identification alone. -/
theorem stalkLegNegOneLinear_eqToHom_negOne
    (ζ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (cSheaf B C b).val.presheaf z)) :
    letI := algebraStalk b.hom z
    stalkLegNegOneLinear B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) B C b).symm)).hom ζ) =
      naiveCotangentStalkCotangentEquiv B C b z ζ := by
  let := algebraStalk b.hom z
  have hcancel : ∀ (M N : _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C)) (e : M = N)
      (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf z)),
      stalkAddEquivOfIso z (eqToIso e)
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
              (eqToHom e.symm)).hom w) = w := by
    intro M N e w
    subst e
    simp only [stalkAddEquivOfIso, eqToHom_refl, eqToIso_refl,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.mapIso_refl]
    rfl
  refine Eq.trans (stalkLegNegOneLinear_apply B C b z _) ?_
  refine Eq.trans (stalkLegNegOne_apply B C b z _) ?_
  exact congrArg (naiveCotangentStalkCotangentEquiv B C b z)
    (hcancel _ _ (naiveCotangentComplex_X_negOne.{u, u, u, u}
      (Opens.grothendieckTopology T) B C b) ζ)

/-- The explicit homotopy of the tower `A ⟶ B ⟶ C`, preceded by the transport identifying the
degree `0` term of `NL_{B/A}` with the sheaf `B ⊗_{A[B]} Ω_{A[B]/A}` it is built from.  This is
the morphism of sheaves of `B`-modules whose extension of scalars along `b` is the first leg of
`Stacks.SheafOfModules.baseChangeRelativeNullHomotopy` in bidegree `(0, -1)`. -/
noncomputable abbrev towerHomotopyWithTransport :
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X 0 ⟶
      (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite.{u, u, u} b)).obj
        ((canonicalConormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology T) B C b).X₁) :=
  eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a) ≫
    naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b (𝟙 B)
      (Category.id_comp b) (Category.comp_id a)

/-- **The stalk of the explicit homotopy of the tower, read through the degree `0` leg of
Stacks 0D09, is `Stacks.SheafOfModules.naiveCotangentTowerHomotopyStalk`.**  The leg is the
identification `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv` preceded by the
transport out of the degree `0` term, so composing with that transport cancels it and leaves the
stalk of the homotopy itself. -/
theorem stalkFunctor_map_towerHomotopyWithTransport
    (κ : letI := algebraStalk a.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace) :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangentSpace A B a z
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
        (towerHomotopyWithTransport A B C a b)).hom
        ((stalkLegZeroLinear A B a z).symm κ) =
      naiveCotangentTowerHomotopyStalk B C b z A a
        ((naiveCotangentStalkCotangentSpaceEquiv A B a z).symm κ) := by
  let := algebraStalk a.hom z
  let := moduleRingStalkCotangentSpace A B a z
  refine Eq.trans (stalkMap_comp_apply z
    (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
      (Opens.grothendieckTopology T) A B a))
    (naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b
      (𝟙 B) (Category.id_comp b) (Category.comp_id a)) _) ?_
  refine congrArg (naiveCotangentTowerHomotopyStalk B C b z A a) ?_
  exact (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology T) A B a))).apply_symm_apply
      ((naiveCotangentStalkCotangentSpaceEquiv A B a z).symm κ)

/-! ### The stalk of the homotopy component of the canonical map -/

/-- **The homotopy component of the canonical map of Stacks 0E1Y, on stalks, split into its three
legs**: the extension of scalars of the explicit homotopy of the tower, the counit of extension
and restriction of scalars, and the transport onto the degree `-1` term of `NL_{C/B}`. -/
theorem stalkFunctor_map_baseChangeRelativeNullHomotopy_apply
    (ζ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X 0))) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
          (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom ζ =
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) B C b).symm)).hom
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
                (Opens.grothendieckTopology T) B C b).counit.app
              ((canonicalConormalSequence.{u, u, u, u}
                (Opens.grothendieckTopology T) B C b).X₁))).hom
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
              ((Stacks.SheafOfModules.towerExtendScalars.{u, u, u}
                  (Opens.grothendieckTopology T) B C b).map
                (towerHomotopyWithTransport A B C a b))).hom ζ)) := by
  refine Eq.trans (congrArg (fun ψ => ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map ψ).hom ζ)
    (baseChangeRelativeNullHomotopy_hom_zero_negOne.{u, u, u}
      (Opens.grothendieckTopology T) A B C a b)) ?_
  rw [CategoryTheory.Functor.map_comp (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z),
    CategoryTheory.Functor.map_comp (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z)]
  rfl

/-- **The stalk of the homotopy component of the canonical map of Stacks 0E1Y, on a pure
tensor.**  On the image under `Opens.stalkTowerExtendScalarsXIso` of `c ⊗ ω` the stalk of the
homotopy is `c · (stalk of the explicit homotopy of the tower) ω`, read through the degree `-1`
identification of Stacks 0D09.

The three legs of `stalkFunctor_map_baseChangeRelativeNullHomotopy_apply` are computed in turn:
the interchange by `Opens.stalkTowerExtendScalarsObj_map_inv_tmul`, the counit by
`Opens.stalkFunctor_map_towerCounit_apply` together with
`Opens.restrictScalarsStalkFunctorIso_hom_app_apply` and
`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul`, and the transport by
`stalkLegNegOneLinear_eqToHom_negOne`; the scalar crosses the leg by
`stalkLegNegOneLinear_smul_fiber`. -/
theorem stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_inv_tmul
    (c : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj))
    (ω : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
        ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X 0))) :
    letI := algebraStalk b.hom z
    stalkLegNegOneLinear B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
            (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom
          ((Opens.stalkTowerExtendScalarsXIso z B C b
              (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).inv
            (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
              Stacks.SitePointBaseChange.stalkRingHom b.hom
                (Opens.pointGrothendieckTopology z)] ω))) =
      fiberStalkRingEquiv C z c •
        naiveCotangentStalkCotangentEquiv B C b z
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
              (towerHomotopyWithTransport A B C a b)).hom ω) := by
  let := algebraStalk b.hom z
  refine Eq.trans (congrArg (stalkLegNegOneLinear B C b z)
    (stalkFunctor_map_baseChangeRelativeNullHomotopy_apply A B C a b z _)) ?_
  let Φ := fun ξ => stalkLegNegOneLinear B C b z
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) B C b).symm)).hom ξ)
  refine Eq.trans (congrArg (fun ξ => Φ
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
                (Opens.grothendieckTopology T) B C b).counit.app
              ((canonicalConormalSequence.{u, u, u, u}
                (Opens.grothendieckTopology T) B C b).X₁))).hom ξ))
    (Opens.stalkTowerExtendScalarsObj_map_inv_tmul z B C b
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X 0)
      ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite.{u, u, u} b)).obj
        ((canonicalConormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology T) B C b).X₁))
      (towerHomotopyWithTransport A B C a b) c ω)) ?_
  refine Eq.trans (congrArg Φ
    (Opens.stalkFunctor_map_towerCounit_apply z B C b
      ((canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) B C b).X₁) _)) ?_
  refine Eq.trans (congrArg Φ
    (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul
      (Stacks.SitePointBaseChange.stalkRingHom b.hom
        (Opens.pointGrothendieckTopology z)) _ c
      ((Opens.restrictScalarsStalkFunctorIso z B C b).hom.app _
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
            (towerHomotopyWithTransport A B C a b)).hom ω)))) ?_
  refine Eq.trans (congrArg (fun m => Φ
        (@SMul.smul (ToType (TopCat.Presheaf.stalk (Tensor.ringSheaf C).obj z)) _ inferInstance
          ((Opens.commRingFiberStalkHom z C).hom c) m))
    (Opens.restrictScalarsStalkFunctorIso_hom_app_apply z B C b _ _)) ?_
  refine Eq.trans (congrArg (stalkLegNegOneLinear B C b z)
    (LinearMap.map_smul ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) B C b).symm)).hom
      ((Opens.commRingFiberStalkHom z C).hom c) _)) ?_
  refine Eq.trans (stalkLegNegOneLinear_smul_fiber B C b z c _) ?_
  exact congrArg (fun y => fiberStalkRingEquiv C z c • y)
    (stalkLegNegOneLinear_eqToHom_negOne B C b z _)

/-- **The stalk of the homotopy component of the canonical map of Stacks 0E1Y, on a pure tensor
of the stalk of its source.**  This is
`stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_inv_tmul` read through the identification
`stalkBaseChangeAddEquivZero` of that stalk with `C_z ⊗_{B_z} (Ω_{A_z[B_z]/A_z} ⊗ B_z)`. -/
theorem stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_symm_tmul
    (t : ToType (TopCat.Presheaf.stalk C.obj z))
    (κ : letI := algebraStalk a.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegNegOneLinear B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
            (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom
          ((stalkBaseChangeAddEquivZero A B C a b z).symm
            (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] κ))) =
      t • naiveCotangentStalkCotangentEquiv B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
            (towerHomotopyWithTransport A B C a b)).hom
          ((stalkLegZeroLinear A B a z).symm κ)) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := moduleRingStalkCotangentSpace A B a z
  refine Eq.trans (congrArg (fun ζ => stalkLegNegOneLinear B C b z
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
          (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom ζ))
    (stalkBaseChangeAddEquivZero_symm_tmul A B C a b z t κ)) ?_
  refine Eq.trans (stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_inv_tmul A B C a b z
    ((fiberStalkRingEquiv C z).symm t) ((stalkLegZeroLinear A B a z).symm κ)) ?_
  exact congrArg (fun r : ToType (TopCat.Presheaf.stalk C.obj z) => r •
      naiveCotangentStalkCotangentEquiv B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
            (towerHomotopyWithTransport A B C a b)).hom
          ((stalkLegZeroLinear A B a z).symm κ)))
    ((fiberStalkRingEquiv C z).apply_symm_apply t)

/-- **The stalk of the homotopy component of the canonical map of Stacks 0E1Y on a pure tensor
with a basis element is `NaiveCotangent.towerNullHomotopyBaseChange` there.**  The value of the
stalk of the explicit homotopy on a basis element of `Ω_{A_z[B_z]/A_z} ⊗ B_z` is
`NaiveCotangent.towerNullHomotopy` of that basis element, which is
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_cotangentSpaceBasis`,
and the scalar is `NaiveCotangent.towerNullHomotopyBaseChange_tmul`. -/
theorem stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_symm_tmul_cotangentSpaceBasis
    (t : ToType (TopCat.Presheaf.stalk C.obj z))
    (s : ToType (TopCat.Presheaf.stalk B.obj z)) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := algebraStalk (a ≫ b).hom z
    haveI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegNegOneLinear B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
            (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom
          ((stalkBaseChangeAddEquivZero A B C a b z).symm
            (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)]
              (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
                (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis s))) =
      NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
        (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)]
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
            (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis s) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := algebraStalk (a ≫ b).hom z
  have _ := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
  let := moduleRingStalkCotangentSpace A B a z
  refine Eq.trans (stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_symm_tmul
    A B C a b z t _) ?_
  refine Eq.trans (congrArg (fun y => t • y)
    (Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv B C b z)
        (stalkFunctor_map_towerHomotopyWithTransport A B C a b z _))
      (naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_cotangentSpaceBasis
        B C b z A a s))) ?_
  exact (NaiveCotangent.towerNullHomotopyBaseChange_tmul
    (ToType (TopCat.Presheaf.stalk A.obj z)) (ToType (TopCat.Presheaf.stalk B.obj z))
    (ToType (TopCat.Presheaf.stalk C.obj z)) t _).symm

/-- **The stalk of the homotopy component of the canonical map of Stacks 0E1Y is the base change
of the null homotopy of Stacks 07VC.**  Read through the identification
`stalkBaseChangeAddEquivZero` of the stalk of `(NL_{B/A} ⊗_B C)^0` with
`C_z ⊗_{B_z} (Ω_{A_z[B_z]/A_z} ⊗ B_z)` and the degree `-1` leg of Stacks 0D09 on the target, the
stalk at `z` of the single component of `Stacks.SheafOfModules.baseChangeRelativeNullHomotopy`
*is* `NaiveCotangent.towerNullHomotopyBaseChange` for the tower of stalk rings.

Both sides are additive, and the preceding statement computes them on every pure tensor whose
right-hand factor is a basis element, so `tmul_basis_ext` finishes. -/
theorem stalkLegNegOneLinear_baseChangeRelativeNullHomotopy
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := algebraStalk (a ≫ b).hom z
    haveI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegNegOneLinear B C b z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
            (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom ξ) =
      NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
          (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
        (stalkBaseChangeAddEquivZero A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  let := algebraStalk (a ≫ b).hom z
  have _ := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a z rfl
  let := moduleRingStalkCotangentSpace A B a z
  let := moduleRingStalkCotangent B C b z
  refine Eq.trans ?_ (tmul_basis_ext
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))).cotangentSpaceBasis
    ((stalkLegNegOneLinear B C b z).toLinearMap.toAddMonoidHom.comp
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
            (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom.toAddMonoidHom.comp
        (stalkBaseChangeAddEquivZero A B C a b z).symm.toAddMonoidHom))
    (NaiveCotangent.towerNullHomotopyBaseChange (ToType (TopCat.Presheaf.stalk A.obj z))
      (ToType (TopCat.Presheaf.stalk B.obj z))
      (ToType (TopCat.Presheaf.stalk C.obj z))).toAddMonoidHom
    (fun t i => stalkLegNegOneLinear_baseChangeRelativeNullHomotopy_symm_tmul_cotangentSpaceBasis
      A B C a b z t i)
    (stalkBaseChangeAddEquivZero A B C a b z ξ))
  exact congrArg (fun ζ => stalkLegNegOneLinear B C b z
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((Stacks.SheafOfModules.baseChangeRelativeNullHomotopy.{u, u, u}
          (Opens.grothendieckTopology T) A B C a b).hom 0 (-1))).hom ζ))
    ((stalkBaseChangeAddEquivZero A B C a b z).symm_apply_apply ξ).symm

end Stacks.NaiveCotangentStalkBaseChange

end

end
