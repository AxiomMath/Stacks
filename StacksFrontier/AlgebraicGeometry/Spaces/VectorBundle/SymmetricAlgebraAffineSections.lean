module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherent

/-!
# Sections of the symmetric algebra of a locally free module over a trivializing chart

Let `W` be an algebraic space, `ℰ` an `𝒪_W`-module on its small étale site and `V` an étale
chart of `W` over which `ℰ` is free on a finite type `ι`. The symmetric algebra `Sym(ℰ)` is the
degreewise sheafification of `U ↦ Symⁿ_{𝒪(U)}(ℰ(U))` followed by the ungraded realization, so a
priori its sections over `V` are not computable. This file computes them when the chart is
affine: they are the symmetric algebra of the sections of `ℰ`, hence the polynomial ring
`𝒪(V)[T_i, i ∈ ι]`,

`Γ(V, Sym(ℰ)) ≅ Sym_{𝒪(V)}(Γ(V, ℰ)) ≅ 𝒪(V)[T_i]`,

compatibly with the structure maps. This is the local model of the vector bundle
`\underline{Spec}(Sym(ℰ))` over a trivializing affine chart.

## Main definitions

* `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom`: the comparison
  `Sym_{𝒪(V)}(Γ(V, ℰ)) ⟶ Γ(V, Sym(ℰ))` over an arbitrary chart, the degreewise sheafification
  units followed by the sheafification unit of the ungraded realization.
* `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingEquiv`: the identification
  `Sym_{𝒪(V)}(Γ(V, ℰ)) ≅ Γ(V, Sym(ℰ))`.
* `AlgebraicGeometry.Space.SymAlgSections.polynomialSectionsRingEquiv`: the identification
  `𝒪(V)[T_i, i ∈ ι] ≅ Γ(V, Sym(ℰ))`.

## Main results

* `AlgebraicGeometry.Space.bijective_sheafifyUnit_symPowInt_app`: over a chart on which `ℰ` is
  free of finite rank, the sheafification unit of the sectionwise symmetric power is bijective on
  the sections over that chart.
* `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingEquiv_algebraMap` and
  `AlgebraicGeometry.Space.SymAlgSections.polynomialSectionsRingEquiv_C`: the identifications
  carry the structure map of the symmetric algebra, respectively the constants, to the structure
  map of the algebra sheaf `Sym(ℰ)`.

## Implementation notes

The degreewise statement is proved on the slice over the chart. There the sectionwise symmetric
power of `ℰ` is, by the trivialization and `Stacks.SheafOfModules.symPowFreeIso`, the free sheaf
of modules on the degree-`n` monomials, which is already a sheaf; sheafification commutes with
restriction to a slice (`Stacks.SheafOfModules.SliceSheafification.restrictedUnit`), so the unit
over the chart is bijective by `Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff`. The
passage over all degrees is `AlgebraicGeometry.Space.bijective_totalUnit_of_isAffine`: an affine
chart is a quasi-compact object of the small étale site, over which the sections of a coproduct
are the direct sum of the sections. Multiplicativity is
`Stacks.GradedAlgebra.sheafify_mul_unit`; the assembly follows `Stacks.SymAlgSections`, which
carries out the same computation for a quasi-coherent module over an affine open of a scheme.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W)) (V : SmallEtale B S hS W.1)

/-- The sectionwise symmetric power of `ℰ`, restricted to the slice over a chart `V` on which
`ℰ` is free on a finite type `ι`, is the free module on the degree-`n` multidegrees. -/
def symPowOverFreeIso {ι : Type u} [DecidableEq ι] [Finite ι] (n : ℕ)
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) :
    (PresheafOfModules.sliceRestrict.{u, u + 1, u} V).obj
        (PresheafOfModules.symPow.{u, u + 1, u, u} n F.val) ≅
      (SheafOfModules.free (R := (structureRingSheaf B S hS W).over V)
        {d : ι →₀ ℕ | d.degree = n}).val :=
  PresheafOfModules.symPowOverIso.{u, u + 1, u} V n F.val ≪≫
    { hom := PresheafOfModules.symPowMap.{u, u + 1, u, u} n e.hom.val
      inv := PresheafOfModules.symPowMap.{u, u + 1, u, u} n e.inv.val
      hom_inv_id := (PresheafOfModules.symPowMap_comp n _ _).symm.trans
        ((congrArg (PresheafOfModules.symPowMap n) (congrArg SheafOfModules.Hom.val
          e.hom_inv_id)).trans (PresheafOfModules.symPowMap_id n _))
      inv_hom_id := (PresheafOfModules.symPowMap_comp n _ _).symm.trans
        ((congrArg (PresheafOfModules.symPowMap n) (congrArg SheafOfModules.Hom.val
          e.inv_hom_id)).trans (PresheafOfModules.symPowMap_id n _)) } ≪≫
    Stacks.SheafOfModules.symPowFreeIso
      (J := (SmallEtale.topology B S hS W.1).over V)
      (O := (Over.forget V).op ⋙ (structureSheaf B S hS W.1 W.2).obj)
      ((structureRingSheaf B S hS W).over V).property n

/-- The object of the slice over `V` given by `V` itself. -/
abbrev sliceTop : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))

/-- **Over a chart on which `ℰ` is free of finite rank, the sheafification unit of the
sectionwise symmetric power `U ↦ Symⁿ_{𝒪(U)}(ℰ(U))` is bijective on the sections over that
chart.** On the slice over the chart the sectionwise symmetric power is already a sheaf, the
free module on the degree-`n` monomials, and sheafification commutes with restriction to the
slice. -/
theorem bijective_sheafifyUnit_symPowInt_app {ι : Type u} [Finite ι] (n : ℕ)
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) :
    Function.Bijective (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
        (PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)) (op V)) := by
  classical
  let R := structureRingSheaf B S hS W
  let P := PresheafOfModules.symPowInt.{u, u + 1, u, u} (n : ℤ) F.val
  let e' := symPowOverFreeIso B S hS W F V n e
  have h1 : Function.Bijective (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (R.over V).obj)
        ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor.{u} R V).obj P))
      (sliceTop B S hS W V)) := by
    have hbij : ∀ X, Function.Bijective
        (((PresheafOfModules.toPresheaf (R.over V).obj).map e'.hom).app X) := fun X =>
      ConcreteCategory.bijective_of_isIso
        (((PresheafOfModules.toPresheaf (R.over V).obj).mapIso e').app X).hom
    refine (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 (R.over V).obj)
      (SheafOfModules.free (R := R.over V) {d : ι →₀ ℕ | d.degree = n}) e'.hom
      (Presheaf.isLocallyInjective_of_injective _ _ fun X => (hbij X).1)
      (Presheaf.isLocallySurjective_of_surjective _ _ fun X => (hbij X).2)
      (sliceTop B S hS W V)).2 ?_
    exact ConcreteCategory.bijective_of_isIso
      ((PresheafOfModules.evaluation _ (sliceTop B S hS W V)).mapIso e').hom
  have h2 := (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 (R.over V).obj)
    (((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj P).over V)
    (Stacks.SheafOfModules.SliceSheafification.restrictedUnit.{u} R V P)
    (Stacks.SheafOfModules.SliceSheafification.isLocallyInjective_overToSheafify.{u} R V P)
    (Stacks.SheafOfModules.SliceSheafification.isLocallySurjective_overToSheafify.{u} R V P)
    (sliceTop B S hS W V)).1 h1
  exact h2

/-! ### The ring of sections of `Sym(ℰ)` over a trivializing affine chart -/

/-- The ring of sections of the structure sheaf over a chart, in the spelling the sectionwise
symmetric powers are formed over. -/
abbrev vectorBundleChartRing : RingCat.{u} :=
  ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V)

/-- The sections of `ℰ` over a chart, as a module over
`AlgebraicGeometry.Space.vectorBundleChartRing`. -/
instance vectorBundleChartSectionsModule :
    Module (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) :=
  (F.val.obj (op V)).isModule

namespace SymAlgSections

open PresheafOfModules
open scoped DirectSum

/-- The homogeneous pieces of `Sym(ℰ)`, as a `ℤ`-indexed family of presheaves of modules. -/
abbrev symPiece (n : ℤ) : PresheafOfModules.{u} (structureRingSheaf B S hS W).obj :=
  ((symmetricAlgebra B S hS W F).piece n).val

/-- `Sym(ℰ)` read as a graded algebra of presheaves of modules. -/
abbrev symPresheafAlgebra : Stacks.GradedAlgebra (symPiece B S hS W F) :=
  (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra

/-- The degree-`n` sheafification unit `Symⁿ_{𝒪(V)}(ℰ(V)) ⟶ Γ(V, Symⁿ(ℰ))` over an arbitrary
chart. -/
def pieceUnitHom (n : ℕ) :
    SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) →+
      ((symPiece B S hS W F (n : ℤ)).obj (op V)) :=
  ((sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
    (symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)).app (op V)).hom.toAddMonoidHom

/-- `pieceUnitHom` evaluates as the component at `V` of the degree-`n` sheafification unit. -/
theorem pieceUnitHom_apply (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    pieceUnitHom B S hS W F V n x =
      Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
        (symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)) (op V) x := rfl

/-- The degreewise sheafification unit followed by the inclusion of the degree-`n` summand of the
direct sum of the sections. -/
def symPowerIncl (n : ℕ) :
    SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) →+
      (symPresheafAlgebra B S hS W F).Total (op V) :=
  (DirectSum.of (fun m : ℤ => ((symPiece B S hS W F m).obj (op V) : Type u)) (n : ℤ)).comp
    (pieceUnitHom B S hS W F V n)

/-- `symPowerIncl` sends `x` to the degree-`n` summand containing `pieceUnitHom x`. -/
theorem symPowerIncl_apply (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    symPowerIncl B S hS W F V n x =
      DirectSum.of (fun m : ℤ => ((symPiece B S hS W F m).obj (op V) : Type u)) (n : ℤ)
        (pieceUnitHom B S hS W F V n x) := rfl

/-- The degree-zero summand carries the unit to the unit. -/
theorem symPowerIncl_one
    (x : SymPow.symmetricPower 0 (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
    (hx : (x : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) = 1) :
    symPowerIncl B S hS W F V 0 x = 1 :=
  (congrArg (DirectSum.of (fun m : ℤ => ((symPiece B S hS W F m).obj (op V) : Type u)) 0)
      ((congrArg (Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
            (symPowInt.{u, u + 1, u, u} (0 : ℤ) F.val)) (op V))
          (Subtype.ext hx :
            x = (symPowIntGradedAlgebra.{u, u + 1, u, u} F.val).one.eval (op V))).trans
        ((symPowIntGradedAlgebra.{u, u + 1, u, u} F.val).sheafify_one_eval
          (𝟙 (structureRingSheaf B S hS W).obj) (op V)).symm)).trans
    ((symPresheafAlgebra B S hS W F).one_eq_incl (op V)).symm

/-- The summands multiply as the symmetric powers do. -/
theorem symPowerIncl_mul (i j : ℕ)
    (a : SymPow.symmetricPower i (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
    (b : SymPow.symmetricPower j (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
    (c : SymPow.symmetricPower (i + j) (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
    (hc : (c : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) =
      (a : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) *
        (b : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))) :
    symPowerIncl B S hS W F V (i + j) c =
      symPowerIncl B S hS W F V i a * symPowerIncl B S hS W F V j b :=
  Eq.symm
    (((symPresheafAlgebra B S hS W F).incl_mul_incl (i : ℤ) (j : ℤ) _ _).trans
      (congrArg (DirectSum.of (fun m : ℤ => ((symPiece B S hS W F m).obj (op V) : Type u)) _)
        (((symPowIntGradedAlgebra.{u, u + 1, u, u} F.val).sheafify_mul_unit
            (𝟙 (structureRingSheaf B S hS W).obj) (i : ℤ) (j : ℤ) (op V) a b).trans
          (congrArg (Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
              (symPowInt.{u, u + 1, u, u} ((i : ℤ) + (j : ℤ)) F.val)) (op V))
            (Subtype.ext hc.symm)))))

/-- The degreewise sheafification unit as a ring homomorphism. -/
def ofSymPowers :
    (⨁ n : ℕ, SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) →+*
      (symPresheafAlgebra B S hS W F).Total (op V) :=
  DirectSum.toSemiring (symPowerIncl B S hS W F V) (symPowerIncl_one B S hS W F V _ rfl)
    (fun {_ _} ai aj => symPowerIncl_mul B S hS W F V _ _ ai aj _ rfl)

/-- `ofSymPowers` sends the degree-`n` summand `x` to `symPowerIncl n x`. -/
theorem ofSymPowers_of (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    ofSymPowers B S hS W F V (DirectSum.of _ n x) = symPowerIncl B S hS W F V n x :=
  DirectSum.toSemiring_of (symPowerIncl B S hS W F V) _ _ n x

/-- **The comparison `Sym_{𝒪(V)}(ℰ(V)) ⟶ Γ(V, Sym(ℰ))` over an arbitrary chart**: the
degreewise sheafification units followed by the sheafification unit of the ungraded
realization. It is bijective over an affine chart trivializing `ℰ`
(`AlgebraicGeometry.Space.SymAlgSections.symSectionsRingEquiv`). -/
def symSectionsRingHom :
    SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) →+*
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :=
  ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalUnit
      (SmallEtale.topology B S hS W.1) (op V)).comp
    ((ofSymPowers B S hS W F V).comp
      (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n (vectorBundleChartRing B S hS W V)
          (F.val.obj (op V)))).toRingHom)

/-- `symSectionsRingHom` is the decomposition into symmetric powers, followed by `ofSymPowers` and
the sheafification unit of the ungraded realization. -/
theorem symSectionsRingHom_apply
    (a : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    symSectionsRingHom B S hS W F V a =
      (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalUnit
        (SmallEtale.topology B S hS W.1) (op V)
        (ofSymPowers B S hS W F V (DirectSum.decompose
          (fun n : ℕ =>
            SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
          a)) :=
  rfl

private theorem decompose_coe (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    DirectSum.decompose
        (fun n : ℕ => SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
        (x : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) =
      DirectSum.of (fun m : ℕ =>
          (SymPow.symmetricPower m (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) : Type u))
        n x :=
  DirectSum.decompose_of_mem
    (fun n : ℕ => SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) x.2

/-- The comparison is determined by the image of the decomposition under `ofSymPowers`. -/
private theorem symSectionsRingHom_eq_of_ofSymPowers
    (a : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
    (y : (symPresheafAlgebra B S hS W F).Total (op V))
    (h : ofSymPowers B S hS W F V (DirectSum.decompose
      (fun n : ℕ => SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
      a) = y) :
    symSectionsRingHom B S hS W F V a =
      (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalUnit
        (SmallEtale.topology B S hS W.1) (op V) y :=
  congrArg _ h

/-- **The comparison on a homogeneous element** of degree `n` is the degree-`n` sheafification
unit followed by the inclusion of the degree-`n` piece into the ungraded realization. -/
theorem symSectionsRingHom_of_mem (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    symSectionsRingHom B S hS W F V x =
      (symmetricAlgebra B S hS W F).ungradedIncl (n : ℤ) (pieceUnitHom B S hS W F V n x) := by
  exact symSectionsRingHom_eq_of_ofSymPowers B S hS W F V x (symPowerIncl B S hS W F V n x)
    ((congrArg (ofSymPowers B S hS W F V) (decompose_coe B S hS W F V n x)).trans
      (ofSymPowers_of B S hS W F V n x))

variable {ι : Type u} [Finite ι]
  (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)

/-- `Symⁿ` of the sections of `ℰ` over a trivializing chart is the sections of `Symⁿ(ℰ)` there:
the degree-`n` sheafification unit, which is bijective by
`AlgebraicGeometry.Space.bijective_sheafifyUnit_symPowInt_app`. -/
def pieceUnit (n : ℕ) :
    SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) ≃+
      ((symPiece B S hS W F (n : ℤ)).obj (op V)) :=
  AddEquiv.ofBijective (pieceUnitHom B S hS W F V n)
    (bijective_sheafifyUnit_symPowInt_app B S hS W F V n e)

/-- `pieceUnit` evaluates as the component at `V` of the degree-`n` sheafification unit. -/
theorem pieceUnit_apply (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    pieceUnit B S hS W F V e n x =
      Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
        (symPowInt.{u, u + 1, u, u} (n : ℤ) F.val)) (op V) x := rfl

/-- The degreewise sheafification unit, assembled over the nonnegative degrees. -/
def natSumUnit :
    (⨁ n : ℕ, SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) →+
      Stacks.DirectSumType (fun n : ℕ => symPiece B S hS W F (n : ℤ)) (op V) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℕ => ((symPiece B S hS W F (m : ℤ)).obj (op V) : Type u)) n).comp
      (pieceUnit B S hS W F V e n).toAddMonoidHom

/-- `natSumUnit` sends the degree-`n` summand `x` to the degree-`n` summand `pieceUnit n x`. -/
theorem natSumUnit_of (n : ℕ)
    (x : SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    natSumUnit B S hS W F V e (DirectSum.of _ n x) =
      DirectSum.of (fun m : ℕ => ((symPiece B S hS W F (m : ℤ)).obj (op V) : Type u)) n
        (pieceUnit B S hS W F V e n x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The inverse of `AlgebraicGeometry.Space.SymAlgSections.natSumUnit`, degree by degree. -/
def natSumUnitInv : Stacks.DirectSumType (fun n : ℕ => symPiece B S hS W F (n : ℤ)) (op V) →+
    (⨁ n : ℕ, SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℕ =>
        (SymPow.symmetricPower m (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) : Type u))
          n).comp
      (pieceUnit B S hS W F V e n).symm.toAddMonoidHom

/-- `natSumUnitInv` sends the degree-`n` summand `y` to the degree-`n` summand
`(pieceUnit n).symm y`. -/
theorem natSumUnitInv_of (n : ℕ) (y : (symPiece B S hS W F (n : ℤ)).obj (op V)) :
    natSumUnitInv B S hS W F V e (DirectSum.of _ n y) =
      DirectSum.of (fun m : ℕ =>
          (SymPow.symmetricPower m (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) : Type u))
          n ((pieceUnit B S hS W F V e n).symm y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- A map out of a direct sum that is a left inverse on each summand is a left inverse. -/
private theorem leftInverse_of_directSum_of {κ : Type*} {M N : κ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [DecidableEq κ]
    (f : (⨁ i, M i) →+ ⨁ i, N i) (g : (⨁ i, N i) →+ ⨁ i, M i)
    (h : ∀ i x, g (f (DirectSum.of M i x)) = DirectSum.of M i x) : Function.LeftInverse g f :=
  DFunLike.congr_fun (DirectSum.addHom_ext (f := g.comp f) (g := AddMonoidHom.id _) h)

/-- Over a trivializing chart, `natSumUnit` is bijective. -/
theorem bijective_natSumUnit : Function.Bijective (natSumUnit B S hS W F V e) :=
  Function.bijective_iff_has_inverse.2 ⟨natSumUnitInv B S hS W F V e,
    leftInverse_of_directSum_of _ _ fun n x =>
      (congrArg (natSumUnitInv B S hS W F V e) (natSumUnit_of B S hS W F V e n x)).trans
        ((natSumUnitInv_of B S hS W F V e n _).trans
          (congrArg (DirectSum.of _ n) ((pieceUnit B S hS W F V e n).symm_apply_apply x))),
    leftInverse_of_directSum_of _ _ fun n y =>
      (congrArg (natSumUnit B S hS W F V e) (natSumUnitInv_of B S hS W F V e n y)).trans
        ((natSumUnit_of B S hS W F V e n _).trans
          (congrArg (DirectSum.of _ n) ((pieceUnit B S hS W F V e n).apply_symm_apply y)))⟩

/-- Over a trivializing chart, `ofSymPowers` is `natSumUnit` followed by the extension of
`ℕ`-indexed direct sums to `ℤ`-indexed ones. -/
theorem ofSymPowers_apply_eq
    (z : ⨁ n : ℕ, SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    ofSymPowers B S hS W F V z =
      Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V) (natSumUnit B S hS W F V e z) := by
  induction z using DirectSum.induction_on with
  | zero =>
      exact (map_zero (ofSymPowers B S hS W F V)).trans
        (((congrArg (Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V))
            (map_zero (natSumUnit B S hS W F V e))).trans
          (map_zero (Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V)))).symm)
  | of n x =>
      exact ((ofSymPowers_of B S hS W F V n x).trans (symPowerIncl_apply B S hS W F V n x)).trans
        ((Stacks.directSumNatToIntApp_of (symPiece B S hS W F) (op V) n
            (pieceUnit B S hS W F V e n x)).symm.trans
          (congrArg (Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V))
            (natSumUnit_of B S hS W F V e n x).symm))
  | add z z' hz hz' =>
      exact (map_add (ofSymPowers B S hS W F V) z z').trans
        ((congrArg₂ (· + ·) hz hz').trans
          (((congrArg (Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V))
              (map_add (natSumUnit B S hS W F V e) z z')).trans
            (map_add (Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V)) _ _)).symm))

include e in
/-- Over a chart on which `ℰ` is free of finite rank, `ofSymPowers` is bijective. -/
theorem bijective_ofSymPowers : Function.Bijective (ofSymPowers B S hS W F V) := by
  have hzero : ∀ n : ℤ, n < 0 → Subsingleton ((symPiece B S hS W F n).obj (op V)) :=
    fun n hn => Stacks.subsingleton_of_isZero (isZero_symmetricAlgebra_piece_of_neg B S hS W F n hn)
      (op V)
  have hcomp : Function.Bijective fun z =>
      Stacks.directSumNatToIntApp (symPiece B S hS W F) (op V) (natSumUnit B S hS W F V e z) :=
    (Stacks.bijective_directSumNatToIntApp (symPiece B S hS W F) (op V) hzero).comp
      (bijective_natSumUnit B S hS W F V e)
  exact (congrArg Function.Bijective
    (funext (ofSymPowers_apply_eq B S hS W F V e))).mpr hcomp

/-- The direct sum of the symmetric powers of the sections, as a ring, is the direct sum of the
sections of the homogeneous pieces of `Sym(ℰ)`. -/
def symPowersRingEquiv :
    (⨁ n : ℕ, SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) ≃+*
      (symPresheafAlgebra B S hS W F).Total (op V) :=
  RingEquiv.ofBijective (ofSymPowers B S hS W F V) (bijective_ofSymPowers B S hS W F V e)

variable (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))

/-- **The sections of `Sym(ℰ)` over an affine chart on which `ℰ` is free of finite rank are the
symmetric algebra of the sections of `ℰ`.** -/
def symSectionsRingEquiv :
    SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) ≃+*
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :=
  (DirectSum.decomposeRingEquiv
      (fun n : ℕ =>
        SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))).trans
    ((symPowersRingEquiv B S hS W F V e).trans
      (RingEquiv.ofBijective
        ((symmetricAlgebra B S hS W F).toPresheafGradedAlgebra.totalUnit
          (SmallEtale.topology B S hS W.1) (op V))
        (bijective_totalUnit_of_isAffine B S hS W (symmetricAlgebra B S hS W F) V hV)))

omit [Finite ι] in
/-- The image of `r` in the degree-zero symmetric power of the sections of `ℰ`. -/
def symOne (r : vectorBundleChartRing B S hS W V) :
    SymPow.symmetricPower 0 (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) :=
  ⟨algebraMap (vectorBundleChartRing B S hS W V)
      (SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r SetLike.GradedOne.one_mem⟩

omit [Finite ι] in
private theorem decompose_algebraMap (r : vectorBundleChartRing B S hS W V) :
    DirectSum.decompose
        (fun n : ℕ => SymPow.symmetricPower n (vectorBundleChartRing B S hS W V) (F.val.obj (op V)))
        (algebraMap (vectorBundleChartRing B S hS W V)
          (SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r) =
      DirectSum.of (fun m : ℕ =>
          (SymPow.symmetricPower m (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) : Type u))
          0 (symOne B S hS W F V r) :=
  decompose_coe B S hS W F V 0 (symOne B S hS W F V r)

private theorem structureMap_eq (r : (structureRingSheaf B S hS W).obj.obj (op V)) :
    (symPresheafAlgebra B S hS W F).structureMap (op V) r =
      ofSymPowers B S hS W F V (DirectSum.of (fun m : ℕ =>
          (SymPow.symmetricPower m (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) : Type u))
          0 (symOne B S hS W F V r)) := by
  have hone := (symPowIntGradedAlgebra.{u, u + 1, u, u} F.val).sheafify_one_eval
    (𝟙 (structureRingSheaf B S hS W).obj) (op V)
  have hlin := ((sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
    (symPowInt.{u, u + 1, u, u} (0 : ℤ) F.val)).app (op V)).hom.map_smul r
      ((symPowIntGradedAlgebra.{u, u + 1, u, u} F.val).one.eval (op V))
  have h3 : r • (symmetricAlgebra B S hS W F).one.eval (op V) =
      Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
        (symPowInt.{u, u + 1, u, u} (0 : ℤ) F.val)) (op V) (symOne B S hS W F V r) :=
    ((congrArg (fun y => r • y) hone).trans hlin.symm).trans
      (congrArg (Hom.app (sheafifyUnit (𝟙 (structureRingSheaf B S hS W).obj)
          (symPowInt.{u, u + 1, u, u} (0 : ℤ) F.val)) (op V))
        (Subtype.ext
          (Algebra.algebraMap_eq_smul_one (R := vectorBundleChartRing B S hS W V)
            (A := SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r).symm))
  exact Eq.trans
    (((symPresheafAlgebra B S hS W F).incl_smul (0 : ℤ) r
          ((symmetricAlgebra B S hS W F).one.eval (op V))).symm.trans
      (congrArg (DirectSum.of (fun m : ℤ => ((symPiece B S hS W F m).obj (op V) : Type u)) 0)
        h3))
    ((ofSymPowers_of B S hS W F V 0 (symOne B S hS W F V r)).trans
      (symPowerIncl_apply B S hS W F V 0 (symOne B S hS W F V r))).symm

/-- **The comparison carries `algebraMap` to the structure map of the algebra sheaf.** -/
theorem symSectionsRingHom_algebraMap (r : vectorBundleChartRing B S hS W V) :
    symSectionsRingHom B S hS W F V (algebraMap (vectorBundleChartRing B S hS W V)
        (SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op V) r := by
  exact symSectionsRingHom_eq_of_ofSymPowers B S hS W F V _
    ((symPresheafAlgebra B S hS W F).structureMap (op V) r)
    ((congrArg (ofSymPowers B S hS W F V) (decompose_algebraMap B S hS W F V r)).trans
      (structureMap_eq B S hS W F V r).symm)

/-- The identification is the comparison
`AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom`. -/
theorem symSectionsRingEquiv_apply
    (a : SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) :
    symSectionsRingEquiv B S hS W F V e hV a = symSectionsRingHom B S hS W F V a :=
  rfl

/-- **The identification carries `algebraMap` to the structure map of the algebra sheaf.** -/
theorem symSectionsRingEquiv_algebraMap (r : vectorBundleChartRing B S hS W V) :
    symSectionsRingEquiv B S hS W F V e hV (algebraMap (vectorBundleChartRing B S hS W V)
        (SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op V) r :=
  symSectionsRingHom_algebraMap B S hS W F V r

variable [DecidableEq ι]

/-- The coordinates of a section of `ℰ` over a chart on which `ℰ` is free on `ι`. -/
def sectionsEquivFun :
    F.val.obj (op V) ≃ₗ[vectorBundleChartRing B S hS W V] (ι → vectorBundleChartRing B S hS W V) :=
  let φ := ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _
    (sliceTop B S hS W V)).mapIso e).toLinearEquiv
  let ψ := Stacks.SheafOfModules.freeCoordLinearEquiv
    (J := (SmallEtale.topology B S hS W.1).over V)
    (O := (Over.forget V).op ⋙ (structureSheaf B S hS W.1 W.2).obj)
    ((structureRingSheaf B S hS W).over V).property (ι := ι) (sliceTop B S hS W V)
  { toFun := fun x => ψ (φ x)
    invFun := fun y => φ.symm (ψ.symm y)
    map_add' := fun x y => (congrArg ψ (φ.map_add x y)).trans (ψ.map_add _ _)
    map_smul' := fun r x => (congrArg ψ (φ.map_smul r x)).trans (ψ.map_smul r (φ x))
    left_inv := fun x => (congrArg φ.symm (ψ.symm_apply_apply (φ x))).trans
      (φ.symm_apply_apply x)
    right_inv := fun y => (congrArg ψ (φ.apply_symm_apply (ψ.symm y))).trans
      (ψ.apply_symm_apply y) }

/-- The basis of the sections of `ℰ` over a chart on which `ℰ` is free on `ι`. -/
def sectionsBasis : Module.Basis ι (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) :=
  Module.Basis.ofEquivFun (sectionsEquivFun B S hS W F V e)

/-- **The local model of `Sym(ℰ)`.** Over an affine chart `V` on which `ℰ` is free on a finite
type `ι`, the ring of sections of `Sym(ℰ)` is the polynomial ring over `𝒪(V)` in the variables
`ι`. -/
def polynomialSectionsRingEquiv :
    MvPolynomial ι (vectorBundleChartRing B S hS W V) ≃+*
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :=
  (SymmetricAlgebra.equivMvPolynomial (sectionsBasis B S hS W F V e)).symm.toRingEquiv.trans
    (symSectionsRingEquiv B S hS W F V e hV)

/-- **The local model carries the constants to the structure map of `Sym(ℰ)`.** -/
theorem polynomialSectionsRingEquiv_C (r : vectorBundleChartRing B S hS W V) :
    polynomialSectionsRingEquiv B S hS W F V e hV (MvPolynomial.C r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op V) r := by
  have h : (SymmetricAlgebra.equivMvPolynomial (sectionsBasis B S hS W F V e)).symm
      (MvPolynomial.C r) = algebraMap (vectorBundleChartRing B S hS W V)
        (SymmetricAlgebra (vectorBundleChartRing B S hS W V) (F.val.obj (op V))) r :=
    ((SymmetricAlgebra.equivMvPolynomial (sectionsBasis B S hS W F V e)).symm.commutes r)
  exact (congrArg (symSectionsRingEquiv B S hS W F V e hV) h).trans
    (symSectionsRingEquiv_algebraMap B S hS W F V e hV r)

end SymAlgSections

end AlgebraicGeometry.Space

end
