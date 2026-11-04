module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartLocalComparison
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartLocalSourceIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartMorphismMatch
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyScalarAction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAEWiring
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsTranspose
public import StacksFrontier.RingTheory.TensorProduct.LocalizedPushoutRearrangement

/-!
# The final assembly of Stacks 0DJ8

`AlgebraicGeometry.baseChange_tfae_of_sourceBridge` reduces the three-way equivalence of
Stacks 0DJ8 to one statement about one chart at one point: a bijection `θ` between the source of
the germ-localized chart map of condition (2) and the source of the pointwise map of Stacks 0DJ7
at the corresponding point of `X'`, commuting with the two maps through the identification of
their targets. This module supplies that bijection and the commutation, and states the
equivalence.

## Main definitions

* `ModuleCat.extendScalarsTargetEquiv`: extension of scalars along a ring isomorphism of the
  target ring, `C ⊗_B M ≅ D ⊗_B M`.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceMap`: the source identification of the cube
  at a chart, on the generators `1 ⊗ m` of the source.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceTranspose`: the source identification
  itself, as a map of modules over `𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`.
* `AlgebraicGeometry.BaseChangeChart.sourceBridgeMap`: the bijection the source bridge of
  Stacks 0DJ8 asks for, between the source of the germ-localized chart map of condition (2) and
  the source of the pointwise map of Stacks 0DJ7.

## Main results

* `ModuleCat.inv_comm_of_hom_comm`: an equivariance of an isomorphism transports to its inverse.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceMap_add`,
  `localRingsSourceMap_includeLeft_smul` and `localRingsSourceMap_includeRight_smul`: the source
  identification on generators is additive and equivariant for both tensor factors of
  `𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`, hence linear over it.
* `AlgebraicGeometry.BaseChangeChart.localRingsSourceTranspose_one_tmul`: the transpose recovers
  the source identification on the generators of its source.
* `AlgebraicGeometry.BaseChangeChart.chartPushoutRingMap_eq`: the chart's pushout ring reaches
  the local ring of `X'` at `x'` by the same map through `𝒪_{X'}(U')` as through the pushout of
  the local rings.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct ChangeOfRings

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace ModuleCat

/-- **Extension of scalars along a ring isomorphism of the target ring.** For `p : B →+* C` and
`e : C →+* D` with a two-sided inverse `e'`, the `B`-modules `C ⊗_B M` and `D ⊗_B M` have the
same underlying group, `e` on the left factor.

This is `Stacks.TensorProductPushout.baseCongr` read at the carriers of
`ModuleCat.extendScalars`, which is where the affine reduction of Stacks 0DJ8 needs it: the
germ comparison identifies the local ring of `Spec 𝒪_{X'}(U')` at `y` with the local ring of
`X'` at the image of `y`, and the two sources being compared are extensions of scalars of one
module along the two. -/
public def extendScalarsTargetEquiv {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (p : B →+* C) (e : C →+* D) (e' : D →+* C)
    (he : ∀ c, e' (e c) = c) (he' : ∀ d, e (e' d) = d) (M : ModuleCat.{u} B) :
    ((extendScalars.{u, u, u} p).obj M) ≃+ ((extendScalars.{u, u, u} (e.comp p)).obj M) :=
  letI : Algebra B C := p.toAlgebra
  letI : Algebra B D := (e.comp p).toAlgebra
  (Stacks.TensorProductPushout.baseCongr (A := B) (M := M) e e' he he'
    fun _ => rfl).toAddEquiv

/-- `ModuleCat.extendScalarsTargetEquiv` on pure tensors. -/
public theorem extendScalarsTargetEquiv_tmul {B C D : Type u} [CommRing B] [CommRing C]
    [CommRing D] (p : B →+* C) (e : C →+* D) (e' : D →+* C)
    (he : ∀ c, e' (e c) = c) (he' : ∀ d, e (e' d) = d) (M : ModuleCat.{u} B) (c : C) (m : M) :
    extendScalarsTargetEquiv p e e' he he' M (c ⊗ₜ[B, p] m) = (e c) ⊗ₜ[B, e.comp p] m :=
  let : Algebra B C := p.toAlgebra
  let : Algebra B D := (e.comp p).toAlgebra
  Stacks.TensorProductPushout.baseCongr_tmul (A := B) (M := M) e e' he he'
    (fun _ => rfl) c m

/-- An isomorphism of modules undoes itself, on elements. -/
public theorem iso_inv_hom_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (x : M) : e.inv.hom (e.hom.hom x) = x :=
  DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.hom_inv_id) x

/-- An isomorphism of modules is undone by its inverse, on elements. -/
public theorem iso_hom_inv_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (z : N) : e.hom.hom (e.inv.hom z) = z :=
  DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp e.inv_hom_id) z

/-- **A pure tensor of an extension of scalars is a scalar times the unit.** -/
public theorem extendScalars_tmul_eq_smul_one_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) (s : S) (m : M) :
    (show (extendScalars.{u, u, u} f).obj M from (s ⊗ₜ[R, f] m)) =
      s • (show (extendScalars.{u, u, u} f).obj M from ((1 : S) ⊗ₜ[R, f] m)) :=
  (congrArg (fun t : S => (show (extendScalars.{u, u, u} f).obj M from (t ⊗ₜ[R, f] m)))
    (mul_one s)).symm.trans (ExtendScalars.smul_tmul f s 1 m).symm

/-- **Extension of scalars along equal ring maps, on pure tensors.** The transport of the
identification of the two extensions is the identity on pure tensors. -/
public theorem eqToHom_extendScalars_tmul {B D : Type u} [CommRing B] [CommRing D]
    {p₁ p₂ : B →+* D} (h : p₁ = p₂) (M : ModuleCat.{u} B) (d : D) (m : M) :
    (eqToHom (congrArg (fun p : B →+* D => (extendScalars.{u, u, u} p).obj M) h)).hom
        (d ⊗ₜ[B, p₁] m) = d ⊗ₜ[B, p₂] m := by
  subst h
  rfl

/-- **An equivariance of an isomorphism transports to its inverse.** If an isomorphism `e`
carries an operation `uu` on its source to an operation `vv` on its target, then its inverse
carries `vv` back to `uu`.

The two operations are taken as bare functions. That is what the affine reduction of Stacks
0DJ8 needs: the operations there are scalar multiplications for module structures which are
not instances on the objects of the isomorphism — the base-change cohomology carries its
`A ⊗_R R'`-action through a `letI` inside its own definition — so they cannot be written as
`•` against the objects' own instances, and with the operations opaque there is nothing to
resolve. -/
public theorem inv_comm_of_hom_comm {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (uu : M → M) (vv : N → N) (h : ∀ x : M, e.hom.hom (uu x) = vv (e.hom.hom x)) (z : N) :
    e.inv.hom (vv z) = uu (e.inv.hom z) :=
  ((congrArg e.inv.hom ((congrArg vv (iso_hom_inv_apply e z)).symm.trans
      (h (e.inv.hom z)).symm)).trans (iso_inv_hom_apply e (uu (e.inv.hom z))))

end ModuleCat

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The source identification of the cube at a chart, on the generators `1 ⊗ m`.** The
composite

`H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))  ⟶
  H^n(K_{g'x'}|_{𝒪_{S,s}} ⊗ᴸ_{𝒪_{S,s}} 𝒪_{S',s'})`

of four maps: the unit of the flat extension along the germ map `𝒪_{S'}(V') → 𝒪_{S', f' x'}`,
read backwards through `AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso`; the
base-change cohomology of the unit of the derived change-of-rings adjunction along the germ map
`𝒪_X(U) → 𝒪_{Spec 𝒪_X(U), q}`; the base-change cohomology of
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso`; and the cohomology of
`AlgebraicGeometry.BaseChangeChart.localRingsSourceIso`.

Its target is the module the source of the pointwise map of Stacks 0DJ7 at `x'` is built from,
and its source the module the source of the germ-localized chart map of Stacks 0DJ8 (2) is built
from. The source identification itself is this map transposed along
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`. -/
public def localRingsSourceMap (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u) →
      (RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n : Type u) :=
  letI := ch.a.hom.toAlgebra
  letI := ch.b.hom.toAlgebra
  letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  letI := (ch.toStalkR y).toAlgebra
  letI := (ch.toStalkA y).toAlgebra
  letI := (ch.toStalkR' y).toAlgebra
  letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  haveI : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  fun m =>
    ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
        ((ch.localRingsSourceIso y w).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
      ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
        ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
            ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
              (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
              ((affineDerivedSections ch.incU).obj K))).hom
          ((ch.homologyBaseChangeLocalizedIso y K n).inv.hom
            ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ⊗ₜ[ch.R', ch.toStalkR' y] m))))

/-- **The source identification on generators is additive.** -/
public theorem localRingsSourceMap_add (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    ∀ x z : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u),
      ch.localRingsSourceMap y w K hK n (x + z) =
        ch.localRingsSourceMap y w K hK n x + ch.localRingsSourceMap y w K hK n z := by
  let := ch.a.hom.toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  -- abbreviations for the three cohomology-level factors of the source identification
  let nu2 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
      ((affineDerivedSections ch.incU).obj K))
  let nu3 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom
  let nu4 := (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
    ((ch.localRingsSourceIso y w).hom.app ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
  intro x z
  refine Eq.trans (congrArg (fun w => nu4.hom (nu3.hom (nu2.hom w)))
    (Eq.trans (congrArg (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
      (TensorProduct.tmul_add _ _ _))
      ((ch.homologyBaseChangeLocalizedIso y K n).inv.hom.map_add _ _))) ?_
  refine Eq.trans (congrArg (fun w => nu4.hom (nu3.hom w)) (nu2.hom.map_add _ _)) ?_
  refine Eq.trans (congrArg (fun w => nu4.hom w) (nu3.hom.map_add _ _)) ?_
  exact nu4.hom.map_add _ _

/-- **The source identification on generators is equivariant for the left tensor factor.** It
carries the action of `𝒪_X(U)` through `𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')` to the action of
`𝒪_{X,g'x'}` through `𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`, along the germ map at `g' x'`. -/
public theorem localRingsSourceMap_includeLeft_smul (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    ∀ (a : ch.A)
      (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u)),
      ch.localRingsSourceMap y w K hK n
          ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
            ch.A ⊗[ch.R] ch.R') • m) =
        (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from
          (Algebra.TensorProduct.includeLeft (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) (ch.toStalkA y a) :
              ToType (X.presheaf.stalk (g' (ch.incU' y)))
                ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show RingTheory.TorIndependence.baseChangeCohomology
                (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from
              ch.localRingsSourceMap y w K hK n m)) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  -- abbreviations for the three cohomology-level factors of the source identification
  let nu2 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
      ((affineDerivedSections ch.incU).obj K))
  let nu3 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom
  let nu4 := (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
    ((ch.localRingsSourceIso y w).hom.app ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
  -- `𝒪_X(U)`-equivariance of the unit into the localized base-change cohomology
  have hiotaL : ∀ (a : ch.A) (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u)),
      (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
          ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⊗ₜ[ch.R', ch.toStalkR' y]
            ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
              ch.A ⊗[ch.R] ch.R') • m)) =
        (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((affineDerivedSections ch.incU).obj K) n from
          (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
              ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((affineDerivedSections ch.incU).obj K) n from
              (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
                ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                  ⊗ₜ[ch.R', ch.toStalkR' y] m))) := by
    intro a m
    refine Eq.trans (congrArg (ch.homologyBaseChangeLocalizedIso y K n).inv.hom ?_)
      (ModuleCat.inv_comm_of_hom_comm (ch.homologyBaseChangeLocalizedIso y K n)
        (fun x => (show RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((affineDerivedSections ch.incU).obj K) n from
          (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
              ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                  ((affineDerivedSections ch.incU).obj K) n from x)))
        (fun z => ((ModuleCat.extendScalars.{u, u, u} (ch.toStalkR' y)).map
            ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
                (R' := ch.R') ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
              (a • 𝟙 ((affineDerivedSections ch.incU).obj K)))).hom z)
        (ch.homologyBaseChangeLocalizedIso_hom_includeLeft_smul y K n a)
        ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⊗ₜ[ch.R', ch.toStalkR' y] m))
    exact (congrArg (fun z => (1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ⊗ₜ[ch.R', ch.toStalkR' y] z)
      (RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral_includeLeft_smul
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n a m)).trans
      (ModuleCat.ExtendScalars.map_tmul _ _ _ _).symm
  -- the cohomology of the source identification is equivariant for `𝒪_X(U)`
  have hnu4L : ∀ (a : ch.A) (z : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) n : Type u)),
      nu4.hom ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
            ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • z) =
        (Algebra.TensorProduct.includeLeft
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) (ch.toStalkA y a) :
            ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          (show RingTheory.TorIndependence.baseChangeCohomology
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from nu4.hom z) := by
    intro a z
    refine Eq.trans (congrArg nu4.hom
      (RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul
        (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) n a z)) ?_
    refine Eq.trans (congrArg (fun ξ => nu4.hom (ModuleCat.Hom.hom ξ z))
      (congrArg ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map)
        (RingTheory.TorIndependence.mapDerivedCategory_restrictScalars_smul
          (ch.toStalkA y) a ((derivedStalkFunctor (g' (ch.incU' y))).obj K)).symm)) ?_
    exact ch.localRingsSourceIso_homology_smul y w n
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K) (ch.toStalkA y a) z
  intro a m
  refine Eq.trans (congrArg (fun z => nu4.hom (nu3.hom (nu2.hom z))) (hiotaL a m)) ?_
  refine Eq.trans (congrArg (fun z => nu4.hom (nu3.hom z)) (nu2.hom.map_smul _ _)) ?_
  refine Eq.trans (congrArg (fun z => nu4.hom z) (nu3.hom.map_smul _ _)) ?_
  exact hnu4L a _

/-- **The source identification on generators is equivariant for the right tensor factor.** It
carries the action of `𝒪_{S'}(V')` to the action of `𝒪_{S',f'x'}`, along the germ map at
`f' x'`. -/
public theorem localRingsSourceMap_includeRight_smul (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    ∀ (r : ch.R')
      (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u)),
      ch.localRingsSourceMap y w K hK n
          ((Algebra.TensorProduct.includeRight r :
            ch.A ⊗[ch.R] ch.R') • m) =
        (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from
          (Algebra.TensorProduct.includeRight (ch.toStalkR' y r) :
              ToType (X.presheaf.stalk (g' (ch.incU' y)))
                ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show RingTheory.TorIndependence.baseChangeCohomology
                (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from
              ch.localRingsSourceMap y w K hK n m)) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  -- abbreviations for the three cohomology-level factors of the source identification
  let nu2 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
      ((affineDerivedSections ch.incU).obj K))
  let nu3 := RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom
  let nu4 := (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
    ((ch.localRingsSourceIso y w).hom.app ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
  -- `𝒪_{S'}(V')`-equivariance of the unit into the localized base-change cohomology
  have hiotaR : ∀ (r : ch.R') (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u)),
      (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
          ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⊗ₜ[ch.R', ch.toStalkR' y]
            ((Algebra.TensorProduct.includeRight r : ch.A ⊗[ch.R] ch.R') • m)) =
        (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((affineDerivedSections ch.incU).obj K) n from
          (Algebra.TensorProduct.includeRight (ch.toStalkR' y r) :
              ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((affineDerivedSections ch.incU).obj K) n from
              (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
                ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                  ⊗ₜ[ch.R', ch.toStalkR' y] m))) := by
    intro r m
    refine Eq.trans (congrArg (fun z => (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
        ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⊗ₜ[ch.R', ch.toStalkR' y] z))
      (RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral_includeRight_smul
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n r m)) ?_
    refine Eq.trans (congrArg (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
      ((TensorProduct.smul_tmul (R := ch.R') r
          (1 : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) _).symm.trans
        (ModuleCat.ExtendScalars.smul_tmul (ch.toStalkR' y) (ch.toStalkR' y r) 1 _).symm)) ?_
    refine Eq.trans ((ch.homologyBaseChangeLocalizedIso y K n).inv.hom.map_smul
      (ch.toStalkR' y r) _) ?_
    exact (RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul
      (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) n (ch.toStalkR' y r) _).symm
  -- the generators `1 ⊗ m` of the pointwise source, as a map of chart-pushout modules
  have hnu4R : ∀ (r : ch.R') (z : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) n : Type u)),
      nu4.hom ((Algebra.TensorProduct.includeRight (ch.toStalkR' y r) :
            ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • z) =
        (Algebra.TensorProduct.includeRight (ch.toStalkR' y r) :
            ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          (show RingTheory.TorIndependence.baseChangeCohomology
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n from nu4.hom z) :=
    fun r z => ch.localRingsSourceIso_homology_includeRight_smul y w n
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K) (ch.toStalkR' y r) z
  intro r m
  refine Eq.trans (congrArg (fun z => nu4.hom (nu3.hom (nu2.hom z))) (hiotaR r m)) ?_
  refine Eq.trans (congrArg (fun z => nu4.hom (nu3.hom z)) (nu2.hom.map_smul _ _)) ?_
  refine Eq.trans (congrArg (fun z => nu4.hom z) (nu3.hom.map_smul _ _)) ?_
  exact hnu4R r _

/-- **The source identification of the cube at a chart.** The transpose, along
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`, of
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap`:

`(𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}) ⊗_{𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')}
    H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))  ⟶
  H^n(K_{g'x'}|_{𝒪_{S,s}} ⊗ᴸ_{𝒪_{S,s}} 𝒪_{S',s'})`.

Being a transpose it is linear over `𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}` by construction, which
is the half of the linearity the final assembly of Stacks 0DJ8 would otherwise have to carry
through the whole chain of corner moves; the other half, that
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap` is linear over the chart's pushout ring,
is `localRingsSourceMap_add`, `localRingsSourceMap_includeLeft_smul` and
`localRingsSourceMap_includeRight_smul`. -/
public def localRingsSourceTranspose (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))
            ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    (ModuleCat.extendScalars.{u, u, u} (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n) ⟶
      RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n :=
  letI := ch.a.hom.toAlgebra
  letI := ch.b.hom.toAlgebra
  letI := (ch.toStalkR y).toAlgebra
  letI := (ch.toStalkA y).toAlgebra
  letI := (ch.toStalkR' y).toAlgebra
  letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  letI : Algebra (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  letI : Module (ch.A ⊗[ch.R] ch.R') ((RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n) : Type u) :=
    Module.compHom _ (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
  have hjL : ∀ a : ch.A,
      (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
          (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a) =
        Algebra.TensorProduct.includeLeft (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) (ch.toStalkA y a) := by
    intro a
    refine Eq.trans (Stacks.TensorProductPushout.mapAlgebraMid_algebraMap_tmul
      (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) a (1 : ch.R')) ?_
    exact congrArg (fun z : ToType (S'.presheaf.stalk (f' (ch.incU' y))) =>
        (ch.toStalkA y a) ⊗ₜ[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))] z)
      (map_one (ch.toStalkR' y))
  have hjR : ∀ r : ch.R',
      (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
          (Algebra.TensorProduct.includeRight r) =
        Algebra.TensorProduct.includeRight (ch.toStalkR' y r) := by
    intro r
    refine Eq.trans (Stacks.TensorProductPushout.mapAlgebraMid_algebraMap_tmul
      (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) (1 : ch.A) r) ?_
    exact congrArg (fun z : ToType (X.presheaf.stalk (g' (ch.incU' y))) =>
        z ⊗ₜ[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))] (ch.toStalkR' y r))
      (map_one (ch.toStalkA y))
  ModuleCat.extendScalarsTranspose (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
    (ModuleCat.ofHom
      (X := RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n)
      (Y := (ModuleCat.restrictScalars.{u, u, u} (algebraMap (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
        (RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n))
      (RingTheory.TorIndependence.tensorLinearMapOfIncludes
        (R := ch.R) (A := ch.A) (S := ch.R')
        (M := ((RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n) : Type u))
        (N := ((RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n) : Type u))
        (AddMonoidHom.mk' (ch.localRingsSourceMap y w K hK n)
          (ch.localRingsSourceMap_add y w K hK n))
        (fun a m => Eq.trans (ch.localRingsSourceMap_includeLeft_smul y w K hK n a m)
          (congrArg (fun c : ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y))) => c •
            (show ((RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n) : Type u) from
              ch.localRingsSourceMap y w K hK n m)) (hjL a)).symm)
        (fun r m => Eq.trans (ch.localRingsSourceMap_includeRight_smul y w K hK n r m)
          (congrArg (fun c : ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y))) => c •
            (show ((RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n) : Type u) from
              ch.localRingsSourceMap y w K hK n m)) (hjR r)).symm)))

/-- **The source identification on the generators `1 ⊗ m`.** The transpose of
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap` recovers it on the generators of its
source, which is the only thing about the transpose the final assembly of Stacks 0DJ8 uses
beyond its linearity. -/
public theorem localRingsSourceTranspose_one_tmul (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))
            ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    ∀ m₀ : ((RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n) : Type u),
      (ch.localRingsSourceTranspose y w K hK n).hom
          ((1 : ToType (X.presheaf.stalk (g' (ch.incU' y)))
            ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
            ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ⊗ₜ[ch.A ⊗[ch.R] ch.R',
            algebraMap (ch.A ⊗[ch.R] ch.R')
            (ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y))))] m₀) =
        ch.localRingsSourceMap y w K hK n m₀ := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  exact fun m₀ => ModuleCat.extendScalarsTranspose_one_tmul _ _ m₀

/-- **The two routes from the chart's pushout ring to the local ring of `X'` at `x'` agree.**
Through `𝒪_{X'}(U')` and the germ map at `y`, or through the pushout
`𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}` of the local rings: on `a ⊗ r'` both give
`g'.stalkMap (toStalkA a) * f'.stalkMap (toStalkR' r')`, by the two compatibilities
`AlgebraicGeometry.BaseChangeChart.toStalkA'_c` and
`AlgebraicGeometry.BaseChangeChart.toStalkA'_d`. -/
public theorem chartPushoutRingMap_eq (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk
          (f (g' (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  ε'.comp ((specGermRingHom ch.A' y).comp (RingTheory.TorIndependence.baseChangeTensorRingMap
        (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A'))) =
        (RingTheory.TorIndependence.baseChangeTensorRingMap
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y)))).comp
          (algebraMap (ch.A ⊗[ch.R] ch.R')
            (ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y))))) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  have : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  have : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t₁ t₂ h₁' h₂' => rw [map_add, map_add, h₁', h₂']
  | tmul a r =>
    have hc := DFunLike.congr_fun (ch.toStalkA'_c y ε' h₁ h₂) a
    have hd := DFunLike.congr_fun (ch.toStalkA'_d y ε' h₁ h₂) r
    simp only [RingHom.comp_apply] at hc hd ⊢
    rw [RingTheory.TorIndependence.baseChangeTensorRingMap_tmul, map_mul, map_mul,
      Stacks.TensorProductPushout.mapAlgebraMid_algebraMap_tmul,
      RingTheory.TorIndependence.baseChangeTensorRingMap_tmul]
    exact congrArg₂ (· * ·) hc.symm hd


/-- **The bijection `θ` of the source bridge of Stacks 0DJ8.** Three cancellations and the
source identification: the germ extension along `𝒪_{X'}(U') → 𝒪_{Spec 𝒪_{X'}(U'), y}` is
merged with the chart's own by `ModuleCat.extendScalarsComp`, the germ comparison at `U'` is
crossed by `ModuleCat.extendScalarsTargetEquiv`, the two spellings of
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X',x'}` are identified by
`AlgebraicGeometry.BaseChangeChart.chartPushoutRingMap_eq`, and the result is split again along
the pushout of the local rings, where
`AlgebraicGeometry.BaseChangeChart.localRingsSourceTranspose` acts. -/
public def sourceBridgeMap (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp
      (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    ((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).obj
        ((ModuleCat.extendScalars.{u, u, u} (RingTheory.TorIndependence.baseChangeTensorRingMap
          (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A'))).obj
          (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n)) : Type u) →
      ((ModuleCat.extendScalars.{u, u, u} (RingTheory.TorIndependence.baseChangeTensorRingMap
          (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          (A' := ToType (X'.presheaf.stalk (ch.incU' y))))).obj
        (RingTheory.TorIndependence.baseChangeCohomology
          (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n) : Type u) :=
  letI := ch.a.hom.toAlgebra
  letI := ch.b.hom.toAlgebra
  letI := ch.c.hom.toAlgebra
  letI := ch.d.hom.toAlgebra
  letI := (ch.c.hom.comp ch.a.hom).toAlgebra
  haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  letI := (ch.toStalkR y).toAlgebra
  letI := (ch.toStalkA y).toAlgebra
  letI := (ch.toStalkR' y).toAlgebra
  letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  letI := ((g'.stalkMap (ch.incU' y)).hom.comp
    (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  letI : Algebra (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
        ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  fun m =>
    ((ModuleCat.extendScalars.{u, u, u} (RingTheory.TorIndependence.baseChangeTensorRingMap
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y))))).map
          (ch.localRingsSourceTranspose y w K hK n)).hom
      ((((ModuleCat.extendScalarsComp (algebraMap (ch.A ⊗[ch.R] ch.R')
              (ToType (X.presheaf.stalk (g' (ch.incU' y)))
                ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
            (RingTheory.TorIndependence.baseChangeTensorRingMap
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            (A' := ToType (X'.presheaf.stalk (ch.incU' y))))).app
          (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n)).hom).hom
        (((eqToIso (congrArg
            (fun p : (ch.A ⊗[ch.R] ch.R') →+* (ToType (X'.presheaf.stalk (ch.incU' y))) =>
              (ModuleCat.extendScalars.{u, u, u} p).obj
                (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
                ((affineDerivedSections ch.incU).obj K) n))
            (ch.chartPushoutRingMap_eq y w ε' h₁ h₂))).hom).hom
          (ModuleCat.extendScalarsTargetEquiv
              ((specGermRingHom ch.A' y).comp (RingTheory.TorIndependence.baseChangeTensorRingMap
                (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A')))
              ε' (ch.incU'.stalkMap y).hom h₂ h₁
              (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
              ((affineDerivedSections ch.incU).obj K) n)
            ((((ModuleCat.extendScalarsComp (RingTheory.TorIndependence.baseChangeTensorRingMap
                (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A'))
                (specGermRingHom ch.A' y)).app
              (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
              ((affineDerivedSections ch.incU).obj K) n)).inv).hom m))))


end BaseChangeChart

end AlgebraicGeometry

end
