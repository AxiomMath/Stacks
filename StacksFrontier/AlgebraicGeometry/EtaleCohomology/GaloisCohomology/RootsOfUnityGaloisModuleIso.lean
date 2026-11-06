module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.RootsOfUnityStalkIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois module of `μ_n` over a field, and Tag 03QU part (3) at `μ_n`

Let `K` be a field and `sbar` a geometric point of `Spec K`, with `κ` the residue field at its
image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar`.  The stalk of `μ_n` at `sbar` is
`μ_n(Kˢᵉᵖ)` (`AlgebraicGeometry.rootsOfUnityStalkIsoRootsOfUnity`) and germ evaluation is Galois
equivariant (`AlgebraicGeometry.rootsOfUnitySectionEval_galoisFiberAction`).  This file packages
those two into an isomorphism of **discrete Galois modules** and feeds it to the comparison of
Stacks 03QU part (3), giving

`H^q_étale(Spec K, μ_n) ≅ H^q(Gal(Kˢᵉᵖ/κ), μ_n(Kˢᵉᵖ))` for every `q`.

The isomorphism of discrete Galois modules
`AlgebraicGeometry.rootsOfUnityContinuousGModuleIso` is **clause (4) of [Stacks, Tag 03QV]**: the
sheaf `μ_n` on the small étale site of `Spec K` corresponds, under the stalk equivalence of
[Stacks, Tag 04JQ], to `μ_n(Kˢᵉᵖ)` with its `G`-action.

## Main definitions

* `AlgebraicGeometry.sepClosureRootsOfUnityGModule` — the discrete Galois module `μ_n(Kˢᵉᵖ)` at
  the coefficient universe of étale cohomology, i.e.
  `Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift` at the raise `u + 1`.
* `AlgebraicGeometry.rootsOfUnityContinuousGModuleIso` — **clause (4) of Tag 03QV: the Galois
  module of `μ_n` is `μ_n(Kˢᵉᵖ)`**.
* `AlgebraicGeometry.rootsOfUnitySheafHAddEquivContinuousGroupCohomology` — **Tag 03QU part (3)
  at `μ_n`**.

## Main results

* `AlgebraicGeometry.subsingleton_rootsOfUnitySheafH_iff_isZero` — the vanishing of
  `H^q_étale(Spec K, μ_n)` is the vanishing of the Galois cohomology of `μ_n(Kˢᵉᵖ)`.

## Implementation notes

This is the `n`-torsion transcription of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule`
and follows it step for step; in particular the equivariance is read on the
abelian-group-valued stalk and its germs, the conversion with the carrier of the module of
Tag 04JQ having been paid once and for all in
`AlgebraicGeometry.etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm`.

**The universe alignment.** `Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift.{s, t} κ
Kˢᵉᵖ n` has carrier `ULift.{t} (Additive μ_n(Kˢᵉᵖ))`; at `t := u + 1` that is exactly the carrier
`AlgebraicGeometry.sepClosureRootsOfUnity` of the stalk computation, so the identification here
is a transport along an isomorphism and no universe-changing functor on `ContinuousGModule` is
needed.

**The universe instantiation of the sheaf.** `Stacks.Kummer.rootsOfUnitySheaf.{u, v}` of a scheme
in `Scheme.{u}` has coefficients in `AddCommGrpCat.{max (u + 1) v}`, and everything here is
stated at `v = u + 1`, which is the coefficient universe of Tag 03QU part (3) and the
instantiation in which Tags 03RG, 03RJ and 03RK state their cohomology groups.

**No vanishing statement is derived here.**  Unlike the multiplicative case, where Stacks 03R8
supplies `H^q(Gal, (Kˢᵉᵖ)ˣ) = 0` for `q ≥ 1`, the Galois cohomology of `μ_n(Kˢᵉᵖ)` does not
vanish, so only the translation
`AlgebraicGeometry.subsingleton_rootsOfUnitySheafH_iff_isZero` is recorded.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example whose
  clause (4) is `AlgebraicGeometry.rootsOfUnityContinuousGModuleIso`.
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): the comparison, whose
  part (3) is instantiated here at `μ_n`.
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the stalk equivalence,
  whose Galois action is identified here with the action on `μ_n(Kˢᵉᵖ)`.
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence,
  which presents `μ_n` as the kernel of the `n`-th power map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

attribute [local instance]
  preservesFilteredColimitsOfSize_forget_addCommGrpCat
  isGrothendieckAbelian_sheaf_smallEtale_pinnedCoefficients

section Comparison

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (n : ℕ)

/-! ### The discrete Galois module of the `n`-th roots of unity of the separable closure -/

/-- **The discrete Galois module `μ_n(Kˢᵉᵖ)` at the coefficient universe of étale cohomology.**
This is `Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift` of the separable closure of
the residue field at the image of the geometric point, raised to `u + 1`; its carrier is the
abelian group `AlgebraicGeometry.sepClosureRootsOfUnity` in which the stalk of `μ_n` is
computed. -/
abbrev sepClosureRootsOfUnityGModule :
    ContinuousGModule.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift.{u, u + 1}
    ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
    ↥(GeometricPoint.separableClosure sbar) n

/-- The same module in the abelian-group encoding of discrete Galois modules, which is the
encoding the stalk equivalence of Tag 04JQ produces. -/
abbrev sepClosureRootsOfUnityGAddCommGrp :
    ContinuousGAddCommGrp.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar)).functor.obj
      (sepClosureRootsOfUnityGModule K sbar n)

/-! ### Germ evaluation on the abelian stalk -/

/-- The comparison of the stalk of `μ_n` with the `n`-th roots of unity of the separable closure,
on the germ of a section, is germ evaluation. -/
theorem rootsOfUnityStalkToRootsOfUnity_abelianEtaleStalkGerm
    (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U) : _)) :
    ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
        (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
          (rootsOfUnitySheafRestriction B K hK n) (Functor.elementsMk _ U p) t) =
      ConcreteCategory.hom (rootsOfUnitySectionEval B K hK sbar n U p) t :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_comp_rootsOfUnityStalkToRootsOfUnity B K hK sbar n U p) t

/-! ### The comparison is a map of Galois modules -/

/-- The abelian group of the Galois module of `μ_n`, identified with the `n`-th roots of unity of
the separable closure: the identification of Tag 04JQ followed by the stalk computation. -/
abbrev rootsOfUnityGaloisModuleIsoRootsOfUnity :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
        (rootsOfUnitySheafRestriction B K hK n)).obj.obj.V : _) ≅
      sepClosureRootsOfUnity K sbar n :=
  (abelianEtaleStalkEquivalenceIso.{u, u + 1} B K hK sbar).app
      (rootsOfUnitySheafRestriction B K hK n) ≪≫
    rootsOfUnityStalkIsoRootsOfUnity B K hK sbar n

/-- **The identification of the stalk of `μ_n` with the `n`-th roots of unity of the separable
closure is Galois equivariant, on the germ of a section.**  The action of Tag 04JQ moves the germ
to the germ at the translated lift, where germ evaluation is germ evaluation followed by the
automorphism. -/
theorem rootsOfUnityStalkToRootsOfUnity_rho_abelianEtaleStalkGerm
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U) : _)) :
    ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (rootsOfUnitySheafRestriction B K hK n)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (rootsOfUnitySheafRestriction B K hK n)).obj.obj.ρ σ).asHom
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
                (rootsOfUnitySheafRestriction B K hK n)).symm
              (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
                (rootsOfUnitySheafRestriction B K hK n) (Functor.elementsMk _ U p) t)))) =
      ConcreteCategory.hom (sepClosureRootsOfUnitySmul K sbar n σ)
        (ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
          (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
            (rootsOfUnitySheafRestriction B K hK n) (Functor.elementsMk _ U p) t)) := by
  rw [etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm.{u, u + 1} B K hK sbar
      (rootsOfUnitySheafRestriction B K hK n) σ (Functor.elementsMk _ U p) t,
    rootsOfUnityStalkToRootsOfUnity_abelianEtaleStalkGerm,
    rootsOfUnityStalkToRootsOfUnity_abelianEtaleStalkGerm,
    rootsOfUnitySectionEval_galoisFiberAction]
  rfl

/-- **The identification of the stalk of `μ_n` with the `n`-th roots of unity of the separable
closure is Galois equivariant**, written on an arbitrary element of the abelian stalk.  Every
such element is the germ of a section, so this is the germwise statement. -/
theorem rootsOfUnityStalkToRootsOfUnity_rho_symm
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (y : ((abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
      (rootsOfUnitySheafRestriction B K hK n) : _)) :
    ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (rootsOfUnitySheafRestriction B K hK n)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (rootsOfUnitySheafRestriction B K hK n)).obj.obj.ρ σ).asHom
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
              (rootsOfUnitySheafRestriction B K hK n)).symm y))) =
      ConcreteCategory.hom (sepClosureRootsOfUnitySmul K sbar n σ)
        (ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n) y) := by
  obtain ⟨U, p, t, rfl⟩ := (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
    (P := (rootsOfUnitySheafRestriction B K hK n).obj) y
  exact rootsOfUnityStalkToRootsOfUnity_rho_abelianEtaleStalkGerm B K hK sbar n σ U p t

/-- The same equivariance, written on an arbitrary element of the carrier of the Galois module of
Tag 04JQ. -/
theorem rootsOfUnityStalkToRootsOfUnity_etaleGaloisModule_rho
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : ((etaleGaloisModule.{u, u + 1} B K hK sbar
      (rootsOfUnitySheafRestriction B K hK n)).obj.obj.V : _)) :
    ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (rootsOfUnitySheafRestriction B K hK n)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
            (rootsOfUnitySheafRestriction B K hK n)).obj.obj.ρ σ).asHom x)) =
      ConcreteCategory.hom (sepClosureRootsOfUnitySmul K sbar n σ)
        (ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
          (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
            (rootsOfUnitySheafRestriction B K hK n) x)) :=
  (congrArg (fun z : ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (rootsOfUnitySheafRestriction B K hK n)).obj.obj.V : _) =>
        ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)
          (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
            (rootsOfUnitySheafRestriction B K hK n)
            (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (rootsOfUnitySheafRestriction B K hK n)).obj.obj.ρ σ).asHom z)))
      ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
        (rootsOfUnitySheafRestriction B K hK n)).symm_apply_apply x)).symm.trans
    (rootsOfUnityStalkToRootsOfUnity_rho_symm B K hK sbar n σ
      (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
        (rootsOfUnitySheafRestriction B K hK n) x))

/-- The equivariance, as a commuting square of morphisms of abelian groups: this is the
hypothesis `CategoryTheory.Action.mkIso` asks for. -/
theorem rootsOfUnityGaloisModuleIsoRootsOfUnity_comm
    (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (rootsOfUnitySheafRestriction B K hK n)).obj.obj.ρ σ).asHom ≫
        (rootsOfUnityGaloisModuleIsoRootsOfUnity B K hK sbar n).hom =
      (rootsOfUnityGaloisModuleIsoRootsOfUnity B K hK sbar n).hom ≫
        sepClosureRootsOfUnitySmul K sbar n σ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext
    (rootsOfUnityStalkToRootsOfUnity_etaleGaloisModule_rho B K hK sbar n σ))

/-- The underlying action of `Gal(Kˢᵉᵖ/κ)` on the stalk of `μ_n` is its action on the `n`-th
roots of unity of the separable closure. -/
@[sga "4½ Arcata 2.4.5"]
def rootsOfUnityGaloisActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
        (rootsOfUnitySheafRestriction B K hK n)).obj.obj ≅
      (sepClosureRootsOfUnityGAddCommGrp K sbar n).obj.obj :=
  Action.mkIso (rootsOfUnityGaloisModuleIsoRootsOfUnity B K hK sbar n)
    (rootsOfUnityGaloisModuleIsoRootsOfUnity_comm B K hK sbar n)

/-- The same isomorphism between the underlying continuous actions. -/
def rootsOfUnityGaloisContActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
        (rootsOfUnitySheafRestriction B K hK n)).obj ≅
      (sepClosureRootsOfUnityGAddCommGrp K sbar n).obj :=
  ObjectProperty.isoMk _ (rootsOfUnityGaloisActionIso B K hK sbar n)

/-- **The Galois module of `μ_n` over a field is `μ_n(Kˢᵉᵖ)`**, in the abelian-group encoding of
discrete Galois modules. -/
def rootsOfUnityGaloisModuleIso :
    etaleGaloisModule.{u, u + 1} B K hK sbar (rootsOfUnitySheafRestriction B K hK n) ≅
      sepClosureRootsOfUnityGAddCommGrp K sbar n :=
  ObjectProperty.isoMk _ (rootsOfUnityGaloisContActionIso B K hK sbar n)

/-- **Stacks Project, Tag 03QV, clause (4).**  The sheaf `μ_n` on the small étale site of
`Spec K` corresponds, under the stalk equivalence of Tag 04JQ, to the discrete Galois module
`μ_n(Kˢᵉᵖ)` with its `G`-action.  This is the stalk computation
`AlgebraicGeometry.rootsOfUnityStalkIsoRootsOfUnity` packaged with its germwise Galois
equivariance `AlgebraicGeometry.rootsOfUnitySectionEval_galoisFiberAction`, and it is the input
Tag 03QU part (3) needs to be evaluated at `μ_n`. -/
@[sga "4½ Arcata 2.4.5"]
def rootsOfUnityContinuousGModuleIso :
    (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (rootsOfUnitySheafRestriction B K hK n) ≅ sepClosureRootsOfUnityGModule K sbar n :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar)).inverse.mapIso
      (rootsOfUnityGaloisModuleIso B K hK sbar n) ≪≫
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).unitIso.app
        (sepClosureRootsOfUnityGModule K sbar n)).symm

/-! ### Tag 03QU part (3) at `μ_n` -/

/-- **Stacks Project, Tag 03QU, part (3), at `μ_n`.**  For a field `K`, a geometric point `sbar`
of `Spec K` and every degree `q`,

`H^q_étale(Spec K, μ_n) ≅ H^q(Gal(Kˢᵉᵖ/κ), μ_n(Kˢᵉᵖ))`,

`κ` being the residue field at the image of `sbar`.  This is the general comparison
`AlgebraicGeometry.smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology` with its Galois
module identified at `μ_n` by `AlgebraicGeometry.rootsOfUnityContinuousGModuleIso`, which is
clause (4) of Tag 03QV. -/
def rootsOfUnitySheafHAddEquivContinuousGroupCohomology (q : ℕ) :
    Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n) q ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        (sepClosureRootsOfUnityGModule K sbar n) :=
  (smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology B K hK sbar
      (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n) q).trans
    (((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (rootsOfUnityContinuousGModuleIso B K hK sbar n)).addCommGroupIsoToAddEquiv)

include B hK in
/-- The vanishing of `H^q_étale(Spec K, μ_n)` is the vanishing of the Galois cohomology of
`μ_n(Kˢᵉᵖ)`. -/
theorem subsingleton_rootsOfUnitySheafH_iff_isZero (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n) q) ↔
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) q
        (sepClosureRootsOfUnityGModule K sbar n)) := by
  rw [subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology B K hK sbar
    (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n) q]
  exact ((continuousGroupCohomologyFunctor.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
      (rootsOfUnityContinuousGModuleIso B K hK sbar n)).isZero_iff

end Comparison

end AlgebraicGeometry

end
