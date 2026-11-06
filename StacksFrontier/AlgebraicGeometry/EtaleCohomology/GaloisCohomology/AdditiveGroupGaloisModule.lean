module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGaloisModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule
import StacksCore.Tactic.StacksAttribute

/-!
# The Galois module of `𝐆_a` over a field, and Tag 03QU part (3) at `𝐆_a`

Let `K` be a field and `sbar` a geometric point of `Spec K`, with `κ` the residue field at its
image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar`.  The stalk of `𝐆_a` at `sbar` is
`(Kˢᵉᵖ, +)` (`AlgebraicGeometry.additiveStalkIsoSepClosure`) and germ evaluation is Galois
equivariant (`AlgebraicGeometry.additiveSectionEval_galoisFiberAction`).  This file packages
those two into an isomorphism of **discrete Galois modules** and feeds it to the comparison of
Stacks 03QU part (3), giving

`H^q_étale(Spec K, 𝐆_a) ≅ H^q(Gal(Kˢᵉᵖ/κ), Kˢᵉᵖ)` for every `q`,

`Kˢᵉᵖ` on the right being the Galois module with addition as group law.  This is the
identification of the second and third terms of the additive chain of equalities of
[Stacks, Tag 03QV].

## Main definitions

* `AlgebraicGeometry.sepClosureAddGModule` — the discrete Galois module `(Kˢᵉᵖ, +)` at the
  coefficient universe of étale cohomology, i.e.
  `Stacks.GaloisCohomology.addContinuousGModuleLift` at the raise `u + 1`.
* `AlgebraicGeometry.additiveContinuousGModuleIso` — **the Galois module of `𝐆_a` is
  `(Kˢᵉᵖ, +)`**.
* `AlgebraicGeometry.additiveSheafHAddEquivContinuousGroupCohomology` — **Tag 03QU part (3) at
  `𝐆_a`**.

## Main results

* `AlgebraicGeometry.subsingleton_additiveSheafH_iff_isZero` — the vanishing of
  `H^q_étale(Spec K, 𝐆_a)` is the vanishing of the Galois cohomology of `(Kˢᵉᵖ, +)`.

## Implementation notes

This is the additive transcription of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule`
and follows it step for step; in particular the equivariance is read on the abelian-group-valued
stalk and its germs, the conversion with the carrier of the module of Tag 04JQ having been paid
once and for all in `AlgebraicGeometry.etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm`.

**The universe alignment.**  `Stacks.GaloisCohomology.addContinuousGModuleLift.{s, t} κ Kˢᵉᵖ` has
carrier `ULift.{t} Kˢᵉᵖ`; at `t := u + 1` that is exactly the carrier
`AlgebraicGeometry.sepClosureAdd` of the stalk computation, so the identification here is a
transport along an isomorphism and no universe-changing functor on `ContinuousGModule` is needed.

**The universe instantiation of the sheaf.**  `Stacks.ArtinSchreier.additiveSheaf.{u, v}` of a
scheme in `Scheme.{u}` has coefficients in `AddCommGrpCat.{max (u + 1) v}`, and everything here
is stated at `v = u + 1`, which is the coefficient universe of Tag 03QU part (3).

**No vanishing statement is derived here.**  Unlike the multiplicative case, where Stacks 03R8
supplies `H^q(Gal, (Kˢᵉᵖ)ˣ) = 0` for `q ≥ 1`, this library proves the vanishing of the
continuous cohomology of the additive group only in degrees one and two and only at the level of
cochains (`Stacks.GaloisCohomology.exists_dZero_eq_additive` and
`Stacks.GaloisCohomology.exists_dOne_eq_additive`), so no vanishing theorem for
`H^q_étale(Spec K, 𝐆_a)` follows from this file alone.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): the comparison, whose
  part (3) is instantiated here at `𝐆_a`.
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the stalk equivalence,
  whose Galois action is identified here with the action on `Kˢᵉᵖ`.
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example whose
  additive chain this identification is the second link of.
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
  (sbar : GeometricPoint (Spec (.of K)))

/-! ### The discrete Galois module of the separable closure under addition -/

/-- **The discrete Galois module `(Kˢᵉᵖ, +)` at the coefficient universe of étale cohomology.**
This is `Stacks.GaloisCohomology.addContinuousGModuleLift` of the separable closure of the
residue field at the image of the geometric point, raised to `u + 1`; its carrier is the abelian
group `AlgebraicGeometry.sepClosureAdd` in which the stalk of `𝐆_a` is computed. -/
abbrev sepClosureAddGModule :
    ContinuousGModule.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  Stacks.GaloisCohomology.addContinuousGModuleLift.{u, u + 1}
    ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
    ↥(GeometricPoint.separableClosure sbar)

/-- The same module in the abelian-group encoding of discrete Galois modules, which is the
encoding the stalk equivalence of Tag 04JQ produces. -/
abbrev sepClosureAddGAddCommGrp :
    ContinuousGAddCommGrp.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar)).functor.obj (sepClosureAddGModule K sbar)

/-! ### Germ evaluation on the abelian stalk -/

/-- The comparison of the stalk of `𝐆_a` with the separable closure, on the germ of a section, is
germ evaluation. -/
theorem additiveStalkToSepClosure_abelianEtaleStalkGerm (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((additiveSheafRestriction B K hK).obj.obj (op U) : _)) :
    ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
        (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
          (additiveSheafRestriction B K hK) ⟨p⟩ t) =
      ConcreteCategory.hom (additiveSectionEval B K hK sbar U p) t :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_comp_additiveStalkToSepClosure B K hK sbar U p) t

/-! ### The comparison is a map of Galois modules -/

/-- The abelian group of the Galois module of `𝐆_a`, identified with the separable closure under
addition: the identification of Tag 04JQ followed by the stalk computation. -/
abbrev additiveGaloisModuleIsoSepClosure :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
        (additiveSheafRestriction B K hK)).obj.obj.V : _) ≅ sepClosureAdd K sbar :=
  (abelianEtaleStalkEquivalenceIso.{u, u + 1} B K hK sbar).app
      (additiveSheafRestriction B K hK) ≪≫
    additiveStalkIsoSepClosure B K hK sbar

/-- **The identification of the stalk of `𝐆_a` with the separable closure is Galois equivariant,
on the germ of a section.**  The action of Tag 04JQ moves the germ to the germ at the translated
lift, where germ evaluation is germ evaluation followed by the automorphism. -/
theorem additiveStalkToSepClosure_rho_abelianEtaleStalkGerm
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((additiveSheafRestriction B K hK).obj.obj (op U) : _)) :
    ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (additiveSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (additiveSheafRestriction B K hK)).obj.obj.ρ σ).asHom
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
                (additiveSheafRestriction B K hK)).symm
              (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
                (additiveSheafRestriction B K hK) ⟨p⟩ t)))) =
      ConcreteCategory.hom (sepClosureAddSmul K sbar σ)
        (ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
          (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
            (additiveSheafRestriction B K hK) ⟨p⟩ t)) := by
  rw [etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm.{u, u + 1} B K hK sbar
      (additiveSheafRestriction B K hK) σ ⟨p⟩ t,
    additiveStalkToSepClosure_abelianEtaleStalkGerm,
    additiveStalkToSepClosure_abelianEtaleStalkGerm,
    additiveSectionEval_galoisFiberAction]
  rfl

/-- **The identification of the stalk of `𝐆_a` with the separable closure is Galois
equivariant**, written on an arbitrary element of the abelian stalk.  Every such element is the
germ of a section, so this is the germwise statement. -/
theorem additiveStalkToSepClosure_rho_symm
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (y : ((abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
      (additiveSheafRestriction B K hK) : _)) :
    ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (additiveSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (additiveSheafRestriction B K hK)).obj.obj.ρ σ).asHom
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
              (additiveSheafRestriction B K hK)).symm y))) =
      ConcreteCategory.hom (sepClosureAddSmul K sbar σ)
        (ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar) y) := by
  obtain ⟨U, p, t, rfl⟩ := (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
    (P := (additiveSheafRestriction B K hK).obj) y
  exact additiveStalkToSepClosure_rho_abelianEtaleStalkGerm B K hK sbar σ U p t

/-- The same equivariance, written on an arbitrary element of the carrier of the Galois module of
Tag 04JQ. -/
theorem additiveStalkToSepClosure_etaleGaloisModule_rho
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : ((etaleGaloisModule.{u, u + 1} B K hK sbar
      (additiveSheafRestriction B K hK)).obj.obj.V : _)) :
    ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (additiveSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
            (additiveSheafRestriction B K hK)).obj.obj.ρ σ).asHom x)) =
      ConcreteCategory.hom (sepClosureAddSmul K sbar σ)
        (ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
          (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
            (additiveSheafRestriction B K hK) x)) :=
  by
  obtain ⟨y, rfl⟩ := (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
    (additiveSheafRestriction B K hK)).symm.surjective x
  simpa using additiveStalkToSepClosure_rho_symm B K hK sbar σ y

/-- The equivariance, as a commuting square of morphisms of abelian groups: this is the
hypothesis `CategoryTheory.Action.mkIso` asks for. -/
theorem additiveGaloisModuleIsoSepClosure_comm
    (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (additiveSheafRestriction B K hK)).obj.obj.ρ σ).asHom ≫
        (additiveGaloisModuleIsoSepClosure B K hK sbar).hom =
      (additiveGaloisModuleIsoSepClosure B K hK sbar).hom ≫ sepClosureAddSmul K sbar σ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext
    (additiveStalkToSepClosure_etaleGaloisModule_rho B K hK sbar σ))

/-- The underlying action of `Gal(Kˢᵉᵖ/κ)` on the stalk of `𝐆_a` is its action on the separable
closure. -/
def additiveGaloisActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
        (additiveSheafRestriction B K hK)).obj.obj ≅
      (sepClosureAddGAddCommGrp K sbar).obj.obj :=
  Action.mkIso (additiveGaloisModuleIsoSepClosure B K hK sbar)
    (additiveGaloisModuleIsoSepClosure_comm B K hK sbar)

/-- The same isomorphism between the underlying continuous actions. -/
def additiveGaloisContActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar (additiveSheafRestriction B K hK)).obj ≅
      (sepClosureAddGAddCommGrp K sbar).obj :=
  ObjectProperty.isoMk _ (additiveGaloisActionIso B K hK sbar)

/-- **The Galois module of `𝐆_a` over a field is the separable closure under addition**, in the
abelian-group encoding of discrete Galois modules. -/
def additiveGaloisModuleIso :
    etaleGaloisModule.{u, u + 1} B K hK sbar (additiveSheafRestriction B K hK) ≅
      sepClosureAddGAddCommGrp K sbar :=
  ObjectProperty.isoMk _ (additiveGaloisContActionIso B K hK sbar)

/-- **The Galois module of `𝐆_a` over a field is the separable closure under addition**, in the
coefficient category of continuous group cohomology.  This is the input Tag 03QU part (3) needs
to be evaluated at `𝐆_a`. -/
def additiveContinuousGModuleIso :
    (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (additiveSheafRestriction B K hK) ≅ sepClosureAddGModule K sbar :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar)).inverse.mapIso
      (additiveGaloisModuleIso B K hK sbar) ≪≫
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).unitIso.app
        (sepClosureAddGModule K sbar)).symm

/-! ### Tag 03QU part (3) at `𝐆_a` -/

/-- **Stacks Project, Tag 03QU, part (3), at `𝐆_a`.**  For a field `K`, a geometric point `sbar`
of `Spec K` and every degree `q`,

`H^q_étale(Spec K, 𝐆_a) ≅ H^q(Gal(Kˢᵉᵖ/κ), Kˢᵉᵖ)`,

`κ` being the residue field at the image of `sbar` and `Kˢᵉᵖ` the Galois module with addition as
group law.  This is the general comparison
`AlgebraicGeometry.smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology` with its Galois
module identified at `𝐆_a` by `AlgebraicGeometry.additiveContinuousGModuleIso`. -/
@[stacks 03QU "part (3) at 𝐆_a, in every degree: the degree-q étale cohomology of the spectrum \
of a field with coefficients in the additive group is the degree-q continuous group cohomology \
of the absolute Galois group with coefficients in the separable closure under addition. This is \
the general objectwise form of part (3) on Mathlib's small étale site, \
smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology, with its Galois module computed at \
𝐆_a by additiveContinuousGModuleIso -- the stalk computation additiveStalkIsoSepClosure \
packaged with its germwise Galois equivariance additiveSectionEval_galoisFiberAction into an \
isomorphism of discrete Galois modules. Nothing is assumed of the field and nothing is carried. \
NOT proved here: parts (1) and (2) of the tag, which are separate registrations"]
def additiveSheafHAddEquivContinuousGroupCohomology (q : ℕ) :
    Sheaf.H.{u + 1, u + 1}
        (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        (sepClosureAddGModule K sbar) :=
  (smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology B K hK sbar
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q).trans
    (((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (additiveContinuousGModuleIso B K hK sbar)).addCommGroupIsoToAddEquiv)

include B hK in
/-- The vanishing of `H^q_étale(Spec K, 𝐆_a)` is the vanishing of the Galois cohomology of the
separable closure under addition. -/
theorem subsingleton_additiveSheafH_iff_isZero (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q) ↔
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) q (sepClosureAddGModule K sbar)) := by
  rw [subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology B K hK sbar
    (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q]
  exact Iso.isZero_iff ((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (additiveContinuousGModuleIso B K hK sbar))

end Comparison

end AlgebraicGeometry

end
