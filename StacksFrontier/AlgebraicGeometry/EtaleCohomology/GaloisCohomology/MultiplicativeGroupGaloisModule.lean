module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.StacksAttribute

/-!
# The Galois module of `𝐆_m` over a field and its étale cohomology

Let `K` be a field and `sbar` a geometric point of `Spec K`, with `κ` the residue field at its
image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar`. The Galois module of `𝐆_m` at `sbar` is
the discrete `Gal(Kˢᵉᵖ/κ)`-module `(Kˢᵉᵖ)ˣ`, so that

`H^q_étale(Spec K, 𝐆_m) ≅ H^q(Gal(Kˢᵉᵖ/κ), (Kˢᵉᵖ)ˣ)` for every `q`.

Consequently `H^1_étale(Spec K, 𝐆_m) = 0`, and `H^q_étale(Spec K, 𝐆_m) = 0` for every `q ≥ 1`
when the Brauer group of every finite extension of `K` is trivial.

## Main definitions

* `AlgebraicGeometry.sepClosureUnitsGModule`: the discrete Galois module `(Kˢᵉᵖ)ˣ` at the
  coefficient universe of étale cohomology.
* `AlgebraicGeometry.multiplicativeContinuousGModuleIso`: the Galois module of `𝐆_m` is
  `(Kˢᵉᵖ)ˣ`.
* `AlgebraicGeometry.multiplicativeSheafHAddEquivContinuousGroupCohomology`:
  `H^q_étale(Spec K, 𝐆_m) ≅ H^q(Gal(Kˢᵉᵖ/κ), (Kˢᵉᵖ)ˣ)`.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_one`: `H^1_étale(Spec K, 𝐆_m) = 0`
  for an arbitrary field (Hilbert's theorem 90).
* `AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_two`:
  `H^2_étale(Spec K, 𝐆_m) = 0` when the Brauer group of every finite extension of `K` is
  trivial.
* `AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer`:
  `H^q_étale(Spec K, 𝐆_m) = 0` in every degree `q ≥ 1` when the Brauer group of every finite
  extension of `K` is trivial.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

attribute [local instance] preservesFilteredColimitsOfSize_forget_addCommGrpCat

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`. -/
local instance isGrothendieckAbelian_sheaf_smallEtale_pinnedCoefficients (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{u, u + 1} X

section Comparison

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-! ### The discrete Galois module of the units of the separable closure -/

/-- The discrete Galois module `(Kˢᵉᵖ)ˣ` at the coefficient universe of étale cohomology:
`Stacks.GaloisCohomology.unitsContinuousGModuleLift` of the separable closure of the residue
field at the image of the geometric point, raised to `u + 1`. -/
abbrev sepClosureUnitsGModule :
    ContinuousGModule.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  Stacks.GaloisCohomology.unitsContinuousGModuleLift.{u, u + 1}
    ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
    ↥(GeometricPoint.separableClosure sbar)

/-- The discrete Galois module `(Kˢᵉᵖ)ˣ` in the abelian-group encoding of discrete Galois
modules. -/
abbrev sepClosureUnitsGAddCommGrp :
    ContinuousGAddCommGrp.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar)).functor.obj (sepClosureUnitsGModule K sbar)

/-! ### Germ evaluation on the abelian stalk -/

/-- The germ of a section of `𝐆_m` in the abelian-group-valued stalk is its germ as an element
of the fiber of the point of the site attached to the geometric point. -/
theorem abelianEtaleStalkGerm_eq_toPresheafFiber
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1})
    (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U)) :
    abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar F ⟨U, p⟩ t =
      ConcreteCategory.hom ((fieldSitePoint B K hK sbar).toPresheafFiber U p
        ((sheafToPresheaf _ _).obj F)) t := rfl

/-- The comparison of the stalk of `𝐆_m` with the units of the separable closure, on the germ of
a section, is germ evaluation. -/
theorem multiplicativeStalkToUnits_abelianEtaleStalkGerm (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((multiplicativeSheafRestriction B K hK).obj.obj (op U) : _)) :
    ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
        (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
          (multiplicativeSheafRestriction B K hK) ⟨U, p⟩ t) =
      ConcreteCategory.hom (multiplicativeSectionEval B K hK sbar U p) t :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_comp_multiplicativeStalkToUnits B K hK sbar U p) t

/-! ### The comparison is a map of Galois modules -/

/-- The abelian group of the Galois module of `𝐆_m`, identified with the units of the separable
closure. -/
abbrev multiplicativeGaloisModuleIsoUnits :
    ((etaleGaloisModule.{u, u + 1} B K hK sbar
        (multiplicativeSheafRestriction B K hK)).obj.obj.V : _) ≅ sepClosureUnits K sbar :=
  (abelianEtaleStalkEquivalenceIso.{u, u + 1} B K hK sbar).app
      (multiplicativeSheafRestriction B K hK) ≪≫
    multiplicativeStalkIsoUnits B K hK sbar

/-- The identification of the stalk of `𝐆_m` with the units of the separable closure is Galois
equivariant, on the germ of a section. -/
theorem multiplicativeStalkToUnits_rho_abelianEtaleStalkGerm
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((multiplicativeSheafRestriction B K hK).obj.obj (op U) : _)) :
    ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (multiplicativeSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (multiplicativeSheafRestriction B K hK)).obj.obj.ρ σ)
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
                (multiplicativeSheafRestriction B K hK)).symm
              (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
                (multiplicativeSheafRestriction B K hK) ⟨U, p⟩ t)))) =
      ConcreteCategory.hom (sepClosureUnitsSmul K sbar σ)
        (ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
          (abelianEtaleStalkGerm.{u, u + 1} B (Spec (.of K)) hK sbar
            (multiplicativeSheafRestriction B K hK) ⟨U, p⟩ t)) := by
  rw [etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm.{u, u + 1} B K hK sbar
      (multiplicativeSheafRestriction B K hK) σ ⟨U, p⟩ t,
    multiplicativeStalkToUnits_abelianEtaleStalkGerm,
    multiplicativeStalkToUnits_abelianEtaleStalkGerm,
    multiplicativeSectionEval_galoisFiberAction]
  rfl

/-- The identification of the stalk of `𝐆_m` with the units of the separable closure is Galois
equivariant, written on an arbitrary element of the abelian stalk. -/
theorem multiplicativeStalkToUnits_rho_symm
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (y : ((abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
      (multiplicativeSheafRestriction B K hK) : _)) :
    ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (multiplicativeSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (multiplicativeSheafRestriction B K hK)).obj.obj.ρ σ)
            ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
              (multiplicativeSheafRestriction B K hK)).symm y))) =
      ConcreteCategory.hom (sepClosureUnitsSmul K sbar σ)
        (ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar) y) := by
  obtain ⟨U, p, t, rfl⟩ := (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
    (P := (multiplicativeSheafRestriction B K hK).obj) y
  exact multiplicativeStalkToUnits_rho_abelianEtaleStalkGerm B K hK sbar σ U p t

/-- The identification of the stalk of `𝐆_m` with the units of the separable closure is Galois
equivariant, written on an arbitrary element of the carrier of
`AlgebraicGeometry.etaleGaloisModule`. -/
theorem multiplicativeStalkToUnits_etaleGaloisModule_rho
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : ((etaleGaloisModule.{u, u + 1} B K hK sbar
      (multiplicativeSheafRestriction B K hK)).obj.obj.V : _)) :
    ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
        (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
          (multiplicativeSheafRestriction B K hK)
          (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
            (multiplicativeSheafRestriction B K hK)).obj.obj.ρ σ) x)) =
      ConcreteCategory.hom (sepClosureUnitsSmul K sbar σ)
        (ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
          (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
            (multiplicativeSheafRestriction B K hK) x)) :=
  (congrArg (fun z : ((etaleGaloisModule.{u, u + 1} B K hK sbar
          (multiplicativeSheafRestriction B K hK)).obj.obj.V : _) ↦
        ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)
          (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
            (multiplicativeSheafRestriction B K hK)
            (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar
              (multiplicativeSheafRestriction B K hK)).obj.obj.ρ σ) z)))
      ((etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
        (multiplicativeSheafRestriction B K hK)).symm_apply_apply x)).symm.trans
    (multiplicativeStalkToUnits_rho_symm B K hK sbar σ
      (etaleGaloisModuleAddEquivStalk.{u, u + 1} B K hK sbar
        (multiplicativeSheafRestriction B K hK) x))

/-- The Galois equivariance of `multiplicativeGaloisModuleIsoUnits`, as a commuting square of
morphisms of abelian groups. -/
theorem multiplicativeGaloisModuleIsoUnits_comm (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
          (multiplicativeSheafRestriction B K hK)).obj.obj.ρ σ ≫
        (multiplicativeGaloisModuleIsoUnits B K hK sbar).hom =
      (multiplicativeGaloisModuleIsoUnits B K hK sbar).hom ≫ sepClosureUnitsSmul K sbar σ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext
    (multiplicativeStalkToUnits_etaleGaloisModule_rho B K hK sbar σ))

/-- The underlying action of `Gal(Kˢᵉᵖ/κ)` on the stalk of `𝐆_m` is its action on the units of
the separable closure. -/
def multiplicativeGaloisActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar
        (multiplicativeSheafRestriction B K hK)).obj.obj ≅
      (sepClosureUnitsGAddCommGrp K sbar).obj.obj :=
  Action.mkIso (multiplicativeGaloisModuleIsoUnits B K hK sbar)
    (multiplicativeGaloisModuleIsoUnits_comm B K hK sbar)

/-- The same isomorphism between the underlying continuous actions. -/
def multiplicativeGaloisContActionIso :
    (etaleGaloisModule.{u, u + 1} B K hK sbar (multiplicativeSheafRestriction B K hK)).obj ≅
      (sepClosureUnitsGAddCommGrp K sbar).obj :=
  ObjectProperty.isoMk _ (multiplicativeGaloisActionIso B K hK sbar)

/-- The Galois module of `𝐆_m` over a field is the units of the separable closure, in the
abelian-group encoding of discrete Galois modules. -/
def multiplicativeGaloisModuleIso :
    etaleGaloisModule.{u, u + 1} B K hK sbar (multiplicativeSheafRestriction B K hK) ≅
      sepClosureUnitsGAddCommGrp K sbar :=
  ObjectProperty.isoMk _ (multiplicativeGaloisContActionIso B K hK sbar)

/-- The Galois module of `𝐆_m` over a field is the units of the separable closure, in the
coefficient category of continuous group cohomology. -/
def multiplicativeContinuousGModuleIso :
    (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        (multiplicativeSheafRestriction B K hK) ≅ sepClosureUnitsGModule K sbar :=
  (continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar)).inverse.mapIso
      (multiplicativeGaloisModuleIso B K hK sbar) ≪≫
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).unitIso.app
        (sepClosureUnitsGModule K sbar)).symm

/-! ### The étale cohomology of `𝐆_m` over a field -/

/-- For a field `K`, a geometric point `sbar` of `Spec K` and every degree `q`,

`H^q_étale(Spec K, 𝐆_m) ≅ H^q(Gal(Kˢᵉᵖ/κ), (Kˢᵉᵖ)ˣ)`,

`κ` being the residue field at the image of `sbar`. -/
@[stacks 03QU "part (3) at 𝐆_m, in every degree: the degree-q étale cohomology of the spectrum \
of a field with coefficients in the multiplicative group is the degree-q continuous group \
cohomology of the absolute Galois group with coefficients in the units of the separable \
closure. This is the general objectwise form of part (3) on Mathlib's small étale site, \
smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology, with its Galois module computed at \
𝐆_m by multiplicativeContinuousGModuleIso -- the stalk computation \
multiplicativeStalkIsoUnits packaged with its germwise Galois equivariance \
multiplicativeSectionEval_galoisFiberAction into an isomorphism of discrete Galois modules. \
Nothing is assumed of the field and nothing is carried. NOT proved here: parts (1) and (2) of \
the tag, which are separate registrations"]
def multiplicativeSheafHAddEquivContinuousGroupCohomology (q : ℕ) :
    Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        (sepClosureUnitsGModule K sbar) :=
  (smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology B K hK sbar
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q).trans
    (((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (multiplicativeContinuousGModuleIso B K hK sbar)).addCommGroupIsoToAddEquiv)

include B hK in
/-- The vanishing of `H^q_étale(Spec K, 𝐆_m)` is the vanishing of the Galois cohomology of the
units of the separable closure. -/
theorem subsingleton_multiplicativeSheafH_iff_isZero (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q) ↔
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) q (sepClosureUnitsGModule K sbar)) := by
  rw [subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology B K hK sbar
    (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q]
  exact ⟨fun h ↦ h.of_iso (((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (multiplicativeContinuousGModuleIso B K hK sbar)).symm),
    fun h ↦ h.of_iso ((continuousGroupCohomologyFunctor.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar) q).mapIso
        (multiplicativeContinuousGModuleIso B K hK sbar))⟩

/-! ### Vanishing in every positive degree -/

include B hK sbar in
/-- `H^1_étale(Spec K, 𝐆_m) = 0` for an arbitrary field. -/
theorem subsingleton_multiplicativeSheafH_one :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 1) :=
  (subsingleton_multiplicativeSheafH_iff_isZero B K hK sbar 1).mpr
    (Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_one.{u, u + 1} _ _)

include B hK in
/-- `H^2_étale(Spec K, 𝐆_m) = 0` when the Brauer group of the residue field at the image of the
geometric point is trivial. -/
theorem subsingleton_multiplicativeSheafH_two
    (hBr : ∀ y : BrauerGroup ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)),
      y = 1) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 2) :=
  (subsingleton_multiplicativeSheafH_iff_isZero B K hK sbar 2).mpr
    (Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_two.{u, u + 1} _ _ hBr)

/-- The separable closure of the residue field at the image of a geometric point, taken inside
the algebraically closed field of the point, is separably closed. -/
instance isSepClosed_separableClosure :
    IsSepClosed ↥(GeometricPoint.separableClosure sbar) :=
  (separableClosure.isSepClosure
    ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) sbar.residueField).sep_closed

include B hK in
/-- `H^q_étale(Spec K, 𝐆_m) = 0` in every degree `q ≥ 1` when the Brauer group of every finite
extension of the residue field at the image of the geometric point is trivial. -/
theorem subsingleton_multiplicativeSheafH_of_forall_brauer
    (hBr : ∀ (L : Type u) [Field L]
      [Algebra ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) L]
      [Module.Finite ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) L]
      (y : BrauerGroup L), y = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q) :=
  (subsingleton_multiplicativeSheafH_iff_isZero B K hK sbar q).mpr
    (Stacks.GaloisCohomology.isZero_continuousGroupCohomology_unitsLift_of_forall_brauer.{u, u + 1}
      _ _ hBr q hq)

end Comparison

/-! ### The vanishing statements with no choice of site or geometric point -/

section Absolute

variable (K : Type u) [Field K]

/-- The ring isomorphism between `K` and the residue field of `Spec K` at a point. -/
def residueFieldSpecRingEquiv (x : Spec (CommRingCat.of K)) :
    K ≃+* ↥((Spec (CommRingCat.of K)).residueField x) :=
  haveI : x.asIdeal.IsPrime := x.isPrime
  (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.trans
    ((Scheme.Spec.residueFieldIso (CommRingCat.of K) x).symm.commRingCatIsoToRingEquiv)

/-- The Brauer group of every finite extension of the residue field of `Spec K` at a point is
trivial as soon as the Brauer group of every finite extension of `K` is. -/
private theorem brauerGroup_eq_one_of_finite_residueField (x : Spec (CommRingCat.of K))
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1) :
    ∀ (L : Type u) [Field L] [Algebra ↥((Spec (CommRingCat.of K)).residueField x) L]
      [Module.Finite ↥((Spec (CommRingCat.of K)).residueField x) L]
      (y : BrauerGroup L), y = 1 := by
  intro L _ _ _ y
  let : Algebra K ↥((Spec (CommRingCat.of K)).residueField x) :=
    (residueFieldSpecRingEquiv K x).toRingHom.toAlgebra
  have : Module.Finite K ↥((Spec (CommRingCat.of K)).residueField x) :=
    Module.Finite.of_surjective (Algebra.linearMap K _)
      (residueFieldSpecRingEquiv K x).surjective
  let : Algebra K L :=
    ((algebraMap ↥((Spec (CommRingCat.of K)).residueField x) L).comp
      (algebraMap K ↥((Spec (CommRingCat.of K)).residueField x))).toAlgebra
  have : IsScalarTower K ↥((Spec (CommRingCat.of K)).residueField x) L :=
    .of_algebraMap_eq' rfl
  have : Module.Finite K L :=
    Module.Finite.trans ↥((Spec (CommRingCat.of K)).residueField x) L
  exact hBr L y

/-- The Brauer group of the residue field of `Spec K` at a point is trivial as soon as the
Brauer group of every finite extension of `K` is. -/
theorem forall_brauerGroup_residueField_eq_one (x : Spec (CommRingCat.of K))
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1) :
    ∀ y : BrauerGroup ↥((Spec (CommRingCat.of K)).residueField x), y = 1 :=
  brauerGroup_eq_one_of_finite_residueField K x hBr _

/-- Hilbert's theorem 90: `H^1_étale(Spec K, 𝐆_m) = 0` for an arbitrary field. -/
theorem subsingleton_sheafH_multiplicativeSheaf_one :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 1) :=
  subsingleton_multiplicativeSheafH_one (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K)

/-- `H^2_étale(Spec K, 𝐆_m) = 0` when the Brauer group of every finite extension of `K` is
trivial. -/
theorem subsingleton_sheafH_multiplicativeSheaf_two
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) 2) :=
  subsingleton_multiplicativeSheafH_two (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K)
    (forall_brauerGroup_residueField_eq_one K _ hBr)

/-- The Brauer group of every finite extension of the residue field of `Spec K` at a point is
trivial as soon as the Brauer group of every finite extension of `K` is. -/
theorem forall_forall_brauerGroup_residueField_eq_one (x : Spec (CommRingCat.of K))
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1) :
    ∀ (L : Type u) [Field L] [Algebra ↥((Spec (CommRingCat.of K)).residueField x) L]
      [Module.Finite ↥((Spec (CommRingCat.of K)).residueField x) L]
      (y : BrauerGroup L), y = 1 :=
  brauerGroup_eq_one_of_finite_residueField K x hBr

/-- `H^q_étale(Spec K, 𝐆_m) = 0` in every degree `q ≥ 1` when the Brauer group of every finite
extension of `K` is trivial. -/
theorem subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q) :=
  subsingleton_multiplicativeSheafH_of_forall_brauer (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K)
    (forall_forall_brauerGroup_residueField_eq_one K _ hBr) q hq

end Absolute

end AlgebraicGeometry

end
