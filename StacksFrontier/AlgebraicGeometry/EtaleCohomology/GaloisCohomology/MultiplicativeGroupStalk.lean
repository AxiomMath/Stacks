module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber

/-!
# The stalk of `𝐆_m` over a field is the multiplicative group of the separable closure

Let `K` be a field and let `sbar` be a geometric point of `Spec K`, with `κ` the residue field at
its image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar` the separable closure of `κ` inside
the algebraically closed field of `sbar`.  The stalk at `sbar` of the multiplicative sheaf
`Stacks.Kummer.multiplicativeSheaf` — restricted along the embedding of the small étale site of
Tag 021B into Mathlib's small étale site — is `(Kˢᵉᵖ)ˣ`, written additively, and germ evaluation
onto it is Galois equivariant.

This is the input that lets the comparison of Tag 03QU part (3)
(`AlgebraicGeometry.smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology`) be evaluated at
`𝐆_m`: before this file nothing in the library related `Stacks.Kummer.multiplicativeSheaf` to the
units of a separable closure.

## Main definitions

* `AlgebraicGeometry.sepClosureFiberEval` and `AlgebraicGeometry.geometricPointFiberEval` —
  evaluating a global function on an object of the small étale site at a lift of the geometric
  point, as a homomorphism of rings into the separable closure.
* `AlgebraicGeometry.multiplicativeSectionEval` — the resulting map on sections of `𝐆_m`.
* `AlgebraicGeometry.multiplicativeStalkToUnits` — germ evaluation on the stalk of `𝐆_m`,
  obtained from the previous one by descent along the colimit defining the stalk.
* `AlgebraicGeometry.sepClosureUnitsSmul` — the Galois action on the units of the separable
  closure, at the coefficient universe of étale cohomology.

## Main results

* `AlgebraicGeometry.multiplicativeStalkToUnits_bijective` and
  `AlgebraicGeometry.multiplicativeStalkIsoUnits` — **the stalk of `𝐆_m` at `sbar` is
  `(Kˢᵉᵖ)ˣ`**, as an isomorphism of abelian groups.  Nothing is assumed of the field.
* `AlgebraicGeometry.multiplicativeSectionEval_galoisFiberAction` — **germ evaluation is Galois
  equivariant**: evaluating at a Galois translate of the lift is evaluating and then acting by
  the automorphism.
* `AlgebraicGeometry.exists_geometricPointFiberEvalUnits_eq_algebraMap` — the spectrum of a
  finite separable subextension of `Kˢᵉᵖ` is a pointed étale neighbourhood of `sbar` on which
  germ evaluation is the inclusion of that subextension.
* `AlgebraicGeometry.exists_refinement_appTop_eq_zero` — a global function vanishing at the lift
  already vanishes on a refinement of the neighbourhood.

## How the comparison is obtained

A lift of `sbar` to an object `U` of the small étale site factors through the spectrum of the
separable closure (`AlgebraicGeometry.geometricPointFiberSepClosureEquiv`), so a global function
on `U` can be evaluated there; this is compatible with restriction along a morphism of the site,
hence descends to the colimit defining the stalk.

Surjectivity of the resulting map is that an element of `Kˢᵉᵖ` generates a finite separable
subextension `E` of `κ`; `Spec E` is an object of the small étale site
(`AlgebraicGeometry.etale_specMap_algebraMap_of_finite_separable` together with the size bound of
the ambient big étale site) carrying the tautological lift, and there the element is an
invertible global function.  Injectivity is the other direction of the same structure theory: a
lift factors through a finite separable piece of `U`
(`AlgebraicGeometry.exists_finite_separable_factorization`), that piece is a refinement inside
the site, and its coordinate ring embeds into `Kˢᵉᵖ`, so a function trivial at the lift is
already trivial on the refinement.  Both halves are run through Mathlib's
`CategoryTheory.GrothendieckTopology.Point` colimit API: germs are jointly surjective onto the
stalk, and two germs agree exactly when they agree on a common refinement.

Equivariance is read off the definition of the Galois action on the lifts
(`AlgebraicGeometry.galoisFiberAction`): the action translates a lift by precomposition with the
spectrum of the automorphism, and global sections of a spectrum return the ring map
(`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`).

## Universes

`Stacks.Kummer.multiplicativeSheaf` of a scheme in `Scheme.{u}` has coefficients in
`AddCommGrpCat.{max (u + 1) v}`; at `v = u` that is `AddCommGrpCat.{u + 1}`, the coefficient
universe in which Tag 03QU part (3) is stated, the objects of the small étale site of `Spec K`
for `K : Type u` living in `Type (u + 1)`.  The sections of the sheaf are therefore `ULift.{u + 1}`
of `Additive (Γ(U, 𝒪)ˣ)`, and so is the stalk: the comparison here lands in `AddCommGrpCat.{u + 1}`
and its Galois module would live in `ContinuousGModule.{u, u + 1}`, **not** in the
`ContinuousGModule.{u, u}` where `Stacks.GaloisCohomology.unitsContinuousGModule` lives.

## What is still missing above this file

Two steps separate this file from an evaluation of Tag 03QU part (3) at `𝐆_m`.

* The comparison here is an isomorphism of abelian groups together with the germwise
  equivariance `AlgebraicGeometry.multiplicativeSectionEval_galoisFiberAction`.  Packaging those
  two into an isomorphism in `ContinuousGModule.{u, u + 1}` needs the Galois action on the
  abelian stalk to be identified with germ translation, i.e. the action transported along
  `AlgebraicGeometry.abelianEtaleStalkEquivalenceIso` from the module of Tag 04JQ.  The inputs
  are `AlgebraicGeometry.etaleGaloisModule_rho_apply`,
  `AlgebraicGeometry.etaleGaloisModuleAddEquivStalk_germ` and
  `AlgebraicGeometry.etaleStalkSmul_germ`; what defeats a direct proof is the cost of the
  conversion between the underlying type of the module of Tag 04JQ and the set-valued stalk,
  which the elaborator does not complete inside its heartbeat budget.
* `Stacks.GaloisCohomology.unitsContinuousGModule` is built on `Additive Ωˣ : Type u`, so it is
  an object of `ContinuousGModule.{u, u}`, while the comparison consumes
  `ContinuousGModule.{u, u + 1}`.  Naming it in the identification therefore needs a
  universe-raising functor on `ContinuousGModule`, which the library does not have.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- `𝐆_m` on the small étale site of Tag 021B of `Spec K`: the restriction along the embedding
of that site into Mathlib's of the multiplicative sheaf of the Kummer theory. -/
abbrev multiplicativeSheafRestriction :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} :=
  (smallEtaleSheafRestriction B K hK).obj
    (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K)))

/-- The separable closure of the residue field at the image of the geometric point, written
additively as the abelian group in which the stalk of `𝐆_m` is computed. -/
abbrev sepClosureUnits : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (ULift.{u + 1} (Additive (↥(GeometricPoint.separableClosure sbar))ˣ))

/-- Evaluating a global function on an object of the small étale site at a lift of the
separable-closure point of the geometric point. -/
def sepClosureFiberEval (U : SmallEtale B (Spec (.of K)) hK)
    (q : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) ⟶
      CommRingCat.of ↥(GeometricPoint.separableClosure sbar) :=
  q.1.appTop ≫ (Scheme.ΓSpecIso _).hom

/-- Evaluation at a lift of the separable-closure point is compatible with restriction along a
morphism of the small étale site. -/
theorem sepClosureFiberEval_map {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (q : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop ≫
        sepClosureFiberEval B K hK sbar U q =
      sepClosureFiberEval B K hK sbar V
        ((sepClosureFiber B (Spec (.of K)) hK sbar).map f q) := by
  show ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop ≫
      (q.1.appTop ≫ (Scheme.ΓSpecIso _).hom) =
    (q.1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop ≫ (Scheme.ΓSpecIso _).hom
  rw [Scheme.Hom.comp_appTop, Category.assoc]

/-- Evaluating a global function at a lift of the geometric point: the lift factors through
the spectrum of the separable closure, where the function is evaluated. -/
def geometricPointFiberEval (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) ⟶
      CommRingCat.of ↥(GeometricPoint.separableClosure sbar) :=
  sepClosureFiberEval B K hK sbar U
    ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p)

/-- Evaluation at a lift of the geometric point is compatible with restriction along a morphism
of the small étale site. -/
theorem geometricPointFiberEval_map {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop ≫
        geometricPointFiberEval B K hK sbar U p =
      geometricPointFiberEval B K hK sbar V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) := by
  have key : (geometricPointFiberSepClosureEquiv B K hK sbar V).symm
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) =
      (sepClosureFiber B (Spec (.of K)) hK sbar).map f
        ((geometricPointFiberSepClosureEquiv B K hK sbar U).symm p) :=
    (geometricPointFiberSepClosureEquiv B K hK sbar V).symm_apply_eq.mpr
      (by rw [← geometricPointFiberSepClosureEquiv_map, Equiv.apply_symm_apply])
  rw [geometricPointFiberEval, geometricPointFiberEval, key,
    ← sepClosureFiberEval_map B K hK sbar f]

/-- Germ evaluation at the lift of the geometric point coming from a lift of the
separable-closure point is germ evaluation at the latter. -/
theorem geometricPointFiberEval_sepClosureEquiv (U : SmallEtale B (Spec (.of K)) hK)
    (q : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    geometricPointFiberEval B K hK sbar U
        (geometricPointFiberSepClosureEquiv B K hK sbar U q) =
      sepClosureFiberEval B K hK sbar U q := by
  rw [geometricPointFiberEval, Equiv.symm_apply_apply]

/-- Evaluation at a lift of the geometric point, read on units of global functions. -/
def geometricPointFiberEvalUnits (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ →*
      (↥(GeometricPoint.separableClosure sbar))ˣ :=
  Units.map (geometricPointFiberEval B K hK sbar U p).hom.toMonoidHom

/-- A multiplicative map out of the invertible global functions on an object of the small étale
site, read additively and raised to the coefficient universe of étale cohomology. -/
def multiplicativeSectionHom (U : SmallEtale B (Spec (.of K)) hK)
    (φ : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ →*
      (↥(GeometricPoint.separableClosure sbar))ˣ) :
    ULift.{u + 1} (Additive (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ) →+
      ULift.{u + 1} (Additive (↥(GeometricPoint.separableClosure sbar))ˣ) :=
  ((AddEquiv.ulift).symm.toAddMonoidHom.comp (MonoidHom.toAdditive φ)).comp
    (AddEquiv.ulift).toAddMonoidHom

/-- A multiplicative endomorphism of the units of the separable closure, read additively and
raised to the coefficient universe of étale cohomology. -/
def sepClosureUnitsHom (φ : (↥(GeometricPoint.separableClosure sbar))ˣ →*
      (↥(GeometricPoint.separableClosure sbar))ˣ) :
    ULift.{u + 1} (Additive (↥(GeometricPoint.separableClosure sbar))ˣ) →+
      ULift.{u + 1} (Additive (↥(GeometricPoint.separableClosure sbar))ˣ) :=
  ((AddEquiv.ulift).symm.toAddMonoidHom.comp (MonoidHom.toAdditive φ)).comp
    (AddEquiv.ulift).toAddMonoidHom

/-- **The germ-evaluation map on sections of `𝐆_m`**: an invertible global function on a pointed
étale neighbourhood of the geometric point is evaluated at the lift, giving an element of the
separable closure. -/
def multiplicativeSectionEval (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (multiplicativeSheafRestriction B K hK).obj.obj (op U) ⟶ sepClosureUnits K sbar :=
  AddCommGrpCat.ofHom
    (multiplicativeSectionHom B K hK sbar U (geometricPointFiberEvalUnits B K hK sbar U p))

/-- The germ-evaluation map on sections, computed on an invertible global function. -/
theorem multiplicativeSectionEval_apply (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (x : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ) :
    ConcreteCategory.hom (multiplicativeSectionEval B K hK sbar U p)
        (ULift.up (Additive.ofMul x)) =
      ULift.up (Additive.ofMul (geometricPointFiberEvalUnits B K hK sbar U p x)) := rfl

/-- Germ evaluation on units is compatible with restriction along a morphism of the small étale
site. -/
theorem geometricPointFiberEvalUnits_map {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    geometricPointFiberEvalUnits B K hK sbar V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) =
      (geometricPointFiberEvalUnits B K hK sbar U p).comp
        (Units.map ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom.toMonoidHom) := by
  rw [geometricPointFiberEvalUnits, geometricPointFiberEvalUnits,
    ← geometricPointFiberEval_map B K hK sbar f p]
  exact Units.map_comp _ _

/-- Germ evaluation is compatible with restriction along a morphism of the small étale site,
which is what lets it descend to the stalk. -/
theorem multiplicativeSectionEval_naturality {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (multiplicativeSheafRestriction B K hK).obj.map f.op ≫
        multiplicativeSectionEval B K hK sbar U p =
      multiplicativeSectionEval B K hK sbar V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) :=
  by
  rw [multiplicativeSectionEval, multiplicativeSectionEval, geometricPointFiberEvalUnits_map]
  rfl

/-- **The stalk of `𝐆_m` at a geometric point of the spectrum of a field, mapped to the units of
the separable closure.**  The germ of an invertible global function on a pointed étale
neighbourhood is sent to the value of that function at the lift. -/
def multiplicativeStalkToUnits :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (multiplicativeSheafRestriction B K hK) ⟶ sepClosureUnits K sbar :=
  (fieldSitePoint B K hK sbar).presheafFiberDesc
    (P := (multiplicativeSheafRestriction B K hK).obj)
    (fun U p => multiplicativeSectionEval B K hK sbar U p)
    (fun {_ _} f p => multiplicativeSectionEval_naturality B K hK sbar f p)

/-- The comparison map out of the stalk, precomposed with the germ map over a pointed étale
neighbourhood, is germ evaluation there. -/
theorem toPresheafFiber_comp_multiplicativeStalkToUnits (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (fieldSitePoint B K hK sbar).toPresheafFiber U p
          (multiplicativeSheafRestriction B K hK).obj ≫
        multiplicativeStalkToUnits B K hK sbar =
      multiplicativeSectionEval B K hK sbar U p :=
  (fieldSitePoint B K hK sbar).toPresheafFiber_presheafFiberDesc _ _ U p

/-! ### Germ evaluation is Galois equivariant -/

/-- **The Galois action on the units of the separable closure**, written additively and raised to
the coefficient universe of étale cohomology. -/
def sepClosureUnitsSmul (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    sepClosureUnits K sbar ⟶ sepClosureUnits K sbar :=
  AddCommGrpCat.ofHom
    (sepClosureUnitsHom K sbar (Units.map σ.toAlgHom.toRingHom.toMonoidHom))

/-- **Germ evaluation at a Galois translate of a lift of the separable-closure point is germ
evaluation followed by the Galois automorphism.**  The action translates a lift by precomposition
with the spectrum of the automorphism, and global sections of that spectrum return the
automorphism. -/
theorem sepClosureFiberEval_sepClosureFiberSmul (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : SmallEtale B (Spec (.of K)) hK)
    (q : (sepClosureFiber B (Spec (.of K)) hK sbar).obj U) :
    sepClosureFiberEval B K hK sbar U
        (sepClosureFiberSmul B (Spec (.of K)) hK sbar σ q) =
      sepClosureFiberEval B K hK sbar U q ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom := by
  show (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ q.1).appTop ≫
      (Scheme.ΓSpecIso _).hom =
    (q.1.appTop ≫ (Scheme.ΓSpecIso _).hom) ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom
  rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

/-- Germ evaluation at a Galois translate of a lift of the geometric point is germ evaluation
followed by the Galois automorphism. -/
theorem geometricPointFiberEval_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    geometricPointFiberEval B K hK sbar U (galoisFiberAction B K hK sbar σ p) =
      geometricPointFiberEval B K hK sbar U p ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom := by
  rw [galoisFiberAction, geometricPointFiberEval_sepClosureEquiv,
    sepClosureFiberEval_sepClosureFiberSmul, geometricPointFiberEval]

/-- Germ evaluation on units at a Galois translate of a lift is germ evaluation followed by the
Galois action on the units of the separable closure. -/
theorem geometricPointFiberEvalUnits_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    geometricPointFiberEvalUnits B K hK sbar U (galoisFiberAction B K hK sbar σ p) =
      (Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp
        (geometricPointFiberEvalUnits B K hK sbar U p) := by
  rw [geometricPointFiberEvalUnits, geometricPointFiberEvalUnits,
    geometricPointFiberEval_galoisFiberAction]
  exact Units.map_comp _ _

/-- **Germ evaluation on sections of `𝐆_m` is Galois equivariant**: evaluating at a Galois
translate of the lift is evaluating and then acting by the automorphism.  This is the
equivariance that makes the comparison of the stalk with the units of the separable closure a map
of Galois modules. -/
theorem multiplicativeSectionEval_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    multiplicativeSectionEval B K hK sbar U (galoisFiberAction B K hK sbar σ p) =
      multiplicativeSectionEval B K hK sbar U p ≫ sepClosureUnitsSmul K sbar σ :=
  by
  rw [multiplicativeSectionEval, multiplicativeSectionEval,
    geometricPointFiberEvalUnits_galoisFiberAction]
  rfl

/-! ### Germ evaluation is surjective and locally injective -/

/-- **Every element of a Galois extension lies in a finite separable subextension**, namely the
one it generates. -/
theorem exists_finiteDimensional_isSeparable_mem {κ L : Type u} [Field κ] [Field L]
    [Algebra κ L] [IsGalois κ L] (a : L) :
    ∃ E : IntermediateField κ L,
      FiniteDimensional κ ↥E ∧ Algebra.IsSeparable κ ↥E ∧ a ∈ E :=
  ⟨IntermediateField.adjoin κ {a},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a),
    Algebra.isSeparable_tower_bot_of_isSeparable κ _ L,
    IntermediateField.mem_adjoin_simple_self κ a⟩

/-- **The spectrum of a finite separable subextension of the separable closure is a pointed étale
neighbourhood of the geometric point**, and germ evaluation there is the inclusion of the
subextension into the separable closure.  Consequently an invertible element of such a
subextension is the value at the lift of an invertible global function. -/
theorem exists_geometricPointFiberEvalUnits_eq_algebraMap
    (E : IntermediateField ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥(GeometricPoint.separableClosure sbar))
    (hfd : FiniteDimensional
      ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)
    (hsep : Algebra.IsSeparable
      ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E) (a : (↥E)ˣ) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V)
      (y : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ),
      geometricPointFiberEvalUnits B K hK sbar V p y =
        Units.map (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)).toMonoidHom a := by
  have := hfd
  have := hsep
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E))) :=
    etale_specMap_algebraMap_of_finite_separable _ _
  have hVst : Etale (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
      (residuePointIso K sbar).hom) := inferInstance
  have hEcon : B.Contains (Spec (.of ↥E)) :=
    (Scheme.size_le_of_locallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
      (residuePointIso K sbar).hom)).trans_lt hK
  let V : SmallEtale B (Spec (.of K)) hK :=
    Stacks.EtaleCohomology.mkObj B hK (Spec (.of ↥E))
      (Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E)) ≫
        (residuePointIso K sbar).hom) hEcon hVst
  have htower : CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E) ≫
      CommRingCat.ofHom (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)) =
      CommRingCat.ofHom (algebraMap
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar)) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq
      ((Spec (CommRingCat.of K)).residueField (sbar.hom default)) ↥E
      ↥(GeometricPoint.separableClosure sbar)).symm
  have hq2 : Spec.map (CommRingCat.ofHom (algebraMap ↥E
        ↥(GeometricPoint.separableClosure sbar))) ≫ B.inclusion.map V.obj.hom =
      GeometricPoint.sepClosureOver sbar :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun w ↦ w ≫ (residuePointIso K sbar).hom)
        ((Spec.map_comp _ _).symm.trans (congrArg Spec.map htower)))
  let q' : (sepClosureFiber B (Spec (.of K)) hK sbar).obj V :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap ↥E
      ↥(GeometricPoint.separableClosure sbar))), hq2⟩
  have hsep' : sepClosureFiberEval B K hK sbar V q' =
      (Scheme.ΓSpecIso (CommRingCat.of ↥E)).hom ≫
        CommRingCat.ofHom (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)) :=
    Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)))
  have hkey : (Scheme.ΓSpecIso (CommRingCat.of ↥E)).inv ≫
      geometricPointFiberEval B K hK sbar V
        (geometricPointFiberSepClosureEquiv B K hK sbar V q') =
      CommRingCat.ofHom (algebraMap ↥E ↥(GeometricPoint.separableClosure sbar)) := by
    rw [geometricPointFiberEval_sepClosureEquiv, hsep', Iso.inv_hom_id_assoc]
  exact ⟨V, geometricPointFiberSepClosureEquiv B K hK sbar V q',
    Units.map (Scheme.ΓSpecIso (CommRingCat.of ↥E)).inv.hom.toMonoidHom a,
    Units.ext (congrArg (fun r : CommRingCat.of ↥E ⟶
      CommRingCat.of ↥(GeometricPoint.separableClosure sbar) => r.hom (a : ↥E)) hkey)⟩

/-- **Every element of the separable closure is the value of an invertible global function on a
pointed étale neighbourhood.**  The element generates a finite separable subextension, whose
spectrum is an object of the small étale site carrying the tautological lift of the geometric
point, and there the element itself is an invertible global function. -/
theorem exists_geometricPointFiberEvalUnits_eq
    (x : (↥(GeometricPoint.separableClosure sbar))ˣ) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V)
      (y : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ),
      geometricPointFiberEvalUnits B K hK sbar V p y = x := by
  obtain ⟨E, hfd, hsep, hxE⟩ :=
    exists_finiteDimensional_isSeparable_mem
      (κ := ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)))
      (L := ↥(GeometricPoint.separableClosure sbar))
      (x : ↥(GeometricPoint.separableClosure sbar))
  have hxne : (⟨(x : ↥(GeometricPoint.separableClosure sbar)), hxE⟩ : ↥E) ≠ 0 :=
    fun h ↦ x.ne_zero (congrArg Subtype.val h)
  obtain ⟨V, p, y, hy⟩ := exists_geometricPointFiberEvalUnits_eq_algebraMap B K hK sbar E hfd hsep
    (Units.mk0 _ hxne)
  exact ⟨V, p, y, hy.trans (Units.ext rfl)⟩

/-- **An invertible global function with trivial value at the lift is trivial on a refinement.**
The lift factors through the spectrum of a finite separable extension, which is an object of the
small étale site refining the neighbourhood, and there the function is already trivial since the
extension embeds into the separable closure. -/
theorem exists_refinement_appTop_eq_zero (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (y : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))
    (hy : (geometricPointFiberEval B K hK sbar U p).hom y = 0) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK) (f : V ⟶ U)
      (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V),
      (geometricPointFiber B (Spec (.of K)) hK sbar).map f q = p ∧
        ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom y = 0 := by
  classical
  set yq := (geometricPointFiberSepClosureEquiv B K hK sbar U).symm p with hyq
  have hpy : geometricPointFiberSepClosureEquiv B K hK sbar U yq = p :=
    Equiv.apply_symm_apply _ p
  obtain ⟨E, hEf, hEa, hEfin, hEsep, j, hj, hover, g, hgy⟩ :=
    exists_finite_separable_factorization B K hK sbar U yq
  let _ := hEf
  let _ := hEa
  let _ := hEfin
  let _ := hEsep
  let _ := hj
  have hEcontains : B.Contains (Spec (.of E)) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map U.obj.hom)).trans_lt hK
  let V : SmallEtale B (Spec (.of K)) hK :=
    Stacks.EtaleCohomology.mkObj B hK (Spec (.of E)) (j ≫ B.inclusion.map U.obj.hom)
      hEcontains inferInstance
  have hVhom : B.inclusion.map V.obj.hom = j ≫ B.inclusion.map U.obj.hom := rfl
  let f : V ⟶ U := Stacks.EtaleCohomology.mkHom B hK (V := V) (W := U) j rfl
  have hfj : (SmallEtale.toScheme B (Spec (.of K)) hK).map f = j := rfl
  have hq2 : g ≫ B.inclusion.map V.obj.hom = GeometricPoint.sepClosureOver sbar := by
    rw [hVhom, ← Category.assoc, ← hgy]
    exact yq.2
  let q' : (sepClosureFiber B (Spec (.of K)) hK sbar).obj V := ⟨g, hq2⟩
  set ψ := Spec.preimage g with hψ
  have hgψ : Spec.map ψ = g := Spec.map_preimage g
  have hnat : g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of ↥(GeometricPoint.separableClosure sbar))).hom =
      (Scheme.ΓSpecIso (CommRingCat.of E)).hom ≫ ψ := by
    rw [← hgψ]
    exact Scheme.ΓSpecIso_naturality ψ
  have hfactor : geometricPointFiberEval B K hK sbar U p =
      j.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom ≫ ψ := by
    rw [geometricPointFiberEval, ← hyq, sepClosureFiberEval, hgy, Scheme.Hom.comp_appTop,
      Category.assoc, hnat]
  refine ⟨V, f, geometricPointFiberSepClosureEquiv B K hK sbar V q', ?_, ?_⟩
  · rw [geometricPointFiberSepClosureEquiv_map, ← hpy]
    refine congrArg _ (Subtype.ext ?_)
    show g ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map f = yq.1
    rw [hfj, hgy]
  · have h1 : ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
        (j.appTop.hom y)) = 0 := by
      rw [← hy, hfactor]
      rfl
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom (j.appTop.hom y) = 0 :=
      (map_eq_zero_iff _ ψ.hom.injective).mp h1
    have h3 : Function.Injective
        (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of E)).hom) :=
      ((ConcreteCategory.isIso_iff_bijective
        (Scheme.ΓSpecIso (CommRingCat.of E)).hom).mp inferInstance).1
    rw [hfj]
    exact h3 (h2.trans (map_zero _).symm)

/-! ### The stalk of `𝐆_m` is the units of the separable closure -/

/-- The forgetful functor from abelian groups in the universe of the objects of the small étale
site preserves the filtered colimits indexed by the site, which is what makes germs jointly
surjective onto the stalk and lets two germs be compared on a common refinement. -/
public theorem preservesFilteredColimitsOfSize_forget_addCommGrpCat :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (CategoryTheory.forget AddCommGrpCat.{u + 1})

attribute [local instance] preservesFilteredColimitsOfSize_forget_addCommGrpCat

/-- **The comparison of the stalk of `𝐆_m` with the units of the separable closure is
bijective.**  Surjectivity is that every element of the separable closure generates a finite
separable subextension, whose spectrum is a pointed étale neighbourhood on which the element is
an invertible global function; injectivity is that a lift of the geometric point factors through
the spectrum of a finite separable extension, which embeds into the separable closure, so a
function trivial at the lift is already trivial on that refinement. -/
theorem multiplicativeStalkToUnits_bijective :
    Function.Bijective (ConcreteCategory.hom (multiplicativeStalkToUnits B K hK sbar)) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨U, p, z₁, z₂, rfl, rfl⟩ :=
      (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective₂
        (P := (multiplicativeSheafRestriction B K hK).obj) a b
    have hab' : ConcreteCategory.hom (multiplicativeSectionEval B K hK sbar U p) z₁ =
        ConcreteCategory.hom (multiplicativeSectionEval B K hK sbar U p) z₂ :=
      (ConcreteCategory.congr_hom
            (toPresheafFiber_comp_multiplicativeStalkToUnits B K hK sbar U p) z₁).symm.trans
        (hab.trans (ConcreteCategory.congr_hom
          (toPresheafFiber_comp_multiplicativeStalkToUnits B K hK sbar U p) z₂))
    set x₁ : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ :=
      Additive.toMul (ULift.down z₁) with hx₁
    set x₂ : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ :=
      Additive.toMul (ULift.down z₂) with hx₂
    have hval : (geometricPointFiberEval B K hK sbar U p).hom x₁.val =
        (geometricPointFiberEval B K hK sbar U p).hom x₂.val :=
      congrArg (fun w : (↥(GeometricPoint.separableClosure sbar))ˣ => w.val)
        (congrArg (fun w => Additive.toMul (ULift.down w)) hab')
    have hw : (geometricPointFiberEval B K hK sbar U p).hom (x₁.val - x₂.val) = 0 := by
      rw [map_sub, hval, sub_self]
    obtain ⟨V, f, q, hq, hz⟩ := exists_refinement_appTop_eq_zero B K hK sbar U p _ hw
    rw [map_sub, sub_eq_zero] at hz
    refine ((fieldSitePoint B K hK sbar).toPresheafFiber_eq_iff' U p z₁ z₂).mpr
      ⟨V, f, q, hq, ?_⟩
    exact congrArg (fun w : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ =>
      ULift.up (Additive.ofMul w)) (Units.ext hz)
  · obtain ⟨V, p, y, hy⟩ := exists_geometricPointFiberEvalUnits_eq B K hK sbar
      (Additive.toMul (ULift.down t))
    refine ⟨(fieldSitePoint B K hK sbar).toPresheafFiber V p
      (multiplicativeSheafRestriction B K hK).obj (ULift.up (Additive.ofMul y)), ?_⟩
    exact (ConcreteCategory.congr_hom
          (toPresheafFiber_comp_multiplicativeStalkToUnits B K hK sbar V p)
          (ULift.up (Additive.ofMul y))).trans
      (congrArg (fun w : (↥(GeometricPoint.separableClosure sbar))ˣ =>
        (ULift.up (Additive.ofMul w) : ToType (sepClosureUnits K sbar))) hy)

/-- The comparison map `multiplicativeStalkToUnits` from the stalk of `𝐆_m` at a geometric point
of the spectrum of a field to the units of the separable closure is an isomorphism. -/
instance isIso_multiplicativeStalkToUnits :
    IsIso (multiplicativeStalkToUnits B K hK sbar) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (multiplicativeStalkToUnits_bijective B K hK sbar)

/-- **The stalk of `𝐆_m` at a geometric point of the spectrum of a field is the multiplicative
group of the separable closure**, written additively and raised to the coefficient universe of
étale cohomology. -/
def multiplicativeStalkIsoUnits :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (multiplicativeSheafRestriction B K hK) ≅ sepClosureUnits K sbar :=
  asIso (multiplicativeStalkToUnits B K hK sbar)

end AlgebraicGeometry

end
