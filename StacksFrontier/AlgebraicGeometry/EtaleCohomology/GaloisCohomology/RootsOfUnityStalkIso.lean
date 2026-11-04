module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.RootsOfUnityStalk

/-!
# The stalk of `μ_n` over a field is the `n`-th roots of unity of the separable closure

Let `K` be a field and let `sbar` be a geometric point of `Spec K`, with `κ` the residue field at
its image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar` the separable closure of `κ` inside
the algebraically closed field of `sbar`.  The stalk at `sbar` of `μ_n`
(`Stacks.Kummer.rootsOfUnitySheaf`), restricted along the embedding of the small étale site of
Tag 021B into Mathlib's small étale site, is `μ_n(Kˢᵉᵖ)` written additively, and germ evaluation
onto it is Galois equivariant.

This is the `n`-torsion analogue of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk` and of
`…GaloisCohomology.AdditiveGroupStalk`, and it is the input that lets the comparison of Tag 03QU
part (3) be evaluated at `μ_n`, which is clause (4) of [Stacks, Tag 03QV].

## Main definitions

* `AlgebraicGeometry.rootsOfUnityStalkToRootsOfUnity` — germ evaluation on the stalk of `μ_n`,
  obtained from `AlgebraicGeometry.rootsOfUnitySectionEval` by descent along the colimit defining
  the stalk.
* `AlgebraicGeometry.sepClosureRootsOfUnitySmul` — the Galois action on `μ_n(Kˢᵉᵖ)`, at the
  coefficient universe of étale cohomology.

## Main results

* `AlgebraicGeometry.rootsOfUnityStalkToRootsOfUnity_bijective` and
  `AlgebraicGeometry.rootsOfUnityStalkIsoRootsOfUnity` — **the stalk of `μ_n` at `sbar` is
  `μ_n(Kˢᵉᵖ)`**, as an isomorphism of abelian groups.  Nothing is assumed of the field and
  nothing is assumed of `n`.
* `AlgebraicGeometry.rootsOfUnitySectionEval_galoisFiberAction` — **germ evaluation is Galois
  equivariant**: evaluating at a Galois translate of the lift is evaluating and then acting by the
  automorphism.
* `AlgebraicGeometry.rootsOfUnitySectionEval_naturality` — germ evaluation commutes with
  restriction along a morphism of the site, which is what lets it descend to the stalk.
* `AlgebraicGeometry.exists_pow_eq_one_geometricPointFiberEvalUnits_eq` — every `n`-th root of
  unity of `Kˢᵉᵖ` is the value at the lift of an invertible global function whose `n`-th power is
  already one on the neighbourhood.

## How the comparison is obtained

Everything ring-theoretic is reused verbatim from the multiplicative file: germ evaluation on
invertible global functions is `AlgebraicGeometry.geometricPointFiberEvalUnits`, it is compatible
with restriction (`AlgebraicGeometry.geometricPointFiberEvalUnits_map`) and Galois equivariant
(`AlgebraicGeometry.geometricPointFiberEvalUnits_galoisFiberAction`), and
`AlgebraicGeometry.coe_restrictRootsOfUnity_sectionRoot` carries each of those statements from
`𝐆_m` to `μ_n`.

Only the two halves of bijectivity need an argument of their own, and both go through the
objectwise description of `μ_n`: a section of it over an object of Mathlib's small étale site is
exactly an invertible global function with `n`-th power one
(`Stacks.Kummer.rootsOfUnitySection_bijective`).

* Surjectivity needs an `n`-th root of unity of `Kˢᵉᵖ` to be the value of an invertible global
  function that is *itself* an `n`-th root of unity, not merely one whose value is.  The
  multiplicative statement `AlgebraicGeometry.exists_geometricPointFiberEvalUnits_eq` produces a
  function `y` with the right value, and `yⁿ - 1` then vanishes at the lift, hence already on a
  refinement by `AlgebraicGeometry.exists_refinement_appTop_eq_zero`; the restriction of `y` to
  that refinement is the function wanted.  This is
  `AlgebraicGeometry.exists_pow_eq_one_geometricPointFiberEvalUnits_eq`.
* Injectivity is the multiplicative argument applied to the two underlying invertible global
  functions: their difference vanishes at the lift, hence on a refinement, and two sections of
  `μ_n` with the same underlying function are equal.

## Universes

`Stacks.Kummer.rootsOfUnitySheaf` of a scheme in `Scheme.{u}` is taken here with coefficients in
`AddCommGrpCat.{u + 1}`, the coefficient universe in which Tag 03QU part (3) is stated, so the
sections of the sheaf — and hence the stalk — are `ULift.{u + 1}` of `Additive μ_n(Γ(U, 𝒪))`.
The comparison therefore lands in `AlgebraicGeometry.sepClosureRootsOfUnity`, which is the
carrier of `Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift` at the raise `u + 1`;
that alignment is what the sibling file
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.RootsOfUnityGaloisModuleIso`
exploits to name the Galois module.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example whose
  clause (4) this file is the stalk computation for.
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): the comparison this
  stalk computation feeds.
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the stalk equivalence.
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence,
  which presents `μ_n` as the kernel of the `n`-th power map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (n : ℕ)

/-! ### Reading germ evaluation on `μ_n` through the underlying invertible global function -/

/-- Two elements of `μ_n(Kˢᵉᵖ)`, at the coefficient universe of étale cohomology, are equal as
soon as the underlying elements of the separable closure are. -/
theorem sepClosureRootsOfUnity_ext {a b : ToType (sepClosureRootsOfUnity K sbar n)}
    (h : ((Additive.toMul (ULift.down a) :
          ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
        (↥(GeometricPoint.separableClosure sbar))ˣ) =
      ((Additive.toMul (ULift.down b) :
          ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
        (↥(GeometricPoint.separableClosure sbar))ˣ)) :
    a = b :=
  congrArg ULift.up (congrArg Additive.ofMul (Subtype.ext h))

/-- Germ evaluation on a section of `μ_n`, read as an invertible element of the separable
closure, is germ evaluation on `𝐆_m` of the invertible global function underlying the
section. -/
theorem coe_rootsOfUnitySectionEval_apply (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    ((Additive.toMul (ULift.down
            (ConcreteCategory.hom (rootsOfUnitySectionEval B K hK sbar n U p) s)) :
          ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
        (↥(GeometricPoint.separableClosure sbar))ˣ) =
      geometricPointFiberEvalUnits B K hK sbar U p (rootsOfUnitySectionUnit B K hK n U s) :=
  coe_restrictRootsOfUnity_sectionRoot B K hK sbar n U p s

/-- The invertible global function underlying a section of `μ_n` is the `n`-th root of unity that
`Stacks.Kummer.rootsOfUnitySection` attaches to it: sections of the restricted sheaf over an
object of the site of Tag 021B are the sections of `μ_n` over its image in Mathlib's small étale
site. -/
theorem rootsOfUnitySectionUnit_eq_rootsOfUnitySection (U : SmallEtale B (Spec (.of K)) hK)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    rootsOfUnitySectionUnit B K hK n U s =
      (Stacks.Kummer.rootsOfUnitySection.{u, u + 1} (Spec (.of K)) n
        (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U)) s).1 :=
  rfl

/-- **Two sections of `μ_n` with the same underlying invertible global function are equal.**
Sections of `μ_n` over an object of the small étale site are exactly the `n`-th roots of unity in
the global functions there. -/
theorem rootsOfUnitySection_injective (U : SmallEtale B (Spec (.of K)) hK)
    {s s' : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))}
    (h : rootsOfUnitySectionUnit B K hK n U s = rootsOfUnitySectionUnit B K hK n U s') :
    s = s' :=
  (Stacks.Kummer.rootsOfUnitySection_bijective.{u, u + 1} (Spec (.of K)) n
    (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U))).1 (Subtype.ext h)

/-- **Every `n`-th root of unity in the global functions on an object of the small étale site is
the invertible global function underlying a section of `μ_n`.** -/
theorem exists_rootsOfUnitySectionUnit_eq (U : SmallEtale B (Spec (.of K)) hK)
    (y : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ) (hy : y ^ n = 1) :
    ∃ s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U)),
      rootsOfUnitySectionUnit B K hK n U s = y := by
  obtain ⟨s, hs⟩ := (Stacks.Kummer.rootsOfUnitySection_bijective.{u, u + 1} (Spec (.of K)) n
    (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U))).2 ⟨y, hy⟩
  exact ⟨s, congrArg Subtype.val hs⟩

/-- Restricting a section of `μ_n` along a morphism of the small étale site pulls the underlying
invertible global function back. -/
theorem rootsOfUnitySectionUnit_map {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op V))) :
    rootsOfUnitySectionUnit B K hK n U
        ((rootsOfUnitySheafRestriction B K hK n).obj.map f.op s) =
      Units.map ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom.toMonoidHom
        (rootsOfUnitySectionUnit B K hK n V s) :=
  Stacks.Kummer.rootsOfUnitySection_naturality.{u, u + 1} (Spec (.of K)) n
    ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).map f) s

/-- **Germ evaluation on sections of `μ_n` is compatible with restriction along a morphism of the
small étale site**, which is what lets it descend to the stalk. -/
theorem rootsOfUnitySectionEval_naturality {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (rootsOfUnitySheafRestriction B K hK n).obj.map f.op ≫
        rootsOfUnitySectionEval B K hK sbar n U p =
      rootsOfUnitySectionEval B K hK sbar n V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine sepClosureRootsOfUnity_ext K sbar n ?_
  have hmid : geometricPointFiberEvalUnits B K hK sbar U p
        (rootsOfUnitySectionUnit B K hK n U
          ((rootsOfUnitySheafRestriction B K hK n).obj.map f.op s)) =
      geometricPointFiberEvalUnits B K hK sbar V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p)
        (rootsOfUnitySectionUnit B K hK n V s) := by
    rw [rootsOfUnitySectionUnit_map, geometricPointFiberEvalUnits_map]
    rfl
  exact (coe_rootsOfUnitySectionEval_apply B K hK sbar n U p _).trans
    (hmid.trans (coe_rootsOfUnitySectionEval_apply B K hK sbar n V _ s).symm)

/-! ### The comparison of the stalk with `μ_n(Kˢᵉᵖ)` -/

/-- **The stalk of `μ_n` at a geometric point of the spectrum of a field, mapped to the `n`-th
roots of unity of the separable closure.**  The germ of a section of `μ_n` on a pointed étale
neighbourhood is sent to the value at the lift of the underlying invertible global function. -/
def rootsOfUnityStalkToRootsOfUnity :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (rootsOfUnitySheafRestriction B K hK n) ⟶ sepClosureRootsOfUnity K sbar n :=
  (fieldSitePoint B K hK sbar).presheafFiberDesc
    (P := (rootsOfUnitySheafRestriction B K hK n).obj)
    (fun U p => rootsOfUnitySectionEval B K hK sbar n U p)
    (fun {_ _} f p => rootsOfUnitySectionEval_naturality B K hK sbar n f p)

/-- The comparison map out of the stalk, precomposed with the germ map over a pointed étale
neighbourhood, is germ evaluation there. -/
theorem toPresheafFiber_comp_rootsOfUnityStalkToRootsOfUnity
    (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (fieldSitePoint B K hK sbar).toPresheafFiber U p
          (rootsOfUnitySheafRestriction B K hK n).obj ≫
        rootsOfUnityStalkToRootsOfUnity B K hK sbar n =
      rootsOfUnitySectionEval B K hK sbar n U p :=
  (fieldSitePoint B K hK sbar).toPresheafFiber_presheafFiberDesc _ _ U p

/-! ### Germ evaluation is Galois equivariant -/

/-- A multiplicative endomorphism of the `n`-th roots of unity of the separable closure, read
additively and raised to the coefficient universe of étale cohomology. -/
def sepClosureRootsOfUnityHom
    (φ : ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar)) →*
      ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
    ULift.{u + 1} (Additive ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) →+
      ULift.{u + 1} (Additive ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :=
  ((AddEquiv.ulift).symm.toAddMonoidHom.comp (MonoidHom.toAdditive φ)).comp
    (AddEquiv.ulift).toAddMonoidHom

/-- **The Galois action on the `n`-th roots of unity of the separable closure**, written
additively and raised to the coefficient universe of étale cohomology. -/
def sepClosureRootsOfUnitySmul (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    sepClosureRootsOfUnity K sbar n ⟶ sepClosureRootsOfUnity K sbar n :=
  AddCommGrpCat.ofHom (sepClosureRootsOfUnityHom K sbar n
    (Stacks.GaloisCohomology.rootsOfUnityGalHom
        ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
        ↥(GeometricPoint.separableClosure sbar) n σ).toMonoidHom)

/-- The Galois action on the `n`-th roots of unity of the separable closure is the Galois action
on the underlying invertible elements. -/
theorem coe_rootsOfUnityGalHom (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (ζ : ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
    ((Stacks.GaloisCohomology.rootsOfUnityGalHom
            ((Spec (CommRingCat.of K)).residueField (sbar.hom default))
            ↥(GeometricPoint.separableClosure sbar) n σ ζ :
          ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
        (↥(GeometricPoint.separableClosure sbar))ˣ) =
      Units.map σ.toAlgHom.toRingHom.toMonoidHom
        (ζ : (↥(GeometricPoint.separableClosure sbar))ˣ) :=
  Units.ext rfl

/-- **Germ evaluation on sections of `μ_n` is Galois equivariant**: evaluating at a Galois
translate of the lift is evaluating and then acting by the automorphism.  This is the
equivariance that makes the comparison of the stalk with `μ_n(Kˢᵉᵖ)` a map of Galois modules. -/
theorem rootsOfUnitySectionEval_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    rootsOfUnitySectionEval B K hK sbar n U (galoisFiberAction B K hK sbar σ p) =
      rootsOfUnitySectionEval B K hK sbar n U p ≫ sepClosureRootsOfUnitySmul K sbar n σ := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine sepClosureRootsOfUnity_ext K sbar n ?_
  have hR := coe_rootsOfUnitySectionEval_apply B K hK sbar n U p s
  have hgal : geometricPointFiberEvalUnits B K hK sbar U (galoisFiberAction B K hK sbar σ p)
        (rootsOfUnitySectionUnit B K hK n U s) =
      Units.map σ.toAlgHom.toRingHom.toMonoidHom
        (geometricPointFiberEvalUnits B K hK sbar U p
          (rootsOfUnitySectionUnit B K hK n U s)) := by
    rw [geometricPointFiberEvalUnits_galoisFiberAction]
    rfl
  exact (coe_rootsOfUnitySectionEval_apply B K hK sbar n U _ s).trans
    (hgal.trans
      ((congrArg (fun z : (↥(GeometricPoint.separableClosure sbar))ˣ =>
            Units.map σ.toAlgHom.toRingHom.toMonoidHom z) hR).symm.trans
        (coe_rootsOfUnityGalHom K sbar n σ _).symm))

/-! ### Germ evaluation is surjective and locally injective -/

/-- Two invertible global functions with the same value at the lift agree on a refinement of the
neighbourhood. -/
private theorem exists_refinement_units_map_eq (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (a b : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ)
    (h : geometricPointFiberEvalUnits B K hK sbar U p a =
      geometricPointFiberEvalUnits B K hK sbar U p b) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK) (f : V ⟶ U)
      (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V),
      (geometricPointFiber B (Spec (.of K)) hK sbar).map f q = p ∧
        Units.map ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom.toMonoidHom a =
          Units.map ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom.toMonoidHom b := by
  have hw : (geometricPointFiberEval B K hK sbar U p).hom (a.val - b.val) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Units.val h
  obtain ⟨V, f, q, hq, hz⟩ := exists_refinement_appTop_eq_zero B K hK sbar U p _ hw
  rw [map_sub, sub_eq_zero] at hz
  exact ⟨V, f, q, hq, Units.ext hz⟩

/-- **Every `n`-th root of unity of the separable closure is the value at the lift of an
invertible global function which is itself an `n`-th root of unity.**  The multiplicative
statement `AlgebraicGeometry.exists_geometricPointFiberEvalUnits_eq` produces a function with the
right value; its `n`-th power is then one at the lift, hence already one on a refinement of the
neighbourhood, and the restricted function is the one wanted. -/
theorem exists_pow_eq_one_geometricPointFiberEvalUnits_eq
    (x : (↥(GeometricPoint.separableClosure sbar))ˣ) (hx : x ^ n = 1) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V)
      (y : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ),
      y ^ n = 1 ∧ geometricPointFiberEvalUnits B K hK sbar V p y = x := by
  obtain ⟨V, p, y, hy⟩ := exists_geometricPointFiberEvalUnits_eq B K hK sbar x
  obtain ⟨W, f, q, hq, hz⟩ := exists_refinement_units_map_eq B K hK sbar V p (y ^ n) 1
    (by rw [map_pow, hy, hx, map_one])
  refine ⟨W, q,
    Units.map ((SmallEtale.toScheme B (Spec (.of K)) hK).map f).appTop.hom.toMonoidHom y,
    by rw [← map_pow, hz, map_one], ?_⟩
  · refine Eq.trans ?_ hy
    rw [← hq]
    exact (congrArg
      (fun φ : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ →*
          (↥(GeometricPoint.separableClosure sbar))ˣ => φ y)
      (geometricPointFiberEvalUnits_map B K hK sbar f q)).symm

-- The forgetful functor from abelian groups in the universe of the objects of the small étale
-- site preserves the filtered colimits indexed by the site, which is what makes germs jointly
-- surjective onto the stalk and lets two germs be compared on a common refinement.
attribute [local instance] preservesFilteredColimitsOfSize_forget_addCommGrpCat

/-- **The comparison of the stalk of `μ_n` with the `n`-th roots of unity of the separable
closure is bijective.**  Surjectivity is
`AlgebraicGeometry.exists_pow_eq_one_geometricPointFiberEvalUnits_eq` together with the
objectwise description of the sections of `μ_n`; injectivity is that the difference of the two
underlying invertible global functions vanishes at the lift, hence already on a refinement of the
neighbourhood, where the two sections therefore agree. -/
theorem rootsOfUnityStalkToRootsOfUnity_bijective :
    Function.Bijective
      (ConcreteCategory.hom (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨U, p, s₁, s₂, rfl, rfl⟩ :=
      (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective₂
        (P := (rootsOfUnitySheafRestriction B K hK n).obj) a b
    have hab' : ConcreteCategory.hom (rootsOfUnitySectionEval B K hK sbar n U p) s₁ =
        ConcreteCategory.hom (rootsOfUnitySectionEval B K hK sbar n U p) s₂ :=
      (ConcreteCategory.congr_hom
            (toPresheafFiber_comp_rootsOfUnityStalkToRootsOfUnity B K hK sbar n U p)
            s₁).symm.trans
        (hab.trans (ConcreteCategory.congr_hom
          (toPresheafFiber_comp_rootsOfUnityStalkToRootsOfUnity B K hK sbar n U p) s₂))
    have hunit : geometricPointFiberEvalUnits B K hK sbar U p
          (rootsOfUnitySectionUnit B K hK n U s₁) =
        geometricPointFiberEvalUnits B K hK sbar U p
          (rootsOfUnitySectionUnit B K hK n U s₂) :=
      (coe_rootsOfUnitySectionEval_apply B K hK sbar n U p s₁).symm.trans
        ((congrArg (fun z : ToType (sepClosureRootsOfUnity K sbar n) =>
              ((Additive.toMul (ULift.down z) :
                  ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
                (↥(GeometricPoint.separableClosure sbar))ˣ)) hab').trans
          (coe_rootsOfUnitySectionEval_apply B K hK sbar n U p s₂))
    obtain ⟨V, f, q, hq, hz⟩ :=
      exists_refinement_units_map_eq B K hK sbar U p _ _ hunit
    refine ((fieldSitePoint B K hK sbar).toPresheafFiber_eq_iff' U p s₁ s₂).mpr
      ⟨V, f, q, hq, ?_⟩
    refine rootsOfUnitySection_injective B K hK n V ?_
    rw [rootsOfUnitySectionUnit_map, rootsOfUnitySectionUnit_map]
    exact hz
  · obtain ⟨V, p, y, hyn, hy⟩ := exists_pow_eq_one_geometricPointFiberEvalUnits_eq B K hK sbar n
      ((Additive.toMul (ULift.down t) :
          ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
        (↥(GeometricPoint.separableClosure sbar))ˣ)
      ((mem_rootsOfUnity n _).mp (Additive.toMul (ULift.down t)).2)
    obtain ⟨s, hs⟩ := exists_rootsOfUnitySectionUnit_eq B K hK n V y hyn
    refine ⟨(fieldSitePoint B K hK sbar).toPresheafFiber V p
      (rootsOfUnitySheafRestriction B K hK n).obj s, ?_⟩
    refine (ConcreteCategory.congr_hom
      (toPresheafFiber_comp_rootsOfUnityStalkToRootsOfUnity B K hK sbar n V p) s).trans ?_
    refine sepClosureRootsOfUnity_ext K sbar n ?_
    exact (coe_rootsOfUnitySectionEval_apply B K hK sbar n V p s).trans
      ((congrArg (fun z : (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤))ˣ =>
          geometricPointFiberEvalUnits B K hK sbar V p z) hs).trans hy)

/-- The comparison of the stalk of `μ_n` at a geometric point of the spectrum of a field with the
`n`-th roots of unity of the separable closure is an isomorphism. -/
instance isIso_rootsOfUnityStalkToRootsOfUnity :
    IsIso (rootsOfUnityStalkToRootsOfUnity B K hK sbar n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (rootsOfUnityStalkToRootsOfUnity_bijective B K hK sbar n)

/-- **The stalk of `μ_n` at a geometric point of the spectrum of a field is the group of `n`-th
roots of unity of the separable closure**, written additively and raised to the coefficient
universe of étale cohomology. -/
def rootsOfUnityStalkIsoRootsOfUnity :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (rootsOfUnitySheafRestriction B K hK n) ≅ sepClosureRootsOfUnity K sbar n :=
  asIso (rootsOfUnityStalkToRootsOfUnity B K hK sbar n)

end AlgebraicGeometry

end
