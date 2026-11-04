module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk

/-!
# The stalk of `𝐆_a` over a field is the additive group of the separable closure

Let `K` be a field and let `sbar` be a geometric point of `Spec K`, with `κ` the residue field at
its image and `Kˢᵉᵖ = GeometricPoint.separableClosure sbar` the separable closure of `κ` inside
the algebraically closed field of `sbar`.  The stalk at `sbar` of `𝐆_a`
(`Stacks.ArtinSchreier.additiveSheaf`), restricted along the embedding of the small étale site of
Tag 021B into Mathlib's small étale site, is `(Kˢᵉᵖ, +)`, and germ evaluation onto it is Galois
equivariant.

This is the additive analogue of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk`, and it
is the input that lets the comparison of Tag 03QU part (3) be evaluated at `𝐆_a`, which is the
middle term of the additive chain of equalities of [Stacks, Tag 03QV].

## Main definitions

* `AlgebraicGeometry.additiveSheafRestriction` — `𝐆_a` on the small étale site of Tag 021B.
* `AlgebraicGeometry.sepClosureAdd` — the additive group of `Kˢᵉᵖ`, raised to the coefficient
  universe of étale cohomology.
* `AlgebraicGeometry.additiveSectionEval` — evaluation of a global function on a pointed étale
  neighbourhood at the lift of the geometric point, read on sections of `𝐆_a`.
* `AlgebraicGeometry.additiveStalkToSepClosure` — germ evaluation on the stalk of `𝐆_a`.
* `AlgebraicGeometry.sepClosureAddSmul` — the Galois action on the additive group of `Kˢᵉᵖ`.

## Main results

* `AlgebraicGeometry.additiveStalkToSepClosure_bijective` and
  `AlgebraicGeometry.additiveStalkIsoSepClosure` — **the stalk of `𝐆_a` at `sbar` is
  `(Kˢᵉᵖ, +)`**, as an isomorphism of abelian groups.  Nothing is assumed of the field.
* `AlgebraicGeometry.additiveSectionEval_galoisFiberAction` — **germ evaluation is Galois
  equivariant**.
* `AlgebraicGeometry.exists_geometricPointFiberEval_eq` — every element of `Kˢᵉᵖ` is the value at
  the lift of a global function on a pointed étale neighbourhood.

## How the comparison is obtained

Everything ring-theoretic is already available from the multiplicative file and is reused
verbatim: evaluation of a global function at a lift of the geometric point is the ring
homomorphism `AlgebraicGeometry.geometricPointFiberEval`, it is compatible with restriction
(`AlgebraicGeometry.geometricPointFiberEval_map`) and Galois equivariant
(`AlgebraicGeometry.geometricPointFiberEval_galoisFiberAction`).

Only the two halves of bijectivity differ, and both are cheaper here than there.

* Surjectivity is deduced from the multiplicative statement
  `AlgebraicGeometry.exists_geometricPointFiberEvalUnits_eq` rather than reproved: a nonzero
  element of `Kˢᵉᵖ` is a unit, and the zero element is the value of the zero function on any
  pointed étale neighbourhood, one of which the multiplicative statement at `1` produces.
* Injectivity is `AlgebraicGeometry.exists_refinement_appTop_eq_zero`, which is already stated
  for a plain global function vanishing at the lift; the multiplicative file had to pass from a
  pair of units to the difference of their values to use it, and here the difference is the
  difference of sections itself.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- `𝐆_a` on the small étale site of Tag 021B of `Spec K`: the restriction along the embedding of
that site into Mathlib's of the additive sheaf of global functions. -/
abbrev additiveSheafRestriction :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} :=
  (smallEtaleSheafRestriction B K hK).obj
    (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K)))

/-- The separable closure of the residue field at the image of the geometric point, read as the
abelian group under addition in which the stalk of `𝐆_a` is computed. -/
abbrev sepClosureAdd : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (ULift.{u + 1} ↥(GeometricPoint.separableClosure sbar))

/-- An additive map out of the global functions on an object of the small étale site, raised to
the coefficient universe of étale cohomology. -/
def additiveSectionHom (U : SmallEtale B (Spec (.of K)) hK)
    (φ : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) ⟶
      CommRingCat.of ↥(GeometricPoint.separableClosure sbar)) :
    ULift.{u + 1} Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) →+
      ULift.{u + 1} ↥(GeometricPoint.separableClosure sbar) :=
  ((AddEquiv.ulift).symm.toAddMonoidHom.comp φ.hom.toAddMonoidHom).comp
    (AddEquiv.ulift).toAddMonoidHom

/-- An additive endomorphism of the separable closure, raised to the coefficient universe of
étale cohomology. -/
def sepClosureAddHom (φ : ↥(GeometricPoint.separableClosure sbar) →+
      ↥(GeometricPoint.separableClosure sbar)) :
    ULift.{u + 1} ↥(GeometricPoint.separableClosure sbar) →+
      ULift.{u + 1} ↥(GeometricPoint.separableClosure sbar) :=
  ((AddEquiv.ulift).symm.toAddMonoidHom.comp φ).comp (AddEquiv.ulift).toAddMonoidHom

/-- **The germ-evaluation map on sections of `𝐆_a`**: a global function on a pointed étale
neighbourhood of the geometric point is evaluated at the lift, giving an element of the separable
closure. -/
def additiveSectionEval (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (additiveSheafRestriction B K hK).obj.obj (op U) ⟶ sepClosureAdd K sbar :=
  AddCommGrpCat.ofHom
    (additiveSectionHom B K hK sbar U (geometricPointFiberEval B K hK sbar U p))

/-- The germ-evaluation map on sections, computed on a global function. -/
theorem additiveSectionEval_apply (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (x : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤)) :
    ConcreteCategory.hom (additiveSectionEval B K hK sbar U p) (ULift.up x) =
      ULift.up ((geometricPointFiberEval B K hK sbar U p).hom x) := rfl

/-- Equal ring homomorphisms from the global functions give equal additive maps on sections. -/
private theorem ofHom_additiveSectionHom_congr (U : SmallEtale B (Spec (.of K)) hK)
    {φ ψ : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) ⟶
      CommRingCat.of ↥(GeometricPoint.separableClosure sbar)} (h : φ = ψ) :
    AddCommGrpCat.ofHom (additiveSectionHom B K hK sbar U φ) =
      AddCommGrpCat.ofHom (additiveSectionHom B K hK sbar U ψ) :=
  congrArg (fun φ => AddCommGrpCat.ofHom (additiveSectionHom B K hK sbar U φ)) h

/-- Germ evaluation is compatible with restriction along a morphism of the small étale site,
which is what lets it descend to the stalk. -/
theorem additiveSectionEval_naturality {U V : SmallEtale B (Spec (.of K)) hK} (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (additiveSheafRestriction B K hK).obj.map f.op ≫ additiveSectionEval B K hK sbar U p =
      additiveSectionEval B K hK sbar V
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p) :=
  ofHom_additiveSectionHom_congr B K hK sbar V (geometricPointFiberEval_map B K hK sbar f p)

/-- **The stalk of `𝐆_a` at a geometric point of the spectrum of a field, mapped to the additive
group of the separable closure.**  The germ of a global function on a pointed étale neighbourhood
is sent to the value of that function at the lift. -/
def additiveStalkToSepClosure :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (additiveSheafRestriction B K hK) ⟶ sepClosureAdd K sbar :=
  (fieldSitePoint B K hK sbar).presheafFiberDesc
    (P := (additiveSheafRestriction B K hK).obj)
    (fun U p => additiveSectionEval B K hK sbar U p)
    (fun {_ _} f p => additiveSectionEval_naturality B K hK sbar f p)

/-- The comparison map out of the stalk, precomposed with the germ map over a pointed étale
neighbourhood, is germ evaluation there. -/
theorem toPresheafFiber_comp_additiveStalkToSepClosure (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (fieldSitePoint B K hK sbar).toPresheafFiber U p (additiveSheafRestriction B K hK).obj ≫
        additiveStalkToSepClosure B K hK sbar =
      additiveSectionEval B K hK sbar U p :=
  (fieldSitePoint B K hK sbar).toPresheafFiber_presheafFiberDesc _ _ U p

/-! ### Germ evaluation is Galois equivariant -/

/-- **The Galois action on the additive group of the separable closure**, raised to the
coefficient universe of étale cohomology. -/
def sepClosureAddSmul (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    sepClosureAdd K sbar ⟶ sepClosureAdd K sbar :=
  AddCommGrpCat.ofHom
    (sepClosureAddHom K sbar σ.toAlgHom.toRingHom.toAddMonoidHom)

/-- **Germ evaluation on sections of `𝐆_a` is Galois equivariant**: evaluating at a Galois
translate of the lift is evaluating and then acting by the automorphism.  This is the
equivariance that makes the comparison of the stalk with the separable closure a map of Galois
modules. -/
theorem additiveSectionEval_galoisFiberAction
    (σ : GeometricPoint.absoluteGaloisGroup sbar) (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    additiveSectionEval B K hK sbar U (galoisFiberAction B K hK sbar σ p) =
      additiveSectionEval B K hK sbar U p ≫ sepClosureAddSmul K sbar σ :=
  ofHom_additiveSectionHom_congr B K hK sbar U
    (geometricPointFiberEval_galoisFiberAction B K hK sbar σ U p)

/-! ### Germ evaluation is surjective and locally injective -/

/-- **Every element of the separable closure is the value at the lift of a global function on a
pointed étale neighbourhood.**  A nonzero element is a unit, where this is
`AlgebraicGeometry.exists_geometricPointFiberEvalUnits_eq`; the zero element is the value of the
zero function on the neighbourhood that statement produces at `1`. -/
theorem exists_geometricPointFiberEval_eq (x : ↥(GeometricPoint.separableClosure sbar)) :
    ∃ (V : SmallEtale B (Spec (.of K)) hK)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V)
      (y : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤)),
      (geometricPointFiberEval B K hK sbar V p).hom y = x := by
  classical
  by_cases hx : x = 0
  · obtain ⟨V, p, -, -⟩ := exists_geometricPointFiberEvalUnits_eq B K hK sbar 1
    exact ⟨V, p, 0, by rw [map_zero, hx]⟩
  · obtain ⟨V, p, y, hy⟩ :=
      exists_geometricPointFiberEvalUnits_eq B K hK sbar (Units.mk0 x hx)
    exact ⟨V, p, (y : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤)),
      congrArg Units.val hy⟩

/-! ### The stalk of `𝐆_a` is the additive group of the separable closure -/

-- The forgetful functor from abelian groups in the universe of the objects of the small étale
-- site preserves the filtered colimits indexed by the site.
attribute [local instance] preservesFilteredColimitsOfSize_forget_addCommGrpCat

/-- The comparison map on the germ of a section over a pointed étale neighbourhood is germ
evaluation of that section. -/
private theorem germ_additiveStalkToSepClosure_apply (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (z : ToType ((additiveSheafRestriction B K hK).obj.obj (op U))) :
    ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)
        (ConcreteCategory.hom ((fieldSitePoint B K hK sbar).toPresheafFiber U p
          (additiveSheafRestriction B K hK).obj) z) =
      ConcreteCategory.hom (additiveSectionEval B K hK sbar U p) z :=
  ConcreteCategory.congr_hom (toPresheafFiber_comp_additiveStalkToSepClosure B K hK sbar U p) z

/-- **The comparison of the stalk of `𝐆_a` with the additive group of the separable closure is
bijective.** -/
theorem additiveStalkToSepClosure_bijective :
    Function.Bijective (ConcreteCategory.hom (additiveStalkToSepClosure B K hK sbar)) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨U, p, z₁, z₂, rfl, rfl⟩ :=
      (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective₂
        (P := (additiveSheafRestriction B K hK).obj) a b
    have hab' : ConcreteCategory.hom (additiveSectionEval B K hK sbar U p) z₁ =
        ConcreteCategory.hom (additiveSectionEval B K hK sbar U p) z₂ :=
      (germ_additiveStalkToSepClosure_apply B K hK sbar U p z₁).symm.trans
        (hab.trans (germ_additiveStalkToSepClosure_apply B K hK sbar U p z₂))
    set y₁ : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) := ULift.down z₁ with hy₁
    set y₂ : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤) := ULift.down z₂ with hy₂
    have hval : (geometricPointFiberEval B K hK sbar U p).hom y₁ =
        (geometricPointFiberEval B K hK sbar U p).hom y₂ :=
      congrArg ULift.down hab'
    have hw : (geometricPointFiberEval B K hK sbar U p).hom (y₁ - y₂) = 0 := by
      rw [map_sub, hval, sub_self]
    obtain ⟨V, f, q, hq, hz⟩ := exists_refinement_appTop_eq_zero B K hK sbar U p _ hw
    rw [map_sub, sub_eq_zero] at hz
    refine ((fieldSitePoint B K hK sbar).toPresheafFiber_eq_iff' U p z₁ z₂).mpr
      ⟨V, f, q, hq, ?_⟩
    exact congrArg (fun w : Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj V, ⊤) =>
      ULift.up w) hz
  · obtain ⟨V, p, y, hy⟩ := exists_geometricPointFiberEval_eq B K hK sbar (ULift.down t)
    refine ⟨(fieldSitePoint B K hK sbar).toPresheafFiber V p
      (additiveSheafRestriction B K hK).obj (ULift.up y), ?_⟩
    exact (germ_additiveStalkToSepClosure_apply B K hK sbar V p _).trans
      (congrArg (fun w : ↥(GeometricPoint.separableClosure sbar) =>
        (ULift.up w : ToType (sepClosureAdd K sbar))) hy)

/-- The comparison of the stalk of `𝐆_a` with the additive group of the separable closure is an
isomorphism. -/
instance isIso_additiveStalkToSepClosure :
    IsIso (additiveStalkToSepClosure B K hK sbar) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (additiveStalkToSepClosure_bijective B K hK sbar)

/-- **The stalk of `𝐆_a` at a geometric point of the spectrum of a field is the additive group of
the separable closure**, raised to the coefficient universe of étale cohomology. -/
def additiveStalkIsoSepClosure :
    (abelianEtaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK sbar).obj
        (additiveSheafRestriction B K hK) ≅ sepClosureAdd K sbar :=
  asIso (additiveStalkToSepClosure B K hK sbar)

end AlgebraicGeometry

end
