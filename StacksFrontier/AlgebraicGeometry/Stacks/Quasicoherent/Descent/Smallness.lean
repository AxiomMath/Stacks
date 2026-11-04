module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmallSchemes
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# A category of schemes below a size cutoff is essentially small

An affine scheme whose ring of global sections has at most `κ` elements is `Spec` of a quotient
of the polynomial ring on `κ` variables over `ℤ`, so these schemes form an essentially small
property of objects. As the underlying category of a big fppf site is essentially small,
sheafification into abelian groups exists on the big fppf sites over `S` and on the sites
associated with an essentially small category fibred in groupoids over them, and weak
equivalences of abelian presheaves there are the locally bijective maps.

## Main results

* `AlgebraicGeometry.essentiallySmall_affineBelow`: the affine schemes with at most `κ`
  elements form an essentially small property of objects.
* `AlgebraicGeometry.BigFppfOver.hasWeakSheafify`,
  `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective` and their localizations at an object:
  the sheafification instances for abelian groups on the big fppf site over `S`.
* `AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology` and
  `AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology`: the same two
  instances on each site associated with an essentially small category fibred in groupoids.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 000I](https://stacks.math.columbia.edu/tag/000I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry

/-- The affine schemes whose ring of global sections has at most `κ` elements, up to
isomorphism, form a set: each is `Spec` of a quotient of `MvPolynomial κ.out ℤ`. -/
public theorem essentiallySmall_affineBelow (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun X : Scheme.{u} => ∃ R : CommRingCat.{u}, #R ≤ κ ∧ Nonempty (X ≅ Spec R)) := by
  classical
  let A := MvPolynomial κ.out ℤ
  let Q := ObjectProperty.ofObj (fun I : Ideal A => Spec (CommRingCat.of (A ⧸ I)))
  refine ⟨Q, inferInstance, ?_⟩
  rintro X ⟨R, hR, ⟨e⟩⟩
  obtain ⟨j⟩ : Nonempty (R ↪ κ.out) := by
    show #R ≤ #κ.out
    simpa using hR
  let f : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Function.invFun j)
  have hf : Function.Surjective f := fun r =>
    ⟨MvPolynomial.X (j r), (MvPolynomial.eval₂Hom_X' _ _ _).trans
      (Function.leftInverse_invFun j.injective r)⟩
  exact ⟨_, ⟨RingHom.ker f⟩, ⟨e ≪≫ (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (RingHom.quotientKerEquivOfSurjective hf)).op)⟩⟩

attribute [instance] BigFppfSite.essentiallySmall_schemes

/-- Sheafification into abelian groups exists on every site with an essentially small
underlying category. -/
private theorem hasWeakSheafify_of_essentiallySmall {C : Type v} [Category.{w} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{u} := by
  let _ : HasSheafify J AddCommGrpCat.{u} := hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  infer_instance

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheafification into abelian groups exists on each of the five big sites over `S`. -/
public theorem hasWeakSheafify (τ : SiteKind) :
    HasWeakSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
  hasWeakSheafify_of_essentiallySmall _

/-- Weak equivalences of abelian presheaves on each of the five big sites over `S` are the
locally bijective maps. -/
public theorem wEqualsLocallyBijective (τ : SiteKind) :
    (baseOverTopology B S hS τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheafification into abelian groups exists on every localization of each of the five big
sites over `S` at an object. -/
public theorem hasWeakSheafify_over (τ : SiteKind) (X : BigFppfOver B S hS) :
    HasWeakSheafify ((baseOverTopology B S hS τ).over X) AddCommGrpCat.{u} :=
  hasWeakSheafify_of_essentiallySmall _

/-- Weak equivalences of abelian presheaves on every localization of each of the five big
sites over `S` at an object are the locally bijective maps. -/
public theorem wEqualsLocallyBijective_over (τ : SiteKind) (X : BigFppfOver B S hS) :
    ((baseOverTopology B S hS τ).over X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end BigFppfOver

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- Sheafification into abelian groups exists on each of the five sites associated with an
essentially small category fibred in groupoids over the big fppf category of schemes over
`S`. -/
public theorem hasWeakSheafify_associatedTopology (τ : SiteKind) :
    HasWeakSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u} :=
  hasWeakSheafify_of_essentiallySmall _

/-- Weak equivalences of abelian presheaves on each of the five sites associated with an
essentially small category fibred in groupoids are the locally bijective maps. -/
public theorem wEqualsLocallyBijective_associatedTopology (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end FibredSite

end AlgebraicGeometry

end
