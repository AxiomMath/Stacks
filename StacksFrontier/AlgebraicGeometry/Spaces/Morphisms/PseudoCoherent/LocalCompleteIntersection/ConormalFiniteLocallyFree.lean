module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Conormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableConormal

/-!
# Unramified local complete intersection morphisms of algebraic spaces

Let `f : X ⟶ Y` be a local complete intersection morphism of algebraic spaces over a scheme `S`.
**Stacks 06CB**: `f` is unramified if and only if it is formally unramified, and in this case
the conormal sheaf `𝒞_{X/Y}` of [Stacks, Tag 0607] is finite locally free on `X`.

The equivalence is
`AlgebraicGeometry.Space.isUnramified_iff_formallyUnramified_of_isLocalCompleteIntersection`.
For the conormal sheaf,
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_isLocalCompleteIntersection`
reduces the claim by étale localization ([Stacks, Tag 060D]) to a formally unramified local
complete intersection morphism of representable algebraic spaces, granted the comparison
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison` between the conormal sheaf of such
a morphism and that of the corresponding morphism of schemes.  That comparison is proved here,
as `AlgebraicGeometry.Space.representableConormalSheafComparison`, from
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme`; the scheme case is
[Stacks, Tag 06B9].

## Main results

* `AlgebraicGeometry.Space.representableConormalSheafComparison`: the comparison, for arbitrary
  representable algebraic spaces.
* `AlgebraicGeometry.Space.unramified_iff_formallyUnramified_and_isFiniteLocallyFreeOnSite_\
  conormalSheaf`: **Stacks 06CB.**

## Implementation notes

The conormal sheaf is attached in this library to a universal first order thickening of `f`,
a datum which exists exactly when `f` is formally unramified ([Stacks, Tag 0606],
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`) and on which the conormal sheaf
depends only up to isomorphism
(`AlgebraicGeometry.Space.UniversalFirstOrderThickening.conormalSheafIso`).  So "in this case the
conormal sheaf is finite locally free" is stated for every such datum.

## References

* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conormal sheaf of a formally unramified morphism of representable algebraic spaces is
finite locally free when that of the corresponding morphism of schemes is.**  This is the
comparison `AlgebraicGeometry.Space.RepresentableConormalSheafComparison`.

The representations identify the morphism with the morphism of algebraic spaces represented by
a morphism `q` of the site, compatibly with a universal first order thickening, and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme` compares the conormal
sheaves for `q`. -/
theorem representableConormalSheafComparison : RepresentableConormalSheafComparison B S hS := by
  intro V U _ _ g s _ hF
  let q₀ := yoneda.preimage (V.1.reprW.hom ≫ g.hom ≫ U.1.reprW.inv)
  have hq₀ : yoneda.map q₀ = V.1.reprW.hom ≫ g.hom ≫ U.1.reprW.inv := yoneda.map_preimage _
  let ψ : U ≅ schemeSpace U.1.reprX :=
    { hom := ObjectProperty.homMk U.1.reprW.inv
      inv := ObjectProperty.homMk U.1.reprW.hom
      hom_inv_id := ObjectProperty.hom_ext _ U.1.reprW.inv_hom_id
      inv_hom_id := ObjectProperty.hom_ext _ U.1.reprW.hom_inv_id }
  have hfu : FormallyUnramified ((schemeSpaceFunctor B S hS).map q₀).hom := by
    change FormallyUnramified (yoneda.map q₀)
    rw [hq₀]
    exact formallyUnramified_comp _ _
      (formallyUnramified_of_etale B S hS _ (presheaf_etale_of_iso B S hS V.1.reprW))
      (formallyUnramified_comp _ _ s.formallyUnramified
        (formallyUnramified_of_etale B S hS _ (presheaf_etale_of_iso B S hS U.1.reprW.symm)))
  let s' : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q₀) :=
    { formallyUnramified := hfu
      ambient := s.ambient
      toBase := s.toBase ≫ ψ.hom
      sub := s.sub
      isUniversal := s.isUniversal.comp_iso B S hS ψ
      sourceIso := V.1.reprW ≪≫ s.sourceIso
      sourceIso_ι_toBase := by
        change (V.1.reprW.hom ≫ s.sourceIso.hom) ≫ s.sub.ι ≫ s.toBase.hom ≫ U.1.reprW.inv =
          yoneda.map q₀
        rw [hq₀, ← s.sourceIso_ι_toBase]
        simp only [Category.assoc] }
  have h' := isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme B S hS q₀ s' hF
  exact (isFiniteLocallyFreeOnSite_conormalSheaf_iff B S hS s).2
    ((isFiniteLocallyFreeOnSite_conormalSheaf_iff B S hS s').1 h')

/-- **Stacks 06CB.**  Let `f : X ⟶ Y` be a local complete intersection morphism of algebraic
spaces over `S`.  Then `f` is unramified if and only if it is formally unramified, and in this
case the conormal sheaf `𝒞_{X/Y}` is finite locally free on `X`: for every universal first order
thickening `t` of `f` — which exists exactly when `f` is formally unramified, by Stacks 0606 —
the conormal sheaf of Stacks 0607 is finite locally free on the small étale site of `X`. -/
@[stacks 06CB]
theorem unramified_iff_formallyUnramified_and_isFiniteLocallyFreeOnSite_conormalSheaf
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f.hom) :
    (IsUnramified B S hS f.hom ↔ FormallyUnramified f.hom) ∧
      ∀ t : UniversalFirstOrderThickening B S hS f,
        SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS t) :=
  ⟨isUnramified_iff_formallyUnramified_of_isLocalCompleteIntersection B S hS X.2 Y.2 hf,
    fun t => isFiniteLocallyFreeOnSite_conormalSheaf_of_isLocalCompleteIntersection B S hS t hf
      (representableConormalSheafComparison B S hS)⟩

end AlgebraicGeometry.Space

end
