module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPsi

/-!
# The source identification of `ψ` at a scheme point, as the composite of its five factors

At a scheme point `f : T ⟶ X` of the base, the identification
`…RelativeProjSituation.fibrePsiSourceIso` of the inverse image of `π^*𝒜_n` along the base change
`φ : T ×_X P ⟶ P` with the module attached by Stacks 03DX (2) to `π_T^*(f^*𝒜)_n` is by definition
the composite of five factors (`AlgebraicGeometry.Space.pointChainPullbackIso`): the comparison
`φ^*π^* ≅ (φ ≫ π)^*` of Stacks 03LU, the transport along `φ ≫ π = q ≫ f`, the inverse comparison
`(q ≫ f)^* ≅ q^*f^*`, the inverse image along `q : T ×_X P ⟶ T` of the identification `ζ` of
`f^*𝒜_n` with the module attached to its Zariski reading, and the identification `ρ` of the
inverse image along `q` of an attached module.

## Main results

* `AlgebraicGeometry.Space.hom_eq_comp_of_eq_trans_hom`: the `.hom` of a composite of five
  isomorphisms of this shape is the composite of the five `.hom`s.
* `…RelativeProjSituation.fibrePsiSourceIso_hom_eq`: the source identification of `ψ` at a scheme
  point is the composite of its five factors.

## Implementation notes

The factorisation is read off the defining equations of `…RelativeProjSituation.fibrePsiSourceIso`
and `AlgebraicGeometry.Space.pointChainPullbackIso`: its statement is the type (`type_of%`) of
`AlgebraicGeometry.Space.hom_eq_comp_of_eq_trans_hom` at those equations, so that the factors are
the definition's own rather than a re-elaboration of the same text.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `.hom` of the composite of the five isomorphisms of a chain
`φ^*π^*M ≅ (φ ≫ π)^*M = (q ≫ v)^*M ≅ q^*v^*M ≅ q^*Z ≅ Z_q` (the comparisons of Stacks 03LU, the
transport along `φ ≫ π = q ≫ v`, the inverse image along `q` of `ζ : v^*M ≅ Z` and an
identification `ρ : q^*Z ≅ Z_q`) is the composite of their `.hom`s: a morphism equal to the first
is equal to the second. -/
theorem hom_eq_comp_of_eq_trans_hom {Fs P Y R : AlgebraicSpaces B S hS}
    {φ : Fs ⟶ P} {π : P ⟶ Y} {q : Fs ⟶ R} {v : R ⟶ Y} (hφ : φ ≫ π = q ≫ v)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {Zr : Modules.{u, u} B S hS R.1 R.2}
    {Zq : Modules.{u, u} B S hS Fs.1 Fs.2}
    {ζ : (modulePullback B S hS v).obj M ≅ Zr} {ρq : (modulePullback B S hS q).obj Zr ≅ Zq}
    {χ : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj M) ⟶ Zq}
    (h : χ = ((modulePullbackCompIso B S hS φ π).app M ≪≫
      eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hφ) ≪≫
      ((modulePullbackCompIso B S hS q v).app M).symm ≪≫
      (modulePullback B S hS q).mapIso ζ ≪≫ ρq).hom) :
    χ = ((modulePullbackCompIso B S hS φ π).app M).hom ≫
      (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hφ)).hom ≫
      ((modulePullbackCompIso B S hS q v).app M).symm.hom ≫
      ((modulePullback B S hS q).mapIso ζ).hom ≫ ρq.hom :=
  h

end Generic

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) (T : BigFppfOver s.site s.base s.containsBase)
  (f : yoneda.obj T ⟶ s.space.1) (n : ℤ)

/-- The source identification of `ψ` at a scheme point `f : T ⟶ X` is the composite of its five
factors: `…RelativeProjSituation.fibrePsiSourceIso` is the comparison
`φ^*π^*𝒜_n ≅ (φ ≫ π)^*𝒜_n` of Stacks 03LU for the base change `φ : T ×_X P ⟶ P`, the transport
along `φ ≫ π = q ≫ f`, the inverse comparison `(q ≫ f)^*𝒜_n ≅ q^*f^*𝒜_n`, the inverse image along
`q : T ×_X P ⟶ T` of the identification of `f^*𝒜_n` with the module attached to its Zariski
reading, and the identification of the inverse image along `q` of an attached module. -/
theorem fibrePsiSourceIso_hom_eq :
    type_of% (hom_eq_comp_of_eq_trans_hom (s.fibreToSpaceHom_comp_relativeProjSpaceHom T f)
      (congrArg Iso.hom ((fibrePsiSourceIso.eq_1 s T f n).trans
        (pointChainPullbackIso.eq_1 _ _ _ _ _ _ _ _)))) :=
  hom_eq_comp_of_eq_trans_hom (s.fibreToSpaceHom_comp_relativeProjSpaceHom T f)
    (congrArg Iso.hom ((fibrePsiSourceIso.eq_1 s T f n).trans
      (pointChainPullbackIso.eq_1 _ _ _ _ _ _ _ _)))

end RelativeProjSituation

end AlgebraicGeometry.Space

end
