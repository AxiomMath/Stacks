module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneFibreSource
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAtPoint

/-!
# The slots `hχ` and `hτ₁` of the target square of clause (1) of Stacks 0D2Z over the site of `s`

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` is the
instance of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at
`Φ = modulePullback s.site s.base s.containsBase` and `κ = modulePullbackCompIso` over the same
site.  Its source identification `K = κ₁ ≫ τ₁ ≫ c^*χ ≫ ρ_c` has two factors which are
definitions: the identification `χ` of the source of `ψ` at the scheme point `f ∘ x` of the base
under `w` (`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiSourceIso`), and the comparison
`τ₁ : w^*r^*π^*𝒜_d ≅ c_w^*φ^*π^*𝒜_d` of the two factorisations `w ≫ r = c_w ≫ φ`
(`…InvertibleTwistingRestriction.modulePullbackCompTransportIso`).  The hypotheses `hχ` and `hτ₁`
ask for them as the composites of their factors, every factor an inverse image or a comparison of
Stacks 03LU over `s.site`.

## Main results

* `…InvertibleTwistingRestriction.siteTargetSquare_hχ`: the hypothesis `hχ` over `s.site`.
* `…InvertibleTwistingRestriction.siteTargetSquare_hτ₁`: the hypothesis `hτ₁` over `s.site`.

## Implementation notes

Both statements are instances of lemmas at variables, read off the defining equations, and stated
as the instances' own types (`type_of%`), so no factor is re-elaborated. The module `𝒜_d` is the
piece of `s.shrink.algebra` over the structure ring of `s.space` on `s.site`, the spelling of the
defining equation of `…RelativeProjSituation.fibrePsiSourceIso`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/


@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- **The hypothesis `hχ` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`**: the identification `χ` of the inverse image of `π^*𝒜_d` along the base
change `φ : W ×_Y P ⟶ P` with the module attached to `q^*((f ∘ x)^*𝒜)_d` is the comparison
`φ^*π^* ≅ (φ ≫ π)^*` of Stacks 03LU, the transport along `φ ≫ π = q ≫ (f ∘ x)`, the inverse
comparison `(q ≫ (f ∘ x))^* ≅ q^*(f ∘ x)^*`, the inverse image along `q` of the identification
`ζ` of `(f ∘ x)^*𝒜_d` with the module attached to its Zariski reading, and the identification
`ρ_q` of Stacks 03DX (2) along `q`. This is
`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiSourceIso_hom_eq` at the scheme point
`f ∘ x` under `w`. -/
theorem siteTargetSquare_hχ :
    type_of% (fibrePsiSourceIso_hom_eq s W (locusPoint w ≫ f.hom) (d : ℤ)) :=
  fibrePsiSourceIso_hom_eq s W (locusPoint w ≫ f.hom) (d : ℤ)

/-- **The hypothesis `hτ₁` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`**: the comparison `w^*r^*(π^*𝒜_d) ≅ c_w^*φ^*(π^*𝒜_d)` of the two
factorisations `w ≫ r = c_w ≫ φ`, for `r : U(ψ) ⟶ P` and the section `c_w` of the fibre
`W ×_Y P ⟶ W`, is the comparison `w^*r^* ≅ (w ≫ r)^*` of Stacks 03LU, the transport along
`w ≫ r = c_w ≫ φ` and the inverse comparison `(c_w ≫ φ)^* ≅ c_w^*φ^*`. This is
`…InvertibleTwistingRestriction.modulePullbackCompTransportIso_hom_eq` at the site `s.site`, the
base `s.base` and the containment `s.containsBase`, at the module `π^*𝒜_d`. -/
theorem siteTargetSquare_hτ₁ :
    type_of% (modulePullbackCompTransportIso_hom_eq (B := s.site) (S := s.base)
      (hS := s.containsBase)
      (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := locusSpaceOfUnitalHom s f L ψ) w)
      ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
      (representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
      (pointHom_comp_invertibleSpaceMorphism w)
      ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf s.site s.base s.containsBase
          s.space) s.shrink.algebra (d : ℤ)))) :=
  modulePullbackCompTransportIso_hom_eq (B := s.site) (S := s.base) (hS := s.containsBase)
    (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := locusSpaceOfUnitalHom s f L ψ) w)
    ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    (representedSpaceMap s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
    (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
    (pointHom_comp_invertibleSpaceMorphism w)
    ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
      (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf s.site s.base s.containsBase
        s.space) s.shrink.algebra (d : ℤ)))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
