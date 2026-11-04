module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneFibreSource
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap

/-!
# The slot `hχ` of the target square of clause (1) of Stacks 0D2Z, in the syntax of the slot

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`, over the
site of `s` (`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`, the
instance of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at
`Φ = modulePullback s.site …` and `κ = modulePullbackCompIso s.site …`), takes as its hypothesis
`hχ` the source identification `…RelativeProjSituation.fibrePsiSourceIso` of `ψ` at the scheme
point `f ∘ x` as the composite of its five factors.

`…InvertibleTwistingRestriction.fibrePsiSourceIso_hom_eq_locusPoint` states this with the objects
of the factorisation read off the defining equations (the fibre `W ×_Y P` as
`representedAlgebraicSpace`, `𝒜_d` over the site of `s.shrink`, the Zariski reading of
`(f ∘ x)^*𝒜_d` as `zariskiReadingQcoh`).  This file states it at the objects of the slot: the
fibre as `⟨yoneda.obj (W ×_Y P), _⟩`, the scheme point as
`yonedaSpace s.site s.base s.containsBase W`, `𝒜_d` as the piece of `s.shrink.algebra` over the
structure ring of `s.space` on `s.site`, the Zariski reading as `s.pointPieceQcoh`, and `χ` as
`(fibrePsiSourceIso …).hom` at its declared type.  It is
`AlgebraicGeometry.Space.hom_eq_comp_of_eq_trans_hom` with every argument the one the slot is
instantiated at, applied to the defining equations of `fibrePsiSourceIso` and
`pointChainPullbackIso`, and stated as that instance's own type (`type_of%`).

## Main results

* `…InvertibleTwistingRestriction.fibrePsiSourceIso_hom_eq_locusPoint_slot`: the hypothesis `hχ`
  of the target square at a scheme point of `U(ψ)`, over the site of `s`, in the syntax of the
  slot.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

-- The arguments, built over the site of `s.shrink`, are checked against the slot over the
-- site of `s` by unfolding `s.shrink`.
/-- **The source identification of `ψ` at the scheme point `f ∘ x` underlying a scheme point `w`
of `U(ψ)` is the composite of its five factors, in the syntax of the slot `hχ`**: the comparison
`φ^*π^*𝒜_d ≅ (φ ≫ π)^*𝒜_d` of Stacks 03LU for the base change `φ : W ×_Y P ⟶ P`, the transport
along `φ ≫ π = q ≫ (f ∘ x)`, the inverse comparison `(q ≫ (f ∘ x))^*𝒜_d ≅ q^*(f ∘ x)^*𝒜_d`, the
inverse image along `q` of the identification `ζ` of `(f ∘ x)^*𝒜_d` with the module attached to
its Zariski reading, and the identification of the inverse image along `q` of an attached module,
over `s.site s.base s.containsBase`.  This is the hypothesis `hχ` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over the site of `s`, at the arguments of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`, read off the defining
equations of `fibrePsiSourceIso` and `pointChainPullbackIso`. -/
theorem fibrePsiSourceIso_hom_eq_locusPoint_slot :
    type_of% (hom_eq_comp_of_eq_trans_hom (B := s.site) (S := s.base) (hS := s.containsBase)
      (Fs := (⟨yoneda.obj (s.relativeProjPoints.fibre W (locusPoint w ≫ f.hom)),
        isAlgebraicSpace_yoneda s.site s.base s.containsBase
          (s.relativeProjPoints.fibre W (locusPoint w ≫ f.hom))⟩ :
        AlgebraicSpaces s.site s.base s.containsBase))
      (R := yonedaSpace s.site s.base s.containsBase W)
      (φ := s.fibreToSpaceHom W (locusPoint w ≫ f.hom)) (π := s.relativeProjSpaceHom)
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom))
      (s.fibreToSpaceHom_comp_relativeProjSpaceHom W (locusPoint w ≫ f.hom))
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρq := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))
      (χ := (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom)
      (congrArg Iso.hom ((fibrePsiSourceIso.eq_1 s W (locusPoint w ≫ f.hom) (d : ℤ)).trans
        (pointChainPullbackIso.eq_1 _ _ _ _ _ _ _ _)))) :=
  hom_eq_comp_of_eq_trans_hom (B := s.site) (S := s.base) (hS := s.containsBase)
    (Fs := (⟨yoneda.obj (s.relativeProjPoints.fibre W (locusPoint w ≫ f.hom)),
        isAlgebraicSpace_yoneda s.site s.base s.containsBase
          (s.relativeProjPoints.fibre W (locusPoint w ≫ f.hom))⟩ :
        AlgebraicSpaces s.site s.base s.containsBase))
    (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
      (locusPoint w ≫ f.hom))
    (M := SheafOfModules.GradedAlgebra.piece
      (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
    (R := yonedaSpace s.site s.base s.containsBase W)
    (φ := s.fibreToSpaceHom W (locusPoint w ≫ f.hom)) (π := s.relativeProjSpaceHom)
    (q := representedSpaceMap s.site s.base s.containsBase
      (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
    (s.fibreToSpaceHom_comp_relativeProjSpaceHom W (locusPoint w ≫ f.hom))
    (χ := (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom)
    (congrArg Iso.hom ((fibrePsiSourceIso.eq_1 s W (locusPoint w ≫ f.hom) (d : ℤ)).trans
      (pointChainPullbackIso.eq_1 _ _ _ _ _ _ _ _)))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
