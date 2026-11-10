module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper morphisms to a scheme with finite fibres

Let `g : W ⟶ V` be a proper morphism from an algebraic space to (the algebraic space of) a scheme
of the big fppf site. The fibre of `|W| ⟶ |V|` over a point is finite exactly when `g` is
quasi-finite at every point of that fibre, and `g` is finite exactly when every fibre is finite.

The first statement is Stacks 0ACZ, conditions (1), (2) and (4), applied to `g`: a proper
morphism is separated, hence quasi-separated, and of finite type, and the decency of the target
that condition (4) asks for holds because a representable presheaf is decent (Stacks 0ABT). The
second combines it with Stacks 0A4X (finite = proper and locally quasi-finite) and Stacks 040Z
(locally quasi-finite = quasi-finite at every point).

For a closed subspace `Z` of an algebraic space `X` proper over `V`, the last statement then
says that finiteness of `Z ⟶ V` depends only on the *set* of points of `Z` inside `|X|`, since a
closed immersion is injective on points (Stacks 06RV). This is the independence of the chosen
closed subspace structure on a closed subset that Stacks 0DZW uses ("any/some closed subspace
structure").

## Main results

* `AlgebraicGeometry.Space.finite_fibre_iff_forall_isQuasiFiniteAt_of_isProper`
* `AlgebraicGeometry.Space.isFinite_iff_forall_finite_fibre_of_isProper`
* `AlgebraicGeometry.Space.isFinite_comp_iff_forall_finite_fibre_of_isClosedSubspace`

## References

* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a proper morphism from an algebraic space to a scheme of the site, the fibre over a point
of the target is finite exactly when the morphism is quasi-finite at every point of that fibre.

This is Stacks 0ACZ, conditions (1), (2) and (4); the decency of the target asked for by
condition (4) holds because a representable presheaf is decent (Stacks 0ABT). -/
theorem finite_fibre_iff_forall_isQuasiFiniteAt_of_isProper
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {V : BigFppfOver B S hS} (g : W ⟶ yoneda.obj V) (hg : IsProper B S hS g)
    (y : points B S hS (yoneda.obj V)) :
    {w : points B S hS W | pointsMap B S hS W g w = y}.Finite ↔
      ∀ w : points B S hS W, pointsMap B S hS W g w = y → IsQuasiFiniteAt B S hS g w := by
  obtain ⟨p, hp⟩ := Quot.exists_rep y
  have hqs := isQuasiSeparated_of_isSeparated B S hS hg.1
  exact (finite_fieldFiber_iff_finite_setFiber_of_decent B S hS hW
      (isAlgebraicSpace_yoneda B S hS V) g hqs hg.2.1 (isDecentSpace_yoneda B S hS V)
      y p hp).symm.trans
    (finite_fieldFiber_iff_quasiFiniteAt_fiber B S hS hW (isAlgebraicSpace_yoneda B S hS V)
      g hqs hg.2.1 y p hp)

/-- A proper morphism from an algebraic space to a scheme of the site is finite exactly when all
of its fibres on points are finite: Stacks 0A4X together with Stacks 0ACZ. -/
@[ega "III 4.4.2" "more general"]
theorem isFinite_iff_forall_finite_fibre_of_isProper
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {V : BigFppfOver B S hS} (g : W ⟶ yoneda.obj V) (hg : IsProper B S hS g) :
    IsFinite B S hS g ↔
      ∀ y : points B S hS (yoneda.obj V),
        {w : points B S hS W | pointsMap B S hS W g w = y}.Finite := by
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hlqf := isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hW hV g
  simp only [finite_fibre_iff_forall_isQuasiFiniteAt_of_isProper B S hS hW g hg]
  constructor
  · intro hfin y w _
    exact hlqf.mp (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hW hV g hfin).2 w
  · intro h
    exact isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hW hV g hg
      (hlqf.mpr fun w => h _ w rfl)

/-- The fibre of a closed subspace over a point, read inside the ambient space, is finite exactly
when its own fibre is: a closed immersion is injective on points (Stacks 06RV). -/
theorem finite_fibre_range_iff_of_isClosedSubspace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor X)
    (hZ : IsClosedSubspace B S hS Z) (f : X ⟶ Y) (y : points B S hS Y) :
    {x : points B S hS X |
        x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) ∧ pointsMap B S hS X f x = y}.Finite ↔
      {z : points B S hS Z.toFunctor |
        pointsMap B S hS Z.toFunctor (Z.ι ≫ f) z = y}.Finite := by
  have himage : pointsMap B S hS Z.toFunctor Z.ι ''
      {z : points B S hS Z.toFunctor | pointsMap B S hS Z.toFunctor (Z.ι ≫ f) z = y} =
      {x : points B S hS X |
        x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) ∧ pointsMap B S hS X f x = y} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, rfl⟩, by rwa [pointsMap_comp] at hz⟩
    · rintro ⟨⟨z, rfl⟩, hx⟩
      exact ⟨z, by rwa [Set.mem_ofPred_eq, pointsMap_comp], rfl⟩
  rw [← himage]
  exact ⟨fun h => h.of_finite_image
    (pointsMap_injective_of_isClosedImmersion B S hS Z.ι hZ.2).injOn, fun h => h.image _⟩

/-- **Finiteness of a closed subspace over a scheme depends only on its points.** Let `X` be an
algebraic space proper over a scheme `V` of the site and let `Z ⊂ X` be a closed subspace. Then
`Z ⟶ V` is finite exactly when the set of points of `Z`, read in `|X|`, meets every fibre of
`|X| ⟶ |V|` in a finite set. In particular two closed subspace structures on the same closed
subset of `|X|` are finite over `V` together. -/
theorem isFinite_comp_iff_forall_finite_fibre_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : BigFppfOver B S hS} (f : X ⟶ yoneda.obj V) (hf : IsProper B S hS f)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z) :
    IsFinite B S hS (Z.ι ≫ f) ↔
      ∀ y : points B S hS (yoneda.obj V),
        {x : points B S hS X |
          x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) ∧
            pointsMap B S hS X f x = y}.Finite := by
  have hprop : IsProper B S hS (Z.ι ≫ f) :=
    isProper_comp B S hS hZ.1 hX (isAlgebraicSpace_yoneda B S hS V) _ _
      (isProper_of_isClosedImmersion B S hS hZ.1 hX Z.ι hZ.2) hf
  rw [isFinite_iff_forall_finite_fibre_of_isProper B S hS hZ.1 _ hprop]
  exact forall_congr' fun y => (finite_fibre_range_iff_of_isClosedSubspace B S hS Z hZ f y).symm

end AlgebraicGeometry.Space

end
