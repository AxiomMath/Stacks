module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartWSystemOfCutoffBoundedApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfCutoffBoundedWSystems

/-!
# Stacks 0D3D under the cutoff bound, from Stacks 0A0W, 08K1 and 0D3A

`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedWSystems`
proves the statement of Stacks 0D3D from the W-systems of Stacks 07SU over approximations bounded by
the cutoff (`hW`), Stacks 0A0W (`h0A0W`), Stacks 08K1 for systems bounded by the cutoff (`h08K1`)
and Stacks 0D3A (`h0D3A`). The first input is now
`AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`; this file records the statement
with it discharged.

## Main results

* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isCutoffBoundedSystem`:
  the statement of Stacks 0D3D from `h0A0W`, `h08K1` and `h0D3A`.

## Implementation notes

The three hypotheses are inputs still owed elsewhere: `h0A0W` and `h08K1` are the inputs of the
0A0X assembly, and `h0D3A` is Stacks 0D3A at a residue field. Nothing here is registered.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D3D under the cutoff bound, from Stacks 0A0W, 08K1 and 0D3A.** Let `S` be a scheme,
`f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L` an invertible `𝒪_X`-module.
There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces factors
through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is ample on `X'/Y'`
(Stacks 0D31).

This is
`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedWSystems`
with its input `hW` supplied by `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`.
The hypotheses are the inputs still owed, all over the integers: `h0A0W`, Stacks 0A0W; `h08K1`,
Stacks 08K1 for a system bounded by the cutoff; and `h0D3A`, Stacks 0D3A at a residue field over a
Noetherian scheme of the site. It is not registered. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isCutoffBoundedSystem
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ schemeSpace T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ schemeSpace (residueFieldObject B _ hZ T y
              (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (schemeSpaceMap
              (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ schemeSpace (openSub T V)),
            IsPullback p₁ f₁ fᵢ (schemeSpaceMap (openSubHom T V)) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ))
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :=
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedWSystems hZ
    (ElementaryChart.hasCutoffBoundedWSystems B hZ) h0A0W h08K1 h0D3A hf hL

end AlgebraicGeometry.Space

end
