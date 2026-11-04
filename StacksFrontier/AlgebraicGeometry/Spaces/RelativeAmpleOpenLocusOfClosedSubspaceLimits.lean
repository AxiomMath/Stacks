module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistAndNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedFinitePresentationEmbeddingOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfCutoffBoundedSystem

/-!
# Stacks 0A0X and Stacks 0D3D from Stacks 0872, 0A0U and 08K1

This file proves absolute Noetherian approximation of a proper morphism of quasi-compact and
quasi-separated algebraic spaces over `Spec ℤ` (Stacks 0A0X), and the existence of the open locus
where an invertible module is relatively ample (Stacks 0D3D), assuming Stacks 0872, Stacks 0A0U
and Stacks 08K1 over the integers, given as the hypotheses `h0872`, `h0A0U` and `h08K1`.

## Main results

* `Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_closedSubspaceLimits`:
  Stacks 0A0X from Stacks 0872, 0A0U and 08K1.
* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_closedSubspaceLimits`:
  Stacks 0D3D from Stacks 0872, 0A0U and 08K1.

## References

* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0A0X, from Stacks 0872, 0A0U and 08K1.** Let `f : X ⟶ Y` be a proper morphism of
quasi-compact and quasi-separated algebraic spaces over `Spec ℤ`. Then `f` is the limit of a
directed system of proper morphisms of finite presentation `X_i ⟶ Y_i` between algebraic spaces
of finite presentation over `Spec ℤ`, the systems `X_i` and `Y_i` having affine transition
morphisms.

The hypotheses `h0872`, `h0A0U` and `h08K1` are Stacks 0872, Stacks 0A0U and Stacks 08K1 for a
system bounded by the cutoff, over the integers. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_closedSubspaceLimits
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0872 : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      IsAlgebraicSpace B _ hZ Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B _ hZ f →
      IsQuasiCompactSpace B _ hZ X → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal X →
      IsQuasiCompactSpace B _ hZ Y → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B _ hZ X' ∧ IsClosedImmersion B _ hZ i ∧
          IsFinitePresentation B _ hZ f' ∧ i ≫ f' = f)
    (h0A0U : ∀ (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ), IsQuasiCompactSpace B _ hZ Y.1 →
      IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B _ hZ f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B _ hZ Y.1) (hZle : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B _ hZ
          ((closedSubspaceDiagram B _ hZ (fun i => (Z i).1) hZle).map g)) ∧
        (∀ i, IsClosedImmersion B _ hZ (Z i).1.ι ∧ IsFinitePresentation B _ hZ (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B _ hZ (fun i => (Z i).1) hZle (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B _ hZ (fun i => (Z i).1) hZle
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f))))
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
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) :=
  exists_isLimit_isProper_isFinitePresentation_arrow_of_isCutoffBoundedSystem hZ
    (fun hX hY f hf hYqc hYqs =>
      exists_isLimit_isProper_isFinitePresentation_of_embedding_of_closedSubspaceLimits B _ hZ
        h0872 h0A0U hX hY f hf hYqc hYqs)
    h08K1 hX hY f hf hYqc hYqs

/-- **Stacks 0D3D, from Stacks 0872, 0A0U and 08K1.** Let `S` be a scheme, `f : X ⟶ Y` a proper
morphism of algebraic spaces over `S` and `L` an invertible `𝒪_X`-module. There is an open
subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces factors through `V` if and
only if the pullback of `L` to `X' = Y' ×_Y X` is ample on `X'/Y'` (Stacks 0D31).

The hypotheses `h0872`, `h0A0U` and `h08K1` are Stacks 0872, Stacks 0A0U and Stacks 08K1 for a
system bounded by the cutoff, over the integers. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_closedSubspaceLimits
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0872 : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      IsAlgebraicSpace B _ hZ Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B _ hZ f →
      IsQuasiCompactSpace B _ hZ X → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal X →
      IsQuasiCompactSpace B _ hZ Y → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B _ hZ X' ∧ IsClosedImmersion B _ hZ i ∧
          IsFinitePresentation B _ hZ f' ∧ i ≫ f' = f)
    (h0A0U : ∀ (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ), IsQuasiCompactSpace B _ hZ Y.1 →
      IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y.1 →
      ∀ {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      ∀ (f : X ⟶ Y.1),
      IsClosedImmersion B _ hZ f →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (Z : I → ClosedSubspaces B _ hZ Y.1) (hZle : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
        (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
        (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B _ hZ
          ((closedSubspaceDiagram B _ hZ (fun i => (Z i).1) hZle).map g)) ∧
        (∀ i, IsClosedImmersion B _ hZ (Z i).1.ι ∧ IsFinitePresentation B _ hZ (Z i).1.ι) ∧
        (∀ i, ((closedSubspaceCone B _ hZ (fun i => (Z i).1) hZle (Subfunctor.range f)
          hle).extend (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
        Nonempty (IsLimit ((closedSubspaceCone B _ hZ (fun i => (Z i).1) hZle
          (Subfunctor.range f) hle).extend (Subfunctor.toRange f))))
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
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isCutoffBoundedSystem hZ
    (fun hX hY f hf hYqc hYqs =>
      exists_isLimit_isProper_isFinitePresentation_of_embedding_of_closedSubspaceLimits B _ hZ
        h0872 h0A0U hX hY f hf hYqc hYqs)
    h08K1
    (fun _ hT {_} fᵢ hfᵢ Lᵢ hLᵢ y hy => have := hT
      exists_mem_isRelativelyAmple_openSub_of_forall_isRelativelyAmple_residueField fᵢ hfᵢ Lᵢ hLᵢ y
        hy)
    hf hL

end AlgebraicGeometry.Space

end
