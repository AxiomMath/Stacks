module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedFinitePresentationEmbeddingOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfClosedSubspaceLimits

/-!
# Proper morphisms of algebraic spaces as limits of morphisms of finite presentation

Consequences of the factorization of a morphism locally of finite type between quasi-compact and
quasi-separated algebraic spaces as a closed immersion followed by a morphism of finite
presentation: separated morphisms of finite type embed into separated morphisms of finite
presentation, proper morphisms are limits of proper morphisms of finite presentation, and the
locus over which an invertible module is relatively ample is open.

## Main results

* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_finitePresentationEmbedding`,
  `exists_isLimit_isProper_isFinitePresentation_of_finitePresentationEmbedding`,
  `exists_isLimit_isProper_isFinitePresentation_arrow_of_finitePresentationEmbedding` and
  `exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_finitePresentationEmbedding`: the four
  results below, assuming the factorization as the hypothesis `h0872`.
* `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType`: a separated
  morphism of finite type with quasi-compact and quasi-separated target is a closed immersion
  followed by a separated morphism of finite presentation.
* `AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_of_isProper`: for a proper
  `f : X ⟶ Y` with `Y` quasi-compact and quasi-separated, `X` is a directed limit along closed
  immersions of algebraic spaces proper and of finite presentation over `Y`.
* `AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_isProper`: a
  proper morphism over `Spec ℤ` with quasi-compact and quasi-separated target is a directed limit
  of proper morphisms of finite presentation between algebraic spaces of finite presentation.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`: for
  a proper `f : X ⟶ Y` and an invertible `𝒪_X`-module `L`, the base changes of `f` on which the
  pullback of `L` is relatively ample are those factoring through an open subspace of `Y`.

## References

* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Assume that every morphism locally of finite type between quasi-compact and quasi-separated
algebraic spaces over `S` is a closed immersion followed by a morphism of finite presentation
(`h0872`). Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`,
with `Y` quasi-compact and quasi-separated. Then there are a separated morphism of finite
presentation `f' : X' ⟶ Y` and a closed immersion `i : X ⟶ X'` with `i ≫ f' = f`. -/
theorem exists_isClosedImmersion_isSeparated_isFinitePresentation_of_finitePresentationEmbedding
    (h0872 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
      IsAlgebraicSpace B S hS Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B S hS f →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧
          IsFinitePresentation B S hS f' ∧ i ≫ f' = f)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hft : IsFiniteType B S hS f)
    (hsep : IsSeparated B S hS f) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f :=
  exists_isClosedImmersion_isSeparated_isFinitePresentation_of_embedding_of_closedSubspaceLimits
    B S hS h0872 (exists_isLimit_closedSubspaces_of_isClosedImmersion B S hS B.contains_terminal)
    hX hY f hft hsep hYqc hYqs

/-- Assume that every morphism locally of finite type between quasi-compact and quasi-separated
algebraic spaces over `S` is a closed immersion followed by a morphism of finite presentation
(`h0872`). Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated. Then `X` is the directed limit, along closed immersions and over
`Y`, of algebraic spaces proper and of finite presentation over `Y`, the projections from `X` being
closed immersions. -/
theorem exists_isLimit_isProper_isFinitePresentation_of_finitePresentationEmbedding
    (h0872 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
      IsAlgebraicSpace B S hS Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B S hS f →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧
          IsFinitePresentation B S hS f' ∧ i ≫ f' = f)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
      (∀ i, IsProper B S hS (t.app i) ∧ IsFinitePresentation B S hS (t.app i)) ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B S hS (D.map e)) ∧
      (∀ i, IsClosedImmersion B S hS (π.app i)) ∧
      π ≫ t = (Functor.const Iᵒᵖ).map f ∧
      Nonempty (IsLimit (Cone.mk X π)) :=
  exists_isLimit_isProper_isFinitePresentation_of_embedding_of_closedSubspaceLimits B S hS h0872
    (exists_isLimit_closedSubspaces_of_isClosedImmersion B S hS B.contains_terminal)
    hX hY f hf hYqc hYqs

end General

section Integers

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Assume that every morphism locally of finite type between quasi-compact and quasi-separated
algebraic spaces over `Spec ℤ` is a closed immersion followed by a morphism of finite presentation
(`h0872`). Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `Spec ℤ`, with `Y`
quasi-compact and quasi-separated. Then `f` is the limit of a directed system of proper morphisms
of finite presentation `X_i ⟶ Y_i` between algebraic spaces of finite presentation over `Spec ℤ`,
the systems `X_i` and `Y_i` having affine transition morphisms. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_finitePresentationEmbedding
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0872 : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      IsAlgebraicSpace B _ hZ Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B _ hZ f →
      IsQuasiCompactSpace B _ hZ X → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal X →
      IsQuasiCompactSpace B _ hZ Y → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B _ hZ X' ∧ IsClosedImmersion B _ hZ i ∧
          IsFinitePresentation B _ hZ f' ∧ i ≫ f' = f)
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
  exists_isLimit_isProper_isFinitePresentation_arrow_of_closedSubspaceLimits hZ h0872
    (exists_isLimit_closedSubspaces_of_isClosedImmersion B _ hZ B.contains_terminal)
    (fun D hD hDalg haff _ => exists_isProper_pullbackMap_of_isCutoffBoundedSystem B _ hZ hZ D hD
      hDalg haff)
    hX hY f hf hYqc hYqs

/-- Assume that every morphism locally of finite type between quasi-compact and quasi-separated
algebraic spaces over `Spec ℤ` is a closed immersion followed by a morphism of finite presentation
(`h0872`). Let `S` be a scheme, `f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L`
an invertible `𝒪_X`-module. There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y`
of algebraic spaces factors through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is
ample on `X'/Y'` (Stacks 0D31). -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_finitePresentationEmbedding
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0872 : ∀ {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B _ hZ X →
      IsAlgebraicSpace B _ hZ Y → ∀ (f : X ⟶ Y), IsLocallyOfFiniteType B _ hZ f →
      IsQuasiCompactSpace B _ hZ X → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal X →
      IsQuasiCompactSpace B _ hZ Y → IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y →
      ∃ (X' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
        IsAlgebraicSpace B _ hZ X' ∧ IsClosedImmersion B _ hZ i ∧
          IsFinitePresentation B _ hZ f' ∧ i ≫ f' = f)
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
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_closedSubspaceLimits hZ h0872
    (exists_isLimit_closedSubspaces_of_isClosedImmersion B _ hZ B.contains_terminal)
    (fun D hD hDalg haff _ => exists_isProper_pullbackMap_of_isCutoffBoundedSystem B _ hZ hZ D hD
      hDalg haff)
    hf hL

end Integers

section Final

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated. Then there are a separated morphism of finite presentation
`f' : X' ⟶ Y` and a closed immersion `i : X ⟶ X'` with `i ≫ f' = f`. -/
@[stacks 0873]
theorem exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hft : IsFiniteType B S hS f)
    (hsep : IsSeparated B S hS f) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f :=
  exists_isClosedImmersion_isSeparated_isFinitePresentation_of_finitePresentationEmbedding B S hS
    (exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType B S hS)
    hX hY f hft hsep hYqc hYqs

/-- Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated. Then `X` is the directed limit, along closed immersions and over `Y`, of algebraic
spaces proper and of finite presentation over `Y`, the projections from `X` being closed
immersions. -/
@[stacks 0A0W]
theorem exists_isLimit_isProper_isFinitePresentation_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
      (∀ i, IsProper B S hS (t.app i) ∧ IsFinitePresentation B S hS (t.app i)) ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B S hS (D.map e)) ∧
      (∀ i, IsClosedImmersion B S hS (π.app i)) ∧
      π ≫ t = (Functor.const Iᵒᵖ).map f ∧
      Nonempty (IsLimit (Cone.mk X π)) :=
  exists_isLimit_isProper_isFinitePresentation_of_finitePresentationEmbedding B S hS
    (exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType B S hS)
    hX hY f hf hYqc hYqs

/-- Let `S` be a scheme, `f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L` an
invertible `𝒪_X`-module. There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of
algebraic spaces factors through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is ample
on `X'/Y'` (Stacks 0D31). -/
@[stacks 0D3D]
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper
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
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_finitePresentationEmbedding
    B.contains_terminal
    (exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType B _ B.contains_terminal)
    hf hL

end Final

section FinalIntegers

variable (B : BigFppfSite.{u})

/-- Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `Spec ℤ`, with `Y`
quasi-compact and quasi-separated. Then `f` is the limit of a directed system of proper morphisms
of finite presentation `X_i ⟶ Y_i` between algebraic spaces of finite presentation over `Spec ℤ`,
the systems `X_i` and `Y_i` having affine transition morphisms. -/
@[stacks 0A0X]
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u}))
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
  exists_isLimit_isProper_isFinitePresentation_arrow_of_finitePresentationEmbedding hZ
    (exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType B _ hZ)
    hX hY f hf hYqc hYqs

end FinalIntegers

end AlgebraicGeometry.Space

end
