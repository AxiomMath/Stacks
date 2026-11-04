module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.AdjointTripleUnitSplit
public import StacksFrontier.CategoryTheory.Adjunction.CounitSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Splitting the counit `f^*f_*ℱ ⟶ ℱ` along the diagonal of an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `ℱ` be an `𝒪_X`-module, let `p, q : X ×_Y X ⟶ X` be the two projections of the
fibre square of `f` with itself and `Δ : X ⟶ X ×_Y X` its relative diagonal. Then
`f^*f_*ℱ ≅ q_*p^*ℱ` and `q_*Δ_*Δ^*p^*ℱ ≅ ℱ`, and the counit `f^*f_*ℱ ⟶ ℱ` of the adjunction
`f^* ⊣ f_*` is a split epimorphism as soon as the unit `p^*ℱ ⟶ Δ_*Δ^*p^*ℱ` is; in particular, for
`f` separated, as soon as the restriction `Δ^*` has a left adjoint `Δ_!` isomorphic to `Δ_*`.

## Main definitions

* `AlgebraicGeometry.Space.selfFibreSquare`, `AlgebraicGeometry.Space.selfFibreFst`,
  `AlgebraicGeometry.Space.selfFibreSnd` and `AlgebraicGeometry.Space.selfFibreDiagonal`: the
  fibre square `X ×_Y X` of `f` with itself, its two projections and its relative diagonal.
* `AlgebraicGeometry.Space.counitSourceIso`: the identification `f^*f_*ℱ ≅ q_*p^*ℱ`.
* `AlgebraicGeometry.Space.diagonalRetractIso`: the identification `q_*Δ_*Δ^*p^*ℱ ≅ ℱ`.
* `AlgebraicGeometry.Space.diagonalUnit`: the unit `p^*ℱ ⟶ Δ_*Δ^*p^*ℱ`.

## Main results

* `AlgebraicGeometry.Space.isEtale_selfFibreFst`,
  `AlgebraicGeometry.Space.isEtale_selfFibreSnd` and
  `AlgebraicGeometry.Space.isEtale_selfFibreDiagonal`: the two projections and the diagonal of
  the fibre square of an étale morphism are étale.
* `AlgebraicGeometry.Space.diagonalEtalePullbackFstIso` and
  `AlgebraicGeometry.Space.diagonalPushforwardSndIso`: `Δ^*p^* ≅ 𝟭` and `Δ_* ⋙ q_* ≅ 𝟭`.
* `AlgebraicGeometry.Space.fullyFaithfulDiagonalPushforward`: for `f` separated the direct image
  along the diagonal is fully faithful.
* `AlgebraicGeometry.Space.counitSplitEpiOfSplitEpiDiagonalUnit`: the counit `f^*f_*ℱ ⟶ ℱ` is a
  split epimorphism if the unit `p^*ℱ ⟶ Δ_*Δ^*p^*ℱ` is.
* `AlgebraicGeometry.Space.counitSplitEpiOfDiagonalShriekIso`: for `f` separated, the counit
  `f^*f_*ℱ ⟶ ℱ` is a split epimorphism if `Δ^*` has a left adjoint isomorphic to `Δ_*`.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The fibre square of a morphism with itself -/

/-- The fibre square `X ×_Y X` of a morphism of algebraic spaces with itself. -/
noncomputable abbrev selfFibreSquare (f : X ⟶ Y) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f f

/-- The first projection `p : X ×_Y X ⟶ X`. -/
noncomputable abbrev selfFibreFst (f : X ⟶ Y) : selfFibreSquare B S hS f ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom f.hom)

/-- The second projection `q : X ×_Y X ⟶ X`. -/
noncomputable abbrev selfFibreSnd (f : X ⟶ Y) : selfFibreSquare B S hS f ⟶ X :=
  ObjectProperty.homMk (pullback.snd f.hom f.hom)

/-- The relative diagonal `Δ : X ⟶ X ×_Y X`. -/
noncomputable abbrev selfFibreDiagonal (f : X ⟶ Y) : X ⟶ selfFibreSquare B S hS f :=
  ObjectProperty.homMk (pullback.diagonal f.hom)

/-- The two projections exhibit `X ×_Y X` as the fibre product of `f` with itself in the
category of algebraic spaces over `S`. -/
theorem isPullback_selfFibreSquare (f : X ⟶ Y) :
    IsPullback (selfFibreFst B S hS f) (selfFibreSnd B S hS f) f f :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS f f

/-- The first projection of the fibre square of an étale morphism with itself is étale, being a
base change of that morphism. -/
theorem isEtale_selfFibreFst (f : X ⟶ Y) (het : IsEtale B S hS f.hom) :
    IsEtale B S hS (selfFibreFst B S hS f).hom :=
  isEtale_of_isPullback B S hS (selfFibreSnd B S hS f) (selfFibreFst B S hS f) f f
    (isPullback_selfFibreSquare B S hS f).flip het

/-- The second projection of the fibre square of an étale morphism with itself is étale, being a
base change of that morphism. -/
theorem isEtale_selfFibreSnd (f : X ⟶ Y) (het : IsEtale B S hS f.hom) :
    IsEtale B S hS (selfFibreSnd B S hS f).hom :=
  isEtale_of_isPullback B S hS (selfFibreFst B S hS f) (selfFibreSnd B S hS f) f f
    (isPullback_selfFibreSquare B S hS f) het

/-- The diagonal is a section of the first projection. -/
theorem selfFibreDiagonal_comp_fst (f : X ⟶ Y) :
    selfFibreDiagonal B S hS f ≫ selfFibreFst B S hS f = 𝟙 X :=
  ObjectProperty.hom_ext _ (pullback.diagonal_fst f.hom)

/-- The diagonal is a section of the second projection. -/
theorem selfFibreDiagonal_comp_snd (f : X ⟶ Y) :
    selfFibreDiagonal B S hS f ≫ selfFibreSnd B S hS f = 𝟙 X :=
  ObjectProperty.hom_ext _ (pullback.diagonal_snd f.hom)

/-- **The relative diagonal of an étale morphism of algebraic spaces is étale.** -/
theorem isEtale_selfFibreDiagonal (f : X ⟶ Y) (het : IsEtale B S hS f.hom) :
    IsEtale B S hS (selfFibreDiagonal B S hS f).hom :=
  isEtale_of_isEtale_over B S hS X.property (selfFibreSquare B S hS f).property X.property
    (pullback.diagonal f.hom) (𝟙 X.1) (pullback.fst f.hom f.hom)
    (isEtale_id B S hS X.1) (isEtale_selfFibreFst B S hS f het)
    (pullback.diagonal_fst f.hom)

/-- The composite of the diagonal with the first projection is étale, being the identity. -/
theorem isEtale_selfFibreDiagonal_comp_fst (f : X ⟶ Y) :
    IsEtale B S hS (selfFibreDiagonal B S hS f ≫ selfFibreFst B S hS f).hom := by
  rw [selfFibreDiagonal_comp_fst]
  exact isEtale_id B S hS X.1

/-! ### The two consequences of the diagonal being a section -/

/-- **`Δ^*p^* ≅ 𝟭`**: restricting to the fibre square along the first projection and then along
the diagonal is isomorphic to the identity. -/
noncomputable def diagonalEtalePullbackFstIso (f : X ⟶ Y) (het : IsEtale B S hS f.hom) :
    etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
          (isEtale_selfFibreFst B S hS f het) ⋙
        etaleModulePullback.{u, u} B S hS (selfFibreDiagonal B S hS f)
          (isEtale_selfFibreDiagonal B S hS f het) ≅
      𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  etaleModulePullbackCompIso B S hS (selfFibreDiagonal B S hS f) (selfFibreFst B S hS f)
      (isEtale_selfFibreDiagonal B S hS f het) (isEtale_selfFibreFst B S hS f het)
      (isEtale_selfFibreDiagonal_comp_fst B S hS f) ≪≫
    eqToIso (etaleModulePullback_congr B S hS (isEtale_selfFibreDiagonal_comp_fst B S hS f)
      (isEtale_id B S hS X.1) (selfFibreDiagonal_comp_fst B S hS f)) ≪≫
    etaleModulePullbackIdIso.{u, u} B S hS (isEtale_id B S hS X.1)

/-- **`Δ_* ⋙ q_* ≅ 𝟭`**: the direct image along the diagonal followed by the direct image along
the second projection is isomorphic to the identity. -/
noncomputable def diagonalPushforwardSndIso (f : X ⟶ Y) :
    modulePushforward B S hS (selfFibreDiagonal B S hS f) ⋙
        modulePushforward B S hS (selfFibreSnd B S hS f) ≅
      𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  modulePushforwardCompIso B S hS (selfFibreDiagonal B S hS f) (selfFibreSnd B S hS f) ≪≫
    eqToIso (congrArg (modulePushforward B S hS) (selfFibreDiagonal_comp_snd B S hS f)) ≪≫
    modulePushforwardIdIso B S hS X

/-! ### The two identifications, and the reduction -/

/-- **`f^*f_*ℱ ≅ q_*p^*ℱ`** for an étale morphism `f`: the étale base change isomorphism for the
fibre square of `f` with itself, composed with the identification of the pullback of modules with
étale restriction. -/
noncomputable def counitSourceIso (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).obj ((modulePushforward B S hS f).obj F) ≅
      (modulePushforward B S hS (selfFibreSnd B S hS f)).obj
        ((etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
          (isEtale_selfFibreFst B S hS f het)).obj F) :=
  (modulePullbackIsoEtaleModulePullback B S hS f het).app _ ≪≫
    ((modulePushforwardEtaleBaseChangeIso B S hS (selfFibreFst B S hS f)
      (selfFibreSnd B S hS f) f f (isPullback_selfFibreSquare B S hS f) het).app F).symm

/-- **`q_*Δ_*Δ^*p^*ℱ ≅ ℱ`** for the relative diagonal `Δ` of the fibre square of `f` with
itself. -/
noncomputable def diagonalRetractIso (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS (selfFibreSnd B S hS f)).obj
        ((modulePushforward B S hS (selfFibreDiagonal B S hS f)).obj
          ((modulePullback B S hS (selfFibreDiagonal B S hS f)).obj
            ((etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
              (isEtale_selfFibreFst B S hS f het)).obj F))) ≅ F :=
  (diagonalPushforwardSndIso B S hS f).app _ ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS (selfFibreDiagonal B S hS f)
      (isEtale_selfFibreDiagonal B S hS f het)).app _ ≪≫
    (diagonalEtalePullbackFstIso B S hS f het).app F

/-- **The unit `p^*ℱ ⟶ Δ_*Δ^*p^*ℱ` of the adjunction `Δ^* ⊣ Δ_*` along the diagonal**, at the
restriction of `ℱ` to the fibre square along the first projection. -/
noncomputable def diagonalUnit (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
        (isEtale_selfFibreFst B S hS f het)).obj F ⟶
      (modulePushforward B S hS (selfFibreDiagonal B S hS f)).obj
        ((modulePullback B S hS (selfFibreDiagonal B S hS f)).obj
          ((etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
            (isEtale_selfFibreFst B S hS f het)).obj F)) :=
  (modulePullbackAdjunction B S hS (selfFibreDiagonal B S hS f)).unit.app
    ((etaleModulePullback.{u, u} B S hS (selfFibreFst B S hS f)
      (isEtale_selfFibreFst B S hS f het)).obj F)

/-- **The counit splits if the unit along the diagonal splits.**  Let `f : X ⟶ Y` be an étale
morphism of algebraic spaces and `ℱ` an `𝒪_X`-module.  If the unit `p^*ℱ ⟶ Δ_*Δ^*p^*ℱ` of the
diagonal of the fibre square of `f` with itself is a split epimorphism, then so is the counit
`f^*f_*ℱ ⟶ ℱ` of the adjunction `f^* ⊣ f_*`. -/
noncomputable def counitSplitEpiOfSplitEpiDiagonalUnit (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hsplit : SplitEpi (diagonalUnit B S hS f het F)) :
    SplitEpi ((modulePullbackAdjunction B S hS f).counit.app F) :=
  Stacks.Adjunction.splitEpiCounitOfIsoRetract (modulePullbackAdjunction B S hS f)
    (counitSourceIso B S hS f het F) (diagonalRetractIso B S hS f het F)
    ((modulePushforward B S hS (selfFibreSnd B S hS f)).map hsplit.section_)
    ((modulePushforward B S hS (selfFibreSnd B S hS f)).map (diagonalUnit B S hS f het F))
    (by rw [← Functor.map_comp, hsplit.id]; exact CategoryTheory.Functor.map_id _ _)

/-- For a separated morphism of algebraic spaces the direct image of modules along the relative
diagonal is fully faithful. -/
noncomputable def fullyFaithfulDiagonalPushforward (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) :
    (modulePushforward B S hS (selfFibreDiagonal B S hS f)).FullyFaithful :=
  fullyFaithfulModulePushforward B S hS (selfFibreDiagonal B S hS f) hsep

/-- **The counit splits given an extension by zero along the diagonal.**  Let `f : X ⟶ Y` be a
separated étale morphism of algebraic spaces and `ℱ` an `𝒪_X`-module.  Given any left adjoint
`Δ_!` of the restriction `Δ^*` along the relative diagonal, together with an isomorphism
`Δ_! ≅ Δ_*`, the counit `f^*f_*ℱ ⟶ ℱ` of the adjunction `f^* ⊣ f_*` is a split epimorphism. -/
noncomputable def counitSplitEpiOfDiagonalShriekIso (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    {shriek : Modules.{u, u} B S hS X.1 X.2 ⥤
      Modules.{u, u} B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2}
    (adjShriek : shriek ⊣ modulePullback B S hS (selfFibreDiagonal B S hS f))
    (θ : shriek ≅ modulePushforward B S hS (selfFibreDiagonal B S hS f)) :
    SplitEpi ((modulePullbackAdjunction B S hS f).counit.app F) :=
  have hH := fullyFaithfulDiagonalPushforward B S hS f hsep
  have := hH.full
  have := hH.faithful
  have : shriek.Full := Functor.Full.of_iso θ.symm
  have : shriek.Faithful := Functor.Faithful.of_iso θ.symm
  counitSplitEpiOfSplitEpiDiagonalUnit B S hS f het F
    (Adjunction.Triple.splitEpiUnitOfIso
      { adj₁ := adjShriek
        adj₂ := modulePullbackAdjunction B S hS (selfFibreDiagonal B S hS f) } θ _)

end AlgebraicGeometry.Space

end
