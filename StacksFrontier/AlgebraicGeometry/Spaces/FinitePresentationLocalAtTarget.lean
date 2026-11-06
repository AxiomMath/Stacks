module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints

/-!
# Finite presentation of morphisms of algebraic spaces is Zariski local on the target

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` and let `U` be a Zariski covering of `Y` by open subspaces in the
sense of Stacks 02YY. Then `f` is of finite presentation exactly when each of its base changes
`f⁻¹(U i) ⟶ U i` is, and the same holds for local finite presentation alone.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_forall_zariskiCover`: local finite
  presentation is Zariski local on the target.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_forall_zariskiCover`: finite presentation is
  Zariski local on the target.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_union_eq_univ`: the same for a covering by
  two open subspaces.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_fpLocal :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_fpLocal
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_fpLocal B S hS).has_limit _

/-- The base change of a morphism locally of finite presentation along an open immersion is
locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_pullback_snd_of_isOpenImmersion
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : IsOpenImmersion B S hS g)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS (pullback.snd f g) :=
  holdsOnEveryEtaleChart_of_isPullback B S hS (IsPullback.of_hasPullback f g).flip
    (presheaf_etale_of_isOpenImmersion B S hS hg) hf

/-- The base change of a morphism of finite presentation along an open immersion is of finite
presentation. -/
theorem isFinitePresentation_pullback_snd_of_isOpenImmersion
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : IsOpenImmersion B S hS g)
    (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B S hS (pullback.snd f g) :=
  ⟨isLocallyOfFinitePresentation_pullback_snd_of_isOpenImmersion B S hS f g hg hf.1,
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf.2.1,
    isQuasiSeparated_pullback_snd B S hS f g hf.2.2⟩

/-- Local finite presentation of a morphism of algebraic spaces over `S` descends along a
Zariski covering of the target: if the base change of `f` over every member of the covering is
locally of finite presentation, then so is `f`. -/
theorem isLocallyOfFinitePresentation_of_zariskiCover
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsLocallyOfFinitePresentation B S hS (pullback.snd f (U i).ι)) :
    IsLocallyOfFinitePresentation B S hS f := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  refine ((isLocallyOfFinitePresentation_tfae B S hS hX hY f).out 9 1).mp ?_
  refine ⟨I, U, fun _ => PUnit.{u + 1}, fun _ _ => ⊤, hU, fun i => ?_, fun i _ => ?_⟩ <;>
    have halg : IsAlgebraicSpace B S hS (pullback f (U i).ι) :=
      isAlgebraicSpace_pullback B S hS f (U i).ι hX (hU.1 i).1 hY
  · exact isZariskiCover_top halg
  · intro V W a b k ha hb hcomm
    refine h i V W (a ≫ Subfunctor.ι ⊤) b k
      (MorphismProperty.comp_mem _ a _ ha
        (presheaf_etale_of_isOpenImmersion B S hS (isOpenSubspace_top halg).2)) hb ?_
    rw [hcomm, Category.assoc]

/-- A morphism of algebraic spaces over `S` is locally of finite presentation exactly when its
base change over every member of a Zariski covering of the target is. -/
theorem isLocallyOfFinitePresentation_iff_forall_zariskiCover
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U) :
    IsLocallyOfFinitePresentation B S hS f ↔
      ∀ i, IsLocallyOfFinitePresentation B S hS (pullback.snd f (U i).ι) :=
  ⟨fun hf i => isLocallyOfFinitePresentation_pullback_snd_of_isOpenImmersion B S hS f _
      (hU.1 i).2 hf,
    isLocallyOfFinitePresentation_of_zariskiCover B S hS hX hY f hU⟩

/-- Finite presentation of a morphism of algebraic spaces over `S` descends along a Zariski
covering of the target: if the base change of `f` over every member of the covering is of
finite presentation, then so is `f`. -/
theorem isFinitePresentation_of_zariskiCover
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsFinitePresentation B S hS (pullback.snd f (U i).ι)) :
    IsFinitePresentation B S hS f :=
  ⟨isLocallyOfFinitePresentation_of_zariskiCover B S hS hX hY f hU fun i => (h i).1,
    isQuasiCompact_of_zariskiCover B S hS f hX hY U hU.1
      (fun y => Set.iUnion_eq_univ_iff.1
        ((isZariskiCover_iff_iUnion_points B S hS Y hY I U hU.1).1 hU) y)
      (fun i => (h i).2.1),
    isQuasiSeparated_of_zariskiCover B S hS hX hU fun i => (h i).2.2⟩

/-- A morphism of algebraic spaces over `S` is of finite presentation exactly when its base
change over every member of a Zariski covering of the target is. -/
theorem isFinitePresentation_iff_forall_zariskiCover
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U) :
    IsFinitePresentation B S hS f ↔
      ∀ i, IsFinitePresentation B S hS (pullback.snd f (U i).ι) :=
  ⟨fun hf i => isFinitePresentation_pullback_snd_of_isOpenImmersion B S hS f _ (hU.1 i).2 hf,
    isFinitePresentation_of_zariskiCover B S hS hX hY f hU⟩

/-- Two open subspaces of an algebraic space whose point sets exhaust it form a Zariski
covering of it, indexed by `ULift.{u} Bool`. -/
theorem isZariskiCover_uliftBool_of_union_eq_univ
    (hY : IsAlgebraicSpace B S hS Y) {U W : Subfunctor Y}
    (hU : IsOpenSubspace B S hS U) (hW : IsOpenSubspace B S hS W)
    (hcov : Set.range (pointsMap B S hS U.toFunctor U.ι) ∪
      Set.range (pointsMap B S hS W.toFunctor W.ι) = Set.univ) :
    IsZariskiCover B S hS (ULift.{u} Bool) fun i => if i.down then U else W := by
  have hopen : ∀ i : ULift.{u} Bool,
      IsOpenSubspace B S hS (if i.down then U else W) := by
    rintro ⟨_ | _⟩ <;> simpa using ‹_›
  refine (isZariskiCover_iff_iUnion_points B S hS Y hY _ _ hopen).2 ?_
  refine Set.iUnion_eq_univ_iff.2 fun y => ?_
  rcases Set.eq_univ_iff_forall.1 hcov y with hy | hy
  · exact ⟨⟨true⟩, by simpa using hy⟩
  · exact ⟨⟨false⟩, by simpa using hy⟩

/-- If `U` and `W` are open subspaces of `Y` whose point sets exhaust it, then `f : X ⟶ Y` is of
finite presentation exactly when both of its base changes over `U` and over `W` are. -/
theorem isFinitePresentation_iff_union_eq_univ
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {U W : Subfunctor Y} (hU : IsOpenSubspace B S hS U) (hW : IsOpenSubspace B S hS W)
    (hcov : Set.range (pointsMap B S hS U.toFunctor U.ι) ∪
      Set.range (pointsMap B S hS W.toFunctor W.ι) = Set.univ) :
    IsFinitePresentation B S hS f ↔
      IsFinitePresentation B S hS (pullback.snd f U.ι) ∧
        IsFinitePresentation B S hS (pullback.snd f W.ι) := by
  rw [isFinitePresentation_iff_forall_zariskiCover B S hS hX hY f
    (isZariskiCover_uliftBool_of_union_eq_univ B S hS hY hU hW hcov)]
  exact ⟨fun h => ⟨h ⟨true⟩, h ⟨false⟩⟩, by rintro ⟨h₁, h₂⟩ ⟨_ | _⟩ <;> simpa using ‹_›⟩

end AlgebraicGeometry.Space

end
