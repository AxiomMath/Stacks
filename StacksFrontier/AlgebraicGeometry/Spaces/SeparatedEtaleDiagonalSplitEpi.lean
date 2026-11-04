module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalSplitUnit

/-!
# Stacks 0HAP: the counit `f^*f_*ℱ ⟶ ℱ` of a separated étale morphism is split

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `ℱ` be an `𝒪_X`-module.  This file proves that the counit
`f^*f_*ℱ ⟶ ℱ` of the adjunction of Stacks 03LU is a split epimorphism, which is Stacks 0HAP.

`StacksFrontier/AlgebraicGeometry/Spaces/EtalePushforwardSplitCounit.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedEtaleDiagonalPushforward.lean` reduce the
statement to the assertion that the unit `ℳ ⟶ Δ_*Δ^*ℳ` of the chart-level adjunction at the
relative diagonal is a split epimorphism, and
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedEtaleDiagonalSplitUnit.lean` constructs the
candidate splitting `AlgebraicGeometry.Space.diagonalExtendByZeroHom`, extension by zero across
the diagonal.  What is proved here is the identity

`diagonalExtendByZeroHom ≫ unit = 𝟙`,

and hence the tag.

## Main definitions

* `AlgebraicGeometry.Space.diagonalChartSharp`: the structure map of the *composite* chart
  functor `V ↦ (V ×_{X ×_Y X} X : (X ×_Y X)_étale)`, namely restriction of regular functions
  along the cartesian projection.
* `AlgebraicGeometry.Space.diagonalPushforwardRestrictIso`: the double restriction
  `Δ_*^{bc}Δ^*_{ét}` as the single restriction along that composite functor.
* `AlgebraicGeometry.Space.splitEpiDiagonalChartUnit`: extension by zero as a splitting of the
  chart-level unit.

## Main results

* `AlgebraicGeometry.Space.diagonalExtendByZeroHom_comp_unit`: **extension by zero splits the
  unit** `ℳ ⟶ Δ_*Δ^*ℳ` of the chart-level adjunction at the diagonal.
* `AlgebraicGeometry.Space.counitSplitEpiOfSeparatedEtale`: **Stacks 0HAP.**

## Implementation notes

The identity is chart-wise exactly `AlgebraicGeometry.Space.diagonalExtendByZero_res`: over an
étale chart `V` of `X ×_Y X` the unit is restriction of sections along the cartesian projection
`V ×_{X ×_Y X} X ⟶ V` (`AlgebraicGeometry.Space.diagonalChartHom`) by
`AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction_unit_app_val_app`, and extension by
zero is a section of that restriction.  Read naively, however, the two sides of the equation are
typed in the sections of the *double* restriction `Δ_*^{bc}(Δ^*_{ét}ℳ)`, which are the sections
of `ℳ` over the chart `V ×_{X ×_Y X} X` restricted along *two* ring maps — the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp` of base change and the identity structure map
`AlgebraicGeometry.Space.etaleRestrictionSharp` of étale restriction — whereas
`AlgebraicGeometry.Space.diagonalExtendByZero_res` is typed over the single ring map
`𝒪(V) ⟶ 𝒪(V ×_{X ×_Y X} X)`.  Those two readings of the scalars are equal only
*propositionally*, by `AlgebraicGeometry.Space.smallBaseChangeSharp_app_diagonalChartHom`, so
identifying them makes the elaborator try to unfold the chosen fibre products of
`CategoryTheory.Functor.relativelyRepresentable.pullback`, which are `Classical.choose`s, and
the comparison does not terminate within the heartbeat budget.

The fix is to make the two spellings of the scalars *syntactically* equal before the equation of
elements is ever stated.  `AlgebraicGeometry.Space.smallBaseChangeSharp_counit` is already an
equation of natural transformations saying that the composite of the two structure maps is
restriction along the counit; `SheafOfModules.pushforwardCongr` turns it into an isomorphism of
pushforward functors, and `SheafOfModules.pushforwardComp` (which is `Iso.refl`) collapses the
two restrictions into one.  Both isomorphisms are the identity on sections, by `rfl`
(`SheafOfModules.pushforwardCongr_hom_app_val_app`,
`SheafOfModules.pushforwardComp_hom_app_val_app`).  Transporting the equation across the
composite isomorphism therefore changes nothing on elements but states it over the single ring
map `𝒪(V) ⟶ 𝒪(V ×_{X ×_Y X} X)`, which is the one
`AlgebraicGeometry.Space.diagonalExtendByZero_res` is typed over; it then closes by `exact`.
The transport back to the original unit is `Stacks.Adjunction.splitEpiOfCompIsIso`.

`AlgebraicGeometry.Space.isContinuous_smallBaseChange_comp_smallEtalePostcomp` is stated with the
étaleness and representability of the morphism as arguments of the two chart functors rather
than derived inside from separatedness: as a local instance its arguments have to be determined
by unification with the goal, and a hypothesis occurring only inside a *proof* argument is not,
proof irrelevance letting the unifier succeed without assigning it.

Quasi-compactness of `f`, which Stacks 0HAP assumes, is not used: the splitting is constructed
from the clopen decomposition of the charts of `X ×_Y X` cut out by the diagonal, which needs
only that the diagonal is an open (`f` étale) and closed (`f` separated) immersion.  Nor is
quasi-coherence of `ℱ` used.  The statement proved here is therefore more general than the tag
in both respects.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace Stacks.Adjunction

/-- **Cancelling an isomorphism from a factorisation of the identity.**  If `Θ : P ≅ Q` and the
composite `s ≫ t` of `s : P ⟶ N` and `t : N ⟶ P` becomes the identity of `Q` after conjugating
by `Θ`, then it is the identity of `P`. -/
theorem eq_id_of_comp_iso {C : Type*} [CategoryTheory.Category C] {P Q N : C} (Θ : P ≅ Q)
    (s : P ⟶ N) (t : N ⟶ P) (h : Θ.inv ≫ s ≫ t ≫ Θ.hom = 𝟙 Q) : s ≫ t = 𝟙 P := by
  have h' : (s ≫ t) ≫ Θ.hom = Θ.hom :=
    (Category.assoc s t Θ.hom).trans ((Θ.inv_comp_eq.mp h).trans (Category.comp_id _))
  calc s ≫ t = ((s ≫ t) ≫ Θ.hom) ≫ Θ.inv := by
        rw [Category.assoc, Θ.hom_inv_id, Category.comp_id]
    _ = 𝟙 P := by rw [h', Θ.hom_inv_id]

end Stacks.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composite chart functor -/

section Continuity

variable {X Y : AlgebraicSpaces B S hS}

/-- **Base change of charts followed by postcomposition is continuous.**  For an étale
representable morphism `g : X ⟶ Y` of algebraic spaces the composite `V ↦ (V ×_Y X : Y_étale)`
of the functors of Stacks 03G2, part (4) and Stacks 03LP is a continuous functor of the small
étale site of `Y` to itself, being a composite of two continuous functors. -/
theorem isContinuous_smallBaseChange_comp_smallEtalePostcomp (g : X ⟶ Y)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom) :
    (smallBaseChange B S hS g hrep ⋙ smallEtalePostcomp B S hS g hg).IsContinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS X.1) _

end Continuity

attribute [local instance] isContinuous_smallBaseChange_comp_smallEtalePostcomp

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
  (hsep : IsSeparated B S hS f.hom)
  (M : Modules.{u, u} B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2)

/-- **The structure map of the composite chart functor at the diagonal:** restriction of regular
functions along the cartesian projection `V ×_{X ×_Y X} X ⟶ V`, which is the counit of
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction`. -/
noncomputable def diagonalChartSharp :
    smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1 (selfFibreSquare B S hS f).2 ⟶
      ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
              (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) ⋙
            smallEtalePostcomp B S hS (selfFibreDiagonal B S hS f)
              (isEtale_selfFibreDiagonal B S hS f het)).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS (selfFibreSquare B S hS f).1)
          (SmallEtale.topology B S hS (selfFibreSquare B S hS f).1)).obj
        (smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1
          (selfFibreSquare B S hS f).2) where
  hom := Functor.whiskerRight (NatTrans.op (smallEtalePostcompBaseChangeAdjunction B S hS
      (selfFibreDiagonal B S hS f) (isEtale_selfFibreDiagonal B S hS f het)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).counit)
    (smallEtaleRingSheaf B S hS (selfFibreSquare B S hS f).1
      (selfFibreSquare B S hS f).2).obj

/-- **The two structure maps of the double restriction compose to the structure map of the
composite chart functor.**  This is `AlgebraicGeometry.Space.smallBaseChangeSharp_counit`, read
at the diagonal and as an equation of morphisms of sheaves of rings. -/
theorem smallBaseChangeSharp_comp_etaleRestrictionRingMap :
    smallBaseChangeSharp B S hS (selfFibreDiagonal B S hS f)
          (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) ≫
        ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
            (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B S hS (selfFibreSquare B S hS f).1)
            (SmallEtale.topology B S hS X.1)).map
          (etaleRestrictionSharp B S hS (selfFibreDiagonal B S hS f)
            (isEtale_selfFibreDiagonal B S hS f het)) =
      diagonalChartSharp B S hS f het hsep :=
  Sheaf.hom_ext (smallBaseChangeSharp_counit B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).symm

/-- **`Δ_*^{bc}Δ^*_{ét}` is the restriction along the composite chart functor.**  Restriction of
modules along the diagonal is `SheafOfModules.pushforward` for the identity structure map and
its chart-level direct image is `SheafOfModules.pushforward` for the structure map of base
change, so the composite is the pushforward for the composite functor and the composite
structure map (`SheafOfModules.pushforwardComp`), which is
`AlgebraicGeometry.Space.diagonalChartSharp` by
`AlgebraicGeometry.Space.smallBaseChangeSharp_comp_etaleRestrictionRingMap`.

Both isomorphisms are the identity on sections; the point of the identification is that it
replaces two successive restrictions of scalars by one, see the implementation notes. -/
noncomputable def diagonalPushforwardRestrictIso :
    SheafOfModules.pushforward.{u} (etaleRestrictionSharp B S hS
          (selfFibreDiagonal B S hS f) (isEtale_selfFibreDiagonal B S hS f het)) ⋙
        SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS
          (selfFibreDiagonal B S hS f)
          (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)) ≅
      SheafOfModules.pushforward.{u} (diagonalChartSharp B S hS f het hsep) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr
      (smallBaseChangeSharp_comp_etaleRestrictionRingMap B S hS f het hsep)

/-- `Δ_*Δ^*ℳ`, read as the restriction of `ℳ` along the composite chart functor. -/
noncomputable def diagonalPushforwardRestrictIsoApp :
    diagonalPushforwardRestrict B S hS f het hsep M ≅
      (SheafOfModules.pushforward.{u} (diagonalChartSharp B S hS f het hsep)).obj M :=
  (diagonalPushforwardRestrictIso B S hS f het hsep).app M

/-! ### Extension by zero splits the unit -/

/-- **Extension by zero splits the unit, read on the restriction along the composite chart
functor.**  Over an étale chart `V` of `X ×_Y X` this is
`AlgebraicGeometry.Space.diagonalExtendByZero_res`: the unit is restriction of sections along
the cartesian projection, and extension by zero is a section of that restriction.  Both sides of
the equation are typed over the single ring map `𝒪(V) ⟶ 𝒪(V ×_{X ×_Y X} X)`, which is what makes
the identification cheap; see the implementation notes. -/
theorem diagonalExtendByZeroHom_comp_unit_chart :
    (diagonalPushforwardRestrictIsoApp B S hS f het hsep M).inv ≫
      (diagonalExtendByZeroHom B S hS f het hsep M ≫
        ((diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app M ≫
          (diagonalPushforwardRestrictIsoApp B S hS f het hsep M).hom)) = 𝟙 _ := by
  ext V x
  exact diagonalExtendByZero_res B S hS f het hsep M V.unop _

/-- **Extension by zero across the diagonal splits the unit `ℳ ⟶ Δ_*Δ^*ℳ`.**  This is the
identity that Stacks 0HAP needs: composed with the unit of
`AlgebraicGeometry.Space.diagonalSmallBaseChangeAdjunction`, the morphism
`AlgebraicGeometry.Space.diagonalExtendByZeroHom` is the identity.

The content is `AlgebraicGeometry.Space.diagonalExtendByZeroHom_comp_unit_chart`; what is done
here is to cancel the identification of the double restriction with the single one, which is an
isomorphism. -/
theorem diagonalExtendByZeroHom_comp_unit :
    diagonalExtendByZeroHom B S hS f het hsep M ≫
      (diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app M = 𝟙 _ := by
  refine Stacks.Adjunction.eq_id_of_comp_iso
    (diagonalPushforwardRestrictIsoApp B S hS f het hsep M) _ _ ?_
  exact diagonalExtendByZeroHom_comp_unit_chart B S hS f het hsep M

/-- **The unit `ℳ ⟶ Δ_*Δ^*ℳ` of the chart-level adjunction at the diagonal of a separated étale
morphism is a split epimorphism**, split by extension by zero across the diagonal. -/
noncomputable def splitEpiDiagonalChartUnit :
    SplitEpi ((diagonalSmallBaseChangeAdjunction B S hS f het hsep).unit.app M) where
  section_ := diagonalExtendByZeroHom B S hS f het hsep M
  id := diagonalExtendByZeroHom_comp_unit B S hS f het hsep M

/-! ### Stacks 0HAP -/

/-- **Stacks 0HAP.**  Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`, and let `ℱ` be an `𝒪_X`-module.  Then the counit
`f^*f_*ℱ ⟶ ℱ` of the adjunction of Stacks 03LU is a split epimorphism.

The reduction to the diagonal is
`AlgebraicGeometry.Space.counitSplitEpiOfSplitEpiChartUnit`, and the splitting along the
diagonal is `AlgebraicGeometry.Space.splitEpiDiagonalChartUnit`: extension by zero across the
clopen diagonal.

Stacks 0HAP assumes `f` quasi-compact and `ℱ` quasi-coherent; neither hypothesis is used here,
see the implementation notes. -/
@[stacks 0HAP]
noncomputable def counitSplitEpiOfSeparatedEtale (F : Modules.{u, u} B S hS X.1 X.2) :
    SplitEpi ((modulePullbackAdjunction B S hS f).counit.app F) :=
  counitSplitEpiOfSplitEpiChartUnit B S hS f het hsep F
    (splitEpiDiagonalChartUnit B S hS f het hsep _)

end AlgebraicGeometry.Space

end
