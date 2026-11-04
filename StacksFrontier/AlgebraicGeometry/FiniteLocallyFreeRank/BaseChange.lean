module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# Finite local freeness of a given rank is stable under base change

Around a cartesian square of schemes
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
the base change `f'` of a morphism `f` that is finite locally free of rank `d` is again finite
locally free of rank `d`.

## Main results

* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback`: the rank is preserved by an
  arbitrary base change; also recorded as an instance of
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property`.

## Implementation notes

Being finite locally free of rank `d` is Zariski local at the target, so by the stability
criterion of `AlgebraicGeometry.AffineTargetMorphismProperty` for a property that is Zariski
local at the target and stable under base change along morphisms of affine schemes,
it is enough to treat a cartesian square whose base and whose base-change base are affine. All
four corners of such a square are then affine, the square of global sections is a pushout of
commutative rings (`AlgebraicGeometry.isPushout_appTop_of_isPullback`), and the statement reduces
to the module-level fact that a finite locally free module of rank `d` stays finite locally free
of rank `d` after base change, `Module.IsFiniteLocallyFreeOfRank.baseChange`.

No comparison of direct images around the square is needed, so neither the base-change morphism
`g^* f_* ⟶ f'_* g'^*` of Tag 02KG nor its invertibility enters; in particular this does not
depend on the unproved half of that tag.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Stacks.Morphisms

/-- The affine case of stability of the rank under base change: for a cartesian square whose
base `S` and whose base-change base `X` are affine, the base change of a morphism that is finite
locally free of rank `d` is finite locally free of rank `d`. -/
private theorem isFiniteLocallyFreeOfRank_of_isPullback_of_isAffine {Z X Y S : Scheme.{u}}
    [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S} {f' : Z ⟶ Y} {g' : Z ⟶ X}
    (sq : IsPullback g' f' f g) {d : ℕ} (hg : IsFiniteLocallyFreeOfRank g d) :
    IsFiniteLocallyFreeOfRank g' d := by
  have hgA : IsAffineHom g := hg.toIsAffineHom
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine Z := IsAffine.of_isPullback sq
  have hg'A : IsAffineHom g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hgA
  have hgFin : IsFinite g :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g d)).1
  have hpush : IsPushout f.appTop g.appTop g'.appTop f'.appTop :=
    isPushout_appTop_of_isPullback sq
  algebraize [f.appTop.hom, g.appTop.hom, g'.appTop.hom, f'.appTop.hom,
    g'.appTop.hom.comp f.appTop.hom]
  have htower : IsScalarTower ↑Γ(S, ⊤) ↑Γ(Y, ⊤) ↑Γ(Z, ⊤) :=
    .of_algebraMap_eq' <| congr($(hpush.1.1).hom)
  have hpush' : Algebra.IsPushout ↑Γ(S, ⊤) ↑Γ(X, ⊤) ↑Γ(Y, ⊤) ↑Γ(Z, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have hfin : Module.Finite ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := g.finite_appTop
  have hmod : Module.IsFiniteLocallyFreeOfRank ↑Γ(S, ⊤) ↑Γ(Y, ⊤) d :=
    (isFiniteLocallyFreeOfRank_iff_module_of_isAffine g d rfl).mp hg
  exact (isFiniteLocallyFreeOfRank_iff_module_of_isAffine g' d rfl).mpr <|
    (hmod.baseChange ↑Γ(X, ⊤)).of_linearEquiv
    (Algebra.IsPushout.equiv ↑Γ(S, ⊤) ↑Γ(X, ⊤) ↑Γ(Y, ⊤) ↑Γ(Z, ⊤)).toLinearEquiv

open AffineTargetMorphismProperty in
/-- The property of being finite locally free of rank `d` is stable under base change. -/
instance isFiniteLocallyFreeOfRank_isStableUnderBaseChange (d : ℕ) :
    (IsFiniteLocallyFreeOfRank.property.{u} d).IsStableUnderBaseChange :=
  isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget _
    fun _ _ _ _ _ _ _ _ _ _ sq hg => isFiniteLocallyFreeOfRank_of_isPullback_of_isAffine sq hg

/-- **Stacks Project, Tag 02KA.** The rank of a finite locally free morphism is preserved by an
arbitrary base change: around a cartesian square the base change `f'` of a morphism `f` that is
finite locally free of rank `d` is again finite locally free of rank `d`. -/
theorem IsFiniteLocallyFreeOfRank.of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y} {d : ℕ} (sq : IsPullback g' f' f g)
    [IsFiniteLocallyFreeOfRank f d] : IsFiniteLocallyFreeOfRank f' d :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := IsFiniteLocallyFreeOfRank.property.{u} d) sq ‹_›

end Stacks.Morphisms

end
