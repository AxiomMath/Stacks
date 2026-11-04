module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse

/-!
# Deforming a finite locally free morphism of degree `d` across a first-order thickening

Let `(h, h') : (Z ⊆ Z') → (U ⊆ U')` be a morphism of first-order thickenings of schemes with
`h : Z ⟶ U` finite locally free of degree `d`.  If the canonical map of conormal sheaves
`h^*𝒞_{U/U'} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 01R4] is an isomorphism, then `h' : Z' ⟶ U'` is
again finite locally free of degree `d` and `Z = U ×_{U'} Z'`.

This is the closing paragraph of the proof of [Stacks Project, Tag 06D8] — "Applying
[Stacks Project, Tag 06BH] once again (or its analogue for schemes,
[Stacks Project, Tag 063Y]) we conclude that `Z' → U'` is flat and `Z = U ×_{U'} Z'`.  Finally,
[Stacks Project, Tag 06AG] shows that `Z' → U'` is finite locally free of degree `d`" — at the
level of schemes, where both inputs are available in this development without hypothesis.

The second statement is the form in which 06D8 actually reaches this step.  There the conormal
identification is produced not directly over `U ⊆ U'` but in two stages: the morphism of
thickenings factors through an intermediate first-order thickening `X ⊆ X'`, flat and cartesian
over `U ⊆ U'`, and what the construction delivers is `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`.  The conormal
identification over the base is then the composite of that with `𝒞_{X/X'} = f^*𝒞_{U/U'}`, which
is [Stacks Project, Tag 063Y] (1) ⟹ (2) at the lower square.

## Main results

* `Stacks.Thickenings.deformationDiagram`: the cartesian finite-order deformation diagram of
  [Stacks Project, Tag 06AG] attached to a morphism of first-order thickenings whose square is
  cartesian and whose ambient morphism is flat, read over the lower thickening itself as base.
* `Stacks.Thickenings.isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap`:
  degree-`d` finite local freeness and cartesianness transfer upward along a first-order
  thickening whose conormal-sheaf map is an isomorphism.
* `Stacks.Thickenings.isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap_factor`:
  the same with the conormal identification given over an intermediate flat cartesian
  thickening, which is the shape 06D8's construction produces.

## Implementation notes

"Finite locally free of degree `d`" is `Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, the
predicate of [Stacks Project, Tag 02KA]; the 06AG transfer theorem
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isFiniteLocallyFreeOfRank_iff` is
stated instead as the conjunction of [Stacks Project, Tag 02KB] with the rank function being
constant, so the two spellings are joined here by
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation` and
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq`.  Flatness of `h` is not a
hypothesis: it is part of being finite locally free, and it is what
[Stacks Project, Tag 063Y] (2) ⟹ (1) needs.

The deformation diagram takes the lower thickening `U ⊆ U'` as its own base, with both structure
morphisms of the target identities; the target square is then cartesian because its two vertical
arrows are identities, and the source square is the cartesianness that 063Y produces.

**What is not proved here.**  This is one paragraph of [Stacks Project, Tag 06D8] and no
`@[stacks 06D8]` attribute is placed by this file.  The paragraph before it constructs `Z'` inside
the universal first-order thickening `Z ⊂ Z''` of `Z` over `X'` by splitting the conormal sequence
of [Stacks Project, Tag 06CC] and cutting out the summand `𝒞_{Z/X}`, and it is what supplies the
isomorphism hypothesis below.  Its three steps are now all available for schemes:

* the sequence is short exact, `Stacks.Thickenings.transitivityConormalShortComplex_shortExact`
  ([Stacks Project, Tag 06BA]), and its third term is finite locally free,
  `AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection`
  ([Stacks Project, Tag 06B9]).  Its left-hand term is the pullback of the conormal sheaf of
  `X ⟶ X'` read as a formally unramified morphism, which is the conormal sheaf of the immersion
  `X ⟶ X'` that `Stacks.Thickenings.firstOrderThickeningConormalSheafMap` is stated at, by
  `Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf`,
  [Stacks Project, Tag 04F5] part (3);
* it splits globally, `Z` being affine:
  `AlgebraicGeometry.Scheme.Modules.nonempty_splitting_of_shortExact_of_isFiniteLocallyFree` of
  `StacksFrontier.AlgebraicGeometry.Modules.AffineGlobalSplitShortExact`;
* the closed subscheme of `Z''` cut out by the summand `𝒞_{Z/X} ⊆ ℐ ⊆ 𝒪_{Z''}` is
  `StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubscheme`, and the identification of its
  conormal sheaf `𝒞_{Z/Z'}` with the complementary summand `i^*𝒞_{X/X'}` compatibly with the
  canonical map of [Stacks Project, Tag 01R4] is
  `Stacks.Thickenings.isIso_immersionConormalSheafMap_of_splitting` of
  `StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubschemeConormal`.

The scheme-level statement of the whole tag is therefore available: it is
`Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningLciDeformation`, which consumes
this file's second statement.  It carries no `@[stacks 06D8]` attribute either, and for the
reason given in the paragraph below: the tag's `X'` is an algebraic space and its conclusion is a
diagram of algebraic spaces over `U'`, so the scheme case does not cover it.

At the level of algebraic spaces, where 06D8 is stated, the first step is still unavailable:
the space-level [Stacks Project, Tag 06CB] and [Stacks Project, Tag 06CC] in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`
carry hypotheses standing in for the comparison between the conormal module on the small étale
site of an algebraic space and the conormal sheaf on the Zariski site of a scheme.  What those
stand-ins are blocked on is the identification of the conormal *objects* and its naturality, not
the comparison of the two categories of modules: the categories are compared, with no hypothesis,
by `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, and a monomorphism and
finite local freeness travel across that comparison by the two statements of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedFiniteLocallyFree.lean`.  The two universal
first-order thickenings of a representable morphism are identified too, by
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map_iff`.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
* [Stacks Project, Tag 04F5](https://stacks.math.columbia.edu/tag/04F5)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

open Stacks.Immersion

variable {Z Z' U U' : Scheme.{u}}

/-- **The deformation diagram of [Stacks Project, Tag 06AG] attached to a cartesian morphism of
first-order thickenings.**  For a morphism `(h, h') : (Z ⊆ Z') → (U ⊆ U')` of first-order
thickenings of schemes with `h'` flat and `Z = U ×_{U'} Z'`, this is the cartesian finite-order
deformation diagram whose base thickening is `U ⊆ U'` itself and whose two horizontal morphisms
are `h` and `h'`.

Both structure morphisms of the target are identities, so the target square is cartesian by
`CategoryTheory.IsPullback.of_id_snd`; the source square is the given cartesianness. The base
thickening is of finite order because it is of first order. -/
def deformationDiagram {iZ : Z ⟶ Z'} {iU : U ⟶ U'} (hiZ : IsFirstOrderThickening iZ)
    (hiU : IsFirstOrderThickening iU) (φ : Arrow.mk iZ ⟶ Arrow.mk iU) (hflat : Flat φ.right)
    (hsq : IsPullback iZ φ.left φ.right iU) :
    CartesianFiniteOrderDeformationDiagram.{u} where
  S := U
  S' := U'
  iS := iU
  iS_finiteOrder := ⟨hiU.1, 1, by simpa using hiU.2⟩
  X := Z
  X' := Z'
  iX := iZ
  iX_thickening := isThickening_of_ker_pow_eq_bot iZ hiZ.1 (n := 1) (by simpa using hiZ.2)
  Y := U
  Y' := U'
  iY := iU
  iY_thickening := isThickening_of_ker_pow_eq_bot iU hiU.1 (n := 1) (by simpa using hiU.2)
  pX := φ.left
  pX' := φ.right
  pY := 𝟙 U
  pY' := 𝟙 U'
  f := φ.left
  f' := φ.right
  f_over_S := Category.comp_id _
  f'_over_S' := Category.comp_id _
  f_thickening_comm := Arrow.w φ
  X_cartesian := hsq
  Y_cartesian := IsPullback.of_id_snd
  X'_flat := hflat

/-- **The closing paragraph of [Stacks Project, Tag 06D8], for schemes.**  Let
`(h, h') : (Z ⊆ Z') → (U ⊆ U')` be a morphism of first-order thickenings of schemes, with
`h = φ.left` finite locally free of degree `d`.  If the canonical map of conormal sheaves
`h^*𝒞_{U/U'} ⟶ 𝒞_{Z/Z'}` is an isomorphism, then `h' = φ.right` is finite locally free of
degree `d` and `Z = U ×_{U'} Z'`.

The hypothesis is condition (2) of [Stacks Project, Tag 063Y], whose implication (2) ⟹ (1) —
`Stacks.Thickenings.flat_and_isPullback_of_isIso_firstOrderThickeningConormalSheafMap` — gives
flatness of `h'` together with the base-change identity; flatness of `h`, which that implication
needs, is part of `h` being finite locally free.  The degree then transfers along
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isFiniteLocallyFreeOfRank_iff`, the
finite-locally-free-of-rank clause of [Stacks Project, Tag 06AG], read at
`Stacks.Thickenings.deformationDiagram`. -/
theorem isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap {iZ : Z ⟶ Z'}
    {iU : U ⟶ U'} (hiZ : IsFirstOrderThickening iZ) (hiU : IsFirstOrderThickening iU)
    (φ : Arrow.mk iZ ⟶ Arrow.mk iU) (d : ℕ)
    (hZU : Stacks.Morphisms.IsFiniteLocallyFreeOfRank φ.left d)
    (hiso : letI := hiZ.1
      letI := hiU.1
      IsIso (firstOrderThickeningConormalSheafMap hiZ hiU φ)) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank φ.right d ∧
      IsPullback iZ φ.left φ.right iU := by
  let := hiZ.1
  let := hiU.1
  have := hZU
  obtain ⟨hfin, hflat, hfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      φ.left).1 (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree φ.left d)
  have := hfin
  have := hflat
  have := hfp
  have hrk : ∀ u : U, φ.left.finrank u = d :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq φ.left d).1 hZU
  obtain ⟨hflat', hsq⟩ :=
    flat_and_isPullback_of_isIso_firstOrderThickeningConormalSheafMap hiZ hiU φ hiso
  have := hflat'
  obtain ⟨hfin', -, -, hrk'⟩ :=
    ((deformationDiagram hiZ hiU φ hflat' hsq).isFiniteLocallyFreeOfRank_iff d).1
      ⟨hfin, hflat, hfp, hrk⟩
  have hfinR : IsFinite φ.right := hfin'
  have hrkR : ∀ u' : U', φ.right.finrank u' = d := hrk'
  exact ⟨(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq φ.right d).2 hrkR,
    hsq⟩

/-- **The closing paragraph of [Stacks Project, Tag 06D8], for schemes, with the conormal
identification given over an intermediate thickening.**  Let
`(Z ⊆ Z') → (X ⊆ X') → (U ⊆ U')` be two stacked morphisms of first-order thickenings of schemes
in which the lower one is cartesian with flat ambient morphism, and let the composite
`Z ⟶ U` be finite locally free of degree `d`.  If the canonical map
`𝒞_{Z/Z'} ← i^*𝒞_{X/X'}` of the upper square is an isomorphism, then `Z' ⟶ U'` is finite
locally free of degree `d` and `Z = U ×_{U'} Z'`.

This is the shape in which 06D8 reaches the previous statement: its construction produces
`𝒞_{Z/Z'} = i^*𝒞_{X/X'}` for the thickening `X ⊆ X'` cut out of the flat deformation of the
target, and `𝒞_{X/X'} = f^*𝒞_{U/U'}` separately, by [Stacks Project, Tag 063Y] (1) ⟹ (2) at the
lower square — `Stacks.Thickenings.isIso_firstOrderThickeningConormalSheafMap`.  The conormal
map of the stacked square is the composite of the two by
`Stacks.Immersion.immersionConormalSheafMap_comp`, the functoriality of
[Stacks Project, Tag 01R4], so it is an isomorphism and the previous statement applies to the
composite morphism of thickenings. -/
theorem isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap_factor
    {X X' : Scheme.{u}} {iZ : Z ⟶ Z'} {iX : X ⟶ X'} {iU : U ⟶ U'}
    (hiZ : IsFirstOrderThickening iZ) (hiX : IsFirstOrderThickening iX)
    (hiU : IsFirstOrderThickening iU) (ψ : Arrow.mk iZ ⟶ Arrow.mk iX)
    (χ : Arrow.mk iX ⟶ Arrow.mk iU) (hflatX : Flat χ.right)
    (hsqX : IsPullback iX χ.left χ.right iU) (d : ℕ)
    (hZU : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ψ.left ≫ χ.left) d)
    (hiso : letI := hiZ.1
      letI := hiX.1
      IsIso (firstOrderThickeningConormalSheafMap hiZ hiX ψ)) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (ψ.right ≫ χ.right) d ∧
      IsPullback iZ (ψ.left ≫ χ.left) (ψ.right ≫ χ.right) iU := by
  let := hiZ.1
  let := hiX.1
  let := hiU.1
  have := hflatX
  have hisoPsi : IsIso (immersionConormalSheafMap iZ iX ψ.left ψ.right
      (toShHom_square (Arrow.w ψ).symm)) := hiso
  have hisoChi : IsIso (immersionConormalSheafMap iX iU χ.left χ.right
      (toShHom_square (Arrow.w χ).symm)) :=
    isIso_firstOrderThickeningConormalSheafMap hiX hiU χ hsqX
  have hisoPull : IsIso ((modulePullback ψ.left.toLRSHom.toShHom).map
      (immersionConormalSheafMap iX iU χ.left χ.right
        (toShHom_square (Arrow.w χ).symm))) := inferInstance
  have hisoApp : IsIso ((modulePullbackComp ψ.left.toLRSHom.toShHom
      χ.left.toLRSHom.toShHom).hom.app
      (ClosedImmersion.conormalSheaf iU.liftCoborder.toLRSHom.toShHom)) := inferInstance
  have hcomp : IsIso (immersionConormalSheafMap iZ iU (ψ.left ≫ χ.left) (ψ.right ≫ χ.right)
      (toShHom_square (square_comp (Arrow.w ψ).symm (Arrow.w χ).symm))) :=
    (iff_of_eq (congrArg IsIso (immersionConormalSheafMap_comp iZ iX iU ψ.left ψ.right
      (Arrow.w ψ).symm χ.left χ.right (Arrow.w χ).symm))).2
      (IsIso.comp_isIso' hisoApp (IsIso.comp_isIso' hisoPull hisoPsi))
  exact isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap hiZ hiU (ψ ≫ χ) d
    hZU hcomp

end Stacks.Thickenings

end
