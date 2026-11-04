module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Base change for the Betti numbers of the derived fibres

Let `X` be a scheme and `E` a pseudo-coherent object of `D(𝒪_X)`.  For `i : ℤ` the `i`-th
derived-fibre Betti function of `E` sends a point `x` to the dimension over the residue field
`κ(x)` of the `i`-th cohomology of the derived fibre `Li_x^* E`, where `i_x : Spec κ(x) ⟶ X` is
the canonical morphism.

For a morphism of schemes `f : Y ⟶ X` and `y : Y` with image `x`, the residue square

```
Spec κ(y) --g--> Spec κ(x)
   |                |
  j_y              i_x
   v                v
   Y -----f------>  X
```

gives `Lg^* ∘ Li_x^* = Lj_y^* ∘ Lf^*`, and `Lg^*` does not change dimensions because `g` is the
spectrum of a homomorphism of fields.  Hence the derived-fibre Betti function of `Lf^* E` is the
pullback along `f` of that of `E`.  This is part (1) of Tag 0BDI.

## Main definitions

* `AlgebraicGeometry.DerivedFibreBetti.HasDerivedPullback` is existence of the derived pullback
  along a morphism of ringed spaces, in the sense of Tag 079W.
* `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti` is the derived-fibre Betti function.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.residueSquare` is the commutative square above, and
  `AlgebraicGeometry.DerivedFibreBetti.residueSquare_toShHom` is the same square read in ringed
  spaces.
* `AlgebraicGeometry.DerivedFibreBetti.residueSquareIso` is the composition isomorphism
  `Lg^* Li_x^* E ≅ Lj_y^* Lf^* E` of that square.
* `AlgebraicGeometry.DerivedFibreBetti.finrank_residueFibre_eq`: across the square the dimension of
  the `i`-th cohomology of the derived fibre at `y` equals the one at `x`.
* `AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_derivedPullback`: the derived pullback of a
  pseudo-coherent object of `D(𝒪_X)` is pseudo-coherent.
* `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback`: the base-change formula
  for the derived-fibre Betti function.

## Implementation notes

*Why the derived pullbacks are not hypotheses.*  Existence of an everywhere-defined derived
pullback is Tag 06YJ, and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy` seats
it as an instance for every morphism of ringed spaces, from the K-flat resolving datum.  So
`HasDerivedPullback` holds throughout and is carried nowhere; no instance hypothesis is needed for
the morphisms whose derived pullbacks the statement mentions.
`hasDerivedPullback_residueFieldMap` records the sharper reason it holds for the horizontal
morphism `g` of the residue square — pullback along the spectrum of a homomorphism of fields is
exact, so there the class of *all* complexes is already a resolving datum.

*Why the square isomorphism is not a hypothesis.*  It is the composition formula of Tag 0D5S for
the two sides of the square, and
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` is that formula with no
resolving datum left over: the class of complexes on `X` which resolves every complex, whose
quasi-isomorphisms degreewise pullback inverts, and on which the comparison for `Li_x^*` is
invertible, is the K-flat one, and Tags 06YJ, 06YC and 079W supply all three conditions.
`residueSquareIso` is the resulting isomorphism, transported along `residueSquare_toShHom`, so it
is not taken as a hypothesis in the `Nonempty` form the dimension statement consumes.

*Where the pseudo-coherence of `Lf^* E` comes from.*  `derivedFiberBetti` does not use its
pseudo-coherence argument, but the left-hand side of the base-change formula has to supply one. It
is derived rather than assumed: `isPseudoCoherent_derivedPullback` is Tag 09U7
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback`,
unconditional) applied in each degree, with Tag 08CC part (2)
(`Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso`) moving the
degree-`m` representative it returns onto the single representative `DerivedCategory.Q.objPreimage`
that pseudo-coherence of a derived object requires.  Carrying that
pseudo-coherence as a hypothesis would add one the Tag 0BDI statement does not have, and it costs
no generality to derive it: the underlying dimension equality
`finrank_residueFibre_eq` carries no pseudo-coherence hypothesis whatsoever.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.DerivedFibreBetti

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The derived pullback of Tag 079W along a morphism of ringed spaces exists: degreewise
pullback followed by localization has an everywhere-defined left derived functor.

This holds for every morphism, by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`. -/
public abbrev HasDerivedPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) : Prop :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))

/-- **The derived pullback along the spectrum of a homomorphism of residue fields exists.**
Pullback along it is exact, so the class of all complexes is a resolving datum. -/
public instance hasDerivedPullback_residueFieldMap {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    HasDerivedPullback (Spec.map (f.residueFieldMap y)).toLRSHom.toShHom :=
  SpecField.hasLeftDerivedFunctor_pullbackOnHomotopy_SpecMap
    (Field.toIsField _) (Field.toIsField _) _

/-- **The `i`-th derived-fibre Betti function of a pseudo-coherent object of `D(𝒪_X)`.**  Its
value at `x` is the dimension over `κ(x)` of the `i`-th cohomology of the derived fibre
`Li_x^* E`, read through global sections on `Spec κ(x)`. -/
public def derivedFiberBetti (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (_hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) : X → ℕ :=
  fun x =>
    Module.finrank (X.residueField x)
      ((moduleSpecΓFunctor (R := X.residueField x)).obj
        ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules i).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (X.fromSpecResidueField x).toLRSHom.toShHom).obj E)))

/-- The value of `derivedFiberBetti X E hE i` at `x`: the dimension over `κ(x)` of the
global sections of the `i`-th cohomology of `Li_x^* E`. -/
@[simp]
public theorem derivedFiberBetti_apply (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) (x : X) :
    derivedFiberBetti X E hE i x =
      Module.finrank (X.residueField x)
        ((moduleSpecΓFunctor (R := X.residueField x)).obj
          ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules i).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (X.fromSpecResidueField x).toLRSHom.toShHom).obj E))) :=
  rfl

section BaseChange

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The residue square of a morphism of schemes at a point.**  The two routes from
`Spec κ(y)` to `X` agree. -/
public theorem residueSquare (y : Y) :
    Spec.map (f.residueFieldMap y) ≫ X.fromSpecResidueField (f.base y) =
      Y.fromSpecResidueField y ≫ f :=
  Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f y

/-- The residue square read as a square of morphisms of ringed spaces.  This is the form the
composition formula of Tag 0D5S consumes, since its derived pullbacks are indexed by morphisms
of ringed spaces rather than of schemes. -/
public theorem residueSquare_toShHom (y : Y) :
    (Spec.map (f.residueFieldMap y)).toLRSHom.toShHom ≫
        (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom =
      (Y.fromSpecResidueField y).toLRSHom.toShHom ≫ f.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : Spec (Y.residueField y) ⟶ X => k.toLRSHom.toShHom) (residueSquare f y)

/-- **The composition isomorphism of the residue square** `Lg^* Li_x^* E ≅ Lj_y^* Lf^* E`.

Both iterated derived pullbacks are derived pullback along the one composite of
`residueSquare_toShHom`, by the unconditional composition formula of Tag 0D5S; the equality of
the two composites is transported by `eqToIso`. -/
public def residueSquareIso (y : Y) (E : DerivedCategory X.Modules) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Spec.map (f.residueFieldMap y)).toLRSHom.toShHom).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom).obj E) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (Y.fromSpecResidueField
        y).toLRSHom.toShHom).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj
          E) :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Spec.map (f.residueFieldMap y)).toLRSHom.toShHom
        (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun k =>
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback.{u, u + 1, u + 1} k).obj E)
      (residueSquare_toShHom f y)) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (Y.fromSpecResidueField y).toLRSHom.toShHom f.toLRSHom.toShHom).app E).symm

/-- **Across the residue square the dimension of the cohomology of the derived fibre does not
change.**  The dimension over `κ(y)` of the `i`-th cohomology of the derived fibre of `Lf^* E` at
`y` is the dimension over `κ(x)` of the `i`-th cohomology of the derived fibre of `E` at
`x = f y`.

The first identification transports along `residueSquareIso`; the second is
`AlgebraicGeometry.SpecField.finrank_derivedPullback` for the homomorphism of residue fields. -/
public theorem finrank_residueFibre_eq (E : DerivedCategory X.Modules) (y : Y) (i : ℤ) :
    Module.finrank (Y.residueField y)
        ((moduleSpecΓFunctor (R := Y.residueField y)).obj
          ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules i).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (Y.fromSpecResidueField y).toLRSHom.toShHom).obj
                ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  f.toLRSHom.toShHom).obj E)))) =
      Module.finrank (X.residueField (f.base y))
        ((moduleSpecΓFunctor (R := X.residueField (f.base y))).obj
          ((DerivedCategory.homologyFunctor
              (Spec (X.residueField (f.base y))).Modules i).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom).obj E))) := by
  have hsq := ((moduleSpecΓFunctor (R := Y.residueField y)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules i).mapIso
      (residueSquareIso f y E))).toLinearEquiv.finrank_eq
  refine hsq.symm.trans ?_
  exact SpecField.finrank_derivedPullback (Field.toIsField _) (Field.toIsField _)
    (f.residueFieldMap y)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom).obj E) i

/-- **Tag 0BDI, base change: the derived pullback of a pseudo-coherent object is
pseudo-coherent.**  This is what makes the derived-fibre Betti function of `Lf^* E` available
from the pseudo-coherence of `E` alone.

A single complex has to work for every `m`, so the representative is chosen once —
`DerivedCategory.Q.objPreimage` — and Tag 09U7 is applied in each degree, its `m`-specific
representative being transported onto that one choice by Tag 08CC part (2). -/
@[stacks 0BDI "base_change"]
public theorem isPseudoCoherent_derivedPullback
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj E)
        := by
  obtain ⟨K₀, hK₀, he₀⟩ := hE
  refine ⟨DerivedCategory.Q.objPreimage
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj
        E), ?_,
    ⟨DerivedCategory.Q.objObjPreimageIso _⟩⟩
  intro m
  exact Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso _ m
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
      f.toLRSHom.toShHom E m
      ⟨K₀, hK₀ m, he₀⟩) _ (DerivedCategory.Q.objObjPreimageIso _)

/-- **Tag 0BDI, base change: the derived-fibre Betti function commutes with base change.**  For a
morphism of schemes `f : Y ⟶ X` the `i`-th derived-fibre Betti function of `Lf^* E` is the
pullback along `f` of the `i`-th derived-fibre Betti function of `E`.

The pseudo-coherence of `Lf^* E` that the left-hand side needs is supplied by
`isPseudoCoherent_derivedPullback`, so `E`'s own pseudo-coherence is the only hypothesis.  The
function does not use its pseudo-coherence argument, so nothing is lost by fixing it: the
underlying dimension equality is `finrank_residueFibre_eq`, which has no pseudo-coherence
hypothesis at all. -/
@[stacks 0BDI "base_change"]
public theorem derivedFiberBetti_derivedPullback
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (i : ℤ) :
    derivedFiberBetti Y ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E)
        (isPseudoCoherent_derivedPullback f E hE) i =
      derivedFiberBetti X E hE i ∘ f.base := by
  funext y
  exact finrank_residueFibre_eq f E y i

end BaseChange

section Semicontinuity

/-- **The derived-fibre Betti function is upper semicontinuous as soon as it is on an open
cover.**  If every point of `X` is in the image of an open immersion `f : Y ⟶ X` along which the
derived-fibre Betti function of `Lf^* E` is upper semicontinuous, then the derived-fibre Betti
function of `E` is upper semicontinuous on `X`.

This is the reduction step of part (2) of Tag 0BDI, and the whole of it that base change
supplies: the pullback along `f` of the Betti function *is* the Betti function of `Lf^* E`, by
`derivedFiberBetti_derivedPullback`, and the base map of an open immersion is an open embedding,
so a neighbourhood filter upstairs pushes forward to the neighbourhood filter downstairs.  What
remains for part (2) is upper semicontinuity on an affine chart; this statement is not the tag
and carries no tag. -/
public theorem upperSemicontinuous_derivedFiberBetti_of_openImmersions (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f) (y : Y),
      f.base y = x ∧
        UpperSemicontinuous (derivedFiberBetti Y
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj E)
          (isPseudoCoherent_derivedPullback f E hE) i)) :
    UpperSemicontinuous (derivedFiberBetti X E hE i) := by
  intro x n hn
  obtain ⟨Y, f, hf, y, hyx, hUSC⟩ := h x
  rw [derivedFiberBetti_derivedPullback f E hE i] at hUSC
  subst hyx
  rw [← (@Scheme.Hom.isOpenEmbedding _ _ f hf).map_nhds_eq y, Filter.eventually_map]
  exact hUSC y n hn

end Semicontinuity

end AlgebraicGeometry.DerivedFibreBetti

end
