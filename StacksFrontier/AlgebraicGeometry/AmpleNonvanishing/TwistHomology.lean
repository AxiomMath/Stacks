module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TermwiseTwist
public import StacksFrontier.Homology.DerivedCategory.MapCyclesHomologyPi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness

/-!
# The cohomology sheaves of the twist by an invertible module, and the class of a section

`Stacks.AmpleNonvanishing.termwiseTwist X L K` is the complex `p ↦ K^p ⊗_{𝒪_X} L`, which
`Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIso` identifies with
`K ⊗^𝐋_{𝒪_X} L[0]` when `L` is invertible. This file computes its cycles and its cohomology
sheaves,

`Z^p(K ⊗ L) ≅ Z^p(K) ⊗ L` and `H^p(K ⊗ L) ≅ H^p(K) ⊗ L`,

and shows that the two comparisons agree with the projection of cycles onto cohomology, so that
a **section** of the twisted cycles has, as its class, the twist of the class of the
corresponding section of the cycles.

This is the input [Stacks, Tag 0BQR] needs in order to see that the global cocycle its proof
builds is a **nonzero** class — the part that says the twist does not disturb the cohomology
sheaves, and does not disturb the class of a section either. The remaining ingredient of that
step, the trivialization of `L ^⊗ n` by a nonvanishing section over `X_s`, is clause 2 of
[Stacks, Tag 01CY] and is already available on sections as
`Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero`.

## Why it is five short declarations

Tensoring on the right with a fixed module is `(sheafTensor 𝒪_X).flip.obj L`, and
`Stacks.AmpleNonvanishing.termwiseTwist` is *definitionally* that functor applied degreewise:
`CochainComplex.KFlatBifunctor.rowComplex` has `X p = (F.obj (K.X p)).obj L` and
`d = (F.map (K.d p p')).app L`, which is exactly what `Functor.mapHomologicalComplex` gives for
`F.flip.obj L`. So the content is entirely in the hypotheses of
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso` and of
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso`, namely that
`(sheafTensor 𝒪_X).flip.obj L` is additive and exact:

* additivity is the additivity of the bifunctor together with `NatTrans.app_add`;
* exactness is `Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat` —
  `AlgebraicGeometry.SheafOfModules.IsFlat` *is* exactness of that very functor, so the lemma is
  the identity — fed with `Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule`.

The spelling of the structure sheaf is `X.toRingedSpace.sheaf` throughout, which is the one the
`Additive` and `HasMapBifunctor` instances of the tensor bifunctor are seated at; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/InvertibleTwistDerived.lean`.

## Where the section statement comes from

The comparison `(S.map F).cycles ≅ F.obj S.cycles` for a functor preserving left homology is
Mathlib's `CategoryTheory.ShortComplex.mapCyclesIso`, whose compatibility with the *inclusion*
of cycles is `CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles`. Its compatibility with the
*projection* `homologyπ` onto homology is not in Mathlib; it is proved, and transferred to
`HomologicalComplex.cycles`, in
`StacksFrontier/Homology/DerivedCategory/MapCyclesHomologyPi.lean`. This file only reads that at
the twist.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishing

/-- **Tensoring on the right with a fixed `𝒪_X`-module is additive**, at the scheme spelling of
the structure sheaf. `Stacks.AmpleNonvanishing.sheafTensor_additive` is the additivity of the
bifunctor itself; this reads it at one fixed right factor, where the action on morphisms is
`f ↦ (sheafTensor.map f).app L` and the passage is `NatTrans.app_add`. -/
instance sheafTensorFlipObj_additive (X : Scheme.{u}) (L : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L).Additive where
  map_add := by
    intro M N f g
    change ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map (f + g)).app L = _
    rw [Functor.map_add]
    rfl

/-- **Tensoring on the right with an invertible `𝒪_X`-module is an exact functor.** An invertible
module is flat (`Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule`, from [Stacks, Tag 05NE]),
and `AlgebraicGeometry.SheafOfModules.IsFlat` is by definition the exactness of this very
functor — `Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat` is the identity. -/
theorem exactFunctor_sheafTensorFlipObj_of_isInvertibleModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] :
    exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) :=
  Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat _ L
    (isFlat_of_isInvertibleModule X L)

/-- **The cohomology sheaves of the twist by an invertible module are the twists of the cohomology
sheaves.** For every complex `K` of `𝒪_X`-modules, every invertible `𝒪_X`-module `L` and every
`p`,

`H^p(p ↦ K^p ⊗_{𝒪_X} L) ≅ H^p(K) ⊗_{𝒪_X} L`.

`Stacks.AmpleNonvanishing.termwiseTwist` is `- ⊗ L` applied degreewise, so this is
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso` for that functor, whose
exactness is `Stacks.AmpleNonvanishing.exactFunctor_sheafTensorFlipObj_of_isInvertibleModule`. It
is natural in `K`, being a component of a natural isomorphism of functors.

Through `Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIso` this reads as
`H^p(K ⊗^𝐋_{𝒪_X} L[0]) ≅ H^p(K) ⊗ L`, which is the step of [Stacks, Tag 0BQR] that lets a class
nonzero in the `p`-th cohomology sheaf of `K` be followed through the twist. -/
def termwiseTwistHomologyIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (K : Stacks.Duality.TensorComplex X) (p : ℤ) :
    (termwiseTwist X L K).homology p ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
        (K.homology p)).obj L :=
  letI hex := exactFunctor_sheafTensorFlipObj_of_isInvertibleModule X L
  letI : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.1
  letI : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.2
  (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L)
    (ComplexShape.up ℤ) p).app K

/-- **The cycles of the twist by an invertible module are the twists of the cycles.** For every
complex `K` of `𝒪_X`-modules, every invertible `𝒪_X`-module `L` and every `p`,

`Z^p(p ↦ K^p ⊗_{𝒪_X} L) ≅ Z^p(K) ⊗_{𝒪_X} L`.

This is `StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso` — Mathlib's
`CategoryTheory.ShortComplex.mapCyclesIso` read on a complex — for the exact functor `- ⊗ L`,
exactly as `Stacks.AmpleNonvanishing.termwiseTwistHomologyIso` is the homology comparison for
the same functor. -/
def termwiseTwistCyclesIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (K : Stacks.Duality.TensorComplex X) (p : ℤ) :
    (termwiseTwist X L K).cycles p ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
        (K.cycles p)).obj L :=
  letI hex := exactFunctor_sheafTensorFlipObj_of_isInvertibleModule X L
  letI : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.1
  letI : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.2
  StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) K p

/-- **The twist of the projection of cycles onto cohomology is the projection of the twisted
cycles onto the twisted cohomology.** For every complex `K` of `𝒪_X`-modules, every invertible
`𝒪_X`-module `L` and every `p`, the square

`Z^p(K ⊗ L) ≅ Z^p(K) ⊗ L ⟶ H^p(K) ⊗ L` = `Z^p(K ⊗ L) ⟶ H^p(K ⊗ L) ≅ H^p(K) ⊗ L`

commutes, the two comparisons being
`Stacks.AmpleNonvanishing.termwiseTwistCyclesIso` and
`Stacks.AmpleNonvanishing.termwiseTwistHomologyIso`.

This is `StacksDraft.DerivedCategoryHomology.mapCyclesIso_hom_map_homologyπ` for `- ⊗ L` at the
short complex `K.sc p`, and it is what makes the cohomology comparison usable on a *section*:
see `Stacks.AmpleNonvanishing.termwiseTwistHomologyIso_class`.

The short-complex lemma is used in place of its complex-level reading
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso_hom_map_homologyπ` for a
reason of elaboration cost: the latter forces the elaborator to see `termwiseTwist X L K` and
`((- ⊗ L).mapHomologicalComplex (.up ℤ)).obj K` as the same *complex*, which means comparing the
two degreewise families as functions and does not fit in the heartbeat budget, whereas the
former only needs the two degree-`p` short complexes to agree, and those are structures with
three objects and two morphisms. -/
theorem termwiseTwistCyclesIso_hom_homologyπ (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (K : Stacks.Duality.TensorComplex X) (p : ℤ) :
    (termwiseTwistCyclesIso X L K p).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (K.homologyπ p)).app L =
      (termwiseTwist X L K).homologyπ p ≫ (termwiseTwistHomologyIso X L K p).hom :=
  let hex := exactFunctor_sheafTensorFlipObj_of_isInvertibleModule X L
  let : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.1
  let : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L) := hex.2
  StacksDraft.DerivedCategoryHomology.mapCyclesIso_hom_map_homologyπ (K.sc p)
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).flip.obj L)

/-- **The class of a section of the twisted cycles is the twist of its class.** For `ψ` a
morphism of `𝒪_X`-modules into the degree-`p` cycles of the twist `p ↦ K^p ⊗_{𝒪_X} L` — in the
intended application `A = 𝒪_X` and `ψ` is a *global section* of `Z^p(K) ⊗ L` — the class of `ψ`
in `H^p(K ⊗ L)` corresponds, under
`Stacks.AmpleNonvanishing.termwiseTwistHomologyIso`, to the image of `ψ` under
`Z^p(K) ⊗ L ⟶ H^p(K) ⊗ L`, the twist of the projection `H.homologyπ p`.

This is the statement [Stacks, Tag 0BQR] consumes: its proof writes down a global section of the
twisted cycles whose class over the chart `X_s` is `τ ⊗ σ|_{X_s}`, and this is what identifies
that class with the twist of `τ`, hence — by the whiskered clause 2 of [Stacks, Tag 01CY],
`Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero` — makes it nonzero. -/
theorem termwiseTwistHomologyIso_class (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (K : Stacks.Duality.TensorComplex X) (p : ℤ)
    {A : Stacks.DerivedTensor.RingedSite.Modules X.sheaf}
    (ψ : A ⟶ (termwiseTwist X L K).cycles p) :
    ψ ≫ (termwiseTwist X L K).homologyπ p ≫ (termwiseTwistHomologyIso X L K p).hom =
      ψ ≫ (termwiseTwistCyclesIso X L K p).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (K.homologyπ p)).app L :=
  congrArg (fun z => ψ ≫ z) (termwiseTwistCyclesIso_hom_homologyπ X L K p).symm

end Stacks.AmpleNonvanishing

end
