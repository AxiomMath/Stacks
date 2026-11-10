module

public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChangeDifferentials
public import StacksFrontier.Cotangent.BaseChangeQuasiIsoUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# `L_{B/A} = L_{B/A'}` in `D(B)`

Let `A → A' → B` be ring maps such that `B = B ⊗_A^𝐋 A'`. Stacks 08QZ asserts that then

`L_{B/A} = L_{B/A'}` in `D(B)`.

`StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChangeDifferentials.lean` proves the step the
source's argument turns on — the sheaf comparison `i^*Ω_{𝒪/A} = u^{-1}(i^*Ω_{𝒪/A'})` of
`CommAlgCat.midBaseChangeOverDifferentialsIso` — and draws from it the *degreewise* conclusion
`CommAlgCat.midCotangentComplexHomologyIso`, that the two cotangent complexes have the same
cohomology in every degree as `B`-modules. This file supplies the conclusion the source states:
a single isomorphism in `D(B)`.

Degreewise isomorphisms do not give one. What is produced here is the **canonical comparison**:
the tower `A → A' → B` is a commutative square of ring maps with `B → B` the identity, Tag 08PN
attaches to that square a `B`-linear map of cotangent complexes
`L_{B/A} ⟶ L_{B/A'}` (`CommAlgCat.squareCotangentComplexMap`), and what is proved is that this
map is a quasi-isomorphism, hence invertible in `D(B)`.

## The route

Stacks 08QZ in this form is the special case `B' = B` of Stacks 08QQ, which is already in the
library as `CommAlgCat.quasiIso_cotangentExtendScalarsMooreMap`: for a commutative square
inducing `B ⊗_A^𝐋 A' = B'`, the functoriality map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` is a
quasi-isomorphism. Two things have to be supplied.

* 08QQ carried one hypothesis beyond the source's own, `Remark 08QI` in the form
  `CommAlgCat.CotangentComputedByEveryResolution`. That is now
  `CommAlgCat.cotangentComputedByEveryResolution`, a theorem, so nothing is carried here.
* 08QQ is stated on the `B'`-linear adjoint, which for `B' = B` is a map out of
  `B ⊗_B L_{B/A}` rather than out of `L_{B/A}`. The two are related by the unit of the
  extension-of-scalars adjunction at the identity ring map, `ModuleCat.extendScalarsId`, which is
  an isomorphism; `CommAlgCat.midCotangentMooreMap_eq` is that comparison.

## Main definitions

* `CommAlgCat.midAlgebraSquare`: the tower `A → A' → B`, read as a commutative square of ring
  maps whose vertical map `B → B` is the identity.
* `CommAlgCat.midCotangentComplexMap`: **the canonical map `L_{B/A} ⟶ L_{B/A'}`** of Tag 08PN
  attached to that square.
* `CommAlgCat.midCotangentComplexDerivedIso`: **Stacks 08QZ**, the isomorphism
  `L_{B/A} ≅ L_{B/A'}` in `D(B)`, whose underlying morphism is that map.

## Main results

* `CommAlgCat.midCotangentMooreMap_eq`: the `B`-linear functoriality map of the square is the
  unit of extension of scalars along the identity followed by its `B`-linear adjoint, the map
  Tag 08QQ is stated on.
* `CommAlgCat.quasiIso_midCotangentComplexMap`: **Stacks 08QZ** — the canonical map
  `L_{B/A} ⟶ L_{B/A'}` is a quasi-isomorphism.
* `CommAlgCat.isIso_Q_map_midCotangentComplexMap`: the same read in `D(B)`.

## Implementation notes

**Nothing is assumed beyond the tag's hypothesis.** `B = B ⊗_A^𝐋 A'` is written out as the two
conditions it is: `RingTheory.TorIndependence.TorIndependent A A' (B : Type u)`, the vanishing of
`Tor_i^A(A', B)` for `i > 0`, and bijectivity of `A' ⊗_A B → B`, `a' ⊗ x ↦ a' · x`, which is
`CommAlgCat.baseChangeUnit (AlgHom.id A (B : Type u))`. These are the hypotheses of the
degreewise statement in
`StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChangeDifferentials.lean`, and the second is not
implied by the first; see the implementation notes there.

**Why the square's vertical map is the identity.** Restriction of scalars along
`(AlgHom.id A (B : Type u)).toRingHom = RingHom.id (B : Type u)` is the identity functor of
`ModuleCat (B : Type u)` *definitionally*, and so is the functor it induces on homological
complexes. So `CommAlgCat.squareCotangentComplexMap` for this square, whose target is in general
the cotangent complex of `B'` read over `B`, is already a morphism
`L_{B/A} ⟶ L_{B/A'}` of cochain complexes of `B`-modules, and
`CommAlgCat.midCotangentComplexMap` needs no transport. Extension of scalars along the identity
is not the identity — it is `B ⊗_B -` — which is why the one comparison below is needed.

**The degreewise statement is not reproved from this.** It could be: cohomology of the two sides
of an isomorphism in `D(B)` agrees. But the degreewise isomorphism already in the library is built
from the two resolutions directly and does not go through Tag 08QQ, so the two statements rest on
different parts of the library and are left side by side.

## References

* [Stacks Project, Tag 08QZ](https://stacks.math.columbia.edu/tag/08QZ)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped ChangeOfRings TensorProduct

universe u

namespace ModuleCat

/-- **The unit of extension of scalars along the identity inverts its adjoint.** For a map
`g : X ⟶ Y` of `R`-modules, read as a map into the restriction of scalars of `Y` along
`RingHom.id R`, the `R`-linear adjoint `R ⊗_R X ⟶ Y` of `g` composed with the unit
`x ↦ 1 ⊗ x` is `g` again. -/
theorem extendScalarsId_inv_app_comp_fromExtendScalars {R : Type u} [CommRing R]
    {X Y : ModuleCat.{u} R} (g : X ⟶ Y) :
    (ModuleCat.extendScalarsId R).inv.app X ≫
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (RingHom.id R) g = g :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (RingHom.id R) g (1 : R) x).trans (one_smul R _))

end ModuleCat

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

/-- **The unit of extension of scalars along the identity of `B`**, applied degreewise to the
Moore complex of `L_{B/A}`: the isomorphism `L_{B/A} ≅ B ⊗_B L_{B/A}`, `x ↦ 1 ⊗ x`. It is what
separates the `B`-linear functoriality map of Tag 08PN from the `B`-linear adjoint that
Tag 08QQ is stated on. -/
def cotangentExtendScalarsIdIso (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    (alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object ≅
      ((ModuleCat.extendScalars (RingHom.id (B : Type u))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
          (cotangentSimplicialModule.{u, u} A B).object) :=
  (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId (B : Type u)).symm
      (ComplexShape.down ℕ)).app
    ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
      (cotangentSimplicialModule.{u, u} A B).object)

section Tower

variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']
  (B : CommAlgCat.{u} A) [Algebra A' (B : Type u)] [IsScalarTower A A' (B : Type u)]

/-- **The tower `A → A' → B` as a commutative square of ring maps**, the square of Stacks 08QZ:
`A → A'` on top, the identity `B → B` on the side, and `B` read over `A'` as
`CommAlgCat.midAlgebra` at the bottom right. -/
abbrev midAlgebraSquare : AlgebraSquare.{u, u, u} A A' B (midAlgebra A' B) :=
  algebraSquareOfAlgHom (B' := midAlgebra A' B) (AlgHom.id A (B : Type u))

/-- **The canonical map `L_{B/A} ⟶ L_{B/A'}`**, the map of cotangent complexes which Tag 08PN
attaches to the square of the tower `A → A' → B`. It is `B`-linear because the vertical map of
the square is the identity of `B`; degreewise it sends the pure differential `1 ⊗ d p` to
`1 ⊗ d (u p)` for `u : P_• ⟶ P'_•` the canonical map of the two standard resolutions
(`CommAlgCat.squareCotangentComplexMap_differential`). -/
def midCotangentComplexMap :
    cotangentComplex.{u, u} A B ⟶ cotangentComplex.{u, u} A' (midAlgebra A' B) :=
  squareCotangentComplexMap (midAlgebraSquare A' B)

/-- The map of Moore complexes under `CommAlgCat.midCotangentComplexMap`: the functoriality map
of Tag 08PN for the square of the tower, before the reindexing which places simplicial degree `n`
in cohomological degree `-n`. -/
abbrev midCotangentMooreMap :
    (alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object ⟶
      (alternatingFaceMapComplex (ModuleCat.{u} (midAlgebra A' B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A' (midAlgebra A' B)).object :=
  squareCotangentMooreMap (midAlgebraSquare A' B)

variable {A' B}

/-- **The functoriality map of the square is the unit followed by its adjoint.** The `B`-linear
map `L_{B/A} ⟶ L_{B/A'}` of Tag 08PN for the square of the tower is the unit
`L_{B/A} ≅ B ⊗_B L_{B/A}` of extension of scalars along the identity, followed by the
`B`-linear map `B ⊗_B L_{B/A} ⟶ L_{B/A'}` which Tag 08QQ is stated on. Degreewise this is the
adjunction's own identity: the adjoint of a map, evaluated on `1 ⊗ x`, is the map. -/
theorem midCotangentMooreMap_eq :
    midCotangentMooreMap A' B =
      (cotangentExtendScalarsIdIso A B).hom ≫
        cotangentExtendScalarsMooreMap (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)) :=
  HomologicalComplex.hom_ext _ _ fun n => by
    change (midCotangentMooreMap A' B).f n =
      (ModuleCat.extendScalarsId (B : Type u)).inv.app
          (((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
            (cotangentSimplicialModule.{u, u} A B).object).X n) ≫
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (RingHom.id (B : Type u))
          (Y := ((alternatingFaceMapComplex (ModuleCat.{u} (midAlgebra A' B : Type u))).obj
            (cotangentSimplicialModule.{u, u} A' (midAlgebra A' B)).object).X n)
          ((midCotangentMooreMap A' B).f n)
    exact (ModuleCat.extendScalarsId_inv_app_comp_fromExtendScalars
      ((midCotangentMooreMap A' B).f n)).symm

/-- **Stacks 08QZ on the Moore complexes.** Let `A → A' → B` be ring maps with
`B = B ⊗_A^𝐋 A'`. Then the functoriality map of Tag 08PN for the square of the tower is a
quasi-isomorphism of the alternating face map complexes of `Ω_{P_•/A} ⊗_{P_•} B` and
`Ω_{P'_•/A'} ⊗_{P'_•} B`. -/
theorem quasiIso_midCotangentMooreMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)))) :
    QuasiIso (midCotangentMooreMap A' B) := by
  rw [midCotangentMooreMap_eq]
  have h := quasiIso_cotangentExtendScalarsMooreMap_unconditional (B' := midAlgebra A' B)
    (AlgHom.id A (B : Type u)) hTor hφ
  have hu : QuasiIso (cotangentExtendScalarsIdIso A B).hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := hu) (hφ' := h)

/-- **Stacks 08QZ.** Let `A → A' → B` be ring maps such that `B = B ⊗_A^𝐋 A'`, which is to say
that `Tor_i^A(A', B)` vanishes for `i > 0` and the canonical map `A' ⊗_A B → B`,
`a' ⊗ x ↦ a' · x`, is bijective. Then the canonical map `L_{B/A} ⟶ L_{B/A'}` of Tag 08PN,
`CommAlgCat.midCotangentComplexMap`, is a quasi-isomorphism.

This is the special case `B' = B` of Stacks 08QQ,
`CommAlgCat.quasiIso_cotangentExtendScalarsMooreMap`: the square of the tower has the identity of
`B` for its vertical map, so `B ⊗_A^𝐋 A' = B'` is the hypothesis of the tag, and the base-change
map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of 08QQ is, under
`CommAlgCat.midCotangentMooreMap_eq`, the functoriality map `L_{B/A} ⟶ L_{B/A'}`. Remark 08QI,
which 08QQ carried as a hypothesis, is `CommAlgCat.cotangentComputedByEveryResolution`, so
nothing beyond the tag's own hypothesis is assumed. -/
@[stacks 08QZ "on the cotangent complexes: under the tag's own hypothesis B = B ⊗_A^𝐋 A' -- Tor \
  independence of A' and B over A, and bijectivity of A' ⊗_A B → B -- the canonical map \
  L_{B/A} ⟶ L_{B/A'} of Tag 08PN is a quasi-isomorphism"]
theorem quasiIso_midCotangentComplexMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)))) :
    QuasiIso (midCotangentComplexMap A' B) := by
  have h : QuasiIso (HomologicalComplex.extendMap (midCotangentMooreMap A' B)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 (quasiIso_midCotangentMooreMap hTor hφ)
  have hΦ : QuasiIso (HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.restrictScalars (midAlgebraSquare A' B).map)
      ((alternatingFaceMapComplex (ModuleCat.{u} (midAlgebra A' B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A' (midAlgebra A' B)).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h) (hφ' := hΦ)

/-- **Stacks 08QZ in the derived category.** Under the tag's hypothesis `B = B ⊗_A^𝐋 A'` the
canonical map `L_{B/A} ⟶ L_{B/A'}` of Tag 08PN becomes an isomorphism in `D(B)`. -/
@[stacks 08QZ "the lemma as the invertibility in D(B) of the canonical map of Tag 08PN: under \
  the tag's own hypothesis B = B ⊗_A^𝐋 A', the image of L_{B/A} ⟶ L_{B/A'} under the \
  localization D(B) is invertible"]
theorem isIso_Q_map_midCotangentComplexMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)))) :
    IsIso (DerivedCategory.Q.map (midCotangentComplexMap A' B)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} (B : Type u))
      (midCotangentComplexMap A' B)).2 (quasiIso_midCotangentComplexMap hTor hφ)

/-- **Stacks 08QZ: `L_{B/A} = L_{B/A'}` in `D(B)`.** Let `A → A' → B` be ring maps such that
`B = B ⊗_A^𝐋 A'` — that is, `Tor_i^A(A', B) = 0` for `i > 0` and `A' ⊗_A B → B` is bijective.
Then the cotangent complexes of `B` over `A` and over `A'` are isomorphic in `D(B)`, by the
canonical map `CommAlgCat.midCotangentComplexMap` of Tag 08PN.

This is the conclusion the source states. The degreewise form,
`CommAlgCat.midCotangentComplexHomologyIso`, is a separate statement proved directly from the two
resolutions; an isomorphism of cohomology in each degree does not by itself produce an
isomorphism in `D(B)`, and the comparison here is the canonical one.

This is the whole of the tag: the hypothesis is the source's, written out, and the conclusion is
the source's, an isomorphism in `D(B)` along the canonical map. -/
@[stacks 08QZ]
def midCotangentComplexDerivedIso
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra A' B) (AlgHom.id A (B : Type u)))) :
    DerivedCategory.Q.obj (cotangentComplex.{u, u} A B) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A' (midAlgebra A' B)) :=
  have := isIso_Q_map_midCotangentComplexMap hTor hφ
  asIso (DerivedCategory.Q.map (midCotangentComplexMap A' B))

end Tower

end CommAlgCat

end
