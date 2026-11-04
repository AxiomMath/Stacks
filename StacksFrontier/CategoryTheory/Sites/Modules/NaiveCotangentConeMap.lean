module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentTowerConeMap

/-!
# The canonical map from a base-changed naive cotangent complex to a shifted cone

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a site.  The
naive cotangent complexes of the three morphisms `a`, `a ≫ b` and `b` are related by two
canonical chain maps of complexes of sheaves of `C`-modules,

`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`  and  `g : NL_{C/A} ⟶ NL_{C/B}`,

the first being the adjoint of the map of Stacks 08TX for the square with vertical morphisms
`𝟙 A` and `b`, and the second the map of Stacks 08TX for the square with vertical morphisms `a`
and `𝟙 C`.  This file proves that the composite `c₁ ≫ g` is null homotopic and deduces, from
Stacks 08RI (2), a factorisation

`c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]`

of `c₁` through the shift by `-1` of the cone of `g`.  This is the canonical map of
**Stacks 0E1Y**, whose low-degree cohomology is the six-term exact sequence attached to the
tower `A ⟶ B ⟶ C`.

The null homotopy comes from the tower: extension of scalars along `b` is left adjoint to
restriction of scalars along `b`, so `c₁ ≫ g` is the adjoint transpose of the `B`-linear
composite

`NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}`,

which by the compatibility of Stacks 08TX with composition of squares is the single map
attached to the square with horizontal morphisms `a` and `b` and vertical morphisms `a` and
`b`.  That square factors through the identity of `B` in the sense of
`Stacks.SheafOfModules.naiveCotangentTowerNullHomotopy`, which therefore supplies a null
homotopy; transporting it across the adjunction gives one for `c₁ ≫ g`.

## Main definitions

* `Stacks.SheafOfModules.towerNaiveCotangentSquareMap`: the `B`-linear chain map
  `NL_{B/A} ⟶ NL_{C/B}` attached to the square with horizontal morphisms `a` and `b` and
  vertical morphisms `a` and `b`.
* `Stacks.SheafOfModules.baseChangeRelativeNullHomotopy`: the null homotopy of `c₁ ≫ g`.
* `Stacks.SheafOfModules.naiveCotangentConeMap`: the canonical map
  `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]`.

## Main results

* `Stacks.SheafOfModules.baseChangeNaiveCotangentMap_comp_relative`: the composite `c₁ ≫ g` is
  the adjoint transpose of `towerNaiveCotangentSquareMap`.
* `Stacks.SheafOfModules.baseChangeRelativeNullHomotopy_hom_zero_negOne`: **the null homotopy of
  `c₁ ≫ g` is the extension of scalars of the explicit homotopy of the tower.**  In its single
  nonzero bidegree `(0, -1)` it is `naiveCotangentTowerHomotopy` with scalars extended along
  `b`, followed by the counit.  Combined with
  `Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`, which
  gives the value of that homotopy on `1 ⊗ d[t]`, this identifies the homotopy occurring in
  `naiveCotangentConeMap_comp_snd` with the map `d[b] ⊗ 1 ↦ [φ(b)] - b[1]` of the proof of
  Stacks 0E1Y.
* `Stacks.SheafOfModules.naiveCotangentConeMap_comp_pShift`: the canonical map `c` composed
  with the shifted projection `C(g)[-1] ⟶ NL_{C/A}` of the cone is `c₁`.
* `Stacks.SheafOfModules.naiveCotangentConeMap_comp_snd`: the canonical map `c` composed with
  the degree `-1` projection `C(g)[-1] ⟶ NL_{C/B}` of the cone is the null homotopy of
  `c₁ ≫ g`.  The two together are the pair of components that Stacks 08RI (2) produces, so
  they determine `c`.

## Implementation notes

The square with vertical morphisms `𝟙 A` and `b` followed by the square with vertical
morphisms `a` and `𝟙 C` is the square with vertical morphisms `𝟙 A ≫ a` and `b ≫ 𝟙 C`.
Writing the composite in that form forces the elaborator to identify restriction of scalars
along `b ≫ 𝟙 C` with restriction of scalars along `b` inside a complex, which is expensive;
the target of `towerNaiveCotangentSquareMap` is therefore written with `b` itself, the two
commutativity proofs being definitionally irrelevant.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of
  the naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), part (2),
  factorisation through a shifted cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {S : Type u} [Category.{v} S] (J : GrothendieckTopology S)
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable (A B C : Sheaf J CommRingCat.{max u v w}) (a : A ⟶ B) (b : B ⟶ C)

/-! ### The composite of the two canonical chain maps -/

/-- The map of Stacks 08TX for the square whose horizontal morphisms are `a : A ⟶ B` and
`b : B ⟶ C` and whose vertical morphisms are again `a` and `b`: the `B`-linear chain map
`NL_{B/A} ⟶ NL_{C/B}`. -/
noncomputable abbrev towerNaiveCotangentSquareMap :=
  naiveCotangentComplexMapOfSquare.{v, u, max u v w, max u v w} J A B a B C b a b rfl

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The map of Stacks 08TX for the square with vertical morphisms `𝟙 A` and `b`, followed by
restriction of scalars of the map for the square with vertical morphisms `a` and `𝟙 C`, is the
map for the square with vertical morphisms `a` and `b`. -/
theorem baseChangeSquareMap_comp_relativeNaiveCotangentComplexMap :
    baseChangeSquareMap.{v, u, w} J A B C a b ≫
        (towerRestrictScalarsComplexes.{v, u, w} J B C b).map
          (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) =
      towerNaiveCotangentSquareMap.{v, u, w} J A B C a b :=
  naiveCotangentComplexMapOfSquare_comp.{v, u, max u v w, max u v w} J A B a A C (a ≫ b)
    (𝟙 A) b (Category.id_comp (a ≫ b)).symm B C b a (𝟙 C)
    (comp_id_eq_comp_of_fac J A C (a ≫ b) B b a rfl)

/-- The composite `NL_{B/A} ⊗_B C ⟶ NL_{C/A} ⟶ NL_{C/B}` is the adjoint transpose of the
`B`-linear chain map `NL_{B/A} ⟶ NL_{C/B}` attached to the square with horizontal and vertical
morphisms `a` and `b`. -/
theorem baseChangeNaiveCotangentMap_comp_relative :
    baseChangeNaiveCotangentMap.{v, u, w} J A B C a b ≫
        relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b =
      (towerExtendScalarsComplexes.{v, u, w} J B C b).map
          (towerNaiveCotangentSquareMap.{v, u, w} J A B C a b) ≫
        towerCounit.{v, u, w} J B C b
          (naiveCotangentComplex.{v, u, max u v w, max u v w} J B C b) := by
  rw [baseChangeNaiveCotangentMap, Category.assoc,
    ← towerCounit_naturality J B C b (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b),
    ← Category.assoc, ← Functor.map_comp,
    baseChangeSquareMap_comp_relativeNaiveCotangentComplexMap]

/-! ### The null homotopy -/

/-- **The `B`-linear chain map `NL_{B/A} ⟶ NL_{C/B}` of the tower is null homotopic.**  The
homotopy is concentrated in bidegree `(0, -1)`, where it sends a local section `x ⊗ d t` to
`x · ([b t] - t)`, the conormal class of the difference between the variable `[b t]` of the
canonical presentation `B[C] ⟶ C` and the coefficient `t`. -/
noncomputable def towerNaiveCotangentSquareMapNullHomotopy :
    Homotopy (towerNaiveCotangentSquareMap.{v, u, w} J A B C a b) 0 :=
  naiveCotangentTowerNullHomotopy.{v, u, max u v w, max u v w} J A B C a b a b (𝟙 B)
    (Category.id_comp b) (Category.comp_id a)

/-- **The composite `NL_{B/A} ⊗_B C ⟶ NL_{C/A} ⟶ NL_{C/B}` is null homotopic.**  Extension of
scalars is additive, so it carries the null homotopy of the `B`-linear chain map of the tower
to a null homotopy of its adjoint transpose. -/
noncomputable def baseChangeRelativeNullHomotopy :
    Homotopy (baseChangeNaiveCotangentMap.{v, u, w} J A B C a b ≫
      relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) 0 :=
  (Homotopy.ofEq (baseChangeNaiveCotangentMap_comp_relative.{v, u, w} J A B C a b)).trans
    ((((towerExtendScalars.{v, u, w} J B C b).mapHomotopy
          (towerNaiveCotangentSquareMapNullHomotopy.{v, u, w} J A B C a b)).compRight
        (towerCounit.{v, u, w} J B C b
          (naiveCotangentComplex.{v, u, max u v w, max u v w} J B C b))).trans
      (Homotopy.ofEq (by rw [Functor.map_zero, Limits.zero_comp])))

/-- **The null homotopy of `c₁ ≫ g` is the extension of scalars of the explicit homotopy of the
tower.**  In its single nonzero bidegree `(0, -1)` the null homotopy of `c₁ ≫ g` is the
extension of scalars along `b` of `naiveCotangentTowerHomotopy`, followed by the counit of
extension and restriction of scalars.

Together with
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`, which
says that `naiveCotangentTowerHomotopy` sends `1 ⊗ d[t]` to the conormal class of `[b t] - t`,
this identifies the homotopy appearing in `naiveCotangentConeMap_comp_snd` with the map
`d[b] ⊗ 1 ↦ [φ(b)] - b[1]` of the proof of Stacks 0E1Y. -/
theorem baseChangeRelativeNullHomotopy_hom_zero_negOne :
    (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b).hom 0 (-1) =
      (towerExtendScalars J B C b).map
            (eqToHom (naiveCotangentComplex_X_zero.{v, u, max u v w, max u v w} J A B a) ≫
              naiveCotangentTowerHomotopy.{v, u, max u v w, max u v w} J A B C a b a b (𝟙 B)
                (Category.id_comp b) (Category.comp_id a)) ≫
          (towerExtendRestrictAdjunction J B C b).counit.app
            ((canonicalConormalSequence.{v, u, max u v w, max u v w} J B C b).X₁) ≫
        eqToHom (naiveCotangentComplex_X_negOne.{v, u, max u v w, max u v w} J B C b).symm := by
  have hhom : (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b).hom 0 (-1) =
      (towerExtendScalars J B C b).map
          ((towerNaiveCotangentSquareMapNullHomotopy.{v, u, w} J A B C a b).hom 0 (-1)) ≫
        (towerCounit.{v, u, w} J B C b
          (naiveCotangentComplex.{v, u, max u v w, max u v w} J B C b)).f (-1) := by
    simp [baseChangeRelativeNullHomotopy]
  rw [hhom, towerCounit_f, show (towerNaiveCotangentSquareMapNullHomotopy.{v, u, w}
        J A B C a b).hom 0 (-1) =
      naiveCotangentTowerHomotopyHom.{v, u, max u v w, max u v w} J A B C a b a b (𝟙 B)
        (Category.id_comp b) (Category.comp_id a) from
      naiveCotangentTowerHomotopyBigraded_zero_negOne.{v, u, max u v w, max u v w}
        J A B C a b a b (𝟙 B) (Category.id_comp b) (Category.comp_id a),
    naiveCotangentTowerHomotopyHom, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, towerCounit_app_naturality J B C b
      (eqToHom (naiveCotangentComplex_X_negOne.{v, u, max u v w, max u v w} J B C b).symm),
    ← Category.assoc, ← Functor.map_comp]

/-! ### The canonical map to the shifted cone -/

/-- **The canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]`** of Stacks 0E1Y, where `C(g)` is the
cone of the canonical chain map `g : NL_{C/A} ⟶ NL_{C/B}`.  It is the explicit factorisation of
Stacks 08RI (2) of `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` through `C(g)[-1]` attached to the null
homotopy `baseChangeRelativeNullHomotopy` of `c₁ ≫ g`: its component along the shifted
projection is `c₁` (`naiveCotangentConeMap_comp_pShift`) and its component along the degree
`-1` projection of the cone is that null homotopy
(`naiveCotangentConeMap_comp_snd`). -/
noncomputable def naiveCotangentConeMap :
    baseChangeNaiveCotangentComplex.{v, u, w} J A B C a b ⟶
      (CategoryTheory.shiftFunctor
          (CochainComplex (_root_.SheafOfModules.{max u v w}
            (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ) (-1 : ℤ)).obj
        (CochainComplex.mappingCone
          (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)) :=
  factorThroughShiftedMappingCone
    (baseChangeNaiveCotangentMap.{v, u, w} J A B C a b)
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)
    (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b)

/-- The canonical map `c` of Stacks 0E1Y, composed with the projection `C(g)[-1] ⟶ NL_{C/A}` of
the shifted cone, is the canonical map `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`. -/
theorem naiveCotangentConeMap_comp_pShift :
    naiveCotangentConeMap.{v, u, w} J A B C a b ≫
        pShift (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) =
      baseChangeNaiveCotangentMap.{v, u, w} J A B C a b :=
  factorThroughShiftedMappingCone_comp_pShift
    (baseChangeNaiveCotangentMap.{v, u, w} J A B C a b)
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)
    (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b)

/-- The canonical map `c` of Stacks 0E1Y, composed with the degree `-1` projection
`C(g)[-1] ⟶ NL_{C/B}` of the shifted cone, is the null homotopy of `c₁ ≫ g` read as a cochain
of degree `-1`.  Together with `naiveCotangentConeMap_comp_pShift` this determines `c`: it is
the map built from the pair `(c₁, the explicit homotopy)` of the proof of Stacks 0E1Y, not an
arbitrary lift of `c₁`. -/
theorem naiveCotangentConeMap_comp_snd :
    (CochainComplex.HomComplex.Cochain.ofHom
          (naiveCotangentConeMap.{v, u, w} J A B C a b)).comp
        ((CochainComplex.mappingCone.snd
            (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)).leftShift (-1) (-1)
          (by omega)) (by omega) =
      CochainComplex.HomComplex.Cochain.ofHomotopy
        (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b) :=
  factorThroughShiftedMappingCone_comp_snd
    (baseChangeNaiveCotangentMap.{v, u, w} J A B C a b)
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)
    (baseChangeRelativeNullHomotopy.{v, u, w} J A B C a b)

end Stacks.SheafOfModules

end
