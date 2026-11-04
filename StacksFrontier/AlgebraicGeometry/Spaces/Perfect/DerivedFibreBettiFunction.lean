module

public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiFieldSpaceInputs

/-!
# The Betti-number function of an object of `D(𝒪_X)` on the points of an algebraic space

For an object `E` of `D(𝒪_X)` on an algebraic space `X` over `S` the `i`-th Betti number
`AlgebraicGeometry.Space.geometricFibreBetti` of `E` at a geometric point `x̄` depends only on
the point of `|X|` below `x̄`. The function `β_i : |X| → ℕ` of Stacks 0D1Y is therefore defined
by evaluating it at a geometric representative, and its formation commutes with arbitrary base
change.

## Main definitions

* `AlgebraicGeometry.Space.geometricFibreBettiFunction` is `β_i : |X| → ℕ`.

## Main results

* `AlgebraicGeometry.Space.geometricFibreBetti_eq_of_fieldSpace`: on the algebraic space of the
  spectrum of a field the Betti numbers do not depend on the geometric point.
* `AlgebraicGeometry.Space.geometricFibreBetti_eq_of_image_eq`: the Betti numbers at two
  geometric points of `X` above the same point of `|X|` agree.
* `AlgebraicGeometry.Space.geometricFibreBettiFunction_apply`: `β_i` is the Betti number at any
  geometric representative, so the choice of representative does not matter.
* `AlgebraicGeometry.Space.geometricFibreBettiFunction_derivedPullback`: clause (1) of
  Stacks 0D1Y, formation of `β_i` commutes with arbitrary base change.

## Implementation notes

*What the independence proof uses.* Let `x̄` be a geometric point of `X` with field `k`, write
`Y` for the algebraic space of `Spec k` and let `v` be a geometric point of `Y` with field `K`.
The Betti number of `M ∈ D(𝒪_Y)` at `v` is computed on the algebraic space `Z` of `Spec K`:
it is the dimension over `Γ(Spec K, 𝒪)` of the sections of `H^i(Lv^*M)` over the identity chart
(`AlgebraicGeometry.Space.geometricFibreBetti_eq_finrank_idChart`), hence the dimension of the
stalk of `H^i(Lv^*M)` at the tautological point of `Z`
(`AlgebraicGeometry.Space.finrank_idChart_eq_finrank_moduleStalk`). The morphism `Z ⟶ Y` is
flat, so `H^i(Lv^*M) ≅ v^*H^i(M)`, and Stacks 05VQ computes the stalk of `v^*H^i(M)` at the
tautological point as the extension of scalars of the stalk of `H^i(M)` at `v`. Both stalk
rings are fields, so the extension of scalars does not change the dimension; the resulting
dimension of the stalk of `H^i(M)` at `v` is the dimension of the sections of `H^i(M)` over the
identity chart of `Y`, which no longer mentions `v`.

*The two spellings of the stalk ring.* The stalk of the structure sheaf occurs both as
`AlgebraicGeometry.Space.geometricStalkRing` and as `Stacks.ringFiber` of the underlying
presheaf, and the two are equal only at default transparency. The chain below therefore passes
the two field witnesses to `AlgebraicGeometry.SpecField.finrank_extendScalars` explicitly and is
assembled with `Eq.trans`, so that no instance has to be synthesized across that equality.

*Pseudo-coherence.* The source takes values of `β_i` in `{0, 1, 2, …} ∪ {∞}` for a general
object and asserts the three clauses for a pseudo-coherent one, which is what makes `β_i` finite
and so makes the `ℕ`-valued function below the source's. The hypothesis is therefore carried by
clause (1) although the proof of that clause needs nothing of it.

*The derived-category model.* The objects spoken about here live in Mathlib's standard model, the
one `AlgebraicGeometry.Space.geometricFibreBetti` is stated at, and that model is named in the
binders rather than installed as an instance for the file.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-! ### Independence of the geometric point -/

/-- **On the algebraic space of the spectrum of a field the Betti numbers do not depend on the
geometric point.** Both are the dimension of the sections of `H^i(M)` over the identity
chart. -/
theorem geometricFibreBetti_eq_of_fieldSpace (p : GeometricPoint B S hS X.1)
    (M : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (fieldValuedPointSpace B S hS p.val))) _ _ (HasDerivedCategory.standard _))
    (i : ℤ) (z w : GeometricPoint B S hS (fieldValuedPointSpace B S hS p.val).1) :
    geometricFibreBetti B S hS M i z = geometricFibreBetti B S hS M i w := by
  let _ := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (fieldValuedPointSpace B S hS p.val)))
  have hp := p.property
  have key : ∀ v : GeometricPoint B S hS (fieldValuedPointSpace B S hS p.val).1,
      geometricFibreBetti B S hS M i v =
        Module.finrank
          ((ringedToposStructureRingSheaf B S hS
            (fieldValuedPointSpace B S hS p.val)).obj.obj
              (op (idChart B S hS p.val.siteObject)))
          (((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS
                (fieldValuedPointSpace B S hS p.val))) i).obj M).val.obj
            (op (idChart B S hS p.val.siteObject))) := by
    intro v
    have hv := v.property
    refine Eq.trans (geometricFibreBetti_eq_finrank_idChart B S hS M i v) ?_
    refine Eq.trans (finrank_idChart_eq_finrank_moduleStalk B S hS v.val
      (tautologicalGeometricPoint B S hS v) _) ?_
    refine Eq.trans (((Stacks.sheafModuleFiberOfCommRing (tautPoint B S hS v)
      (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS v.val)).O).mapIso
        (homologyDerivedPullbackIsoOfIsFlat B S hS (fieldHom B S hS v.val)
          (isFlat_fieldHom B S hS p.val v) i M)).toLinearEquiv.finrank_eq) ?_
    refine Eq.trans (((modulePullbackFiberIso B S hS (fieldHom B S hS v.val)
      (tautologicalGeometricPoint B S hS v)).app
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS
            (fieldValuedPointSpace B S hS p.val))) i).obj M)).toLinearEquiv.finrank_eq) ?_
    refine Eq.trans (AlgebraicGeometry.SpecField.finrank_extendScalars
      (isField_geometricStalkRing_fieldValuedPointSpace B S hS p.val
        (geometricPointMap (fieldHom B S hS v.val).hom
          (tautologicalGeometricPoint B S hS v)))
      (isField_geometricStalkRing_fieldValuedPointSpace B S hS v.val
        (tautologicalGeometricPoint B S hS v))
      (CommRingCat.ofHom (smallEtaleStalkPullbackRingMap B S hS (fieldHom B S hS v.val)
        (tautologicalGeometricPoint B S hS v))) _) ?_
    refine Eq.trans (congrArg
      (fun t : GeometricPoint B S hS (fieldValuedPointSpace B S hS p.val).1 =>
        Module.finrank
          (Stacks.ringFiber (etaleSitePoint B S hS (fieldValuedPointSpace B S hS p.val).1 t
            (fieldValuedPointSpace B S hS p.val).2)
            (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p.val)).O.obj)
          ((Stacks.sheafModuleFiberOfCommRing
              (etaleSitePoint B S hS (fieldValuedPointSpace B S hS p.val).1 t
                (fieldValuedPointSpace B S hS p.val).2)
              (smallEtaleRingedTopos B S hS (fieldValuedPointSpace B S hS p.val)).O).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS
                (fieldValuedPointSpace B S hS p.val))) i).obj M)))
      (geometricPointMap_fieldMorphism_tautological B S hS v)) ?_
    exact (finrank_idChart_eq_finrank_moduleStalk B S hS p.val v _).symm
  exact (key z).trans (key w).symm

/-- **The Betti numbers at two geometric points above the same point of `|X|` agree.** -/
theorem geometricFibreBetti_eq_of_image_eq
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (i : ℤ) (x y : GeometricPoint B S hS X.1) (h : x.image = y.image) :
    geometricFibreBetti B S hS E i x = geometricFibreBetti B S hS E i y :=
  geometricFibreBetti_eq_of_image_eq_of_fieldSpace B S hS E i
    (fun p M z w => geometricFibreBetti_eq_of_fieldSpace B S hS p M i z w) x y h

/-! ### The Betti-number function on the points -/

/-- **The `i`-th Betti-number function `β_i : |X| → ℕ` of an object of `D(𝒪_X)`**: the `i`-th
Betti number at the canonical geometric representative of the point, independent of the choice
of representative by `geometricFibreBettiFunction_apply`. -/
def geometricFibreBettiFunction
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (i : ℤ) (x : points B S hS X.1) : ℕ :=
  geometricFibreBetti B S hS E i (canonicalGeometricPoint B S hS X.1 x)

/-- **The Betti-number function is the Betti number at any geometric representative.** This is
the independence of the choice of representative. -/
theorem geometricFibreBettiFunction_apply
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (i : ℤ) (x : GeometricPoint B S hS X.1) :
    geometricFibreBettiFunction B S hS E i x.image = geometricFibreBetti B S hS E i x :=
  geometricFibreBetti_eq_of_image_eq B S hS E i _ x
    (canonicalGeometricPoint_image B S hS X.1 x.image)

/-- **Stacks 0D1Y, clause (1): formation of `β_i` commutes with arbitrary base change.** For a
morphism `g : Y ⟶ X` of algebraic spaces the Betti-number function of `Lg^*E` is the Betti-number
function of `E` composed with the map `|Y| → |X|`. -/
@[stacks 0D1Y "clause (1)"]
theorem geometricFibreBettiFunction_derivedPullback {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (_hE : @AlgebraicGeometry.RingedSite.IsPseudoCoherent
      (smallEtaleRingedSite B S hS X.1 X.2) _ _ _ _ _ _ (HasDerivedCategory.standard _) E)
    (i : ℤ) :
    geometricFibreBettiFunction B S hS ((smallEtaleDerivedModulePullback B S hS g).obj E) i =
      geometricFibreBettiFunction B S hS E i ∘ pointsMap B S hS Y.1 g.hom := by
  funext y
  have himg : (geometricPointMap g.hom (canonicalGeometricPoint B S hS Y.1 y)).image =
      pointsMap B S hS Y.1 g.hom y := by
    rw [geometricPointMap_image, canonicalGeometricPoint_image]
  exact (geometricFibreBetti_derivedPullback B S hS g E i
      (canonicalGeometricPoint B S hS Y.1 y)).trans
    ((geometricFibreBettiFunction_apply B S hS E i
        (geometricPointMap g.hom (canonicalGeometricPoint B S hS Y.1 y))).symm.trans
      (congrArg (geometricFibreBettiFunction B S hS E i) himg))

end AlgebraicGeometry.Space

end
