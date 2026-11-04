module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumChartBaseChange

/-!
# The transition of a descent datum at a test space is the transition on the pair

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces over `X`, and let `D` be a descent datum for quasi-coherent modules relative to that
family.  On a test space `T` equipped with a morphism `w` to the pairwise fibre product
`Y i ×_X Y j` and the two composites `vi`, `vj` to the members, the transition of `D` is read on
the sections over a chart `U` of `T` as a bijection

`D.F i` over the chart `U ≫ vi` of `Y i`  ⟷  `D.F j` over the chart `U ≫ vj` of `Y j`,

namely `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`.  This file identifies that
reading with the reading of the pairwise isomorphism `D.transition i j` itself over the chart
of `Y i ×_X Y j` that `U` induces: a test space contributes nothing beyond the chart it presents
to the pair.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectFst` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectSnd`: a section over a chart of a
  member, carried between the two descriptions of that chart given by a factorization through
  the pairwise fibre product.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom_reading_of_test_comp`: the reading
  of the transition at a test space is the reading of the transition on the pair, at the
  tautological factorization `vi = w ≫ pairFst …`, `vj = w ≫ pairSnd …`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom_reading_of_test`: the same for an
  arbitrary factorization, with the sections carried across the two spellings of their charts by
  `.testChartSectFst` and `.testChartSectSnd`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom_test_apply`: the same
  identification before the source is read as a section of the component module.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_test`: at the tautological
  factorization the transition is the inverse image of the pairwise isomorphism, conjugated by
  the comparisons of Stacks 03LU.

## Implementation notes

For a general factorization `vi`, the chart `(smallEtalePostcomp vi hvi).obj U` of `Y i` and the
chart `(smallEtalePostcomp (pairFst …) ha).obj ((smallEtalePostcomp w hw).obj U)` are equal only
after substituting `hi`, and similarly on the target side. Sections are carried between the two
by `AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectFst` and
`AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectSnd`, which are the identity at the
tautological factorization.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-! ### The transition at a tautological factorization -/

/-- At the tautological factorization through `w : T ⟶ Y i ×_X Y j`, the transition
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn` at the test space `T` is the inverse
image along `w` of the pairwise isomorphism, conjugated by the comparisons of Stacks 03LU. -/
theorem transitionOn_test (F : ∀ i, Modules.{u, u} B S hS (Yi i).1 (Yi i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Yi f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) (w : T ⟶ pair B S hS Yi f i j) :
    ((modulePullbackCompIso B S hS w (pairFst B S hS Yi f i j)).app (F i)).symm ≪≫
        (modulePullback B S hS w).mapIso (φ i j) ≪≫
        (modulePullbackCompIso B S hS w (pairSnd B S hS Yi f i j)).app (F j) =
      transitionOn B S hS Yi f F φ i j w (w ≫ pairFst B S hS Yi f i j)
        (w ≫ pairSnd B S hS Yi f i j) rfl rfl := by
  simp [transitionOn, pullbackComparison_rfl]

/-! ### The reading at a test space -/

/-- For a chart `U` of a test space `T` mapping to `Y i ×_X Y j` by `w`, with the two tautological
composites to the members, the reading at `T` of a section of the inverse image is the reading of
the pairwise isomorphism itself over the chart of `Y i ×_X Y j` that `U` induces, once the
section is carried across the comparison of Stacks 03LU. -/
theorem transitionHom_test_apply (D : DescentDatum B S hS Yi f) {i j : I}
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    (hwb : IsEtale B S hS (w ≫ pairSnd B S hS Yi f i j).hom)
    (U : SmallEtale B S hS T.1)
    (m : ((modulePullback B S hS (w ≫ pairFst B S hS Yi f i j)).obj (D.F i)).val.obj (.op U)) :
    etaleSect B S hS (w ≫ pairSnd B S hS Yi f i j) hwb (D.F j) U
        ((transitionHom B S hS Yi f D i j w (w ≫ pairFst B S hS Yi f i j)
            (w ≫ pairSnd B S hS Yi f i j) rfl rfl).val.app (.op U) m) =
      etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
        ((smallEtalePostcomp B S hS w hw).obj U)
        ((D.transition i j).hom.val.app (.op ((smallEtalePostcomp B S hS w hw).obj U))
          (etaleSect B S hS w hw
            ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj (D.F i)) U
            (((modulePullbackCompIso B S hS w (pairFst B S hS Yi f i j)).inv.app
              (D.F i)).val.app (.op U) m))) :=
  ((congrArg (etaleSect B S hS (w ≫ pairSnd B S hS Yi f i j) hwb (D.F j) U)
        (hom_val_app_trans₃_congr B S hS
          (transitionOn_test B S hS Yi f D.F D.transition i j w)
          ((modulePullbackCompIso B S hS w (pairFst B S hS Yi f i j)).inv.app (D.F i))
          ((modulePullback B S hS w).map (D.transition i j).hom)
          ((modulePullbackCompIso B S hS w (pairSnd B S hS Yi f i j)).hom.app (D.F j))
          (transitionHom B S hS Yi f D i j w (w ≫ pairFst B S hS Yi f i j)
            (w ≫ pairSnd B S hS Yi f i j) rfl rfl)
          rfl rfl rfl rfl U m)).trans
      ((modulePullbackCompIsoEtaleRestriction B S hS).comp_app w
        (pairSnd B S hS Yi f i j) hw hb hwb (D.F j) U
        (((modulePullback B S hS w).map (D.transition i j).hom).val.app (.op U)
          (((modulePullbackCompIso B S hS w (pairFst B S hS Yi f i j)).inv.app
            (D.F i)).val.app (.op U) m)))).trans
    (congrArg (etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
        ((smallEtalePostcomp B S hS w hw).obj U))
      (etaleSect_map B S hS w hw (D.transition i j).hom U
        (((modulePullbackCompIso B S hS w (pairFst B S hS Yi f i j)).inv.app
          (D.F i)).val.app (.op U) m)))

/-- At the tautological factorization, for a chart `U` of a test space `T` mapping to
`Y i ×_X Y j` by `w`, the reading of the transition over `U` of a section of `D.F i` is the
reading of `D.transition i j` over the chart of `Y i ×_X Y j` that `U` induces. -/
theorem transitionHom_reading_of_test_comp (D : DescentDatum B S hS Yi f) {i j : I}
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (hwa : IsEtale B S hS (w ≫ pairFst B S hS Yi f i j).hom)
    (hwb : IsEtale B S hS (w ≫ pairSnd B S hS Yi f i j).hom)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS
      (w ≫ pairFst B S hS Yi f i j) hwa).obj U))) :
    etaleSect B S hS (w ≫ pairSnd B S hS Yi f i j) hwb (D.F j) U
        ((transitionHom B S hS Yi f D i j w (w ≫ pairFst B S hS Yi f i j)
            (w ≫ pairSnd B S hS Yi f i j) rfl rfl).val.app (.op U)
          (etaleSectInv B S hS (w ≫ pairFst B S hS Yi f i j) hwa (D.F i) U s)) =
      etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
        ((smallEtalePostcomp B S hS w hw).obj U)
        ((D.transition i j).hom.val.app (.op ((smallEtalePostcomp B S hS w hw).obj U))
          (etaleSectInv B S hS (pairFst B S hS Yi f i j) ha (D.F i)
            ((smallEtalePostcomp B S hS w hw).obj U) s)) :=
  (transitionHom_test_apply B S hS Yi f D w hw hb hwb U
        (etaleSectInv B S hS (w ≫ pairFst B S hS Yi f i j) hwa (D.F i) U s)).trans
    (congrArg (fun z => etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
          ((smallEtalePostcomp B S hS w hw).obj U)
        ((D.transition i j).hom.val.app (.op ((smallEtalePostcomp B S hS w hw).obj U)) z))
      (etaleSect_compIso_inv_etaleSectInv B S hS w hw (pairFst B S hS Yi f i j) ha hwa
        (D.F i) U s))

/-! ### An arbitrary factorization -/

/-- A section of `D.F i` over the chart of `Y i` induced by `vi`, read as a section over the
chart of `Y i` induced by the first projection out of the chart of `Y i ×_X Y j` induced by `U`.
Granted the factorization `hi` the two charts are the same, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp_obj_comp`. -/
def testChartSectFst (D : DescentDatum B S hS Yi f) {i j : I}
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (vi : T ⟶ Yi i) (hvi : IsEtale B S hS vi.hom)
    (hi : w ≫ pairFst B S hS Yi f i j = vi) (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    (D.F i).val.obj (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j) ha).obj
      ((smallEtalePostcomp B S hS w hw).obj U))) := by
  subst hi
  exact s

/-- At the tautological factorization the retyping of
`AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectFst` is the identity. -/
theorem testChartSectFst_rfl (D : DescentDatum B S hS Yi f) {i j : I}
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (hwa : IsEtale B S hS (w ≫ pairFst B S hS Yi f i j).hom) (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS
      (w ≫ pairFst B S hS Yi f i j) hwa).obj U))) :
    testChartSectFst B S hS Yi f D ha w hw (w ≫ pairFst B S hS Yi f i j) hwa rfl U s = s := rfl

/-- A section of `D.F j` over the chart of `Y j` induced by the second projection out of the
chart of `Y i ×_X Y j` induced by `U`, read as a section over the chart of `Y j` induced by `vj`.
This is `AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectFst` on the target side of a
transition. -/
def testChartSectSnd (D : DescentDatum B S hS Yi f) {i j : I}
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (vj : T ⟶ Yi j) (hvj : IsEtale B S hS vj.hom)
    (hj : w ≫ pairSnd B S hS Yi f i j = vj) (U : SmallEtale B S hS T.1)
    (t : (D.F j).val.obj (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j) hb).obj
      ((smallEtalePostcomp B S hS w hw).obj U)))) :
    (D.F j).val.obj (.op ((smallEtalePostcomp B S hS vj hvj).obj U)) := by
  subst hj
  exact t

/-- At the tautological factorization the retyping of
`AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectSnd` is the identity. -/
theorem testChartSectSnd_rfl (D : DescentDatum B S hS Yi f) {i j : I}
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (hwb : IsEtale B S hS (w ≫ pairSnd B S hS Yi f i j).hom) (U : SmallEtale B S hS T.1)
    (t : (D.F j).val.obj (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j) hb).obj
      ((smallEtalePostcomp B S hS w hw).obj U)))) :
    testChartSectSnd B S hS Yi f D hb w hw (w ≫ pairSnd B S hS Yi f i j) hwb rfl U t = t := rfl

/-- For a chart `U` of a test space `T` carrying a morphism `w` to `Y i ×_X Y j` and two
étale morphisms `vi`, `vj` to the members factoring through it, the reading of the transition
over `U` is the reading of `D.transition i j` over the chart of `Y i ×_X Y j` that `U` induces.
The sections are carried across the two spellings of their charts by
`AlgebraicGeometry.Space.QuasiCoherentDescent.testChartSectFst` and `.testChartSectSnd`, each of
which is the identity at the tautological factorization. -/
theorem transitionHom_reading_of_test {i j : I} (D : DescentDatum B S hS Yi f)
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (hvi : IsEtale B S hS vi.hom)
    (hvj : IsEtale B S hS vj.hom)
    (hi : w ≫ pairFst B S hS Yi f i j = vi) (hj : w ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    etaleSect B S hS vj hvj (D.F j) U
        ((transitionHom B S hS Yi f D i j w vi vj hi hj).val.app (.op U)
          (etaleSectInv B S hS vi hvi (D.F i) U s)) =
      testChartSectSnd B S hS Yi f D hb w hw vj hvj hj U
        (etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
          ((smallEtalePostcomp B S hS w hw).obj U)
          ((D.transition i j).hom.val.app (.op ((smallEtalePostcomp B S hS w hw).obj U))
            (etaleSectInv B S hS (pairFst B S hS Yi f i j) ha (D.F i)
              ((smallEtalePostcomp B S hS w hw).obj U)
              (testChartSectFst B S hS Yi f D ha w hw vi hvi hi U s)))) := by
  subst hj hi
  exact transitionHom_reading_of_test_comp B S hS Yi f D ha hb w hw hvi hvj U s

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
