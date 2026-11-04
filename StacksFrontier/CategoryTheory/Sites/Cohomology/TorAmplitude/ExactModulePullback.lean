module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude along an exact functor of modules between two ringed sites

Let `(C, O)` and `(C', O')` be ringed sites whose structure sheaves have sections in one
universe, and let `P : Mod(O) ⥤ Mod(O')` be an exact additive functor, with
`LP : D(O) ⥤ D(O')` the functor it induces on the unbounded derived categories.

An object `E` of `D(O)` of Tor amplitude in `[a, b]` has a representative by a complex of flat
`O`-modules concentrated in `[a, b]`; if `P` carries flat modules to flat modules, the image
complex is again of that shape, so `LP E` has Tor amplitude in `[a, b]`.  Conversely, if `P`
reflects zero objects and the two derived tensor products are compatible along `P`, then Tor
amplitude of `LP E` forces Tor amplitude of `E`, because the cohomology sheaves of
`E ⊗^L F` are carried to the cohomology sheaves of `LP E ⊗^L P F`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_mapDerivedCategory`: Tor
  amplitude in `[a, b]` is preserved by an exact functor of modules carrying flat modules to
  flat modules.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_mapDerivedCategory`: Tor
  amplitude in `[a, b]` is reflected by an exact functor of modules which reflects zero objects
  and is compatible with the two derived tensor products.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_mapDerivedCategory_iff` and
  `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_mapDerivedCategory_iff`:
  the two statements combined, for an interval and for finite Tor dimension.

## Implementation notes

The preservation statement is the argument of Stacks 08H5 run for a functor of modules rather
than for a derived pullback along a morphism of ringed topoi.  That generality is what the
small étale comparison of Stacks 08H7 needs: its two sites have objects in different universes,
so it is not a morphism of ringed topoi in the sense of
`AlgebraicGeometry.RingedToposSiteHom` between ringed topoi sharing all three universes, which
is the shape
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedPullback` is stated at.
Nothing is lost by dropping the geometric datum: the proof uses only exactness of the functor
and its effect on flat modules.

The objects and the morphisms of the two sites have independent universes; the sections of the
two structure sheaves share the universe `max u v` of the source site, which is what Stacks
08G1 needs in order to produce the flat representative.  Only the source site is constrained
that way: the direction which consumes a flat representative,
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`, is
available at an arbitrary sections universe.  The two derived categories have independent hom
universes `d` and `d'`.

Compatibility of the derived tensor products along `P` is asked for only at a module placed in
degree zero on the second factor, which is all that the Tor-amplitude predicate examines, and
in the inverse-image form `LP E ⊗^L (P F)[0] ≅ LP (E ⊗^L F[0])`.  Reflection of zero objects
is asked for as a bare implication rather than as faithfulness of `P`, from which it follows;
on an additive functor between abelian categories the two are equivalent.

## References

* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v u' v' d d'

namespace Stacks.SheafOfModules.DerivedTensorProduct

-- The sections universe is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, max u v}} {X' : RingedSite.{u', v', max u v}}
  [HasSheafify X.J AddCommGrpCat.{max u v}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify X'.J AddCommGrpCat.{max u v}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} X)]
  [HasDerivedCategory.{d'} (RingedSite.Modules.{u', v', max u v} X')]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
    X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', max u v, max u v, max u v} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', max u v, max u v, max u v}
    X'.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u', v', max u v} X') ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)
      (ComplexShape.up ℤ)]
  (P : RingedSite.Modules.{u, v, max u v} X ⥤ RingedSite.Modules.{u', v', max u v} X')
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (T : DerivedTensorProduct.{u, v, max u v, d} X)
  (T' : DerivedTensorProduct.{u', v', max u v, d'} X')

/-! ### Preservation -/

section Preservation

variable (hPflat : ∀ M : RingedSite.Modules.{u, v, max u v} X,
  AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := X.O) M →
    AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', max u v, max u v} (O := X'.O) (P.obj M))

include hPflat in
/-- **Tor amplitude in a nonempty interval is preserved by an exact functor of modules which
preserves flatness.**

Stacks 08G1 represents `E` by a complex `K` of flat `O`-modules concentrated in `[a, b]`.  Then
`P` applied degreewise to `K` has flat terms, is still concentrated in `[a, b]` since `P` is
additive, and represents `LP E` since `P` is exact; the direction of Stacks 08G1 which takes no
input concludes. -/
theorem hasTorAmplitude_mapDerivedCategory_of_le
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' (P.mapDerivedCategory.obj E) a b := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ := exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
  refine hasTorAmplitude_of_flatRepresentative T' _ a b
    ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (fun i => hPflat _ (hflat i)) (fun i hi => P.map_isZero (hzero i hi)) ?_
  exact (P.mapDerivedCategoryFactors.app K).symm ≪≫ P.mapDerivedCategory.mapIso e

include hPflat in
/-- **Tor amplitude is preserved by an exact functor of modules which preserves flatness.**

A degenerate interval `b < a` says that the derived tensor products of `E` with every module
vanish in *every* degree, so `E` has Tor amplitude in the one-point interval `[i + 1, i + 1]`
for whichever degree `i` is being examined, and
`hasTorAmplitude_mapDerivedCategory_of_le` applies there. -/
theorem hasTorAmplitude_mapDerivedCategory
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) (a b : ℤ)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' (P.mapDerivedCategory.obj E) a b := by
  by_cases hab : a ≤ b
  · exact hasTorAmplitude_mapDerivedCategory_of_le P T T' hPflat E a b hab hamp
  · intro F i _
    have hamp' : HasTorAmplitude T E (i + 1) (i + 1) :=
      fun G j _ => hamp G j (by simp only [Set.mem_Icc]; omega)
    exact hasTorAmplitude_mapDerivedCategory_of_le P T T' hPflat E (i + 1) (i + 1) le_rfl hamp'
      F i (by simp only [Set.mem_Icc]; omega)

include hPflat in
/-- **Finite Tor dimension is preserved by an exact functor of modules which preserves
flatness**: an interval containing the Tor amplitude of `E` contains that of `LP E`. -/
theorem hasFiniteTorDimension_mapDerivedCategory
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' (P.mapDerivedCategory.obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_mapDerivedCategory P T T' hPflat E a b hamp⟩

end Preservation

/-! ### Reflection -/

section Reflection

variable (hPzero : ∀ M : RingedSite.Modules.{u, v, max u v} X, IsZero (P.obj M) → IsZero M)
  (hPtensor : ∀ (E : RingedSite.DerivedModules.{u, v, max u v, d} X)
      (F : RingedSite.Modules.{u, v, max u v} X),
    (T'.tensor.obj (P.mapDerivedCategory.obj E)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u', v', max u v} X') 0).obj
          (P.obj F)) ≅
      P.mapDerivedCategory.obj ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, max u v} X) 0).obj F)))

include hPzero hPtensor in
/-- **Tor amplitude in `[a, b]` is reflected by an exact functor of modules which reflects zero
objects and is compatible with the two derived tensor products.**

For a module `F` on the source, `LP E ⊗^L (P F)[0]` is `LP (E ⊗^L F[0])`, whose cohomology in
degree `i` is `P` applied to the cohomology of `E ⊗^L F[0]` in degree `i`, exactness of `P`
commuting with the homology of the derived category.  Vanishing of the former therefore forces
vanishing of the latter. -/
theorem hasTorAmplitude_of_mapDerivedCategory
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) (a b : ℤ)
    (hamp : HasTorAmplitude T' (P.mapDerivedCategory.obj E) a b) :
    HasTorAmplitude T E a b := by
  intro F i hi
  refine hPzero _ ?_
  refine ((hamp (P.obj F) i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u', v', max u v} X') i).mapIso
      (hPtensor E F).symm)).of_iso ?_
  exact ((P.mapDerivedCategoryHomologyIso i).app
    ((T.tensor.obj E).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, max u v} X) 0).obj F))).symm

include hPzero hPtensor in
/-- **Finite Tor dimension is reflected** under the hypotheses of
`hasTorAmplitude_of_mapDerivedCategory`. -/
theorem hasFiniteTorDimension_of_mapDerivedCategory
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X)
    (h : HasFiniteTorDimension T' (P.mapDerivedCategory.obj E)) :
    HasFiniteTorDimension T E := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_of_mapDerivedCategory P T T' hPzero hPtensor E a b hamp⟩

end Reflection

/-! ### The two directions combined -/

section Iff

variable (hPflat : ∀ M : RingedSite.Modules.{u, v, max u v} X,
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := X.O) M →
      AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', max u v, max u v} (O := X'.O) (P.obj M))
  (hPzero : ∀ M : RingedSite.Modules.{u, v, max u v} X, IsZero (P.obj M) → IsZero M)
  (hPtensor : ∀ (E : RingedSite.DerivedModules.{u, v, max u v, d} X)
      (F : RingedSite.Modules.{u, v, max u v} X),
    (T'.tensor.obj (P.mapDerivedCategory.obj E)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u', v', max u v} X') 0).obj
          (P.obj F)) ≅
      P.mapDerivedCategory.obj ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, max u v} X) 0).obj F)))

include hPflat hPzero hPtensor in
/-- **Tor amplitude in `[a, b]` holds for `E` exactly when it holds for `LP E`**, for an exact
functor of modules which preserves flatness, reflects zero objects and is compatible with the
two derived tensor products. -/
theorem hasTorAmplitude_mapDerivedCategory_iff
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) (a b : ℤ) :
    HasTorAmplitude T E a b ↔ HasTorAmplitude T' (P.mapDerivedCategory.obj E) a b :=
  ⟨hasTorAmplitude_mapDerivedCategory P T T' hPflat E a b,
    hasTorAmplitude_of_mapDerivedCategory P T T' hPzero hPtensor E a b⟩

include hPflat hPzero hPtensor in
/-- **Finite Tor dimension holds for `E` exactly when it holds for `LP E`**, under the
hypotheses of `hasTorAmplitude_mapDerivedCategory_iff`. -/
theorem hasFiniteTorDimension_mapDerivedCategory_iff
    (E : RingedSite.DerivedModules.{u, v, max u v, d} X) :
    HasFiniteTorDimension T E ↔ HasFiniteTorDimension T' (P.mapDerivedCategory.obj E) :=
  ⟨hasFiniteTorDimension_mapDerivedCategory P T T' hPflat E,
    hasFiniteTorDimension_of_mapDerivedCategory P T T' hPzero hPtensor E⟩

end Iff

end Stacks.SheafOfModules.DerivedTensorProduct

end
