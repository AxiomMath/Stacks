module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A direct summand of a finite free sheaf of modules is flat

Let `(C, O)` be a ringed site. A finite free `O`-module is flat, and hence so is every direct
summand of one; consequently every term of a strictly perfect complex (Stacks 08FL) is a flat
`O`-module.

This is the sentence "a direct summand of a finite free module is flat" which the source uses
without comment in the proofs of Stacks 08G7 and Stacks 08G8.

## Main results

* `Stacks.SheafOfModules.isFlat_free`: a free `O`-module on a finite index type is flat.
* `Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree`: a direct summand of a finite
  free `O`-module is flat.
* `Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect`: every term of a strictly perfect
  complex of `O`-modules is flat.

## Implementation notes

The free `O`-module on an index type is *by definition* the coproduct of copies of the structure
sheaf, `SheafOfModules.free I = ∐ (fun _ : I ↦ unit O)`, so a finite free module is flat by the
direct-sum clause of Stacks 05NG, `Stacks.SheafOfModules.FlatColimits.isFlat_coproduct_finite`,
applied to the flatness of the structure sheaf
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`. A direct summand is then flat because
a retract of a flat module is, `Stacks.SheafOfModules.FlatRetract.isFlat_of_retract`.

The predicate used is the `IsDirectSummandOfFiniteFree` of Stacks 08FM which
`IsStrictlyPerfect` is stated against; at a module universe equal to the universe of the
sections of the structure sheaf — which is where strictly perfect complexes on a ringed site
live — it is the plain retract condition, by `isDirectSummandOfFiniteFree_iff_free`.

The ringed-space analogue is
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree`,
whose proof is different: there flatness is checked objectwise on the presheaf level, using that
a retract of a free module over a ring is a flat module, and transported along sheafification.
Neither statement specialises to the other, the two `IsDirectSummandOfFiniteFree` predicates
being about a ringed space and about a site respectively.

The universe of the sections is `max u v`, `u` and `v` being the object and the morphism
universes of the site. That is forced, not chosen: it is where the flatness of the structure
sheaf is available, the unit law it rests on being read off the monoidal structure on `Mod(O)`;
see the implementation notes of `Stacks.SheafOfModules.sheafTensorUnitNatIso`.

## References

* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **A finite free `O`-module is flat.** The free `O`-module on an index type is the coproduct
of copies of the structure sheaf indexed by it, the structure sheaf is flat, and a finite direct
sum of flat modules is flat by Stacks 05NG. -/
theorem isFlat_free (I : Type (max u v)) [Finite I] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
      (_root_.SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) I) :=
  FlatColimits.isFlat_coproduct_finite Y.O
    (fun _ : I => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    fun _ => DerivedTensorProduct.isFlat_unit

/-- **A direct summand of a finite free `O`-module is flat.** The module is a retract of a
finite free `O`-module, which is flat by `isFlat_free`, and a retract of a flat module is
flat. -/
theorem isFlat_of_isDirectSummandOfFiniteFree
    (F : AlgebraicGeometry.RingedSite.Modules.{u, v, max u v} Y)
    (hF : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) F := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF
  exact FlatRetract.isFlat_of_retract Y.O i r hir (isFlat_free (ULift.{max u v} (Fin n)))

/-- **Every term of a strictly perfect complex of `O`-modules is flat.** The terms are direct
summands of finite free `O`-modules, which are flat. -/
theorem isFlat_X_of_isStrictlyPerfect
    {P : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, max u v} Y) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (P.X i) :=
  isFlat_of_isDirectSummandOfFiniteFree (P.X i) (hP.termDirectSummand i)

/-- **A strictly perfect complex of `O|_V`-modules on a slice of a ringed site is K-flat**:
its terms are direct summands of finite free `O|_V`-modules, hence flat, and only finitely
many of them are nonzero, so the complex is bounded above; Stacks 06YQ concludes.

This is the statement on the slice `C/V`; the one on the site itself is
`AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect`, which is phrased with the
predicate `Stacks.SheafOfModules.IsKFlat` rather than `Stacks.SheafOfModules.KFlat`. -/
theorem kFlat_over_of_isStrictlyPerfect (X : RingedSite.{u, v, max u v})
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{max u v}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (V : X.C)
    (P : CochainComplex
      (_root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P) :
    KFlat (X.O.over V) P := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun i hi => ?_
    by_contra h
    exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)
  exact kFlat_of_boundedAbove_of_flat (X.O.over V) P ⟨r, hLE⟩
    fun i => isFlat_X_of_isStrictlyPerfect (Y := X.over V) hP i

end Stacks.SheafOfModules

end
