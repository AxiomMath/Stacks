module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalLiftingThroughCohomologyIsomorphisms
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryOfALeftFraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Local representation of a derived morphism between complexes on the site itself

Let `(C, O)` be a ringed site and let `E`, `F` be complexes of `O`-modules — on the site itself,
not on a slice — with `E|_V` strictly perfect for an object `V` of `C`. Every morphism
`α : E ⟶ F` of `D(O)` is, after restriction to the slice `C/W` along the arrows `f : W ⟶ V` of a
covering sieve of `V`, the image under the localization functor of an honest map of complexes

`β : E|_W ⟶ F|_W`.

This is Stacks 08FR (1) read on the slices of the base site rather than on the iterated slices
of a slice. It is the form the local argument of [Stacks, Tag 0FPV] needs: there the strictly
perfect source is the structure sheaf in degree zero, which lives on `C` and whose restrictions
to the slices are the structure sheaves of the slices, and the datum wanted over `W` is a map of
complexes out of `O|_W[0]` — equivalently, by
`StacksFrontier.CategoryTheory.Sites.Modules.UnitComplexMapsOverAnObject`, a degree-zero cocycle
section of `F` over `W`.

Nothing below is a clause of a tag; `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`
carries Stacks 08FR (1) and this is that statement transported, so no `@[stacks …]` attribute is
attached.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_restrictComplexMap`: the statement above.

## Implementation notes

**The crossing.** Stacks 08FQ,
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_homotopy_general`, lifts a map of
complexes on `C/V` up to homotopy along the arrows of a covering sieve, but it delivers the lift
on the *iterated* slice `(C/V)/(Over.mk f)`, through
`SheafOfModules.overFunctor (O|_V) (Over.mk f)`, whereas the statement below is phrased on
`C/W`, through `SheafOfModules.overFunctor O W`. The two are joined by composing the two
comparisons of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice`:

* `Stacks.SheafOfModules.sliceBackwardComplexIso`, which brings the iterated slice down to
  restriction along `f`, and
* `Stacks.SheafOfModules.overFunctorMapComplexIso`, which composes restriction to `C/V` with
  restriction along `f` into restriction to `C/W`.

Both are isomorphisms of *functors* on cochain complexes, so the transport of the lift is a
conjugation and its naturality is available; the whole crossing happens at the level of
complexes, and only then is the result read in the derived category. That is why no coherence
between `CategoryTheory.Functor.mapDerivedCategory` and composition of functors is needed —
`CategoryTheory.Functor.mapDerivedCategorySquareIso` is not used — and the transport of the
homotopy needs only additivity of `Stacks.SheafOfModules.sliceBackward`, not its exactness.

**From a homotopy to the derived square.** The passage from "`β` composed with the restriction of
the denominator is homotopic to the restriction of the numerator" to the commuting square with
`CategoryTheory.Functor.mapDerivedCategoryFactors` is
`CategoryTheory.Functor.mapDerivedCategory_map_eq_of_Q_eq`, the calculus of left fractions and
nothing else.

**The lower bound** on the degrees of `E|_V` is a hypothesis rather than being read off strict
perfectness. Stacks 08FQ needs some `a` with `(E|_V)^j = 0` for `j < a`; strict perfectness
supplies one, but at every use site below one is already at hand — for the structure sheaf in
degree zero it is `a = 0` — and asking for it keeps this file independent of the private
boundedness argument of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap`.

## References

* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 08FQ](https://stacks.math.columbia.edu/tag/08FQ)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction to a slice of the site preserves finite limits. -/
local instance sliceRepPreservesFiniteLimits (W : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction to a slice of the site preserves finite colimits. -/
local instance sliceRepPreservesFiniteColimits (W : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- Restriction along an arrow of the site preserves finite limits, by Stacks 04IX. -/
local instance sliceRepPreservesFiniteLimitsOverMap {V W : X.C} (g : W ⟶ V) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits, by Stacks 04IX. -/
local instance sliceRepPreservesFiniteColimitsOverMap {V W : X.C} (g : W ⟶ V) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceRepDer : ∀ W : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))]

/-- The category of sheaves of modules over the restriction of `O` to the slice over `W` has a
derived category. -/
local instance sliceRepHasDerivedOver (W : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
  hSliceRepDer W

/-- The comparison identifying the restriction to `C/V` followed by the transport through the
iterated slice over `Over.mk f` with the restriction to `C/W`, as an isomorphism of functors on
cochain complexes. It is the composite of the two comparisons of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice`. -/
def restrictIteratedSliceIso {V W : X.C} (f : W ⟶ V) :
    (SheafOfModules.overFunctor.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
            (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (Stacks.SheafOfModules.sliceBackward.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
            (ComplexShape.up ℤ) ≅
      (SheafOfModules.overFunctor.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Functor.isoWhiskerLeft
      ((SheafOfModules.overFunctor.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.sliceBackwardComplexIso.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f) ≪≫
    Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f

/-- **Stacks 08FR (1), on the slices of the base site.** Let `(C, O)` be a ringed site, let `E`
and `F` be complexes of `O`-modules, let `V` be an object of `C` and suppose `E|_V` is strictly
perfect and vanishes in degrees below `a`. Then any morphism `α : E ⟶ F` of `D(O)` is, after
restriction to the slice over `W` along the arrows `f : W ⟶ V` of a covering sieve of `V`, the
image under the localization functor of a morphism of complexes `E|_W ⟶ F|_W`. -/
theorem exists_coveringSieve_restrictComplexMap (V : X.C)
    {E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (X.restrictComplex E V)) (a : ℤ)
    (hEa : ∀ i : ℤ, i < a → IsZero ((X.restrictComplex E V).X i))
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ S : Sieve V, S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (f : W ⟶ V), S f →
        ∃ β : X.restrictComplex E W ⟶ X.restrictComplex F W,
          (SheafOfModules.overFunctor.{w}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.map α ≫
              (SheafOfModules.overFunctor.{w}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                W).mapDerivedCategoryFactors.hom.app F =
            (SheafOfModules.overFunctor.{w}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                W).mapDerivedCategoryFactors.hom.app E ≫
              DerivedCategory.Q.map β := by
  obtain ⟨Z, b, s, hs, hα⟩ := DerivedCategory.left_fac α
  have hsq : QuasiIso s := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  set GV := (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
    (ComplexShape.up ℤ) with hGV
  have : (SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hQI : QuasiIso (GV.map s) := by rw [hGV]; infer_instance
  have hhom : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap (GV.map s) j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap (GV.map s) j).1 (hQI.quasiIsoAt j)
  obtain ⟨S, hS, hlift⟩ := exists_coveringSieve_lift_homotopy_general X V (GV.map b) (GV.map s) a
    hE hEa (fun j _ => hhom j) (by have := hhom a; infer_instance)
  refine ⟨S, hS, fun W f hf => ?_⟩
  obtain ⟨γ, ⟨hγ⟩⟩ := hlift f hf
  set T := (Stacks.SheafOfModules.sliceBackward.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
    (ComplexShape.up ℤ) with hT
  set χ := restrictIteratedSliceIso X f with hχ
  set GW := (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapHomologicalComplex
    (ComplexShape.up ℤ) with hGW
  refine ⟨χ.inv.app E ≫ T.map γ ≫ χ.hom.app F, ?_⟩
  refine Functor.mapDerivedCategory_map_eq_of_Q_eq
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) α b s hs hα _ ?_
  have h1 : (χ.inv.app E ≫ T.map γ ≫ χ.hom.app F) ≫ GW.map s =
      χ.inv.app E ≫ T.map (γ ≫ ((SheafOfModules.overFunctor.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map (GV.map s)) ≫
          χ.hom.app Z := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun k => χ.inv.app E ≫ T.map γ ≫ k) (χ.hom.naturality s).symm
  have h2 : χ.inv.app E ≫ T.map (((SheafOfModules.overFunctor.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map (GV.map b)) ≫
          χ.hom.app Z = GW.map b := by
    rw [show T.map (((SheafOfModules.overFunctor.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map (GV.map b)) =
      ((SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
            (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (Stacks.SheafOfModules.sliceBackward.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map b from rfl, χ.hom.naturality b, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  have hhtp : DerivedCategory.Q.map (T.map (γ ≫ ((SheafOfModules.overFunctor.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) (Over.mk f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (GV.map s))) =
      DerivedCategory.Q.map (T.map (((SheafOfModules.overFunctor.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map (GV.map b))) :=
    DerivedCategory.Q_map_eq_of_homotopy _
      ((Stacks.SheafOfModules.sliceBackward.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomotopy hγ)
  rw [h1, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, hhtp,
    ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, h2]

/-- **The restriction of a chain-level representative along an arrow of the site.** If
`β : E|_V ⟶ F|_V` represents a morphism of `D(O)`, the morphism representing it over an object
`W` mapping to `V` is `β` restricted along the arrow, read through the comparison
`Stacks.SheafOfModules.overFunctorMapComplexIso` of the two descriptions of `E|_W`. -/
def restrictComplexMapAlong {V W : X.C} (g : W ⟶ V)
    {E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (β : X.restrictComplex E V ⟶ X.restrictComplex F V) :
    X.restrictComplex E W ⟶ X.restrictComplex F W :=
  (Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).inv.app E ≫
    ((SheafOfModules.overMap.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map β ≫
      (Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).hom.app F

/-- **A chain-level representative of a derived morphism restricts along the arrows of the
site.** If `β : E|_V ⟶ F|_V` induces `α : E ⟶ F` of `D(O)` over `V`, then its restriction
`AlgebraicGeometry.RingedSite.restrictComplexMapAlong` along any `g : W ⟶ V` induces `α` over
`W`.

This is what lets the covering sieve produced by
`AlgebraicGeometry.RingedSite.exists_coveringSieve_restrictComplexMap` be refined: a second
covering, of the members of the first, can be used without losing the representative, since the
representative travels down the arrows. Nothing about the sieve is involved — the statement holds
for every arrow of `C`.

The proof is the transport the two halves of
`StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryOfALeftFraction` were written for: the
square over `V` becomes, by
`CategoryTheory.Functor.Q_map_eq_of_mapDerivedCategory_map_eq`, a derived-category identity
between maps of complexes on `C/V`; restriction along `g` is exact, so it preserves that identity
(`CategoryTheory.Functor.Q_map_mapHomologicalComplex_eq_of_Q_map_eq`); and
`CategoryTheory.Functor.mapDerivedCategory_map_eq_of_Q_eq` rebuilds the square over `W`. -/
theorem mapDerivedCategory_map_eq_restrictComplexMapAlong {V W : X.C} (g : W ⟶ V)
    {E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (β : X.restrictComplex E V ⟶ X.restrictComplex F V)
    (hβ : (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map α ≫
        (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app F =
      (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app E ≫
        DerivedCategory.Q.map β) :
    (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.map α ≫
        (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.hom.app F =
      (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.hom.app E ≫
        DerivedCategory.Q.map (restrictComplexMapAlong X g β) := by
  obtain ⟨Z, b, s, hs, hα⟩ := DerivedCategory.left_fac α
  set GV := (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
    (ComplexShape.up ℤ) with hGV
  set GW := (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapHomologicalComplex
    (ComplexShape.up ℤ) with hGW
  set H := (SheafOfModules.overMap.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
    (ComplexShape.up ℤ) with hH
  set ψ := Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g with hψ
  have h1 : DerivedCategory.Q.map (β ≫ GV.map s) = DerivedCategory.Q.map (GV.map b) :=
    Functor.Q_map_eq_of_mapDerivedCategory_map_eq
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
      α b s hs hα β hβ
  have h2 : DerivedCategory.Q.map (H.map (β ≫ GV.map s)) =
      DerivedCategory.Q.map (H.map (GV.map b)) :=
    Functor.Q_map_mapHomologicalComplex_eq_of_Q_map_eq
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) h1
  refine Functor.mapDerivedCategory_map_eq_of_Q_eq
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) α b s hs hα _ ?_
  have hmid : H.map (β ≫ GV.map s) = H.map β ≫ (GV ⋙ H).map s := H.map_comp _ _
  have hstep : restrictComplexMapAlong X g β ≫ GW.map s =
      ψ.inv.app E ≫ H.map (β ≫ GV.map s) ≫ ψ.hom.app Z := by
    rw [restrictComplexMapAlong, hmid]
    simp only [Category.assoc]
    exact congrArg (fun k => ψ.inv.app E ≫ H.map β ≫ k) (ψ.hom.naturality s).symm
  have hfin : ψ.inv.app E ≫ H.map (GV.map b) ≫ ψ.hom.app Z = GW.map b := by
    rw [show H.map (GV.map b) = (GV ⋙ H).map b from rfl, ψ.hom.naturality b, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  rw [hstep, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, h2,
    ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hfin]

end AlgebraicGeometry.RingedSite

end
