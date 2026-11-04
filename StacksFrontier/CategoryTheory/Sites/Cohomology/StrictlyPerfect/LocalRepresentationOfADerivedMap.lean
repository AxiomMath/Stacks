module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalLiftingThroughCohomologyIsomorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Local representation of a derived morphism out of a strictly perfect complex

Let `(C, O)` be a ringed site, `U` an object of `C`, and `E`, `F` complexes of `O|_U`-modules
with `E` strictly perfect. Every morphism `α : E ⟶ F` of `D(O|_U)` is, after restriction along
the arrows of a covering sieve of `U`, the image of an honest map of complexes.

This is part (1) of Stacks 08FR. The argument is the one in the Stacks Project: the calculus of
left fractions in the derived category writes `α = Q(b) ∘ Q(s)⁻¹` with `s : F ⟶ W` a
quasi-isomorphism and `b : E ⟶ W` a map of complexes, and Stacks 08FQ lifts `b` through `s`, up
to homotopy, on a covering sieve.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`: Stacks 08FR (1).

## Implementation notes

Restriction of `O|_U`-modules along an arrow `f : V ⟶ U` of the site is written here as
`SheafOfModules.overMap O f`, landing in `O|_V`-modules on the site `C/V`, whereas Stacks 08FP,
08FQ and 08FR (2) are stated with `SheafOfModules.overFunctor (O|_U) (Over.mk f)`, landing in
modules on the iterated slice `(C/U)/(Over.mk f)`. The two agree, by
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`; the comparison and its degreewise form
`Stacks.SheafOfModules.sliceBackwardComplexIso` on complexes are in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IteratedSlice.lean`.

The sheafification hypotheses are taken in `∀`-form over the objects of the site, as in Stacks
08FT, rather than only at `U`: the conclusion asserts that `O|_V`-modules form an abelian
category for every arrow `V ⟶ U` of the covering sieve, and that is a property of the slice
site over `V`, not something the corresponding property at `U` implies.

The sections of the structure sheaf and of the modules lie in a free universe `w`, on the
diagonal with each other: the strict perfectness of `E` compares it with `SheafOfModules.free I`
for `I` in the universe of the ring, so the module universe cannot be chosen independently of
it. Nothing else here is universe-restricted — every sheafification hypothesis is assumed, so
the universe-raising producers of sheafification on a slice are never invoked. An earlier
version of this file was stated with `w = 0` and said that pin was forced; it was not.

The objects and the morphisms of the site lie in independent universes `u` and `v`. An earlier
version collapsed them to `AlgebraicGeometry.RingedSite.{u, u, w}`; that pin was not forced
either — the local lifting input
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_homotopy_general` is itself stated at
`AlgebraicGeometry.RingedSite.{u, v, w}` — and freeing it is what lets the statement be read on
a site whose objects and morphisms genuinely differ in universe, the small pro-étale site
`AlgebraicGeometry.RingedSite.{u + 1, u, w}` being the case this is wanted for.

To be exact about what that costs, since it is a strengthening of the hypotheses and so a
*weakening* of the statement: this theorem does **not** imply the variant which assumes
sheafification only at `U`. That variant appears not to be
provable — a covering sieve is closed under precomposition, so no choice of sieve avoids needing
the slice hypotheses at every `V`, and nothing supplies them. Mathlib has no
`HasSheafify J A → HasSheafify (J.over X) A`, and its own convention is the `∀`-form (see
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`,
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`,
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean`), as is this
repository's in the neighbouring files carrying Stacks 08FT, 08FU and 08G5.

The cost is nonetheless vacuous at every place the result is wanted, which is what settles the
question: all three consumers of this statement — the two halves of Stacks 08G6, that local
strict perfectness implies perfectness and that perfectness is independent of the
representative, and Stacks 08G9 — themselves assume
`∀ V, HasSheafify (J.over V) AddCommGrpCat` and `∀ V, (J.over V).WEqualsLocallyBijective
AddCommGrpCat`, so the theorem below applies at each of them verbatim. The statement thus carries
hypotheses narrower than those of its own consumers, which is where the discrepancy
originates.

The `@[stacks 08FR]` attribute is kept on that basis: faithfulness is judged against the Stacks
source, whose statement carries no typeclass hypotheses at all.

## References

* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section IndependentUniverses

variable (X : RingedSite.{u, v, w}) (U : X.C)
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

omit [HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] in
/-- A strictly perfect complex vanishes below some degree, on a site whose objects and
morphisms lie in independent universes: boundedness says that the set of degrees in which it
is nonzero is finite, so the negatives of those degrees are bounded above. -/
private theorem exists_lower_bound_independentUniverses
    {E : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) :
    ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (E.X i) := by
  obtain ⟨a, ha⟩ := hE.bounded.bddBelow
  exact ⟨a, fun i hi => Classical.byContradiction fun h => absurd hi (not_lt.mpr (ha h))⟩

/-- **Stacks 08FR (1), on a site whose objects and morphisms lie in independent universes.**
Let `(C, O)` be a ringed site and `U` an object of `C`. Let `E`, `F` be complexes of
`O|_U`-modules with `E` strictly perfect. Any morphism `α : E ⟶ F` of `D(O|_U)` is, after
restriction along the arrows of a covering sieve of `U`, the image under the localisation
functor of a morphism of complexes.

The universes of the objects and of the morphisms of the site are independent here, where
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap` has them equal. The small
pro-étale site of a scheme, `AlgebraicGeometry.RingedSite.{u + 1, u, w}`, is the case this
is wanted for. -/
theorem exists_coveringSieve_complexMap_independentUniverses
    {E F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        let H := SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        ∃ (hsheaf : HasSheafify (X.J.over V) AddCommGrpCat.{w})
          (hlocal : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β := by
  obtain ⟨a, ha⟩ := exists_lower_bound_independentUniverses X U hE
  obtain ⟨W, b, s, hs, hα⟩ := DerivedCategory.left_fac α
  have : QuasiIso s := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have hhom : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap s j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap s j).1 inferInstance
  have hαs : α ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map b := by
    rw [hα, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨S, hS, hlift⟩ := exists_coveringSieve_lift_homotopy_general X U b s a hE ha
    (fun j _ => hhom j) (by have := hhom a; infer_instance)
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  have hlift' := hlift f hf
  let : HasDerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    HasDerivedCategory.standard _
  let hlim : PreservesFiniteLimits
      (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits f
  let hcolim : PreservesFiniteColimits
      (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits f
  refine ⟨inferInstance, inferInstance, inferInstance, hlim, hcolim, ?_⟩
  set Gcc := (SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)
  set Tcc := (Stacks.SheafOfModules.sliceBackward (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    f).mapHomologicalComplex (ComplexShape.up ℤ)
  set Hcc := (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    f).mapHomologicalComplex (ComplexShape.up ℤ)
  obtain ⟨γ, ⟨hγ⟩⟩ := hlift'
  have θ : Gcc ⋙ Tcc ≅ Hcc :=
    Stacks.SheafOfModules.sliceBackwardComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  refine ⟨θ.inv.app E ≫ Tcc.map γ ≫ θ.hom.app F, ?_⟩
  have hnat : ∀ {K L : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ} (x : K ⟶ L),
      (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          f).mapDerivedCategory.map (DerivedCategory.Q.map x) ≫
          (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            f).mapDerivedCategoryFactors.hom.app L =
        (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            f).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (Hcc.map x) :=
    fun x => (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      f).mapDerivedCategoryFactors_hom_naturality x
  have hiso : IsIso (DerivedCategory.Q.map (Hcc.map s)) := by
    have h1 : IsIso ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        f).mapDerivedCategoryFactors.hom.app F ≫ DerivedCategory.Q.map (Hcc.map s)) := by
      rw [← hnat s]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        f).mapDerivedCategoryFactors.hom.app F)
      (DerivedCategory.Q.map (Hcc.map s))
  have hθs : θ.hom.app F ≫ Hcc.map s = Tcc.map (Gcc.map s) ≫ θ.hom.app W :=
    (θ.hom.naturality s).symm
  have hδ : (θ.inv.app E ≫ Tcc.map γ ≫ θ.hom.app F) ≫ Hcc.map s =
      θ.inv.app E ≫ Tcc.map (γ ≫ Gcc.map s) ≫ θ.hom.app W := by
    rw [Functor.map_comp]
    simp only [Category.assoc, hθs]
  have hb : Hcc.map b = θ.inv.app E ≫ Tcc.map (Gcc.map b) ≫ θ.hom.app W := by
    have h2 : Hcc.map b ≫ θ.inv.app W = θ.inv.app E ≫ Tcc.map (Gcc.map b) :=
      θ.inv.naturality b
    rw [← Category.assoc, ← h2, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hmid : DerivedCategory.Q.map (Tcc.map (γ ≫ Gcc.map s)) =
      DerivedCategory.Q.map (Tcc.map (Gcc.map b)) :=
    DerivedCategory.Q_map_eq_of_homotopy _ ((Stacks.SheafOfModules.sliceBackward
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomotopy hγ)
  rw [← cancel_mono (DerivedCategory.Q.map (Hcc.map s)), Category.assoc, ← hnat s,
    ← Category.assoc, ← Functor.map_comp, hαs, hnat b, Category.assoc,
    ← DerivedCategory.Q.map_comp, hδ, hb]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp DerivedCategory.Q (Tcc.map γ) (Tcc.map (Gcc.map s)),
    ← Functor.map_comp Tcc γ (Gcc.map s), hmid]

end IndependentUniverses

section EqualObjectAndMorphismUniverses

variable (X : RingedSite.{u, u, w}) (U : X.C)
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

omit [HasDerivedCategory.{d}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))] in
/-- A strictly perfect complex vanishes below some degree: boundedness says that the set of
degrees in which it is nonzero is finite, so the negatives of those degrees are bounded
above. -/
private theorem exists_lower_bound
    {E : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) :
    ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (E.X i) :=
  exists_lower_bound_independentUniverses X U hE

/-- **Stacks 08FR (1).** Let `(C, O)` be a ringed site and `U` an object of `C`. Let `E`, `F` be
complexes of `O|_U`-modules with `E` strictly perfect. Any morphism `α : E ⟶ F` of `D(O|_U)` is,
after restriction along the arrows of a covering sieve of `U`, the image under the localisation
functor of a morphism of complexes. -/
@[stacks 08FR "local_representation"]
theorem exists_coveringSieve_complexMap
    {E F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        let H := SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        ∃ (hsheaf : HasSheafify (X.J.over V) AddCommGrpCat.{w})
          (hlocal : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β :=
  exists_coveringSieve_complexMap_independentUniverses X U hE α

end EqualObjectAndMorphismUniverses

end AlgebraicGeometry.RingedSite

end
