module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral

/-!
# A derived approximation over a slice becomes a chain-level one, at independent universes

Let `(C, O)` be a ringed site, `V` an object of `C` and `K` a complex of `O`-modules. Suppose a
strictly perfect complex `P` of `O|_V`-modules comes with a morphism
`β : Q(P) ⟶ Q(K|_V)` of `D(O|_V)` which is an isomorphism on cohomology in every degree `> m`
and an epimorphism in degree `m`. Then `V` has a covering sieve over each arrow of which `K`
admits a *chain-level* strictly perfect approximation in the same two degrees, and consequently
an object of `D(O)` approximated over every object of `C` is `m`-pseudo-coherent.

Both statements already exist on the diagonal site `RingedSite.{u, u, 0}`, where the sections of
the modules lie in `Type`; this file states them with the underlying category, its morphisms and
the sections of the modules at independent universes, which is where the perfectness cluster of
[Stacks, Tag 0FPV] lives.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived_general`: the
  chain-level approximation on a covering, at independent universes.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_derived_approximation_general`:
  `m`-pseudo-coherence from a derived approximation over every object, at independent universes.

## Implementation notes

The argument is the one on the diagonal and is reproduced verbatim up to the universe of the
sections; the single step which does not transport is the preservation of strict perfection
under restriction along an arrow of the site, whose diagonal form
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong` is stated only at sections in
`Type`. `AlgebraicGeometry.RingedSite.isStrictlyPerfect_overMap` is its form at a free universe
of the sections and is used in its place.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FQ](https://stacks.math.columbia.edu/tag/08FQ)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section SliceGeneral

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **A derived strictly perfect approximation over a slice becomes a chain-level one on a
covering**, with the site, its morphisms and the sections of the modules at independent
universes. Let `P` be a strictly perfect complex of `O|_V`-modules and
`β : Q(P) ⟶ Q(K|_V)` a morphism of `D(O|_V)` which is invertible on cohomology in every degree
`> m` and epic in degree `m`. Then there is a covering sieve of `V` over each arrow `W ⟶ V` of
which a strictly perfect complex of `O|_W`-modules maps to `K|_W` with the same two
properties. -/
theorem exists_coveringSieve_approximation_of_derived_general (V : X.C)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V))
    (hiso : ∀ j : ℤ, m < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map β))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    ∃ T : Sieve V, T ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P' : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
          ∃ α' : P' ⟶ X.restrictComplex K W,
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
            Epi (HomologicalComplex.homologyMap α' m) := by
  obtain ⟨G, γ, s, hs, hfac⟩ := DerivedCategory.left_fac β
  have hγiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap γ j) := fun j hj =>
    CategoryTheory.isIso_homologyMap_of_left_fac β γ s hs hfac j (hiso j hj)
  have hγepi : Epi (HomologicalComplex.homologyMap γ m) :=
    CategoryTheory.epi_homologyMap_of_left_fac β γ s hs hfac m hepi
  have hsj : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap s j) := fun j =>
    CategoryTheory.isIso_homologyMap_of_isIso_Q_map s hs j
  have : QuasiIso s := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  obtain ⟨T, hT, hlift⟩ := exists_coveringSieve_lift_of_quasiIso X V γ s hP
  refine ⟨T, hT, fun W g hg => ?_⟩
  obtain ⟨b, ⟨hb⟩⟩ := hlift g hg
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  have hcmp : (restrictCochainAlong X g).obj (X.restrictComplex K V) ≅ X.restrictComplex K W :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
  have hcmpIso : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap hcmp.hom j) := fun j => by
    have : IsIso hcmp.hom := hcmp.isIso_hom
    show IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map hcmp.hom)
    infer_instance
  have hsg : ∀ j : ℤ,
      IsIso (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j) := fun j =>
    AlgebraicGeometry.RingedSpace.isIso_homologyMap_map
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) s j (hsj j)
  have hcomm : ∀ j : ℤ, HomologicalComplex.homologyMap b j ≫
      HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j =
        HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) j := fun j => by
    rw [← HomologicalComplex.homologyMap_comp]
    exact Homotopy.homologyMap_eq hb j
  refine ⟨(restrictCochainAlong X g).obj P,
    isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    b ≫ hcmp.hom, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    have h₃ : IsIso (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) j) :=
      AlgebraicGeometry.RingedSpace.isIso_homologyMap_map
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) γ j (hγiso j hj)
    rw [← hcomm j] at h₃
    have := hsg j
    have := hcmpIso j
    have := IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap b j)
      (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j)
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have h₃ : Epi (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) m) :=
      AlgebraicGeometry.RingedSpace.epi_homologyMap_map
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) γ m hγepi
    rw [← hcomm m] at h₃
    have := hsg m
    have := hcmpIso m
    have : Epi (HomologicalComplex.homologyMap b m) :=
      (epi_comp_iff_of_isIso (HomologicalComplex.homologyMap b m)
        (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) m)).mp h₃
    infer_instance

/-- **A derived strictly perfect approximation over every object makes an object of `D(O)`
`m`-pseudo-coherent**, with the site, its morphisms and the sections of the modules at
independent universes. If `E` is the image of a complex `K` and every object `V` of `C` carries
a strictly perfect complex of `O|_V`-modules approximating `E|_V` in degrees `> m` in the
derived category, then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_derived_approximation_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ V : X.C, ∃ P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V),
        (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    X.IsPseudoCoherentFrom E m := by
  refine ⟨K, fun V => ?_, ⟨e⟩⟩
  obtain ⟨P, hP, β, hiso, hepi⟩ := h V
  obtain ⟨T, hT, hdata⟩ :=
    X.exists_coveringSieve_approximation_of_derived_general V K m P hP β hiso hepi
  exact ⟨T.arrows, by rw [Sieve.generate_sieve]; exact hT, hdata⟩

end SliceGeneral

end AlgebraicGeometry.RingedSite

end
