module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A derived strictly perfect approximation over a slice becomes a chain-level one on a covering

Let `(C, O)` be a ringed site, `V` an object of `C` and `K` a complex of `O`-modules. Suppose a
strictly perfect complex `P` of `O|_V`-modules comes with a morphism
`β : Q(P) ⟶ Q(K|_V)` of `D(O|_V)` which is an isomorphism on cohomology in every degree `> m`
and an epimorphism in degree `m`. Then `V` has a covering sieve over each arrow of which `K`
admits a *chain-level* strictly perfect approximation in the same two degrees — which is
exactly the data the definition of `m`-pseudo-coherence of `K` asks for.

This is the step which turns the output of a derived construction into the input of Stacks
08FT, and it is what makes a globally defined derived approximation on a localized ringed site
imply pseudo-coherence there.

## The argument

Write `β` as a left fraction `Q(γ) ≫ Q(s)⁻¹` with `γ : P ⟶ G` and `s : K|_V ⟶ G` morphisms of
complexes of `O|_V`-modules (`DerivedCategory.left_fac`). The numerator `γ` inherits the two
cohomological properties of `β` (`CategoryTheory.isIso_homologyMap_of_left_fac` and
`CategoryTheory.epi_homologyMap_of_left_fac`) and `s` is a quasi-isomorphism, so
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_of_quasiIso` lifts `γ` through `s` up to
homotopy after restricting along the arrows of a covering sieve of `V`. The lift is the required
approximation: restriction along an arrow of the site is exact, so it preserves both
cohomological properties, and the homotopy identifies the composite of the lift with `s` with
the restriction of `γ`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived`: the statement
  above.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_derived_approximation`: consequently, a
  ringed site over whose every object a strictly perfect complex approximates `E` in the derived
  category has `E` `m`-pseudo-coherent.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FQ](https://stacks.math.columbia.edu/tag/08FQ)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.RingedSite

section Slice

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **A derived strictly perfect approximation over a slice becomes a chain-level one on a
covering.** Let `P` be a strictly perfect complex of `O|_V`-modules and
`β : Q(P) ⟶ Q(K|_V)` a morphism of `D(O|_V)` which is invertible on cohomology in every degree
`> m` and epic in degree `m`. Then there is a covering sieve of `V` over each arrow `W ⟶ V` of
which a strictly perfect complex of `O|_W`-modules maps to `K|_W` with the same two properties.

Writing `β` as a left fraction `Q(γ) ≫ Q(s)⁻¹` makes `γ` a chain-level approximation and `s` a
quasi-isomorphism, and
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_of_quasiIso` lifts `γ` through `s` on a
covering sieve. -/
@[sga "6 I 2.2" "b)"]
theorem exists_coveringSieve_approximation_of_derived (V : X.C)
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (P : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V))
    (hiso : ∀ j : ℤ, m < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map β))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    ∃ T : Sieve V, T ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P' : CochainComplex
            (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
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
    change IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map hcmp.hom)
    infer_instance
  have hsg : ∀ j : ℤ,
      IsIso (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j) := fun j =>
    AlgebraicGeometry.RingedSpace.isIso_homologyMap_map
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) s j (hsj j)
  have key : ∀ j : ℤ, HomologicalComplex.homologyMap b j ≫
      HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j =
        HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) j := fun j => by
    rw [← HomologicalComplex.homologyMap_comp]
    exact Homotopy.homologyMap_eq hb j
  refine ⟨(restrictCochainAlong X g).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP, b ≫ hcmp.hom, fun j hj => ?_, ?_⟩
  · have h₃ : IsIso (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) j) :=
      AlgebraicGeometry.RingedSpace.isIso_homologyMap_map
        (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) γ j (hγiso j hj)
    rw [← key] at h₃
    have := hsg j
    have := hcmpIso j
    have := IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap b j)
      (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map s) j)
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  · have h₃ : Epi (HomologicalComplex.homologyMap ((restrictCochainAlong X g).map γ) m) :=
      AlgebraicGeometry.RingedSpace.epi_homologyMap_map
        (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) γ m hγepi
    rw [← key] at h₃
    have := hsg m
    have := hcmpIso m
    rw [HomologicalComplex.homologyMap_comp]
    exact epi_comp' ((epi_comp_iff_of_isIso _ _).mp h₃) (IsIso.epi_of_iso _)

/-- **A derived strictly perfect approximation over every object makes an object of `D(O)`
`m`-pseudo-coherent.** If `E` is the image of a complex `K` and every object `V` of `C` carries
a strictly perfect complex of `O|_V`-modules approximating `E|_V` in degrees `> m` in the
derived category, then `E` is `m`-pseudo-coherent.

The approximation over `V` is transported to the complex representative `K|_V` and then made
chain-level on a covering of `V` by
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived`; no further
covering is composed, so the covering of `V` the definition asks for is the one produced
there. -/
theorem isPseudoCoherentFrom_of_derived_approximation
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ V : X.C, ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V),
        (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    X.IsPseudoCoherentFrom E m := by
  refine ⟨K, fun V => ?_, ⟨e⟩⟩
  obtain ⟨P, hP, β, hiso, hepi⟩ := h V
  obtain ⟨T, hT, hdata⟩ :=
    X.exists_coveringSieve_approximation_of_derived V K m P hP β hiso hepi
  exact ⟨T.arrows, by rw [Sieve.generate_sieve]; exact hT, hdata⟩

end Slice

end AlgebraicGeometry.RingedSite

end
