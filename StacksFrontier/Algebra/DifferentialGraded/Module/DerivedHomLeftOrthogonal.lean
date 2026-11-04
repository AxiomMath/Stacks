module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryIsoDetection
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShiftFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # Ordinary Hom computes derived Hom out of a module left orthogonal to the acyclics

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, let `N` be
a differential graded `(A, B)`-bimodule, and let `RHom(N, -) : D(B, d) ⥤ D(A, d)` be a right
derived functor of Hom out of `N` (Tag 09LI). If the localization
`Q : K(B, d) ⥤ D(B, d)` is bijective on the morphisms out of `N` — that is, if

`Hom_{D(B,d)}(N, N') = Hom_{K(Mod_{(B,d)})}(N, N')` for every `N' ∈ K(B, d)`

— then `RHom(N, M) = Hom_{Mod^{dg}_{(B,d)}}(N, M)` functorially in `M`. That is Tag 0BYW, and the
source's example of a module satisfying the hypothesis is one with property (P), by Tag 09KY.

The conclusion is the invertibility of the canonical comparison natural transformation of
Tag 09LI, whose source is ordinary differential graded Hom out of `N` followed by localization and
whose target is derived Hom precomposed with localization. Invertibility of *that* map is what the
source's functorial equality says: the identification is the canonical one and it is natural in
the second argument.

The reason the hypothesis suffices is that ordinary Hom out of `N` then already inverts the
quasi-isomorphisms, so the derived functor is its factorisation through the localization and the
comparison is the factorising isomorphism
(`CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts`). The inversion is checked on
cohomology: the degree-`n` cohomology of `Hom^•_B(N, M)` is `Hom_{K(B,d)}(N, M[n])` by Tag 09LC
and Tag 0FQR, and the hypothesis turns the map induced by a quasi-isomorphism `s` into
postcomposition with a morphism that becomes invertible in `D(B, d)`.

## Main definitions

* `DifferentialGradedModule.homShiftCoyonedaIso`: the degree-`n` cohomology of ordinary internal
  Hom out of `N`, as a functor on `K(B, d)`, is `Hom_{K(B,d)}(N, (-)[n])`.
* `DifferentialGradedModule.DerivedHomData.comparisonNatIso`: the identification
  `Hom_{Mod^{dg}_{(B,d)}}(N, -) ≅ RHom(N, -) ∘ Q` of functors on `K(B, d)` that Tag 0BYW asserts.

## Main results

* `DifferentialGradedModule.isInvertedBy_homToDerivedCategory_of_bijective_q_map`: under the
  hypothesis of Tag 0BYW, ordinary Hom out of `N` followed by localization inverts the
  quasi-isomorphisms.
* `DifferentialGradedModule.DerivedHomData.isIso_comparison_of_bijective_q_map`: **Tag 0BYW**, the
  comparison is invertible under that hypothesis.
* `DifferentialGradedModule.DerivedHomData.isIso_comparison_of_propertyP`: **Tag 0BYW**, the
  property-(P) sufficient condition.
* `DifferentialGradedModule.DerivedHomData.comparisonNatIso`: **Tag 0BYW** as the source states
  it, the identification `RHom(N, -) = Hom^•_{(B,d)}(N, -)` of functors.

## Implementation notes

*Why the conclusion is stated for an arbitrary derived Hom datum.* `RHom(N, -)` is determined by
Tag 09LI only up to the canonical isomorphism
`DifferentialGradedModule.DerivedHomData.functorIso`, so a statement about the particular datum
`DifferentialGradedModule.derivedHomData` would be weaker than one about every datum. The
hypothesis of the lemma is about `N` and not about the construction, and the proof — the functor
being derived already inverts the quasi-isomorphisms, so *any* right derived functor of it is the
factorisation — does not see which datum it is applied to.

*Why the hypothesis is the bijectivity and not left orthogonality.* The source's hypothesis is the
equality of the morphism modules of `D(B, d)` and `K(B, d)` out of `N`, which is exactly the
bijectivity of `Q` on those modules, so that is what is assumed. It is equivalent to `N` being
orthogonal on the left to the acyclic modules; the implication that is used here is
`DifferentialGradedModule.bijective_q_map_of_leftOrthogonal`, and it is what makes the
property-(P) case a corollary, via Tag 09KM
(`DifferentialGradedModule.leftOrthogonal_acyclic_of_propertyP`).

*Why the quasi-isomorphisms are recognised by cohomology.* The inversion statement has to be
checked on an arbitrary morphism of `K(B, d)`, and the only description of ordinary internal Hom
available for that is its cohomology. `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`
proves that the quasi-isomorphisms are the morphisms with acyclic cone by passing through the
homological kernel of degree-zero cohomology, and
`DifferentialGradedModule.quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology` records the
intermediate criterion that the proof of that statement establishes, which is what is needed
here. The alternative route — that ordinary Hom out of `N` carries acyclic modules to acyclic
modules, and that this transfers to the quasi-isomorphisms because both are triangulated — needs
the internal Hom functor on homotopy categories to be exact, which is more than the shift
compatibility `DifferentialGradedModule.homHomotopyCategoryFunctorShiftIso` that is used instead.

*Relation to `DifferentialGradedModule.homShiftCohomologyIso`.*
`DifferentialGradedModule.homShiftCoyonedaIso` is the same identification read on the homotopy
category `K(A, d)` rather than on the derived category `D(A, d)`; the two are built from the same
two inputs, Tag 09LC and Tag 0FQR, and the one on `D(A, d)` is this one followed by the shift
compatibility of the localization and
`DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso'`. The version on `K(A, d)` is the
one that the recognition of quasi-isomorphisms above can be applied to, since that criterion lives
on `K(A, d)`.

*Universes.* The base ring, the differential graded algebras and their modules are taken at this
chapter's single-universe encoding, as everywhere in this directory. Nothing below depends on the
universes being equal.

## References

* [Stacks Project, Tag 0BYW](https://stacks.math.columbia.edu/tag/0BYW); the derived functor is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the computation of the morphism modules
  of `D(B, d)` is [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), the orthogonality of a
  module with property (P) is [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), the
  cohomology of the internal Hom is [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), its
  compatibility with the shift is [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR), and the
  quasi-isomorphisms are [Tag 09KW](https://stacks.math.columbia.edu/tag/09KW).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

variable (A B : DifferentialGradedAlgebra R) (N : DifferentialGradedModule B)
  (L : BimoduleStructure A B N)

/-! ### The cohomology of ordinary Hom out of `N`, on the homotopy category -/

/-- **`H^n(Hom^•_B(N, -)) ≅ Hom_{K(B,d)}(N, (-)[n])`.** Degree-`n` cohomology of ordinary internal
Hom out of the differential graded `(A, B)`-bimodule `N`, as a functor on `K(B, d)`, is the module
of morphisms `N ⟶ (-)[n]` of `K(B, d)`.

This is Tag 09LC, which identifies degree-zero cohomology of the internal Hom with the morphism
module of the homotopy category (`DifferentialGradedModule.homCohomologyZeroNatIso`), together
with Tag 0FQR, which moves the shift across the internal Hom
(`DifferentialGradedModule.homHomotopyCategoryFunctorShiftIso`). -/
def homShiftCoyonedaIso (n : ℤ) :
    homHomotopyCategoryFunctor A B N L ⋙
        (CategoryTheory.shiftFunctor (HomotopyCategory A) n ⋙
          degreeZeroCohomologyOnHomotopy' A) ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B) n ⋙
        (linearCoyoneda R (HomotopyCategory B)).obj
          (Opposite.op ((toHomotopyCategory B).obj N)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homHomotopyCategoryFunctorShiftIso A B N L n)
      (degreeZeroCohomologyOnHomotopy' A) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor (HomotopyCategory B) n)
      (homCohomologyZeroNatIso A B N L)

/-! ### Ordinary Hom out of `N` inverts the quasi-isomorphisms -/

/-- If the localization is bijective on the morphisms out of `N` in the homotopy category, then
postcomposition with a morphism `t` that becomes invertible in `D(B, d)` is bijective on those
morphism modules.

The square expressing that the localization takes postcomposition with `t` to postcomposition with
the image of `t` commutes, three of its four maps are bijective, so the fourth is. -/
theorem bijective_comp_right_of_bijective_q_map
    (hN : ∀ P : HomotopyCategory B, Function.Bijective
      ((quasiIsomorphisms' B).Q.map : ((toHomotopyCategory B).obj N ⟶ P) → _))
    {X Y : HomotopyCategory B} (t : X ⟶ Y)
    (ht : IsIso ((quasiIsomorphisms' B).Q.map t)) :
    Function.Bijective (fun f : (toHomotopyCategory B).obj N ⟶ X => f ≫ t) := by
  set Q := (quasiIsomorphisms' B).Q
  set M := (toHomotopyCategory B).obj N
  have himage : Function.Bijective (fun g : Q.obj M ⟶ Q.obj X => g ≫ Q.map t) :=
    (asIso (Q.map t)).homToEquiv.bijective
  refine (Function.Bijective.of_comp_iff' (hN Y) _).mp ?_
  convert himage.comp (hN X) using 1
  exact funext fun f => Q.map_comp f t

/-- If the localization is bijective on the morphisms out of `N` in the homotopy category, then
ordinary internal Hom out of `N`, followed by localization of the target, inverts the
quasi-isomorphisms of differential graded `B`-modules; so it factors through `D(B, d)`.

A morphism of `K(A, d)` is a quasi-isomorphism as soon as degree-zero cohomology inverts all its
shifts
(`DifferentialGradedModule.quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology`), and on the
image of internal Hom those cohomology modules are the morphism modules `Hom_{K(B,d)}(N, (-)[n])`
by `DifferentialGradedModule.homShiftCoyonedaIso`. There the induced map is postcomposition with a
shift of the given quasi-isomorphism, which is bijective by
`DifferentialGradedModule.bijective_comp_right_of_bijective_q_map`. -/
theorem isInvertedBy_homToDerivedCategory_of_bijective_q_map
    (hN : ∀ P : HomotopyCategory B, Function.Bijective
      ((quasiIsomorphisms' B).Q.map : ((toHomotopyCategory B).obj N ⟶ P) → _)) :
    (quasiIsomorphisms' B).IsInvertedBy (homToDerivedCategory A B N L) := by
  intro X Y s hs
  have hQs : IsIso ((quasiIsomorphisms' B).Q.map s) :=
    Localization.inverts (quasiIsomorphisms' B).Q (quasiIsomorphisms' B) s hs
  have hhom : quasiIsomorphisms' A ((homHomotopyCategoryFunctor A B N L).map s) := by
    rw [quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology]
    intro n
    have hshift : IsIso ((quasiIsomorphisms' B).Q.map (s⟦n⟧')) :=
      (NatIso.isIso_map_iff ((quasiIsomorphisms' B).Q.commShiftIso n) s).2
        (by dsimp; infer_instance)
    have hcoyoneda : IsIso (((linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj N))).map (s⟦n⟧')) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_comp_right_of_bijective_q_map B N hN (s⟦n⟧') hshift)
    exact (NatIso.isIso_map_iff (homShiftCoyonedaIso A B N L n) s).2 hcoyoneda
  change IsIso ((quasiIsomorphisms' A).Q.map ((homHomotopyCategoryFunctor A B N L).map s))
  exact Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _ hhom

/-! ### Tag 0BYW -/

namespace DerivedHomData

/-- If `Hom_{D(B,d)}(N, N') = Hom_{K(Mod_{(B,d)})}(N, N')` for all `N' ∈ K(B, d)`, then
`RHom(N, M) = Hom_{Mod^{dg}_{(B,d)}}(N, M)` functorially in `M` in `D(B, d)`.

The equality of morphism modules is the hypothesis `hN`, that the localization
`Q : K(B, d) ⥤ D(B, d)` is bijective on the morphisms out of `N`. The functorial equality of the
conclusion is the invertibility of the comparison natural transformation of Tag 09LI, from
ordinary differential graded Hom out of `N` read in `D(A, d)` to derived Hom precomposed with the
localization; `DifferentialGradedModule.DerivedHomData.comparisonNatIso` is the resulting
isomorphism of functors.

Under the hypothesis the functor being derived already inverts the quasi-isomorphisms
(`DifferentialGradedModule.isInvertedBy_homToDerivedCategory_of_bijective_q_map`), and the
comparison of any right derived functor of a functor that inverts them is invertible. -/
@[stacks 0BYW "the comparison under the Hom hypothesis"]
theorem isIso_comparison_of_bijective_q_map (D : DerivedHomData A B N L)
    (hN : ∀ P : HomotopyCategory B, Function.Bijective
      ((quasiIsomorphisms' B).Q.map : ((toHomotopyCategory B).obj N ⟶ P) → _)) :
    IsIso D.comparison :=
  let := D.isRightDerived
  Functor.isIso_of_isRightDerivedFunctor_of_inverts D.functor D.comparison
    (isInvertedBy_homToDerivedCategory_of_bijective_q_map A B N L hN)

/-- A differential graded `(A, B)`-bimodule whose underlying `B`-module has property (P) computes
derived Hom by ordinary differential graded Hom, canonically and naturally in the second argument.

A module with property (P) is orthogonal on the left to the acyclic modules, which is Tag 09KM,
and the localization is bijective on the morphisms out of such a module, which is the mechanism of
Tag 09KY; so the hypothesis of the previous statement holds. -/
@[stacks 0BYW "the property-(P) sufficient condition"]
theorem isIso_comparison_of_propertyP (D : DerivedHomData A B N L)
    (hN : Nonempty (PropertyPFiltration N)) :
    IsIso D.comparison :=
  isIso_comparison_of_bijective_q_map A B N L D fun _ =>
    bijective_q_map_of_leftOrthogonal (leftOrthogonal_acyclic_of_propertyP hN.some) _

/-- **`RHom(N, -) = Hom_{Mod^{dg}_{(B,d)}}(N, -)` as functors.** Ordinary differential graded Hom
out of `N`, read in `D(A, d)`, is derived Hom out of `N` precomposed with the localization, by the
comparison map of Tag 09LI and naturally in the second argument. -/
@[stacks 0BYW "as an identification of functors"]
def comparisonNatIso (D : DerivedHomData A B N L)
    (hN : ∀ P : HomotopyCategory B, Function.Bijective
      ((quasiIsomorphisms' B).Q.map : ((toHomotopyCategory B).obj N ⟶ P) → _)) :
    homToDerivedCategory A B N L ≅ (quasiIsomorphisms' B).Q ⋙ D.functor :=
  letI := isIso_comparison_of_bijective_q_map A B N L D hN
  asIso D.comparison

end DerivedHomData

end DifferentialGradedModule

end
