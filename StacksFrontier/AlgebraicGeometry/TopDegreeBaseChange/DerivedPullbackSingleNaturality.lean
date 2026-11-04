module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality

/-!
# The comparison `H^d(Lf^*(M[-d])) ⟶ f^* M` is natural in `M`

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap` is the canonical
map `H^d(Lf^*(M[-d])) ⟶ f^* M` of a morphism of ringed spaces `f`, and
`...isIso_homologyDerivedPullbackSingleMap` shows it is invertible.  Both are stated for one
module `M` at a time, which is all the step of [Stacks, Tag 0EX3] they were written for needs.
This file adds what a *naturality* argument needs: the comparison is a morphism of functors of
`M`.

The distinction is not idle.  An isomorphism `f^* ℱ ≅ ℱ` for each coherent `ℱ`, one module at a
time, cannot tell the absolute Frobenius of a scheme over a finite field from the identity — over
`Spec 𝔽_4` the Frobenius twist of a module is always abstractly isomorphic to the module.  The
naturality of such a family does tell them apart, and the family that arises from a Fourier-Mukai
functor isomorphic to the identity is manufactured by composing `H^d` of this comparison with
isomorphisms of functors; so the comparison's naturality is exactly what has to be supplied for
the family to be natural.  That is the use made of this file in the proof of
[Stacks, Tag 0G0E].

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.app_comp_naturality` — the formal core, in a
  setting with no geometry in it: a four-fold composite of components of natural transformations
  whose sources and targets compose in the displayed pattern is natural.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap_naturality` —
  the comparison `H^d(Lf^*(M[-d])) ⟶ f^* M` is natural in `M`.

## Implementation notes

*Why the formal core is stated separately.*  `derivedToOrdinaryPullbackSingle` is a composite of
four factors, each the component at `M` of a natural transformation:

`Lf^*(α_M)`, `(Lf^*)^{comp}_{M[-d]}`, `Qh(μ_M)`, `β^{-1}_{f^* M}`,

for `α` the identification of `DerivedCategory.singleFunctor` with
`HomotopyCategory.singleFunctor ⋙ Qh`, `(Lf^*)^{comp}` the derived-pullback comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`, `μ` the
commutation `Functor.mapHomotopyCategorySingleFunctor` of degreewise pullback with the
homotopy-category single functor, and `β` the identification `α` at `X`.  So the naturality is a
formal consequence of theirs, and `app_comp_naturality` is that consequence with the four
transformations arbitrary.

Stating it that way is not only tidier: at the concrete spelling
`SheafOfModules (structureSheafRing _)` the rewrites that chain the four naturality squares run
into the same deterministic `isDefEq` timeout that
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap_eq` records for
distributing `H^d` over the same composite — a cost, not a wall, and one that disappears when the
categories are abstract.  Instantiating the abstract lemma is then a single term.  The
naturality itself is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_naturality`, in
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality`.

*The degree-`d` statement.*  Passing to `H^d` needs only that
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso` is the component of a natural
isomorphism, which is `...homologySingleIso_hom`: it is
`DerivedCategory.singleFunctorCompHomologyFunctorIso` at `M`.  Nothing else about `H^d` is used,
and in particular the composite stays under a single `H^d` throughout.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open _root_.DerivedCategory

universe u

/-! ### The formal core -/

section Generic

variable {A A' B C C' D : Type*} [Category A] [Category A'] [Category B] [Category C]
  [Category C'] [Category D]

/-- **A four-fold composite of components of natural transformations is natural.**  Given
functors and natural transformations

`α : S ⟶ H ⋙ Q`,  `c : Q ⋙ P ⟶ K ⋙ Q'`,  `m : H ⋙ K ⟶ L ⋙ H'`,  `β : H' ⋙ Q' ⟶ T`,

the morphisms `P(α_M) ≫ c_{H M} ≫ Q'(m_M) ≫ β_{L M} : (S ⋙ P) M ⟶ (L ⋙ T) M` form a natural
transformation `S ⋙ P ⟶ L ⋙ T`. -/
theorem app_comp_naturality (S : A ⥤ B) (H : A ⥤ C) (Q : C ⥤ B) (P : B ⥤ D)
    (K : C ⥤ C') (Q' : C' ⥤ D) (L : A ⥤ A') (H' : A' ⥤ C') (T : A' ⥤ D)
    (α : S ⟶ H ⋙ Q) (c : Q ⋙ P ⟶ K ⋙ Q') (m : H ⋙ K ⟶ L ⋙ H') (β : H' ⋙ Q' ⟶ T)
    {M N : A} (φ : M ⟶ N) :
    P.map (S.map φ) ≫
        (P.map (α.app N) ≫ c.app (H.obj N) ≫ Q'.map (m.app N) ≫ β.app (L.obj N)) =
      (P.map (α.app M) ≫ c.app (H.obj M) ≫ Q'.map (m.app M) ≫ β.app (L.obj M)) ≫
        T.map (L.map φ) := by
  rw [← Functor.map_comp_assoc, α.naturality, Functor.comp_map, Functor.map_comp_assoc,
    ← Functor.comp_map Q P, c.naturality_assoc, Functor.comp_map K Q',
    ← Functor.comp_map H K, ← Functor.map_comp_assoc, m.naturality, Functor.map_comp_assoc,
    Functor.comp_map L H', ← Functor.comp_map H' Q', β.naturality]
  simp only [Category.assoc]

end Generic

/-! ### The two naturality statements -/

section Geometry

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.SheafOfModules.coefficientLocallyBijective
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **The comparison `H^d(Lf^*(M[-d])) ⟶ f^* M` is natural in `M`.** This is
`derivedToOrdinaryPullbackSingle_naturality` (`TopDegreeTensorNaturality`) after `H^d`, together
with the naturality of `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso`, which is a
component of `DerivedCategory.singleFunctorCompHomologyFunctorIso`. -/
theorem homologyDerivedPullbackSingleMap_naturality
    {M N : SheafOfModules.{u} (structureSheafRing Y)} (φ : M ⟶ N) (d : ℤ) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((derivedPullback f).map
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map φ)) ≫
      homologyDerivedPullbackSingleMap f N d =
    homologyDerivedPullbackSingleMap f M d ≫ (modulePullback f).map φ := by
  rw [homologyDerivedPullbackSingleMap, homologyDerivedPullbackSingleMap,
    ← Functor.map_comp_assoc, derivedToOrdinaryPullbackSingle_naturality,
    Functor.map_comp_assoc, homologySingleIso_hom, homologySingleIso_hom,
    ← Functor.comp_map (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d)
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d),
    NatTrans.naturality]
  rfl

/-- **`H^d(Lf^*(·[-d])) ≅ f^*` as functors.**  The isomorphism
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso`, assembled over
all modules into an isomorphism of functors by
`homologyDerivedPullbackSingleMap_naturality`. -/
def homologyDerivedPullbackSingleNatIso (d : ℤ) :
    singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d ⋙ derivedPullback f ⋙
        homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d ≅
      modulePullback f :=
  NatIso.ofComponents (fun M => homologyDerivedPullbackSingleIso f M d)
    (fun φ => homologyDerivedPullbackSingleMap_naturality f φ d)

end Geometry

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
