module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraRestrictOpenSubspace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOpenSubspace

/-!
# The map induced on exterior powers commutes with restriction to an open subspace

Let `X` be a ringed space, `U ⊆ X` open, `f : M ⟶ N` a morphism of sheaves of `𝒪_X`-modules, `A`
an exterior algebra of `M` and `B` one of `N`. `SheafOfModules.exteriorRestrictOpenSubspaceIso`
identifies `(⋀ⁿM)|_U` with `⋀ⁿ(M|_U)` and `(⋀ⁿN)|_U` with `⋀ⁿ(N|_U)`. This file proves that
those identifications carry the restriction of `⋀ⁿf` to `⋀ⁿ(f|_U)`:

`(⋀ⁿf)|_U ≫ e_N = e_M ≫ ⋀ⁿ(f|_U)`.

**Where the argument lives.** `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap` is the
degree-`n` component of a *unital homomorphism* of sheaves of graded algebras, determined by what
it does to the degree-one generator, and `SheafOfModules.exteriorRestrictOpenSubspaceIso` is the
degree-`n` component of another one. So both sides of the identity above are degree-`n`
components of unital homomorphisms out of the restricted algebra `A|_U`, and `A|_U` is an
exterior algebra of `M|_U` (`SheafOfModules.isExteriorAlgebra_openSubspaceAlg`): the two agree
because they agree on the generator. No multiplicativity has to be checked and no local section
is computed, the whole content being the uniqueness clause of the universal property.

**Why the restriction is spelled as a composite of two pushforwards.** The restriction of the
exterior algebra, `SheafOfModules.openSubspaceAlg`, is built along the factorization of
restriction to an open subspace into the slice restriction `SheafOfModules.overFunctor` followed
by the transport `Stacks.SheafOfModules.openSubspaceEquiv` to the open subspace. Written that
way — `SheafOfModules.openSubspaceRestriction` below — the crossing is *definitional* on objects
and on the generator: `(openSubspaceAlg A U).piece n` is `(openSubspaceRestriction U).obj
(A.piece n)` and `SheafOfModules.openSubspaceGen` is `(openSubspaceRestriction U).map` of the
generator of `A`, both by `rfl`
(`SheafOfModules.openSubspaceAlg_piece_openSubspaceRestriction` and
`SheafOfModules.openSubspaceGen_eq_openSubspaceRestriction_map`). The single comparison
`exteriorRestrictOpenSubspaceIso`, which `SheafOfModules.exteriorRestrictOpenSubspaceIso_mul`
says is multiplicative, is then the whole exterior-power crossing, with no further bridge to
compose with; and `Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor` carries a
consequence over to `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, the functor a
splitting of a restricted short complex of `𝒪_X`-modules is stated against.

The same crossing read at `Stacks.Cohomology.HigherDirectImage.moduleRestriction` is the same
statement — that functor is this composite, the pushforward along the open-image functor of opens
being the pushforward along the two halves in turn — but the identification is not one the
elaborator can afford inside a statement that also carries the data of four exterior algebras:
it exhausts the default heartbeat budget at `isDefEq`. Hence the composite spelling
here.

## Main definitions

* `SheafOfModules.openSubspaceRestriction`: **restriction of sheaves of modules to an open
  subspace**, as the slice restriction followed by the transport to the open subspace — the
  factorization `SheafOfModules.openSubspaceAlg` is built along.
* `SheafOfModules.GradedAlgebra.UnitalHom.openSubspace`: **a unital homomorphism of sheaves of
  graded algebras, restricted to an open subspace.** Its degree-`n` component is the restriction
  of the degree-`n` component of the original.

## Main results

* `SheafOfModules.openSubspaceAlg_piece_openSubspaceRestriction` and
  `SheafOfModules.openSubspaceGen_eq_openSubspaceRestriction_map`: the restricted exterior
  algebra has the restrictions of the pieces for its pieces and the restriction of the generator
  for its generator, on the nose.
* `SheafOfModules.openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso`:
  **the map induced on degree-`n` exterior powers commutes with restriction to an open
  subspace**, through `SheafOfModules.exteriorRestrictOpenSubspaceIso` at the source and at the
  target.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.PushforwardSheafification

universe u

namespace SheafOfModules

open _root_.SheafOfModules.GradedAlgebra

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- **Restriction of sheaves of `𝒪_X`-modules to the open subspace `U`**, in the factorization
`SheafOfModules.openSubspaceAlg` is built along: the restriction to the slice site over `U`,
followed by the transport along `Stacks.SheafOfModules.openSubspaceSiteFunctor` to the open
subspace. It is `Stacks.Cohomology.HigherDirectImage.moduleRestriction` and
`AlgebraicGeometry.SheafOfModules.siteRestrict`, and is isomorphic to
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` by
`Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor`. -/
abbrev openSubspaceRestriction :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
        (Stacks.SheafOfModules.openSubspaceSiteFunctor U) ((structureSheafRing X).over U)) :=
  SheafOfModules.overFunctor (structureSheafRing X) U ⋙
    sheafPushforwardFunctor.{u} (Opens.grothendieckTopology ↥U)
      (Stacks.SheafOfModules.openSubspaceSiteFunctor U) ((structureSheafRing X).over U)

namespace GradedAlgebra

variable {A B : GradedAlgebra.{u, u} (structureSheafRing X)}

/-- **A unital homomorphism of sheaves of graded algebras, restricted to an open subspace.**
It is `SheafOfModules.GradedAlgebra.UnitalHom.sitePushforward` along the slice site followed by
`Stacks.SheafOfModules.openSubspaceUnitalHom`, which is the factorization
`SheafOfModules.openSubspaceAlg` itself is built along, so no transport appears. -/
def UnitalHom.openSubspace (g : UnitalHom A B) :
    UnitalHom (_root_.SheafOfModules.openSubspaceAlg A U)
      (_root_.SheafOfModules.openSubspaceAlg B U) :=
  Stacks.SheafOfModules.openSubspaceUnitalHom U
    (g.sitePushforward (𝟙 ((structureSheafRing X).over U)))

/-- The degree-`n` component of the restricted homomorphism is the restriction of the degree-`n`
component, the pieces of the restricted algebra being the restrictions of the pieces. -/
@[simp]
theorem UnitalHom.openSubspace_app (g : UnitalHom A B) (n : ℤ) :
    (g.openSubspace U).app n =
      (_root_.SheafOfModules.openSubspaceRestriction U).map (g.app n) :=
  rfl

end GradedAlgebra

section Restriction

variable (M : SheafOfModules.{u} (structureSheafRing X))
  (A : GradedAlgebra.{u, u} (structureSheafRing X)) (gen : M ⟶ A.piece 1)

/-- **The pieces of the restricted exterior algebra are the restrictions of the pieces.** -/
theorem openSubspaceAlg_piece_openSubspaceRestriction (n : ℤ) :
    (openSubspaceAlg A U).piece n = (openSubspaceRestriction U).obj (A.piece n) :=
  rfl

/-- **The restricted degree-one generator is the restriction of the generator.**
`SheafOfModules.openSubspaceGen` is the slice restriction of the generator pushed forward along
the site functor of the open subspace, which is what `SheafOfModules.openSubspaceRestriction`
applies to a morphism. -/
theorem openSubspaceGen_eq_openSubspaceRestriction_map :
    openSubspaceGen M A gen U = (openSubspaceRestriction U).map gen :=
  rfl

end Restriction

variable {M N : SheafOfModules.{u} (structureSheafRing X)}
  {A B : GradedAlgebra.{u, u} (structureSheafRing X)}
  {ι : M ⟶ A.piece 1} {κ : N ⟶ B.piece 1}
  (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (f : M ⟶ N)
  {A' B' : GradedAlgebra.{u, u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
    (Stacks.SheafOfModules.openSubspaceSiteFunctor U) ((structureSheafRing X).over U))}
  {ι' : (openSubspaceRestriction U).obj M ⟶ A'.piece 1}
  {κ' : (openSubspaceRestriction U).obj N ⟶ B'.piece 1}
  (hA' : IsExteriorAlgebra A' ι') (hB' : IsExteriorAlgebra B' κ')

include hB hB' in
/-- **The comparison of the two exterior algebras of `N|_U` extends the restricted generator**,
read with the restricted generator written as the restriction of the generator. This is
`SheafOfModules.exteriorRestrictOpenSubspaceIso_generator` at the spelling the identity below
produces it at. -/
theorem openSubspaceRestriction_map_comp_exteriorRestrictOpenSubspaceIso_hom :
    (openSubspaceRestriction U).map κ ≫
        (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' 1).hom = κ' :=
  Eq.trans
    (congrArg
      (fun z => z ≫ (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' 1).hom)
      (openSubspaceGen_eq_openSubspaceRestriction_map U N B κ).symm)
    (exteriorRestrictOpenSubspaceIso_generator N B κ hB U B' κ' hB')

include hA hB hB' in
/-- **The left-hand side of the crossing, on the generator.** The restriction of the
homomorphism inducing `⋀ⁿf`, followed by the comparison of the two exterior algebras of `N|_U`,
carries the restricted generator of `A` to `f|_U ≫ κ'`: it is the restriction of the equation
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one` characterizing `⋀f`, followed by
the fact that the comparison extends the generator. -/
theorem openSubspaceGen_comp_openSubspaceRestriction_map_map_app_one :
    openSubspaceGen M A ι U ≫
        ((openSubspaceRestriction U).map ((hA.map hB f).app 1) ≫
          (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' 1).hom) =
      (openSubspaceRestriction U).map f ≫ κ' :=
  Eq.trans
    (congrArg
      (fun z => z ≫ ((openSubspaceRestriction U).map ((hA.map hB f).app 1) ≫
        (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' 1).hom))
      (openSubspaceGen_eq_openSubspaceRestriction_map U M A ι))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans
        (congrArg
          (fun z => z ≫ (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' 1).hom)
          (Eq.trans ((openSubspaceRestriction U).map_comp ι ((hA.map hB f).app 1)).symm
            (Eq.trans (congrArg (openSubspaceRestriction U).map (hA.map_app_one hB f))
              ((openSubspaceRestriction U).map_comp f κ))))
        (Eq.trans (Category.assoc _ _ _)
          (congrArg (fun z => (openSubspaceRestriction U).map f ≫ z)
            (openSubspaceRestriction_map_comp_exteriorRestrictOpenSubspaceIso_hom U hB hB')))))

include hA hA' hB' in
/-- **The right-hand side of the crossing, on the generator.** The comparison of the two
exterior algebras of `M|_U`, followed by the homomorphism inducing `⋀ⁿ(f|_U)`, carries the
restricted generator of `A` to `f|_U ≫ κ'`. -/
theorem openSubspaceGen_comp_exteriorRestrictOpenSubspaceIso_hom_comp_map_app_one :
    openSubspaceGen M A ι U ≫
        ((exteriorRestrictOpenSubspaceIso M A ι hA U A' ι' hA' 1).hom ≫
          (hA'.map hB' ((openSubspaceRestriction U).map f)).app 1) =
      (openSubspaceRestriction U).map f ≫ κ' :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun z => z ≫ (hA'.map hB' ((openSubspaceRestriction U).map f)).app 1)
        (exteriorRestrictOpenSubspaceIso_generator M A ι hA U A' ι' hA'))
      (hA'.map_app_one hB' ((openSubspaceRestriction U).map f)))

include hA hB hA' hB' in
/-- **The map induced on exterior powers commutes with restriction to an open subspace.** With
`e_M : (⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)` and `e_N : (⋀ⁿN)|_U ≅ ⋀ⁿ(N|_U)` the comparisons
`SheafOfModules.exteriorRestrictOpenSubspaceIso`,

`(⋀ⁿf)|_U ≫ e_N = e_M ≫ ⋀ⁿ(f|_U)`.

Both sides are the degree-`n` component of a unital homomorphism `A|_U ⟶ B'` of sheaves of
graded algebras on `U`: on the left the restriction of the homomorphism inducing `⋀f`
(`SheafOfModules.GradedAlgebra.UnitalHom.openSubspace`) followed by the comparison of the two
exterior algebras of `N|_U`, on the right the comparison of the two exterior algebras of `M|_U`
followed by the homomorphism inducing `⋀(f|_U)`. `A|_U` is an exterior algebra of `M|_U`
(`SheafOfModules.isExteriorAlgebra_openSubspaceAlg`) with degree-one generator the restriction of
`ι`, and both homomorphisms carry that generator to `f|_U ≫ κ'`, so they are equal. -/
theorem openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso (n : ℤ) :
    (openSubspaceRestriction U).map (hA.pieceMap hB f n) ≫
        (exteriorRestrictOpenSubspaceIso N B κ hB U B' κ' hB' n).hom =
      (exteriorRestrictOpenSubspaceIso M A ι hA U A' ι' hA' n).hom ≫
        hA'.pieceMap hB' ((openSubspaceRestriction U).map f) n :=
  congrArg (fun g : UnitalHom (openSubspaceAlg A U) B' => g.app n)
    (IsUniversal.hom_ext (isExteriorAlgebra_openSubspaceAlg M A ι hA U)
      (κ := (openSubspaceRestriction U).map f ≫ κ')
      (g := ((hA.map hB f).openSubspace U).comp
        ((isExteriorAlgebra_openSubspaceAlg N B κ hB U).desc B' κ' hB'.1))
      (h := ((isExteriorAlgebra_openSubspaceAlg M A ι hA U).desc A' ι' hA'.1).comp
        (hA'.map hB' ((openSubspaceRestriction U).map f)))
      (hB'.1.comp ((openSubspaceRestriction U).map f))
      (openSubspaceGen_comp_openSubspaceRestriction_map_map_app_one U hA hB f hB')
      (openSubspaceGen_comp_exteriorRestrictOpenSubspaceIso_hom_comp_map_app_one U hA f hA' hB'))

end SheafOfModules

end
