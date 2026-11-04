module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareTransportAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMapDegreeOne

/-!
# The naturality of Stacks 04G2 (1) read at the defining ideal sheaf of the range

`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq` is the
naturality of the comparison of [Stacks Project, Tag 04G2] (1) in the closed immersion, stated at
the `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso` respelling: the inverse image
of the kernel ideal sheaf of the *represented* morphism, in degree one, with the canonical map of
the square written as `AlgebraicGeometry.Space.kernelIdealSquareMap`.

A consumer of that naturality — the tail factor of
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`, which is the input 4 of
[Stacks Project, Tag 04AM] — meets the comparison at the *defining ideal sheaf of the range of the
closed immersion*, and the canonical map of the square as
`AlgebraicGeometry.Space.idealSheafMap`, because that is the spelling
`AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` and
`AlgebraicGeometry.Space.conormalMap` are written at.  This file carries the naturality across
that respelling.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSquareMap_one_comp_eq_idealSheafMap_of_subspaces`: **the
  degree-one square map of kernel ideal sheaves, read after the transport of its source, is the
  map of defining ideal sheaves of [Stacks Project, Tag 04CP]** — at an arbitrary spelling of the
  two closed immersions.
* `AlgebraicGeometry.Space.conormalSheafMap_representedConormalDefiningIdealIso_of_comp_eq`:
  **the naturality of the comparison of [Stacks Project, Tag 04G2] (1) in the closed immersion,
  read at the defining ideal sheaf of the range**, with nothing assumed.

## Why the degree-one agreement has to be restated, and why it is not a copy

`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` states the agreement for the
square map of the *inclusions of the two closed subspaces*.  The naturality above is stated for
the square map of the two *represented* morphisms, and a represented closed immersion is not the
inclusion of its range: it is that inclusion precomposed with
`AlgebraicGeometry.Space.rangeSpaceIso`.  So that agreement does not apply, and cannot be
made to by instantiation.

It restates without any new argument, because the square map is pinned by its composite with the
inclusion of the sheaf of ideals into the structure sheaf — a monomorphism — and that composite,
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`, mentions the two closed immersions *only*
through the two sheaves of ideals they cut out.  Two spellings cutting out equal sheaves of ideals
therefore have equal square maps, across the transports of the two equalities.  What is proved
here is moreover the *consumed* form — the transport of the source already composed on, where it
cancels — rather than the agreement with transports on both sides, because that is the only form
a square can use: the transport of the source is what the square comparison of the two routes
carries across by its own naturality.

## Why the proofs are terms and not rewrites

Rewriting the agreement into the naturality is a `rewrite` failure, not a slow proof: the category
of the inverse image is `AlgebraicGeometry.Space.Modules` of the ambient space while the equality
of sheaves of ideals is stated in `SheafOfModules` of its structure ring sheaf.  The two are
definitionally equal and the *statements* elaborate, but a rewrite motive built over the mixed
term is reported as not type-correct under `implicit` transparency, and the next pattern — here
`CategoryTheory.eqToHom_map` — is then not found in a target that visibly contains it.  Composing
equations with `Eq.trans` and `congrArg` never builds a motive, and both proofs below are
therefore terms, assembled by two generic lemmas at variables.

One more elaboration fact matters.  `AlgebraicGeometry.Space.idealSheafMap` takes its two ambient spaces
as **implicit** arguments, inferrable from the two closed subspaces only through a projection —
`Z : ClosedSubspaces B S hS X.1` — and at the range of a represented closed immersion that
projection is not a pattern the unifier can solve.  Writing the two ambient spaces out, as
`(X := _)` and `(X' := _)`, is the difference between the naturality's statement elaborating in a
second and a deterministic `isDefEq` timeout at 200 000 heartbeats on the junction where the
square comparison meets the map of ideal sheaves.  The naturality at the kernel-ideal
spelling never meets this, because `AlgebraicGeometry.Space.kernelIdealSquareMap` takes all four
morphisms of its square explicitly.

No `@[stacks]` attribute is claimed: Tag 04CP is registered at
`AlgebraicGeometry.Space.conormalMap` and Tag 04G2 at the two comparisons, and what is proved here
is a change of spelling inside the proof of [Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- **Two maps out of the inverse image of a submodule agree, after one transport on each side,
because their composites with a monomorphism do**, at variables.

`m` and `m'` are pinned by their composites with `ιT` and `ιT'` into a common object, those
composites are the image of `ιA` and of `ιA'` followed by one and the same `t` (`hm`, `hm'`), and
the two transports carry `ιA'` to `ιA` under `F` (`hδ`) and `ιT` to `ιT'` (`hτ`).

This is `CategoryTheory.eq_eqToHom_comp_comp_eqToHom_of_mono` of
`StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMapDegreeOne` with the two transports taken
as *data* and composed onto the two sides, rather than written as `CategoryTheory.eqToHom` of two
object equalities on one side.  That is what makes the conclusion usable inside a naturality
square, and it is also what keeps the proof a term: no rewrite motive is built over a morphism of
the inverse image, which is where the mixed spelling of the module category bites; see the module
documentation. -/
theorem comp_eq_comp_of_mono_of_map (F : C ⥤ D) {A A' O : C} {T T' V : D}
    {ιA : A ⟶ O} {ιA' : A' ⟶ O} {δ : F.obj A' ⟶ F.obj A}
    (hδ : δ ≫ F.map ιA = F.map ιA')
    {ιT : T ⟶ V} {ιT' : T' ⟶ V} {τ : T' ⟶ T} (hτ : τ ≫ ιT = ιT')
    (hmono : Mono ιT) {t : F.obj O ⟶ V} {m : F.obj A ⟶ T} {m' : F.obj A' ⟶ T'}
    (hm : m ≫ ιT = F.map ιA ≫ t) (hm' : m' ≫ ιT' = F.map ιA' ≫ t) :
    δ ≫ m = m' ≫ τ := by
  refine (cancel_mono ιT).1 ?_
  simp only [Category.assoc, hm, hτ, hm', reassoc_of% hδ]

/-- **A naturality square carried across a respelling of the three objects it is read at**, at
variables.

A square `m ≫ q₁ ≫ k = β₁ ≫ β₂ ≫ x` is given at one spelling; `m` and `x` factor as a map at the
other spelling followed by a transport (`hm`, `hx`), the square comparison `q₁` moves across the
transport of the inner object (`hnat`), and the inner transport absorbs the map at the first
spelling into the map at the second followed by the transport of the target (`htk`).  Cancelling
that last transport against a section of it (`ht`) leaves the square at the other spelling.

Everything is a variable, so a consumer supplies this as a term with each hypothesis in the
spelling it has and every position is *assigned* rather than unified; that is the discipline of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_hom_comp_of_factorizations`
and of `Stacks.CategoryTheory.square_transport_aux_of_mid`. -/
theorem square_of_respelled_transports {A P₁ P₂ B₀ B₁ C₀ C₁ Dobj E : C}
    {m : A ⟶ B₁} {α : A ⟶ B₀} {t₁ : B₀ ⟶ B₁} {q₁ : B₁ ⟶ C₁} {q₀ : B₀ ⟶ C₀} {t₂ : C₀ ⟶ C₁}
    {k : C₁ ⟶ Dobj} {d : C₀ ⟶ E} {t₃ : E ⟶ Dobj} {t₃' : Dobj ⟶ E}
    {β₁ : A ⟶ P₁} {β₂ : P₁ ⟶ P₂} {x : P₂ ⟶ Dobj} {γ : P₂ ⟶ E}
    (hK : m ≫ q₁ ≫ k = β₁ ≫ β₂ ≫ x)
    (hm : m = α ≫ t₁) (hx : x = γ ≫ t₃)
    (hnat : t₁ ≫ q₁ = q₀ ≫ t₂) (htk : t₂ ≫ k = d ≫ t₃) (ht : t₃ ≫ t₃' = 𝟙 E) :
    α ≫ q₀ ≫ d = β₁ ≫ β₂ ≫ γ := by
  have e1 : (α ≫ q₀ ≫ d) ≫ t₃ = α ≫ (q₀ ≫ t₂) ≫ k := by
    simp only [Category.assoc]
    rw [htk]
  have e2 : α ≫ (q₀ ≫ t₂) ≫ k = m ≫ q₁ ≫ k := by
    rw [← hnat, hm]
    simp only [Category.assoc]
  have e3 : β₁ ≫ β₂ ≫ x = (β₁ ≫ β₂ ≫ γ) ≫ t₃ := by
    rw [hx]
    simp only [Category.assoc]
  simpa [ht] using (((e1.trans e2).trans hK).trans e3) =≫ t₃'

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso squarePullbackCompIso
  representedSmallEtaleModuleEquivalence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The degree-one square map at an arbitrary spelling of the two closed immersions -/

section DegreeOne

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **The degree-one square map of kernel ideal sheaves, read after the transport of its source, is
the map of defining ideal sheaves of [Stacks Project, Tag 04CP].**

Let `i : Y ⟶ X` and `i' : Y' ⟶ X'` be morphisms over `g : X ⟶ X'` whose kernel ideal sheaves in
degree one are the defining ideal sheaves of closed subspaces `Z ⊆ X` and `Z' ⊆ X'`, and let the
inclusions of those subspaces also form a commutative square over `g`.  Then the inverse image
along `g` of the transport of the source, followed by the degree-one square map of `i` and `i'`,
is the map `g^*𝓘' ⟶ 𝓘` of `AlgebraicGeometry.Space.idealSheafMap` of the square of inclusions,
followed by the transport of the target.

This is `AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` with the two closed
immersions freed from being the inclusions of the two subspaces, and with the transport of the
source consumed; see the module documentation for why a represented closed immersion needs that
freedom, and why it costs no new argument.  The two object equalities are implicit, since proof
irrelevance makes `CategoryTheory.eqToHom` of either depend only on its type. -/
theorem kernelIdealSquareMap_one_comp_eq_idealSheafMap_of_subspaces
    (i : Y ⟶ X) (i' : Y' ⟶ X') (f : Y ⟶ Y') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (f₂ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq₂ : subspaceInclusion B S hS X Z ≫ g = f₂ ≫ subspaceInclusion B S hS X' Z')
    (h : kernelIdealSheafZPow B S hS i 1 = definingIdealSheaf B S hS X Z)
    (h' : kernelIdealSheafZPow B S hS i' 1 = definingIdealSheaf B S hS X' Z')
    {e : (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (kernelIdealSheafZPow B S hS i 1).toSheafOfModules}
    {e₂ : (definingIdealSheaf B S hS X' Z').toSheafOfModules =
      (kernelIdealSheafZPow B S hS i' 1).toSheafOfModules} :
    (modulePullback B S hS g).map (eqToHom e₂) ≫
        kernelIdealSquareMap B S hS i i' f g hsq 1 =
      idealSheafMap B S hS Z Z' g f₂ hsq₂ ≫ eqToHom e :=
  Stacks.CategoryTheory.comp_eq_comp_of_mono_of_map (modulePullback B S hS g)
    (((modulePullback B S hS g).map_comp (eqToHom e₂)
          (kernelIdealSheafZPow B S hS i' 1).ι).symm.trans
      (congrArg (modulePullback B S hS g).map
        (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι h'.symm e₂)))
    (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι h.symm e)
    (inferInstanceAs (Mono (kernelIdealSheafZPow B S hS i 1).ι))
    (kernelIdealSquareMap_comp_ι B S hS i i' f g hsq 1)
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f₂ hsq₂)

end DegreeOne

/-! ### The naturality of the comparison at the defining ideal sheaf of the range -/

section Square

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')

/-- **The naturality of the comparison of [Stacks Project, Tag 04G2] (1) in the closed immersion,
read at the defining ideal sheaf of the range, with nothing assumed.**

For a commutative square `j ≫ a = b ≫ j'` of the big fppf category over `S` whose horizontal
morphisms are closed immersions of schemes, and any morphism `f₂` of the two ranges over
`a` — the comparison
`AlgebraicGeometry.Space.representedConormalDefiningIdealIso` carries the map
`AlgebraicGeometry.Space.idealSheafMap` of defining ideal sheaves of the square of inclusions,
read through the square comparison `AlgebraicGeometry.Space.squarePullbackCompIso`, to the
associated module of the map `Stacks.ClosedImmersion.conormalSheafMap` of Morphisms, Lemma
[Stacks Project, Tag 01R4].

This is
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`
carried across the respelling of the three objects it is read at: the source and target
transports are
`AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso_hom_eq`, the square comparison
moves across the inner one by its own naturality, and the inner transport absorbs the degree-one
square map into `AlgebraicGeometry.Space.idealSheafMap` by
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_comp_eq_idealSheafMap_of_subspaces`.  The
pasting is `Stacks.CategoryTheory.square_of_respelled_transports`.

No étaleness and no cartesianness is used: the morphism of ranges and its square are data, and a
consumer at an étale chart supplies them. -/
theorem conormalSheafMap_representedConormalDefiningIdealIso_of_comp_eq
    [hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]
    (hsq : j ≫ a = b ≫ j')
    (f₂ : closedSubspaceRangeSpace B S hS j hj ⟶ closedSubspaceRangeSpace B S hS j' hj')
    (hsq₂ : subspaceInclusion B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj) ≫ representedSpaceMap B S hS a =
        f₂ ≫ subspaceInclusion B S hS ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩
          (closedSubspaceRange B S hS j' hj')) :
    (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (representedConormalDefiningIdealIso B S hS j').hom ≫
        (squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
            (representedSpaceMap B S hS a)
            (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.app
          (definingIdealSheaf B S hS ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩
            (closedSubspaceRange B S hS j' hj')).toSheafOfModules ≫
          (modulePullback B S hS (representedSpaceMap B S hS j)).map
            (idealSheafMap B S hS
              (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
              (X' := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)
              (closedSubspaceRange B S hS j hj)
              (closedSubspaceRange B S hS j' hj') (representedSpaceMap B S hS a) f₂ hsq₂) =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.ClosedImmersion.conormalSheafMap
                (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) ≫
          (representedConormalDefiningIdealIso B S hS j).hom := by
  refine Stacks.CategoryTheory.square_of_respelled_transports
    (conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq B S hS j j' b a hsq)
    ((congrArg (modulePullback B S hS (representedSpaceMap B S hS b)).map
        (representedConormalKernelIdealZPowIso_hom_eq B S hS j')).trans
      ((modulePullback B S hS (representedSpaceMap B S hS b)).map_comp _ _))
    (representedConormalKernelIdealZPowIso_hom_eq B S hS j)
    ((squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
        (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
        (representedSpaceMap B S hS a)
        (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.naturality _) ?_
    (Iso.hom_inv_id ((modulePullback B S hS (representedSpaceMap B S hS j)).mapIso
      (eqToIso (congrArg
        (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule => N.toSheafOfModules)
        (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj).symm))))
  · exact (((modulePullback B S hS (representedSpaceMap B S hS j)).map_comp _ _).symm.trans
      (congrArg (modulePullback B S hS (representedSpaceMap B S hS j)).map
        (kernelIdealSquareMap_one_comp_eq_idealSheafMap_of_subspaces B S hS
          (representedSpaceMap B S hS j) (representedSpaceMap B S hS j')
          (representedSpaceMap B S hS b) (representedSpaceMap B S hS a)
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)
          (closedSubspaceRange B S hS j hj) (closedSubspaceRange B S hS j' hj') f₂ hsq₂
          (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj)
          (kernelIdealSheafZPow_one_representedSpaceMap B S hS j' hj')))).trans
      ((modulePullback B S hS (representedSpaceMap B S hS j)).map_comp _ _)


end Square

end AlgebraicGeometry.Space

end
