module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

import StacksCore.Tactic.StacksAttribute

/-!
# Direct image with compact support preserves torsion cohomology

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `Λ` be a ring. The functor
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5N sends a complex with torsion cohomology
sheaves to a complex with torsion cohomology sheaves. This is Stacks 0GJX.

The reduction is the one of the source. A `Λ`-linear lift of `f_!` is exact, so the functor it
induces on unbounded derived categories commutes with cohomology: the `i`-th cohomology sheaf of
`f_! K` is `f_!` of the `i`-th cohomology sheaf of `K`. Torsion of a sheaf of `Λ`-modules is a
property of its underlying abelian sheaf, and the lift is identified with `f_!` on underlying
abelian sheaves, so the statement reduces to the preservation of torsion by `f_!` on abelian
sheaves — which is the content of Stacks 0F5F, the description of the stalks of `f_!`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleTorsionSheafProperty` — the property that an étale sheaf of
  `Λ`-modules is torsion, namely that its underlying abelian sheaf is.
* `AlgebraicGeometry.SmallEtale.moduleTorsionCohomologyProperty` — the property that all
  cohomology sheaves of an object of `D(X_étale, Λ)` are torsion.
* `AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctorCompHomologyFunctorIso` — the
  identification `H^i(f_! K) ≅ f_!(H^i K)` for `f_!` on unbounded derived categories of étale
  sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.moduleTorsionSheafProperty_fShriekMod` — a `Λ`-linear lift of
  `f_!` sends torsion étale sheaves of `Λ`-modules to torsion étale sheaves of `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor` —
  **Stacks 0GJX**: `f_!` on unbounded derived categories of étale sheaves of `Λ`-modules
  preserves having torsion cohomology sheaves.

## Implementation notes

Torsion of a sheaf of `Λ`-modules is *defined* here as torsion of its underlying abelian sheaf,
`Stacks.Torsion.torsionSheafProperty` of the image under
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf`. That is the meaning of torsion in the source,
where the coefficient ring plays no role in the condition, and it makes the passage from the
abelian statement to the `Λ`-linear one a transport along the isomorphism `hlift` identifying a
`Λ`-linear lift of `f_!` with `f_!` on underlying abelian sheaves. The library's
`Stacks.EtaleCohomology.IsTorsionEtaleModule` is a predicate for a different category of module
sheaves and is not used.

The abelian-sheaf input is
`AlgebraicGeometry.SmallEtale.torsionSheafProperty_fShriekFunctor_obj`, that `f_!` on abelian
étale sheaves sends torsion sheaves to torsion sheaves, which is read off the stalk description of
`f_!` in Stacks 0F5F. It is consumed at the cohomology sheaves of `K`, one degree at a time.

The statement is about the unbounded derived categories produced by Stacks 0F5N, with no
boundedness restriction: a `Λ`-linear lift of `f_!` is exact, so no derived functor is involved
and the comparison of cohomology,
`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`, is available at every degree.
The hypotheses on `f`, `Λ`, the lift `fShriekMod`, the comparison `hlift` and the
`CategoryTheory.HasDerivedCategory` instances are exactly those of
`AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctor`, so the two statements compose.

## References

* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Torsion

universe u v w r

namespace AlgebraicGeometry.SmallEtale

/-- The property that an étale sheaf of `Λ`-modules is torsion: its underlying abelian sheaf is a
torsion abelian sheaf in the sense of Stacks 0DD7. -/
public def moduleTorsionSheafProperty (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type r)
    [Ring Λ] : ObjectProperty (ModuleSheaf.{u, v, r} B S Λ) :=
  fun F ↦ torsionSheafProperty (SmallEtale.topology B S.obj S.property)
    ((forgetModuleSheaf.{u, v, r} B S Λ).obj F)

/-- The property that all cohomology sheaves of an object of `D(S_étale, Λ)` are torsion. -/
public def moduleTorsionCohomologyProperty (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type r)
    [Ring Λ] [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B S Λ)] :
    ObjectProperty (DerivedCategory (ModuleSheaf.{u, v, r} B S Λ)) :=
  fun K ↦ ∀ i : ℤ, moduleTorsionSheafProperty.{u, v, r} B S Λ
    ((DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B S Λ) i).obj K)

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- Torsion of abelian étale sheaves on `Y` is invariant under isomorphism. -/
private theorem torsionSheafProperty_of_iso (B : BigEtaleSite.{u}) {Y : B.Scheme}
    {A A' : AbelianSheaf.{u, w} B Y} (e : A' ≅ A)
    (h : torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) A') :
    torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) A :=
  (torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) :
    ObjectProperty (AbelianSheaf.{u, w} B Y)).prop_of_iso e h

/-- A `Λ`-linear lift of the direct image with compact support sends torsion étale sheaves of
`Λ`-modules to torsion étale sheaves of `Λ`-modules: the lift is identified with `f_!` on
underlying abelian sheaves, and `f_!` preserves torsion there. -/
@[stacks 0GJX "the sheaf-level reduction: a `Λ`-linear lift of `f_!` preserves torsion"]
public theorem moduleTorsionSheafProperty_fShriekMod
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f)
    (F : ModuleSheaf.{u, v, r} B X Λ)
    (hF : moduleTorsionSheafProperty.{u, v, r} B X Λ F) :
    moduleTorsionSheafProperty.{u, v, r} B Y Λ (fShriekMod.obj F) :=
  torsionSheafProperty_of_iso.{u, max v r} B (hlift.app F).symm
    (torsionSheafProperty_fShriekFunctor_obj.{u, max v r} B f _ hF)

variable [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B Y Λ)]

/-- The identification `H^i(f_! K) ≅ f_!(H^i K)` for `f_!` on unbounded derived categories of
étale sheaves of `Λ`-modules: a `Λ`-linear lift of `f_!` is exact, and an exact functor commutes
with the cohomology functors of the derived category. -/
public def moduleFShriekDerivedFunctorCompHomologyFunctorIso
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f)
    (i : ℤ) :
    moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f fShriekMod hlift ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B Y Λ) i ≅
      DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B X Λ) i ⋙ fShriekMod :=
  have := additive_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  have := preservesFiniteLimits_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  have := isLeftAdjoint_of_forgetModuleSheafIso.{u, v, r} B Λ f fShriekMod hlift
  have : PreservesFiniteColimits fShriekMod := ⟨fun _ _ _ => inferInstance⟩
  fShriekMod.mapDerivedCategoryCompHomologyFunctorIso i

/-- **Stacks 0GJX.** Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `Λ` be
a ring. The functor `f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5N sends a complex with
torsion cohomology sheaves to a complex with torsion cohomology sheaves.

The `Λ`-linear lift of `f_!` is exact, so the cohomology of `f_! K` is `f_!` of the cohomology of
`K`; torsion of a sheaf of `Λ`-modules is torsion of its underlying abelian sheaf, which `hlift`
identifies with the image under `f_!` of the underlying abelian sheaf; and `f_!` preserves torsion
abelian sheaves, which Stacks 0GJX reads off the stalk description of `f_!` in Stacks 0F5F. -/
@[stacks 0GJX "general coefficient ring `Λ`: for a `Λ`-linear lift of `f_!`, the functor \
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Tag 0F5N sends complexes with torsion cohomology \
sheaves to complexes with torsion cohomology sheaves"]
public theorem moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f)
    (K : DerivedCategory (ModuleSheaf.{u, v, r} B X Λ))
    (hK : moduleTorsionCohomologyProperty.{u, v, w, r} B X Λ K) :
    moduleTorsionCohomologyProperty.{u, v, w, r} B Y Λ
      ((moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f fShriekMod hlift).obj K) := by
  intro i
  exact torsionSheafProperty_of_iso.{u, max v r} B
    ((forgetModuleSheaf.{u, v, r} B Y Λ).mapIso
      ((moduleFShriekDerivedFunctorCompHomologyFunctorIso.{u, v, w, r}
        B Λ f fShriekMod hlift i).app K)).symm
    (moduleTorsionSheafProperty_fShriekMod.{u, v, r} B Λ f fShriekMod hlift _ (hK i))

end AlgebraicGeometry.SmallEtale

end
