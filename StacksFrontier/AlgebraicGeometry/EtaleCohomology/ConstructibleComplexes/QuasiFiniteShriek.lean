module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage

/-!
# Direct image with compact support of a complex with constructible cohomology

Let `Λ` be a Noetherian ring and let `f : X ⟶ Y` be a morphism of schemes which is locally
quasi-finite and of finite presentation. Tag 0GK3 asserts that the functor
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Tag 0F5N sends `D_c(X_étale, Λ)` into
`D_c(Y_étale, Λ)`.

The source's proof opens by reducing the statement about complexes to a statement about sheaves:
`f_!` is exact, so it needs no deriving, acts on the derived category termwise, and
`Hⁱ(f_! K) ≅ f_!(Hⁱ K)`; hence it suffices that `f_!` take a constructible sheaf of `Λ`-modules
to a constructible sheaf. This file proves that reduction for an arbitrary `Λ`-linear lift of
`f_!`, with the sheaf-level statement as the hypothesis `hShriekSheaf`. The tag itself, with the
sheaf-level case proved, is
`Stacks.EtaleCohomology.isConstructible_moduleFShriekDerivedFunctor_general` in the module
`QuasiFiniteShriekUnconditional` beside this one, whose sheaf-level case is
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_fShriekMod`.

## Main definitions

* `Stacks.EtaleCohomology.ModuleFShriekConstructibleOnSheaves` — the sheaf-level form of
  Tag 0GK3, the statement the source's proof reduces to.
* `Stacks.EtaleCohomology.moduleFShriekDerivedCompHomologyFunctorIso` — the identification
  `Hⁱ ∘ f_! ≅ f_! ∘ Hⁱ` for the functor `f_!` of Tag 0F5N. This carries no hypothesis.

## Main results

* `Stacks.EtaleCohomology.isConstructible_moduleFShriekDerivedFunctor` — the reduction of
  Tag 0GK3 to its sheaf-level case, for an arbitrary `Λ`-linear lift of `f_!`, from the
  hypothesis `hShriekSheaf`.

## Implementation notes

`D_c(X_étale, Λ)` is `Stacks.EtaleCohomology.IsConstructible`, the predicate of Tag 095W on the
unbounded derived category of sheaves of `Λ`-modules on the small étale site of Tag 021B;
membership of `Stacks.EtaleCohomology.ConstructibleDerivedCategory` is immediate from it. The
derived category is the standard model, the one at which that predicate is stated.

`f_!` is the functor of Tag 0F5N in the form in which this repository carries it for a general
coefficient ring, `AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctor`: the `Λ`-linear lift
`fShriekMod` of the abelian `f_!` of Tag 0F6R is taken as data together with the isomorphism
`hlift` identifying the two on underlying abelian sheaves, and it is assumed to have a right
adjoint, which is Tag 0F59 part (3). Exactness of the lift is then a theorem, and
`moduleFShriekDerivedFunctor` is literally `CategoryTheory.Functor.mapDerivedCategory` of the
lift, so `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso` gives the
identification of cohomology sheaves directly.

The hypotheses on `f` are exactly the source's: `AlgebraicGeometry.LocallyQuasiFinite`, and
`AlgebraicGeometry.LocallyOfFinitePresentation` with `AlgebraicGeometry.QuasiCompact` and
`AlgebraicGeometry.QuasiSeparated`, whose conjunction is `AlgebraicGeometry.FinitePresentation`,
Tag 01TP part (3). Being locally quasi-finite includes being locally of finite type, which is
what `f_!` itself needs; here it is supplied by Mathlib from local finite presentation. The
reduction proved below uses only exactness of `f_!`; finite presentation enters solely as the
hypothesis under which the sheaf-level statement holds.

### The hypothesis `hShriekSheaf`

`Stacks.EtaleCohomology.ModuleFShriekConstructibleOnSheaves` is the sheaf-level form of the tag,
quantified over every pair of schemes of the big étale site, every locally quasi-finite morphism
of finite presentation between them, every `Λ`-linear lift of its direct image with compact
support, and every sheaf of `Λ`-modules on the source. For the lift
`AlgebraicGeometry.SmallEtale.fShriekMod` it is proved as
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_fShriekMod`, following the source: descend to
an affine `Y`, present a constructible sheaf by the generators of Tag 095N, factor by Zariski's
main theorem (Tag 0F2N), and conclude from Tags 03S8 and 095R.

## References

* [Stacks Project, Tag 0GK3](https://stacks.math.columbia.edu/tag/0GK3)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v r

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) v r} Λ)]

/-- The sheaf-level form of Stacks 0GK3, the statement to which the source's proof reduces the
tag: for every locally quasi-finite morphism of finite presentation `g : X ⟶ Y` of the big étale
site and every `Λ`-linear lift of its direct image with compact support, that lift carries a
constructible sheaf of `Λ`-modules on `X` to a constructible sheaf of `Λ`-modules on `Y`. -/
public def ModuleFShriekConstructibleOnSheaves : Prop :=
  ∀ (X Y : B.Scheme) (g : X ⟶ Y) [LocallyQuasiFinite (B.inclusion.map g)]
    [LocallyOfFinitePresentation (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [QuasiSeparated (B.inclusion.map g)]
    (gShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ),
    (gShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B g) →
    ∀ G : ModuleSheaf.{u, v, r} B X Λ, IsConstructibleModuleSheaf B X Λ G →
      IsConstructibleModuleSheaf B Y Λ (gShriekMod.obj G)

section

variable {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
  (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
    forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f)

/-- Degree-`i` cohomology commutes with the functor `f_!` of Stacks 0F5N: a `Λ`-linear lift of
the direct image with compact support is exact, so the induced functor on unbounded derived
categories is the termwise one and `Hⁱ(f_! K) ≅ f_!(Hⁱ K)`, naturally in `K`. This is the Lean
content of the first sentence of the proof of Stacks 0GK3, and it carries no hypothesis beyond
the data of the lift. -/
public def moduleFShriekDerivedCompHomologyFunctorIso (i : ℤ) :
    moduleFShriekDerivedFunctor B Λ f fShriekMod hlift ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B Y Λ) i ≅
      DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B X Λ) i ⋙ fShriekMod :=
  letI := additive_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  letI := preservesFiniteLimits_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  letI := isLeftAdjoint_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  letI : PreservesFiniteColimits fShriekMod := ⟨fun _ _ _ => inferInstance⟩
  fShriekMod.mapDerivedCategoryCompHomologyFunctorIso i

variable [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)]

/-- **The reduction of Stacks 0GK3 to its sheaf-level case.** Let `Λ` be a Noetherian ring and
let `f : X ⟶ Y` be a morphism of schemes which is locally quasi-finite and of finite presentation,
and let `fShriekMod` be any `Λ`-linear lift of the direct image with compact support. If `K` lies
in `D_c(X_étale, Λ)`, then its image under the induced functor on derived categories lies in
`D_c(Y_étale, Λ)`, provided the sheaf-level statement `hShriekSheaf` holds.

The proof is the source's reduction. A `Λ`-linear lift of the direct image with compact support
is exact, so it acts on the derived category termwise and `Hⁱ(f_! K) ≅ f_!(Hⁱ K)`; each `Hⁱ K` is
constructible by hypothesis, and constructibility of its image under `f_!` is `hShriekSheaf`.
Stacks 0GK3 itself, with the sheaf-level case proved, is
`Stacks.EtaleCohomology.isConstructible_moduleFShriekDerivedFunctor_general`. -/
public theorem isConstructible_moduleFShriekDerivedFunctor
    (hShriekSheaf : ModuleFShriekConstructibleOnSheaves B Λ)
    (K : DerivedCategory (ModuleSheaf.{u, v, r} B X Λ)) (hK : IsConstructible B X Λ K) :
    IsConstructible B Y Λ ((moduleFShriekDerivedFunctor B Λ f fShriekMod hlift).obj K) := by
  intro i
  refine isConstructibleModuleSheaf_congr B Λ Y
    ((moduleFShriekDerivedCompHomologyFunctorIso B Λ f fShriekMod hlift i).app K).symm ?_
  exact hShriekSheaf X Y f fShriekMod hlift _ (hK i)

end

end Stacks.EtaleCohomology

end
