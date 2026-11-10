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
to a constructible sheaf. That reduction is proved here, and the sheaf-level statement it reduces
to is carried as the hypothesis `hShriekSheaf`. What the source then does with the sheaf-level
statement — descend to an affine `Y`, cut `X` into finitely many affines, use Zariski's main
theorem to factor `f` as an open immersion followed by a finite morphism of finite presentation,
and conclude from Tags 03S8, 0F51 and 095R — needs inputs this repository does not have; see
"What is carried" below.

## Main definitions

* `Stacks.EtaleCohomology.ModuleFShriekConstructibleOnSheaves` — the sheaf-level form of
  Tag 0GK3, the statement the source's proof reduces to.
* `Stacks.EtaleCohomology.moduleFShriekDerivedCompHomologyFunctorIso` — the identification
  `Hⁱ ∘ f_! ≅ f_! ∘ Hⁱ` for the functor `f_!` of Tag 0F5N. This carries no hypothesis.

## Main results

* `Stacks.EtaleCohomology.isConstructible_moduleFShriekDerivedFunctor` — **Tag 0GK3**, granted
  the sheaf-level statement as the hypothesis `hShriekSheaf`.

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
hypothesis under which the carried sheaf-level statement is available.

### What is carried

One hypothesis, `hShriekSheaf`, the sheaf-level form of this very tag:
`Stacks.EtaleCohomology.ModuleFShriekConstructibleOnSheaves`. It is quantified over every pair of
schemes of the big étale site, every locally quasi-finite morphism of finite presentation between
them, every `Λ`-linear lift of its direct image with compact support, and every sheaf of
`Λ`-modules on the source, so it mentions neither this theorem's `f`, nor `fShriekMod`, nor `K`,
nor its conclusion. It is a statement about *sheaves*; the conclusion is about *complexes*, and
the passage from the one to the other is what is proved.

What would discharge it, by name. The two inputs that are absent outright are Tag 095R, that the
direct image along a finite morphism preserves constructibility, which carries no tag attribute
anywhere in this repository, and Tag 03S8 for an arbitrary constructible sheaf of `Λ`-modules:
of the latter there is only the case of the generators,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, the extension by zero of a
constant free rank-one module sheaf at a quasi-compact quasi-separated étale object, which rests
in turn on `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda`, Tag 03S8 part (1) for
sheaves of sets, itself carrying Tag 03S0 as a hypothesis. The remaining inputs of the source's
argument are present but for a different coefficient category or a different `f_!`:
`Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization`
is Tag 0F2N, Zariski's main theorem;
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic` is Tag 0F5H for the `f_!`
of Tag 0F6R with abelian coefficients; and
`AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso`
(Tag 0F50) and `AlgebraicGeometry.SmallEtale.fShriekSubsheaf_arrow_isIso` (Tag 0F51) are stated
for the proper-support `f_!` of Tag 0F4X, a different functor from the finite-support `f_!` of
Tag 0F6R that Tag 0F5N derives. So module-coefficient forms of 0F5H, 0F50 and 0F51 for the
`f_!` of Tag 0F6R are needed as well.

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

omit [IsNoetherianRing Λ] in
/-- **Stacks 0GK3**, granted the sheaf-level case. Let `Λ` be a Noetherian ring and let
`f : X ⟶ Y` be a morphism of schemes which is locally quasi-finite and of finite presentation.
If a complex `K` of étale sheaves of `Λ`-modules on `X` lies in `D_c(X_étale, Λ)`, then
`f_! K` lies in `D_c(Y_étale, Λ)`, where `f_!` is the functor of Stacks 0F5N.

The proof is the source's reduction. A `Λ`-linear lift of the direct image with compact support
is exact, so it acts on the derived category termwise and `Hⁱ(f_! K) ≅ f_!(Hⁱ K)`; each `Hⁱ K` is
constructible by hypothesis, and constructibility of its image under `f_!` is `hShriekSheaf`.

`hShriekSheaf` is the sheaf-level form of this tag, quantified over every morphism of the big
étale site that is locally quasi-finite and of finite presentation, every `Λ`-linear lift of its
direct image with compact support and every sheaf of `Λ`-modules on its source; it mentions
neither `f`, nor `fShriekMod`, nor `K`. See "What is carried" in the module documentation. -/
@[stacks 0GK3 "the source's reduction of the tag to its sheaf-level case, which is carried as \
hShriekSheaf: granted that a Λ-linear lift of f_! takes constructible sheaves of Λ-modules to \
constructible sheaves for every locally quasi-finite morphism of finite presentation, the \
functor f_! of Stacks 0F5N on unbounded derived categories sends D_c into D_c. The step from \
sheaves to complexes, exactness of f_! and hence Hⁱ(f_! K) ≅ f_!(Hⁱ K), is proved"]
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
