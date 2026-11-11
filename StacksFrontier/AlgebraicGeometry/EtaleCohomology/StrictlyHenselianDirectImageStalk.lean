module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkHigherDirectImageStrictHenselization
import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of higher direct images over a strictly henselian base

Let `R` be a strictly henselian local ring, let `s` be a geometric point of `Spec R` lying over
the closed point and let `f : X ⟶ Spec R` be a morphism in a big étale site. For an abelian
sheaf `F` on the small étale site of `X`, the stalk of `R^n f_* F` at `s` is the étale
cohomology group `H^n_ét(X, F)`.

Over such a base the étale neighbourhoods of `s` have an initial object, namely the final object
of the small étale site, so global sections are the stalk at `s` and are exact (Stacks 03QO).
Global sections on `X` are global sections on `Spec R` composed with the direct image, so an
exact functor passes through the right derived functor of the direct image.

## Main definitions

* `Stacks.StrictlyHenselian.sectionsToEtaleStalk` — the germ at `s` of a global section, for
  sheaves with values in an arbitrary category.
* `Stacks.StrictlyHenselian.higherDirectImage` — the `n`-th higher direct image along a
  morphism to `Spec R`.

## Main results

* `Stacks.StrictlyHenselian.isIso_sectionsToEtaleStalk` — that germ map is an isomorphism, the
  coefficient category being arbitrary.
* `Stacks.StrictlyHenselian.higherDirectImageEtaleStalkIso` — the stalk of the `n`-th higher
  direct image is the `n`-th étale cohomology group of the source.

### Relation to Stacks 03Q9

Tag 03Q9 identifies `(R^n f_* F)_s` with `H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)` over an
arbitrary base, for `f` quasi-compact and quasi-separated. Its three assertions are
`AlgebraicGeometry.stalkHigherDirectImageIso`,
`AlgebraicGeometry.stalkDerivedPushforwardHomologyIso` and
`AlgebraicGeometry.stalkDerivedPushforwardIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkHigherDirectImageStrictHenselization.lean`,
in Mathlib's `AlgebraicGeometry.Scheme.Etale` model of the small étale site; the first of these is
registered for the tag at the end of this file. The statement here
is the special case of a base that is already strictly henselian local at `s`, in the
`AlgebraicGeometry.BigEtaleSite` model: there `𝒪^{sh}_{S,s} = R`, the base change
`X ×_S Spec(𝒪^{sh}_{S,s})` is `X` itself and the right hand side is `H^n_ét(X, F)`, and no
hypothesis on `f` is needed.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.StrictlyHenselian

variable (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
  (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))

/-- The germ at `s` of a global section on the small étale site of `Spec R`: the colimit
inclusion of the final object, viewed as an étale neighbourhood of `s`. -/
public def sectionsToEtaleStalk {A : Type*} [Category A]
    (F : (SmallEtale B (Spec (.of R)) hS)ᵒᵖ ⥤ A)
    [HasColimit ((Functor.Elements.π (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F)] :
    F.obj (op (SmallEtale.final B (Spec (.of R)) hS)) ⟶
      etaleStalk B (Spec (.of R)) hS s F :=
  colimit.ι ((Functor.Elements.π (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F)
    (op (finalNeighborhood B R hS s))

/-- Over a strictly henselian local ring the germ at a geometric point lying over the closed
point is an isomorphism from global sections onto the stalk, for arbitrary coefficients. -/
public theorem isIso_sectionsToEtaleStalk [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) {A : Type*} [Category A]
    (F : (SmallEtale B (Spec (.of R)) hS)ᵒᵖ ⥤ A)
    [HasColimit ((Functor.Elements.π (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F)] :
    IsIso (sectionsToEtaleStalk B R hS s F) := by
  obtain ⟨h⟩ := nonempty_isInitial_finalNeighborhood B R hS s hs
  exact (colimit.isColimit _).isIso_ι_app_of_isTerminal _ (IsInitial.op _ h)

section HigherDirectImage

variable [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u + 1}]
  {X : B.Scheme}
  [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}]
  [EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  (f : X ⟶ B.obj (Spec (.of R)) hS)

/-- The `n`-th higher direct image of abelian étale sheaves along `f : X ⟶ Spec R`. -/
public abbrev higherDirectImage (n : ℕ) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u + 1} :=
  letI := Stacks.HigherDirectImage.pushforward_additive.{u, u + 1} B f
  (Stacks.HigherDirectImage.pushforward.{u, u + 1} B f).rightDerived n

variable [StrictlyHenselianLocalRing R]

/-- **Stacks 03Q9 over a strictly henselian base**, in the `BigEtaleSite` model; the general
statement, in Mathlib's model, is
`AlgebraicGeometry.stalkHigherDirectImageIso`. The stalk at `s` of the `n`-th higher direct
image of `F` along `f : X ⟶ Spec R` is the `n`-th étale cohomology group of `X` with
coefficients in `F`. -/
public def higherDirectImageEtaleStalkIso
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) (n : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    etaleStalk B (Spec (.of R)) hS s ((higherDirectImage B R hS f n).obj F).obj ≅
      ((smallEtaleGlobalSections B X).rightDerived n).obj F :=
  letI := Stacks.HigherDirectImage.pushforward_additive.{u, u + 1} B f
  letI : PreservesFiniteLimits (smallEtaleGlobalSections B (B.obj (Spec (.of R)) hS)) :=
    preservesFiniteLimits_of_natIso
      (Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B (Spec (.of R)) hS)
        AddCommGrpCat.{u + 1} (SmallEtale.finalIsTerminal B (Spec (.of R)) hS))
  letI : PreservesFiniteColimits (smallEtaleGlobalSections B (B.obj (Spec (.of R)) hS)) :=
    preservesFiniteColimits_of_natIso
      (Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B (Spec (.of R)) hS)
        AddCommGrpCat.{u + 1} (SmallEtale.finalIsTerminal B (Spec (.of R)) hS))
  letI := isIso_sectionsToEtaleStalk B R hS s hs
    ((higherDirectImage B R hS f n).obj F).obj
  (asIso (sectionsToEtaleStalk B R hS s ((higherDirectImage B R hS f n).obj F).obj)).symm ≪≫
    Stacks.DerivedFunctor.rightDerivedEvaluationIso
      (Stacks.HigherDirectImage.pushforward.{u, u + 1} B f)
      (smallEtaleGlobalSections B (B.obj (Spec (.of R)) hS)) F n ≪≫
    (Stacks.DerivedFunctor.rightDerivedIso
      (smallEtalePushforwardCompGlobalSectionsIso B f) n).app F

end HigherDirectImage

end Stacks.StrictlyHenselian

add_to_stacks 03Q9 "first assertion, for an abelian sheaf `F` on `X_étale`, `f : X → S` \
quasi-compact and quasi-separated over an arbitrary scheme `S` and an arbitrary geometric point \
`s` of `S`: `(R^n f_* F)_s = H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)`, with `R^n` Mathlib's \
right derived functors of direct image and of global sections on the small étale sites; the strict \
henselization is taken inside a big étale site `B` containing `S`"
  AlgebraicGeometry.stalkHigherDirectImageIso

end
