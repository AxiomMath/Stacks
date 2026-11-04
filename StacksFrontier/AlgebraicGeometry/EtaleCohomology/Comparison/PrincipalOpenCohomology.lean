module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of an étale sheaf on a principal open

Let `R` be a ring and let `B` be a big étale site containing `Spec R` and all of its principal
opens `D(f)`. Each `D(f)` is then an object of the small étale site of `Spec R`, and it is
*subterminal* there: there is at most one morphism from any étale `Spec R`-scheme into it,
because `D(f) ⟶ Spec R` is a monomorphism.

Subterminality is what makes cohomology over `D(f)` expressible with coefficients in a sheaf
of any size. Mathlib's `Sheaf.H` fixes the coefficient universe to that of the site's
morphisms, because it uses the free abelian sheaf on a representable presheaf; here the
representable presheaf of `D(f)` has subsingleton values, so it can be shrunk to any universe
and the same `Ext` construction applies. The resulting groups `principalOpenCohomology` and
their restriction maps `principalOpenCohomologyMap` are the ones appearing in Gabber's
vanishing criterion, Stacks 0GY0.

## Main definitions

* `Stacks.GabberCriterion.principalOpen` — `D(f)` as an object of the small étale site.
* `Stacks.GabberCriterion.principalOpenHom` — the morphism induced by `D(a) ⊆ D(b)`.
* `Stacks.GabberCriterion.principalOpenPresheaf` — its representable presheaf, shrunk to the
  coefficient universe, together with `principalOpenPresheafRepresentableBy` identifying what
  it represents.
* `Stacks.GabberCriterion.principalOpenFreeAbelianSheaf` and
  `Stacks.GabberCriterion.principalOpenFreeAbelianSheafMap` — the free abelian sheaf on that
  presheaf and its functoriality.
* `Stacks.GabberCriterion.principalOpenCohomology` and
  `Stacks.GabberCriterion.principalOpenCohomologyMap` — cohomology over `D(f)` and its
  restriction maps.

## Main results

* `Stacks.GabberCriterion.subsingleton_hom_principalOpen` — a principal open is subterminal in
  the small étale site.

## References

* [Stacks Project, Tag 0GY0](https://stacks.math.columbia.edu/tag/0GY0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u v w

namespace Stacks.GabberCriterion

variable {R : Type u} [CommRing R]

/-- The principal open `D(f)` as an object of a chosen small étale site of `Spec R`: an open
immersion is étale. -/
public def principalOpen
    (B : BigEtaleSite.{u})
    (hSpec : B.Contains (Spec (.of R)))
    (hD : ∀ f : R,
      B.Contains (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen f)))
    (f : R) : SmallEtale B (Spec (.of R)) hSpec := by
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen f
  refine ⟨Over.mk (X := B.obj (Spec (.of R)) hSpec)
    (Y := B.obj U.toScheme (hD f)) (ObjectProperty.homMk U.ι), ?_⟩
  change Etale U.ι
  infer_instance

/-- An inclusion `D(a) ⊆ D(b)` induces the corresponding morphism in the small étale site of
`Spec R`. -/
public def principalOpenHom
    (B : BigEtaleSite.{u})
    (hSpec : B.Contains (Spec (.of R)))
    (hD : ∀ f : R,
      B.Contains (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen f)))
    {a b : R} (hab : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b) :
    principalOpen B hSpec hD a ⟶ principalOpen B hSpec hD b := by
  refine ObjectProperty.homMk <| Over.homMk
    (ObjectProperty.homMk ((Spec (.of R)).homOfLE hab)) ?_
  apply ObjectProperty.hom_ext
  exact Scheme.homOfLE_ι _ hab

section Cohomology

variable (B : BigEtaleSite.{u})
    (hSpec : B.Contains (Spec (.of R)))
    (hD : ∀ f : R,
      B.Contains (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen f)))

/-- A principal open is subterminal in the small étale site: there is at most one morphism
into it, because `D(f) ⟶ Spec R` is a monomorphism. -/
public instance subsingleton_hom_principalOpen (f : R)
    (Y : SmallEtale B (Spec (.of R)) hSpec) :
    Subsingleton (Y ⟶ principalOpen B hSpec hD f) := by
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen f
  refine ⟨fun a b ↦ ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply (cancel_mono U.ι).1
  exact (congrArg B.inclusion.map (Over.w a.hom)).trans
    (congrArg B.inclusion.map (Over.w b.hom)).symm

/-- The representable presheaf of a principal open is small in every universe, since its
values are subsingletons. -/
public instance small_yoneda_principalOpen (f : R) :
    FunctorToTypes.Small.{v} (yoneda.obj (principalOpen B hSpec hD f)) :=
  fun _ ↦ inferInstanceAs (Small (_ ⟶ principalOpen B hSpec hD f))

/-- The representable presheaf of `D(f)`, shrunk to the coefficient universe. -/
public def principalOpenPresheaf (f : R) :
    (SmallEtale B (Spec (.of R)) hSpec)ᵒᵖ ⥤ Type v :=
  FunctorToTypes.shrink (yoneda.obj (principalOpen B hSpec hD f))

/-- Shrinking does not change the object represented by the principal-open presheaf. -/
public def principalOpenPresheafRepresentableBy (f : R) :
    (principalOpenPresheaf.{u, v} B hSpec hD f).RepresentableBy
      (principalOpen B hSpec hD f) where
  homEquiv := equivShrink.{v} _
  homEquiv_comp a b := by
    change equivShrink.{v} _ (a ≫ b) =
      equivShrink.{v} _ (a ≫ (equivShrink.{v} _).symm (equivShrink.{v} _ b))
    rw [Equiv.symm_apply_apply]

variable [HasSheafify (SmallEtale.topology B (Spec (.of R)) hSpec) AddCommGrpCat.{v}]

/-- The free abelian sheaf represented by a principal open. -/
@[sga "4 XVIII 1.4.24" "(F), special case"]
public def principalOpenFreeAbelianSheaf (f : R) :
    Sheaf (SmallEtale.topology B (Spec (.of R)) hSpec) AddCommGrpCat.{v} :=
  (presheafToSheaf _ _).obj (principalOpenPresheaf B hSpec hD f ⋙ AddCommGrpCat.free)

/-- An inclusion of principal opens induces a map of their free abelian sheaves. -/
public def principalOpenFreeAbelianSheafMap {a b : R}
    (hab : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b) :
    principalOpenFreeAbelianSheaf.{u, v} B hSpec hD a ⟶
      principalOpenFreeAbelianSheaf.{u, v} B hSpec hD b :=
  (presheafToSheaf _ _).map (Functor.whiskerRight
    (FunctorToTypes.shrinkMap (yoneda.map (principalOpenHom B hSpec hD hab)))
    AddCommGrpCat.free)

variable [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of R)) hSpec)
    AddCommGrpCat.{v})]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hSpec) AddCommGrpCat.{v})

/-- Cohomology over a principal open, with coefficients in an independently sized abelian
sheaf. -/
public abbrev principalOpenCohomology (q : ℕ) (f : R) : AddCommGrpCat.{w} :=
  ((extFunctor q).obj (op (principalOpenFreeAbelianSheaf B hSpec hD f))).obj F

/-- Restriction of cohomology along an inclusion of principal opens. -/
public def principalOpenCohomologyMap (q : ℕ) {a b : R}
    (hab : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b) :
    principalOpenCohomology B hSpec hD F q b ⟶
      principalOpenCohomology B hSpec hD F q a :=
  ((extFunctor q).map (principalOpenFreeAbelianSheafMap B hSpec hD hab).op).app F

end Cohomology

end Stacks.GabberCriterion
