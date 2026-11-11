module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSiteUnivLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FinitePushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite direct images of sheaves of `Λ`-modules are acyclic, and Stacks 0GJD

Let `Λ` be a ring and let `f : X ⟶ Y` be a morphism of a big étale site whose underlying morphism
of schemes is finite. This file proves that the direct image of sheaves of `Λ`-modules along `f`
on the small étale sites of Stacks 021B is exact, so that `R^q f_*ℱ = 0` for `q > 0` (part (2) of
Stacks 03QP for sheaves of `Λ`-modules), and deduces **Stacks 0GJD**: if `H^q_étale(X, ℱ)` is a
finite `Λ`-module, then so is `H^q_étale(Y, f_*ℱ)`, with no hypothesis beyond the finiteness of
`f`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.modulePushforward_exact_of_isIntegralHom` — for `f`
  with integral underlying morphism of schemes, the direct image of sheaves of `Λ`-modules is an
  exact functor (Stacks 04C2 for sheaves of `Λ`-modules on the sites of Stacks 021B).
* `Stacks.EtaleCohomology.TorsionModules.isZero_rightDerived_modulePushforward_of_isIntegralHom`
  — the vanishing `R^q f_*ℱ = 0` for `q > 0` (Stacks 03QP, part (2)).
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_pushforward_of_isFinite` —
  **Stacks 0GJD**.

## Implementation notes

**Coefficient universe.** Sheaves of `Λ`-modules, for `Λ : Type r`, are taken with values in
`ModuleCat.{max (u + 1) w r} Λ`, `u` being the universe of the schemes of the big étale site. At
this universe the small étale sites are essentially small and `Λ` embeds in the coefficient
universe, so every piece of infrastructure the statement needs is a theorem, not a hypothesis:
sheafification is `AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf`, the sheaf categories are
Grothendieck abelian by `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_moduleSheaf`, hence
have enough injectives and injective resolutions, which is what makes the right derived functors
computing `H^q` exist.

**The vanishing.** A morphism of sheaves of modules is an epimorphism exactly when it is locally
surjective, local surjectivity is a property of the underlying morphism of sheaves of sets, and
the underlying sheaf of sets of a direct image is the direct image of the underlying sheaf of
sets; so preservation of epimorphisms is
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms_of_univLE`
(Stacks 04C2, part (1)). With left exactness this makes the direct image exact, and exact functors
have no higher right derived functors.

**The collapse.** The comparison `H^q_étale(X, ℱ) ≅ H^q_étale(Y, f_*ℱ)` given the vanishing is
`Stacks.EtaleCohomology.TorsionModules.moduleCohomologyPushforwardIso` (Stacks 0733, part (1),
for sheaves of `Λ`-modules on these sites).

## References

* [Stacks Project, Tag 0GJD](https://stacks.math.columbia.edu/tag/0GJD)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology.TorsionModules

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- On the small étale site of Stacks 021B, sheafification of presheaves of `Λ`-modules with
values in `ModuleCat.{max (u + 1) w r} Λ` inverts exactly the locally bijective morphisms;
equivalently, a morphism of sheaves of `Λ`-modules is an epimorphism exactly when it is locally
surjective. Transported from a small model of the site, where it is
`Stacks.EtaleCohomology.wEqualsLocallyBijective_moduleCat_smallSite`. -/
instance wEqualsLocallyBijective_smallEtaleModuleCat (Z : B.Scheme) :
    (SmallEtale.topology B Z.obj Z.property).WEqualsLocallyBijective
      (ModuleCat.{max (u + 1) w r} Λ) := by
  have : ((equivSmallModel.{max (u + 1) w r}
      (SmallEtale B Z.obj Z.property)).inverse.inducedTopology
        (SmallEtale.topology B Z.obj Z.property)).WEqualsLocallyBijective
      (ModuleCat.{max (u + 1) w r} Λ) :=
    Stacks.EtaleCohomology.wEqualsLocallyBijective_moduleCat_smallSite Λ
      (D := SmallModel.{max (u + 1) w r} (SmallEtale B Z.obj Z.property)) _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _,
    max (u + 1) w r} (SmallEtale.topology B Z.obj Z.property)

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- For `f` with integral underlying morphism of schemes, the direct image of sheaves of
`Λ`-modules along `f` carries surjections to surjections.

A morphism of sheaves of modules is an epimorphism exactly when it is locally surjective, and
local surjectivity is a property of the underlying morphism of sheaves of sets. Since the
underlying sheaf of sets of a direct image is the direct image of the underlying sheaf of sets,
the statement reduces to
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms_of_univLE`. -/
theorem modulePushforward_preservesEpimorphisms_of_isIntegralHom
    [IsIntegralHom (B.inclusion.map f)] :
    (modulePushforward.{u, max w r} B Λ f).PreservesEpimorphisms := by
  have hset :
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (Type (max (u + 1) w r)) (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).PreservesEpimorphisms :=
    SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms_of_univLE.{u,
      max (u + 1) w r} B f
  constructor
  intro F G φ hφ
  have hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max (u + 1) w r} Λ) φ).2 hφ
  have hset' : Epi (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (Type (max (u + 1) w r)) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).map
      ((sheafCompose (SmallEtale.topology B X.obj X.property)
        (CategoryTheory.forget (ModuleCat.{max (u + 1) w r} Λ))).map φ)) := hset.preserves _
  have hforget : Epi ((sheafCompose (SmallEtale.topology B Y.obj Y.property)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) w r} Λ))).map
      ((modulePushforward.{u, max w r} B Λ f).map φ)) := hset'
  have hlocforget : Sheaf.IsLocallySurjective
      ((sheafCompose (SmallEtale.topology B Y.obj Y.property)
        (CategoryTheory.forget (ModuleCat.{max (u + 1) w r} Λ))).map
        ((modulePushforward.{u, max w r} B Λ f).map φ)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hforget
  have : Sheaf.IsLocallySurjective ((modulePushforward.{u, max w r} B Λ f).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (SmallEtale.topology B Y.obj Y.property) _).2 hlocforget
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Stacks 04C2, for sheaves of `Λ`-modules on the small étale sites of Stacks 021B.** For `f`
with integral underlying morphism of schemes, the direct image of sheaves of `Λ`-modules along
`f` is an exact functor: it is left exact as a right adjoint, it preserves epimorphisms by
`modulePushforward_preservesEpimorphisms_of_isIntegralHom`, and an additive functor between
abelian categories preserving kernels and epimorphisms preserves homology, hence finite colimits
as well. -/
theorem modulePushforward_exact_of_isIntegralHom [IsIntegralHom (B.inclusion.map f)] :
    exactFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w r} Λ))
      (Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w r} Λ))
      (modulePushforward.{u, max w r} B Λ f) := by
  have hepi := modulePushforward_preservesEpimorphisms_of_isIntegralHom.{u, w, r} B Λ f
  have hhom := Functor.preservesHomology_of_preservesEpis_and_kernels
    (modulePushforward.{u, max w r} B Λ f)
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- **Stacks 03QP, part (2), for sheaves of `Λ`-modules on the small étale sites of Stacks
021B.** For `f` with integral underlying morphism of schemes — a finite morphism, for instance —
the higher direct images of a sheaf of `Λ`-modules along `f` vanish: `R^q f_*ℱ = 0` for every
`q > 0`. The direct image is exact by `modulePushforward_exact_of_isIntegralHom`, and the higher
right derived functors of an exact functor vanish. -/
@[stacks 03QP "part (2), for sheaves of Λ-modules on the small étale sites of Tag 021B",
  sga "4 VIII 5.5" "more general",
  sga "4 VIII 5.6" "more general",
  sga "4 Vbis 4.3.4" "more general",
  sga "4 XIV 1.11" "partial",
  sga "4½ Arcata 2.3.6" "more general"]
theorem isZero_rightDerived_modulePushforward_of_isIntegralHom
    [IsIntegralHom (B.inclusion.map f)]
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w r} Λ))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((modulePushforward.{u, max w r} B Λ f).rightDerived q).obj ℱ) :=
  Functor.isZero_rightDerived_of_exactFunctor _
    (modulePushforward_exact_of_isIntegralHom.{u, w, r} B Λ f) ℱ q hq

/-- **Stacks Project, Tag 0GJD.** Let `Λ` be a ring, let `f : X ⟶ Y` be a morphism of a big étale
site whose underlying morphism of schemes is finite, and let `ℱ` be a sheaf of `Λ`-modules on the
small étale site of `X`. If `H^q_étale(X, ℱ)` is a finite `Λ`-module, then so is
`H^q_étale(Y, f_*ℱ)`.

The source states this for `Λ` Noetherian, `k` an algebraically closed field and `f` a finite
morphism of separated schemes of finite type over `k` of dimension at most one. None of that is
used by the source's proof, and none of it is assumed here: the source's statement is the special
case in which those hypotheses hold. The proof is the source's: the higher direct images
of `f` vanish (`isZero_rightDerived_modulePushforward_of_isIntegralHom`, Stacks 03QP), so the
Leray spectral sequence collapses to `H^q_étale(X, ℱ) ≅ H^q_étale(Y, f_*ℱ)`
(`moduleCohomologyPushforwardIso`, Stacks 0733), and finiteness transports along it. -/
@[stacks 0GJD "stated for an arbitrary ring Λ and an arbitrary finite morphism f of the big étale \
  site, for sheaves of Λ-modules on the small étale sites of Tag 021B; the source's further \
  hypotheses (Λ Noetherian, k algebraically closed, X and Y separated of finite type over k of \
  dimension at most one) are unused by its proof and dropped"]
theorem module_finite_cohomology_pushforward_of_isFinite [IsFinite (B.inclusion.map f)]
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w r} Λ))
    (q : ℕ)
    (hfin : Module.Finite Λ
      (((moduleGlobalSections.{u, max w r} B Λ X).rightDerived q).obj ℱ)) :
    Module.Finite Λ (((moduleGlobalSections.{u, max w r} B Λ Y).rightDerived q).obj
      ((modulePushforward.{u, max w r} B Λ f).obj ℱ)) :=
  Module.Finite.equiv
    (moduleCohomologyPushforwardIso.{u, max w r} B Λ f ℱ
      (isZero_rightDerived_modulePushforward_of_isIntegralHom.{u, w, r} B Λ f ℱ) q).toLinearEquiv

end Stacks.EtaleCohomology.TorsionModules

end
