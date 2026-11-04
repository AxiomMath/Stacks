module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveModuleVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the cohomology of a pullback of an injective sheaf along a functor of sites

Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, so that `g⁻¹` is restriction along `u` — this is Sites, Lemma
00XR, which also needs `u` cocontinuous; the statements below are about restriction along `u`
itself and so do not use cocontinuity. Stacks 0D6X asserts that for an injective module `I` on
`D` the pullback `g⁻¹I` has no higher cohomology on any object of `C`.

The proof is the one in the source. For a covering `𝒰 = {U_i → U}` of `C` the image
`u(𝒰) = {u(U_i) → u(U)}` is a covering of `D`, and when `u` preserves the iterated fibre
products of `𝒰` — condition (2) of the definition of a continuous functor of sites, Sites,
Definition 00WV — the two Čech complexes agree, so
`Ȟ^p(𝒰, g⁻¹I) = Ȟ^p(u(𝒰), I)`; this is
`Stacks.CechSite.cechCohomology_isZero_of_isZero_of_functor`. The right-hand side vanishes in
positive degrees because `I` is injective: by Stacks 03FC for a module over a sheaf of rings,
and by Stacks 03AW for an abelian sheaf. Vanishing of the higher Čech cohomology on a cofinal
system of coverings gives vanishing of the higher sheaf cohomology, by Stacks 03F9.

## Main results

* `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives`:
  the transfer along `u` of the Čech-vanishing criterion of Stacks 03F9 — higher sheaf
  cohomology of a restriction vanishes as soon as the higher Čech cohomology of the *image*
  coverings does.
* `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`: the same
  criterion for a source site small in the coefficient universe, which is what supplies the
  homological inputs the previous one takes as hypotheses.
* `Stacks.CechSite.injective_sheaf_sheafCohomology_isZero_of_functor`: the case of an
  injective abelian sheaf, that is, of the structure sheaf `ℤ`.
* `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`: **Stacks 0D6X**, for an
  injective module over an arbitrary sheaf of rings on `D`.

## Implementation notes

The hypotheses on the system of coverings are those of Stacks 03F9,
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero`: a collection `B` of objects
and, for each object, a collection `Cov` of coverings whose iterated fibre products exist and
lie in `B`, cofinal on the objects of `B`. Two hypotheses are added, both of them the content
of condition (2) of Sites, Definition 00WV for the selected coverings: the iterated fibre
products of each image covering exist in `D`, and the comparison maps to them from the images
of the iterated fibre products in `C` are invertible. Nothing is assumed about coverings
outside `Cov`, so `u` is not required to be continuous in the sense of Sites, Definition 00WV
— only Mathlib's `CategoryTheory.Functor.IsContinuous`, which is the conclusion of Sites,
Lemma 00WW, in order for restriction along `u` to land in sheaves at all.

The coefficient universe contains the object and morphism universes of `D`, the morphism
universe of `C` and the covering-index universe, which is the small-site convention of the
source: it is forced by Stacks 03F9 and by Stacks 03AW, each of which needs enough injective
abelian sheaves at the coefficient universe. The object universe of `C` and the universe of
`Ext` remain independent.

## References

* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

universe a w v v₂ u u₂ x

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

section

variable {C : Type u} [Category.{max v w} C]
  {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max v w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks 03F9 transported along a functor of sites, without a smallness assumption on
the source site.** This is `sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` resting
on `sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives` instead of on
`sheafCohomology_isZero_of_cechCohomology_isZero`: the homological inputs that smallness of `C`
would supply are hypotheses here. The small étale site of a scheme needs this form, being not
essentially small at the morphism universe of the site. -/
theorem sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (F : Sheaf K AddCommGrpCat.{max v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsZero (cechCohomology (E.1.map u) F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} J K).obj F)
      p U) := by
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives J B Cov
    hProducts hCovObjects hCovCofinal
    ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} J K).obj F) ?_ U hU p hp
  intro V E hE q hq
  let := hProducts E hE
  let := hImageProducts E hE
  exact cechCohomology_isZero_of_isZero_of_functor u E.1 F.obj
    (fun n i ↦ hComparison E hE n i) q (hCech E hE q hq)

end

section

variable {C : Type u} [Category.{max v w} C] [Small.{max v w} C]
  {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max v w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks 03F9 transported along a functor of sites.** If the higher Čech cohomology of a
sheaf `F` on `D` vanishes on the image of every covering in a cofinal system of coverings of
`C`, and `u` preserves the iterated fibre products of those coverings, then the higher sheaf
cohomology of the restriction of `F` along `u` vanishes on every object of the system. -/
theorem sheafCohomology_isZero_of_cechCohomology_isZero_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (F : Sheaf K AddCommGrpCat.{max v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsZero (cechCohomology (E.1.map u) F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} J K).obj F)
      p U) := by
  let : IsGrothendieckAbelian.{max v w} (Sheaf J AddCommGrpCat.{max v w}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max v w} J AddCommGrpCat.{max v w}
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max v w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  exact sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives J K u B
    Cov hProducts hImageProducts hCovObjects hCovCofinal hComparison F hCech U hU p hp

end

section

variable {C : Type u} [Category.{max a u₂ v₂ w} C] [Small.{max a u₂ v₂ w} C]
  {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max a u₂ v₂ w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u₂ v₂ w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X.** Let `u : C ⥤ D` be a continuous functor of sites and let
`g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g⁻¹` is restriction along
`u` by Sites, Lemma 00XR. If `I` is an injective abelian sheaf on `D` then `H^p(U, g⁻¹I) = 0`
for all `p > 0` and every object `U` of the cofinal system of coverings, in particular for
every object of `C` when the system is cofinal everywhere. This is the case `O_D = ℤ` of
Stacks 0D6X, which is proved for an arbitrary structure sheaf in
`Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`; it is stated separately
because an injective object of `Ab(D)` is not, in the formalization, an injective module over
the constant sheaf of rings `ℤ`. -/
theorem injective_sheaf_sheafCohomology_isZero_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : Sheaf K AddCommGrpCat.{max a u₂ v₂ w}) [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u₂ v₂ w} J K).obj I)
      p U) :=
  sheafCohomology_isZero_of_cechCohomology_isZero_of_functor J K u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison I
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_sheaf_cechCohomology_isZero.{a} (E.1.map u) I q hq)
    U hU p hp

end

section Modules

universe r

variable {C : Type u} [Category.{max a u₂ v₂ r w} C] [Small.{max a u₂ v₂ r w} C]
  (Y : AlgebraicGeometry.RingedSite.{u₂, v₂, r})
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u₂ v₂ r w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u₂ v₂ r w})]
  (u : C ⥤ Y.C) [u.IsContinuous J Y.J]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X.** Let `u : C ⥤ D` be a continuous functor of sites and let
`g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g⁻¹` is restriction along
`u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. Then `H^p(U, g⁻¹I) = 0` for all `p > 0` and every object `U` of the cofinal
system of coverings, in particular for every object of `C` when the system is cofinal
everywhere. As in the source, the cohomology of a module is that of its underlying abelian
sheaf. -/
@[stacks 0D6X]
theorem injective_module_sheafCohomology_isZero_of_functor
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : SheafOfModules.{max a u₂ v₂ r w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u₂ v₂ r w} J Y.J).obj
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) p U) :=
  sheafCohomology_isZero_of_cechCohomology_isZero_of_functor J Y.J u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison
    ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_moduleCechCohomology_isZero.{a, w, u₂, v₂, r} Y (E.1.map u) I q hq)
    U hU p hp

end Modules

/-! ### Coefficients in a sheaf of rings, not assumed commutative

The same vanishing for an arbitrary site `(D, K)` with a sheaf of rings `O : Sheaf K RingCat`,
not assumed commutative; a ringed site is the case
`O = Stacks.SheafOfModules.Tensor.ringSheaf Y.O`. -/

section ModulesSheafOfRings

universe r

variable {C : Type u} [Category.{max a u₂ v₂ r w} C] [Small.{max a u₂ v₂ r w} C]
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (O : Sheaf K RingCat.{r})
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u₂ v₂ r w}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u₂ v₂ r w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  (B : Set C)
  (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
  (hProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
  (hImageProducts : ∀ {U : C}
    (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
    E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))))

/-- **Stacks Project, Tag 0D6X.** Let `u : C ⥤ D` be a continuous functor of sites and let
`g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g⁻¹` is restriction along
`u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. Then `H^p(U, g⁻¹I) = 0` for all `p > 0` and every object `U` of the cofinal
system of coverings, in particular for every object of `C` when the system is cofinal
everywhere. As in the source, the cohomology of a module is that of its underlying abelian
sheaf. -/
@[stacks 0D6X]
theorem injective_module_sheafCohomology_isZero_of_functor_sheafOfRings
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (hComparison : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
        IsIso (cechProductMapOfFunctor u E.1 p i))
    (I : SheafOfModules.{max a u₂ v₂ r w} O) [Injective I]
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u₂ v₂ r w} J K).obj
      ((SheafOfModules.toSheaf O).obj I)) p U) :=
  sheafCohomology_isZero_of_cechCohomology_isZero_of_functor J K u B Cov hProducts
    hImageProducts hCovObjects hCovCofinal hComparison
    ((SheafOfModules.toSheaf O).obj I)
    (fun E hE q hq ↦
      let := hImageProducts E hE
      injective_moduleCechCohomology_isZero_sheafOfRings.{a, w, u₂, v₂, r} K O (E.1.map u) I q hq)
    U hU p hp

end ModulesSheafOfRings

end Stacks.CechSite
