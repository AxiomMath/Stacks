module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the cohomology of a pullback of an injective module along a continuous functor

Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, so that `g⁻¹` is restriction along `u` (Sites, Lemma 00XR).
Stacks 0D6X asserts that for a sheaf of rings `O_D` on `D` and an injective `O_D`-module `I`,
`H^p(U, g⁻¹I) = 0` for all `p > 0` and every object `U` of `C`.

The source's proof has three steps:

1. since `u` is continuous, for a covering `𝒰 = {U_i → U}` of `C` the family
   `u(𝒰) = {u(U_i) → u(U)}` is a covering of `D` and
   `u(U_{i_0} ×_U … ×_U U_{i_n}) = u(U_{i_0}) ×_{u(U)} … ×_{u(U)} u(U_{i_n})`, so
   `Ȟ^p(𝒰, g⁻¹I) = Ȟ^p(u(𝒰), I)`;
2. the right-hand side vanishes for `p > 0` because `I` is injective (Stacks 03FC);
3. vanishing of higher Čech cohomology on all coverings gives vanishing of higher cohomology
   (Stacks 03F9).

The lemma `Stacks.CechSite.injective_module_subsingleton_ext_of_functor` carries out steps 2
and 3 for any system of coverings, but takes the identification of fibre products in step 1
(the invertibility of the comparison maps `Stacks.CechSite.cechProductMapOfFunctor`) as its
hypothesis `hComparison`. This file proves step 1 from continuity of `u`, and so states
Stacks 0D6X with no hypothesis beyond the source's.

## Continuity

A continuous functor of sites in the sense of Sites, Definition 00WV, (1) sends coverings to
coverings and (2) for every covering arrow `V_i ⟶ V` (whose fibre products along arbitrary
arrows `T ⟶ V` exist, a site in the sense of Sites, Definition 00VH, having them) and every
`T ⟶ V`, sends the fibre product `V_i ×_V T` to `u(V_i) ×_{u(V)} u(T)`. Mathlib's
`CategoryTheory.Functor.IsContinuous` records the consequence of (1) proved in Sites,
Lemma 00WW, that restriction along `u` preserves sheaves; clause (2) is
`Stacks.Sites.PreservesCoveringPullbacks`, which asks it on a cofinal system of covering
families of the topology. Both are implied by continuity in the sense of the source, so the
hypotheses below are at most the source's.

From clause (2), `Stacks.Sites.preservesLimit_fibreProducts_overPost` shows that `Over.post u`
preserves every iterated fibre product of such a covering family, and
`Stacks.CechSite.isIso_cechProductMapOfFunctor` turns that into invertibility of the comparison
maps: this is `Stacks.CechSite.isIso_cechProductMapOfFunctor_of_continuityCovering`.

## Main results

* `Stacks.CechSite.continuityCoverings`: the covering families of `C` whose arrows admit fibre
  products along every arrow and whose fibre products `u` preserves; under
  `Stacks.Sites.PreservesCoveringPullbacks` they are cofinal
  (`Stacks.CechSite.exists_continuityCovering_le`).
* `Stacks.CechSite.isIso_cechProductMapOfFunctor_of_continuityCovering`: step 1 of the source's
  proof — the Čech comparison maps along `u` of those coverings are isomorphisms.
* `Stacks.CechSite.injective_sheaf_subsingleton_ext_of_continuous_general`: Stacks 0D6X for an
  injective abelian sheaf, at general universes.
* `Stacks.CechSite.injective_module_subsingleton_ext_of_continuous`: **Stacks 0D6X**.

## Implementation notes

Cohomology over `U` is `Ext` out of the free abelian sheaf on the representable presheaf of `U`,
lifted to the coefficient universe, and the cohomology of a module is the cohomology of its
underlying abelian sheaf, as in the other forms of Stacks 0D6X; for modules the two agree by
Stacks 03FD.

Neither site is assumed small. The universes of the objects and morphisms of `C` and `D`, of the
sections of `O_D` and of `Ext` are independent; the coefficients lie in a universe containing
all of them (the free slack being `a`). That is the small-site convention of the source, in the
form needed by Stacks 03F9 and 03FC: the Čech-to-derived criterion needs enough injective abelian
sheaves on `C` at the coefficient universe, and the covering families extracted from the
topology are indexed by their own arrows, in `max u v`.

Cocontinuity of `u` is not used: it is what makes restriction along `u` the inverse image of a
morphism of topoi (Sites, Lemma 00XR), but the vanishing holds for restriction along any
continuous functor of sites, so the statements below are more general than the source's.

## References

* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

universe x a v u v₂ u₂ r

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

section Coverings

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (u : C ⥤ D)

/-- The covering families of `C` used in the proof of Stacks 0D6X: those whose arrows admit fibre
products along every arrow to the covered object, and whose fibre products `u` preserves. These
are the coverings to which clause (2) of the continuity of `u` (Sites, Definition 00WV)
applies. -/
def continuityCoverings (U : C) : Set { E : PreZeroHypercover.{max u v} U // E.sieve₀ ∈ J U } :=
  { E | (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (E.1.f j) g) u) }

variable {J u}

/-- The iterated fibre products of a covering family of `continuityCoverings` exist. -/
theorem hasProduct_of_continuityCovering {U : C}
    {E : { E : PreZeroHypercover.{max u v} U // E.sieve₀ ∈ J U }}
    (hE : E ∈ continuityCoverings J u U) (n : ℕ) (i : Fin (n + 1) → E.1.I₀) :
    HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
  Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 n i

/-- The iterated fibre products of the image under `u` of a covering family of
`continuityCoverings` exist: they are the images of the iterated fibre products of the
family. -/
theorem hasProduct_map_of_continuityCovering {U : C}
    {E : { E : PreZeroHypercover.{max u v} U // E.sieve₀ ∈ J U }}
    (hE : E ∈ continuityCoverings J u U) (n : ℕ) (i : Fin (n + 1) → (E.1.map u).I₀) :
    HasProduct (fun b ↦ Over.mk ((E.1.map u).f (i b))) := by
  have := hasProduct_of_continuityCovering hE n i
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 n i
  have : HasLimit (Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post u) :=
    HasLimit.mk ⟨_, isLimitOfPreserves (Over.post u) (limit.isLimit _)⟩
  exact hasLimit_of_iso
    (F := Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post u)
    (G := Discrete.functor (fun b ↦ Over.mk ((E.1.map u).f (i b))))
    (Discrete.natIso fun _ => Iso.refl _)

/-- **Step 1 of the proof of Stacks 0D6X.** For a covering family `{U_i → U}` of
`continuityCoverings`, the comparison maps
`u(U_{i_0} ×_U … ×_U U_{i_n}) ⟶ u(U_{i_0}) ×_{u(U)} … ×_{u(U)} u(U_{i_n})` are isomorphisms. -/
theorem isIso_cechProductMapOfFunctor_of_continuityCovering {U : C}
    {E : { E : PreZeroHypercover.{max u v} U // E.sieve₀ ∈ J U }}
    (hE : E ∈ continuityCoverings J u U) (n : ℕ) (i : Fin (n + 1) → E.1.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
      HasProduct (fun b ↦ Over.mk (E.1.f (j b))) := hasProduct_of_continuityCovering hE
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
      HasProduct (fun b ↦ Over.mk ((E.1.map u).f (j b))) :=
      hasProduct_map_of_continuityCovering hE
    IsIso (cechProductMapOfFunctor u E.1 n i) := by
  have := hasProduct_of_continuityCovering hE
  have := hasProduct_map_of_continuityCovering hE
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 n i
  exact isIso_cechProductMapOfFunctor u E.1 n i

variable (J u) in
/-- Under the covering-pullback clause of continuity, the families of `continuityCoverings` are
cofinal among the coverings of every object. -/
theorem exists_continuityCovering_le [Stacks.Sites.PreservesCoveringPullbacks J u]
    (U : C) (R : Sieve U) (hR : R ∈ J U) :
    ∃ E : { E : PreZeroHypercover.{max u v} U // E.sieve₀ ∈ J U },
      E ∈ continuityCoverings J u U ∧ E.1.sieve₀ ≤ R := by
  obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u R hR
  exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩

end Coverings

section Abelian

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂})]
  (u : C ⥤ D) [u.IsContinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J u]

/-- **Stacks 0D6X for an injective abelian sheaf, at general universes.** Let `u : C ⥤ D` be a
continuous functor of sites. If `I` is an injective abelian sheaf on `D` then
`H^p(U, u^p I) = 0` for every `p > 0` and every object `U` of `C`, cohomology over `U` being
`Ext` out of the free abelian sheaf on the (lifted) representable presheaf of `U`.

This is the case `O_D = ℤ` of Stacks 0D6X, stated separately because an injective object of
`Ab(D)` is not, in the formalization, an injective module over the constant sheaf of rings `ℤ`.
Neither site is assumed small. -/
theorem injective_sheaf_subsingleton_ext_of_continuous_general
    (I : Sheaf K AddCommGrpCat.{max a u v u₂ v₂}) [Injective I]
    (U : C) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂}).obj
      (uliftYoneda.{max a u v u₂ v₂}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂} J K).obj I) p) :=
  injective_sheaf_subsingleton_ext_of_functor.{x, a} J K u Set.univ
    (continuityCoverings J u) (fun _ hE ↦ hasProduct_of_continuityCovering hE)
    (fun _ hE ↦ hasProduct_map_of_continuityCovering hE)
    (fun _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _, fun _ _ ↦ Set.mem_univ _⟩)
    (fun V _ R hR ↦ exists_continuityCovering_le J u V R hR)
    (fun _ hE n i ↦ isIso_cechProductMapOfFunctor_of_continuityCovering hE n i)
    I U (Set.mem_univ _) p hp

end Abelian

section Modules

variable {C : Type u} [Category.{v} C] (Y : AlgebraicGeometry.RingedSite.{u₂, v₂, r})
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max a u v u₂ v₂ r}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max a u v u₂ v₂ r})]
  (u : C ⥤ Y.C) [u.IsContinuous J Y.J] [Stacks.Sites.PreservesCoveringPullbacks J u]

/-- **Stacks Project, Tag 0D6X.** Let `u : C ⥤ D` be a continuous functor of sites and let
`g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g⁻¹` is restriction along
`u` (Sites, Lemma 00XR). Let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. Then `H^p(U, g⁻¹I) = 0` for all `p > 0` and all objects `U` of `C`.

Continuity of `u` (Sites, Definition 00WV) is `CategoryTheory.Functor.IsContinuous` together
with its covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks`, and the
identification of Čech complexes `Ȟ^p(𝒰, g⁻¹I) = Ȟ^p(u(𝒰), I)` of the source's proof is
derived from it, by `isIso_cechProductMapOfFunctor_of_continuityCovering`. Cohomology over `U`
is `Ext` out of the free abelian sheaf on the (lifted) representable presheaf of `U`, and the
cohomology of a module is that of its underlying abelian sheaf. Cocontinuity of `u`, which
makes `g` a morphism of topoi, is not needed. Neither site is assumed small; the universes of
the two sites, of the sections of `O_D` and of `Ext` are free. -/
@[stacks 0D6X "the Čech comparison derived from continuity; cocontinuity is not needed, neither \
site is small, and cohomology over `U` is `Ext` out of the free abelian sheaf on the lifted \
representable"]
theorem injective_module_subsingleton_ext_of_continuous
    (I : SheafOfModules.{max a u v u₂ v₂ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [Injective I] (U : C) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{max a u v u₂ v₂ r}).obj
      (uliftYoneda.{max a u v u₂ v₂ r}.obj U ⋙ AddCommGrpCat.free))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max a u v u₂ v₂ r} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) p) :=
  injective_module_subsingleton_ext_of_functor.{x, a} Y J u Set.univ
    (continuityCoverings J u) (fun _ hE ↦ hasProduct_of_continuityCovering hE)
    (fun _ hE ↦ hasProduct_map_of_continuityCovering hE)
    (fun _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _, fun _ _ ↦ Set.mem_univ _⟩)
    (fun V _ R hR ↦ exists_continuityCovering_le J u V R hR)
    (fun _ hE n i ↦ isIso_cechProductMapOfFunctor_of_continuityCovering hE n i)
    I U (Set.mem_univ _) p hp

end Modules

end Stacks.CechSite
