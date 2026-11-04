module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# Restricting a linear system to an open subscheme

`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, clause
(5) of [Stacks, Tag 0FCY], takes a `k`-linear map `ψ : V → Γ(X, ℒ)` whose values generate `ℒ`
*everywhere*: it asks `⨆ v, X_{ψ(v)} = ⊤`. A linear system that does not generate everywhere
defines the morphism only over the open

`W = ⨆ v, X_{ψ(v)}`,

and to apply Tag 0FCY there one needs the restriction of the system to `W` — as a `k`-linear map
into `Γ(W, ℒ|_W)` whose nonvanishing opens cover `W`. This file supplies that restriction for an
arbitrary morphism of schemes over `Spec k`.

## Main definitions

* `Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ`: the pullback of global
  sections along a morphism of schemes over `Spec k`, as a `k`-linear map.

## Main results

* `Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.appTop_baseRingHom`: **a constant pulls
  back to the constant**, for a morphism over `Spec k`.
* `Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackGlobalSections_smul_scalar`:
  **pulling a global section back is `k`-linear**, the `k`-action on both sides being
  `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule`.
* `Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections`:
  **[Stacks, Tag 0H78] in the `AlgebraicGeometry.pullbackGlobalSections` spelling**: the
  nonvanishing open of a pulled-back global section is the preimage of the nonvanishing open.
* `…GeneratingSectionsRestrict.iSup_nonvanishingOpen_pullbackGlobalSections_eq_top`: **the
  nonvanishing opens of a restricted system cover the open it is restricted to**, which is the
  hypothesis of Tag 0FCY read over `W`.

## Implementation notes

**Three spellings of the pullback of a global section, and why the middle one is used.** The
inverse image of a sheaf of modules on a scheme is written both as
`AlgebraicGeometry.Scheme.Modules.pullback` and as `RingedSpaceModuleAdjunction.modulePullback`
of the underlying morphism of ringed spaces; the two are the *same* functor, by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`, but only the
first has type `S'.Modules`, and that is what instance search needs in order to find the
`k`-action
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule` on `Γ(-, ⊤)`:
at the second spelling the ring of the module is `(structureRingSheaf S').obj.obj (op ⊤)` and
`r • x` for `r : k` does not elaborate at all. So the pullback of a section is taken as
`AlgebraicGeometry.pullbackGlobalSections`, which lands at the first spelling. Tag 0H78 is proved
at the second, as `Stacks.NonvanishingPullback.pullbackGlobalSection`; the two sections differ by
a restriction along `⊤ ≤ i⁻¹⊤`, which is the identity because the category of opens is thin, so
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit` and `rfl` identify them.

**The structure morphism of the source is a hypothesis, not an instance.** `k`-linearity holds
only when the source is a scheme over `Spec k` *through* the morphism, so the compatibility
`i ≫ (S ↘ Spec k) = S' ↘ Spec k` is carried explicitly. In the intended application the source is
an open subscheme `W` of `S` and the instance is chosen as `⟨W.ι ≫ (S ↘ Spec k)⟩`, which makes
the hypothesis `rfl`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (isInvertibleModule_schemeModulesPullback)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom globalSectionsModule)

universe u

namespace Stacks.AlgebraicGeometry.GeneratingSectionsRestrict

/-! ### Tag 0H78 at the `pullbackGlobalSections` spelling -/

section Nonvanishing

variable {S S' : Scheme.{u}} (i : S' ⟶ S) (M : S.Modules)

/-- **The two spellings of the pullback of a global section agree.**
`AlgebraicGeometry.pullbackGlobalSections` interposes the restriction along `⊤ ≤ i⁻¹⊤` that
`Stacks.NonvanishingPullback.pullbackGlobalSection` does not; the two opens are equal and the
category of opens is thin, so that restriction is the identity. -/
theorem pullbackGlobalSections_eq_pullbackGlobalSection (s : Γ(M, ⊤)) :
    pullbackGlobalSections i M s = Stacks.NonvanishingPullback.pullbackGlobalSection i M s := by
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit]
  rfl

/-- **[Stacks, Tag 0H78] in the `AlgebraicGeometry.pullbackGlobalSections` spelling**: the
nonvanishing open of the pullback of a global section is the preimage of its nonvanishing
open. -/
theorem nonvanishingOpen_pullbackGlobalSections [IsInvertibleModule S M] (s : Γ(M, ⊤)) :
    nonvanishingOpen S' ((Scheme.Modules.pullback i).obj M) (pullbackGlobalSections i M s) =
      i ⁻¹ᵁ nonvanishingOpen S M s := by
  rw [pullbackGlobalSections_eq_pullbackGlobalSection]
  exact (Opens.ext (Stacks.NonvanishingPullback.preimage_nonvanishingLocus i M s)).symm

end Nonvanishing

/-! ### The restricted system covers the open it is restricted to -/

section Cover

variable {S : Scheme.{u}} (L : S.Modules) [IsInvertibleModule S L]

/-- **The nonvanishing opens of a restricted system cover the open it is restricted to.** Each is
the preimage of the corresponding nonvanishing open of the original system, by [Stacks, Tag 0H78],
and `W` lies in the union of those. This is the hypothesis that clause (5) of [Stacks, Tag 0FCY]
takes, read over `W`. -/
theorem iSup_nonvanishingOpen_pullbackGlobalSections_eq_top {ι : Type*} {W : S.Opens}
    (ψ : ι → Γ(L, ⊤)) (hW : W ≤ ⨆ v, nonvanishingOpen S L (ψ v)) :
    (⨆ v, nonvanishingOpen W.toScheme ((Scheme.Modules.pullback W.ι).obj L)
      (pullbackGlobalSections W.ι L (ψ v))) = ⊤ := by
  have h : ∀ v, nonvanishingOpen W.toScheme ((Scheme.Modules.pullback W.ι).obj L)
      (pullbackGlobalSections W.ι L (ψ v)) = W.ι ⁻¹ᵁ nonvanishingOpen S L (ψ v) :=
    fun v => nonvanishingOpen_pullbackGlobalSections W.ι L (ψ v)
  rw [iSup_congr h, ← Scheme.Hom.preimage_iSup]
  refine Opens.ext ?_
  simp only [Scheme.Hom.coe_preimage, Opens.coe_top]
  rw [Set.eq_univ_iff_forall]
  exact fun x => hW x.2

end Cover

/-! ### `k`-linearity of the pullback of a global section -/

section Linear

attribute [local instance] globalSectionsModule

variable (k : Type u) [CommRing k] {S S' : Scheme.{u}}
  [S.Over (Spec (CommRingCat.of k))] [S'.Over (Spec (CommRingCat.of k))] (i : S' ⟶ S)
  (M : S.Modules)
  (hi : i ≫ (S ↘ Spec (CommRingCat.of k)) = S' ↘ Spec (CommRingCat.of k))

include hi

/-- **A constant pulls back to the constant.** For a morphism over `Spec k` the global function
`baseRingHom k S r` has image `baseRingHom k S' r`: both are `r` composed with the structure
morphism, and the two structure morphisms agree by hypothesis. -/
theorem appTop_baseRingHom (r : k) : i.appTop (baseRingHom k S r) = baseRingHom k S' r := by
  have h : i.appTop (baseRingHom k S r) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (i ≫ (S ↘ Spec (CommRingCat.of k))).appTop).hom r := rfl
  rw [h, hi]
  rfl

/-- **Pulling a global section back is `k`-linear.** The `k`-action on global sections is
restriction of scalars along `baseRingHom`, pulling back a section is semilinear over
`AlgebraicGeometry.Scheme.Hom.appTop`
(`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul`), and a constant pulls back to
the constant. -/
theorem pullbackGlobalSections_smul_scalar (r : k) (s : Γ(M, ⊤)) :
    pullbackGlobalSections i M (r • s) = r • pullbackGlobalSections i M s := by
  have hr : (r • s : Γ(M, ⊤)) = baseRingHom k S r • s := rfl
  have key := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul i M
    (baseRingHom k S r) s
  rw [hr, key, appTop_baseRingHom k i hi r]
  rfl

/-- **The pullback of global sections along a morphism of schemes over `Spec k`, as a `k`-linear
map.** Composing a linear system with it is the restriction of that system. -/
def pullbackSectionsₗ : Γ(M, ⊤) →ₗ[k] Γ((Scheme.Modules.pullback i).obj M, ⊤) where
  toFun s := pullbackGlobalSections i M s
  map_add' x y := map_add (ConcreteCategory.hom (pullbackGlobalSections i M)) x y
  map_smul' r s := pullbackGlobalSections_smul_scalar k i M hi r s

/-- The `k`-linear map `pullbackSectionsₗ k i M hi` sends a global section `s` of `M` to its
pullback `pullbackGlobalSections i M s`. -/
@[simp] theorem pullbackSectionsₗ_apply (s : Γ(M, ⊤)) :
    pullbackSectionsₗ k i M hi s = pullbackGlobalSections i M s := rfl

end Linear

end Stacks.AlgebraicGeometry.GeneratingSectionsRestrict

end
