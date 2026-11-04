module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The higher direct images form a universal δ-functor

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites, inducing the direct image
`f_* = u^s : Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)` of sheaves with values in an abelian category `𝒜`. The higher
direct images `R^q f_*` are the right derived functors of `f_*`. This file equips that family with
the data [Stacks, Tag 071F] asserts it carries: for every short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of sheaves on `𝒞` a connecting morphism `R^q f_* Q ⟶ R^(q+1) f_* F`, natural
in the sequence, making

`0 ⟶ R⁰f_* F ⟶ R⁰f_* I ⟶ R⁰f_* Q ⟶ R¹f_* F ⟶ R¹f_* I ⟶ ⋯`

exact; and it proves the resulting cohomological δ-functor ([Stacks, Tag 010Q]) is *universal*
([Stacks, Tag 010S]).

The first half of [Stacks, Tag 071F] — the computation `R^i f_* F = H^i(f_* I^•)` from a chosen
injective resolution — is recorded elsewhere in this library, on Mathlib's
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`. What is added here is the second half,
the δ-functor structure.

## Main definitions

* `Stacks.Cohomology.HigherDirectImageDelta.higherDirectImage`: the functor `R^q f_*`.
* `Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageDeltaFunctor`: the family
  `q ↦ R^q f_*` as a cohomological δ-functor `Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)`.
* `Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageδ`: the connecting morphism
  `R^q f_* X₃ ⟶ R^(q+1) f_* X₁` of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`.

## Main results

* `Stacks.Cohomology.HigherDirectImageDelta.mono_higherDirectImage_zero_map_f`,
  `exact_higherDirectImage_map`, `exact_map_g_higherDirectImageδ`,
  `exact_higherDirectImageδ_map_f`: the long exact sequence, recorded three terms at a time,
  together with `mono` in degree zero.
* `Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageδ_naturality`: the connecting
  morphisms are natural in the short exact sequence.
* `Stacks.Cohomology.HigherDirectImageDelta.isUniversal_higherDirectImageDeltaFunctor`: the
  δ-functor of higher direct images is universal.
* `Stacks.Cohomology.HigherDirectImageDelta.isZero_higherDirectImage_succ_injective`: the
  effaceability that makes it universal — `R^(q+1) f_*` kills injective sheaves.
* `Stacks.Cohomology.HigherDirectImageDelta.isUniversal_abelianHigherDirectImageDeltaFunctor`:
  the same statement for sheaves of abelian groups, `Ab(𝒞) ⥤ Ab(𝒟)`, which is how the source
  phrases it; there no hypothesis beyond continuity of `u` is left, because
  `Stacks.Cohomology.HigherDirectImageDelta.hasSheafify_addCommGrpCat` and
  `Stacks.Cohomology.HigherDirectImageDelta.enoughInjectives_sheaf_addCommGrpCat` discharge the
  rest.

## Implementation notes

**Where the content comes from.** All of the exactness is
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, which transports the long
exact homology sequence of the bounded below derived category (`DerivedCategory.homologySequenceδ`
applied to the distinguished triangle attached to a short exact sequence) across the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the `ℤ`-indexed and `ℕ`-indexed right derived
functors. Nothing in this file is specific to sites beyond the three facts that the two sheaf
categories are abelian, that the direct image is additive, and that the source has enough
injectives; the first two are instances here, the third is a hypothesis, since it is a theorem
about the site rather than a formal consequence of continuity.

**Universality** is `CategoryTheory.DeltaFunctor.isUniversal_of_isZero_injective`, Stacks 010T
for a category with enough injectives: the higher right derived functors of any additive functor
vanish on injective objects, by `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`.

**The derived category hypotheses.** `[HasDerivedCategory _]` is a choice of localisation of the
category of cochain complexes, always available as `HasDerivedCategory.standard`; it is carried as
a hypothesis rather than fixed by a local instance so that a consumer which has already chosen one
can use these results with that choice.

## References

* [Stacks Project, Tag 071F](https://stacks.math.columbia.edu/tag/071F)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HigherDirectImageDelta

universe v₁ u₁ v₂ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K]

/-- **The `q`-th higher direct image** `R^q f_* : Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)`, the `q`-th right derived
functor of the direct image along a continuous functor `u : 𝒟 ⥤ 𝒞`. -/
@[ega "0 12.2.1", sga "4 V 5.0" "special case"]
def higherDirectImage [EnoughInjectives (Sheaf K A)] (q : ℕ) : Sheaf K A ⥤ Sheaf J A :=
  (u.sheafPushforwardContinuous A J K).rightDerived q

variable [EnoughInjectives (Sheaf K A)]

/-- `R^q f_*` is Mathlib's `q`-th right derived functor of the direct image. -/
theorem higherDirectImage_eq (q : ℕ) :
    higherDirectImage J K A u q = (u.sheafPushforwardContinuous A J K).rightDerived q :=
  rfl

/-- The higher direct images are additive. -/
instance additive_higherDirectImage (q : ℕ) : (higherDirectImage J K A u q).Additive :=
  inferInstanceAs ((u.sheafPushforwardContinuous A J K).rightDerived q).Additive

/-- **The higher direct images of an injective sheaf vanish in positive degrees.** This is the
effaceability of the δ-functor below, and the reason it is universal. -/
theorem isZero_higherDirectImage_succ_injective (q : ℕ) (I : Sheaf K A) [Injective I] :
    IsZero ((higherDirectImage J K A u (q + 1)).obj I) :=
  Functor.isZero_rightDerived_obj_injective_succ (u.sheafPushforwardContinuous A J K) q I

section Delta

variable [HasDerivedCategory.{w₁} (Sheaf K A)] [HasDerivedCategory.{w₂} (Sheaf J A)]

/-- **[Stacks, Tag 071F], second half: the family `q ↦ R^q f_*` of higher direct images is a
cohomological δ-functor** `Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)`. Attached to a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of sheaves on `𝒞` are connecting morphisms
`R^q f_* X₃ ⟶ R^(q+1) f_* X₁`, natural in the sequence, for which
`0 ⟶ R⁰f_* X₁ ⟶ R⁰f_* X₂ ⟶ R⁰f_* X₃ ⟶ R¹f_* X₁ ⟶ ⋯` is exact. -/
@[ega "0 12.2.1" "partial"]
def higherDirectImageDeltaFunctor : DeltaFunctor (Sheaf K A) (Sheaf J A) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (u.sheafPushforwardContinuous A J K)

/-- The degree-`q` component of the δ-functor is the `q`-th higher direct image. -/
@[simp]
theorem higherDirectImageDeltaFunctor_functor (q : ℕ) :
    (higherDirectImageDeltaFunctor J K A u).functor q = higherDirectImage J K A u q :=
  rfl

variable {S T : ShortComplex (Sheaf K A)}

/-- **The connecting morphism `R^q f_* X₃ ⟶ R^(q+1) f_* X₁`** of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of sheaves on `𝒞`. -/
def higherDirectImageδ (hS : S.ShortExact) (q : ℕ) :
    (higherDirectImage J K A u q).obj S.X₃ ⟶ (higherDirectImage J K A u (q + 1)).obj S.X₁ :=
  (higherDirectImageDeltaFunctor J K A u).δ hS q

/-- `R^q f_* X₂ ⟶ R^q f_* X₃ ⟶ R^(q+1) f_* X₁` composes to zero. -/
@[reassoc]
theorem map_g_comp_higherDirectImageδ (hS : S.ShortExact) (q : ℕ) :
    (higherDirectImage J K A u q).map S.g ≫ higherDirectImageδ J K A u hS q = 0 :=
  (higherDirectImageDeltaFunctor J K A u).map_g_δ hS q

/-- `R^q f_* X₃ ⟶ R^(q+1) f_* X₁ ⟶ R^(q+1) f_* X₂` composes to zero. -/
@[reassoc]
theorem higherDirectImageδ_comp_map_f (hS : S.ShortExact) (q : ℕ) :
    higherDirectImageδ J K A u hS q ≫ (higherDirectImage J K A u (q + 1)).map S.f = 0 :=
  (higherDirectImageDeltaFunctor J K A u).δ_map_f hS q

/-- The long exact sequence begins with `0 ⟶ R⁰f_* X₁ ⟶ R⁰f_* X₂`: the direct image preserves the
monomorphism of a short exact sequence. -/
theorem mono_higherDirectImage_zero_map_f (hS : S.ShortExact) :
    Mono ((higherDirectImage J K A u 0).map S.f) :=
  (higherDirectImageDeltaFunctor J K A u).mono_map_f hS

/-- `R^q f_* X₁ ⟶ R^q f_* X₂ ⟶ R^q f_* X₃` is exact. -/
theorem exact_higherDirectImage_map (hS : S.ShortExact) (q : ℕ) :
    (S.map (higherDirectImage J K A u q)).Exact :=
  (higherDirectImageDeltaFunctor J K A u).exact_map hS q

/-- `R^q f_* X₂ ⟶ R^q f_* X₃ ⟶ R^(q+1) f_* X₁` is exact. -/
theorem exact_map_g_higherDirectImageδ (hS : S.ShortExact) (q : ℕ) :
    (ShortComplex.mk ((higherDirectImage J K A u q).map S.g) (higherDirectImageδ J K A u hS q)
      (map_g_comp_higherDirectImageδ J K A u hS q)).Exact :=
  (higherDirectImageDeltaFunctor J K A u).exact_δ₁ hS q

/-- `R^q f_* X₃ ⟶ R^(q+1) f_* X₁ ⟶ R^(q+1) f_* X₂` is exact. -/
theorem exact_higherDirectImageδ_map_f (hS : S.ShortExact) (q : ℕ) :
    (ShortComplex.mk (higherDirectImageδ J K A u hS q)
      ((higherDirectImage J K A u (q + 1)).map S.f)
      (higherDirectImageδ_comp_map_f J K A u hS q)).Exact :=
  (higherDirectImageDeltaFunctor J K A u).exact_δ₂ hS q

/-- **The connecting morphisms are natural in the short exact sequence**: for a morphism `φ` of
short complexes between two short exact sequences,
`R^q f_*(φ₃) ≫ δ_T = δ_S ≫ R^(q+1) f_*(φ₁)`. -/
@[reassoc, ega "III 4.1.7.21" "more general"]
theorem higherDirectImageδ_naturality (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (q : ℕ) :
    (higherDirectImage J K A u q).map φ.τ₃ ≫ higherDirectImageδ J K A u hT q =
      higherDirectImageδ J K A u hS q ≫ (higherDirectImage J K A u (q + 1)).map φ.τ₁ :=
  (higherDirectImageDeltaFunctor J K A u).δ_naturality hS hT φ q

/-- **[Stacks, Tag 071F], second half: the δ-functor of higher direct images is universal**
([Stacks, Tag 010S]) — every natural transformation out of `R⁰f_* = f_*` into the degree-zero part
of another δ-functor extends uniquely to a morphism of δ-functors. By [Stacks, Tag 010T] this
follows from `isZero_higherDirectImage_succ_injective`. -/
@[ega "0 12.2.1" "more general"]
theorem isUniversal_higherDirectImageDeltaFunctor :
    (higherDirectImageDeltaFunctor J K A u).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun q I _ ↦
    isZero_higherDirectImage_succ_injective J K A u q I

/-- Universality of the δ-functor of higher direct images, as an instance, so that results about
universal δ-functors apply to `higherDirectImageDeltaFunctor` without an explicit argument. -/
instance : (higherDirectImageDeltaFunctor J K A u).IsUniversal :=
  isUniversal_higherDirectImageDeltaFunctor J K A u

end Delta

/-! ### Sheaves of abelian groups

The source states [Stacks, Tag 071F] for the categories `Ab(𝒞)` and `Ab(𝒟)` of sheaves of abelian
groups. The hypotheses of the general construction above are all theorems there, so no assumption
beyond continuity of `u` survives.
-/

section AbelianSheaves

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]

/-- **Abelian sheaves on a site admit sheafification**, in the universe generated by the site.
A restatement of `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` with the coefficient
universe pinned, so that it can serve as an instance. -/
theorem hasSheafify_addCommGrpCat (J : GrothendieckTopology D) :
    HasSheafify J AddCommGrpCat.{max u₁ v₁} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u₁, v₁, v₁}

attribute [local instance] hasSheafify_addCommGrpCat HasDerivedCategory.standard

/-- **Abelian sheaves on a site have enough injectives**, in the universe generated by the site.
A restatement of `Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp` with the
coefficient universe pinned, so that it can serve as an instance. -/
@[ega "0 12.2.1" "partial",
  sga "4 I 7.13" "special case",
  sga "4 II 6.9" "Remark 6.9, special case",
  sga "4 V 0.2.1" "abelian sheaves on sites",
  sga "4½ Arcata 1.6.3",
  sga "4½ Etat_0 6.2" "special case"]
theorem enoughInjectives_sheaf_addCommGrpCat (J : GrothendieckTopology D) :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u₁ v₁}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u₁, v₁, v₁}

attribute [local instance] enoughInjectives_sheaf_addCommGrpCat

variable (J : GrothendieckTopology D) (K : GrothendieckTopology C) (u : D ⥤ C)
  [u.IsContinuous J K]

/-- **[Stacks, Tag 071F], second half, for sheaves of abelian groups.** For a continuous functor
`u : 𝒟 ⥤ 𝒞` between sites the higher direct images `R^q f_*` form a *universal* cohomological
δ-functor `Ab(𝒞) ⥤ Ab(𝒟)`. The δ-functor itself is `higherDirectImageDeltaFunctor`, so its
connecting morphisms and its long exact sequence are the ones named above; what is recorded here
is that for abelian sheaves no hypothesis beyond continuity of `u` is needed, since `Ab(𝒞)` admits
sheafification and has enough injectives. -/
@[ega "0 12.2.1" "more general"]
theorem isUniversal_abelianHigherDirectImageDeltaFunctor :
    (higherDirectImageDeltaFunctor J K AddCommGrpCat.{max u₁ v₁} u).IsUniversal :=
  isUniversal_higherDirectImageDeltaFunctor J K AddCommGrpCat.{max u₁ v₁} u

end AbelianSheaves

end Stacks.Cohomology.HigherDirectImageDelta

end
