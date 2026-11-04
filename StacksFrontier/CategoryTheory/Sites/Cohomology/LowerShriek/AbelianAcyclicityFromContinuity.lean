module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Cellular
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclicity of lower shriek on abelian sheaves, from continuity of the functor of sites

Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the corresponding
morphism of topoi, so that `g⁻¹` is restriction along `u`. The construction of the derived lower
shriek of Stacks 07AC rests on one statement about complexes: that `g_!` carries a bounded above
acyclic complex whose terms are direct sums of the generators `j_{U!} ℤ_U` to an acyclic complex.
That statement is the hypothesis (2) of the criterion of Stacks 0794, and the source *derives* it,
from the vanishing `H^p(U, g⁻¹I) = 0` of Stacks 0D6X for an injective sheaf `I` on `D`, which in
turn the source derives from continuity of `u`.

This file performs both derivations for abelian sheaves. The library already had the two
reductions in hypothetical form —
`Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor` for the first and
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` for the second
— and what was missing in general was the discharge of the Čech comparison, that is, of the
invertibility of the maps
`u(U_{i_0} ×_U … ×_U U_{i_p}) ⟶ u(U_{i_0}) ×_{u(U)} … ×_{u(U)} u(U_{i_p})`.
That invertibility is clause (2) of the definition of a continuous functor of sites, Sites,
Definition 00WV, which Mathlib's `CategoryTheory.Functor.IsContinuous` does not record and which
`Stacks.Sites.PreservesCoveringPullbacks` does: a cofinal system of coverings whose arrows admit
the fibre products and whose fibre products `u` preserves. From it
`Stacks.Sites.preservesLimit_fibreProducts_overPost` gives the iterated comparison maps, and
`Stacks.CechSite.isIso_cechProductMapOfFunctor` their invertibility.

The module counterpart of everything below is
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleDerivedLowerShriek.lean`, which
runs the same two derivations for an injective module over a sheaf of rings on `D` and lands
Stacks 07AC; `Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules_acyclic` there is the
module form of `abelianLowerShriekAcyclic_of_continuous` below.

## Main results

All in the namespace `Stacks.Cohomology.DerivedLowerShriek` except the first:

* `Stacks.CechSite.injective_sheaf_subsingleton_ext_of_continuous`: **Stacks 0D6X for an
  injective abelian sheaf**, with the Čech comparison derived from continuity of `u` rather than
  assumed: `Ext^n(j_{U!} ℤ_U, g⁻¹I) = 0` for every object `U` of `C`, every injective abelian
  sheaf `I` on `D` and every `n ≥ 1`.
* `abelianLowerShriekAcyclic_of_continuous`: the acyclicity statement of Stacks 07AC for abelian
  sheaves, for a continuous functor of sites.
* `hasPointwiseLeftDerivedAbelianLowerShriek_of_continuous` and
  `isLeftDerivedFunctor_derivedAbelianLowerShriek_comp_derivedAbelianRestriction`: the existence
  of `Lg_!^{Ab}` and its absoluteness against derived restriction, as instances.
* `isIso_derivedAbelianLowerShriekComparison_app_of_acyclic`: `Lg_!^{Ab}` is computed degreewise
  on a bounded above complex of direct sums of the `j_{U!} ℤ_U`, from the acyclicity statement
  alone and on a site that need not be small; and
  `isIso_derivedAbelianLowerShriekComparison_app`, the same for a continuous functor of small
  sites, where that statement is a theorem.
* `isSumOfExtensionByZeroUnitsAb_single`: the single complex on `j_{U!} ℤ_U` has its terms in
  that class, so the previous result applies to it.

## Implementation notes

In the declarations that derive the acyclicity from continuity, the two sites are small and
their objects, morphisms and the coefficients lie in one universe `u`, which is the convention of
`ModuleDerivedLowerShriek.lean` and of the source. It is forced by the inputs: the Čech criterion
of Stacks 03F9 behind Stacks 0D6X needs the coefficient universe to contain the morphism
universe, and `Presieve.preZeroHypercover` indexes a covering by its own arrows, so the covering
system extracted from the topology by `Stacks.Sites.exists_preZeroHypercover_le` has index type
in that same universe.

The cellular-class declarations of the section `General` ask for none of that, the resolutions
needing only `Small.{max v w} C`, so they are stated at `C, D : Type u₁` with `Category.{v}` and
coefficients `AddCommGrpCat.{max v w}` — the universes of `AbelianDerivedExistence.lean`. The
small-site forms are their instances, and the geometric sites of
`DerivedSectionsOnABigSite.lean` are another.

Cocontinuity of `u` is what makes restriction along `u` the inverse image `g⁻¹` of a morphism of
topoi, by Sites, Lemma 00XR, but continuity alone makes restriction land in sheaves and have a
left adjoint. No step of Stacks 0D6X or of the acyclicity statement uses it, so it is absent from
those two, which are correspondingly more general than the source's; the declarations about
`Lg_!^{Ab}` keep it because the abbreviations `derivedAbelianLowerShriek` and
`derivedAbelianRestriction` of `AbelianDerivedExistence.lean` are themselves stated with it.

## References

* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open StacksDraft.UnboundedLeftDerivedFunctor

universe u u₁ v w

namespace Stacks.CechSite

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J u]

/-- **Stacks 0D6X for an injective abelian sheaf, with the Čech comparison derived from
continuity.** Let `u : C ⥤ D` be a continuous functor of sites and let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, so that `g⁻¹` is restriction along `u` by Sites, Lemma 00XR. If
`I` is an injective abelian sheaf on `D` then `H^n(U, g⁻¹I) = 0` for every `n > 0` and *every*
object `U` of `C`, the cohomology over `U` being `Ext` out of the free abelian sheaf `j_{U!} ℤ_U`
on the representable presheaf of `U`.

This is `Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor` with its covering system,
that system's iterated fibre products and cofinality, and — the mathematical point — the
invertibility of the comparison maps of those fibre products all supplied from
`Stacks.Sites.PreservesCoveringPullbacks`, which is clause (2) of the definition of a continuous
functor of sites, Sites, Definition 00WV. The covering system is the cofinal one of
`Stacks.Sites.exists_preZeroHypercover_le` and the comparison maps are invertible by
`Stacks.CechSite.isIso_cechProductMapOfFunctor`, since `Over.post u` preserves the iterated fibre
products of those coverings.

This is the case `O_D = ℤ` of Stacks 0D6X; it is proved for an arbitrary sheaf of rings in
`Stacks.Cohomology.DerivedLowerShriek.subsingleton_ext_freeAbelianSheaf_restriction`, and is
stated separately because an injective object of `Ab(D)` is not, in the formalization, an
injective module over the constant sheaf of rings `ℤ`. -/
theorem injective_sheaf_subsingleton_ext_of_continuous (U : C)
    (I : Sheaf K AddCommGrpCat.{u}) [Injective I] (n : ℕ) (hn : 0 < n) :
    Subsingleton (Ext (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u} J U)
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj I) n) := by
  set Cov : ∀ V : C, Set { E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V } :=
    fun V => { E | (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) u) } with hCov
  have hProducts : ∀ {V : C} (E : { E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V }),
      E ∈ Cov V → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
    fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImageProducts : ∀ {V : C} (E : { E : PreZeroHypercover.{u} V // E.sieve₀ ∈ J V }),
      E ∈ Cov V → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map u).I₀),
        HasProduct (fun b ↦ Over.mk ((E.1.map u).f (i b))) := fun E hE q i => by
    have := hProducts E hE q i
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
    have : HasLimit (Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post u) :=
      HasLimit.mk ⟨_, isLimitOfPreserves (Over.post u) (limit.isLimit _)⟩
    exact hasLimit_of_iso
      (F := Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post u)
      (G := Discrete.functor (fun b ↦ Over.mk ((E.1.map u).f (i b))))
      (Discrete.natIso fun _ => Iso.refl _)
  exact injective_sheaf_subsingleton_ext_of_functor.{u, u} J K u Set.univ Cov hProducts
    hImageProducts
    (fun E _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩)
    (fun V _ R hR => by
      obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u R hR
      exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩)
    (fun E hE q i => by
      let := hProducts E hE
      let := hImageProducts E hE
      let := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
      exact isIso_cechProductMapOfFunctor u E.1 q i)
    I U (Set.mem_univ _) n hn

end Stacks.CechSite

namespace Stacks.Cohomology.DerivedLowerShriek

/-! ### The cellular class and the counit, on a site that need not be small -/

section General

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (g : C ⥤ D)
  [g.IsContinuous J K] [HasSheafify J AddCommGrpCat.{max v w}]

/-- The class of direct sums of the `j_{U!} ℤ_U` is closed under isomorphisms. -/
lemma isSumOfExtensionByZeroUnitsAb_of_iso {F F' : Sheaf J AddCommGrpCat.{max v w}}
    (hF : IsSumOfExtensionByZeroUnitsAb.{w} J F) (e : F ≅ F') :
    IsSumOfExtensionByZeroUnitsAb.{w} J F' := by
  obtain ⟨ι, V, ⟨e'⟩⟩ := hF
  exact ⟨ι, V, ⟨e' ≪≫ e⟩⟩

/-- The abelian sheaf `j_{U!} ℤ_U` placed in degree zero has its terms in the class of direct
sums of the `j_{V!} ℤ_V`. -/
lemma isSumOfExtensionByZeroUnitsAb_single (U : C) (n : ℤ) :
    IsSumOfExtensionByZeroUnitsAb.{w} J
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (extensionByZeroUnitAb.{w} J U)).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact isSumOfExtensionByZeroUnitsAb_of_iso J
      ⟨PUnit.{max v w + 1}, fun _ => U, ⟨coproductUniqueIso _⟩⟩
      (HomologicalComplex.singleObjXSelf _ 0 _).symm
  · obtain ⟨Z, hZ, hPZ⟩ :=
      (IsSumOfExtensionByZeroUnitsAb.{w} J).exists_prop_of_containsZero
    exact isSumOfExtensionByZeroUnitsAb_of_iso J hPZ
      (hZ.iso (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn))

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify K AddCommGrpCat.{max v w}]
  [(g.sheafPushforwardContinuous AddCommGrpCat.{max v w} J K).IsRightAdjoint]
  [(abelianLowerShriekOnHomotopy.{w} J K g ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v w}) (ComplexShape.up ℤ))]

/-- **`Lg_!^{Ab}` is computed degreewise on a bounded above complex of direct sums of the
`j_{U!} ℤ_U`**: the counit `Lg_!^{Ab} ∘ Q ⟶ Q ∘ g_!^{Ab}` is invertible there, these complexes
being cellular for the class with which `Lg_!^{Ab}` is constructed (Stacks 0794).

The one input is the acyclicity statement of Stacks 07AC, the same one from which `Lg_!^{Ab}`
itself is built; nothing here asks the sites to be small, only the source site to be essentially
small, which is what the resolutions of the cellular class need. -/
lemma isIso_derivedAbelianLowerShriekComparison_app_of_acyclic [Small.{max v w} C]
    (hFP : AbelianLowerShriekAcyclic.{w} J K g)
    (L : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnitsAb.{w} J (L.X n)) :
    IsIso ((derivedAbelianLowerShriekComparison.{w} J K g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  have := hasExactColimitsOfShape_nat_sheafAb.{max v w} J
  have := hasExactColimitsOfShape_nat_sheafAb.{max v w} K
  have h := derives_cellularLocalizerMorphism (abelianLowerShriek.{w} J K g)
    (IsSumOfExtensionByZeroUnitsAb.{w} J)
    (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} J)
    (fun F => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} J F) hFP
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism
    _ (hasLeftResolutions_cellularLocalizerMorphism
      (IsSumOfExtensionByZeroUnitsAb.{w} J)
      (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} J)
      (fun F => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} J F))
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ h DerivedCategory.Qh _ _
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
      ⟨L, CochainComplex.isPCellular_of_isStrictlyLE _ L hL, ⟨Iso.refl _⟩⟩⟩

end Derived

end General

/-! ### The acyclicity, from continuity, on a small site -/

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J u]

/-- **The acyclicity statement of Stacks 07AC for abelian sheaves, for a continuous functor of
sites.** Lower shriek `g_!^{Ab} : Ab(C) ⥤ Ab(D)` carries every bounded above acyclic complex
whose terms are direct sums of the free abelian sheaves `j_{U!} ℤ_U` to an acyclic complex.

This is the statement that hypothesis (2) of the criterion of Stacks 0794 asks of `g_!^{Ab}`, and
the one input to which the library reduces the existence of `Lg_!^{Ab}` and its adjunction with
`g⁻¹`. It is `abelianLowerShriekAcyclic_of_ext_vanishing` — the reduction of this acyclicity to
the object-level vanishing of Stacks 0D6X, by `Ext`-acyclicity of the generators for the
adjunction `g_!^{Ab} ⊣ g⁻¹` — applied to
`Stacks.CechSite.injective_sheaf_subsingleton_ext_of_continuous`, which is that vanishing. -/
theorem abelianLowerShriekAcyclic_of_continuous : AbelianLowerShriekAcyclic.{u} J K u :=
  abelianLowerShriekAcyclic_of_ext_vanishing.{u, u} J K u fun V I _ n hn =>
    Stacks.CechSite.injective_sheaf_subsingleton_ext_of_continuous J K u V I n hn

section Derived

variable [u.IsCocontinuous J K]

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for abelian sheaves, existence, for a continuous functor of sites**: the left
derived functor `Lg_!^{Ab}` of degreewise lower shriek on abelian sheaves exists at every
object. -/
instance hasPointwiseLeftDerivedAbelianLowerShriek_of_continuous :
    (abelianLowerShriekOnHomotopy.{u} J K u ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{u} J K u
    (abelianLowerShriekAcyclic_of_continuous J K u)

/-- `Lg_!^{Ab}` stays a left derived functor after composition with derived restriction, being
constructed by resolutions. This is the second hypothesis of the derived adjunction of
Stacks 09T5. -/
instance isLeftDerivedFunctor_derivedAbelianLowerShriek_comp_derivedAbelianRestriction :
    (derivedAbelianLowerShriek.{u} J K u ⋙
        derivedAbelianRestriction.{u} J K u).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{u} J K u)
          (derivedAbelianRestriction.{u} J K u)).inv ≫
        Functor.whiskerRight (derivedAbelianLowerShriekComparison.{u} J K u)
          (derivedAbelianRestriction.{u} J K u))
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u} J K u
    (abelianLowerShriekAcyclic_of_continuous J K u) DerivedCategory.Qh
    (derivedAbelianLowerShriek.{u} J K u) (derivedAbelianLowerShriekComparison.{u} J K u)
    (derivedAbelianRestriction.{u} J K u)

omit [u.IsCocontinuous J K] in
/-- **`Lg_!^{Ab}` is computed degreewise on a bounded above complex of direct sums of the
`j_{U!} ℤ_U`**: the counit `Lg_!^{Ab} ∘ Q ⟶ Q ∘ g_!^{Ab}` is invertible there, these complexes
being cellular for the class with which `Lg_!^{Ab}` is constructed (Stacks 0794). -/
lemma isIso_derivedAbelianLowerShriekComparison_app
    (L : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnitsAb.{u} J (L.X n)) :
    IsIso ((derivedAbelianLowerShriekComparison.{u} J K u).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  isIso_derivedAbelianLowerShriekComparison_app_of_acyclic J K u
    (abelianLowerShriekAcyclic_of_continuous J K u) L hL

end Derived

end Stacks.Cohomology.DerivedLowerShriek

end
