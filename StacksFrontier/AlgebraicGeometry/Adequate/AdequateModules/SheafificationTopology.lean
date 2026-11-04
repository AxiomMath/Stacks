module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ModuleExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Sheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom

/-!
# The topology on the algebras of an affine of the site, over an arbitrary base

`Stacks.Adequate.AffineAdequateSheafTopology` is the input under which
[Stacks, Tag 06VP] is proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Sheafification.lean`: over each affine
scheme `Spec A` of a chosen big `τ`-site over `S` there is a topology on the `A`-algebras of the
site for which the affine-spectrum functor is continuous and cocontinuous and every module
extension `B ↦ B ⊗[A] M` is a sheaf. **This file discharges it**, and so proves Tag 06VP with
no hypothesis beyond the source's own.

The first two clauses are proved here. The third, the sheaf condition for the module extensions,
is `Stacks.Adequate.isSheaf_siteModuleExtension` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/ModuleExtensionSheaf.lean`: faithfully
flat descent, [Stacks, Tag 023M], along the finite jointly faithfully flat families that refine
the covering sieves of the algebras of the site. That is what the source's computation of the
plus construction as a colimit of Čech `H⁰` over the standard affine `τ`-coverings of an affine
amounts to.

The topology is not new: it is `Stacks.Adequate.affineSubsiteTopology`, the topology induced on
the `A`-algebras of the site by the topology of the big site along the affine-spectrum functor,
which `AffineSectionsFullyFaithful` builds for a chosen big site **over `Spec A`**.
What this file adds is the passage from that base to an arbitrary base `S`, which that
statement does not cover: over a general base the affine-spectrum functor is not full, so it is
not a dense subsite and the continuity and cocontinuity instances do not apply to it directly.

## Main definitions

* `Stacks.Adequate.IsChosenTopology` — the clause `Stacks.Adequate.BigSite.chosen` as a
  standalone predicate, so that a localization of a chosen big site can be assembled without
  repeating the five-fold case distinction.
* `Stacks.Adequate.atAffine` — a chosen big site over `S`, localized at an affine scheme
  `Spec A` of the site, as a chosen big site over `Spec A` **with the same cutoff**. The cutoff
  is unchanged on the nose, so the two sites have the same category of site algebras and the
  same `Stacks.Adequate.affineSubsiteTopology`.
* `Stacks.Adequate.affineBaseChange` — the functor `Over (Spec A) ⥤ Over S` of the site induced
  by the structure morphism `f : Spec A ⟶ S`.
* `Stacks.Adequate.AffineModuleExtensionSheaf` — the third clause of
  `Stacks.Adequate.AffineAdequateSheafTopology`: over an affine base, every module extension
  `B ↦ B ⊗[A] M` is a sheaf for the induced topology on the site algebras. It is named
  separately because the three clauses are discharged by different arguments.

## Main results

* `Stacks.Adequate.affineSpecOverFactor` — the affine-spectrum functor of `Spec A` over `S` is
  the affine-spectrum functor of `Spec A` over itself followed by `affineBaseChange`. The two
  differ only by the unit `h ≫ 𝟙 = h` of the structure morphism, so the comparison is an
  isomorphism and not an equality.
* `Stacks.Adequate.affineSpecOver_isContinuous` and
  `Stacks.Adequate.affineSpecOver_isCocontinuous` — the affine-spectrum functor over a general
  base is continuous and cocontinuous for the induced topology. Both are the composite of the
  dense-subsite instance over the affine base with the corresponding property of
  `affineBaseChange`, transported along `affineSpecOverFactor`.
* `Stacks.Adequate.affineAdequateSheafTopology_of_moduleExtensionSheaf` —
  `AffineModuleExtensionSheaf` implies `AffineAdequateSheafTopology`.
* `Stacks.Adequate.affineModuleExtensionSheaf` — `AffineModuleExtensionSheaf` holds at every
  value universe. Applying the previous result to it is what proves
  `Stacks.Adequate.affineAdequateSheafTopology` of
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSheafTopology.lean`, the
  unconditional `AffineAdequateSheafTopology` at every value universe.
* `Stacks.Adequate.isAdequate_sheafification'` — **[Stacks, Tag 06VP]**, with no hypothesis
  beyond the source's own. This is where the attribute sits.

## Implementation notes

`Stacks.Adequate.BigSite.chosen` is a `Prop`, so a chosen big site over `Spec A` cannot be
*defined* by cases on it; but `AffineAdequateSheafTopology` is a `Prop`, so the five-fold case
distinction can be made inside the proof of
`affineAdequateSheafTopology_of_moduleExtensionSheaf`. Each of the five branches supplies the
same four pieces of data — the localized topology at `Spec A`, its structure-sheaf condition,
its `chosen` clause, and the continuity and cocontinuity of `affineBaseChange` — to the uniform
`Stacks.Adequate.exists_affineSubsiteTopology`.

Continuity and cocontinuity of `affineBaseChange` are Mathlib's instances for `Over.map` between
localizations of one Grothendieck topology, read through
`AlgebraicGeometry.overTopology_eq_over'`: the topology of a localized big site *is*
the localization of the topology of the big site, so `Over.map` along a morphism of the site is
the localization comparison and nothing about schemes is used.

The three clauses of `AffineAdequateSheafTopology` are discharged at the *same* topology, so the
third is a statement about that one topology and no longer existentially quantified. It is also
free of `S`: the category of `A`-algebras of the site and the topology on it depend only on `A`,
on `τ` and on the cutoff, which is why `AffineModuleExtensionSheaf` quantifies over chosen big
sites with an affine base — and that is what lets the proof of the third clause work over an
affine base only.

`Stacks.Adequate.isAdequate_sheafification` keeps `AffineAdequateSheafTopology` as an explicit
hypothesis. It is not the tag's statement any more, but it is the shape in which several
conditional statements of [Stacks, Tag 06VQ] consume it, and those are stated against that
hypothesis.

## References

* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

/-! ### Localizing a chosen big site at an affine of the site -/

/-- The clause `Stacks.Adequate.BigSite.chosen` as a standalone predicate: the topology `J` on
the slice at `S` of the schemes below `κ` is the one of the accepted big-site construction for
the topology `τ`. -/
public abbrev IsChosenTopology (τ : CoveringTopology) (κ : Cardinal.{u}) (S : Scheme.{u})
    (hS : schemeSizeBelow κ S)
    (J : GrothendieckTopology (Over (⟨S, hS⟩ : SchemeBelow κ))) : Prop :=
  (τ = .zariski ∧ ∃ B : BigZariskiSite.{u},
    ∃ hS' : B.Contains S, ∃ _e : B.schemeCardinal = κ,
      HEq J (BigZariskiOver.topology B S hS')) ∨
  (τ = .etale ∧ ∃ B : BigEtaleSite.{u},
    ∃ hS' : B.Contains S, ∃ _e : B.cutoff = κ,
      HEq J (BigEtaleOver.topology B S hS')) ∨
  (τ = .fppf ∧ ∃ B : BigFppfSite.{u},
    ∃ hS' : B.Contains S, ∃ _e : B.cutoff = κ,
      HEq J (BigFppfOver.topology B S hS')) ∨
  (τ = .smooth ∧ ∃ B : BigSmoothSite.{u},
    ∃ hS' : S.size < B.cutoff, ∃ _e : B.cutoff = κ,
      HEq J (BigSmoothOver.topology B S hS')) ∨
  (τ = .syntomic ∧ ∃ B : BigSyntomicSite.{u},
    ∃ hS' : B.Contains S, ∃ _e : B.cutoff = κ,
      HEq J (BigSyntomicOver.topology B S hS'))

/-- The `chosen` clause of a chosen big site is `Stacks.Adequate.IsChosenTopology`. -/
public theorem isChosenTopology_chosen {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : IsChosenTopology τ B.cutoff S B.base_mem B.topology := B.chosen

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
  (A : CommRingCat.{u}) (f : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))
  (topA : GrothendieckTopology (Over (⟨Spec A, hA⟩ : SchemeBelow B.cutoff)))
  (hshA : Presheaf.IsSheaf topA
    (Stacks.Sites.structurePresheaf (Spec A)
      (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff)))))
  (hchA : IsChosenTopology τ B.cutoff (Spec A) hA topA)

/-- The structure morphism of an affine scheme of the site over `S`, as a morphism of the
underlying category of schemes of the site. -/
public noncomputable abbrev affineBaseHom :
    (⟨Spec A, hA⟩ : SchemeBelow B.cutoff) ⟶ ⟨S, B.base_mem⟩ :=
  ObjectProperty.homMk f

/-- A chosen big site over `S`, localized at an affine scheme `Spec A` of the site, as a chosen
big site over `Spec A`. Its cutoff is the cutoff of the given site, unchanged. -/
public def atAffine : BigSite τ (Spec A) where
  cutoff := B.cutoff
  base_mem := hA
  topology := topA
  isSheaf := hshA
  chosen := hchA

/-- The localization at an affine of the site keeps the cutoff of the site. -/
public theorem atAffine_cutoff : (atAffine B A hA topA hshA hchA).cutoff = B.cutoff := rfl

/-- The comparison of the site over `Spec A` with the site over `S`: post-composition with the
structure morphism of `Spec A`. -/
public noncomputable def affineBaseChange :
    (atAffine B A hA topA hshA hchA).category ⥤ B.category :=
  Over.map (affineBaseHom B A f hA)

/-- **The affine-spectrum functor over `S` factors through the one over `Spec A`.** The two
agree up to the unit `h ≫ 𝟙 = h` for the structure morphism of the spectrum of an algebra. -/
public noncomputable def affineSpecOverFactor :
    affineSpecOver B A f ≅
      affineSpecOver (atAffine B A hA topA hshA hchA) A (𝟙 (Spec A)) ⋙
        affineBaseChange B A f hA topA hshA hchA :=
  NatIso.ofComponents
    (fun _ => Over.isoMk (Iso.refl _)
      (ObjectProperty.hom_ext _ (congrArg (· ≫ f) (Category.comp_id _))))
    (fun _ => Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl))

/-- **The affine-spectrum functor of an affine of the site over an arbitrary base is
continuous** for the topology induced on the site algebras over that affine. -/
public theorem affineSpecOver_isContinuous
    (hcont : (affineBaseChange B A f hA topA hshA hchA).IsContinuous topA B.topology) :
    (affineSpecOver B A f).IsContinuous
      (affineSubsiteTopology (atAffine B A hA topA hshA hchA)) B.topology := by
  let : (affineBaseChange B A f hA topA hshA hchA).IsContinuous
      (atAffine B A hA topA hshA hchA).topology B.topology := hcont
  have := Functor.isContinuous_comp
    (affineSpecOver (atAffine B A hA topA hshA hchA) A (𝟙 (Spec A)))
    (affineBaseChange B A f hA topA hshA hchA)
    (affineSubsiteTopology (atAffine B A hA topA hshA hchA))
    (atAffine B A hA topA hshA hchA).topology B.topology
  exact @Functor.isContinuous_of_iso _ _ _ _ _ _
    (affineSpecOverFactor B A f hA topA hshA hchA).symm _ _ this

/-- **The affine-spectrum functor of an affine of the site over an arbitrary base is
cocontinuous** for the topology induced on the site algebras over that affine. -/
public theorem affineSpecOver_isCocontinuous
    (hco : (affineBaseChange B A f hA topA hshA hchA).IsCocontinuous topA B.topology) :
    (affineSpecOver B A f).IsCocontinuous
      (affineSubsiteTopology (atAffine B A hA topA hshA hchA)) B.topology := by
  let : (affineBaseChange B A f hA topA hshA hchA).IsCocontinuous
      (atAffine B A hA topA hshA hchA).topology B.topology := hco
  have := CategoryTheory.isCocontinuous_comp (L := B.topology)
    (affineSpecOver (atAffine B A hA topA hshA hchA) A (𝟙 (Spec A)))
    (affineBaseChange B A f hA topA hshA hchA)
    (affineSubsiteTopology (atAffine B A hA topA hshA hchA))
    (atAffine B A hA topA hshA hchA).topology
  exact @Functor.IsCocontinuous.of_iso _ _ _ _ _ _ _ _
    (affineSpecOverFactor B A f hA topA hshA hchA).symm this

/-! ### Discharging the first two clauses of `AffineAdequateSheafTopology` -/

/-- **The third clause of `Stacks.Adequate.AffineAdequateSheafTopology`**: over an affine base,
every module extension `B ↦ B ⊗[A] M` is a sheaf for the topology induced on the algebras of the
site by the topology of the site. It is proved as
`Stacks.Adequate.affineModuleExtensionSheaf`; it remains named because the three clauses are
discharged separately. -/
public abbrev AffineModuleExtensionSheaf : Prop :=
  ∀ {τ' : CoveringTopology} {A' : CommRingCat.{u}} (B' : BigSite τ' (Spec A'))
    (M : ModuleCat.{max u m} A'),
    Presheaf.IsSheaf (affineSubsiteTopology B')
      ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion (A' : Type u)
          (schemeSizeBelow B'.cutoff))).obj M).presheaf

/-- The clause of `Stacks.Adequate.AffineAdequateSheafTopology` at one affine of the site,
given the localized site at that affine and the two properties of `affineBaseChange`. -/
public theorem exists_affineSubsiteTopology
    (hcont : (affineBaseChange B A f hA topA hshA hchA).IsContinuous topA B.topology)
    (hco : (affineBaseChange B A f hA topA hshA hchA).IsCocontinuous topA B.topology)
    (hM : AffineModuleExtensionSheaf.{u, m}) :
    ∃ J : GrothendieckTopology
      (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ,
      (affineSpecOver B A f).IsCocontinuous J B.topology ∧
      (affineSpecOver B A f).IsContinuous J B.topology ∧
      ∀ M : ModuleCat.{max u m} A,
        Presheaf.IsSheaf J ((AdequateFunctor.moduleExtensionFunctorOn
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M).presheaf :=
  ⟨affineSubsiteTopology (atAffine B A hA topA hshA hchA),
    affineSpecOver_isCocontinuous B A f hA topA hshA hchA hco,
    affineSpecOver_isContinuous B A f hA topA hshA hchA hcont,
    fun M => hM (atAffine B A hA topA hshA hchA) M⟩

/-- Post-composition with a morphism of a big site is continuous and cocontinuous for the two
localizations of the topology of the site: the topology of a localized big site is the
localization of the topology of the site. -/
private theorem overMap_continuity {τ' : CoveringTopology} (C : AlgebraicGeometry.BigSite.{u} τ')
    {S' : Scheme.{u}} (hS' : S'.size < AlgebraicGeometry.cutoff τ' C)
    {T : Scheme.{u}} (hT : T.size < AlgebraicGeometry.cutoff τ' C)
    (g : (⟨T, hT⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ' C)) ⟶ ⟨S', hS'⟩) :
    (Over.map g).IsContinuous (AlgebraicGeometry.overTopology τ' C T hT)
        (AlgebraicGeometry.overTopology τ' C S' hS') ∧
      (Over.map g).IsCocontinuous (AlgebraicGeometry.overTopology τ' C T hT)
        (AlgebraicGeometry.overTopology τ' C S' hS') := by
  rw [AlgebraicGeometry.overTopology_eq_over', AlgebraicGeometry.overTopology_eq_over']
  exact ⟨inferInstance, inferInstance⟩

/-- The clause of `Stacks.Adequate.AffineAdequateSheafTopology` for a big site whose topology is
the localization `AlgebraicGeometry.overTopology` of the topology of a big site `C`, given that
the same holds at every affine of the site. -/
private theorem affineAdequateSheafTopology_overTopology {τ' : CoveringTopology}
    (C : AlgebraicGeometry.BigSite.{u} τ') {S' : Scheme.{u}}
    (hS' : S'.size < AlgebraicGeometry.cutoff τ' C)
    (hsh : Presheaf.IsSheaf (AlgebraicGeometry.overTopology τ' C S' hS')
      (Stacks.Sites.structurePresheaf S'
        (Over.post (ObjectProperty.ι (schemeSizeBelow (AlgebraicGeometry.cutoff τ' C))))))
    (hch : IsChosenTopology τ' (AlgebraicGeometry.cutoff τ' C) S' hS'
      (AlgebraicGeometry.overTopology τ' C S' hS'))
    (hchA : ∀ (A : CommRingCat.{u}) (hA : schemeSizeBelow (AlgebraicGeometry.cutoff τ' C)
      (Spec A)), IsChosenTopology τ' (AlgebraicGeometry.cutoff τ' C) (Spec A) hA
        (AlgebraicGeometry.overTopology τ' C (Spec A) hA))
    (hM : AffineModuleExtensionSheaf.{u, m}) :
    AffineAdequateSheafTopology.{u, m}
      (⟨AlgebraicGeometry.cutoff τ' C, hS', AlgebraicGeometry.overTopology τ' C S' hS', hsh,
        hch⟩ : BigSite τ' S') := by
  intro A f hA
  exact exists_affineSubsiteTopology _ A f hA
    (AlgebraicGeometry.overTopology τ' C (Spec A) hA)
    (AlgebraicGeometry.bigSite_structure_isSheaf C (Spec A) hA) (hchA A hA)
    (overMap_continuity C hS' hA (ObjectProperty.homMk f)).1
    (overMap_continuity C hS' hA (ObjectProperty.homMk f)).2 hM

/-- **The first two clauses of `Stacks.Adequate.AffineAdequateSheafTopology` from the third.**
The topology on the algebras of the site and the continuity and cocontinuity of the
affine-spectrum functor for it are supplied by this file; the sheaf condition for the module
extensions is `Stacks.Adequate.affineModuleExtensionSheaf`, so the two together discharge the
predicate outright, which is `Stacks.Adequate.affineAdequateSheafTopology` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSheafTopology.lean`. -/
public theorem affineAdequateSheafTopology_of_moduleExtensionSheaf
    {τ' : CoveringTopology} {S' : Scheme.{u}} (B' : BigSite τ' S')
    (hM : AffineModuleExtensionSheaf.{u, m}) :
    AffineAdequateSheafTopology.{u, m} B' := by
  obtain ⟨cut, base_mem, top, hsh, chosen⟩ := B'
  rcases id chosen with ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ |
    ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ <;>
  subst hτ <;> subst he <;> obtain rfl := eq_of_heq hJ
  · refine affineAdequateSheafTopology_overTopology (τ' := .zariski) C base_mem hsh chosen
      (fun A hA => ?_) hM
    exact Or.inl ⟨rfl, C, hA, rfl, HEq.rfl⟩
  · refine affineAdequateSheafTopology_overTopology (τ' := .etale) C base_mem hsh chosen
      (fun A hA => ?_) hM
    exact Or.inr (Or.inl ⟨rfl, C, hA, rfl, HEq.rfl⟩)
  · refine affineAdequateSheafTopology_overTopology (τ' := .fppf) C base_mem hsh chosen
      (fun A hA => ?_) hM
    exact Or.inr (Or.inr (Or.inl ⟨rfl, C, hA, rfl, HEq.rfl⟩))
  · refine affineAdequateSheafTopology_overTopology (τ' := .smooth) C base_mem hsh chosen
      (fun A hA => ?_) hM
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, C, hA, rfl, HEq.rfl⟩)))
  · refine affineAdequateSheafTopology_overTopology (τ' := .syntomic) C base_mem hsh chosen
      (fun A hA => ?_) hM
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, C, hA, rfl, HEq.rfl⟩)))

/-- **The sheaf condition for the module extensions over an affine base**, which is
`Stacks.Adequate.isSheaf_siteModuleExtension`: faithfully flat descent along the finite families
that refine the covering sieves of the algebras of the site. -/
public theorem affineModuleExtensionSheaf : AffineModuleExtensionSheaf.{u, m} :=
  fun B' M => isSheaf_siteModuleExtension.{u, m} B' M

/-- **[Stacks, Tag 06VP].** Let `S` be a scheme and let `F` be a presheaf of `O`-modules on the
big `τ`-site over `S`. If for *every* affine scheme `Spec A` over `S` belonging to the site the
functor `F_{F, A}` is adequate, then the sheafification of `F` is an adequate `O`-module.

The sheafification enters, as in `Stacks.Adequate.isAdequate_sheafification`, as a locally
injective and locally surjective map `η : F ⟶ G.val` to a sheaf of modules `G`, which is the
universal property of the associated sheaf; the conclusion is adequacy of `G`.

Nothing is assumed beyond the source's own hypothesis: the input of the source's proof that was
named `Stacks.Adequate.AffineAdequateSheafTopology` is discharged by
`Stacks.Adequate.affineAdequateSheafTopology_of_moduleExtensionSheaf` applied to
`Stacks.Adequate.affineModuleExtensionSheaf`, which is the proof of
`Stacks.Adequate.affineAdequateSheafTopology` and is spelled out here because that declaration
lives in a file importing this one. The attribute sits here rather than on
`Stacks.Adequate.isAdequate_sheafification`, which is this statement under that input as an
assumption and which the proof of this one calls. -/
@[stacks 06VP]
public theorem isAdequate_sheafification'
    {τ' : CoveringTopology} {S' : Scheme.{u}} (B' : BigSite τ' S')
    (F : PresheafOfModules.{max u m} B'.structureSheaf.obj)
    (G : SheafOfModules.{max u m} B'.structureSheaf) (η : F ⟶ G.val)
    (hinj : PresheafOfModules.IsLocallyInjective B'.topology η)
    (hsurj : PresheafOfModules.IsLocallySurjective B'.topology η)
    (hF : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S'),
      schemeSizeBelow B'.cutoff (Spec A) →
        AdequateFunctor.IsAdequate
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B'.cutoff))
          (presheafAffineSectionFunctor B' F A f)) :
    IsAdequate B' G :=
  isAdequate_sheafification B'
    (affineAdequateSheafTopology_of_moduleExtensionSheaf B' affineModuleExtensionSheaf.{u, m})
    F G η hinj hsurj hF

end Stacks.Adequate

end
