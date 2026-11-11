module

public import StacksFrontier.Algebra.Module.Adequate.FiniteTypeDetection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainReflection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafNaturality
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedLocalizationUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.QcohAllAlgebraSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.UniversallyAcyclicAllAlgebras

/-!
# Tag 06ZR over a condition on sections over the affines of the site

`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic`
proves [Stacks, Tag 06ZR] over one hypothesis `hacyc`: that a bounded below complex of
quasi-coherent `𝒪_U`-modules is universally acyclic exactly when the complex of adequate
`𝒪`-modules it is carried to by `u` is acyclic. This module rewrites the right-hand side of that
hypothesis so that no sheaf on the site, and no adequate module, appears in it any more:

* `Stacks.Adequate.BigSite.plus_subcategoryAcyclic_adequate_eq_inverseImage` reads acyclicity in
  `Adeq(𝒪)` off the affine-section functors, over an affine base and with no hypothesis;
* `Stacks.Adequate.BigSite.associatedModuleQcohIsoSections` identifies the affine sections of
  `u 𝓖` with `Γ(Spec C, f^*𝓖)`, naturally in `𝓖`.

Composing the two leaves `hacyc` as: *a bounded below complex of quasi-coherent `𝒪_U`-modules is
universally acyclic exactly when, for every `A`-algebra `C` of the site, the complex of
`A`-modules `Γ(Spec C, f_C^*·)` is acyclic.* That is the form in which the source argues, and
what remains of it is the comparison of quantifiers: the left-hand side ranges over **all**
schemes `T ⟶ Spec A`, the right-hand side only over the affines of the site.

The site is then removed from the right-hand side as well: the sections construction extends to
a module-valued functor on **all** `A`-algebras, and restriction to the algebras of a site
detects acyclicity of complexes of adequate functors, so the condition over the algebras of the
site is the same condition over every `A`-algebra. What is left of the comparison of quantifiers
is exactly the passage from affine schemes over `Spec A` to arbitrary ones, and that passage is
`Stacks.Adequate.universallyAcyclic_spec_eq_inverseImage_moduleExtension` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/UniversallyAcyclicAllAlgebras.lean`. So
the hypothesis is discharged here and [Stacks, Tag 06ZR] over an affine base is
unconditional.

## Main results

* `Stacks.Adequate.BigSite.affineSections_pullbackSectionsSheafFunctor_obj` — the affine sections
  of `𝓖ᵃ` over an `A`-algebra `C` of the site are `Γ(Spec C, f^*𝓖)`, by definitional unfolding.
* `Stacks.Adequate.BigSite.affineSectionsAssociatedModuleQcohIso` — hence the affine-section
  functor of `u 𝓖` is `C ↦ Γ(Spec C, f^*𝓖)`, naturally in `𝓖`.
* `Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq` — the
  right-hand side of `hacyc` rewritten on those sections.
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections`
  — **[Stacks, Tag 06ZR] over that rewritten hypothesis.**
* `Stacks.Adequate.BigSite.schemeSizeBelow_spec_of_finiteType` — every finite-type `A`-algebra
  *is* an algebra of the site, which is the input the comparison of quantifiers needs on the
  affine side.
* `Stacks.Adequate.BigSite.exists_preimage_of_siteAlgebras` — **the comparison of quantifiers on
  the affine side, pointwise**: for adequate module-valued functors on all `A`-algebras, a
  condition of exactness type which holds over every algebra of the site holds over every
  `A`-algebra.
* `Stacks.Adequate.BigSite.eq_zero_of_siteAlgebras` — its companion for vanishing.
* `Stacks.Adequate.BigSite.exists_siteAlgebra_of_finiteType` — the same statement as
  `Stacks.Adequate.BigSite.schemeSizeBelow_spec_of_finiteType` in the shape the reflection
  statement of `AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction` asks for.
* `Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections` — **the
  right-hand side of `hsec` read over all `A`-algebras**: no site appears in it any more.
* `BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_allAlgebras` —
  **[Stacks, Tag 06ZR] over a condition on all `A`-algebras.**
* `Stacks.Adequate.BigSite.qcohAffineBaseSectionsIsoTildeInverse` — the sections of `𝓖ᵃ` over the
  base affine are `Γ(Spec A, 𝓖)`.
* `Stacks.Adequate.BigSite.qcohAllAlgebraSectionsIsoModuleExtension` — hence the all-algebras
  sections construction is the module extension of `Γ(Spec A, ·)`.
* `Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections` — **the
  condition on all `A`-algebras, proved.**
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_affine` —
  **[Stacks, Tag 06ZR] at `τ = fppf`, unconditionally.**

## Implementation notes

The rewriting is `CategoryTheory.ObjectProperty.inverseImage` algebra. Two steps are not formal:
an inverse image along a composite of two `mapHomotopyCategoryPlus`'s has to be recognised as
the inverse image along the `mapHomotopyCategoryPlus` of the composite, which is
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`; and the inverse image is unchanged when
the functor is replaced by an isomorphic one, which needs the object property to be closed under
isomorphisms and is `Stacks.Adequate.inverseImage_eq_of_natIso`. Both consume the additivity of
every functor in sight, and the additivity of `Stacks.Adequate`
`.BigSite.pullbackSectionsSheafFunctor` is obtained by transporting that of `u` along the natural
isomorphism, there being no direct proof in the library.

**What is and is not here.** The affine side of the comparison of quantifiers *is* here, in
pointwise form: a finite-type `A`-algebra has `Spec` of size below the cutoff, by
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` against
`Stacks.Adequate.BigSite.cutoff_isStrongPrelimit`, so the algebras of the site include all
finite-type ones; and passing from those to *all* `A`-algebras is the filtered-colimit argument
over the finitely generated subalgebras, `Stacks.Adequate.exists_preimage_of_finiteType`, which
joins `Stacks.Adequate.isColimit_fgSubalgebraCoconeOpOp` to [Stacks, Tag 06UU],
`AdequateFunctor.isColimit_mapCocone_of_isAdequate`. The two are composed in
`Stacks.Adequate.BigSite.exists_preimage_of_siteAlgebras`.

**The boundary of [Stacks, Tag 06ZR]: there is none left over an affine base.** The hypothesis
`hsec` above was first rewritten so that it quantifies over **all** `A`-algebras rather than over
the algebras of the site, in
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections`, and then
proved. The four steps, each now closed:

1. *Site algebras to all affines over `Spec A`, pointwise* — **closed**, by
   `Stacks.Adequate.BigSite.exists_preimage_of_siteAlgebras` and
   `Stacks.Adequate.BigSite.eq_zero_of_siteAlgebras` above.
2. *The sections construction as a module-valued functor on all `A`-algebras* — **closed**, by
   `Stacks.Adequate.BigSite.qcohAllAlgebraSections` of
   `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/QcohAllAlgebraSections.lean`: it is
   the module extension `C ↦ C ⊗_A 𝓖ᵃ(Spec A)`, adequate for free, and
   `Stacks.Adequate.BigSite.qcohAllAlgebraSectionsRestrictionIso` identifies its restriction to
   the algebras of the site with the affine-section functor of `𝓖ᵃ`, by the comparison of
   Descent, Proposition 03DX.
3. *Acyclicity of a complex of module-valued functors against its behaviour over a smaller
   domain of algebras* — **closed**, by
   `AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction` of
   `StacksFrontier/AlgebraicGeometry/Adequate/AdequateFunctors/DomainReflection.lean` together
   with `Stacks.Adequate.plus_subcategoryAcyclic_eq_inverseImage`: restriction to a domain
   containing the finite-type algebras is exact and reflects isomorphisms of adequate functors,
   so it detects acyclicity.
4. *All affines over `Spec A` to all schemes `T ⟶ Spec A`* — **closed**, in three pieces.
   Acyclicity in `K⁺(Mod(𝒪_T))` is local on an affine open cover and the pullback along a
   composite is the iterated pullback, so universal acyclicity is tested over the affine `T`:
   that is `Stacks.Adequate.universallyAcyclic_of_affine` of
   `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/QcohPullbackOpenCover.lean` on
   `Stacks.AlgebraicGeometry.Modules.plus_subcategoryAcyclic_of_pullback`. An affine `T` is
   `Spec Γ(T, ⊤)` and pullback along an isomorphism of schemes is an equivalence, so it is tested
   over the spectra: `Stacks.Adequate.universallyAcyclic_of_spec` of
   `StacksFrontier/AlgebraicGeometry/Modules/QcohPullbackIsoTarget.lean`. And over `Spec C` the
   pullback is the extension of scalars, by [Stacks, Tag 01I9], while acyclicity of a complex of
   module-valued functors is acyclicity over each single algebra, so the two sides are the same
   family of conditions on complexes of `C`-modules:
   `Stacks.Adequate.universallyAcyclic_spec_eq_inverseImage_moduleExtension` of
   `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/UniversallyAcyclicAllAlgebras.lean`,
   on `Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_spec_iff` and
   `Stacks.Homology.plus_acyclic_presheafOfModules_iff`.

The hypothesis is therefore discharged, in
`Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections`, and
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_affine` is
[Stacks, Tag 06ZR] on the chosen big fppf site. The source states the lemma over an affine base
`U = Spec A` only, for whichever of the five topologies the chapter has fixed; the passage from
`τ = fppf` to the other four is
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/DerivedLocalizationAllTopologies.lean`,
where the registration is. The `_of_huniv`, `_of_acyclic`, `_of_sections` and `_of_allAlgebras`
statements remain, untagged, as the record of the reduction.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06UU](https://stacks.math.columbia.edu/tag/06UU)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

/-- **The inverse image of an object property closed under isomorphisms depends on the functor
only up to isomorphism.** -/
public theorem inverseImage_eq_of_natIso {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] {F G : C ⥤ D} (e : F ≅ G) :
    P.inverseImage F = P.inverseImage G := by
  ext X
  exact ⟨fun h ↦ P.prop_of_iso (e.app X) h, fun h ↦ P.prop_of_iso (e.app X).symm h⟩

/-- An inverse image along a composite of two `mapHomotopyCategoryPlus`'s is the inverse image
along the `mapHomotopyCategoryPlus` of the composite, up to a natural isomorphism. -/
private theorem inverseImage_inverseImage_mapHomotopyCategoryPlus_eq
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive C] [Preadditive D]
    [Preadditive E] (P : ObjectProperty (HomotopyCategory.Plus E)) [P.IsClosedUnderIsomorphisms]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    (P.inverseImage G.mapHomotopyCategoryPlus).inverseImage F.mapHomotopyCategoryPlus =
      P.inverseImage H.mapHomotopyCategoryPlus :=
  inverseImage_eq_of_natIso P (Functor.mapHomotopyCategoryPlusCompIso e)

section Affine

variable {A : CommRingCat.{u}} (B : BigFppfSite.{u}) (hS : B.Contains (Spec A))

/-! ### The affine sections of `u 𝓖` -/

/-- **The affine sections of `𝓖ᵃ` over an affine of the site are `Γ(Spec C, f^*𝓖)`.** For an
`A`-algebra `C` of the chosen big fppf site over `Spec A`, the value at `C` of the affine-section
functor of `Stacks.Adequate.BigSite.pullbackSectionsSheafFunctor` is the module of global
sections of the pullback of `𝓖` along the structure morphism `Spec C ⟶ Spec A`. This holds by
definitional unfolding: that is what the sections construction of [Stacks, Tag 03DU] (3) is. -/
public theorem BigSite.affineSections_pullbackSectionsSheafFunctor_obj
    (F : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory)
    (X : AdequateFunctor.AlgebrasInSite A
      (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)) :
    (((((BigSite.pullbackSectionsSheafFunctor B hS ⋙
            affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A
              (𝟙 (Spec A))).obj F).obj (op (op X))) : Type u)) =
      (Γ((Scheme.Modules.pullback
        (overOfAlg (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A)) X).hom).obj F.obj,
          ⊤) : Type u) := rfl

/-- **The affine-section functor of `u 𝓖` is `C ↦ Γ(Spec C, f^*𝓖)`, naturally in `𝓖`.** This is
`Stacks.Adequate.BigSite.associatedModuleQcohIsoSections` whiskered with the affine-section
functor over the affine base; the right-hand side is read off on objects by
`Stacks.Adequate.BigSite.affineSections_pullbackSectionsSheafFunctor_obj`. -/
public noncomputable def BigSite.affineSectionsAssociatedModuleQcohIso :
    (BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleQcoh ⋙
        affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A)) ≅
      BigSite.pullbackSectionsSheafFunctor B hS ⋙
        affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A)) :=
  Functor.isoWhiskerRight (BigSite.associatedModuleQcohIsoSections B hS) _

/-- The sections construction is additive, being isomorphic to `u`, which is a left adjoint. -/
public instance BigSite.additive_pullbackSectionsSheafFunctor :
    (BigSite.pullbackSectionsSheafFunctor B hS).Additive :=
  Functor.additive_of_iso (BigSite.associatedModuleQcohIsoSections B hS)

/-- The all-algebras sections construction is additive: it is the sections over the base affine
followed by extension of scalars, and both of those are additive. -/
public instance BigSite.additive_qcohAllAlgebraSections :
    (BigSite.qcohAllAlgebraSections B hS).Additive :=
  inferInstanceAs ((BigSite.qcohAffineBaseSections B hS ⋙
    AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A).Additive)

/-! ### The remaining hypothesis of Tag 06ZR, read on those sections -/

attribute [local instance] BigSite.abelianAdequateAffine

/-- **The right-hand side of the remaining hypothesis of [Stacks, Tag 06ZR], read on sections
over the affines of the site.** A bounded below complex of quasi-coherent `𝒪_U`-modules has
acyclic image under `u` in `Adeq(𝒪)` exactly when, for every `A`-algebra `C` of the site, the
complex `Γ(Spec C, f_C^*·)` is acyclic.

The acyclicity in `Adeq(𝒪)` is read on the affine-section functors by
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_adequate_eq_inverseImage`, and the affine
sections of the image of `u` are those of `𝓖ᵃ` by
`Stacks.Adequate.BigSite.affineSectionsAssociatedModuleQcohIso`. -/
public theorem BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq :
    (HomotopyCategory.Plus.subcategoryAcyclic
          (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory).inverseImage
        ((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq).mapHomotopyCategoryPlus =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctorOn.{u}
            (AdequateFunctor.siteAlgebraInclusion A
              (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)))).inverseImage
        (BigSite.pullbackSectionsSheafFunctor B hS ⋙
          affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A
            (𝟙 (Spec A))).mapHomotopyCategoryPlus := by
  rw [BigSite.plus_subcategoryAcyclic_adequate_eq_inverseImage B hS]
  exact inverseImage_inverseImage_mapHomotopyCategoryPlus_eq _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).liftCompιIso
          ((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleQcoh)
          (BigSite.ofBigFppfSite B (Spec A) hS).isAdequate_associatedModuleQcoh_obj)
        (affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A))) ≪≫
      BigSite.affineSectionsAssociatedModuleQcohIso B hS)

/-- **[Stacks, Tag 06ZR] over a condition on sections over the affines of the site.** Over an
affine scheme `U = Spec A` the bounded below derived category `D⁺(Adeq(𝒪))` is the localization
of `K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms, granted only that a bounded below
complex of quasi-coherent `𝒪_U`-modules is universally acyclic exactly when, for every
`A`-algebra `C` of the site, its complex of sections `Γ(Spec C, f_C^*·)` is acyclic.

This is
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic`
with its hypothesis rewritten by
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq`. Nothing
about sheaves on the site, or about adequate modules, is left in the hypothesis: both sides are
conditions on complexes of modules over rings.

It carries no tag, being still conditional; the registration of the source's lemma is on
`Stacks.Adequate.BigSite.isLocalization_associatedModuleAdeq_universalQuasiIso` of
`DerivedLocalizationAllTopologies.lean`. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections
    (hsec : universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctorOn.{u}
            (AdequateFunctor.siteAlgebraInclusion A
              (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)))).inverseImage
        (BigSite.pullbackSectionsSheafFunctor B hS ⋙
          affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A
            (𝟙 (Spec A))).mapHomotopyCategoryPlus) :
    (((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq).mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u}
            (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic B hS
    (hsec.trans
      (BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq B hS).symm)

end Affine

/-! ### Finite-type algebras are algebras of the site -/

section SiteAlgebras

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **A finite-type `A`-algebra is an algebra of the site.** The cutoff of a chosen big site is
a strong prelimit cardinal above `ℵ₀` — `Stacks.Adequate.BigSite.cutoff_isStrongPrelimit` and
`Stacks.Adequate.BigSite.aleph0_lt_cutoff`, which are clauses of [Stacks, Tag 000R] (9) — so
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` carries the base's membership in the site
to the spectrum of any finite-type algebra over it.

This is what the affine side of the remaining comparison of quantifiers in [Stacks, Tag 06ZR]
needs: the hypothesis of
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections`
quantifies over the algebras of the site, and every finite-type algebra is one of them. -/
public theorem BigSite.schemeSizeBelow_spec_of_finiteType
    (C : Type u) [CommRing C] [Algebra ↥A C] (hC : Algebra.FiniteType ↥A C) :
    schemeSizeBelow B.cutoff (Spec (CommRingCat.of C)) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit ↥A C B.base_mem

/-- `Stacks.Adequate.BigSite.schemeSizeBelow_spec_of_finiteType` packaged as an object of the
category of `A`-algebras of the site. -/
public def BigSite.siteAlgebraOfFiniteType (C : CommAlgCat.{u} ↥A)
    (hC : Algebra.FiniteType ↥A ↥C) :
    AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff) :=
  ⟨C, BigSite.schemeSizeBelow_spec_of_finiteType B ↥C hC⟩

/-- **The comparison of quantifiers of [Stacks, Tag 06ZR] on the affine side: for adequate
module-valued functors, the algebras of the site already see everything all `A`-algebras see.**
Let `α : F ⟶ G` and `β : G ⟶ H` be morphisms of module-valued functors on *all* `A`-algebras,
with `G` and `H` adequate. If over every `A`-algebra of the chosen big site every section of `G`
killed by `β` lies in the image of `α`, then the same holds over every `A`-algebra whatsoever.

The algebras of the site include all the finite-type ones — that is
`Stacks.Adequate.BigSite.siteAlgebraOfFiniteType`, built on
`Stacks.Adequate.BigSite.schemeSizeBelow_spec_of_finiteType` — and the finite-type algebras
already detect such a condition, which is the joining argument
`Stacks.Adequate.exists_preimage_of_finiteType`: an `A`-algebra is the filtered colimit of its
finitely generated subalgebras and an adequate functor commutes with that colimit,
[Stacks, Tag 06UU].

This is the affine half of the comparison of quantifiers left open by
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections`,
in its pointwise form. What it does *not* do is read a hypothesis of that shape off the
hypothesis `hsec` of that theorem: that would need the sections construction
`C ↦ Γ(Spec C, f_C^*𝓖)` as a module-valued functor on **all** `A`-algebras, which the library
has only over the algebras of a site, and an identification of acyclicity of a complex of
module-valued functors with its pointwise exactness. Neither is here. -/
public theorem BigSite.exists_preimage_of_siteAlgebras
    {F G H : AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A}
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G)
    (hH : AdequateFunctor.IsAdequate (𝟭 _) H) (α : F ⟶ G) (β : G ⟶ H)
    (hsite : ∀ (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
      (w : G.obj (op (op X.obj))), β.app (op (op X.obj)) w = 0 →
        ∃ v : F.obj (op (op X.obj)), α.app (op (op X.obj)) v = w)
    (R : CommAlgCat.{u} ↥A) (y : G.obj (op (op R))) (hy : β.app (op (op R)) y = 0) :
    ∃ x : F.obj (op (op R)), α.app (op (op R)) x = y :=
  exists_preimage_of_finiteType R hG hH α β
    (fun C hC ↦ hsite (BigSite.siteAlgebraOfFiniteType B C hC)) y hy

/-- **An adequate module-valued functor on all `A`-algebras which vanishes over the algebras of
the site vanishes.** The companion of `Stacks.Adequate.BigSite.exists_preimage_of_siteAlgebras`,
on the same two inputs: the algebras of the site include the finite-type ones, and an adequate
functor vanishing on those vanishes, `Stacks.Adequate.eq_zero_of_finiteType`. -/
public theorem BigSite.eq_zero_of_siteAlgebras
    (G : AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G)
    (hsite : ∀ (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
      (w : G.obj (op (op X.obj))), w = 0)
    (R : CommAlgCat.{u} ↥A) (y : G.obj (op (op R))) : y = 0 :=
  eq_zero_of_finiteType R G hG
    (fun C hC ↦ hsite (BigSite.siteAlgebraOfFiniteType B C hC)) y

end SiteAlgebras

/-! ### Tag 06ZR over a condition on all algebras of the base -/

section AllAlgebras

variable {A : CommRingCat.{u}} (B : BigFppfSite.{u}) (hS : B.Contains (Spec A))

attribute [local instance] BigSite.abelianAdequateAffine

/-- **Every finite-type `A`-algebra is an algebra of the site**, in the shape
`AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction` asks of a domain of algebras:
it is literally one of the objects of that domain, by
`Stacks.Adequate.BigSite.siteAlgebraOfFiniteType`. -/
public theorem BigSite.exists_siteAlgebra_of_finiteType (C : CommAlgCat.{u} ↥A)
    (hC : Algebra.FiniteType ↥A ↥C) :
    ∃ X : AdequateFunctor.AlgebrasInSite ↥A
        (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff),
      (AdequateFunctor.siteAlgebraInclusion ↥A
        (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)).obj X = C :=
  ⟨BigSite.siteAlgebraOfFiniteType (BigSite.ofBigFppfSite B (Spec A) hS) C hC, rfl⟩

/-- `Stacks.Adequate.BigSite.qcohAllAlgebraSections` with values in the **adequate** module-valued
functors, which is where the comparison of quantifiers lives: every one of its values is
adequate, by `Stacks.Adequate.BigSite.isAdequate_qcohAllAlgebraSections_obj`. -/
public noncomputable abbrev BigSite.qcohAllAlgebraSectionsAdequate :
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory ⥤
      (AdequateFunctor.adequate.{u, u, u} ↥A).FullSubcategory :=
  ObjectProperty.lift _ (BigSite.qcohAllAlgebraSections B hS)
    (BigSite.isAdequate_qcohAllAlgebraSections_obj B hS)

/-- The adequate factorisation is additive, its action on morphisms being that of
`Stacks.Adequate.BigSite.qcohAllAlgebraSections`. -/
public instance BigSite.additive_qcohAllAlgebraSectionsAdequate :
    (BigSite.qcohAllAlgebraSectionsAdequate B hS).Additive where
  map_add := ObjectProperty.hom_ext _ (BigSite.qcohAllAlgebraSections B hS).map_add

/-- **The affine-section functor of `𝓖ᵃ` over the algebras of the site, factored through the
adequate module-valued functors on all `A`-algebras.** This is
`Stacks.Adequate.BigSite.qcohAllAlgebraSectionsRestrictionIso` with the all-algebras sections
construction replaced by its adequate factorisation, which is where the comparison of
quantifiers of [Stacks, Tag 06UU] can be applied to it. -/
public noncomputable def BigSite.qcohAllAlgebraSectionsAdequateRestrictionIso :
    BigSite.qcohAllAlgebraSectionsAdequate B hS ⋙
        ((AdequateFunctor.adequate.{u, u, u} ↥A).ι ⋙
          PresheafOfModules.pushforward₀
            (AdequateFunctor.siteAlgebraInclusion ↥A
              (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)).op
            (AdequateFunctor.algebraRingDiagram.{u} ↥A)) ≅
      BigSite.pullbackSectionsSheafFunctor B hS ⋙
        affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A (𝟙 (Spec A)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
    BigSite.qcohAllAlgebraSectionsRestrictionIso B hS

/-- **The remaining hypothesis of [Stacks, Tag 06ZR] no longer mentions the site at all: its
right-hand side may be read over ALL `A`-algebras.** Acyclicity of the complex of affine-section
functors of `𝓖ᵃ` over the `A`-algebras *of the site* is the same condition as acyclicity of the
complex of module-valued functors `C ↦ C ⊗_A 𝓖ᵃ(Spec A)` over *all* `A`-algebras.

Both sides are the acyclic complexes of the abelian category of adequate module-valued functors
on all `A`-algebras, pulled back along an exact functor that reflects isomorphisms, so both are
`Stacks.Adequate.plus_subcategoryAcyclic_eq_inverseImage`. On the left the functor is
restriction to the algebras of the site after the inclusion of the adequate functors, which
reflects isomorphisms by
`AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction` — the comparison of
quantifiers of [Stacks, Tag 06UU] — against
`Stacks.Adequate.BigSite.exists_siteAlgebra_of_finiteType`; on the right it is the inclusion
alone, which reflects isomorphisms because it is fully faithful. The two complexes are
identified by `Stacks.Adequate.BigSite.qcohAllAlgebraSectionsAdequateRestrictionIso` and by
`CategoryTheory.ObjectProperty.liftCompιIso`. -/
public theorem BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections :
    (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctorOn.{u}
            (AdequateFunctor.siteAlgebraInclusion ↥A
              (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)))).inverseImage
        (BigSite.pullbackSectionsSheafFunctor B hS ⋙
          affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS) A
            (𝟙 (Spec A))).mapHomotopyCategoryPlus =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)).inverseImage
        (BigSite.qcohAllAlgebraSections B hS).mapHomotopyCategoryPlus := by
  let := AdequateFunctor.preservesHomology_adequateι.{u} (A := ↥A)
  let := AdequateFunctor.preservesHomology_adequateι_comp_restriction.{u}
    (AdequateFunctor.siteAlgebraInclusion ↥A
      (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff))
  let := AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction.{u}
    (AdequateFunctor.siteAlgebraInclusion ↥A
      (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff))
    (BigSite.exists_siteAlgebra_of_finiteType B hS)
  let : (AdequateFunctor.adequate.{u, u, u} ↥A).ι.ReflectsIsomorphisms :=
    (AdequateFunctor.adequate.{u, u, u} ↥A).fullyFaithfulι.reflectsIsomorphisms
  have h₁ := (plus_subcategoryAcyclic_eq_inverseImage
    ((AdequateFunctor.adequate.{u, u, u} ↥A).ι ⋙
      PresheafOfModules.pushforward₀
        (AdequateFunctor.siteAlgebraInclusion ↥A
          (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)).op
        (AdequateFunctor.algebraRingDiagram.{u} ↥A))).symm
  have h₂ := plus_subcategoryAcyclic_eq_inverseImage (AdequateFunctor.adequate.{u, u, u} ↥A).ι
  refine Eq.trans (inverseImage_inverseImage_mapHomotopyCategoryPlus_eq _
    (BigSite.qcohAllAlgebraSectionsAdequateRestrictionIso B hS)).symm ?_
  refine Eq.trans ?_ (inverseImage_inverseImage_mapHomotopyCategoryPlus_eq _
    (ObjectProperty.liftCompιIso (AdequateFunctor.adequate.{u, u, u} ↥A)
      (BigSite.qcohAllAlgebraSections B hS)
      (BigSite.isAdequate_qcohAllAlgebraSections_obj B hS)))
  exact congrArg
    (fun S => ObjectProperty.inverseImage S
      (BigSite.qcohAllAlgebraSectionsAdequate B hS).mapHomotopyCategoryPlus)
    (h₁.trans h₂)

/-- **[Stacks, Tag 06ZR] over a condition on all `A`-algebras.** Over an affine scheme
`U = Spec A` the bounded below derived category `D⁺(Adeq(𝒪))` is the localization of
`K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms, granted only that a bounded below complex
of quasi-coherent `𝒪_U`-modules is universally acyclic exactly when, for **every** `A`-algebra
`C`, its complex of sections `Γ(Spec C, f_C^*·)` is acyclic.

This is
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections`
with its hypothesis rewritten by
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections`. The site
has disappeared from the hypothesis: what is left of it is the comparison between all schemes
`T ⟶ Spec A` and the affine ones, and nothing about a cutoff on the size of `T`.

It carries no tag, being still conditional; the registration of the source's lemma is on
`Stacks.Adequate.BigSite.isLocalization_associatedModuleAdeq_universalQuasiIso` of
`DerivedLocalizationAllTopologies.lean`. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_allAlgebras
    (hall : universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)).inverseImage
        (BigSite.qcohAllAlgebraSections B hS).mapHomotopyCategoryPlus) :
    (((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq).mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u}
            (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_sections B hS
    (hall.trans
      (BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections B hS).symm)

/-! ### The last hypothesis, discharged -/

/-- **The sections of `𝓖ᵃ` over the base affine are `Γ(Spec A, 𝓖)`.** The sections of `𝓖ᵃ` over
an object of the site are the global sections of the pullback of `𝓖` to the scheme of that
object, and the structure morphism of the base affine is the identity, so the pullback there may
be dropped: that is `Stacks.Adequate.pullbackBaseAffineIso`.

Both sides are `Stacks.Adequate.moduleSpecΓFunctor` of a pullback, by definitional unfolding —
the affine-section construction *is* the global sections of the pullback — so only the pullback
along the identity has to be removed. -/
public noncomputable def BigSite.qcohAffineBaseSectionsIsoTildeInverse :
    BigSite.qcohAffineBaseSections B hS ≅ (tildeEquiv (R := A)).inverse :=
  Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι
    (Functor.isoWhiskerRight
        (pullbackBaseAffineIso (BigSite.ofBigFppfSite B (Spec A) hS)) moduleSpecΓFunctor ≪≫
      Functor.leftUnitor moduleSpecΓFunctor)

/-- **The all-algebras sections construction is the module extension of the global sections over
the base.** `Stacks.Adequate.BigSite.qcohAllAlgebraSections` is by definition the sections over
the base affine followed by extension of scalars, and those sections are `Γ(Spec A, 𝓖)` by
`Stacks.Adequate.BigSite.qcohAffineBaseSectionsIsoTildeInverse`. -/
public noncomputable def BigSite.qcohAllAlgebraSectionsIsoModuleExtension :
    BigSite.qcohAllAlgebraSections B hS ≅
      (tildeEquiv (R := A)).inverse ⋙ AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A :=
  Functor.isoWhiskerRight (BigSite.qcohAffineBaseSectionsIsoTildeInverse B hS) _

/-- **The remaining hypothesis of [Stacks, Tag 06ZR] over an affine base, proved.** A bounded
below complex of quasi-coherent `𝒪_{Spec A}`-modules is universally acyclic exactly when the
complex of module-valued functors `C ↦ C ⊗_A Γ(Spec A, ·)` on all `A`-algebras is acyclic.

This is `Stacks.Adequate.universallyAcyclic_spec_eq_inverseImage_moduleExtension`, where the
right-hand side is stated on the module extension of the global sections, transported along
`Stacks.Adequate.BigSite.qcohAllAlgebraSectionsIsoModuleExtension`. -/
public theorem BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections :
    universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)).inverseImage
        (BigSite.qcohAllAlgebraSections B hS).mapHomotopyCategoryPlus :=
  universallyAcyclic_spec_eq_inverseImage_moduleExtension.trans
    (inverseImage_eq_of_natIso _
      ((Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl ((tildeEquiv (R := A)).inverse ⋙
            AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A))).symm ≪≫
        Functor.mapHomotopyCategoryPlusCompIso
          (BigSite.qcohAllAlgebraSectionsIsoModuleExtension B hS).symm))

/-- **[Stacks, Tag 06ZR] at `τ = fppf`.** Over an affine scheme `U = Spec A`, on the chosen
big fppf site of `B` over `U`, the bounded below derived category `D⁺(Adeq(𝒪))` is the
localization of `K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms. The statement for each of
the five topologies of the source's conventions is
`Stacks.Adequate.BigSite.isLocalization_associatedModuleAdeq_universalQuasiIso` of
`DerivedLocalizationAllTopologies.lean`, which carries the registration.

This is `BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_allAlgebras` with
its single hypothesis discharged by
`Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections`. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_affine :
    (((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq).mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u}
            (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_allAlgebras B hS
    (BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections B hS)

end AllAlgebras

end Stacks.Adequate

end
