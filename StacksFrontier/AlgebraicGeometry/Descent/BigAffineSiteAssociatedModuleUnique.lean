module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines

/-!
# Conditions (7) and (8) of Stacks 0GZV at `τ = fppf`

Let `S` be a scheme inside a chosen big fppf site `B` and let `𝓕` be a sheaf of
`𝒪_Aff`-modules on the big affine fppf site `(Aff/S)_fppf`. Condition (7) of Stacks 0GZV says
that `𝓕` corresponds, under the equivalence of ringed topoi of Stacks 0GZU, to a quasi-coherent
module on `(Sch/S)_fppf`; condition (8) says that `𝓕` arises from a **unique** quasi-coherent
`𝒪_S`-module `𝒢` by the construction of Descent, Section 35.8, that is, is the restriction to
the affine objects of `𝒢^a`. **This file proves that conditions (7) and (8) are equivalent at
`τ = fppf`, and proves the uniqueness of `𝒢` in condition (8) there.**

## The argument

The source gets (7) ⇔ (8) from Descent, Proposition 03DX, and that is the route taken here.

* The *uniqueness* of `𝒢` is the full faithfulness of the composite

  `QCoh(𝒪_S) ⥤ Mod((Sch/S)_fppf, 𝒪) ⥤ Mod((Aff/S)_fppf, 𝒪_Aff)`,  `𝒢 ↦ 𝒢^a|_{(Aff/S)_fppf}`.

  Both factors are fully faithful with no hypothesis. The first is Stacks 0GN7 for the big
  site, `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`, which holds at
  every `τ`. The second is the Comparison Lemma for sheaves of modules,
  `Stacks.DenseSubsiteModules.moduleRestriction`, whose fullness and faithfulness need only
  that the inclusion of the affine objects is a dense subsite inclusion — Stacks 021V,
  available as `AlgebraicGeometry.bigAffineFppfInclusion_isDenseSubsite`. In particular the
  uniqueness half uses **no** part of Descent, Proposition 03DX.

* (8) ⇒ (7) is Stacks 03DV (1): `𝒢^a` is quasi-coherent on `(Sch/S)_fppf`, so it is itself a
  witness for condition (7).

* (7) ⇒ (8) is the essential surjectivity half of Descent, Proposition 03DX (1) at
  `τ = fppf`, which this development has unconditionally as
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`: the module on
  `(Sch/S)_fppf` witnessing condition (7) is isomorphic to some `𝒢^a`, and restricting that
  isomorphism to the affine objects gives condition (8).

## Main definitions

* `AlgebraicGeometry.bigAffineFppfModuleRestriction`: restriction of sheaves of modules from
  `(Sch/S)_fppf` to `(Aff/S)_fppf`, over the restricted structure sheaf. This is the functor
  induced on modules by the equivalence of ringed topoi of Stacks 0GZU.
* `AlgebraicGeometry.bigAffineFppfAssociatedModuleQcoh`: the functor
  `𝒢 ↦ 𝒢^a|_{(Aff/S)_fppf}` of condition (8) of Stacks 0GZV at `τ = fppf`.
* `AlgebraicGeometry.BigAffineFppf.IsRestrictionOfQuasicoherent` and
  `AlgebraicGeometry.BigAffineFppf.IsRestrictedAssociatedModule`: conditions (7) and (8) of
  Stacks 0GZV at `τ = fppf`, as predicates on `𝓕`.

## Main results

* `AlgebraicGeometry.fullyFaithfulBigAffineFppfModuleRestriction`: the restriction functor is
  fully faithful, with no hypothesis.
* `AlgebraicGeometry.fullyFaithfulBigAffineFppfAssociatedModuleQcoh` and
  `AlgebraicGeometry.bigAffineFppf_iso_of_associatedModuleQcoh_restriction_iso`:
  **Stacks 0GZV, the uniqueness of `𝒢` in condition (8) at `τ = fppf`.**
* `AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_of_isRestrictedAssociatedModule`:
  **Stacks 0GZV, (8) ⇒ (7) at `τ = fppf`.**
* `AlgebraicGeometry.bigAffineFppf_isRestrictedAssociatedModule_of_isRestrictionOfQuasicoherent`:
  **Stacks 0GZV, (7) ⇒ (8) at `τ = fppf`**, uniqueness of `𝒢` included.
* `AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_iff_isRestrictedAssociatedModule`:
  **Stacks 0GZV, conditions (7) and (8) are equivalent at `τ = fppf`.**

## Implementation notes

The coefficient sheaf of the target of the restriction functor is
`Stacks.DenseSubsiteModules.ringRestriction` of the structure sheaf of `(Sch/S)_fppf`, and that
is the structure sheaf the big affine fppf ringed site of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines` carries, on the nose:
`AlgebraicGeometry.ringRestriction_bigFppfOver_structureSheaf`. So conditions (7) and (8) below
are predicates on a module over the same structure sheaf as conditions (1)–(6) there, and they
compose with those: `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_restriction` is
(7) ⇒ the quasi-coherence conjunct of (6), and
`AlgebraicGeometry.bigAffineFppf_isIso_canonicalMap_of_isQuasicoherentOnSite` carries that on to
condition (1).

`𝒢^a` is taken to be the pullback of `𝒢` along the morphism of ringed sites
`id_{fppf,Zar} : ((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, which is the description of Remark 03FH and
the form in which the development's 0GN7 and 03DX are stated; its identification with the
sections description of Definition 03DU (3) is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, Stacks 070S (1).

The sections of the modules stay in the universe `u` of the schemes, as they do throughout
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`: the Comparison Lemma
for sheaves of modules ties the universe of the module sections to the universe of the ring
sections.

## Coverage

This file is `τ = fppf`.  The four coarser `τ` are
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCoarserAssociatedModule`, which proves the
uniqueness of `𝒢`, (8) ⇒ (7), (1) ⇔ (7), (1) ⇒ (8) and (7) ⇔ (8) at all five topologies at
once.

(The four coarser `τ` need a dense-subsite inclusion of the affine objects for the inherited
`τ`-topology, and the four dense-subsite instances of
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence` provide it: they
might seem to concern the affine objects of independently chosen big Zariski, étale, smooth and
syntomic sites, different categories from `AlgebraicGeometry.BigAffineFppf B S hS`, but the big
`τ`-sites `AlgebraicGeometry.BigFppfSite.toBigZariskiSite` and its three
companions are assembled from `B`'s own cutoff and covering bound syntactically, so their
affine objects over `S` are `AlgebraicGeometry.BigAffineFppf B S hS` on the nose and those four
instances *are* statements about the inclusion of this file — and
`AlgebraicGeometry.generate_affineOverPresieve_mem` uses them that way.  Nor is (7) ⇒ (8)
specific to fppf, resting on Descent, Proposition 03DX (1) at `τ`: (7) ⇒ (1) ⇒ (8) avoids 03DX at
`τ` altogether.)

The implication **(1) ⇒ (7)** of Stacks 0GZV, equivalently (6) ⇒ (7), is covered in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteModuleComparisonLemma`, which together with
this file closes (1) ⇒ (8) as well. It has two inputs: a sheaf of modules on `(Sch/S)_fppf`
restricting to the given cartesian `𝓕`, and the quasi-coherence of that module on the big site.

The **second** input is
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`, in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesReflect`: once `𝓕` is
quasi-coherent on the affine subsite, every ambient lift of it is quasi-coherent. The **first**
is `AlgebraicGeometry.bigAffineFppf_exists_moduleLift`, i.e. the essential surjectivity of
`AlgebraicGeometry.bigAffineFppfModuleRestriction`, the Comparison Lemma for sheaves of modules
at the universe `u` of the module sections. That needs
`∀ X, HasLimitsOfShape (StructuredArrow X (BigAffineFppf.inclusion B S hS).op) AddCommGrpCat.{u}`,
which holds because the index categories are *essentially* `u`-small:
`AlgebraicGeometry.essentiallySmall_bigAffineFppf` and local `u`-smallness of `(Sch/S)_fppf`.

(Two points about these inputs. The reflection of quasi-coherence needs only the *full
faithfulness* half of the Comparison Lemma, and that holds at every universe of module sections,
independently of the universe of the ring sections:
`Stacks.DenseSubsiteModules.fullyFaithful_moduleRestrictionRaised`; the single-universe shape of
`Stacks.DenseSubsiteModules.moduleRestriction` is a feature of its statement, not an obstruction.
On the existence side, the structured-arrow categories have their objects in `Type (u + 1)`, and
nothing follows from that: `CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` asks for
essential `u`-smallness of the index category, which holds. The raising of the sections into
`Type (max (u + 1) w)` in the statement of Stacks 0GZU in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence` buys a free
section universe `w`, not reachability of `u`, and no descent from `u + 1` to `u` is needed.

The counit argument of Descent, Proposition 03DX (2) from quasi-coherence of the affine
restriction alone, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounitFromAffine`, is not a
weakening, since quasi-coherence of the affine restriction is equivalent to quasi-coherence on the
small étale site.)

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0GZU](https://stacks.math.columbia.edu/tag/0GZU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of sheaves of modules from the big fppf site of `S` to its big affine fppf
site, taken over the restricted structure sheaf. This is the functor induced on modules by the
equivalence of ringed topoi of Stacks 0GZU. -/
public noncomputable abbrev bigAffineFppfModuleRestriction :=
  Stacks.DenseSubsiteModules.moduleRestriction (BigAffineFppf.topology B S hS)
    (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
    (BigFppfOver.structureSheaf B S hS)

/-- The structure sheaf over which `AlgebraicGeometry.bigAffineFppfModuleRestriction` takes its
values is the one the big affine fppf ringed site of Stacks 0GZV carries. -/
public theorem ringRestriction_bigFppfOver_structureSheaf :
    Stacks.DenseSubsiteModules.ringRestriction (BigAffineFppf.topology B S hS)
        (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
        (BigFppfOver.structureSheaf B S hS) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O) :=
  rfl

/-- **Restriction of sheaves of modules to the big affine fppf site is fully faithful**, with no
hypothesis: the inclusion of the affine objects is a dense subsite inclusion by Stacks 021V, and
the Comparison Lemma for sheaves of modules needs nothing more for full faithfulness. -/
public noncomputable def fullyFaithfulBigAffineFppfModuleRestriction :
    (bigAffineFppfModuleRestriction B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- **The functor of condition (8) of Stacks 0GZV at `τ = fppf`**: a quasi-coherent
`𝒪_S`-module `𝒢` is sent to the restriction to the affine objects of the associated module
`𝒢^a` of Descent, Definition 03DU. -/
public noncomputable abbrev bigAffineFppfAssociatedModuleQcoh :=
  BigFppfOver.baseAssociatedModuleQcoh B S hS .fppf ⋙ bigAffineFppfModuleRestriction B S hS

/-- **Stacks 0GZV, the uniqueness of `𝒢` in condition (8) at `τ = fppf`.** The functor
`𝒢 ↦ 𝒢^a|_{(Aff/S)_fppf}` from the quasi-coherent `𝒪_S`-modules to the `𝒪_Aff`-modules on
`(Aff/S)_fppf` is fully faithful: it is Stacks 0GN7 for the big site followed by the Comparison
Lemma for sheaves of modules on the dense subsite of affine objects. No part of Descent,
Proposition 03DX is used. -/
@[stacks 0GZV "(8) at τ = fppf, uniqueness of 𝒢"]
public noncomputable def fullyFaithfulBigAffineFppfAssociatedModuleQcoh :
    (bigAffineFppfAssociatedModuleQcoh B S hS).FullyFaithful :=
  (BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh B S hS .fppf).comp
    (fullyFaithfulBigAffineFppfModuleRestriction B S hS)

/-- **Stacks 0GZV, the uniqueness of `𝒢` in condition (8) at `τ = fppf`**, read as a uniqueness
statement: two quasi-coherent `𝒪_S`-modules whose associated modules have isomorphic
restrictions to the big affine fppf site of `S` are isomorphic. -/
@[stacks 0GZV "(8) at τ = fppf, uniqueness of 𝒢"]
public theorem bigAffineFppf_iso_of_associatedModuleQcoh_restriction_iso
    (G₁ G₂ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : (bigAffineFppfAssociatedModuleQcoh B S hS).obj G₁ ≅
      (bigAffineFppfAssociatedModuleQcoh B S hS).obj G₂) :
    Nonempty (G₁.obj ≅ G₂.obj) :=
  ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso
    ((fullyFaithfulBigAffineFppfAssociatedModuleQcoh B S hS).preimageIso e)⟩

namespace BigAffineFppf

/-- **Condition (7) of Stacks 0GZV at `τ = fppf`**: under the equivalence of ringed topoi of
Stacks 0GZU, `𝓕` corresponds to a quasi-coherent module on `(Sch/S)_fppf`. -/
public abbrev IsRestrictionOfQuasicoherent
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) : Prop :=
  ∃ M : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS),
    M.IsQuasicoherentOnSite ∧ Nonempty (F ≅ (bigAffineFppfModuleRestriction B S hS).obj M)

/-- **Condition (8) of Stacks 0GZV at `τ = fppf`**: `𝓕` is the restriction to the affine
objects of the associated module `𝒢^a` of a quasi-coherent `𝒪_S`-module `𝒢`, and `𝒢` is unique
up to isomorphism. -/
public abbrev IsRestrictedAssociatedModule
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) : Prop :=
  ∃ G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
    Nonempty (F ≅ (bigAffineFppfAssociatedModuleQcoh B S hS).obj G) ∧
      ∀ H : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
        Nonempty (F ≅ (bigAffineFppfAssociatedModuleQcoh B S hS).obj H) →
          Nonempty (G.obj ≅ H.obj)

end BigAffineFppf

/-- **Stacks 0GZV, (8) ⇒ (7) at `τ = fppf`.** The module on `(Sch/S)_fppf` that condition (7)
asks for is `𝒢^a` itself, which is quasi-coherent there by Stacks 03DV (1). -/
@[stacks 0GZV "(8) ⇒ (7) at τ = fppf"]
public theorem bigAffineFppf_isRestrictionOfQuasicoherent_of_isRestrictedAssociatedModule
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (hF : BigAffineFppf.IsRestrictedAssociatedModule B S hS F) :
    BigAffineFppf.IsRestrictionOfQuasicoherent B S hS F := by
  obtain ⟨G, ⟨e⟩, -⟩ := hF
  refine ⟨(BigFppfOver.baseAssociatedModuleQcoh B S hS .fppf).obj G, ?_, ⟨e⟩⟩
  exact BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS .fppf
    G.obj G.property

/-- **Stacks 0GZV, (7) ⇒ (8) at `τ = fppf`**, with the uniqueness of `𝒢` included. The module
`𝓜` on `(Sch/S)_fppf` given by condition (7) is quasi-coherent, hence isomorphic to `𝒢^a` for a
quasi-coherent `𝒪_S`-module `𝒢` by the essential surjectivity half of Descent,
Proposition 03DX (1) at `τ = fppf`; restricting that isomorphism to the affine objects gives
`𝓕 ≅ 𝒢^a|_{(Aff/S)_fppf}`, and `𝒢` is unique up to isomorphism by
`AlgebraicGeometry.fullyFaithfulBigAffineFppfAssociatedModuleQcoh`. -/
@[stacks 0GZV "(7) ⇒ (8) at τ = fppf, existence and uniqueness of 𝒢"]
public theorem bigAffineFppf_isRestrictedAssociatedModule_of_isRestrictionOfQuasicoherent
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O))
    (hF : BigAffineFppf.IsRestrictionOfQuasicoherent B S hS F) :
    BigAffineFppf.IsRestrictedAssociatedModule B S hS F := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hF
  obtain ⟨G, ⟨f⟩⟩ := BigFppfOver.quasicoherentIsEssImageAssociatedModule' B S hS M hM
  replace e := e ≪≫ (bigAffineFppfModuleRestriction B S hS).mapIso f.symm
  exact ⟨G, ⟨e⟩, fun H ⟨g⟩ =>
    bigAffineFppf_iso_of_associatedModuleQcoh_restriction_iso B S hS G H (e.symm ≪≫ g)⟩

/-- **Stacks 0GZV, conditions (7) and (8) are equivalent at `τ = fppf`**, which is how the
source reads them off each other from Descent, Proposition 03DX. -/
@[stacks 0GZV "(7) ⇔ (8) at τ = fppf"]
public theorem bigAffineFppf_isRestrictionOfQuasicoherent_iff_isRestrictedAssociatedModule
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) :
    BigAffineFppf.IsRestrictionOfQuasicoherent B S hS F ↔
      BigAffineFppf.IsRestrictedAssociatedModule B S hS F :=
  ⟨bigAffineFppf_isRestrictedAssociatedModule_of_isRestrictionOfQuasicoherent B S hS F,
    bigAffineFppf_isRestrictionOfQuasicoherent_of_isRestrictedAssociatedModule B S hS F⟩

end AlgebraicGeometry

end
