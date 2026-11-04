module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf

/-!
# Restricting the associated module to the opens gives the module back

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module, and let `Fᵃ` be the associated module
of [Stacks, Tag 03DU] read as an abelian sheaf on the small étale site of `S`.  This file proves
the degree-zero half of [Stacks, Tag 03P2] in the case `𝒞 = S_étale`:

  `ε_* Fᵃ ≅ ℱ`,

the direct image along `ε : S_étale ⟶ S_Zar` of `Fᵃ` being the abelian sheaf underlying `F`
itself.  It is stated at the level of **abelian** sheaves, which is the level the Leray collapse
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` consumes.

No sheafification intervenes on either side.  `AlgebraicGeometry.opensToEtale` is continuous, so
`CategoryTheory.Functor.sheafPushforwardContinuous` along it is literally restriction of
sections: the underlying presheaf of `ε_* Fᵃ` is

  `(opensToEtale S).op ⋙ (Scheme.Etale.forget S).op ⋙ quasiCoherentPresheafFunctor S F`,

whose value at an open `V` of `S` is `Γ(V, V.ι^* F)`, and the comparison is the map which pulls
a section of `F` over `V` back to the open subscheme `V`.  That map is a bijection for an
arbitrary module on an arbitrary scheme, by
`AlgebraicGeometry.isIso_pullbackSectionHom_ι`, so quasi-coherence of `F` is used only to have
`AlgebraicGeometry.quasiCoherentPresheafFunctor` at all.

## Main definitions

* `AlgebraicGeometry.smallEtaleAssociatedSheaf`: `Fᵃ` as an abelian sheaf on the small étale
  site of `S`, namely the restriction along `AlgebraicGeometry.Scheme.Etale.forget` of
  `AlgebraicGeometry.fpqcOverAssociatedSheaf`.  This is the sheaf whose higher direct images
  `AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` kills.
* `AlgebraicGeometry.smallEtaleSectionsUnit`: the comparison at the level of abelian presheaves
  on the opens of `S`, pulling a section of `F` over an open back to the open subscheme.
* `AlgebraicGeometry.smallEtaleSectionsUnitIso`: **the identification `ℱ ≅ ε_* Fᵃ`** of abelian
  sheaves on the Zariski site of `S`.  Its `CategoryTheory.Iso.symm` is the identification as
  [Stacks, Tag 03P2] writes it.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleSectionsUnit`: the comparison is an isomorphism.

## Implementation notes

The module-level analogues of `smallEtaleSectionsUnit` already in the library —
`AlgebraicGeometry.SmallEtale.sectionsUnit` and `AlgebraicGeometry.BigFppfOver.sectionsUnit` —
are *not* usable here, and this is not a duplication of them.  They are morphisms of presheaves
of **modules** over the structure sheaf of their site, and that site is the size-bounded small
étale site `AlgebraicGeometry.SmallEtale B S hS` respectively the big fppf site, neither of which
is `AlgebraicGeometry.Scheme.Etale`; the functor out of the opens is
`AlgebraicGeometry.SmallEtale.opensToSmallEtale` respectively
`AlgebraicGeometry.BigFppfOver.opensToBig`, not `AlgebraicGeometry.opensToEtale`.  Forgetting the
module structure of either would still leave the wrong site.  What *is* shared, and is reused
rather than reproved, is the content: the three lemmas
`AlgebraicGeometry.isIso_pullbackSectionHom_ι`,
`AlgebraicGeometry.pullbackSectionHom_map` and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`, none of which mentions a site.

Working directly with abelian groups is what makes this short: at the module level the
comparison has to be transposed across the pullback--pushforward adjunction of presheaves of
modules and then sheafified, which is where the local-bijectivity hypothesis of
[Stacks, Tag 070S] (2) enters.  Here `CategoryTheory.Functor.sheafPushforwardContinuous` is
restriction on the nose, so the comparison *is* the unit and no such hypothesis appears.

The isomorphism of sheaves is obtained from the isomorphism of presheaves through
`CategoryTheory.fullyFaithfulSheafToPresheaf`, the two underlying presheaves agreeing by `rfl`;
`CategoryTheory.asIso` is applied with its `CategoryTheory.IsIso` argument given explicitly,
instance search not finding `isIso_smallEtaleSectionsUnit` at the natural transformation.

**No `@[stacks]` attribute is attached.**  [Stacks, Tag 03P2] is a single equality quantified
over `𝒞` ranging over five big `τ`-sites *and* `S_étale`; the `S_étale` case alone is not a part
the source delimits, and this file is in any case only the degree-zero input to it.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

/-- **`Fᵃ` as an abelian sheaf on the small étale site of `S`**, obtained by restricting
`AlgebraicGeometry.fpqcOverAssociatedSheaf` along the canonical functor from the small étale
site to the schemes over `S`.  Its value at an object `T ⟶ S` is `Γ(T, T.hom^* F)`.

This is the sheaf whose higher cohomology on affine objects vanishes by
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine` and whose higher direct images
along `ε : S_étale ⟶ S_Zar` vanish by
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale`. -/
public abbrev smallEtaleAssociatedSheaf : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u} :=
  ((Scheme.Etale.forget S).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S)).obj
      (fpqcOverAssociatedSheaf S F)

/-- **The direct image `ε_*` of abelian sheaves along `ε : S_étale ⟶ S_Zar`**, as the sheaf
pushforward along the continuous functor `AlgebraicGeometry.opensToEtale`, with coefficients at
the morphism universe of the small étale site.

This is `AlgebraicGeometry.zariskiPushforward` one coefficient universe down; the quasi-coherent
comparison lives at `AddCommGrpCat.{u}`, that being where
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` is stated. -/
public abbrev smallEtaleZariskiPushforward :
    Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} :=
  (opensToEtale S).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S)

/-- **Pulling sections back, as a morphism of abelian presheaves on the opens of `S`.**  A
section of `F` over an open `V` of `S` pulls back to a section of `V.ι^* F` over all of the open
subscheme `V`, and this is natural in `V`: it is a morphism from the abelian presheaf underlying
`F` to the restriction along `AlgebraicGeometry.opensToEtale` of the presheaf of
[Stacks, Tag 03DS].

Naturality is the two lemmas `AlgebraicGeometry.pullbackSectionHom_map` — restricting the
section before pulling it back changes nothing — and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` — the presheaf of 03DS carries
pullbacks of sections to pullbacks of sections. -/
public def smallEtaleSectionsUnit :
    Scheme.Modules.presheaf F ⟶
      (opensToEtale S).op ⋙ (Scheme.Etale.forget S).op ⋙ quasiCoherentPresheafFunctor S F where
  app V := pullbackSectionHom (Scheme.Opens.ι V.unop) F V.unop ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl)
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    refine Eq.trans (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a) ?_
    exact (pullbackSectionsMap_pullbackSectionHom F
      ((Scheme.Etale.forget S).map ((opensToEtale S).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- The component of `AlgebraicGeometry.smallEtaleSectionsUnit` at an open of `S` is the map
which pulls a section back to the open subscheme. -/
@[simp]
public theorem smallEtaleSectionsUnit_app (V : (S.Opens)ᵒᵖ) :
    (smallEtaleSectionsUnit S F).app V =
      pullbackSectionHom (Scheme.Opens.ι V.unop) F V.unop ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl) :=
  rfl

/-- **Pulling sections back to the open subschemes is an isomorphism.**  Each component is the
map of `AlgebraicGeometry.isIso_pullbackSectionHom_ι`, which is a statement about an arbitrary
module on an arbitrary scheme and sees no site. -/
public theorem isIso_smallEtaleSectionsUnit : IsIso (smallEtaleSectionsUnit S F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  exact isIso_pullbackSectionHom_ι F V.unop

/-- **`ℱ ≅ ε_* Fᵃ`, the degree-zero input of [Stacks, Tag 03P2] in the case `𝒞 = S_étale`.**
The abelian sheaf on the Zariski site of `S` underlying a quasi-coherent module `F` agrees with
the direct image along `ε : S_étale ⟶ S_Zar` of the associated module `Fᵃ` read on the small
étale site.

The two underlying presheaves agree by `rfl` — the pushforward along a continuous functor is
restriction of sections — so this is `AlgebraicGeometry.isIso_smallEtaleSectionsUnit` carried
across `CategoryTheory.fullyFaithfulSheafToPresheaf`.  The `CategoryTheory.Iso.symm` of this is
the identification as [Stacks, Tag 03P2] writes it. -/
public def smallEtaleSectionsUnitIso :
    (SheafOfModules.toSheaf S.ringCatSheaf).obj F ≅
      (smallEtaleZariskiPushforward S).obj (smallEtaleAssociatedSheaf S F) :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u}).preimageIso
    (@asIso _ _ _ _ (smallEtaleSectionsUnit S F) (isIso_smallEtaleSectionsUnit S F))

end AlgebraicGeometry

end
