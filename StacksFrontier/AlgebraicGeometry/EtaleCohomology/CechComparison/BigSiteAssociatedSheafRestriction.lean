module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteOpensContinuity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity

/-!
# Restricting the associated module from a big `τ`-site to the opens gives the module back

Let `B` be one of the five big sites of a topology `τ`, let `S` be a scheme below its cutoff,
let `F` be a quasi-coherent `𝒪_S`-module and let `Fᵃ` be the associated module of
[Stacks, Tag 03DU] read as an abelian sheaf on the localized big site.  This file proves the
degree-zero half of [Stacks, Tag 03P2] for `𝒞 = (Sch/S)_τ`:

  `ε_* Fᵃ ≅ ℱ`,

the direct image along `ε : (Sch/S)_τ ⟶ S_Zar` of `Fᵃ` being the abelian sheaf underlying `F`
itself.  It is stated at the level of **abelian** sheaves, which is the level the Leray collapse
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` consumes.

No sheafification intervenes on either side.  `Stacks.Adequate.opensBelowToOver` is continuous
by `AlgebraicGeometry.isContinuous_opensBelowToOver`, so
`CategoryTheory.Functor.sheafPushforwardContinuous` along it is literally restriction of
sections: the underlying presheaf of `ε_* Fᵃ` is

  `(opensBelowToOver hS).op ⋙ (overToSlice τ B S hS).op ⋙ quasiCoherentPresheafFunctor S F`,

whose value at an open `V` of `S` is `Γ(V, V.ι^* F)`, and the comparison is the map which pulls
a section of `F` over `V` back to the open subscheme `V`.  That map is a bijection for an
arbitrary module on an arbitrary scheme, by
`AlgebraicGeometry.isIso_pullbackSectionHom_ι`, so quasi-coherence of `F` is used only to have
`AlgebraicGeometry.quasiCoherentPresheafFunctor` at all.

## Main definitions

* `AlgebraicGeometry.bigOverAssociatedSheaf`: `Fᵃ` as an abelian sheaf on the localized big
  `τ`-site of `S`, namely the restriction along `AlgebraicGeometry.overToSlice` of
  `AlgebraicGeometry.fpqcOverAssociatedSheaf`.  This is the sheaf whose higher cohomology on
  affine objects `AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` kills.
* `AlgebraicGeometry.bigOverSectionsUnit`: the comparison at the level of abelian presheaves on
  the opens of `S`, pulling a section of `F` over an open back to the open subscheme.
* `AlgebraicGeometry.bigOverSectionsUnitIso`: **the identification `ℱ ≅ ε_* Fᵃ`** of abelian
  sheaves on the Zariski site of `S`.  Its `CategoryTheory.Iso.symm` is the identification as
  [Stacks, Tag 03P2] writes it.

## Main results

* `AlgebraicGeometry.isIso_bigOverSectionsUnit`: the comparison is an isomorphism.

## Implementation notes

This is the big-site twin of the file carrying
`AlgebraicGeometry.smallEtaleSectionsUnitIso`, and shares its content: the three lemmas
`AlgebraicGeometry.isIso_pullbackSectionHom_ι`,
`AlgebraicGeometry.pullbackSectionHom_map` and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`, none of which mentions a site, are
reused rather than reproved.  Only the functor out of the opens of `S` differs, and with it the
site the restriction lands on.

The module-level analogues already in the library — `AlgebraicGeometry.SmallEtale.sectionsUnit`
and `AlgebraicGeometry.BigFppfOver.sectionsUnit` — are not usable here.  They are morphisms of
presheaves of **modules** over the structure sheaf of their site, and that site is the
size-bounded small étale site respectively the big fppf category over `S`, neither of which is
a localized big `τ`-site.  Working directly with abelian groups is also what makes this short:
at the module level the comparison has to be transposed across the pullback--pushforward
adjunction of presheaves of modules and then sheafified, which is where the local-bijectivity
hypothesis of [Stacks, Tag 070S] (2) enters.  Here
`CategoryTheory.Functor.sheafPushforwardContinuous` is restriction on the nose, so the
comparison *is* the unit and no such hypothesis appears.

The isomorphism of sheaves is obtained from the isomorphism of presheaves through
`CategoryTheory.fullyFaithfulSheafToPresheaf`, the two underlying presheaves agreeing by `rfl`;
`CategoryTheory.asIso` is applied with its `CategoryTheory.IsIso` argument given explicitly,
instance search not finding `isIso_bigOverSectionsUnit` at the natural transformation.

**No `@[stacks]` attribute is attached.**  [Stacks, Tag 03P2] is a single equality quantified
over `𝒞` ranging over five big `τ`-sites *and* `S_étale`; no single one of those six cases is a
part the source delimits, and this file is in any case only the degree-zero input to it.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Adequate
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (τ : CoveringTopology)
  (B : BigSite.{u} τ) (hS : S.size < cutoff τ B)

/-- **`Fᵃ` as an abelian sheaf on a localized big `τ`-site of `S`**, obtained by restricting
`AlgebraicGeometry.fpqcOverAssociatedSheaf` along `AlgebraicGeometry.overToSlice`.  Its value at
an object `T ⟶ S` is `Γ(T, T.hom^* F)`.

This is the sheaf whose higher cohomology on affine objects vanishes by
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`. -/
public abbrev bigOverAssociatedSheaf : Sheaf (overTopology τ B S hS) AddCommGrpCat.{u} :=
  ((overToSlice τ B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (overTopology τ B S hS) (Scheme.fpqcTopology.{u}.over S)).obj (fpqcOverAssociatedSheaf S F)

/-- **The direct image `ε_*` of abelian sheaves along `ε : (Sch/S)_τ ⟶ S_Zar`**, as the sheaf
pushforward along the continuous functor `Stacks.Adequate.opensBelowToOver`, with coefficients at
the morphism universe of the big site. -/
public abbrev bigOverZariskiPushforward :
    Sheaf (overTopology τ B S hS) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u} :=
  (opensBelowToOver (κ := cutoff τ B) hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥S) (overTopology τ B S hS)

/-- **Pulling sections back, as a morphism of abelian presheaves on the opens of `S`.**  A
section of `F` over an open `V` of `S` pulls back to a section of `V.ι^* F` over all of the open
subscheme `V`, and this is natural in `V`: it is a morphism from the abelian presheaf underlying
`F` to the restriction along `Stacks.Adequate.opensBelowToOver` of the presheaf of
[Stacks, Tag 03DS].

Naturality is the two lemmas `AlgebraicGeometry.pullbackSectionHom_map` — restricting the
section before pulling it back changes nothing — and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` — the presheaf of 03DS carries
pullbacks of sections to pullbacks of sections. -/
public def bigOverSectionsUnit :
    Scheme.Modules.presheaf F ⟶
      (opensBelowToOver (κ := cutoff τ B) hS).op ⋙ (overToSlice τ B S hS).op ⋙
        quasiCoherentPresheafFunctor S F where
  app V := pullbackSectionHom (Scheme.Opens.ι V.unop) F V.unop ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl)
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    refine Eq.trans (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a) ?_
    exact (pullbackSectionsMap_pullbackSectionHom F
      ((overToSlice τ B S hS).map ((opensBelowToOver (κ := cutoff τ B) hS).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- The component of `AlgebraicGeometry.bigOverSectionsUnit` at an open of `S` is the map which
pulls a section back to the open subscheme. -/
@[simp]
public theorem bigOverSectionsUnit_app (V : (S.Opens)ᵒᵖ) :
    (bigOverSectionsUnit S F τ B hS).app V =
      pullbackSectionHom (Scheme.Opens.ι V.unop) F V.unop ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl) :=
  rfl

/-- **Pulling sections back to the open subschemes is an isomorphism.**  Each component is the
map of `AlgebraicGeometry.isIso_pullbackSectionHom_ι`, which is a statement about an arbitrary
module on an arbitrary scheme and sees no site. -/
public theorem isIso_bigOverSectionsUnit : IsIso (bigOverSectionsUnit S F τ B hS) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  exact isIso_pullbackSectionHom_ι F V.unop

/-- **`ℱ ≅ ε_* Fᵃ`, the degree-zero input of [Stacks, Tag 03P2] in the case
`𝒞 = (Sch/S)_τ`.**  The abelian sheaf on the Zariski site of `S` underlying a quasi-coherent
module `F` agrees with the direct image along `ε : (Sch/S)_τ ⟶ S_Zar` of the associated module
`Fᵃ` read on the localized big site.

The two underlying presheaves agree by `rfl` — the pushforward along a continuous functor is
restriction of sections — so this is `AlgebraicGeometry.isIso_bigOverSectionsUnit` carried
across `CategoryTheory.fullyFaithfulSheafToPresheaf`.  The `CategoryTheory.Iso.symm` of this is
the identification as [Stacks, Tag 03P2] writes it. -/
public def bigOverSectionsUnitIso :
    (SheafOfModules.toSheaf S.ringCatSheaf).obj F ≅
      (bigOverZariskiPushforward S τ B hS).obj (bigOverAssociatedSheaf S F τ B hS) :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}).preimageIso
    (@asIso _ _ _ _ (bigOverSectionsUnit S F τ B hS) (isIso_bigOverSectionsUnit S F τ B hS))

end AlgebraicGeometry

end
