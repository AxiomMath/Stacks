module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.ProObject
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDirectImageLevels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ChaoticEquivalenceCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the chaotic sites on the affine side of Stacks 07JL

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]).  [Stacks, Tag 07JL]
puts the chaotic topology of [Stacks, Tag 07GE] on

`𝒞 = (Cris(C/A))ᵒᵖ`  and  `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ`,

and the proof of [Stacks, Tag 07JN] computes cohomology on both.  The first half of this file
supplies the four instances that make `CategoryTheory.Sheaf.H` exist on these two sites
(sheafification, local smallness, enough injectives, `Ext`-groups), at the coefficient universe
`max u v (w + 1)`, by `CategoryTheory.Sheaf.enoughInjectives_of_small`.

The rest of the file draws from them two transports of cohomology.  First, the chaotic subsite
`𝒞_X ⊆ Cris(X/S)` of thickenings of the whole of an affine `X`, on which [Stacks, Tag 07JK]
computes `RΓ(Cris(X/S), F)`, is anti-equivalent to the little affine crystalline category by
`Crystalline.GlobalCrystallineSituation.wholeSpaceOpEquivLittleAffineOp`, hence equivalent as a
*site* to `𝒞 = (Cris(C/A))ᵒᵖ` with the chaotic topology on both sides.  An equivalence of chaotic
sites does not change cohomology (`Stacks.ChaoticSite.sheafHAddEquivOfEquivalence`), so composing
with [Stacks, Tag 07JK] gives

`H^j(𝒞, G_F) ≅ H^j(Cris(X/S), F)`

for a locally quasi-coherent `F`, where `G_F` is the transport of `F|_{𝒞_X}` to `𝒞`.  Second, the
same comparison carries the cohomology of the small model `Crystalline.CompletedSmallSite` of
`𝒞^∧`, on which [Stacks, Tag 07JM] is run, to the cohomology of `𝒞^∧` itself.

With these, `Crystalline.GlobalCrystallineSituation.SmallSite.IsDirectImageCohomologyComparison`
reduces to the Leray degeneration `H^j(𝒞^∧, g_*(G|_𝒞)) ≅ H^j(𝒞, G|_𝒞)` alone, which is stated
here as the proposition `IsAbelianCompletedLerayComparison`.

What the comparison with [Stacks, Tag 07JK] uses of the coefficient sheaf is the predicate
`Vanishing07JJ`, the conclusion of [Stacks, Tag 07JJ]; local quasi-coherence of a module enters
only through `...SmallSite.vanishing07JJ_abelianSheaf`, which supplies it.  So the general
statements below carry `Vanishing07JJ` and an arbitrary abelian sheaf, and each module-valued
statement is the corresponding general one instantiated.  Some such hypothesis is needed:
for an arbitrary abelian sheaf, the positive-degree cohomology over an affine object need not
vanish.

## Main definitions

* `Crystalline.littleChaoticTopology` — the chaotic topology on `𝒞 = (Cris(C/A))ᵒᵖ`.
* `Crystalline.completedChaoticTopology` — the chaotic topology on `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSiteChaoticEquiv` — the equivalence of
  sites `𝒞_X ≌ 𝒞` underlying the comparison, both chaotic.
* `Crystalline.GlobalCrystallineSituation.SmallSite.littleChaoticSheafOfWhole` — the transport of
  an abelian sheaf on `𝒞_X` to an abelian sheaf on `𝒞`.
* `Crystalline.completedChaoticSheafOfPresheaf` — an abelian presheaf on `Cris^∧(C/A)` read as an
  abelian sheaf on `𝒞^∧`, the counterpart on `𝒞^∧` of `Crystalline.smallSheafOfPresheaf`.
* `...SmallSite.IsAbelianCompletedLerayComparison` and `...SmallSite.IsCompletedLerayComparison` —
  the Leray degeneration `H^j(𝒞^∧, g_*(G|_𝒞)) ≅ H^j(𝒞, G|_𝒞)` of [Stacks, Tag 07JN], for an
  abelian sheaf and for the abelian sheaf of a module respectively; the second is the first at
  `abelianSheaf F`.

## Main results

* `Crystalline.hasSheafify_littleChaotic`, `Crystalline.locallySmall_sheaf_littleChaotic`,
  `Crystalline.enoughInjectives_sheaf_littleChaotic`, `Crystalline.hasExt_sheaf_littleChaotic` —
  **the four instances making `Sheaf.H` exist on `𝒞`**.
* `Crystalline.hasSheafify_completedChaotic`,
  `Crystalline.locallySmall_sheaf_completedChaotic`,
  `Crystalline.enoughInjectives_sheaf_completedChaotic`,
  `Crystalline.hasExt_sheaf_completedChaotic` — **the same four on `𝒞^∧`**.
* `...SmallSite.littleChaoticSheafHAddEquiv` — **the cohomology of `𝒞` is the cohomology of
  `𝒞_X`**, for the transport of any abelian sheaf.
* `...SmallSite.chaoticCohomologyComparisonIsoOfVanishing07JJ` — **the comparison of
  [Stacks, Tag 07JK] for an arbitrary abelian sheaf satisfying `Vanishing07JJ`**.
* `...SmallSite.littleChaoticCohomologyComparisonOfVanishing07JJ` and
  `...SmallSite.littleChaoticCohomologyComparison` — **`H^j(𝒞, G_𝒞) ≅ H^j(Cris(X/S), G)`**, the
  composite of the previous item with the transport across `𝒞_X ≌ 𝒞`; the first for an abelian
  sheaf satisfying `Vanishing07JJ`, the second for a locally quasi-coherent sheaf of modules.
* `Crystalline.smallSheafHAddEquivCompletedChaotic` — **the cohomology of the small model of
  `𝒞^∧` is the cohomology of `𝒞^∧`.**
* `...SmallSite.isDirectImageCohomologyComparison_of_leray` and
  `...SmallSite.computesCohomology_wholeSpaceSystem_of_leray` — granted the Leray degeneration,
  the complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)` for a locally quasi-coherent
  `F`.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Crystalline

/-! ### The chaotic sites of Stacks 07JL and their cohomological instances -/

section Instances

universe u v w

variable (s : AffineCrystallineSituation.{u, v})

/-- **The site `𝒞 = (Cris(C/A))ᵒᵖ` of [Stacks, Tag 07JL]**: the opposite of the little affine
crystalline category, with the chaotic topology of [Stacks, Tag 07GE]. -/
abbrev littleChaoticTopology :
    GrothendieckTopology ((CrystallineThickening.{u, v, w} s)ᵒᵖ) := ⊥

/-- **The site `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` of [Stacks, Tag 07JL]**: the opposite of the completed
little affine crystalline category, with the chaotic topology of [Stacks, Tag 07GE]. -/
abbrev completedChaoticTopology :
    GrothendieckTopology ((CompletedCrystallineThickening.{u, v, w} s)ᵒᵖ) := ⊥

/-- Abelian presheaves on `𝒞` admit sheafification, at the coefficient universe
`max u v (w + 1)` of the affine side. -/
instance hasSheafify_littleChaotic :
    HasSheafify (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v (w + 1), w, max u v (w + 1)} _

/-- Abelian sheaves on `𝒞` are locally `max u v (w + 1)`-small. -/
instance locallySmall_sheaf_littleChaotic :
    LocallySmall.{max u v (w + 1)}
      (Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  Sheaf.locallySmall_of_small.{max u v (w + 1), max u v (w + 1), w, max u v (w + 1),
    max u v (w + 1) + 1} _ Ab.{max u v (w + 1)}

/-- **Abelian sheaves on `𝒞 = (Cris(C/A))ᵒᵖ` have enough injectives.**  The objects of
`Cris(C/A)` form a type in the coefficient universe `max u v (w + 1)`, so the sheaves form a
Grothendieck abelian category there, by `CategoryTheory.Sheaf.enoughInjectives_of_small`. -/
@[sga "4 I 7.13" "special case", sga "4 V 0.1.1" "special case"]
instance enoughInjectives_sheaf_littleChaotic :
    EnoughInjectives (Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  Sheaf.enoughInjectives_of_small.{max u v (w + 1), max u v (w + 1), w, max u v (w + 1),
    max u v (w + 1) + 1} _ Ab.{max u v (w + 1)}

/-- **`Ext`-groups of abelian sheaves on `𝒞` exist** in the coefficient universe. -/
instance hasExt_sheaf_littleChaotic :
    HasExt.{max u v (w + 1)}
      (Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  hasExt_of_enoughInjectives.{max u v (w + 1)} _

/-- Abelian presheaves on `𝒞^∧` admit sheafification, at the coefficient universe
`max u v (w + 1)` of the affine side. -/
instance hasSheafify_completedChaotic :
    HasSheafify (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v (w + 1), w, max u v (w + 1)} _

/-- Abelian sheaves on `𝒞^∧` are locally `max u v (w + 1)`-small. -/
instance locallySmall_sheaf_completedChaotic :
    LocallySmall.{max u v (w + 1)}
      (Sheaf (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  Sheaf.locallySmall_of_small.{max u v (w + 1), max u v (w + 1), w, max u v (w + 1),
    max u v (w + 1) + 1} _ Ab.{max u v (w + 1)}

/-- **Abelian sheaves on `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` have enough injectives.**  An object of
`Cris^∧(C/A)` bundles its own carrier, so the objects form a type in the coefficient universe
`max u v (w + 1)` and `CategoryTheory.Sheaf.enoughInjectives_of_small` applies. -/
@[sga "4 I 7.13" "special case"]
instance enoughInjectives_sheaf_completedChaotic :
    EnoughInjectives (Sheaf (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  Sheaf.enoughInjectives_of_small.{max u v (w + 1), max u v (w + 1), w, max u v (w + 1),
    max u v (w + 1) + 1} _ Ab.{max u v (w + 1)}

/-- **`Ext`-groups of abelian sheaves on `𝒞^∧` exist** in the coefficient universe. -/
instance hasExt_sheaf_completedChaotic :
    HasExt.{max u v (w + 1)}
      (Sheaf (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) :=
  hasExt_of_enoughInjectives.{max u v (w + 1)} _

/-- **An abelian presheaf on `Cris^∧(C/A)` read as an abelian sheaf on `𝒞^∧`.**  The topology is
chaotic, so every presheaf is a sheaf; this is the counterpart on the site of [Stacks, Tag 07JL]
itself of `Crystalline.smallSheafOfPresheaf`, which reads the same presheaf as a sheaf on the
small model `Crystalline.CompletedSmallSite`. -/
def completedChaoticSheafOfPresheaf
    (𝓖 : CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    Sheaf (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)} :=
  ⟨(opOpEquivalence (CompletedCrystallineThickening.{u, v, w} s)).functor ⋙ 𝓖,
    Presheaf.isSheaf_bot _⟩

/-- **Restricting along the small model gives back the small-model sheaf.**  The sheaf on the
small model of `𝒞^∧` attached to an abelian presheaf on `Cris^∧(C/A)` is the restriction, along
`Crystalline.completedSmallSiteEquiv`, of the sheaf on `𝒞^∧` attached to the same presheaf, by
definition. -/
theorem chaoticRestriction_completedChaoticSheafOfPresheaf
    (𝓖 : CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    (Stacks.ChaoticSite.chaoticRestriction (completedSmallSiteEquiv.{u, v, w} s)
        Ab.{max u v (w + 1)}).obj (completedChaoticSheafOfPresheaf s 𝓖) =
      smallSheafOfPresheaf s 𝓖 :=
  rfl

/-- **The cohomology of the small model of `𝒞^∧` is the cohomology of `𝒞^∧`.**  For every degree
`j`, the group that [Stacks, Tag 07JM] computes on the small model
(`Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_generator`) is the cohomology of
the site `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` of [Stacks, Tag 07JL] itself.

The two sites are equivalent but do **not** have their morphisms in one universe: the small
model is `CategoryTheory.AsSmall`, so its morphisms live in the universe of its objects. -/
def smallSheafHAddEquivCompletedChaotic
    (𝓖 : CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) (j : ℕ) :
    Sheaf.H.{max u v (w + 1), max u v (w + 1)} (smallSheafOfPresheaf s 𝓖) j ≃+
      Sheaf.H.{max u v (w + 1), max u v (w + 1)} (completedChaoticSheafOfPresheaf s 𝓖) j :=
  haveI := hasExt_sheaf_completedSmallSite.{u, v, w} s
  Stacks.ChaoticSite.sheafHAddEquivOfEquivalence.{max u v (w + 1)}
    (completedSmallSiteEquiv.{u, v, w} s) (completedChaoticSheafOfPresheaf s 𝓖) j

end Instances

/-! ### Transporting the cohomology of Stacks 07JK to the little affine chaotic site -/

namespace GlobalCrystallineSituation.SmallSite

universe u

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The equivalence of chaotic sites `𝒞_X ≌ 𝒞`.**  The subcategory `𝒞_X ⊆ Cris(X/S)` of
thickenings of the whole of `X` is anti-equivalent to the little affine crystalline category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`, so it is equivalent to the site `𝒞 = (Cris(C/A))ᵒᵖ` of
[Stacks, Tag 07JL].  This is
`Crystalline.GlobalCrystallineSituation.wholeSpaceOpEquivLittleAffineOp` read as an equivalence of
sites: both carry the chaotic topology. -/
abbrev wholeSiteChaoticEquiv :
    WholeSpaceThickening S ≌
      (_root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp))ᵒᵖ :=
  wholeSpaceOpEquivLittleAffineOp hp

/-- **The transport of an abelian sheaf on `𝒞_X` to an abelian sheaf on `𝒞`**, along the
equivalence of sites `wholeSiteChaoticEquiv`.  Restriction along the equivalence carries it back
to the sheaf it came from, up to the unit isomorphism. -/
abbrev littleChaoticSheafOfWhole
    (G : Sheaf (chaoticTopology S) AddCommGrpCat.{u + 1}) :
    Sheaf (littleChaoticTopology.{u, u, u} (affineSituation S hp)) AddCommGrpCat.{u + 1} :=
  (Stacks.ChaoticSite.chaoticSheafEquiv (wholeSiteChaoticEquiv hp)
    AddCommGrpCat.{u + 1}).functor.obj G

/-- **The cohomology of `𝒞` is the cohomology of `𝒞_X`.**  For every degree `j`,

`H^j(𝒞_X, G) ≅ H^j(𝒞, G_𝒞)`

where `G_𝒞` is the transport of `G` across the equivalence of sites.  This is
`Stacks.ChaoticSite.sheafHAddEquivOfEquivalence'`, an equivalence of chaotic sites changing
neither the constant sheaf on `ℤ` nor the injective objects. -/
def littleChaoticSheafHAddEquiv (G : Sheaf (chaoticTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    chaoticCohomology S G j ≃+
      Sheaf.H.{u + 1, u + 1} (littleChaoticSheafOfWhole hp G) j :=
  Stacks.ChaoticSite.sheafHAddEquivOfEquivalence'.{u + 1} (wholeSiteChaoticEquiv hp) G j

/-- **The comparison of [Stacks, Tag 07JK] for an arbitrary abelian sheaf satisfying the
conclusion of [Stacks, Tag 07JJ]**: `H^j(𝒞_X, G|_{𝒞_X}) ≅ H^j(Cris(X/S), G)` for an abelian sheaf
`G` on `Cris(X/S)` with `Vanishing07JJ S G`.

The proof of [Stacks, Tag 07JK] uses local quasi-coherence of a sheaf of modules only to produce
`Vanishing07JJ S (abelianSheaf F)` (`...SmallSite.vanishing07JJ_abelianSheaf`), so it applies to
any abelian sheaf satisfying that predicate.  `...SmallSite.chaoticCohomologyComparisonIso` is
this statement at `G = abelianSheaf F`. -/
def chaoticCohomologyComparisonIsoOfVanishing07JJ
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G) (j : ℕ) :
    (chaoticCohomologyFunctor S j).obj ((restrictToWhole S).obj G) ≅
      (cohomologyFunctor S j).obj G :=
  ((chaoticRightDerivedGlobalSectionsIso S j).app
      ((restrictAffineToWhole S).obj ((restrictToAffine S).obj G))).symm ≪≫
    lerayRightDerivedGlobalSectionsIso hp ((restrictToAffine S).obj G) j
      (fun q h1 _ => isZero_higherDirectImageToWhole_of_vanishing07JJ S hG q h1) ≪≫
    (affineRightDerivedGlobalSectionsIso S j).app ((restrictToAffine S).obj G) ≪≫
    affineCohomologyIso S G j

/-- **`H^j(𝒞, G_𝒞) ≅ H^j(Cris(X/S), G)`** for an arbitrary abelian sheaf `G` on `Cris(X/S)`
satisfying the conclusion `Vanishing07JJ` of [Stacks, Tag 07JJ], where `G_𝒞` is the transport to
`𝒞` of the restriction of `G` to the chaotic subsite `𝒞_X` of [Stacks, Tag 07JK].

This is `chaoticCohomologyComparisonIsoOfVanishing07JJ` composed with the transport
`littleChaoticSheafHAddEquiv` across the equivalence of chaotic sites `𝒞_X ≌ 𝒞`. -/
def littleChaoticCohomologyComparisonOfVanishing07JJ
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G) (j : ℕ) :
    Sheaf.H.{u + 1, u + 1} (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj G)) j ≃+
      cohomology S G j :=
  (littleChaoticSheafHAddEquiv hp ((restrictToWhole S).obj G) j).symm.trans
    (chaoticCohomologyComparisonIsoOfVanishing07JJ hp G hG j).addCommGroupIsoToAddEquiv

/-- **`H^j(𝒞, G_F) ≅ H^j(Cris(X/S), F)`**: the cohomology of the little affine chaotic site
`𝒞 = (Cris(C/A))ᵒᵖ` of [Stacks, Tag 07JL] computes the crystalline cohomology of a locally
quasi-coherent sheaf of modules, where `G_F` is the transport to `𝒞` of the restriction of the
associated abelian sheaf to the chaotic subsite `𝒞_X` of [Stacks, Tag 07JK].

This is [Stacks, Tag 07JK] composed with the transport `littleChaoticSheafHAddEquiv` across the
equivalence of sites `𝒞_X ≌ 𝒞`, under the hypotheses of [Stacks, Tag 07JK]: `X` and `S` affine,
`p` nilpotent on `Γ(X, ⊤)`, and `F` locally quasi-coherent. -/
def littleChaoticCohomologyComparison (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) (j : ℕ) :
    Sheaf.H.{u + 1, u + 1}
        (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj (abelianSheaf F))) j ≃+
      cohomology S (abelianSheaf F) j :=
  littleChaoticCohomologyComparisonOfVanishing07JJ hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF) j

/-! ### The remaining step of Stacks 07JN, and the assembly -/

/-- **The Leray step of [Stacks, Tag 07JN]**, stated on the site `𝒞^∧` of [Stacks, Tag 07JL]
itself and for an arbitrary abelian coefficient sheaf `G`: the Leray degeneration

`H^j(𝒞^∧, g_*(G|_𝒞)) ≅ H^j(𝒞, G|_𝒞)`

for the direct image `g_*` of [Stacks, Tag 07JL], along the vanishing `R^p g_*(G|_𝒞) = 0` for
`p ≥ 1`.

Together with the two transports of this file and [Stacks, Tag 07JK], it gives
`Crystalline.GlobalCrystallineSituation.SmallSite.IsDirectImageCohomologyComparison`.  The
vanishing of `R^p g_*` is the derived half of [Stacks, Tag 07JL], `R^p g_* ≅ R^p lim_e`, together
with the vanishing of `R^p lim_e` under the surjectivity hypothesis (2) of [Stacks, Tag 07JN]. -/
def IsAbelianCompletedLerayComparison
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ j : ℕ, Nonempty (
    Sheaf.H.{u + 1, u + 1} (completedChaoticSheafOfPresheaf (affineSituation S hp)
        ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
          (affineSections S hp G.obj))) j ≃+
      Sheaf.H.{u + 1, u + 1}
        (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj G)) j)

/-- **The Leray step of [Stacks, Tag 07JN] for the abelian sheaf attached to a sheaf of modules**:
`IsAbelianCompletedLerayComparison` at `G = abelianSheaf F`. -/
def IsCompletedLerayComparison (F : SheafOfModules.{u} (structureSheaf S)) : Prop :=
  IsAbelianCompletedLerayComparison hp (abelianSheaf F)

omit [WholeSpacePresentation S hp] in
/-- **The direct image comparison follows from the Leray degeneration.**  Granted
`IsAbelianCompletedLerayComparison`, the proposition
`Crystalline.GlobalCrystallineSituation.SmallSite.IsDirectImageCohomologyComparison` holds for an
abelian sheaf satisfying the conclusion `Vanishing07JJ` of [Stacks, Tag 07JJ].

The composite is: the cohomology of the small model of `𝒞^∧` is the cohomology of `𝒞^∧`
(`smallSheafHAddEquivCompletedChaotic`); then the Leray degeneration, which is the hypothesis;
then the cohomology of `𝒞` is the crystalline cohomology of `G`
(`littleChaoticCohomologyComparisonOfVanishing07JJ`, which is the transport across `𝒞 ≌ 𝒞_X`
composed with the five steps of [Stacks, Tag 07JK]). -/
theorem isDirectImageCohomologyComparison_of_abelianLeray
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (h : IsAbelianCompletedLerayComparison hp G) :
    IsDirectImageCohomologyComparison S hp G := fun j => by
  obtain ⟨e⟩ := h j
  exact ⟨((smallSheafHAddEquivCompletedChaotic (affineSituation S hp) _ j).trans e).trans
    (littleChaoticCohomologyComparisonOfVanishing07JJ hp G hG j)⟩

omit [WholeSpacePresentation S hp] in
/-- **The direct image comparison follows from the Leray degeneration**, for the abelian sheaf
attached to a locally quasi-coherent sheaf of modules.  This is
`isDirectImageCohomologyComparison_of_abelianLeray` with its hypothesis discharged by
`...SmallSite.vanishing07JJ_abelianSheaf`. -/
theorem isDirectImageCohomologyComparison_of_leray
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (h : IsCompletedLerayComparison hp F) :
    IsDirectImageCohomologyComparison S hp (abelianSheaf F) :=
  isDirectImageCohomologyComparison_of_abelianLeray hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF) h

/-- **[Stacks, Tag 07JN] for the source's system `(X, T(n)_e, δ(n))`, conditional on the Leray
degeneration.**  For an abelian sheaf `G` satisfying the conclusion `Vanishing07JJ` of
[Stacks, Tag 07JJ], granted `IsAbelianCompletedLerayComparison`, the complex
`M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), G)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`.

The hypothesis `IsAbelianCompletedLerayComparison` is a step of the source's proof, not a
hypothesis of [Stacks, Tag 07JN]. -/
theorem computesCohomology_wholeSpaceSystem_of_abelianLeray
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (h : IsAbelianCompletedLerayComparison hp G) :
    ComputesCohomology (wholeSpaceSystem S hp) G :=
  computesCohomology_wholeSpaceSystem_of_directImage S hp G
    (isDirectImageCohomologyComparison_of_abelianLeray hp G hG h)

/-- **[Stacks, Tag 07JN] for the source's system `(X, T(n)_e, δ(n))`, conditional on the Leray
degeneration**, for a locally quasi-coherent sheaf of modules.  Besides
`IsCompletedLerayComparison`, a step of the source's proof, the hypotheses are those of
[Stacks, Tag 07JK]: `X` and `S` affine, `p` nilpotent on `Γ(X, ⊤)`, `F` locally quasi-coherent.
This is `computesCohomology_wholeSpaceSystem_of_abelianLeray` with its hypothesis discharged by
`...SmallSite.vanishing07JJ_abelianSheaf`. -/
theorem computesCohomology_wholeSpaceSystem_of_leray
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (h : IsCompletedLerayComparison hp F) :
    ComputesCohomology (wholeSpaceSystem S hp) (abelianSheaf F) :=
  computesCohomology_wholeSpaceSystem_of_abelianLeray hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF) h

/-! ### The Leray step with its comparison map named -/

/-- **The type of a named comparison for the Leray step of [Stacks, Tag 07JN]**: a family of
additive maps

`H^j(𝒞^∧, g_*(G|_𝒞)) →+ H^j(𝒞, G|_𝒞)`,

one in each degree. -/
abbrev IsAbelianCompletedLerayComparisonMaps
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ∀ j : ℕ, Sheaf.H.{u + 1, u + 1} (completedChaoticSheafOfPresheaf (affineSituation S hp)
      ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
        (affineSections S hp G.obj))) j →+
    Sheaf.H.{u + 1, u + 1} (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj G)) j

/-- **The Leray step of [Stacks, Tag 07JN] *via* a named comparison**: the carried family `c` is
bijective in every degree.  Equivalent, as a statement about `G`, to
`IsAbelianCompletedLerayComparison`, by
`isAbelianCompletedLerayComparison_iff_exists_via`. -/
def IsAbelianCompletedLerayComparisonVia
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (c : IsAbelianCompletedLerayComparisonMaps hp G) : Prop :=
  ∀ j : ℕ, Function.Bijective (c j)

/-- The isomorphism of degree `j` named by a bijective comparison family. -/
noncomputable def IsAbelianCompletedLerayComparisonVia.equiv
    {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
    {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    {c : IsAbelianCompletedLerayComparisonMaps hp G}
    (hc : IsAbelianCompletedLerayComparisonVia hp G c) (j : ℕ) :
    Sheaf.H.{u + 1, u + 1} (completedChaoticSheafOfPresheaf (affineSituation S hp)
        ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
          (affineSections S hp G.obj))) j ≃+
      Sheaf.H.{u + 1, u + 1} (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj G)) j :=
  AddEquiv.ofBijective (c j) (hc j)

omit [WholeSpacePresentation S hp] in
/-- **A named bijective comparison gives the Leray step of [Stacks, Tag 07JN].** -/
theorem isAbelianCompletedLerayComparison_of_via
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    {c : IsAbelianCompletedLerayComparisonMaps hp G}
    (hc : IsAbelianCompletedLerayComparisonVia hp G c) :
    IsAbelianCompletedLerayComparison hp G :=
  fun j => ⟨hc.equiv j⟩

omit [WholeSpacePresentation S hp] in
/-- **The Leray step of [Stacks, Tag 07JN] is exactly the existence of a named bijective
comparison.** -/
theorem isAbelianCompletedLerayComparison_iff_exists_via
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    IsAbelianCompletedLerayComparison hp G ↔
      ∃ c : IsAbelianCompletedLerayComparisonMaps hp G,
        IsAbelianCompletedLerayComparisonVia hp G c :=
  ⟨fun h => ⟨fun j => (h j).some.toAddMonoidHom, fun j => (h j).some.bijective⟩,
    fun ⟨_, hc⟩ => isAbelianCompletedLerayComparison_of_via hp G hc⟩

/-- **A named Leray comparison is a named comparison for the direct image.**  The composite of
`smallSheafHAddEquivCompletedChaotic`, the carried family, and
`littleChaoticCohomologyComparisonOfVanishing07JJ`, the three steps of
`isDirectImageCohomologyComparison_of_abelianLeray`. -/
def isDirectImageCohomologyComparisonMapsOfAbelianLeray
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (c : IsAbelianCompletedLerayComparisonMaps hp G) :
    IsDirectImageCohomologyComparisonMaps S hp G :=
  fun j =>
    ((littleChaoticCohomologyComparisonOfVanishing07JJ hp G hG j).toAddMonoidHom.comp
        (c j)).comp
      (smallSheafHAddEquivCompletedChaotic (affineSituation S hp) _ j).toAddMonoidHom

omit [WholeSpacePresentation S hp] in
/-- **The transport preserves bijectivity**, the two outer factors being isomorphisms. -/
theorem isDirectImageCohomologyComparisonVia_of_abelianLeray
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    {c : IsAbelianCompletedLerayComparisonMaps hp G}
    (hc : IsAbelianCompletedLerayComparisonVia hp G c) :
    IsDirectImageCohomologyComparisonVia S hp G
      (isDirectImageCohomologyComparisonMapsOfAbelianLeray hp G hG c) :=
  fun j =>
    (((littleChaoticCohomologyComparisonOfVanishing07JJ hp G hG j).bijective.comp (hc j)).comp
      (smallSheafHAddEquivCompletedChaotic (affineSituation S hp) _ j).bijective)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
