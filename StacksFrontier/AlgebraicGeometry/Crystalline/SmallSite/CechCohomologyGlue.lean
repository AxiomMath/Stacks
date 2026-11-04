module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedCechDescent
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CocontinuousGlobalSections

/-!
# The two interfaces between the Čech engine of Stacks 07JM and the complex `M(0) → M(1) → ⋯`

The proof of [Stacks, Tag 07JN] runs the Čech engine [Stacks, Tag 07JM] on the completed affine
crystalline site `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ`, where the generator `D` of [Stacks, Tag 07KI] lives,
and transports the answer back to `Cris(X/S)` along the morphism of topoi of
[Stacks, Tag 07JL].  Both halves of that transport are in the library:
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedCechDescent.lean` runs the engine
and descends it along the direct image, and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean` builds the
system `(X, T(n)_e, δ(n))` and the cosimplicial object `D(0) → D(1) → ⋯` of `Cris^∧(C/A)`.  This
file supplies the two interfaces that stood between them and the conclusion.

## The Leray/global-sections interface

The first is the comparison of global sections `Γ(𝒞^∧, g_* -) ≅ Γ(𝒞, -)` which
`Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` needs in order to turn the vanishing
`R^p g_* = 0` into a comparison of cohomology.  It is `Stacks.Sites.cocontinuousGlobalSectionsIso`,
in a generality that needs neither terminal objects nor finality nor a chaotic topology:

for **any** continuous and cocontinuous functor of sites, global sections of the cocontinuous
pushforward are global sections.

The reason is that the cocontinuous pushforward *is* the right Kan extension along `uᵒᵖ`
(`CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso` is `Iso.refl`),
global sections are the limit over the opposite site (`CategoryTheory.Sheaf.ΓNatIsoLim`), and the
limit of a right Kan extension is the limit — `CategoryTheory.Functor.ranCompLimIso`.  This is the
replacement for `Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal`, which is the same
statement for the *continuous* pushforward and asks `u` to be final; the functor
`Crystalline.crystallineToCompleted` is final as a functor of the thickening categories, so after
the two opposites its image in the sites is initial rather than final and that lemma does not
apply.

## The cosimplicial interface

The second is the identification of the Čech complex `𝓖(D) → 𝓖(D × D) → ⋯` of
[Stacks, Tag 07JM] with the complex `M(0) → M(1) → M(2) → ⋯` of
`Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplex`.  The degreewise
identification of the terms is `Crystalline.powerCechComplexXIsoSections`; matching the
differentials needs the cosimplicial structure of `D(•)`, which
`Crystalline.envelopeCosimplicial` supplies.  The chain is

* `Crystalline.generatorPowerSimplicialIso` — the simplicial object `[n] ↦ D^{n + 1}` of powers
  of the generator in `𝒞^∧`, which is what [Stacks, Tag 07JM] takes the Čech complex of, is
  isomorphic to the simplicial object `[n] ↦ D(n)` coming from `envelopeCosimplicial`;
* `Crystalline.powerCechComplexIsoEnvelopeCofaceComplex` — hence the Čech complex of `D` with
  coefficients in an abelian presheaf `𝓖` on `Cris^∧(C/A)` is the alternating coface map complex
  of the cosimplicial abelian group `[n] ↦ 𝓖(D(n))`;
* `Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplexIsoPowerCechComplex` — and for
  the presheaf `𝓖 = levelLimitSections`, `B ↦ lim_e F(B/(p)^{N + e})`, that complex *is*
  `M(0) → M(1) → M(2) → ⋯` of the system `(X, T(n)_e, δ(n))`.  The last identification is
  definitional: `sectionsComplex_wholeSpaceSystem_eq` is proved by `rfl`.

Composing with the Čech engine gives, in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`,
`addEquivSheafHHomologySectionsComplex` and the existence statement
`nonempty_addEquiv_sheafH_homology_sectionsComplex` it yields: the complex `M(0) → M(1) → ⋯`
computes the cohomology of `𝒞^∧` with coefficients in `levelLimitSections`.

The missing step, `IsCompletedSiteComparison`, also has a named form —
`IsCompletedSiteComparisonMaps` and `IsCompletedSiteComparisonVia`, equivalent to it by
`isCompletedSiteComparison_iff_exists_isCompletedSiteComparisonVia` — and composing a named
comparison for it with the named half above gives
`computesCohomologyMapsWholeSpaceSystem`, the comparison of the conclusion of
[Stacks, Tag 07JN] as a *map* rather than as a mere existence.

## What is and is not proved

No tag attribute is placed.  [Stacks, Tag 07JN] is
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
`SmallSite/WholeSpaceSystemCohomology.lean`, which carries the tag; this module records one step of
an earlier route to it, with the step it does not supply named rather than hidden.

What is proved is the two interfaces, in full and with no hypothesis beyond those of the ambient
affine crystalline situation.  This note previously said that everything mentioning the Čech
complex carried `[HasBinaryCoproducts (Crystalline.CompletedCrystallineThickening s)]`, inherited
from the Čech engine; that hypothesis is gone, the engine having been weakened to ask only for
the powers of its covering object, which [Stacks, Tag 07L4] supplies — see the module docstring
of `CompletedCechDescent.lean`.

What is **not** proved is the comparison

`H^j(𝒞^∧, levelLimitSections F) ≅ H^j(Cris(X/S), F)`,

carried below as the named hypothesis
`Crystalline.GlobalCrystallineSituation.SmallSite.IsCompletedSiteComparison`, under which
`computesCohomology_wholeSpaceSystem` concludes [Stacks, Tag 07JN]'s
`ComputesCohomology (wholeSpaceSystem S hp) F`.  The source proves that comparison in three
moves, of which two are available and one is blocked:

1. `H^j(Cris(X/S), F) ≅ H^j(𝒞, F|_𝒞)`, which is [Stacks, Tag 07JK] and is formalized as
   `Crystalline.GlobalCrystallineSituation.SmallSite.chaoticCohomologyComparisonIso`
   (`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ChaoticComparison.lean`, line 209).
2. `H^j(𝒞, F|_𝒞) ≅ H^j(𝒞^∧, g_* (F|_𝒞))`, the Leray degeneration along the vanishing
   `R^p g_* = 0`.  Its global-sections input is `gammaCompAbelianSheafPushforwardIso` below; the
   remaining hypotheses of `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` on `g_*` are
   `Crystalline.abelianSheafPushforward_additive`,
   `Crystalline.preservesFiniteLimits_abelianSheafPushforward` and
   `Crystalline.preservesInjectiveObjects_abelianSheafPushforward`; the vanishing itself is the
   business of `CompletedPushforwardVanishing.lean` and of hypothesis (2) of
   [Stacks, Tag 07JN].
3. `g_* (F|_𝒞) ≅ levelLimitSections F`, that is, the value of the direct image of
   [Stacks, Tag 07JL] at `B` is the limit `lim_e F(B/(p)^{N + e})` of its finite-level sections.
   The cofinality input that computes that Kan extension as a limit over the finite levels is no
   longer private: it lives in
   `StacksFrontier/AlgebraicGeometry/Crystalline/AffineCrystallineSite/FiniteLevelCofinality.lean`,
   and with it `Crystalline.abelianDirectImageObjObjIsoLimitFiniteLevelSections` proves
   `g_*(F)(X) ≅ lim_e F(X/(p)^{N + e})` — tagged [Stacks, Tag 07JL].

   Three things still separate that from the hypothesis `IsCompletedSiteComparison` below, and
   they are mathematics rather than visibility:
   * the two finite-level diagrams are *built* differently and have to be matched.  The 07JL
     system is a `Crystalline.FiniteLevelSystem`, whose cutoff comes from
     `DividedPowers.eventually_isDividedPowerCompletionLimit` and whose terms come from the
     `private` `finiteLevelData`; `levelLimitSections` below runs over
     `Crystalline.GlobalCrystallineSituation.SmallSite.levelFunctor`, with the uniform cutoff
     `uniformLevel` and terms `levelThickening`.  The types agree, so what is wanted is either a
     `FiniteLevelSystem` built from the uniform levels, or the statement that the two cofinal
     `ℕᵒᵖ`-diagrams have the same limit.
   * naturality in `B`: the 07JL isomorphisms are objectwise, while `levelLimitSections` is a
     functor, so a natural isomorphism needs the matching to be natural — or the comparison to be
     made only on global sections and `Sheaf.H`, which is cheaper and is all that is used here.
   * the *derived* half of 07JL, `R^p g_* ≅ R^p lim_e` for `p ≥ 1`, which the Leray step consumes
     and which is not in the library at all; only the `p = 0` value is now available.

So the one thing this file cannot supply is a computation of the direct image, not a comparison
of cohomology.  Everything else that [Stacks, Tag 07JN] needs on the completed site is here or
elsewhere in the library.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry

universe u v w

noncomputable section

/-! ### Global sections of a cocontinuous pushforward -/

namespace Stacks.ConstantSheaf

section Pushforward

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsCocontinuous J K] [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [HasLimitsOfShape Cᵒᵖ A] [HasLimitsOfShape Dᵒᵖ A]

/-- **The inverse image of a cocontinuous functor of sites carries the constant sheaf to the
constant sheaf**: `C_D ⋙ g⁻¹ ≅ C_C`.  This is the form in which the comparison of global sections
is used when one reduces `Γ(D, g_* -) ≅ Γ(C, -)` to a statement about constant sheaves; here the
implication runs the other way, by uniqueness of left adjoints applied to
`Stacks.Sites.cocontinuousGlobalSectionsIso`. -/
def constantSheafCompRestrictionIsoCocontinuous [G.IsContinuous J K] :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj K A).comp (G.sheafAdjunctionCocontinuous A J K))
      (Stacks.Sites.cocontinuousGlobalSectionsIso G A J K))
    (constantSheafΓAdj J A)

end Pushforward

end Stacks.ConstantSheaf

/-! ### A projection formula for the simplicial object of powers -/

namespace Stacks.Cohomology

variable {C : Type*} [SmallCategory C] (X : C)
  [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => X)]

/-- The structure maps of the simplicial object `[n] ↦ X^{n + 1}` of powers of an object are
characterised on the projections: the `j`-th projection out of `X^{m + 1}` pulled back along a
morphism `φ` of the simplex category is the `φ(j)`-th projection out of `X^{n + 1}`. -/
lemma powerSimplicial_map_comp_π {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (j : Fin (m.unop.len + 1)) :
    (powerSimplicial X).map φ ≫ Pi.π (fun _ : Fin (m.unop.len + 1) => X) j =
      Pi.π (fun _ : Fin (n.unop.len + 1) => X) (φ.unop.toOrderHom j) := by
  simp [powerSimplicial]

end Stacks.Cohomology

namespace Crystalline

/-! ### The cosimplicial object `D(•)` read in the site `𝒞^∧` -/

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- **The cosimplicial object `D(0) → D(1) → ⋯` of [Stacks, Tag 07L4], read as a simplicial
object of the site `𝒞^∧`.**  Taking opposites turns the cosimplicial object
`Crystalline.envelopeCosimplicial` of `Cris^∧(C/A)` into a simplicial object of
`(Cris^∧(C/A))ᵒᵖ`, and `CategoryTheory.AsSmall.up` carries it into the small model
`Crystalline.CompletedSmallSite` on which [Stacks, Tag 07JM] is run. -/
def envelopeSimplicialSite : SimplicialObject (CompletedSmallSite.{u, v, max u w} s) :=
  (envelopeCosimplicial s g hg).op ⋙ AsSmall.up

/-- The degree-`n` object of `Crystalline.envelopeSimplicialSite` is the envelope thickening
`D(n)`, viewed in the small site. -/
@[simp]
lemma envelopeSimplicialSite_obj (n : SimplexCategoryᵒᵖ) :
    (envelopeSimplicialSite s g hg).obj n =
      AsSmall.up.obj (op (tensorPowerEnvelopeThickening s g hg n.unop.len).thickening) :=
  rfl

/-- The fan of [Stacks, Tag 07L4] in degree `n`, with its apex spelled as the degree-`n` part of
`Crystalline.envelopeSimplicialSite`.  This is `Crystalline.generatorPowerFan` with the apex
written in the form the simplicial structure maps use, which is what lets the two be composed. -/
def envelopeFan (n : SimplexCategoryᵒᵖ) :
    Fan (fun _ : Fin (n.unop.len + 1) => generator s g hg) :=
  Fan.mk ((envelopeSimplicialSite s g hg).obj n)
    (fun j => (generatorPowerFan s g hg n.unop.len).proj j)

/-- The `j`-th projection of `Crystalline.envelopeFan` is the `j`-th projection of
`Crystalline.generatorPowerFan`. -/
@[simp]
lemma envelopeFan_proj (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
    (envelopeFan s g hg n).proj j = (generatorPowerFan s g hg n.unop.len).proj j :=
  rfl

/-- **The simplicial structure maps of `D(•)` in the site are characterised on the projections**:
in `𝒞^∧` the map `D(n) ⟶ D(m)` induced by `φ : ⦋m⦌ ⟶ ⦋n⦌` followed by the `j`-th projection of
`D(m)` is the `φ(j)`-th projection of `D(n)`.  This is
`Crystalline.envelopeCosimplicial_coprojection_comp_map` with every opposite taken. -/
lemma envelopeSimplicialSite_map_comp_proj {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (j : Fin (m.unop.len + 1)) :
    (envelopeSimplicialSite s g hg).map φ ≫ (envelopeFan s g hg m).proj j =
      (envelopeFan s g hg n).proj (φ.unop.toOrderHom j) :=
  (congrArg ULift.up) <| Quiver.Hom.unop_inj <|
    envelopeCosimplicial_coprojection_comp_map s g hg φ.unop j

section Cech

/-- `D(n)` is the `(n + 1)`-fold power of the generator, with the apex spelled as the degree-`n`
part of `Crystalline.envelopeSimplicialSite`.  This is
`Crystalline.isLimitGeneratorPowerFan`. -/
def isLimitEnvelopeFan (n : SimplexCategoryᵒᵖ) : IsLimit (envelopeFan s g hg n) :=
  isLimitGeneratorPowerFan s g hg n.unop.len

/-- **`D^{n + 1} ≅ D(n)` in the site `𝒞^∧`**, in degree `n`: the degree-`n` part of the
simplicial object of powers of the generator, which is what the Čech complex of
[Stacks, Tag 07JM] is built from, is the degree-`n` part of `D(•)`. -/
def generatorPowerSimplicialIsoApp (n : SimplexCategoryᵒᵖ) :
    (Stacks.Cohomology.powerSimplicial (generator s g hg)).obj n ≅
      (envelopeSimplicialSite s g hg).obj n :=
  generatorPowerIso s g hg n.unop.len

/-- The isomorphism `Crystalline.generatorPowerSimplicialIsoApp` followed by the `j`-th projection
of `D(n)` is the `j`-th projection of the product `D^{n + 1}`. -/
@[simp]
lemma generatorPowerSimplicialIsoApp_hom_comp_proj (n : SimplexCategoryᵒᵖ)
    (j : Fin (n.unop.len + 1)) :
    (generatorPowerSimplicialIsoApp s g hg n).hom ≫ (envelopeFan s g hg n).proj j =
      Pi.π (fun _ : Fin (n.unop.len + 1) => generator s g hg) j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- **The simplicial object of powers of the generator is `D(•)`.**  The isomorphisms
`D^{n + 1} ≅ D(n)` of [Stacks, Tag 07L4] are compatible with the simplicial structure maps: both
sides are determined by their projections to `D`, and on the `j`-th projection both act by the
`φ(j)`-th projection.

This is the identification the match of the Čech complex of [Stacks, Tag 07JM] with the complex
`M(0) → M(1) → ⋯` was waiting for; see the module docstring. -/
def generatorPowerSimplicialIso :
    Stacks.Cohomology.powerSimplicial (generator s g hg) ≅ envelopeSimplicialSite s g hg :=
  NatIso.ofComponents (generatorPowerSimplicialIsoApp s g hg) (by
    intro n m φ
    refine Fan.IsLimit.hom_ext (isLimitEnvelopeFan s g hg m) _ _ fun j => ?_
    have hL : (Stacks.Cohomology.powerSimplicial (generator s g hg)).map φ ≫
        ((generatorPowerSimplicialIsoApp s g hg m).hom ≫ (envelopeFan s g hg m).proj j) =
        Pi.π (fun _ : Fin (n.unop.len + 1) => generator s g hg) (φ.unop.toOrderHom j) := by
      rw [generatorPowerSimplicialIsoApp_hom_comp_proj,
        Stacks.Cohomology.powerSimplicial_map_comp_π]
    have hR : (generatorPowerSimplicialIsoApp s g hg n).hom ≫
        ((envelopeSimplicialSite s g hg).map φ ≫ (envelopeFan s g hg m).proj j) =
        Pi.π (fun _ : Fin (n.unop.len + 1) => generator s g hg) (φ.unop.toOrderHom j) := by
      rw [envelopeSimplicialSite_map_comp_proj, generatorPowerSimplicialIsoApp_hom_comp_proj]
    exact ((Category.assoc _ _ _).trans hL).trans (((Category.assoc _ _ _).trans hR).symm))

/-- `Crystalline.generatorPowerSimplicialIso` read as an isomorphism of cosimplicial objects of
`(𝒞^∧)ᵒᵖ`, which is the shape in which an abelian presheaf is evaluated on it. -/
def envelopeRightOpIso :
    (Stacks.Cohomology.powerSimplicial (generator s g hg)).rightOp ≅
      (envelopeSimplicialSite s g hg).rightOp :=
  NatIso.ofComponents
    (fun n => ((generatorPowerSimplicialIso s g hg).app (op n)).op.symm)
    fun φ => Quiver.Hom.unop_inj ((generatorPowerSimplicialIso s g hg).inv.naturality φ.op).symm

/-- **The Čech complex of [Stacks, Tag 07JM] is the alternating coface map complex of
`[n] ↦ 𝓖(D(n))`.**  For an abelian presheaf `𝓖` on `Cris^∧(C/A)`, read as an abelian sheaf on the
small model of `𝒞^∧`, the complex

`𝓖(D) → 𝓖(D × D) → 𝓖(D × D × D) → ⋯`

of [Stacks, Tag 07JM] is the complex attached to the cosimplicial abelian group
`envelopeCosimplicial ⋙ 𝓖`, that is, to `𝓖(D(0)) → 𝓖(D(1)) → ⋯`.

The degreewise statement is `Crystalline.powerCechComplexXIsoSections`; what is added here is the
match of the differentials, which is the content of
`Crystalline.generatorPowerSimplicialIso`. -/
def powerCechComplexIsoEnvelopeCofaceComplex
    (𝓖 : CompletedCrystallineThickening.{u, v, max u w} s ⥤ Ab.{max u v (max u w + 1)}) :
    Stacks.Cohomology.powerCechComplex (smallSheafOfPresheaf s 𝓖).obj (generator s g hg) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex Ab.{max u v (max u w + 1)}).obj
        (envelopeCosimplicial s g hg ⋙ 𝓖) :=
  (AlgebraicTopology.alternatingCofaceMapComplex Ab.{max u v (max u w + 1)}).mapIso
    (Functor.isoWhiskerRight (envelopeRightOpIso s g hg) (smallSheafOfPresheaf s 𝓖).obj)

/-- **The comparison of [Stacks, Tag 07JM] in cosimplicial form, named.**  The isomorphism of
`H^n(𝒞^∧, 𝓖)` with the degree-`n` cohomology of `𝓖(D(0)) → 𝓖(D(1)) → ⋯`, as a `def`: the named
comparison on the powers of the generator, followed by the identification of the two complexes.

The existence statement is `nonempty_addEquiv_sheafH_homology_envelopeCofaceComplex` below. -/
def addEquivSheafHHomologyEnvelopeCofaceComplex
    (𝓖 : CompletedCrystallineThickening.{u, v, max u w} s ⥤ Ab.{max u v (max u w + 1)}) (n : ℕ) :
    Sheaf.H (smallSheafOfPresheaf s 𝓖) n ≃+
      ((AlgebraicTopology.alternatingCofaceMapComplex Ab.{max u v (max u w + 1)}).obj
        (envelopeCosimplicial s g hg ⋙ 𝓖)).homology n :=
  (addEquivSheafHHomologyPowerCechComplexGenerator s g hg (smallSheafOfPresheaf s 𝓖) n).trans
    ((HomologicalComplex.homologyFunctor Ab.{max u v (max u w + 1)}
      (ComplexShape.up ℕ) n).mapIso
        (powerCechComplexIsoEnvelopeCofaceComplex s g hg 𝓖)).addCommGroupIsoToAddEquiv

/-- **[Stacks, Tag 07JM] on the completed affine crystalline site, in cosimplicial form.**  For
an abelian presheaf `𝓖` on `Cris^∧(C/A)` the cohomology `H^n(𝒞^∧, 𝓖)` is the degree-`n`
cohomology of the complex `𝓖(D(0)) → 𝓖(D(1)) → 𝓖(D(2)) → ⋯` attached to the cosimplicial object
`D(•)` of [Stacks, Tag 07L4].

This is `Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_generator` with the
powers of the generator replaced by the objects `D(n)` and their cosimplicial structure.

The comparison is `Crystalline.addEquivSheafHHomologyEnvelopeCofaceComplex` below. -/
theorem nonempty_addEquiv_sheafH_homology_envelopeCofaceComplex
    (𝓖 : CompletedCrystallineThickening.{u, v, max u w} s ⥤ Ab.{max u v (max u w + 1)}) (n : ℕ) :
    Nonempty (Sheaf.H (smallSheafOfPresheaf s 𝓖) n ≃+
      ((AlgebraicTopology.alternatingCofaceMapComplex Ab.{max u v (max u w + 1)}).obj
        (envelopeCosimplicial s g hg ⋙ 𝓖)).homology n) :=
  ⟨addEquivSheafHHomologyEnvelopeCofaceComplex s g hg 𝓖 n⟩

end Cech

/-! ### The Leray interface for the direct image of Stacks 07JL -/

/-- **`Γ(𝒞^∧, g_* -) ≅ Γ(𝒞, -)` for the direct image of [Stacks, Tag 07JL].**  This is the
comparison of global sections that `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` asks for in
order to turn the vanishing `R^p g_* = 0` into the Leray comparison
`H^j(𝒞, 𝓕) ≅ H^j(𝒞^∧, g_* 𝓕)`; the remaining hypotheses of that lemma on `g_*` are supplied by
`Crystalline.abelianSheafPushforward_additive`,
`Crystalline.preservesFiniteLimits_abelianSheafPushforward` and
`Crystalline.preservesInjectiveObjects_abelianSheafPushforward`.

It is the general `Stacks.Sites.cocontinuousGlobalSectionsIso` instantiated at the
functor of [Stacks, Tag 07JL]; no property of the crystalline categories is used. -/
def gammaCompAbelianSheafPushforwardIso :
    abelianSheafPushforward.{u, v, w} s ⋙
        Sheaf.Γ (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} s)ᵒᵖ)
          Ab.{max u v (w + 1)} ≅
      Sheaf.Γ (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} s)ᵒᵖ)
        Ab.{max u v (w + 1)} :=
  Stacks.Sites.cocontinuousGlobalSectionsIso _ _ _ _

/-- **The inverse image of [Stacks, Tag 07JL] carries the constant abelian sheaf of `𝒞^∧` to the
constant abelian sheaf of `𝒞`.**  This is the statement to which uniqueness of right adjoints
reduces `gammaCompAbelianSheafPushforwardIso`; here it is deduced from it. -/
def constantSheafCompRestrictionIso :
    constantSheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} s)ᵒᵖ)
          Ab.{max u v (w + 1)} ⋙
        (crystallineToCompleted s).op.sheafPushforwardContinuous Ab.{max u v (w + 1)} ⊥ ⊥ ≅
      constantSheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} s)ᵒᵖ)
        Ab.{max u v (w + 1)} :=
  Stacks.ConstantSheaf.constantSheafCompRestrictionIsoCocontinuous _ _ _ _

end Crystalline

/-! ### `M(0) → M(1) → M(2) → ⋯` as the Čech complex of the generator -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable (S : GlobalCrystallineSituation.{u}) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The presheaf `B ↦ lim_e F(B/(p)^{N + e})` on `Cris^∧(C/A)`** attached to an abelian
presheaf `F` on `Cris(X/S)`: the sections of `F`, read on the little affine crystalline category
through the equivalence of
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, evaluated on the finite
levels of a completed thickening and taken to the limit.

This is the presheaf whose values on the objects `D(n)` are the terms `M(n)` of
[Stacks, Tag 07JN], by `sectionsComplex_wholeSpaceSystem_eq`.  The source identifies it with the
direct image `g_* F` of [Stacks, Tag 07JL]; that identification is not available here, and is the
one step of [Stacks, Tag 07JN] this file does not supply — see the module docstring. -/
def levelLimitSections (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    CompletedCrystallineThickening.{u, u, u} (affineSituation S hp) ⥤ AddCommGrpCat.{u + 1} :=
  Functor.curryObj (levelFunctor (affineSituation S hp)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (affineSections S hp F) ⋙ lim

/-- The value of `levelLimitSections` at a completed thickening `B` is the limit over `e` of the
sections of `F` on the finite levels of `B`. -/
@[simp]
lemma levelLimitSections_obj (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) :
    (levelLimitSections S hp F).obj B =
      limit ((Functor.curryObj (levelFunctor (affineSituation S hp))).obj B ⋙
        affineSections S hp F) :=
  rfl

/-- **The complex `M(0) → M(1) → M(2) → ⋯` of the system `(X, T(n)_e, δ(n))` is the complex of
the cosimplicial abelian group `[n] ↦ (lim_e F(B/(p)^{N + e}))(D(n))`.**  Both sides are the
alternating coface map complex of the same cosimplicial abelian group, so the identification is
definitional: the system `(X, T(n)_e, δ(n))` is by construction the finite levels of `D(•)`
carried across the affine-to-global equivalence. -/
theorem sectionsComplex_wholeSpaceSystem_eq
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    sectionsComplex (wholeSpaceSystem S hp) F =
      (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
        (envelopeCosimplicial (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) ⋙ levelLimitSections S hp F) :=
  rfl

section Cech

/-- **The complex `M(0) → M(1) → M(2) → ⋯` of [Stacks, Tag 07JN] is the Čech complex of the
generator `D` of [Stacks, Tag 07KI]**, with coefficients in the abelian presheaf
`B ↦ lim_e F(B/(p)^{N + e})` of `Crystalline.levelLimitSections` on `Cris^∧(C/A)`.

This is the second of the two interfaces of this file, and it is exactly what was owed: the
degreewise identification of the terms was `Crystalline.powerCechComplexXIsoSections`, and the
differentials are matched by `Crystalline.generatorPowerSimplicialIso` through
`Crystalline.powerCechComplexIsoEnvelopeCofaceComplex`. -/
def sectionsComplexIsoPowerCechComplex (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    sectionsComplex (wholeSpaceSystem S hp) F ≅
      Stacks.Cohomology.powerCechComplex
        (smallSheafOfPresheaf (affineSituation S hp) (levelLimitSections S hp F)).obj
        (generator (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp)) :=
  (powerCechComplexIsoEnvelopeCofaceComplex (affineSituation S hp) (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) (levelLimitSections S hp F)).symm

/-- **The comparison of `M(0) → M(1) → M(2) → ⋯` with the cohomology of the completed site,
named.**  The isomorphism

`H^n(𝒞^∧, lim_e F(B/(p)^{N + e})) ≅ H^n(M(0) → M(1) → ⋯)`

as a `def`: it is `addEquivSheafHHomologyEnvelopeCofaceComplex` at the canonical presentation of
`C`, read through `sectionsComplexIsoPowerCechComplex`.

This is the half of [Stacks, Tag 07JN] that the library proves, and naming it is what lets the
whole tag's comparison be assembled as a *map* rather than asserted to exist; see
`computesCohomologyMapsWholeSpaceSystem`. -/
def addEquivSheafHHomologySectionsComplex
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
        (levelLimitSections S hp F)) n ≃+
      (sectionsComplex (wholeSpaceSystem S hp) F).homology n :=
  addEquivSheafHHomologyEnvelopeCofaceComplex (affineSituation S hp)
    (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp)
    (levelLimitSections S hp F) n

/-- **`M(0) → M(1) → M(2) → ⋯` computes the cohomology of the completed site.**  For every `n`
the degree-`n` cohomology of the complex `M(0) → M(1) → ⋯` of the system `(X, T(n)_e, δ(n))` is
`H^n(𝒞^∧, lim_e F(B/(p)^{N + e}))`.

This is [Stacks, Tag 07JM] run on `Cris^∧(C/A)` — where the generator `D` of
[Stacks, Tag 07KI] lives — and matched with the complex of [Stacks, Tag 07JN].  It is everything
[Stacks, Tag 07JN] asserts except the comparison of `H^n(𝒞^∧, lim_e F(B/(p)^{N + e}))` with
`H^n(Cris(X/S), F)`, which is `IsCompletedSiteComparison` below.

The comparison is named: `addEquivSheafHHomologySectionsComplex` below. -/
theorem nonempty_addEquiv_sheafH_homology_sectionsComplex
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    Nonempty (Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
        (levelLimitSections S hp F)) n ≃+
      (sectionsComplex (wholeSpaceSystem S hp) F).homology n) :=
  ⟨addEquivSheafHHomologySectionsComplex S hp F n⟩

/-- **The one step of [Stacks, Tag 07JN] that is not available**, as an explicit hypothesis: the
cohomology of the completed site `𝒞^∧` with coefficients in the presheaf
`B ↦ lim_e F(B/(p)^{N + e})` is the cohomology of `Cris(X/S)` with coefficients in `F`.

The source proves this by combining [Stacks, Tag 07JK], the Leray degeneration along
`R^p g_* = 0` — whose global-sections input is `Crystalline.gammaCompAbelianSheafPushforwardIso`
and whose vanishing input comes from hypothesis (2) of [Stacks, Tag 07JN] — and the computation
of the direct image of [Stacks, Tag 07JL] as the limit over the finite levels.  It is the last of
these that is blocked; see the module docstring for the `private` declarations involved. -/
def IsCompletedSiteComparison (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ j : ℕ, Nonempty (Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
    (levelLimitSections S hp F.obj)) j ≃+ cohomology S F j)

/-- **[Stacks, Tag 07JN] for the system `(X, T(n)_e, δ(n))`, conditional on
`IsCompletedSiteComparison`.**  Granted the comparison of the cohomology of the completed site
with the cohomology of `Cris(X/S)`, the complex `M(0) → M(1) → M(2) → ⋯` computes
`RΓ(Cris(X/S), F)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`.

No tag attribute is placed: the hypothesis is a step of the source's proof, not a hypothesis of
[Stacks, Tag 07JN].  The two hypotheses the source does make on `F` — local quasi-coherence and
`CohomologyRestriction.IsSurjectiveComparison` — enter only through that step, in the form of the
vanishing `R^p g_* = 0`, and so do not appear here.

The comparison of the conclusion is named, and it is not an arbitrary one:
`computesCohomologyMapsWholeSpaceSystem` builds it out of a named comparison for the missing
step and the named half the library proves. -/
theorem computesCohomology_wholeSpaceSystem
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : IsCompletedSiteComparison S hp F) :
    ComputesCohomology (wholeSpaceSystem S hp) F := fun j => by
  obtain ⟨c⟩ := h j
  exact ⟨((addEquivSheafHHomologySectionsComplex S hp F.obj j).symm.trans c).toAddCommGrpIso⟩

/-! ### The missing step of [Stacks, Tag 07JN] with its comparison map named -/

/-- **The type of a named comparison for the missing step of [Stacks, Tag 07JN]**: a family of
additive maps

`H^j(𝒞^∧, lim_e F(B/(p)^{N + e})) →+ H^j(Cris(X/S), F)`,

one in each degree.

`IsCompletedSiteComparison` asserts that the two groups are *isomorphic* in each degree, which
names no map; a term of this type is a named map, and `IsCompletedSiteComparisonVia` is the
assertion about it that the step amounts to. -/
abbrev IsCompletedSiteComparisonMaps (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ∀ j : ℕ, Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
    (levelLimitSections S hp F.obj)) j →+ cohomology S F j

/-- **The missing step of [Stacks, Tag 07JN] *via* a named comparison**: the carried family `c`
is bijective in every degree.

By `isCompletedSiteComparison_iff_exists_isCompletedSiteComparisonVia` this is, as a statement
about `F`, exactly `IsCompletedSiteComparison`; what it adds is a name for the comparison, which
an existence statement about isomorphisms cannot supply. -/
def IsCompletedSiteComparisonVia (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (c : IsCompletedSiteComparisonMaps S hp F) : Prop :=
  ∀ j : ℕ, Function.Bijective (c j)

/-- The isomorphism of degree `j` named by a bijective comparison family. -/
noncomputable def IsCompletedSiteComparisonVia.equiv
    {S : GlobalCrystallineSituation.{u}} {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
    [IsAffine S.X] [IsAffine S.S.scheme] {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    {c : IsCompletedSiteComparisonMaps S hp F} (hc : IsCompletedSiteComparisonVia S hp F c)
    (j : ℕ) :
    Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
      (levelLimitSections S hp F.obj)) j ≃+ cohomology S F j :=
  AddEquiv.ofBijective (c j) (hc j)

/-- **A named bijective comparison gives the missing step of [Stacks, Tag 07JN]**: forget the
map and keep the isomorphism. -/
theorem isCompletedSiteComparison_of_via
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    {c : IsCompletedSiteComparisonMaps S hp F} (hc : IsCompletedSiteComparisonVia S hp F c) :
    IsCompletedSiteComparison S hp F :=
  fun j => ⟨hc.equiv j⟩

/-- **The missing step of [Stacks, Tag 07JN] is exactly the existence of a named bijective
comparison.**  So passing to the named shape neither weakens nor strengthens the statement about
`F`; it only gives the comparison a name, and a statement about a *given* map can be discharged
only by a named one. -/
theorem isCompletedSiteComparison_iff_exists_isCompletedSiteComparisonVia
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    IsCompletedSiteComparison S hp F ↔
      ∃ c : IsCompletedSiteComparisonMaps S hp F, IsCompletedSiteComparisonVia S hp F c :=
  ⟨fun h => ⟨fun j => (h j).some.toAddMonoidHom, fun j => (h j).some.bijective⟩,
    fun ⟨_, hc⟩ => isCompletedSiteComparison_of_via S hp F hc⟩

/-- **The comparison of the conclusion of [Stacks, Tag 07JN], as a map.**  Given a named
comparison `c` for the one step the library does not prove, this is the comparison

`H^j(M(0) → M(1) → ⋯) ⟶ H^j(Cris(X/S), F)`

of the tag's conclusion: the named half the library *does* prove
(`addEquivSheafHHomologySectionsComplex`), inverted, followed by `c`.

This is the point of naming the chain.  `computesCohomology_wholeSpaceSystem` produces a
`Nonempty`, so the isomorphism it asserts is no particular map and cannot be compared with any
given one; this is a map, and `computesCohomologyVia_computesCohomologyMapsWholeSpaceSystem`
says it is invertible exactly when `c` is. -/
noncomputable def computesCohomologyMapsWholeSpaceSystem
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (c : IsCompletedSiteComparisonMaps S hp F) (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) F.obj).homology j ⟶
      (cohomologyFunctor S j).obj F :=
  AddCommGrpCat.ofHom
    ((c j).comp (addEquivSheafHHomologySectionsComplex S hp F.obj j).symm.toAddMonoidHom)

/-- **The named comparison of the conclusion of [Stacks, Tag 07JN] is invertible as soon as the
named comparison of the missing step is.**  This is the composition step that a `Nonempty`
destroys: the two factors are named, so the composite is a named map, and its invertibility
follows from theirs. -/
theorem isIso_computesCohomologyMapsWholeSpaceSystem
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    {c : IsCompletedSiteComparisonMaps S hp F} (hc : IsCompletedSiteComparisonVia S hp F c)
    (j : ℕ) :
    IsIso (computesCohomologyMapsWholeSpaceSystem S hp F c j) := by
  let e : (sectionsComplex (wholeSpaceSystem S hp) F.obj).homology j ≅
      (cohomologyFunctor S j).obj F :=
    ((addEquivSheafHHomologySectionsComplex S hp F.obj j).symm.trans
      (hc.equiv j)).toAddCommGrpIso
  have he : computesCohomologyMapsWholeSpaceSystem S hp F c j = e.hom := rfl
  rw [he]
  infer_instance

end Cech

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
