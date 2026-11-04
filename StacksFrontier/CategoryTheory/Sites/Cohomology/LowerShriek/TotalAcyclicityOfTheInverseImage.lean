module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Limits.Finite.PreservesWidePullbacks
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of an injective module is totally acyclic

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) → Sh(D)` be the
corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. If the lower shriek functor `g_!^{Sh} : Sh(C) → Sh(D)` on sheaves of *sets* commutes
with fibre products, then `g^{-1}I` is totally acyclic in the sense of Stacks 072Y. This is
Stacks 0D6Y.

The proof is the one in the source, run through the criterion of Stacks 07A1
(`Stacks.Cohomology.isTotallyAcyclic_iff`). Condition (1), the vanishing of `H^p(U, g^{-1}I)` on
every object of `C`, is Stacks 0D6X. Condition (2) is the exactness, for every surjection
`K' → K` of sheaves of sets on `C`, of the extended Čech complex
`0 → H^0(K, g^{-1}I) → H^0(K', g^{-1}I) → H^0(K' ×_K K', g^{-1}I) → …`. For that, `g_!^{Sh}`
being a left adjoint carries the surjection `K' → K` to a surjection `g_!^{Sh}K' → g_!^{Sh}K`,
and adjunction identifies `H^0` of an iterated fibre power of `K'` over `K` with coefficients in
`g^{-1}I` with `H^0` of its image under `g_!^{Sh}`, with coefficients in `I`; the hypothesis on
`g_!^{Sh}` turns that image into the corresponding iterated fibre power of `g_!^{Sh}K'` over
`g_!^{Sh}K`. Since `I` is injective it is itself totally acyclic — the content of Stacks 072Z
applied to the identity — so the converse half of Stacks 07A1 makes the complex on `D` exact,
and transporting back gives condition (2).

## Main results

* `ChainComplex.homComplexFunctorAdjunctionIso`: for an adjunction `L ⊣ R` of additive functors,
  the Hom complex of a chain complex with coefficients in `R I` is the Hom complex of its image
  under `L` with coefficients in `I`.
* `Stacks.Cohomology.DerivedLowerShriek.freeAbelianSheafPullbackIso`: the free abelian sheaf
  functor commutes with lower shriek, both sides being left adjoint to restriction followed by
  forgetting the group structure.
* `Stacks.Cohomology.DerivedLowerShriek.cechComplexExactPos_inverseImage`: condition (2) of
  Stacks 07A1 for the inverse image of an injective module.
* `Stacks.Cohomology.DerivedLowerShriek.vanishesOnObjects_inverseImage`: condition (1), which is
  Stacks 0D6X.
* `Stacks.Cohomology.DerivedLowerShriek.vanishesOnObjects_inverseImage_sheaf`: condition (1) for
  the inverse image of an injective *abelian sheaf*, the case `O_D = ℤ` of Stacks 0D6X. The
  target site is an arbitrary site rather than a ringed one, no structure sheaf entering.
* `Stacks.Cohomology.DerivedLowerShriek.isTotallyAcyclic_of_injective_module`: an injective
  module is totally acyclic, which is Stacks 072Z applied to the identity.
* `Stacks.Cohomology.DerivedLowerShriek.isTotallyAcyclic_inverseImage_of_injective`:
  **Stacks 0D6Y**.
* `Stacks.Cohomology.DerivedLowerShriek.isTotallyAcyclic_pushforwardModule_of_injective`:
  the same conclusion read on the inverse image module itself.
* `Stacks.Cohomology.DerivedLowerShriek.isTotallyAcyclic_inverseImage_of_injective_of_pullbacks`:
  Stacks 0D6Y under the sufficient condition of its footnote — `C` has finite connected limits
  and `u` commutes with them — which supplies the hypothesis on `g_!^{Sh}` by Sites,
  Lemma 00XS.
* `Stacks.Cohomology.DerivedLowerShriek.isTotallyAcyclic_inverseImage_of_injective_of_cospans`:
  Stacks 0D6Y with the hypothesis the source states, that `g_!^{Sh}` commute with binary fibre
  products.

## Implementation notes

**The hypothesis on `g_!^{Sh}`.** The source asks that `g_!^{Sh}` commute with fibre products,
meaning binary ones; what the proof consumes is commutation with the iterated fibre products
`K' ×_K … ×_K K'` out of which the source's displayed complex is built, that is, preservation
of the wide pullbacks `WidePullbackShape (Fin (n + 1))`. The two agree: an iterated fibre
product is a fibre product of one fewer of its factors against the remaining one, so
`CategoryTheory.Limits.preservesLimitsOfShape_widePullbackShape` derives the iterated form from
the binary one over any category having fibre products, and `Sh(C)` has them. The three
statements below in the wide form therefore also hold in the source's; this is
`isTotallyAcyclic_inverseImage_of_injective_of_cospans`. The sufficient condition of the
footnote gives the wide form directly, without that reduction — each
`WidePullbackShape (Fin (n + 1))` is a finite connected shape, and Sites, Lemma 00XS makes
`g_!^{Sh}` preserve limits of every such shape.

**Condition (1).** Stacks 0D6X is available in this library as
`Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`, for a ringed site — a
structure sheaf with values in commutative rings — together with a cofinal system of coverings
whose iterated fibre products exist and are preserved by `u`. That system is the one furnished by
`Stacks.Sites.PreservesCoveringPullbacks`, which is condition (2) of the Stacks definition of a
continuous functor of sites, Sites, Definition 00WV; the image coverings' iterated fibre products
and the invertibility of the comparison maps follow from
`Stacks.Sites.preservesLimit_fibreProducts_overPost`.

**Condition (2).** No Čech complex of a covering appears: the complex of Stacks 07A1 is the Hom
complex of the free abelian sheaf complex of the Čech nerve of a surjection of sheaves of sets,
and the whole transport is a chain of isomorphisms of functors. The free abelian sheaf functor
commutes with lower shriek because `FA_C ⋙ g_!` and `g_!^{Sh} ⋙ FA_D` are both left adjoint to
`g^{-1}` followed by forgetting the group structure, those two composites being equal on the
nose; the Čech nerve commutes with `g_!^{Sh}` by `CategoryTheory.Arrow.cechNerveComp`, which is
where the hypothesis is used; and the alternating face map complex commutes with the additive
functor `g_!`. The resulting isomorphism of chain complexes of abelian sheaves on `D` is turned
into an isomorphism of the two Hom complexes by `ChainComplex.homComplexFunctorAdjunctionIso`
and `ChainComplex.homComplexFunctorMapIso`, and exactness transports along it.

**Universes.** Both sites are small and their objects, morphisms, the structure sheaf, the module
sections and the `Ext`-groups lie in one universe `w`, as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.PullbackOfInjectiveAcyclic`. This
is forced by the inputs: the criterion of Stacks 03F9 behind Stacks 0D6X needs the coefficient
universe to contain the morphism universe and the site to be small, and
`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree` is stated for a small site with all of its
universes equal.

**Cocontinuity** of `u` is a hypothesis of Stacks 0D6Y and is what makes restriction along `u`
the inverse image `g^{-1}` of a morphism of topoi (Sites, Lemma 00XR), but no step of the proof
uses it: continuity alone makes restriction land in sheaves and have a left adjoint. It is
therefore `omit`ted from the three statements of the tag below, which are correspondingly more
general than the source's.

## References

* [Stacks Project, Tag 0D6Y](https://stacks.math.columbia.edu/tag/0D6Y)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks Project, Tag 072Y](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 00XS](https://stacks.math.columbia.edu/tag/00XS)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe v u u' w

namespace ChainComplex

section

variable {W : Type u} [Category.{v} W] [Preadditive W]
  {W' : Type u'} [Category.{v} W'] [Preadditive W']

/-- **The Hom complex of a chain complex transports along an adjunction.** For an adjunction
`L ⊣ R` of additive functors, `Hom(s_•, R I)` is `Hom((L s)_•, I)`: degreewise this is the
additive form `CategoryTheory.Adjunction.homAddEquiv` of the adjunction isomorphism, and it
commutes with the differentials because that isomorphism is natural in the source. -/
def homComplexFunctorAdjunctionIso {L : W ⥤ W'} {R : W' ⥤ W} (adj : L ⊣ R) [L.Additive]
    (s : ChainComplex W ℕ) (I : W') :
    (homComplexFunctor s).obj (R.obj I) ≅
      (homComplexFunctor
        ((L.mapHomologicalComplex (ComplexShape.down ℕ)).obj s)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (adj.homAddEquiv (s.X n) I).symm.toAddCommGrpIso)
    (fun n m _ ↦ by
      ext a
      exact (adj.homEquiv_naturality_left_symm (s.d m n) a).symm)

/-- **An isomorphism of chain complexes induces one of their Hom complexes**, contravariantly. -/
def homComplexFunctorMapIso {s₁ s₂ : ChainComplex W ℕ} (e : s₁ ≅ s₂) (I : W) :
    (homComplexFunctor s₂).obj I ≅ (homComplexFunctor s₁).obj I :=
  ((preadditiveYoneda.obj I).mapHomologicalComplex _).mapIso
    ((HomologicalComplex.opFunctor W (ComplexShape.down ℕ)).mapIso e.op)

end

end ChainComplex

namespace Stacks.Cohomology.DerivedLowerShriek

section LowerShriek

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K]

/-- Lower shriek on abelian sheaves is additive, being a left adjoint of the additive
restriction functor. -/
instance additive_sheafPullback_addCommGrpCat :
    (u.sheafPullback AddCommGrpCat.{w} J K).Additive :=
  (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).left_adjoint_additive

/-- **The free abelian sheaf functor commutes with lower shriek.** Both `FA_C ⋙ g_!` and
`g_!^{Sh} ⋙ FA_D` are left adjoint to the composite of `g^{-1}` with the functor taking an
abelian sheaf to its underlying sheaf of sets, and that composite does not depend on the order
in which restriction and forgetting are performed. -/
def freeAbelianSheafPullbackIso :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free : Sheaf J (Type w) ⥤ _) ⋙
        u.sheafPullback AddCommGrpCat.{w} J K ≅
      u.sheafPullback (Type w) J K ⋙ Sheaf.composeAndSheafify K AddCommGrpCat.free :=
  Adjunction.leftAdjointUniq
    ((Sheaf.adjunction J AddCommGrpCat.adj).comp
      (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K))
    ((u.sheafAdjunctionContinuous (Type w) J K).comp (Sheaf.adjunction K AddCommGrpCat.adj))

variable [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
  (u.sheafPullback (Type w) J K)]

/-- **Lower shriek carries the free abelian sheaf complex of a Čech nerve to the free abelian
sheaf complex of the Čech nerve of the image map.** The three steps are: the alternating face
map complex commutes with the additive functor `g_!`; the free abelian sheaf functor commutes
with `g_!`; and the Čech nerve commutes with `g_!^{Sh}`, which is the hypothesis that
`g_!^{Sh}` preserve the iterated fibre products. -/
def cechFreeAbelianSheafComplexPullbackIso {K' K₀ : Sheaf J (Type w)} (g : K' ⟶ K₀) :
    ((u.sheafPullback AddCommGrpCat.{w} J K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk g.hom).cechNerve) ≅
      (SimplicialObject.freeAbelianSheafComplexFunctor K).obj
        (Arrow.mk ((u.sheafPullback (Type w) J K).map g).hom).cechNerve :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (u.sheafPullback AddCommGrpCat.{w} J K)).app
      ((Arrow.mk g.hom).cechNerve ⋙ Presheaf.freeAbelianSheaf J) ≪≫
    (alternatingFaceMapComplex _).mapIso
      ((Functor.isoWhiskerRight (Functor.isoWhiskerRight
          (Arrow.cechNerveComp (sheafToPresheaf J (Type w)) (Arrow.mk g))
          (Presheaf.freeAbelianSheaf J)) (u.sheafPullback AddCommGrpCat.{w} J K)).symm ≪≫
        Functor.isoWhiskerLeft (Arrow.mk g).cechNerve (freeAbelianSheafPullbackIso J K u) ≪≫
        Functor.isoWhiskerRight (Arrow.cechNerveComp (u.sheafPullback (Type w) J K) (Arrow.mk g))
          (Sheaf.composeAndSheafify K AddCommGrpCat.free) ≪≫
        Functor.isoWhiskerRight (Arrow.cechNerveComp (sheafToPresheaf K (Type w))
          (Arrow.mk ((u.sheafPullback (Type w) J K).map g))) (Presheaf.freeAbelianSheaf K))

end LowerShriek

section Target

variable {D : Type w} [SmallCategory D] (K : GrothendieckTopology D)
  [HasExt.{w} (Sheaf K AddCommGrpCat.{w})]

omit [HasExt.{w} (Sheaf K AddCommGrpCat.{w})] in
/-- The free abelian sheaf generated by a sheaf of sets is sectionwise torsion free: it is the
sheafification of the sectionwise free abelian group, which is flat. -/
lemma isTorsionFree_freeAbelianSheaf (X : Sheaf K (Type w)) (V : Dᵒᵖ) :
    Module.IsTorsionFree ℤ (((Presheaf.freeAbelianSheaf K).obj X.obj).obj.obj V) :=
  ModuleSheafCohomology.isTorsionFree_sheafify K (X.obj ⋙ AddCommGrpCat.free) (fun V' ↦ by
    show Module.IsTorsionFree ℤ (FreeAbelianGroup (X.obj.obj V'))
    exact Module.Flat.isTorsionFree) V

/-- **An injective module is totally acyclic.** This is Stacks 072Z for the identity morphism of
ringed topoi: cohomology over a sheaf of sets is `Ext` out of the free abelian sheaf it
generates, which is sectionwise torsion free, and `Ext` out of a sectionwise torsion-free sheaf
into the abelian sheaf underlying an injective module vanishes in positive degree. -/
theorem isTotallyAcyclic_of_injective_module (O : Sheaf K RingCat.{w})
    (I : SheafOfModules.{w} O) [Injective I] :
    IsTotallyAcyclic.{w} K ((SheafOfModules.toSheaf O).obj I) := by
  intro X p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact ⟨fun a b ↦ by
    rw [ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree K O I _
        (isTorsionFree_freeAbelianSheaf K X) n a,
      ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree K O I _
        (isTorsionFree_freeAbelianSheaf K X) n b]⟩

end Target

section ConditionTwo

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w} (Sheaf K AddCommGrpCat.{w})]
  [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
    (u.sheafPullback (Type w) J K)]

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] in
/-- **Condition (2) of Stacks 07A1 for the inverse image of an injective module.** For every
surjection `K' → K` of sheaves of sets on `C` the extended Čech complex
`0 → H^0(K, g^{-1}I) → H^0(K', g^{-1}I) → H^0(K' ×_K K', g^{-1}I) → …` is exact in positive
degrees.

Lower shriek is a left adjoint, so it carries the surjection to a surjection and the whole
complex for `g^{-1}I` on `C` to the corresponding complex for `I` on `D`, where it is exact
because an injective module is totally acyclic. -/
theorem cechComplexExactPos_inverseImage (O : Sheaf K RingCat.{w}) (I : SheafOfModules.{w} O)
    [Injective I] :
    CechComplexExactPos J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) := by
  intro K' K₀ g hg n
  have hD : CechComplexExactPos K ((SheafOfModules.toSheaf O).obj I) :=
    cechComplexExactPos_of_isTotallyAcyclic.{w} K _ (isTotallyAcyclic_of_injective_module K O I)
  have hepi : Epi ((u.sheafPullback (Type w) J K).map g) := by
    have := (u.sheafAdjunctionContinuous (Type w) J K).leftAdjoint_preservesColimits
    exact (u.sheafPullback (Type w) J K).map_epi g
  have h := hD ((u.sheafPullback (Type w) J K).map g) hepi n
  have e := (ChainComplex.homComplexFunctorAdjunctionIso
      (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk g.hom).cechNerve)
      ((SheafOfModules.toSheaf O).obj I)) ≪≫
    (ChainComplex.homComplexFunctorMapIso (cechFreeAbelianSheafComplexPullbackIso J K u g)
      ((SheafOfModules.toSheaf O).obj I)).symm
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  exact IsZero.of_iso h ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso e)

end ConditionTwo

/-- Vanishing of the cohomology of `F` on every object in positive degrees gives
`VanishesOnObjects`: `Ext` out of the free abelian sheaf of a representable is such a group. -/
private theorem vanishesOnObjects_of_isZero_H' {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (h : ∀ (U : C) (p : ℕ), 0 < p → IsZero (Sheaf.H'.{w, w, w} F p U)) :
    VanishesOnObjects.{w} J F := by
  intro U Q hQ p hp
  have hsub : Subsingleton (Abelian.Ext.{w}
      ((presheafToSheaf J AddCommGrpCat.{w}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F p) :=
    AddCommGrpCat.subsingleton_of_isZero (h U p hp)
  let iso : (presheafToSheaf J AddCommGrpCat.{w}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (presheafToSheaf J AddCommGrpCat.{w}).obj (Q ⋙ AddCommGrpCat.free) :=
    (presheafToSheaf J AddCommGrpCat.{w}).mapIso
      (Functor.isoWhiskerRight hQ.toIso AddCommGrpCat.free)
  exact (((Abelian.extFunctor p).mapIso iso.op).app F).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr.mpr hsub

/-- Positive-degree cohomology of `F` on every object vanishes once a vanishing statement along a
covering system is known, for the cofinal system furnished by
`Stacks.Sites.PreservesCoveringPullbacks`: its iterated fibre products exist and are preserved by
`Over.post u`, so the comparison maps are invertible. -/
private theorem isZero_H'_of_preservesCoveringPullbacks {C : Type w} [SmallCategory C]
    {D : Type w} [Category.{w} D] (J : GrothendieckTopology C) (u : C ⥤ D)
    [Stacks.Sites.PreservesCoveringPullbacks J u] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w})
    (key : ∀ (B : Set C) (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
      (hProducts : ∀ {U : C} (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
      (hImageProducts : ∀ {U : C} (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → (E.1.map u).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a)))),
      (∀ {U : C} (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
        U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
          ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
            letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
              HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
            (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B) →
      (∀ U ∈ B, ∀ R ∈ J U, ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R) →
      (∀ {U : C} (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
        (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map u).I₀),
            HasProduct (fun a ↦ Over.mk ((E.1.map u).f (j a))) := hImageProducts E hE
          IsIso (Stacks.CechSite.cechProductMapOfFunctor u E.1 p i)) →
      ∀ U ∈ B, ∀ p : ℕ, 0 < p → IsZero (Sheaf.H'.{w, w, w} F p U)) :
    ∀ (U : C) (p : ℕ), 0 < p → IsZero (Sheaf.H'.{w, w, w} F p U) := by
  intro U p hp
  have hProducts : ∀ {V : C} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J V }),
      E ∈ { E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J V } |
          (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
          (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) u) } →
      ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
    fun E hE q i ↦ Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImage : ∀ {V : C} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J V })
      (hE : E ∈ { E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J V } |
          (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
          (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) u) })
      (q : ℕ) (i : Fin (q + 1) → (E.1.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.1.map u).f (i a))) := by
    intro V E hE q i
    have := hProducts E hE q i
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
    exact HasLimit.mk ⟨_, isLimitOfHasProductOfPreservesLimit (Over.post (X := V) u)
      (fun a ↦ Over.mk (E.1.f (i a)))⟩
  refine key Set.univ
      (fun V ↦ { E | (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
        (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) u) })
      hProducts hImage (fun E hE ↦ ⟨Set.mem_univ _, fun i ↦ Set.mem_univ _,
        fun q i ↦ Set.mem_univ _⟩) ?_ ?_ U (Set.mem_univ U) p hp
  · intro V _ S hS
    obtain ⟨E, hJ, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u S hS
    exact ⟨⟨E, hJ⟩, ⟨hpb, hpr⟩, hle⟩
  · intro V E hE q i
    have := hProducts E hE
    have := hImage E hE
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
    exact Stacks.CechSite.isIso_cechProductMapOfFunctor u E.1 q i

section ConditionOne

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (Y : AlgebraicGeometry.RingedSite.{w, w, w}) (u : C ⥤ Y.C) [u.IsContinuous J Y.J]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- **Condition (1) of Stacks 07A1 for the inverse image of an injective module**, which is
Stacks 0D6X: `H^p(U, g^{-1}I) = 0` for every `p > 0` and every object `U` of `C`.

The covering system of `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor` is
the cofinal one furnished by `Stacks.Sites.PreservesCoveringPullbacks`; the iterated fibre
products of the image coverings exist and the comparison maps to them are invertible because
`Over.post u` preserves the iterated fibre products of those coverings. -/
theorem vanishesOnObjects_inverseImage
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    VanishesOnObjects.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) := by
  exact vanishesOnObjects_of_isZero_H' J _ (isZero_H'_of_preservesCoveringPullbacks J u _
    (Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor.{w, w, w, w, w, w}
      Y J u · · · · · · · I))

end ConditionOne

section ConditionOneAbelian

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {D : Type w} [Category.{w} D] (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- **Condition (1) of Stacks 07A1 for the inverse image of an injective abelian sheaf**, the
case `O_D = ℤ` of Stacks 0D6X: `H^p(U, g⁻¹I) = 0` for every `p > 0` and every object `U` of `C`.

This is `vanishesOnObjects_inverseImage` with the structure sheaf dropped. It is a separate
statement because an injective object of `Ab(D)` is not, in the formalization, an injective
module over the constant sheaf of rings `ℤ`; correspondingly the target is an arbitrary site
rather than a ringed one, and its morphism universe is free of any coefficient universe.

The proof is the module one, run through
`Stacks.CechSite.injective_sheaf_sheafCohomology_isZero_of_functor` in place of
`Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`: the covering system is the
cofinal one furnished by `Stacks.Sites.PreservesCoveringPullbacks`, and the iterated fibre
products of the image coverings exist with invertible comparison maps because `Over.post u`
preserves the iterated fibre products of those coverings. -/
theorem vanishesOnObjects_inverseImage_sheaf (I : Sheaf K AddCommGrpCat.{w}) [Injective I] :
    VanishesOnObjects.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj I) := by
  exact vanishesOnObjects_of_isZero_H' J _ (isZero_H'_of_preservesCoveringPullbacks J u _
    (Stacks.CechSite.injective_sheaf_sheafCohomology_isZero_of_functor.{w, w, w, w, w, w}
      J K u · · · · · · · I))

end ConditionOneAbelian

section Main

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (Y : AlgebraicGeometry.RingedSite.{w, w, w}) (u : C ⥤ Y.C)
  [u.IsContinuous J Y.J] [u.IsCocontinuous J Y.J]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w} (Sheaf Y.J AddCommGrpCat.{w})]

omit [u.IsCocontinuous J Y.J] in
/-- **Stacks Project, Tag 0D6Y.** Let `u : C ⥤ D` be a continuous and cocontinuous functor of
sites and let `g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g^{-1}` is
restriction along `u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on `D` and let `I` be
an injective `O_D`-module. If `g_!^{Sh} : Sh(C) → Sh(D)` commutes with fibre products, then
`g^{-1}I` is totally acyclic: its cohomology over every sheaf of sets on `C` vanishes in every
positive degree.

As in the source, total acyclicity of a module is that of its underlying abelian sheaf; the
abelian sheaf underlying `g^{-1}I` is the restriction along `u` of the abelian sheaf underlying
`I`, which is how the conclusion is phrased. -/
@[stacks 0D6Y]
theorem isTotallyAcyclic_inverseImage_of_injective
    [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J Y.J)]
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) :=
  isTotallyAcyclic_of_conditions J _ (vanishesOnObjects_inverseImage J Y u I)
    (cechComplexExactPos_inverseImage J Y.J u (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) I)

omit [u.IsCocontinuous J Y.J] in
/-- **Stacks Project, Tag 0D6Y, under the sufficient condition of its footnote.** If `C` has
fibre products and equalizers — equivalently, all finite connected limits — and `u` preserves
them, then `g_!^{Sh}` commutes with fibre products by Sites, Lemma 00XS, and the inverse image
of an injective `O_D`-module is totally acyclic. -/
@[stacks 0D6Y "the case of the footnote's sufficient condition: `C` has finite connected limits
  and `u` commutes with them"]
theorem isTotallyAcyclic_inverseImage_of_injective_of_pullbacks [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u] [PreservesLimitsOfShape WalkingParallelPair u]
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) :=
  have : ∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J Y.J) := fun n ↦
    Functor.preservesLimitsOfShape_sheafPullback u J Y.J (WidePullbackShape (Fin (n + 1)))
  isTotallyAcyclic_inverseImage_of_injective J Y u I

omit [u.IsCocontinuous J Y.J] in
/-- **Stacks Project, Tag 0D6Y, read on the inverse image module.** The abelian sheaf underlying
the inverse image `g^{-1}I` of an injective `O_D`-module — restriction along `u`, as a module
over the inverse image `g^{-1}O_D` of the structure sheaf — is totally acyclic. -/
@[stacks 0D6Y "the conclusion read on the inverse image module rather than on the restriction of
  the underlying abelian sheaf"]
theorem isTotallyAcyclic_pushforwardModule_of_injective
    [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J Y.J)]
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((SheafOfModules.toSheaf _).obj
        ((SheafOfModules.pushforward (F := u)
          (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J Y.J).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj I)) :=
  isTotallyAcyclic_inverseImage_of_injective J Y u I

omit [u.IsCocontinuous J Y.J] in
/-- **Stacks Project, Tag 0D6Y, with the hypothesis the source states.** Let `u : C ⥤ D` be a
continuous and cocontinuous functor of sites and let `g : Sh(C) → Sh(D)` be the corresponding
morphism of topoi. Let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. If `g_!^{Sh} : Sh(C) → Sh(D)` commutes with binary fibre products, then `g^{-1}I`
is totally acyclic.

The complex of Stacks 07A1 is built from the iterated fibre powers of a surjection of sheaves of
sets, so it is commutation with those that the proof uses. Commutation with binary fibre
products supplies it: an iterated fibre power is a fibre product of one fewer of its factors
against the remaining one, and `Sh(C)` has fibre products, so
`CategoryTheory.Limits.preservesLimitsOfShape_widePullbackShape` applies. -/
@[stacks 0D6Y "the tag at the source's own hypothesis, that `g_!^{Sh}` commute with binary
  fibre products; the iterated fibre powers the proof uses follow from it"]
theorem isTotallyAcyclic_inverseImage_of_injective_of_cospans
    [PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type w) J Y.J)]
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J Y.J).obj
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I)) :=
  have : ∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J Y.J) := fun n ↦
    preservesLimitsOfShape_widePullbackShape _ (Fin (n + 1))
  isTotallyAcyclic_inverseImage_of_injective J Y u I

end Main

/-! ### Coefficients in a sheaf of rings, not assumed commutative

Condition (1) and Stacks 0D6Y for an arbitrary site `(D, K)` with a sheaf of rings
`O : Sheaf K RingCat`, not assumed commutative. A ringed site is the case
`O = Stacks.SheafOfModules.Tensor.ringSheaf Y.O`. -/

section ConditionOneSheafOfRings

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) (O : Sheaf K RingCat.{w})
  (u : C ⥤ D) [u.IsContinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- **Condition (1) of Stacks 07A1 for the inverse image of an injective module**, which is
Stacks 0D6X: `H^p(U, g^{-1}I) = 0` for every `p > 0` and every object `U` of `C`. -/
theorem vanishesOnObjects_inverseImage_sheafOfRings (I : SheafOfModules.{w} O) [Injective I] :
    VanishesOnObjects.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) := by
  exact vanishesOnObjects_of_isZero_H' J _ (isZero_H'_of_preservesCoveringPullbacks J u _
    (Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor_sheafOfRings.{w, w,
      w, w, w, w} K O J u · · · · · · · I))

end ConditionOneSheafOfRings

section MainSheafOfRings

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) (O : Sheaf K RingCat.{w})
  (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w} (Sheaf K AddCommGrpCat.{w})]

omit [u.IsCocontinuous J K] in
/-- **Stacks Project, Tag 0D6Y.** Let `u : C ⥤ D` be a continuous and cocontinuous functor of
sites and let `g : Sh(C) → Sh(D)` be the corresponding morphism of topoi, so that `g^{-1}` is
restriction along `u` by Sites, Lemma 00XR. Let `O_D` be a sheaf of rings on `D` and let `I` be
an injective `O_D`-module. If `g_!^{Sh} : Sh(C) → Sh(D)` commutes with fibre products, then
`g^{-1}I` is totally acyclic: its cohomology over every sheaf of sets on `C` vanishes in every
positive degree.

As in the source, total acyclicity of a module is that of its underlying abelian sheaf; the
abelian sheaf underlying `g^{-1}I` is the restriction along `u` of the abelian sheaf underlying
`I`, which is how the conclusion is phrased. -/
@[stacks 0D6Y]
theorem isTotallyAcyclic_inverseImage_of_injective_sheafOfRings
    [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J K)]
    (I : SheafOfModules.{w} O) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  isTotallyAcyclic_of_conditions J _ (vanishesOnObjects_inverseImage_sheafOfRings J K O u I)
    (cechComplexExactPos_inverseImage J K u O I)

omit [u.IsCocontinuous J K] in
/-- **Stacks Project, Tag 0D6Y, under the sufficient condition of its footnote.** If `C` has
fibre products and equalizers — equivalently, all finite connected limits — and `u` preserves
them, then `g_!^{Sh}` commutes with fibre products by Sites, Lemma 00XS, and the inverse image
of an injective `O_D`-module is totally acyclic. -/
@[stacks 0D6Y "the case of the footnote's sufficient condition: `C` has finite connected limits
  and `u` commutes with them"]
theorem isTotallyAcyclic_inverseImage_of_injective_of_pullbacks_sheafOfRings
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u] [PreservesLimitsOfShape WalkingParallelPair u]
    (I : SheafOfModules.{w} O) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  have : ∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J K) := fun n ↦
    Functor.preservesLimitsOfShape_sheafPullback u J K (WidePullbackShape (Fin (n + 1)))
  isTotallyAcyclic_inverseImage_of_injective_sheafOfRings J K O u I

omit [u.IsCocontinuous J K] in
/-- **Stacks Project, Tag 0D6Y, read on the inverse image module.** The abelian sheaf underlying
the inverse image `g^{-1}I` of an injective `O_D`-module — restriction along `u`, as a module
over the inverse image `g^{-1}O_D` of the structure sheaf — is totally acyclic. -/
@[stacks 0D6Y "the conclusion read on the inverse image module rather than on the restriction of
  the underlying abelian sheaf"]
theorem isTotallyAcyclic_pushforwardModule_of_injective_sheafOfRings
    [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J K)]
    (I : SheafOfModules.{w} O) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((SheafOfModules.toSheaf _).obj
        ((SheafOfModules.pushforward (F := u)
          (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J K).obj O))).obj I)) :=
  isTotallyAcyclic_inverseImage_of_injective_sheafOfRings J K O u I

omit [u.IsCocontinuous J K] in
/-- **Stacks Project, Tag 0D6Y, with the hypothesis the source states.** Let `u : C ⥤ D` be a
continuous and cocontinuous functor of sites and let `g : Sh(C) → Sh(D)` be the corresponding
morphism of topoi. Let `O_D` be a sheaf of rings on `D` and let `I` be an injective
`O_D`-module. If `g_!^{Sh} : Sh(C) → Sh(D)` commutes with binary fibre products, then `g^{-1}I`
is totally acyclic.

The complex of Stacks 07A1 is built from the iterated fibre powers of a surjection of sheaves of
sets, so it is commutation with those that the proof uses. Commutation with binary fibre
products supplies it: an iterated fibre power is a fibre product of one fewer of its factors
against the remaining one, and `Sh(C)` has fibre products, so
`CategoryTheory.Limits.preservesLimitsOfShape_widePullbackShape` applies. -/
@[stacks 0D6Y "the tag at the source's own hypothesis, that `g_!^{Sh}` commute with binary
  fibre products; the iterated fibre powers the proof uses follow from it"]
theorem isTotallyAcyclic_inverseImage_of_injective_of_cospans_sheafOfRings
    [PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type w) J K)]
    (I : SheafOfModules.{w} O) [Injective I] :
    IsTotallyAcyclic.{w} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  have : ∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
      (u.sheafPullback (Type w) J K) := fun n ↦
    preservesLimitsOfShape_widePullbackShape _ (Fin (n + 1))
  isTotallyAcyclic_inverseImage_of_injective_sheafOfRings J K O u I

end MainSheafOfRings

end Stacks.Cohomology.DerivedLowerShriek

end
