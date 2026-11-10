module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Cohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison

/-!
# The Čech criterion for the higher cohomology of an adequate module on an affine object

Let `S` be a scheme and let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site over `S`.
[Stacks, Tag 06VM] (3) asserts that `H^q(U, 𝓕) = 0` for every `q > 0` and every affine object
`U` of the site. The source's proof is the Čech criterion of [Stacks, Tag 03F9], applied to the
collection `B` of affine objects of the site and to the collection `Cov` of finite affine
`τ`-coverings of those objects. This module sets up that application: the criterion in a form
that applies to a chosen big site, the collection `Cov`, the facts about the site the criterion
asks for, and the names of the three inputs of the source's proof. The assertion itself, with
every input proved, is `Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`.

## Main definitions

* `Stacks.Adequate.BigSite.affineCov` — the finite affine `τ`-coverings of an object of the
  site: the finite coverings of an affine object by affine objects whose underlying morphisms
  have the covering morphism property of `τ` and are jointly surjective. This is the collection
  `Cov` of [Stacks, Tag 03F9] used here.
* `Stacks.Adequate.BigSite.AffineCovCofinal`, `Stacks.Adequate.BigSite.AffineCechExactness` and
  `Stacks.Adequate.BigSite.CoproductCechComparison` — the three inputs of the source's proof, as
  propositions. They are proved by `Stacks.Adequate.BigSite.affineCovCofinal`,
  `Stacks.Adequate.affineCechExactness_of_isAdequate` and
  `Stacks.Adequate.BigSite.coproductCechComparison` respectively.

## Main results

* `Stacks.Adequate.cechCriterion_of_essentiallySmall` — [Stacks, Tag 03F9] for a site which is
  only essentially small at the coefficient universe, with the conclusion stated for the right
  derived functors of sections over an object.
* `Stacks.Adequate.BigSite.hasFiniteLimits_category` and
  `Stacks.Adequate.BigSite.essentiallySmall_category` — the underlying category of a chosen big
  site has finite limits and is essentially small at the universe of its schemes. The first is
  [Stacks, Tag 022K] for a chosen big site, the second is [Stacks, Tag 000J] for the cutoff
  category of schemes.
* `Stacks.Adequate.BigSite.isAffine_product_of_mem_affineCov` — the iterated fibre products
  occurring in a finite affine covering of an affine object are again affine objects of the
  site. This is the hypothesis `hCovObjects` of [Stacks, Tag 03F9] at `affineCov`.
* `Stacks.Adequate.BigSite.exists_affine_coproduct_morphism` — the disjoint union of a finite
  affine covering of an affine object belongs to the site, and the morphism from it is flat and
  surjective.

## Implementation notes

*Cohomology.* Cohomology over `U` in degree `q` is the `q`-th right derived functor of
`(sheafSections B.topology AddCommGrpCat).obj (op U)`, sections over `U` on abelian sheaves,
which is the source's own definition of cohomology on a site, applied to the abelian sheaf
`CategoryTheory.SheafOfModules.toSheaf` underlying the module.

*The universe transport.* [Stacks, Tag 03F9] is stated with `Small.{max v w} C`, that is at a
coefficient universe containing the *object* universe of the site, and the underlying category
of a chosen big site has its objects one universe above its morphisms: it is
`Over (⟨S, _⟩ : SchemeBelow B.cutoff)`, whose objects live in `Type (u + 1)`. So the criterion
cannot be applied directly at the coefficient universe `max u m` of the modules on the site.
The site is however essentially small at that universe, by
`Stacks.Adequate.BigSite.essentiallySmall_category`, and `cechCriterion_of_essentiallySmall`
transports the criterion to it: the criterion is applied on a small model of the site with the
induced topology, where sheaf cohomology and right derived sections agree, and the conclusion is
carried back along the induced equivalence of categories of abelian sheaves, which commutes with
right derived functors because the functor of an equivalence preserves injective resolutions.

*The three inputs.* `Stacks.Adequate.BigSite.AffineCechExactness` is [Stacks, Tag 06VL]: for a
surjective flat morphism of affine objects of the site the extended Čech complex of an adequate
module is exact. `Stacks.Adequate.BigSite.CoproductCechComparison` is [Stacks, Tag 03FI] part
(3) read on the chosen big site. `Stacks.Adequate.BigSite.AffineCovCofinal` is cofinality of the
finite affine coverings among all covering sieves of an affine object, the hypothesis
`hCovCofinal` of [Stacks, Tag 03F9]; this is [Stacks, Tag 03XA]. Each is proved in a module
lying above this one, because each needs machinery this module does not import.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u m ℓ

namespace Stacks.Adequate

/-! ### The Čech criterion over a site essentially small at the coefficients -/

/-- An additive functor preserving homology and injective objects carries an injective
resolution to an injective resolution of the image. -/
private noncomputable def injectiveResolutionMap
    {A₁ : Type*} [Category* A₁] {A₂ : Type*} [Category* A₂] [Abelian A₁] [Abelian A₂]
    (Ψ : A₁ ⥤ A₂) [Ψ.Additive] [Ψ.PreservesHomology] [Ψ.PreservesInjectiveObjects]
    {X : A₁} (I : InjectiveResolution X) : InjectiveResolution (Ψ.obj X) where
  cocomplex := (Ψ.mapHomologicalComplex _).obj I.cocomplex
  injective n := Ψ.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℕ) 0).inv.app X ≫
    (Ψ.mapHomologicalComplex _).map I.ι
  quasiIso := by
    have : QuasiIso ((Ψ.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := inferInstance
    infer_instance

/-- Precomposing an additive functor with the functor of an equivalence commutes with right
derived functors. -/
private noncomputable def rightDerivedPrecompEquivIso
    {A₁ : Type*} [Category* A₁] {A₂ : Type*} [Category* A₂] {E : Type*} [Category* E]
    [Abelian A₁] [Abelian A₂] [Abelian E] [EnoughInjectives A₁] [EnoughInjectives A₂]
    (Φ : A₁ ≌ A₂) [Φ.functor.Additive] (T : A₂ ⥤ E) [T.Additive] (X : A₁) (n : ℕ) :
    ((Φ.functor ⋙ T).rightDerived n).obj X ≅ (T.rightDerived n).obj (Φ.functor.obj X) :=
  let I := injectiveResolution X
  (I.isoRightDerivedObj (Φ.functor ⋙ T) n) ≪≫
    ((injectiveResolutionMap Φ.functor I).isoRightDerivedObj T n).symm

/-- Isomorphic additive functors have isomorphic right derived functors. -/
private noncomputable def rightDerivedIsoOfNatIso
    {A₁ : Type*} [Category* A₁] {E : Type*} [Category* E] [Abelian A₁] [Abelian E]
    [HasInjectiveResolutions A₁] {T₁ T₂ : A₁ ⥤ E} [T₁.Additive] [T₂.Additive]
    (α : T₁ ≅ T₂) (n : ℕ) : T₁.rightDerived n ≅ T₂.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

/-- The transport of a `0`-hypercover along the functor of an equivalence, retargeted along the
counit isomorphism. -/
private def transportHypercover {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    (e : D₁ ≌ D₂) {Y : D₂} (E : PreZeroHypercover.{0} (e.inverse.obj Y)) :
    PreZeroHypercover.{0} Y where
  I₀ := E.I₀
  X i := e.functor.obj (E.X i)
  f i := e.functor.map (E.f i) ≫ e.counit.app Y

/-- Transporting a `0`-hypercover and pulling it back recovers it up to isomorphism. -/
private def transportHypercoverIso {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    (e : D₁ ≌ D₂) {Y : D₂} (E : PreZeroHypercover.{0} (e.inverse.obj Y)) :
    E ≅ (transportHypercover e E).map e.inverse :=
  PreZeroHypercover.isoMk (Equiv.refl _) (fun i ↦ e.unitIso.app (E.X i)) (by
    intro i
    change e.unit.app (E.X i) ≫
      e.inverse.map (e.functor.map (E.f i) ≫ e.counit.app Y) = E.f i
    rw [Functor.map_comp, ← Category.assoc, Equivalence.unit_naturality e (E.f i),
      Category.assoc, Equivalence.unit_inverse_comp, Category.comp_id])

/-- A `0`-hypercover covers for the topology induced along the inverse of an equivalence exactly
when its pullback along that inverse covers. -/
private theorem sieve₀_mem_inducedTopology_iff {D₁ : Type*} [Category* D₁] {D₂ : Type*}
    [Category* D₂] (e : D₁ ≌ D₂) (J : GrothendieckTopology D₁) {Y : D₂}
    (E : PreZeroHypercover.{0} Y) :
    E.sieve₀ ∈ e.inverse.inducedTopology J Y ↔ (E.map e.inverse).sieve₀ ∈ J (e.inverse.obj Y) := by
  rw [PreZeroHypercover.sieve₀_map]
  exact Functor.mem_inducedTopology_iff_of_isCoverDense e.inverse J _

/-- A `0`-hypercover refining the pushforward of a sieve along the inverse of an equivalence
transports to a `0`-hypercover refining the sieve. -/
private theorem transportHypercover_sieve₀_le {D₁ : Type*} [Category* D₁] {D₂ : Type*}
    [Category* D₂] (e : D₁ ≌ D₂) {Y : D₂} (E : PreZeroHypercover.{0} (e.inverse.obj Y))
    {R : Sieve Y} (hER : E.sieve₀ ≤ R.functorPushforward e.inverse) :
    (transportHypercover e E).sieve₀ ≤ R := by
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨Z, g, h, hgR, hfac⟩ := hER _ (PreZeroHypercover.sieve₀_f E i)
  change R.arrows (e.functor.map (E.f i) ≫ e.counit.app Y)
  have hrw : e.functor.map (E.f i) ≫ e.counit.app Y =
      (e.functor.map h ≫ e.counit.app Z) ≫ g := by
    rw [hfac, Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact e.counit.naturality g
  rw [hrw]
  exact R.downward_closed hgR _

/-- **The Čech criterion of [Stacks, Tag 03F9] with the object universe of the site removed.**
The site is only assumed essentially small at the coefficient universe, and the conclusion is
stated for the right derived functors of sections over the object. -/
public theorem cechCriterion_of_essentiallySmall
    {D : Type*} [Category* D] (J : GrothendieckTopology D)
    [HasFiniteLimits D] [EssentiallySmall.{ℓ} D]
    [HasSheafify J AddCommGrpCat.{ℓ}]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{ℓ})]
    (Bs : Set D)
    (hBsIso : ∀ {X Y : D}, (X ≅ Y) → X ∈ Bs → Y ∈ Bs)
    (Cov : ∀ V : D, Set { E : PreZeroHypercover.{0} V // E.sieve₀ ∈ J V })
    (hCovIso : ∀ {V : D} (E E' : { E : PreZeroHypercover.{0} V // E.sieve₀ ∈ J V }),
      (E.1 ≅ E'.1) → E ∈ Cov V → E' ∈ Cov V)
    (hCovObjects : ∀ {V : D} (E : { E : PreZeroHypercover.{0} V // E.sieve₀ ∈ J V }),
      E ∈ Cov V → V ∈ Bs ∧ (∀ i, E.1.X i ∈ Bs) ∧
        ∀ (k : ℕ) (i : Fin (k + 1) → E.1.I₀),
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ Bs)
    (hCovCofinal : ∀ V ∈ Bs, ∀ R ∈ J V,
      ∃ E : { E : PreZeroHypercover.{0} V // E.sieve₀ ∈ J V }, E ∈ Cov V ∧ E.1.sieve₀ ≤ R)
    (F : Sheaf J AddCommGrpCat.{ℓ})
    (hCech : ∀ {V : D} (E : { E : PreZeroHypercover.{0} V // E.sieve₀ ∈ J V }),
      E ∈ Cov V → ∀ k : ℕ, 0 < k → IsZero (Stacks.CechSite.cechCohomology E.1 F.obj k))
    (V : D) (hV : V ∈ Bs) (k : ℕ) (hk : 0 < k) :
    IsZero ((((sheafSections J AddCommGrpCat.{ℓ}).obj (op V)).rightDerived k).obj F) := by
  let e : D ≌ SmallModel.{ℓ} D := equivSmallModel.{ℓ} D
  let K : GrothendieckTopology (SmallModel.{ℓ} D) := e.inverse.inducedTopology J
  have : HasFiniteLimits (SmallModel.{ℓ} D) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  let Φ : Sheaf J AddCommGrpCat.{ℓ} ≌ Sheaf K AddCommGrpCat.{ℓ} := e.sheafCongr J K _
  have : EnoughInjectives (Sheaf K AddCommGrpCat.{ℓ}) :=
    EnoughInjectives.of_equivalence Φ.inverse
  have : HasExt.{ℓ} (Sheaf K AddCommGrpCat.{ℓ}) :=
    hasExt_of_enoughInjectives (Sheaf K AddCommGrpCat.{ℓ})
  let Bs' : Set (SmallModel.{ℓ} D) := fun Y ↦ e.inverse.obj Y ∈ Bs
  let Cov' : ∀ Y : SmallModel.{ℓ} D, Set { E : PreZeroHypercover.{0} Y // E.sieve₀ ∈ K Y } :=
    fun Y E' ↦ ∃ h : (E'.1.map e.inverse).sieve₀ ∈ J (e.inverse.obj Y),
      (⟨E'.1.map e.inverse, h⟩ :
        { E : PreZeroHypercover.{0} (e.inverse.obj Y) // E.sieve₀ ∈ J (e.inverse.obj Y) }) ∈
        Cov (e.inverse.obj Y)
  have key : IsZero ((((sheafSections K AddCommGrpCat.{ℓ}).obj
      (op (e.functor.obj V))).rightDerived k).obj (Φ.functor.obj F)) := by
    refine (Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero
      K Bs' Cov' (fun {_} _ _ _ _ ↦ inferInstance) ?_ ?_ (Φ.functor.obj F) ?_
      (e.functor.obj V) (hBsIso (e.unitIso.app V) hV) k hk).of_iso
      (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections K
        (Φ.functor.obj F) k (e.functor.obj V)).symm
    · rintro Y E' ⟨h, hmem⟩
      obtain ⟨h1, h2, h3⟩ := hCovObjects ⟨E'.1.map e.inverse, h⟩ hmem
      refine ⟨h1, h2, fun q i ↦ hBsIso ?_ (h3 q i)⟩
      exact ((Over.forget _).mapIso (PreservesProduct.iso (Over.post e.inverse)
        (fun a ↦ Over.mk (E'.1.f (i a))))).symm
    · intro Y hY R hR
      obtain ⟨E, hEcov, hER⟩ := hCovCofinal (e.inverse.obj Y) hY _
        ((Functor.mem_inducedTopology_iff_of_isCoverDense e.inverse J R).1 hR)
      have hpull : ((transportHypercover e E.1).map e.inverse).sieve₀ ∈ J (e.inverse.obj Y) := by
        rw [← PreZeroHypercover.sieve₀_eq_of_iso (transportHypercoverIso e E.1)]
        exact E.2
      exact ⟨⟨transportHypercover e E.1, (sieve₀_mem_inducedTopology_iff e J _).2 hpull⟩,
        ⟨hpull, hCovIso E ⟨_, hpull⟩ (transportHypercoverIso e E.1) hEcov⟩,
        transportHypercover_sieve₀_le e E.1 hER⟩
    · rintro Y E' ⟨h, hmem⟩ q hq
      exact (hCech ⟨E'.1.map e.inverse, h⟩ hmem q hq).of_iso
        (Stacks.CechSite.cechCohomologyIsoOfFunctor e.inverse E'.1 F.obj
          (fun n i ↦ Stacks.CechSite.isIso_cechProductMapOfFunctor e.inverse E'.1 n i) q).symm
  let Γ := (sheafSections K AddCommGrpCat.{ℓ}).obj (op (e.functor.obj V))
  have : Φ.functor.Additive := ⟨by intros; rfl⟩
  let α : Φ.functor ⋙ Γ ≅ (sheafSections J AddCommGrpCat.{ℓ}).obj (op V) :=
    NatIso.ofComponents (fun P ↦ P.obj.mapIso (e.unitIso.app V).op) (fun f ↦
      (((sheafToPresheaf J AddCommGrpCat.{ℓ}).map f).naturality (e.unitIso.app V).op.hom).symm)
  exact (key.of_iso (rightDerivedPrecompEquivIso Φ Γ F k)).of_iso
    ((rightDerivedIsoOfNatIso α k).app F).symm

/-! ### Finite limits in a chosen big site -/

/-- The cutoff of a chosen big site is uncountable, since the base scheme belongs to it. -/
public theorem BigSite.aleph0_lt_cutoff {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : ℵ₀ < B.cutoff :=
  lt_of_le_of_lt (Scheme.aleph0_le_size S) B.base_mem

/-- The inclusion of the cutoff category of schemes into schemes preserves finite limits. -/
private theorem schemeBelowInclusion_preservesFiniteLimits (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) :
    PreservesFiniteLimits (ObjectProperty.ι (schemeSizeBelow κ)) := by
  have : (schemeSizeBelow κ).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) :=
    schemeSizeBelow_closedUnderTerminal κ hκ
  have : HasFiniteLimits (SchemeBelow κ) := schemeSizeBelow_hasFiniteLimits κ hκ
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- The underlying category of a chosen big site has finite limits: it is a slice of the
cutoff category of schemes, which has a terminal object and fibre products. This is
[Stacks, Tag 022K] for a chosen big site. -/
public theorem BigSite.hasFiniteLimits_category {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : HasFiniteLimits B.category := by
  have : HasFiniteLimits (SchemeBelow B.cutoff) :=
    schemeSizeBelow_hasFiniteLimits B.cutoff B.aleph0_lt_cutoff
  exact inferInstanceAs
    (HasFiniteLimits (Over (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff)))

/-- **The canonical functor from a chosen big site to the schemes over `S` preserves finite
limits.** It is `Over.post` of the inclusion of the cutoff category of schemes, and that
inclusion preserves finite limits because the cutoff category is closed under terminal objects
and fibre products. So a fibre product formed in the site is the fibre product of the underlying
schemes — which is what makes a Čech construction in the site agree with the geometric one. -/
public theorem BigSite.preservesFiniteLimits_toOver {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : PreservesFiniteLimits B.toOver := by
  have : HasFiniteLimits (SchemeBelow B.cutoff) :=
    schemeSizeBelow_hasFiniteLimits B.cutoff B.aleph0_lt_cutoff
  have : PreservesFiniteLimits (ObjectProperty.ι (schemeSizeBelow B.cutoff)) :=
    schemeBelowInclusion_preservesFiniteLimits B.cutoff B.aleph0_lt_cutoff
  exact PreservesFiniteLimits.overPost

/-- A chosen big site is essentially small at the universe of its schemes, by
[Stacks, Tag 000J] for the cutoff category of schemes. -/
public theorem BigSite.essentiallySmall_category {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : EssentiallySmall.{u} B.category := by
  have : EssentiallySmall.{u} (SchemeBelow B.cutoff) := essentiallySmall_schemeBelow B.cutoff
  exact essentiallySmall_of_fully_faithful
    (Over.post (X := (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff))
      (equivSmallModel.{u} (SchemeBelow B.cutoff)).functor)

/-! ### The covering morphism property -/

/-- The covering morphism property of each of the five topologies is stable under
composition. -/
private theorem coveringMorphismProperty_isStableUnderComposition (τ : CoveringTopology) :
    (coveringMorphismProperty.{u} τ).IsStableUnderComposition := by
  cases τ with
  | fppf =>
      constructor
      rintro X Y Z f g ⟨_, _⟩ ⟨_, _⟩
      exact ⟨inferInstance, inferInstance⟩
  | syntomic => exact AlgebraicGeometry.syntomic_isStableUnderComposition
  | _ => infer_instance

/-- A morphism of the covering morphism property of `τ` stays in it after composing with an
open immersion on the left. -/
private theorem coveringMorphismProperty_comp_isOpenImmersion (τ : CoveringTopology)
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] {f : Y ⟶ Z}
    (hf : coveringMorphismProperty τ f) : coveringMorphismProperty τ (g ≫ f) :=
  have := coveringMorphismProperty_isStableUnderComposition.{u} τ
  (coveringMorphismProperty τ).comp_mem _ _
    (isOpenImmersion_le_coveringMorphismProperty τ g inferInstance) hf

/-- A morphism of the covering morphism property of `τ` is flat. -/
private theorem coveringMorphismProperty_flat (τ : CoveringTopology) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : coveringMorphismProperty τ f) : Flat f := by
  cases τ with
  | syntomic => exact AlgebraicGeometry.flat hf
  | fppf => exact hf.1
  | zariski | etale | smooth =>
      have := hf
      infer_instance

/-- A morphism of the covering morphism property of `τ` is locally of finite presentation. -/
private theorem coveringMorphismProperty_locallyOfFinitePresentation (τ : CoveringTopology)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : coveringMorphismProperty τ f) :
    LocallyOfFinitePresentation f := by
  cases τ with
  | syntomic => exact AlgebraicGeometry.locallyOfFinitePresentation hf
  | fppf => exact hf.2
  | zariski | etale | smooth =>
      have := hf
      infer_instance

/-! ### Finite affine coverings of an affine object -/

/-- The finite affine `τ`-coverings of an object `U` of a chosen big site over `S`: the finite
coverings of an affine object by affine objects whose underlying morphisms have the covering
morphism property of `τ` and are jointly surjective. This is the collection `Cov` to which
[Stacks, Tag 03F9] is applied. -/
public def BigSite.affineCov {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (U : B.category) : Set { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U } :=
  { E | U ∈ B.affineObjects ∧ Finite E.1.I₀ ∧ (∀ i, E.1.X i ∈ B.affineObjects) ∧
      (∀ i, coveringMorphismProperty τ (B.toOver.map (E.1.f i)).left) ∧
      ∀ x : U.left.obj, ∃ i, x ∈ Set.range (B.toOver.map (E.1.f i)).left }

/-- The affine objects of a chosen big site are closed under isomorphism. -/
public theorem BigSite.mem_affineObjects_of_iso {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) {X Y : B.category} (θ : X ≅ Y) (hX : X ∈ B.affineObjects) :
    Y ∈ B.affineObjects := by
  change IsAffine Y.left.obj
  have : IsAffine X.left.obj := hX
  have e : X.left.obj ≅ Y.left.obj := (B.toOver ⋙ Over.forget S).mapIso θ
  exact IsAffine.of_isIso e.inv

/-- The finite affine coverings of an object are closed under isomorphism of coverings. -/
public theorem BigSite.mem_affineCov_of_iso {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S)
    {U : B.category} (E E' : { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U })
    (θ : E.1 ≅ E'.1) (hE : E ∈ B.affineCov U) : E' ∈ B.affineCov U := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  have : Finite E.1.I₀ := h2
  have hfac : ∀ {E₁ E₂ : PreZeroHypercover.{0} U} (φ : E₁ ⟶ E₂) (j : E₁.I₀),
      (B.toOver.map (E₁.f j)).left =
        (B.toOver.map (φ.h₀ j)).left ≫ (B.toOver.map (E₂.f (φ.s₀ j))).left := by
    intro E₁ E₂ φ j
    rw [← φ.w₀ j, B.toOver.map_comp]
    rfl
  refine ⟨h1, Finite.of_equiv _ (PreZeroHypercover.equivOfIso θ), fun j ↦ ?_, fun j ↦ ?_,
    fun x ↦ ?_⟩
  · exact B.mem_affineObjects_of_iso (asIso (θ.inv.h₀ j)).symm (h3 _)
  · rw [hfac θ.inv j]
    have hio : IsOpenImmersion ((B.toOver.map (θ.inv.h₀ j)).left) :=
      inferInstanceAs (IsOpenImmersion ((B.toOver ⋙ Over.forget S).map (θ.inv.h₀ j)))
    exact coveringMorphismProperty_comp_isOpenImmersion τ _ (h4 (θ.inv.s₀ j))
  · obtain ⟨i, y, hy⟩ := h5 x
    refine ⟨θ.hom.s₀ i, (B.toOver.map (θ.hom.h₀ i)).left.base y, ?_⟩
    rw [← hy, hfac θ.hom i]
    rfl

/-! ### The granted inputs -/

/-- Every covering sieve of an affine object of the site is refined by a finite affine
covering. -/
public abbrev BigSite.AffineCovCofinal {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : Prop :=
  ∀ U ∈ B.affineObjects, ∀ R ∈ B.topology U,
    ∃ E ∈ B.affineCov U,
      (E : { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U }).1.sieve₀ ≤ R

/-- **[Stacks, Tag 06VL].** For a surjective flat morphism `Spec B' → Spec A` of affine objects
of the site over `S` the extended Čech complex

`0 → F(Spec A) → F(Spec B') → F(Spec B' ⊗_A B') → ⋯`

of an adequate `𝒪`-module is exact; in positive degrees this is the vanishing of the Čech
cohomology of the one-member family `{Spec B' → Spec A}`. -/
public abbrev BigSite.AffineCechExactness {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  IsAdequate B F →
    ∀ {X Y : B.category} (f : Y ⟶ X), X ∈ B.affineObjects → Y ∈ B.affineObjects →
      Flat (B.toOver.map f).left → Surjective (B.toOver.map f).left →
        letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
        ∀ n : ℕ, 0 < n →
          IsZero (Stacks.CechSite.cechCohomology (PreZeroHypercover.singleton.{0} f)
            ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj n)

/-- **[Stacks, Tag 03FI] part (3) read on a chosen big site.** For a finite covering `E` of an
object of the site and a morphism `f` of the site whose image in the schemes over `S` is the
morphism from the disjoint union of the image of `E`, the Čech cohomology of `E` agrees with
the Čech cohomology of the one-member family `{f}`. -/
public abbrev BigSite.CoproductCechComparison {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ {X : B.category} (E : PreZeroHypercover.{0} X), Finite E.I₀ →
    ∀ (Y : B.category) (f : Y ⟶ X),
      (PreZeroHypercover.singleton.{0} f).map B.toOver =
        PreZeroHypercover.singleton.{0} (Sigma.desc (E.map B.toOver).f) →
        letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
        ∀ n : ℕ,
          Nonempty (Stacks.CechSite.cechCohomology E
              ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj n ≅
            Stacks.CechSite.cechCohomology (PreZeroHypercover.singleton.{0} f)
              ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj n)

/-- **The iterated fibre products of a finite affine covering of an affine object of the site
are again affine.** The product in the slice over `U` is a wide pullback of the covering
morphisms, computed on underlying schemes because the forgetful functor to the schemes over
`S` preserves finite limits; a wide pullback of a diagram of affine schemes is affine. -/
public theorem BigSite.isAffine_product_of_mem_affineCov {τ : CoveringTopology}
    {S : Scheme.{u}} (B : BigSite τ S) {U : B.category}
    (E : { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U })
    (hE : E ∈ B.affineCov U) :
    letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
    ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B.affineObjects := by
  have : HasFiniteLimits B.category := B.hasFiniteLimits_category
  intro p i
  have hincl : PreservesFiniteLimits (ObjectProperty.ι (schemeSizeBelow B.cutoff)) :=
    schemeBelowInclusion_preservesFiniteLimits B.cutoff B.aleph0_lt_cutoff
  let Z : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.1.f (i a))
  let Fd := Discrete.functor Z
  let W := (Over.ConstructProducts.conesEquivInverse U Fd).obj (limit.cone Fd)
  have hW : IsLimit W :=
    (IsLimit.ofConeEquiv (Over.ConstructProducts.conesEquiv U Fd).symm).symm (limit.isLimit Fd)
  let G : B.category ⥤ Scheme.{u} :=
    Over.forget (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff) ⋙
      ObjectProperty.ι (schemeSizeBelow B.cutoff)
  change IsAffine (G.obj (∏ᶜ Z).left)
  have hAff : ∀ j : WidePullbackShape (Fin (p + 1)),
      IsAffine ((Over.ConstructProducts.widePullbackDiagramOfDiagramOver U Fd ⋙ G).obj j) := by
    intro j
    cases j with
    | none => exact hE.1
    | some a => exact hE.2.2.1 (i a)
  exact Scheme.isAffine_of_isLimit (G.mapCone W) (isLimitOfPreserves G hW)

/-- **The disjoint union of a finite affine covering of an affine object belongs to the site.**
For a finite covering of an affine object of the site by affine objects whose underlying
morphisms have the covering morphism property and are jointly surjective, there is a morphism
`f : Y ⟶ X` of the site with `Y` affine whose image in the schemes over `S` is the morphism
from the disjoint union of the image of the covering; it is flat and surjective. The disjoint
union belongs to the site because a morphism locally of finite type from a quasi-compact
scheme does not raise the size of its target. -/
public theorem BigSite.exists_affine_coproduct_morphism {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) {X : B.category} (E : PreZeroHypercover.{0} X) [Finite E.I₀]
    (hA : ∀ i, E.X i ∈ B.affineObjects)
    (hP : ∀ i, coveringMorphismProperty τ (B.toOver.map (E.f i)).left)
    (hS : ∀ x : X.left.obj, ∃ i, x ∈ Set.range (B.toOver.map (E.f i)).left) :
    ∃ (Y : B.category) (f : Y ⟶ X), IsAffine Y.left.obj ∧
      Flat (B.toOver.map f).left ∧ Surjective (B.toOver.map f).left ∧
      (PreZeroHypercover.singleton.{0} f).map B.toOver =
        PreZeroHypercover.singleton.{0} (Sigma.desc (E.map B.toOver).f) := by
  let E' := E.map B.toOver
  have : Finite E'.I₀ := inferInstanceAs (Finite E.I₀)
  let T : Over S := ∐ E'.X
  let g : T ⟶ B.toOver.obj X := Sigma.desc E'.f
  let e : T.left ≅ ∐ (fun i ↦ (E'.X i).left) := PreservesCoproduct.iso (Over.forget S) E'.X
  have hg : g.left = e.hom ≫ Sigma.desc (fun i ↦ (E'.f i).left) := by
    rw [← cancel_epi e.inv, Iso.inv_hom_id_assoc]
    exact sigmaComparison_map_desc (Over.forget S) E'.X _ E'.f
  have haff : ∀ i, IsAffine (E'.X i).left := hA
  have : IsAffine T.left := IsAffine.of_isIso e.hom
  have hflat : ∀ i, Flat (E'.f i).left := fun i ↦ coveringMorphismProperty_flat τ (hP i)
  have : Flat g.left := by
    rw [hg]
    infer_instance
  have : IsZariskiLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : LocallyOfFinitePresentation (Sigma.desc (fun i ↦ (E'.f i).left)) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦
      coveringMorphismProperty_locallyOfFinitePresentation τ (hP i)
  have : LocallyOfFinitePresentation g.left := by
    rw [hg]
    infer_instance
  have hsurj : Surjective g.left := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨i, y, hy⟩ := hS x
    refine ⟨(Sigma.ι E'.X i).left y, ?_⟩
    change ((Sigma.ι E'.X i).left ≫ g.left) y = x
    rwa [← Over.comp_left, show Sigma.ι E'.X i ≫ g = E'.f i from Sigma.ι_comp_desc E'.f i]
  have hT : T.left.size < B.cutoff :=
    (Scheme.size_le_of_locallyOfFiniteType g.left).trans_lt X.left.property
  let Y : B.category :=
    Over.mk (ObjectProperty.homMk T.hom : (⟨T.left, hT⟩ : SchemeBelow B.cutoff) ⟶ _)
  let f : Y ⟶ X := Over.homMk (ObjectProperty.homMk g.left)
    (by apply ObjectProperty.hom_ext; exact g.w)
  exact ⟨Y, f, inferInstanceAs (IsAffine T.left), inferInstanceAs (Flat g.left), hsurj, rfl⟩

end Stacks.Adequate

end
