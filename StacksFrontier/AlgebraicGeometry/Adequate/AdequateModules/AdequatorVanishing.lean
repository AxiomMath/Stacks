module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Adequator
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsInjectivesSmall

/-!
# Vanishing of the higher right derived functors of the adequator

Let `U = Spec A` be affine. [Stacks, Tag 06ZU] asserts that `R^p A(𝓕) = 0` for all `p > 0` and
every object `𝓕` of `Adeq(𝒪)`, where `A` is the adequator of [Stacks, Tag 06ZS].

The source's proof reads an injective resolution `k(𝓕) ⟶ 𝓘^•` in the `𝒪`-modules on the site,
observes that `j(𝓘^•)` is a resolution of `j(k(𝓕))` ([Stacks, Tags 06YK] and [06VM]) by
injective *presheaves* of modules ([Stacks, Tag 03FB]), so that `A(𝓘^•) = Q(j(𝓘^•))` computes
`R^p A(𝓕)`, and finally kills the cohomology of `Q(j(𝓘^•))` in positive degrees by the
positive-degree vanishing of extension groups of [Stacks, Tag 06ZI]. The step that turns the
last vanishing into exactness of `Q(j(𝓘^•))` is a general fact about an adjunction, isolated
here as `Stacks.Adequate.exactAt_mapHomologicalComplex_of_coreflection`.

## Main definitions

* `Stacks.Adequate.AffineSectionsAcyclic` — right acyclicity of the affine-section functor at a
  sheaf of modules, which is what [Stacks, Tags 06YK and 06VM] give for an adequate one.
* `Stacks.Adequate.AffineSectionsExtVanishing` — the vanishing of the degree-`p` extension
  groups from the affine sections of a separating family into the affine sections of a sheaf of
  modules, which is what [Stacks, Tag 06ZI] gives.

## Main results

* `Stacks.Adequate.exactAt_mapHomologicalComplex_of_coreflection` — the homological core: for an
  adjunction `i ⊣ Q`, a fully faithful additive `G` preserving injective objects and carrying
  an injective resolution `I` of `X` to a resolution of `G(X)`, and a separating family in the
  domain of `i` along which the degree-`n` extension groups into `G(X)` vanish, the complex
  `Q(I^•)` is exact in degree `n > 0`.
* `Stacks.Adequate.isZero_rightDerived_of_coreflection` — the same conclusion read as the
  vanishing of `R^n Q(X)`.
* `Stacks.Adequate.isZero_rightDerived_adequator` — **[Stacks, Tag 06ZU]** for the named
  adequator `Stacks.Adequate.adequator`: `R^p A(𝓕) = 0` for every `p > 0` and every object `𝓕`
  of `Adeq(𝒪)`.
* `Stacks.Adequate.affineSectionsAcyclic_of_sections` — the module-valued half of
  [Stacks, Tag 06YK] for the affine-section functor, which reduces
  `Stacks.Adequate.AffineSectionsAcyclic` to a sectionwise vanishing.
* `Stacks.Adequate.additive_adequator` — the adequator is additive.

## Implementation notes

The inputs of the source's proof are carried as hypotheses.

* The statement is about `Stacks.Adequate.adequator`, so it inherits that definition's hypotheses
  `Q`, `E`, `adj`, `hj` and `comm`: a right adjoint `Q` of the inclusion of the adequate
  module-valued functors on the algebras *of the site* ([Stacks, Tag 06Z6] over that domain), the
  identification `E` of `Adeq(𝒪)` with those functors ([Stacks, Tag 06ZJ]), full faithfulness of
  the affine-section functor and the commuting square of [Stacks, Tag 06ZT]. The proof uses the
  source's `j` only through the adjunction `Stacks.Adequate.adequatorAdjunction`, which is built
  from the same affine-section functor.
* The abelian structure on `Adeq(𝒪)` enters as the three closure properties behind
  [Stacks, Tag 06VQ] (1), namely `ObjectProperty.IsClosedUnderKernels`,
  `ObjectProperty.IsClosedUnderCokernels` and `ObjectProperty.IsClosedUnderFiniteProducts` for
  adequacy; they are discharged by `Stacks.Adequate.adequate_isClosedUnderKernels` and its two
  companions. Taking them rather than an abstract `Abelian` instance keeps the additive
  structure on `Adeq(𝒪)` the one induced from the `𝒪`-modules, so that the inclusion is additive
  without a further hypothesis.
* `AffineSectionsAcyclic` is exactness of `j(𝓘^•)`, which the source gets from
  [Stacks, Tags 06YK and 06VM]. The library's Tag 06VM,
  `Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, computes cohomology as
  the right derived functor of sections of the underlying *abelian* sheaf, so reaching
  `AffineSectionsAcyclic` from it needs the abelian-group-valued half of Tag 06YK as well;
  `Stacks.Adequate.affineSectionsAcyclic_of_sections` performs the module-valued half, reducing
  it to the vanishing of the derived module-valued sections over each algebra of the site.
* That the affine-section functor carries injective sheaves of modules to injective presheaves
  of modules is `Stacks.Adequate.preservesInjectiveObjects_affineSectionsFunctor`, at the module
  universe `max u m`.
* `hP` together with `AffineSectionsExtVanishing` is what [Stacks, Tag 06ZI] supplies, the
  library's form of that tag, `AdequateFunctor.isZero_rightDerivedPlus_adequateCoreflection`,
  being stated for the coreflection on *all* `A`-algebras rather than on the algebras of the
  site.
* The general statement that `PresheafOfModules.pushforward` preserves injective objects is
  **false**: both of its factors fail, `PresheafOfModules.restrictScalars` already for
  `ℤ → ZMod 2` and `PresheafOfModules.pushforward₀` already for the trivial action of a
  nontrivial finite group. The affine-section functor is instead factored through the affine
  subsite of the big site, as restriction of sheaves of modules to that subsite along the scalar
  identification, an equivalence by the Comparison Lemma, followed by [Stacks, Tag 03FB] there.
* `Stacks.Adequate.additive_affineSectionsFunctor` and
  `Stacks.Adequate.preservesFiniteLimits_affineSectionsFunctor` are
  `Stacks.Adequate.affineSectionsFunctor_additive` and
  `Stacks.Adequate.affineSectionsFunctor_preservesFiniteLimits` at an independent value universe
  instead of `u`, which is the generality the adequator is stated in.

## References

* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06ZT](https://stacks.math.columbia.edu/tag/06ZT)
* [Stacks Project, Tag 06ZI](https://stacks.math.columbia.edu/tag/06ZI)
* [Stacks Project, Tag 06YK](https://stacks.math.columbia.edu/tag/06YK)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 03FB](https://stacks.math.columbia.edu/tag/03FB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m w v₃ u₃ v₄ u₄ v₅ u₅

/-- Module-valued functors on a chosen domain of `A`-algebras form an abelian category, being
presheaves of modules over the diagram of scalar rings. Recorded at this head so that instance
search does not rebuild the abelian structure at the independent value universe. -/
public instance (priority := 2000) AdequateFunctor.abelian_moduleValuedFunctorOn
    {R : Type u} [CommRing R] {C : Type u₃} [Category.{v₃} C] (ι : C ⥤ CommAlgCat.{u} R) :
    Abelian (AdequateFunctor.ModuleValuedFunctorOn.{m} ι) :=
  inferInstance

namespace Stacks.Adequate

/-! ### The homological core -/

section Coreflection

variable {C : Type u₃} [Category.{v₃} C] [Abelian C] {D : Type u₄} [Category.{v₄} D] [Abelian D]
  {E : Type u₅} [Category.{v₅} E] [Abelian E]

/-- The image of an injective resolution under an additive functor preserving injective objects
is an injective resolution of the image, provided the mapped augmentation is still a
quasi-isomorphism. -/
public def mapInjectiveResolution (G : C ⥤ E) [G.Additive] [G.PreservesInjectiveObjects]
    {X : C} (I : InjectiveResolution X)
    [QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι)] :
    InjectiveResolution (G.obj X) where
  cocomplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := G.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

/-- An additive left exact functor all of whose positive right derived functors vanish at `X`
carries an injective resolution of `X` to a resolution of the image of `X`. -/
public theorem quasiIso_mapHomologicalComplex_of_isZero_rightDerived
    [EnoughInjectives C] (G : C ⥤ E) [G.Additive] [PreservesFiniteLimits G]
    {X : C} (I : InjectiveResolution X)
    (hG : ∀ n : ℕ, 0 < n → IsZero ((G.rightDerived n).obj X)) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    let S := ((CochainComplex.single₀ C).obj X).sc' 0 0 1
    let T := I.cocomplex.sc' 0 0 1
    let φ : S ⟶ T :=
      (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map I.ι
    have : G.PreservesLeftHomologyOf S := G.preservesLeftHomology_of_zero_f S rfl
    have : G.PreservesLeftHomologyOf T :=
      G.preservesLeftHomology_of_zero_f T (HomologicalComplex.shape _ _ _ (by simp))
    have : ShortComplex.QuasiIso φ := (CochainComplex.quasiIsoAt₀_iff I.ι).mp inferInstance
    exact ShortComplex.quasiIso_map_of_preservesLeftHomology G φ
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (hG (n + 1) (Nat.succ_pos n)).of_iso (I.isoRightDerivedObj G (n + 1)).symm
    · exact HomologicalComplex.ExactAt.of_isZero
        (G.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)))

/-- **The homological core of [Stacks, Tag 06ZU].** Let `i ⊣ Q` be an adjunction with `i`
additive, let `G` be a fully faithful additive functor preserving injective objects which
carries an injective resolution `I` of `X` to a resolution of `G(X)`, and let `P` be a
separating family in the domain of `i` whose objects have no degree-`n` extensions into `G(X)`.
Then `Q(I^•)` is exact in degree `n > 0`. -/
@[stacks 06ZU "the homological step of the proof: exactness in positive degrees of a right
adjoint applied to an injective resolution, from the Ext vanishing along a separating family;
stated for an arbitrary adjunction"]
public theorem exactAt_mapHomologicalComplex_of_coreflection [HasExt.{w} E]
    (i : D ⥤ C) (Q : C ⥤ D) [i.Additive] [Q.Additive] (adj : i ⊣ Q)
    (G : C ⥤ E) [G.Additive] [G.Full] [G.Faithful] [G.PreservesInjectiveObjects]
    (P : ObjectProperty D) (hP : P.IsSeparating)
    {X : C} (I : InjectiveResolution X)
    [QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι)]
    (n : ℕ) (hn : 0 < n)
    (hExt : ∀ L : D, P L → Subsingleton (Abelian.Ext.{w} (G.obj (i.obj L)) (G.obj X) n)) :
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt n := by
  let R := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  rw [HomologicalComplex.exactAt_iff' R (n - 1) n (n + 1)
    (ComplexShape.prev_eq' (ComplexShape.up ℕ)
      (ComplexShape.up_mk (n - 1) n (Nat.sub_add_cancel hn))) (by simp)]
  let S : ShortComplex D := ShortComplex.mk
    (Q.map (I.cocomplex.d (n - 1) n)) (Q.map (I.cocomplex.d n (n + 1)))
    (by rw [← Q.map_comp, I.cocomplex.d_comp_d, Q.map_zero])
  change S.Exact
  let v : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have hlift (L : D) (hL : P L) (k : L ⟶ kernel S.g) : ∃ ψ : L ⟶ S.X₁, k = ψ ≫ v := by
    let φ : L ⟶ Q.obj (I.cocomplex.X n) := k ≫ kernel.ι S.g
    let t := (adj.homEquiv L (I.cocomplex.X n)).symm φ
    have ht : t ≫ I.cocomplex.d n (n + 1) = 0 := by
      apply (adj.homEquiv L (I.cocomplex.X (n + 1))).injective
      rw [adj.homEquiv_naturality_right, adj.homAddEquiv_zero]
      simp [t, φ, S]
    let J := mapInjectiveResolution G I
    let t' : G.obj (i.obj L) ⟶ J.cocomplex.X n := G.map t
    have ht' : t' ≫ J.cocomplex.d n (n + 1) = 0 := by
      change G.map t ≫ G.map _ = 0
      rw [← G.map_comp, ht, G.map_zero]
    have hα : J.extMk t' (n + 1) (by omega) ht' = 0 := (hExt L hL).allEq _ _
    obtain ⟨g, hg⟩ :=
      (J.extMk_eq_zero_iff t' (n + 1) (by omega) ht' (n - 1) (by omega)).1 hα
    change G.obj (i.obj L) ⟶ G.obj (I.cocomplex.X (n - 1)) at g
    change g ≫ G.map (I.cocomplex.d (n - 1) n) = G.map t at hg
    have hg₀ : G.preimage g ≫ I.cocomplex.d (n - 1) n = t :=
      G.map_injective (by rwa [G.map_comp, G.map_preimage])
    refine ⟨adj.homEquiv L (I.cocomplex.X (n - 1)) (G.preimage g), ?_⟩
    apply (cancel_mono (kernel.ι S.g)).1
    rw [Category.assoc]
    change φ = _ ≫ v ≫ kernel.ι S.g
    rw [show v ≫ kernel.ι S.g = S.f from kernel.lift_ι _ _ _]
    change φ = _ ≫ Q.map (I.cocomplex.d (n - 1) n)
    rw [← adj.homEquiv_naturality_right, hg₀]
    exact ((adj.homEquiv L (I.cocomplex.X n)).apply_symm_apply φ).symm
  have : Epi v := ⟨fun f g h => by
    apply hP f g
    intro L hL k
    obtain ⟨ψ, rfl⟩ := hlift L hL k
    simpa only [Category.assoc] using congrArg (fun z => ψ ≫ z) h⟩
  exact S.exact_iff_epi_kernel_lift.2 this

/-- **The homological core of [Stacks, Tag 06ZU]**, read as the vanishing of a right derived
functor of the right adjoint: under the hypotheses of
`Stacks.Adequate.exactAt_mapHomologicalComplex_of_coreflection`, `R^n Q(X) = 0`. -/
@[stacks 06ZU "the same step read as the vanishing of the right derived functors of the right
adjoint; stated for an arbitrary adjunction"]
public theorem isZero_rightDerived_of_coreflection [EnoughInjectives C] [HasExt.{w} E]
    (i : D ⥤ C) (Q : C ⥤ D) [i.Additive] [Q.Additive] (adj : i ⊣ Q)
    (G : C ⥤ E) [G.Additive] [G.Full] [G.Faithful] [G.PreservesInjectiveObjects]
    [PreservesFiniteLimits G]
    (P : ObjectProperty D) (hP : P.IsSeparating) (X : C)
    (hacyclic : ∀ k : ℕ, 0 < k → IsZero ((G.rightDerived k).obj X))
    (n : ℕ) (hn : 0 < n)
    (hExt : ∀ L : D, P L → Subsingleton (Abelian.Ext.{w} (G.obj (i.obj L)) (G.obj X) n)) :
    IsZero ((Q.rightDerived n).obj X) := by
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (injectiveResolution X).ι) :=
    quasiIso_mapHomologicalComplex_of_isZero_rightDerived G (injectiveResolution X) hacyclic
  exact (exactAt_mapHomologicalComplex_of_coreflection.{w} i Q adj G P hP
    (injectiveResolution X) n hn hExt).isZero_homology.of_iso
      ((injectiveResolution X).isoRightDerivedObj Q n)

end Coreflection

/-! ### Exactness and acyclicity of the affine-section functor -/

section Sections

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- The affine-section functor at an independent value universe is additive: it is the forgetful
functor to presheaves of modules followed by a pushforward, and both are computed on sections. -/
public instance additive_affineSectionsFunctor (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    (affineSectionsFunctor.{u, max u m} B A f).Additive where
  map_add := by intros; rfl

/-- The affine-section functor at an independent value universe preserves finite limits, being
the forgetful functor to presheaves of modules followed by a pushforward. -/
public instance preservesFiniteLimits_affineSectionsFunctor (A : CommRingCat.{u})
    (f : Spec A ⟶ S) : PreservesFiniteLimits (affineSectionsFunctor.{u, max u m} B A f) :=
  comp_preservesFiniteLimits (SheafOfModules.forget.{max u m} B.structureSheaf)
    (PresheafOfModules.pushforward.{max u m} (affineRingMap B A f))

variable [HasSheafify B.topology AddCommGrpCat.{max u m}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
  [EnoughInjectives (SheafOfModules.{max u m} B.structureSheaf)]

/-- Right acyclicity of the affine-section functor at a sheaf of modules on the site: all its
positive right derived functors vanish there. For an adequate sheaf of modules this is what
[Stacks, Tags 06YK and 06VM] assert, and it is what makes the affine sections of an injective
resolution a resolution of the affine sections. -/
public abbrev AffineSectionsAcyclic (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) : Prop :=
  ∀ k : ℕ, 0 < k → IsZero (((affineSectionsFunctor.{u, max u m} B A f).rightDerived k).obj F)

/-- **[Stacks, Tag 06YK] for the affine-section functor.** The affine-section functor is right
acyclic at a sheaf of modules as soon as its module-valued sections over every algebra of the
site are, evaluation of presheaves of modules being exact. -/
@[stacks 06YK "the module-valued half for the affine-section functor: its right derived
functors are computed on sections over the algebras of the site, evaluation of presheaves of
modules being exact"]
public theorem affineSectionsAcyclic_of_sections (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (hsec : ∀ (k : ℕ), 0 < k →
      ∀ X : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖᵒᵖ,
      IsZero (((affineSectionsFunctor.{u, max u m} B A f ⋙
        PresheafOfModules.evaluation
          (AdequateFunctor.algebraRingDiagramOn
            (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
          X).rightDerived k).obj F)) :
    AffineSectionsAcyclic.{u, m} B A f F := by
  intro k hk
  refine (IsZero.iff_id_eq_zero _).2 (PresheafOfModules.hom_ext fun X => ?_)
  have : (PresheafOfModules.evaluation.{max u m} (AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
      X).PreservesHomology := Functor.preservesHomologyOfExact _
  exact ((hsec k hk X).of_iso ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso
    (affineSectionsFunctor.{u, max u m} B A f)
    (PresheafOfModules.evaluation.{max u m} (AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
      X) k).app F)).eq_of_src _ _

end Sections

/-! ### Tag 06ZU for the named adequator -/

section Adequator

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))
  (Q : AdequateFunctor.ModuleValuedFunctorOn.{max u m}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ⥤
    (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).FullSubcategory)
  (E : (adequate.{u, max u m} B).FullSubcategory ≌
    (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).FullSubcategory)
  [HasSheafify B.topology AddCommGrpCat.{max u m}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m}]

omit [HasSheafify B.topology AddCommGrpCat.{max u m}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m}] in
/-- The adequator is additive, being a right adjoint of the inclusion of `Adeq(𝒪)` into the
`𝒪`-modules on the site, which is additive. -/
public lemma additive_adequator
    (adj : (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι ⊣ Q)
    (hj : (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).FullyFaithful)
    (comm : E.functor ⋙ (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, max u m} B).ι ⋙ affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))) :
    (adequator.{u, max u m} B Q E).Additive :=
  (adequatorAdjunction.{u, max u m} B Q E adj hj comm).right_adjoint_additive

variable [HasExt.{w} (AdequateFunctor.ModuleValuedFunctorOn.{max u m}
  (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))]

/-- The vanishing of the degree-`p` extension groups from the affine sections of the members of
a family `P` of adequate `𝒪`-modules into the affine sections of a sheaf of modules `F`. For a
separating family `P` and an adequate `F` this is what [Stacks, Tag 06ZI] asserts. -/
public abbrev AffineSectionsExtVanishing
    (P : ObjectProperty (adequate.{u, max u m} B).FullSubcategory)
    (F : SheafOfModules.{max u m} B.structureSheaf) (p : ℕ) : Prop :=
  ∀ L : (adequate.{u, max u m} B).FullSubcategory, P L →
    Subsingleton (Abelian.Ext.{w}
      ((affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).obj L.obj)
      ((affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).obj F) p)

variable [(adequate.{u, max u m} B).IsClosedUnderKernels]
  [(adequate.{u, max u m} B).IsClosedUnderCokernels]
  [(adequate.{u, max u m} B).IsClosedUnderFiniteProducts]
  [EnoughInjectives (SheafOfModules.{max u m} B.structureSheaf)]

/-- **[Stacks, Tag 06ZU].** For `U = Spec A` affine, every object `𝓕` of `Adeq(𝒪)` and every
`p > 0`, the `p`-th right derived functor of the adequator of [Stacks, Tag 06ZS] vanishes at
`𝓕`: the adequator of an injective resolution of `𝓕` is exact in positive degrees. -/
@[stacks 06ZU "the full statement, `R^p A(F) = 0` for every `p > 0` and every object of
`Adeq(O)`, for the named adequator of Tag 06ZS. Assumed: that adequator's own inputs (`Q`, `E`,
`adj` from Tags 06Z6 and 06ZJ over the algebras of the site, `hj` and `comm` from Tag 06ZT),
right acyclicity of the affine-section functor (`hacyclic`, Tags 06YK and 06VM), the
positive-degree Ext vanishing along a separating family (`hP` and `hExt`, Tag 06ZI), the three
closure properties of Tag 06VQ (1) and `EnoughInjectives` for the sheaves of modules on the
site. Preservation of injective objects by the affine-section functor is proved, through Tag 03FB
on the affine subsite"]
public theorem isZero_rightDerived_adequator
    (adj : (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι ⊣ Q)
    (hj : (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).FullyFaithful)
    (comm : E.functor ⋙ (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, max u m} B).ι ⋙ affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A)))
    (F : (adequate.{u, max u m} B).FullSubcategory) (p : ℕ) (hp : 0 < p)
    (hacyclic : AffineSectionsAcyclic.{u, m} B A (𝟙 (Spec A)) F.obj)
    (P : ObjectProperty (adequate.{u, max u m} B).FullSubcategory) (hP : P.IsSeparating)
    (hExt : AffineSectionsExtVanishing.{u, m, w} B P F.obj p) :
    letI : (adequator.{u, max u m} B Q E).Additive := additive_adequator B Q E adj hj comm
    IsZero (((adequator.{u, max u m} B Q E).rightDerived p).obj F.obj) := by
  have : (adequator.{u, max u m} B Q E).Additive := additive_adequator B Q E adj hj comm
  have := preservesInjectiveObjects_affineSectionsFunctor.{u, m} B
  have : (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).Full := hj.full
  have : (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).Faithful := hj.faithful
  exact isZero_rightDerived_of_coreflection.{w} (adequate.{u, max u m} B).ι
    (adequator.{u, max u m} B Q E) (adequatorAdjunction.{u, max u m} B Q E adj hj comm)
    (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))) P hP F.obj hacyclic p hp hExt

end Adequator

end Stacks.Adequate

end
