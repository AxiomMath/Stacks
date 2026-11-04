module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineFullSubsitePullbacks
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDisjointUnion

/-!
# Quasi-coherent modules on the flat-fppf site form a weak Serre subcategory

Let `𝒳` be an algebraic stack. This file proves **Stacks 07B4 (2)**: the quasi-coherent modules
on the flat-fppf site `𝒳_{flat,fppf}` (**Stacks 0787**), ringed by the restriction of the
structure sheaf of `𝒳`, form a weak Serre subcategory of all modules.

## The proof

The flat objects of `𝒳` lying over affine schemes form a cover-dense full subcategory `A` of
`𝒳_{flat,fppf}` (`AlgebraicGeometry.Stack.FlatFppf.isCoverDense_affineObject_ι`). Together with
the class `Q` of arrows of `A` lying over flat, locally finitely presented morphisms of schemes it
is a site of affine schemes in the sense of
`StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite`:

* `A` has fibre products along `Q`, and the underlying scheme functor preserves them
  (`AlgebraicGeometry.Stack.AffineFullSubsite`): they are computed in `𝒳` (**Stacks 06N5**), and
  a base change of an arrow of `Q` lies over a flat morphism, so its source is again a flat
  object;
* every covering sieve of `A` contains a finite, jointly surjective family of arrows of `Q`: a
  covering sieve of an object over an affine scheme is refined by the lift of a finite chosen fppf
  covering by affine schemes (**Stacks 021P**,
  `AlgebraicGeometry.BigFppfOver.exists_finite_affine_covering_refinement`);
* such a family generates a covering sieve;
* every arrow `y ⟶ x` of `A` factors, locally on `y` for the fppf topology, through a pair of
  arrows over flat morphisms (`AlgebraicGeometry.Stack.factorizationSieve_mem`, the 2-fibre product
  argument), and that covering is refined by a finite cover as above.

`Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite` then concludes.

## Main results

* `AlgebraicGeometry.Stack.exists_finite_affine_isCovering_le_of_mem_associatedTopology`: a
  covering sieve of an object over an affine scheme contains a finite chosen fppf covering family
  by objects over affine schemes.
* `AlgebraicGeometry.Stack.FlatFppf.isWeakSerreClass_isQuasicoherentOnSite`: **Stacks 07B4 (2)**.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack

universe u t v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Refinement

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **A covering sieve of an object over an affine scheme contains a finite chosen fppf covering
family by objects over affine schemes.** For a category `p : X ⥤ (Sch/S)_{fppf}` fibred in
groupoids and an object `y` of `X` over an affine scheme, every covering sieve of `y` for the
associated fppf topology (**Stacks 06TP**) contains a finite family of arrows into `y`, with
sources over affine schemes, whose image is a chosen covering family of the big fppf category
over `S`.

Downstairs this is **Stacks 021P**
(`AlgebraicGeometry.BigFppfOver.exists_finite_affine_covering_refinement`); it is lifted to `X`
by `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, applied to the
class of families that are finite affine chosen coverings whenever their target is affine. -/
theorem exists_finite_affine_isCovering_le_of_mem_associatedTopology
    (hp : p.IsFiberedInGroupoids) {y : X}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)))
    (T : Sieve y) (hT : T ∈ associatedTopology B S hS p B.topology y) :
    ∃ E : PreZeroHypercover.{u + 1} y, Finite E.I₀ ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (E.X i)))) ∧
      BigFppfOver.IsCovering B S hS ⟨p.obj y, E.map p⟩ ∧ E.presieve₀ ≤ T.arrows := by
  classical
  obtain ⟨E, hE, hle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS p B.topology
    (fun E => IsAffineOver B S hS E.1 → Finite E.2.I₀ ∧
      (∀ i, IsAffineOver B S hS (E.2.X i)) ∧ BigFppfOver.IsCovering B S hS E)
    (fun U R hR => by
      by_cases hU : IsAffineOver B S hS U
      · obtain ⟨Q, hfin, haff, hcov, hQle⟩ :=
          BigFppfOver.exists_finite_affine_covering_refinement B S hS hU hR
        exact ⟨Q, fun _ => ⟨hfin, haff, hcov⟩, hQle⟩
      · refine ⟨⟨Σ V : BigFppfOver B S hS, {g : V ⟶ U // R g}, fun i => i.1,
          fun i => i.2.1⟩, fun h => absurd h hU, ?_⟩
        rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
        exact fun i => i.2.2)
    hp T hT
  obtain ⟨hfin, haff, hcov⟩ := hE hy
  exact ⟨E, hfin, haff, hcov, hle⟩

end Refinement

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- The flat objects of `𝒳` lying over affine schemes. -/
local notation "𝒜" =>
  AffineFullSubsite.affineObject B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳)

/-- The affine scheme lying under a flat object over an affine scheme. -/
local notation "𝒮" =>
  ObjectProperty.ι 𝒜 ⋙ AffineFullSubsite.schemeFunctor B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳)

/-- The flat objects over affine schemes are cover dense in the flat-fppf site: this is
`AlgebraicGeometry.Stack.FlatFppf.isCoverDense_affineObject_ι`, for the spelling of those objects
in `AlgebraicGeometry.Stack.AffineFullSubsite`. -/
instance isCoverDense_affineFullSubsite_ι :
    (ObjectProperty.ι 𝒜).IsCoverDense (inclusionTopology B S hS 𝒳) :=
  isCoverDense_affineObject_ι B S hS 𝒳

/-- The arrows between flat objects over affine schemes lying over flat, locally finitely
presented morphisms of schemes. -/
abbrev flatLfp : MorphismProperty (ObjectProperty.FullSubcategory 𝒜) :=
  AffineFullSubsite.morphismProperty B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳)
    (@Flat ⊓ @LocallyOfFinitePresentation)

variable {B S hS 𝒳} in
/-- **A covering sieve in `𝒳` of a flat object over an affine scheme contains a finite cover by
arrows of `flatLfp`.** The finite chosen fppf covering family of
`AlgebraicGeometry.Stack.exists_finite_affine_isCovering_le_of_mem_associatedTopology` has
sources over affine schemes, and they are flat objects because its members lie over flat
morphisms. -/
theorem exists_isCover_of_mem_associatedTopology {x : ObjectProperty.FullSubcategory 𝒜}
    (T : Sieve x.obj.obj) (hT : T ∈ associatedTopology B S hS 𝒳.val.val.p B.topology x.obj.obj) :
    ∃ (I : Type (u + 1)) (W : I → ObjectProperty.FullSubcategory 𝒜) (g : ∀ i, W i ⟶ x),
      Stacks.FlatAffineSite.IsCover (𝒮) (flatLfp B S hS 𝒳) g ∧
        ∀ i, T (g i).hom.hom := by
  obtain ⟨E, hfin, haff, hcov, hle⟩ := exists_finite_affine_isCovering_le_of_mem_associatedTopology
    B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x.property T hT
  obtain ⟨hsurj, hfl⟩ := B.jointlySurjective_and_flat_and_lfp_of_isCovering hcov
  have hobj : ∀ i, flatObject B S hS 𝒳.val (E.X i) := fun i =>
    flatObject_of_flat B S hS 𝒳 (E.f i) (hfl i).1 x.obj.property
  refine ⟨E.I₀, fun i => ⟨⟨E.X i, hobj i⟩, haff i⟩,
    fun i => ObjectProperty.homMk (ObjectProperty.homMk (E.f i)), ⟨hfin, fun i => hfl i, hsurj⟩,
    fun i => hle _ _ (Presieve.ofArrows.mk i)⟩

/-- **Every covering sieve of the flat objects over affine schemes contains a finite cover by
arrows of `flatLfp`.** -/
theorem hasCoverRefinements_flatLfp :
    Stacks.FlatAffineSite.HasCoverRefinements.{u + 1} (𝒮) (flatLfp B S hS 𝒳)
      ((ObjectProperty.ι 𝒜).inducedTopology (inclusionTopology B S hS 𝒳)) := by
  intro x T hT
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hT
  have hT' : (T.functorPushforward (ObjectProperty.ι 𝒜)).functorPushforward
      (objectProperty B S hS 𝒳).ι ∈ associatedTopology B S hS 𝒳.val.val.p B.topology x.obj.obj :=
    (CoverPreserving.of_isContinuous (objectProperty B S hS 𝒳).ι (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology)).cover_preserve hT
  obtain ⟨I, W, g, hg, hmem⟩ := exists_isCover_of_mem_associatedTopology _ hT'
  refine ⟨I, W, g, hg, fun i => ?_⟩
  obtain ⟨Z, g₁, h₁, ⟨Z', g₂, h₂, hg₂, rfl⟩, he⟩ := hmem i
  have : g i = (ObjectProperty.homMk (ObjectProperty.homMk h₁ ≫ h₂) : W i ⟶ Z') ≫ g₂ :=
    by ext; simpa using he
  rw [this]
  exact T.downward_closed hg₂ _

/-- **A finite jointly surjective family of arrows of `flatLfp` generates a covering sieve.** Its
image in the big fppf category over `S` is an fppf covering family, so it generates a covering
sieve there, and its members are strongly cartesian. -/
theorem coversAreCovering_flatLfp :
    Stacks.FlatAffineSite.CoversAreCovering.{u + 1} (𝒮) (flatLfp B S hS 𝒳)
      ((ObjectProperty.ι 𝒜).inducedTopology (inclusionTopology B S hS 𝒳)) := by
  intro x I W g hg
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine (inclusionTopology B S hS 𝒳).superset_covering ?_ (?_ : Sieve.ofArrows
    (fun i => (W i).obj) (fun i => (g i).hom) ∈ inclusionTopology B S hS 𝒳 x.obj)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i => ⟨W i, g i, 𝟙 _, Sieve.ofArrows_mk _ _ i, (Category.id_comp _).symm⟩
  rw [inclusionTopology, Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck ⟨fun _ _ _ => inferInstance, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
  rw [associatedTopology, Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck
    ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian 𝒳.val.isFiberedInGroupoids q, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
  show Sieve.ofArrows _ _ ∈ _
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  refine BigFppfSite.ofArrows_mem_topology B _ _ _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun z => ?_, fun i => hg.mem i⟩)
  obtain ⟨i, y, hy⟩ := hg.surj z
  exact ⟨i, y, hy⟩

/-- **Every arrow of the flat objects over affine schemes factors, locally for a finite cover by
arrows of `flatLfp`, through a pair of arrows over flat morphisms.** This is the 2-fibre product
argument `AlgebraicGeometry.Stack.factorizationSieve_mem`, refined to a finite cover. -/
theorem hasFlatFactorizations_flatLfp :
    Stacks.FlatAffineSite.HasFlatFactorizations.{u + 1} (𝒮)
      (flatLfp B S hS 𝒳) := by
  intro x y h
  obtain ⟨I, W, r, hr, hmem⟩ := exists_isCover_of_mem_associatedTopology _
    (factorizationSieve_mem B S hS (y' := x.obj) y.obj.property h.hom.hom)
  refine ⟨I, W, r, hr, fun i => ?_⟩
  obtain ⟨w, c, a, b, haff, ha, hb, hca, hcb⟩ := hmem i
  let Z : ObjectProperty.FullSubcategory 𝒜 :=
    ⟨⟨w, flatObject_of_flat B S hS 𝒳 a ha y.obj.property⟩, haff⟩
  refine ⟨Z, ObjectProperty.homMk (ObjectProperty.homMk c),
    ObjectProperty.homMk (ObjectProperty.homMk a), ObjectProperty.homMk (ObjectProperty.homMk b),
    r i, ha, hb, (hr.mem i).1, ?_, ?_⟩
  · ext; simpa using hca
  · ext; simpa using hcb

/-- Sheafification of abelian presheaves on the flat-fppf site, at the universe of the structure
sheaf's sections: the site is essentially small. -/
instance hasSheafify_inclusionTopology_addCommGrpCat :
    HasSheafify (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the flat-fppf site, which is essentially small, the morphisms of abelian presheaves
inverted by sheafification are the locally bijective ones. -/
instance wEqualsLocallyBijective_inclusionTopology_addCommGrpCat :
    (inclusionTopology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **Stacks 07B4 (2).** For an algebraic stack `𝒳`, the quasi-coherent modules on the flat-fppf
site `𝒳_{flat,fppf}`, ringed by `𝒪_{𝒳_{flat,fppf}}`, form a weak Serre subcategory of
`Mod(𝒪_{𝒳_{flat,fppf}})`.

The flat objects over affine schemes are a cover-dense subsite of `𝒳_{flat,fppf}` which, with the
arrows over flat, locally finitely presented morphisms, has fibre products along its coverings,
finite covers refining its covering sieves, and flat factorizations of its arrows; so
`Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite` applies. -/
@[stacks 07B4 "part (2): QCoh(O_{X_{flat,fppf}}) is a weak Serre subcategory of \
Mod(O_{X_{flat,fppf}})"]
theorem isWeakSerreClass_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf
      (subsiteRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
        (objectProperty B S hS 𝒳)).O) :
      ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (subsiteRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
          (objectProperty B S hS 𝒳)).O))).IsWeakSerreClass := by
  have hP : ∀ ⦃x y : 𝒳.val.val.obj⦄ (f : x ⟶ y),
      (@Flat ⊓ @LocallyOfFinitePresentation) ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).map f) →
        objectProperty B S hS 𝒳 y → objectProperty B S hS 𝒳 x :=
    fun _ _ f hf hy => closedUnderFlatMorphisms B S hS 𝒳 f hf.1 hf.2 hy
  have hO : Presheaf.IsSheaf (inclusionTopology B S hS 𝒳)
      ((AffineFullSubsite.schemeFunctor B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳)).op ⋙
        Scheme.Γ) :=
    (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
      (objectProperty B S hS 𝒳)).property
  have : ∀ x : ObjectProperty.FullSubcategory 𝒜, IsAffine ((𝒮).obj x) := fun x => x.property
  obtain ⟨-, _, _⟩ := flat_and_locallyOfFinitePresentation_instances.{u}
  have := AffineFullSubsite.hasPullbacks 𝒳.val.isFiberedInGroupoids hP
  have := AffineFullSubsite.isStableUnderBaseChange 𝒳.val.isFiberedInGroupoids hP
  exact Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite
    (inclusionTopology B S hS 𝒳)
    (AffineFullSubsite.schemeFunctor B S hS 𝒳.val.val.p (objectProperty B S hS 𝒳)) hO 𝒜
    (Q := flatLfp B S hS 𝒳) (fun _ _ _ hf => hf.1)
    (AffineFullSubsite.preservesPullbacksAlong 𝒳.val.isFiberedInGroupoids hP)
    (hasCoverRefinements_flatLfp B S hS 𝒳) (coversAreCovering_flatLfp B S hS 𝒳)
    (hasFlatFactorizations_flatLfp B S hS 𝒳)

end FlatFppf

end AlgebraicGeometry.Stack

end
