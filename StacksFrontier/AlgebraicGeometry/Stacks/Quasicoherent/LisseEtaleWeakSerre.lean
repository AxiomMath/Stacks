module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineFullSubsitePullbacks
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleGraphFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LisseEtaleCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtalePrecoverage

/-!
# Quasi-coherent modules on the lisse-étale site form a weak Serre subcategory

Let `𝒳` be an algebraic stack. This file proves **Stacks 07B4, part (1)**: the quasi-coherent
modules on the lisse-étale site `𝒳_{lisse,étale}` of `𝒳`, ringed by the restriction of the
structure sheaf, form a weak Serre subcategory of all modules.

## The proof

`Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite` proves the weak
Serre property for any essentially small site carrying a cover-dense full subcategory `A` of
objects over affine schemes which, with the class `Q` of arrows it is given, is a site of affine
schemes with fibre products along `Q` and flat factorizations. Here `A` is the smooth objects
over affine schemes and `Q` the arrows lying over étale morphisms of schemes; the hypotheses of
that theorem are discharged as follows.

* `A` is cover dense: every smooth object is covered by the lifts of an affine open cover of its
  scheme, which are again smooth
  (`AlgebraicGeometry.Stack.LisseEtale.isCoverDense_affineObject_ι`).
* `Q` has fibre products in `A`, stable under base change, preserved by the scheme functor:
  `StacksFrontier.AlgebraicGeometry.Stacks.AffineFullSubsitePullbacks` (**Stacks 06N5**), smooth
  objects being closed under étale arrows.
* Every covering sieve of `A` contains a finite jointly surjective family of members of `Q`
  (`AlgebraicGeometry.Stack.LisseEtale.hasCoverRefinements`, **Stacks 0218** through
  `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`), and every such
  family covers (`AlgebraicGeometry.Stack.LisseEtale.coversAreCovering`).
* Every arrow `h : Y ⟶ X` of `A` factors, étale locally on `Y`, through a pair of smooth arrows
  out of an object of `A` (`AlgebraicGeometry.Stack.LisseEtale.hasFlatFactorizations`): this is
  `AlgebraicGeometry.Stack.LisseEtale.factorizationSieveOf_mem`, the graph of `h` in the 2-fibre
  product `X ×_{x, 𝒳} (Sch/Y)`, whose projections are smooth.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isWeakSerreClass_isQuasicoherentOnSite`: **Stacks 07B4,
  part (1)**.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 06N5](https://stacks.math.columbia.edu/tag/06N5)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack

universe u t v v'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AffineFullSubsite

variable {𝒞 : Type v} [Category.{v'} 𝒞] (p : 𝒞 ⥤ BigFppfOver B S hS) (P : ObjectProperty 𝒞)

/-- **A covering sieve for the étale topology of an object of `A` contains a cover of `A`**: a
finite jointly surjective family of arrows of `A` lying over étale morphisms, provided `P` is
closed under arrows lying over étale morphisms. This is **Stacks 0218** localized at `S`, carried
to `𝒞` by `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`. -/
theorem exists_isCover_etale_of_mem (hp : p.IsFiberedInGroupoids)
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), Etale ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x)
    (X : (affineObject B S hS p P).FullSubcategory) (T : Sieve ((inclusion B S hS p P).obj X))
    (hT : T ∈ associatedTopology B S hS p (etaleTopology B) ((inclusion B S hS p P).obj X)) :
    ∃ (I : Type (u + 1)) (W : I → (affineObject B S hS p P).FullSubcategory) (g : ∀ i, W i ⟶ X),
      Stacks.FlatAffineSite.IsCover ((affineObject B S hS p P).ι ⋙ schemeFunctor B S hS p P)
        (morphismProperty B S hS p P @Etale) g ∧ ∀ i, T ((inclusion B S hS p P).map (g i)) := by
  classical
  obtain ⟨E, hE, hle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS p
    (etaleTopology B)
    (fun E => IsAffineOver B S hS E.1 → Finite E.2.I₀ ∧ (∀ i, IsAffineOver B S hS (E.2.X i)) ∧
      etaleCovering B ⟨(BigFppfOver.forget B S hS).obj E.1, E.2.map (BigFppfOver.forget B S hS)⟩)
    (fun U R hR => by
      by_cases hU : IsAffineOver B S hS U
      · obtain ⟨E, hfin, haff, hcov, hle⟩ :=
          BigFppfOver.exists_finite_affine_etaleCovering_refinement B S hS hU hR
        exact ⟨E, fun _ => ⟨hfin, haff, hcov⟩, hle⟩
      · refine ⟨⟨Σ V : BigFppfOver B S hS, {g : V ⟶ U // R g}, fun i => i.1, fun i => i.2.1⟩,
          fun h => absurd h hU, ?_⟩
        rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
        exact fun i => i.2.2)
    hp T hT
  obtain ⟨hfin, haff, hcov⟩ := hE X.property
  have hmem : ((E.map p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
      etalePrecoverage B ((BigFppfOver.forget B S hS).obj (p.obj ((inclusion B S hS p P).obj X))) :=
    ⟨_, rfl, hcov⟩
  have het : ∀ i, Etale ((p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)) := fun i =>
    etale_of_mem_etalePrecoverage B _ hmem _ (Presieve.ofArrows.mk i)
  let W (i : E.I₀) : (affineObject B S hS p P).FullSubcategory :=
    ⟨⟨E.X i, hP _ (het i) X.obj.property⟩, haff i⟩
  let g (i : E.I₀) : W i ⟶ X := ObjectProperty.homMk (ObjectProperty.homMk (E.f i))
  refine ⟨E.I₀, W, g, ⟨hfin, het, fun x => ?_⟩, fun i => hle _ _ (Presieve.ofArrows.mk i)⟩
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 hcov.2).1 x
  exact ⟨i, y, hy⟩

end AffineFullSubsite

namespace LisseEtale

variable (𝒳 : AlgebraicStacks.{u, t} B S hS)

/-- The smooth objects of `𝒳` lying over affine schemes, read as the affine part of the full
subcategory of smooth objects. This is `AlgebraicGeometry.Stack.LisseEtale.affineObject`. -/
abbrev affineSmooth : ObjectProperty (LisseEtale.{u, t} B S hS 𝒳) :=
  AffineFullSubsite.affineObject B S hS 𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳)

/-- The scheme functor of the smooth objects over affine schemes. -/
abbrev affineSmoothScheme : (affineSmooth B S hS 𝒳).FullSubcategory ⥤ Scheme.{u} :=
  (affineSmooth B S hS 𝒳).ι ⋙
    AffineFullSubsite.schemeFunctor B S hS 𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳)

/-- The arrows between smooth objects over affine schemes lying over étale morphisms. -/
abbrev affineEtale : MorphismProperty (affineSmooth B S hS 𝒳).FullSubcategory :=
  AffineFullSubsite.morphismProperty B S hS 𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳) @Etale

/-- The topology the smooth objects over affine schemes inherit from the lisse-étale site. -/
abbrev affineSmoothTopology : GrothendieckTopology (affineSmooth B S hS 𝒳).FullSubcategory :=
  (affineSmooth B S hS 𝒳).ι.inducedTopology (inclusionTopology.{u, t} B S hS 𝒳)

/-- The inclusion of the smooth objects over affine schemes into `𝒳`. -/
abbrev affineSmoothInclusion : (affineSmooth B S hS 𝒳).FullSubcategory ⥤ 𝒳.val.val.obj :=
  AffineFullSubsite.inclusion B S hS 𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳)

variable {B S hS 𝒳} in
/-- An object with an arrow over an étale morphism to a smooth object is smooth. -/
theorem smoothObject_of_etale ⦃x y : 𝒳.val.val.obj⦄ (f : x ⟶ y)
    (hf : Etale ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).map f))
    (hy : smoothObject.{u, t} B S hS 𝒳 y) : smoothObject.{u, t} B S hS 𝒳 x := by
  refine closedUnderSmoothMorphisms B S hS 𝒳 f ?_ hy
  have : Etale (B.inclusion.map (𝒳.val.val.p.map f).left) := hf
  infer_instance

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- The smooth objects of `𝒳` over affine schemes form a cover-dense full subcategory of the
lisse-étale site. -/
instance isCoverDense_affineSmooth_ι :
    (affineSmooth B S hS 𝒳).ι.IsCoverDense (inclusionTopology.{u, t} B S hS 𝒳) :=
  isCoverDense_affineObject_ι B S hS 𝒳

/-- **Every covering sieve of the smooth objects over affine schemes contains a cover**: a finite
jointly surjective family of arrows over étale morphisms. -/
theorem hasCoverRefinements :
    Stacks.FlatAffineSite.HasCoverRefinements.{u + 1} (affineSmoothScheme B S hS 𝒳)
      (affineEtale B S hS 𝒳) (affineSmoothTopology B S hS 𝒳) := by
  intro X T hT
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hT
  have h𝒳 := (CoverPreserving.of_isContinuous (smoothObject.{u, t} B S hS 𝒳).ι
    (inclusionTopology.{u, t} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).cover_preserve hT
  rw [← Sieve.functorPushforward_comp] at h𝒳
  obtain ⟨I, W, g, hcov, hmem⟩ := AffineFullSubsite.exists_isCover_etale_of_mem B S hS
    𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳) 𝒳.val.isFiberedInGroupoids smoothObject_of_etale
    X _ h𝒳
  refine ⟨I, W, g, hcov, fun i => ?_⟩
  obtain ⟨Z, s, k, hs, hk⟩ := hmem i
  have : g i = ObjectProperty.homMk (ObjectProperty.homMk k) ≫ s :=
    (affineSmoothInclusion B S hS 𝒳).map_injective (by simpa using hk)
  rw [this]
  exact T.downward_closed hs _

/-- **A cover of the smooth objects over affine schemes generates a covering sieve**: a finite
jointly surjective family of arrows over étale morphisms lies over an étale covering family. -/
theorem coversAreCovering :
    Stacks.FlatAffineSite.CoversAreCovering.{u + 1} (affineSmoothScheme B S hS 𝒳)
      (affineEtale B S hS 𝒳) (affineSmoothTopology B S hS 𝒳) := by
  intro X I W g hg
  let G := affineSmoothInclusion B S hS 𝒳
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  have h𝒳 : Sieve.ofArrows (fun i => G.obj (W i)) (fun i => G.map (g i)) ∈
      associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) (G.obj X) := by
    rw [associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => 𝒳.val.isFiberedInGroupoids.isStronglyCartesian q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    change Sieve.ofArrows _ _ ∈ (etaleTopology B).over (B.obj hS) _
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [etalePrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ?_, fun i => hg.mem i⟩
    obtain ⟨i, y, hy⟩ := hg.surj x
    exact ⟨i, y, hy⟩
  refine (inclusionTopology.{u, t} B S hS 𝒳).superset_covering ?_
    ((smoothObject.{u, t} B S hS 𝒳).ι.cover_lift (inclusionTopology.{u, t} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) h𝒳)
  intro Z h hh
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨W i, g i, ObjectProperty.homMk k, Sieve.ofArrows_mk _ _ i,
    (smoothObject.{u, t} B S hS 𝒳).ι.map_injective hk⟩

/-- **Arrows between smooth objects over affine schemes have flat factorizations**: an arrow
`h : Y ⟶ X` factors, étale locally on `Y`, through a pair of smooth arrows out of a smooth object
over an affine scheme. This is `AlgebraicGeometry.Stack.LisseEtale.factorizationSieveOf_mem`,
refined to a finite cover by
`AlgebraicGeometry.Stack.AffineFullSubsite.exists_isCover_etale_of_mem`; the object the
factorization passes through is smooth, mapping to `Y` by a smooth arrow. -/
theorem hasFlatFactorizations :
    Stacks.FlatAffineSite.HasFlatFactorizations.{u + 1} (affineSmoothScheme B S hS 𝒳)
      (affineEtale B S hS 𝒳) := by
  intro X Y h
  let G := affineSmoothInclusion B S hS 𝒳
  let y' : FlatFppf B S hS 𝒳 :=
    ⟨G.obj X, AlgebraicStacks.isFlat_of_isSmooth B S hS _ X.obj.property⟩
  have hT := factorizationSieveOf_mem (𝒳 := 𝒳) (y' := y') Y.obj.property X.obj.property (G.map h)
  obtain ⟨I, W, r, hr, hmem⟩ := AffineFullSubsite.exists_isCover_etale_of_mem B S hS
    𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳) 𝒳.val.isFiberedInGroupoids smoothObject_of_etale
    Y _ hT
  refine ⟨I, W, r, hr, fun i => ?_⟩
  obtain ⟨w, c, a, b, haff, ha, hb, hca, hcb⟩ := hmem i
  let Z : (affineSmooth B S hS 𝒳).FullSubcategory :=
    ⟨⟨w, closedUnderSmoothMorphisms B S hS 𝒳 a ha Y.obj.property⟩, haff⟩
  have hrf : Flat ((affineSmoothScheme B S hS 𝒳).map (r i)) := by
    have : Etale ((affineSmoothScheme B S hS 𝒳).map (r i)) := hr.mem i
    infer_instance
  have flat_of_smooth : ∀ {x y : 𝒳.val.val.obj} (f : x ⟶ y)
      (_ : Smooth ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map f))),
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map f)) := fun _ _ => by
    infer_instance
  refine ⟨Z, ObjectProperty.homMk (ObjectProperty.homMk c),
    ObjectProperty.homMk (ObjectProperty.homMk a), ObjectProperty.homMk (ObjectProperty.homMk b),
    r i, ?_, ?_, hrf, G.map_injective hca, G.map_injective hcb⟩
  · exact flat_of_smooth a ha
  · exact flat_of_smooth b hb

/-- For every algebraic stack `𝒳`, the quasi-coherent modules on the lisse-étale site
`𝒳_{lisse,étale}`, ringed by `𝒪_{𝒳_{lisse,étale}}` (the restriction of the structure sheaf,
`AlgebraicGeometry.Stack.LisseEtale.ringedTopos'`), form a weak Serre subcategory of
`Mod(𝒪_{𝒳_{lisse,étale}})`. -/
@[stacks 07B4 "part (1)"]
theorem isWeakSerreClass_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos'.{u, t} B S hS 𝒳).O) :
      ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (ringedTopos'.{u, t} B S hS 𝒳).O))).IsWeakSerreClass := by
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative @Etale).toIsStableUnderComposition
  have : (affineEtale B S hS 𝒳).IsStableUnderComposition :=
    AffineFullSubsite.isStableUnderComposition B S hS _ _ _
  have : (affineEtale B S hS 𝒳).HasPullbacks :=
    AffineFullSubsite.hasPullbacks 𝒳.val.isFiberedInGroupoids smoothObject_of_etale
  have : (affineEtale B S hS 𝒳).IsStableUnderBaseChange :=
    AffineFullSubsite.isStableUnderBaseChange 𝒳.val.isFiberedInGroupoids smoothObject_of_etale
  have : ∀ X : (affineSmooth B S hS 𝒳).FullSubcategory,
      IsAffine ((affineSmoothScheme B S hS 𝒳).obj X) := fun X => X.property
  exact Stacks.FlatAffineSite.isWeakSerreClass_isQuasicoherentOnSite_of_affineSubsite
    (inclusionTopology.{u, t} B S hS 𝒳)
    (AffineFullSubsite.schemeFunctor B S hS 𝒳.val.val.p (smoothObject.{u, t} B S hS 𝒳))
    (ringedTopos'.{u, t} B S hS 𝒳).O.property (affineSmooth B S hS 𝒳)
    (Q := affineEtale B S hS 𝒳) (fun _ _ f hf => by
      have : Etale ((affineSmoothScheme B S hS 𝒳).map f) := hf
      infer_instance)
    (AffineFullSubsite.preservesPullbacksAlong 𝒳.val.isFiberedInGroupoids smoothObject_of_etale)
    (hasCoverRefinements B S hS 𝒳) (coversAreCovering B S hS 𝒳) (hasFlatFactorizations B S hS 𝒳)

end LisseEtale

end AlgebraicGeometry.Stack

end
