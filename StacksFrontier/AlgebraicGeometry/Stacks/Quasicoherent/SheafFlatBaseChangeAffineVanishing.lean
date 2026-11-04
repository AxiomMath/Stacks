module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackSiteSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineAcyclicityFromSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsOfSheafifiedComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeCechVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings

/-!
# The higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a sheaf of
`𝒪_𝒳`-modules on `𝒳_fppf` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base
change property of **Stacks 0762**, read with the pullback of sheaves. Then for every object `x`
of `𝒳` lying over an affine scheme

`H^p(x, F) = 0` for `p > 0`,

both for the cohomology of the underlying abelian sheaf and for the right derived functors of the
sections `Γ(x, -) : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒳(x))`. This is the first sentence of the proof of
**Stacks 08IY**, and the vanishing on which the proofs of **Stacks 075R**, **Stacks 0771** (2) and
**Stacks 07B8** rest; the source obtains it from Descent, **Stacks 0756**, and Cohomology of
Schemes, **Stacks 01XB**.

## The argument

Cartan's criterion (**Stacks 03F9**,
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives`) is applied
to the objects lying over affine schemes and the families of arrows lying over standard fppf
coverings (Stacks 03X8): finitely many affine members, flat and of finite presentation, jointly
surjective.

* These families are cofinal among the coverings of an object over an affine scheme: a covering
  sieve of the big fppf site is refined by a standard fppf covering (**Stacks 021P**,
  `AlgebraicGeometry.exists_standardFppf_refinement`), and a refinement downstairs is lifted along
  the fibred category by
  `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`.
* Their iterated fibre products lie over affine schemes, the iterated fibre products of affine
  schemes over an affine scheme.
* The Čech cohomology of `F` along them vanishes in positive degrees: along an arrow lying over a
  flat morphism the flat base change property identifies the sections of `F` with those of the
  quasi-coherent module below the target
  (`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`), compatibly with the restriction maps
  (`AlgebraicGeometry.Stack.LiftedSectionsCocycleOfSheafified`, proved in the library), so the Čech
  complex is the Amitsur complex of a faithfully flat ring map
  (`AlgebraicGeometry.Stack.isZero_cechCohomology_of_flatSectionsIso`, **Stacks 03FJ**).

The module-valued form follows by
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`.

## Main results

* `AlgebraicGeometry.Stack.isZero_cechCohomology_of_sheafFlatBaseChange`: the Čech vanishing.
* `AlgebraicGeometry.Stack.exists_standardFppfFamily_le_of_mem_fppf`: the cofinality.
* `AlgebraicGeometry.Stack.isZero_sheafCohomology_of_sheafFlatBaseChange`: the vanishing of the
  cohomology of the underlying abelian sheaf.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange`: the vanishing
  of the module-valued cohomology, for a category fibred in groupoids whose sheaf categories have
  enough injectives.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`:
  the same for an algebraic stack, with no hypothesis.

## References

* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 021P in the big fppf category over `S`, keeping the standard covering.** A covering
sieve of an object of the big fppf category over `S` lying over an affine scheme contains a
covering family whose image in the schemes is a standard fppf covering.

This is `AlgebraicGeometry.exists_standardFppf_refinement` localized at `S`: the standard covering
refining the image of the sieve under `CategoryTheory.Sieve.overEquiv` is read back over `S` by
equipping each of its members with the composite structure morphism. -/
theorem BigFppfOver.exists_isStandardFppfCovering_le
    {U : BigFppfOver B S hS} (hU : IsAffineOver B S hS U)
    {R : Sieve U} (hR : R ∈ B.topology.over (B.obj hS) U) :
    ∃ Q : PreZeroHypercover.{u + 1} U, BigFppfOver.IsCovering B S hS ⟨U, Q⟩ ∧
      IsStandardFppfCovering (fun i ↦ B.inclusion.obj ((BigFppfOver.forget B S hS).obj (Q.X i)))
        (fun i ↦ B.inclusion.map ((BigFppfOver.forget B S hS).map (Q.f i))) ∧
      Q.presieve₀ ≤ R.arrows := by
  have hRbase : (Sieve.overEquiv U) R ∈ B.topology ((BigFppfOver.forget B S hS).obj U) := by
    rwa [GrothendieckTopology.mem_over_iff] at hR
  have hTaff : IsAffine (B.inclusion.obj ((BigFppfOver.forget B S hS).obj U)) := hU
  obtain ⟨Q, hQcover, hQstd, hQle⟩ :=
    exists_standardFppf_refinement B (T := (BigFppfOver.forget B S hS).obj U)
      (R := Sieve.overEquiv U R) hRbase
  refine ⟨⟨Q.I₀, fun i => Over.mk (Q.f i ≫ U.hom), fun i => Over.homMk (Q.f i) rfl⟩,
    hQcover, hQstd, Presieve.ofArrows_le_iff.2 fun i ↦ ?_⟩
  exact (Sieve.overEquiv_iff R (Q.f i)).mp (hQle _ _ ⟨i⟩)

namespace Stack

section Fibred

variable {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The Čech complex of a locally quasi-coherent module with the flat base change property of
Stacks 0762, along a family of arrows lying over a standard fppf covering of an affine scheme, is
exact in positive degrees.**

This is `AlgebraicGeometry.Stack.isZero_cechCohomology_of_flatSectionsIso` at the quasi-coherent
module `𝓕` below `x` of the first step of the proof of **Stacks 076T**: along an arrow lying over
a flat morphism the comparison `c_φ` of Stacks 06WC induces an isomorphism of sheaves, so
`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified` identifies the sections, and its
compatibility with the restriction maps is
`AlgebraicGeometry.Stack.LiftedSectionsCocycleOfSheafified`, proved in the library. -/
theorem isZero_cechCohomology_of_sheafFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F)
    {x : 𝒳} [IsAffine ((toScheme B S hS p).obj x)] (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    (hstd : IsStandardCovering .fppf (fun i ↦ (toScheme B S hS p).obj (𝒰.X i))
      (fun i ↦ (toScheme B S hS p).map (𝒰.f i)))
    (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology 𝒰 F.presheaf n) := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc x
  have := d.isQuasicoherent
  have hcoc : LiftedSectionsCocycleOfSheafified B E h S hS p hp :=
    liftedSectionsCocycleOfSheafified_of_factorFourSquare B E h S hS p hp
      (liftedSectionsFactorFourSquareOfSheafified_of_compat B E h S hS p hp
        (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp))
  have hiso : ∀ (Y : Over x), Flat ((toScheme B S hS p).map Y.hom) →
      IsIso (sheafifiedRestrictComparison B E h S hS p hp F Y.hom (hlqc.2 _).choose) :=
    fun Y hY ↦ (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) Y.hom F (hlqc.2 _).choose).2 (hbc Y.hom hY)
  let e : ∀ Y : Over x, Flat ((toScheme B S hS p).map Y.hom) →
      (F.presheaf.obj (op Y.left) ≅ (quasiCoherentPresheafFunctor (p.obj x).left.1 d.val).obj
        (op ((Over.post (toScheme B S hS p)).obj Y))) := fun Y hY ↦
    liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc Y.hom d.val d.isQuasicoherent d.isSheaf
      d.iso (hiso Y hY)
  have he : ∀ {Y Y' : Over x} (hY : Flat ((toScheme B S hS p).map Y.hom))
      (hY' : Flat ((toScheme B S hS p).map Y'.hom)) (g : Y' ⟶ Y),
      F.presheaf.map g.left.op ≫ (e Y' hY').hom =
        (e Y hY).hom ≫ (quasiCoherentPresheafFunctor (p.obj x).left.1 d.val).map
          ((Over.post (toScheme B S hS p)).map g).op := by
    intro Y Y' hY hY' g
    exact hcoc F hlqc d.val d.isQuasicoherent d.isSheaf d.iso g.left Y.hom Y'.hom
      (Over.w g).symm (hiso Y hY) (hiso Y' hY')
  exact isZero_cechCohomology_of_flatSectionsIso B S hS p hp F.presheaf d.val e he 𝒰 hstd n hn

include hp in
/-- **The families lying over standard fppf coverings are cofinal at an object over an affine
scheme.** Every covering sieve of an object `x` of `𝒳_fppf` lying over an affine scheme contains a
covering family, indexed by a type in the hom universe of `𝒳`, whose image in the schemes is a
standard fppf covering (Stacks 03X8).

A standard fppf covering refining the image of the sieve downstairs
(`AlgebraicGeometry.BigFppfOver.exists_isStandardFppfCovering_le`, **Stacks 021P**) is lifted along
`p` by `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, whose
base-level input is asked of every object: the class of families fed to it asks for a standard
covering only over an affine target, and the tautological family of a sieve supplies it
elsewhere. The lifted family is finite, and is reindexed by `ULift (Fin n)`. -/
theorem exists_standardFppfFamily_le_of_mem_fppf {x : 𝒳} [IsAffine ((toScheme B S hS p).obj x)]
    {T : Sieve x} (hT : T ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    ∃ 𝒰 : PreZeroHypercover.{u} x,
      𝒰.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x ∧
      IsStandardCovering .fppf (fun i ↦ (toScheme B S hS p).obj (𝒰.X i))
        (fun i ↦ (toScheme B S hS p).map (𝒰.f i)) ∧
      𝒰.sieve₀ ≤ T := by
  classical
  obtain ⟨E₀, hE, hEle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS p
    B.topology
    (fun E ↦ IsAffineOver B S hS E.1 → BigFppfOver.IsCovering B S hS E ∧
      IsStandardFppfCovering (fun i ↦ B.inclusion.obj ((BigFppfOver.forget B S hS).obj (E.2.X i)))
        (fun i ↦ B.inclusion.map ((BigFppfOver.forget B S hS).map (E.2.f i))))
    (fun U R hR ↦ by
      by_cases hU : IsAffineOver B S hS U
      · obtain ⟨Q, hcov, hstd, hle⟩ := BigFppfOver.exists_isStandardFppfCovering_le B S hS hU hR
        exact ⟨Q, fun _ ↦ ⟨hcov, hstd⟩, hle⟩
      · refine ⟨⟨Σ V : BigFppfOver B S hS, {g : V ⟶ U // R g}, fun i => i.1, fun i => i.2.1⟩,
          fun h => absurd h hU, ?_⟩
        exact Presieve.ofArrows_le_iff.2 fun i => i.2.2)
    hp T hT
  obtain ⟨hcov, hstd⟩ := hE ‹IsAffine ((toScheme B S hS p).obj x)›
  have hfin : Finite E₀.I₀ := hstd.finite_index
  let e : E₀.I₀ ≃ ULift.{u} (Fin (Nat.card E₀.I₀)) :=
    (Finite.equivFin E₀.I₀).trans Equiv.ulift.symm
  let 𝒰 : PreZeroHypercover.{u} x :=
    ⟨ULift.{u} (Fin (Nat.card E₀.I₀)), fun i => E₀.X (e.symm i), fun i => E₀.f (e.symm i)⟩
  have hsieve : 𝒰.sieve₀ = Sieve.ofArrows E₀.X E₀.f := by
    ext W g
    show Sieve.ofArrows _ _ g ↔ _
    rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨i, a, h⟩
      exact ⟨e.symm i, a, h⟩
    · rintro ⟨i, a, h⟩
      refine ⟨e i, ?_⟩
      show ∃ a', g = a' ≫ E₀.f (e.symm (e i))
      rw [e.symm_apply_apply]
      exact ⟨a, h⟩
  have hup : Sieve.ofArrows E₀.X E₀.f ∈ BigFppfOver.associatedTopology B S hS p .fppf x := by
    rw [BigFppfOver.associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian hp q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows (fun i => p.obj (E₀.X i)) (fun i => p.map (E₀.f i)) ∈
        (B.topology.over (B.obj hS)) (p.obj x) := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      have hpre : ((E₀.map p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
          B.precoverage ((BigFppfOver.forget B S hS).obj (p.obj x)) :=
        ⟨(E₀.map p).map (BigFppfOver.forget B S hS), rfl, hcov⟩
      simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map] using
        Precoverage.generate_mem_toGrothendieck hpre
    exact hBcover
  refine ⟨𝒰, hsieve ▸ hup, ?_, ?_⟩
  · refine
      { finite_index := inferInstance
        affine_source := fun i ↦ hstd.affine_source (e.symm i)
        jointly_surjective := ?_
        standard := fun i ↦ ⟨hstd.flat (e.symm i), hstd.finite_presentation (e.symm i)⟩ }
    rw [← hstd.jointly_surjective]
    exact e.symm.surjective.iUnion_comp
      (fun j ↦ Set.range (B.inclusion.map ((BigFppfOver.forget B S hS).map (p.map (E₀.f j)))))
  · rw [hsieve, Sieve.ofArrows, Sieve.generate_le_iff]
    exact hEle

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]

/-- **The higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over an object lying
over an affine scheme**, for the cohomology of its underlying abelian sheaf: `H^n(x, F) = 0` for
`n > 0`.

Cartan's criterion (**Stacks 03F9**) along the families lying over standard fppf coverings: they
are cofinal (`AlgebraicGeometry.Stack.exists_standardFppfFamily_le_of_mem_fppf`), their iterated
fibre products lie over affine schemes, and the Čech cohomology of `F` along them vanishes in
positive degrees (`AlgebraicGeometry.Stack.isZero_cechCohomology_of_sheafFlatBaseChange`). -/
theorem isZero_sheafCohomology_of_sheafFlatBaseChange
    [HasExt.{t} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
    (F : fppfSiteModules B S hS p hp)
    (hF : locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp F)
    (x : 𝒳) (hx : IsAffineOver B S hS (p.obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{t} ((SheafOfModules.toSheaf (fppfSiteRingSheaf B S hS p hp)).obj F) n x) := by
  classical
  have : HasPullbacks 𝒳 := hasPullbacks_fibred B S hS p hp
  let J := BigFppfOver.associatedTopology B S hS p .fppf
  let Bset : Set 𝒳 := {y | IsAffine ((toScheme B S hS p).obj y)}
  let Cov : ∀ y : 𝒳, Set {𝒰 : PreZeroHypercover.{u} y // 𝒰.sieve₀ ∈ J y} := fun y 𝒰 ↦
    ∃ hy : IsAffine ((toScheme B S hS p).obj y),
      @IsStandardCovering .fppf _ hy _ (fun i ↦ (toScheme B S hS p).obj (𝒰.1.X i))
        (fun i ↦ (toScheme B S hS p).map (𝒰.1.f i))
  have hProd : ∀ {y : 𝒳} (𝒰 : PreZeroHypercover.{u} y) (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀),
      HasProduct (fun a ↦ Over.mk (𝒰.f (i a))) := fun _ m _ ↦
    Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives J
    Bset Cov (fun 𝒰 _ ↦ hProd 𝒰.1) ?_ ?_ _ ?_ x hx n hn
  · intro y 𝒰 h𝒰
    have hy := h𝒰.1
    have hstd := h𝒰.2
    refine ⟨hy, fun i ↦ hstd.affine_source i, fun m i ↦ ?_⟩
    have : MorphismProperty.IsStableUnderComposition @IsAffineHom :=
      ⟨fun _ _ hf hg ↦ by have := hf; have := hg; infer_instance⟩
    have : MorphismProperty.RespectsIso @IsAffineHom :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have haff := prop_toScheme_map_cechProduct_hom B S hS p hp @IsAffineHom 𝒰.1
      (fun j ↦ by have := hstd.affine_source j; infer_instance) m i
    exact isAffine_of_isAffineHom
      ((toScheme B S hS p).map (∏ᶜ (fun a ↦ Over.mk (𝒰.1.f (i a)))).hom)
  · intro y hy R hR
    have : IsAffine ((toScheme B S hS p).obj y) := hy
    obtain ⟨𝒰, h𝒰J, hstd, hle⟩ := exists_standardFppfFamily_le_of_mem_fppf B S hS p hp hR
    exact ⟨⟨𝒰, h𝒰J⟩, ⟨hy, hstd⟩, hle⟩
  · intro y 𝒰 h𝒰 m hm
    have : IsAffine ((toScheme B S hS p).obj y) := h𝒰.1
    exact isZero_cechCohomology_of_sheafFlatBaseChange B E h S hS p hp F.val hF.1 hF.2 𝒰.1
      h𝒰.2 m hm

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

/-- **The higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over an object lying
over an affine scheme**: the right derived functors of the sections
`Γ(x, -) : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒳(x))` vanish in positive degrees on `F`. This is the vanishing
which **Stacks 08IY** opens with.

It is `AlgebraicGeometry.Stack.isZero_sheafCohomology_of_sheafFlatBaseChange` read for
module-valued cohomology by
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`. The
instance hypotheses are those of that comparison; for an algebraic stack they all hold, see
`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`. -/
theorem isZero_rightDerived_evaluation_of_sheafFlatBaseChange
    [HasExt.{max v u} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
    [EnoughInjectives (fppfSiteModules B S hS p hp)]
    [HasExt.{max v u} (fppfSiteModules B S hS p hp)]
    (F : fppfSiteModules B S hS p hp)
    (hF : locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp F)
    (x : 𝒳) (hx : IsAffineOver B S hS (p.obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp) (op x)).rightDerived
      n).obj F) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'
    (BigFppfOver.associatedTopology B S hS p .fppf) (fppfSiteRingSheaf B S hS p hp) x j F
    (isZero_sheafCohomology_of_sheafFlatBaseChange B E h S hS p hp F hF x hx (j + 1)
      (Nat.succ_pos j))

end Fibred

section AlgebraicStack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] hasSheafify_associatedTopology_algebraicStack
  wEqualsLocallyBijective_associatedTopology_algebraicStack enoughInjectives_fppfModules

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

/-- **The higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` vanishes over an object lying
over an affine scheme**, for an algebraic stack `𝒳`: for `F` locally quasi-coherent with the
flat base change property of **Stacks 0762**, `H^n(x, F) = 0` for `n > 0` and `x` lying over an
affine scheme, as the right derived functors of the sections `Γ(x, -)`.

This is `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange` with its
instance hypotheses discharged: the fppf site of `𝒳` is essentially small in the universe of its
schemes. -/
theorem isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack
    (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F)
    (x : 𝒳.val.val.obj) (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation
      (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) (op x)).rightDerived
        n).obj F) :=
  have := enoughInjectives_fppfSiteSheaf_of_essentiallySmall B S hS 𝒳.val.val.p
  have : HasExt.{u + 1} (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      AddCommGrpCat.{u}) := HasExt.standard _
  have : HasExt.{u + 1} (fppfModules B S hS 𝒳) := HasExt.standard _
  isZero_rightDerived_evaluation_of_sheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F hF x hx n hn

end AlgebraicStack

end Stack

end AlgebraicGeometry

end
