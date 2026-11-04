module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestrictionLargeSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedBaseChangeHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineModuleVanishingLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeEtaleWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatAffineCartesianWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineZariskiRefinement

/-!
# The derived base change map of derived sections over objects of an algebraic stack

Let `𝒳` be an algebraic stack and `K` an object of `D(𝒪_𝒳)`, the derived category of sheaves of
`𝒪_𝒳`-modules on `𝒳_fppf` with sections in `Type (u + 1)` (the module universe at which `QC(𝒳)`
of Stacks 0H0H and the derived lower shriek
`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc` live).  For an object `x` of `𝒳`,
`RΓ(x, K)` is an object of `D(𝒪(x))`
(`Stacks.Cohomology.HypercohomologyEdge.derivedSections`), and a morphism `a : x ⟶ x'` gives the
derived restriction `RΓ(x', K) ⟶ RΓ(x, K)`, `𝒪(x')`-linear
(`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict`).  Its adjoint transpose under
`- ⊗^L_{𝒪(x')} 𝒪(x) ⊣ Res` (Stacks 0GMT) is the map of **Stacks 0H15**

`RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)`.

This file names that map and the property, required of `Lg_!K` by Stacks 0H15, that it is a
quasi-isomorphism for every morphism of `𝒳_{affine}`.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsBaseChange`: the map displayed above.
* `AlgebraicGeometry.Stack.FlatFppf.HasAffineDerivedSectionsBaseChange`: it is invertible for
  every morphism `x ⟶ x'` of objects lying over affine schemes.

## Implementation notes

The derived categories are the standard models, as in the statements of Stacks 07B9 (2)(c) at
this universe and of the derived base change `dBaseChange` of
`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange`, which is the one defining `QC(𝒳)`.

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- Sheaves of `𝒪_𝒳`-modules with sections in `Type (u + 1)` form a Grothendieck abelian category,
which supplies the unbounded derived functors of sections. -/
local instance isGrothendieckAbelian_ambientModulesSucc :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1} _

/-- The rings of sections of the structure sheaf of `𝒳` are commutative: they are rings of global
functions on schemes. -/
theorem ambientRingStructureSheaf_mul_comm (x : 𝒳.val.val.obj)
    (a b : (ambientRingStructureSheaf B S hS 𝒳).obj.obj (op x)) : a * b = b * a :=
  let : CommRing ((ambientRingStructureSheaf B S hS 𝒳).obj.obj (op x)) :=
    inferInstanceAs (CommRing (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj x)))))
  mul_comm a b

/-- **The map of Stacks 0H15.** For a morphism `a : x ⟶ x'` of `𝒳` and `K` in `D(𝒪_𝒳)`, the
derived base change map `RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` in `D(𝒪(x))`: the adjoint
transpose, under `- ⊗^L_{𝒪(x')} 𝒪(x) ⊣ Res` (Stacks 0GMT), of the derived restriction map
`RΓ(x', K) ⟶ RΓ(x, K)`. -/
def derivedSectionsBaseChange {x x' : 𝒳.val.val.obj} (a : x ⟶ x')
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :
    (dBaseChange.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).obj
      ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x').obj K) ⟶
      (derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).obj K :=
  ((dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
    ((derivedSectionsRestrict (ambientRingStructureSheaf B S hS 𝒳) a).app K)

/-- **The conclusion of Stacks 0H15**, as a property of an object `K` of `D(𝒪_𝒳)`: for every
morphism `x ⟶ x'` of `𝒳_{affine}` — objects of `𝒳` lying over affine schemes — the derived base
change map `RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` is a quasi-isomorphism. -/
def HasAffineDerivedSectionsBaseChange
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) : Prop :=
  ∀ ⦃x x' : 𝒳.val.val.obj⦄ (a : x ⟶ x'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) →
      IsIso (derivedSectionsBaseChange B S hS 𝒳 a K)


section FlatCase

attribute [local instance]
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- A Zariski covering family of the image of an object `W` of `𝒳` lifts to an fppf covering
family of `W` by objects lying over its members. -/
private theorem exists_lift_ofArrows_mem_fppf (W : 𝒳.val.val.obj) {ι : Type (u + 1)}
    (Y : ι → BigFppfOver B S hS) (f : ∀ i, Y i ⟶ 𝒳.val.val.p.obj W)
    (hY : Sieve.ofArrows Y f ∈
      BigFppfOver.baseOverTopology B S hS .zariski (𝒳.val.val.p.obj W)) :
    ∃ (y : ι → 𝒳.val.val.obj) (φ : ∀ i, y i ⟶ W), (∀ i, 𝒳.val.val.p.obj (y i) = Y i) ∧
      Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf W := by
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  choose y φ hφ using fun j => hp.exists_lift (f j) W rfl
  have hdom : ∀ j, p.obj (y j) = Y j := fun j =>
    have := hφ j
    IsHomLift.domain_eq p (f j) (φ j)
  have hfmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (f j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    simpa using IsHomLift.fac p (f j) (φ j)
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨y, φ, hdom, BigFppfOver.associatedTopology_le_fppf B S hS p .zariski _ ?_⟩
  refine (Functor.isInheritedTopology_inheritedTopology p
    (BigFppfOver.baseOverTopology B S hS .zariski) y φ
    fun j => hp.isStronglyCartesian (φ j)).2 ?_
  refine (BigFppfOver.baseOverTopology B S hS .zariski).superset_covering (fun Z g hg => ?_) hY
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed (hfmem j) a

/-- **Enough affine objects, with small index types.** Every object of the fppf site of an
algebraic stack has a covering family, indexed by a type in the hom universe `u` of the site, by
objects lying over affine schemes: an affine open cover of the scheme below, lifted. -/
theorem hasEnoughObjects_isAffine :
    (associatedTopology B S hS 𝒳.val.val.p B.topology).HasEnoughObjects
      (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) := by
  classical
  intro W
  let p := 𝒳.val.val.p
  let O₀ := (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  let O : (B.inclusion.obj (p.obj W).left).OpenCover.{u + 1} :=
    { I₀ := ULift.{u + 1} O₀.I₀
      X := fun i => O₀.X i.down
      f := fun i => O₀.f i.down
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun i ↦ O₀.map_prop _⟩
        obtain ⟨y, hy⟩ := O₀.covers x
        exact ⟨⟨O₀.idx x⟩, y, hy⟩ }
  let V : PreZeroHypercover.{u + 1} (p.obj W).left :=
    { I₀ := O.I₀
      X := fun i => ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) (p.obj W).left.2⟩
      f := fun i => ObjectProperty.homMk (O.f i) }
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := fun j => by
    show IsAffine (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X j.down))
    exact isAffine_Spec _
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .zariski (p.obj W) := by
    have hZ : IsZariskiCovering (⟨(p.obj W).left, V⟩ : Covering B.Schemes) := by
      show (V.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage _
      simpa [V, PreZeroHypercover.map] using O.mem₀
    obtain ⟨⟨T', E'⟩, hE', hbase, hfamily⟩ :=
      B.zariskiCovering_has_representative ⟨(p.obj W).left, V⟩ hZ
    change (p.obj W).left = T' at hbase
    cases hbase
    have hgen : Sieve.generate V.presieve₀ ∈ B.zariskiTopology (p.obj W).left := by
      rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
        (show PreZeroHypercover.CombinatoriallyEquivalent V E' by simpa using hfamily)]
      exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hE'⟩
    let Vover : PreZeroHypercover.{u + 1} (p.obj W) := ⟨V.I₀, Vobj, vmap⟩
    show Sieve.generate Vover.presieve₀ ∈ B.zariskiTopology.over (B.obj hS) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward]
    simpa [Vover, Vobj, vmap, PreZeroHypercover.presieve₀, PreZeroHypercover.map] using hgen
  obtain ⟨y, φ, hdom, hcov⟩ := exists_lift_ofArrows_mem_fppf B S hS 𝒳 W Vobj vmap hBcover
  refine ⟨O₀.I₀, fun i => y ⟨i⟩, fun i => φ ⟨i⟩, ?_, fun i => ?_⟩
  · refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering
      (fun Z g hg => ?_) hcov
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j.down, a, rfl⟩
  · show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y ⟨i⟩)))
    rw [hdom ⟨i⟩]
    exact hVaff ⟨i⟩

/-- **Hypercohomology over an affine object of `D_{LQCoh^fbc}`** (Stacks 0BKZ with the affine
vanishing of `LQCoh^fbc`, at module universe `u + 1`): if the cohomology sheaves of `K` lie in
`LQCoh^fbc(𝒪_𝒳)` and `y` lies over an affine scheme, the edge morphism
`H^q(RΓ(y, K)) ⟶ Γ(y, H^q K)` is an isomorphism for every `q`. -/
theorem isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (y : 𝒳.val.val.obj) (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)))
    (q : ℤ) :
    IsIso ((hypercohomologyEdge.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) y
      q).app K) :=
  isIso_hypercohomologyEdge_app_of_acyclic_cover _ y K _ (hasEnoughObjects_isAffine B S hS 𝒳)
    (fun V hV n hn m => isZero_rightDerived_evaluation_of_sheafFlatBaseChange_succ B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ (hK m) V hV n hn) hy q

/-- **Homology of the flat base change map.** If the cohomology sheaves of `K` lie in
`LQCoh^fbc(𝒪_𝒳)` and `a : x ⟶ x'` is a morphism of `𝒳_{affine}` lying over a flat morphism of
schemes, the adjoint transpose of the map induced by derived restriction on `q`-th homology is an
isomorphism. -/
private theorem isIso_homEquiv_symm_homology_derivedSectionsRestrict
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    {x x' : 𝒳.val.val.obj} (a : x ⟶ x')
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)))
    (hx' : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')))
    (ha : Flat (B.inclusion.map (𝒳.val.val.p.map a).left))
    [PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom)]
    [PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom)] (q : ℤ) :
    IsIso (((moduleBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
      ((DerivedCategory.homologyFunctor _ q).map
          ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1}
            (ambientRingStructureSheaf B S hS 𝒳) a).app K) ≫
        (Stacks.Homology.derivedHomologyIso (ModuleCat.restrictScalars.{u + 1}
          ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom) q).hom.app
          ((derivedSections.{_, _, _, u + 1, u + 1}
            (ambientRingStructureSheaf B S hS 𝒳) x).obj K))) := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  let F := (DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} O) q).obj K
  have := isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange B S hS 𝒳 E h K hK x hx q
  have := isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange B S hS 𝒳 E h K hK x' hx' q
  have e : (DerivedCategory.homologyFunctor _ q).map
      ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} O a).app K) ≫
      (Stacks.Homology.derivedHomologyIso
        (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) q).hom.app
        ((derivedSections.{_, _, _, u + 1, u + 1} O x).obj K) =
      (hypercohomologyEdge O x' q).app K ≫ (sectionsRestrict O a).app F ≫
        (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).map
          (inv ((hypercohomologyEdge O x q).app K)) := by
    show (derivedSectionsRestrictHomology O a q).app K = _
    rw [← reassoc_of% (derivedSectionsRestrictHomology_app_comp_hypercohomologyEdge.{_, _, _,
      u + 1, u + 1} O a q K), ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hc₀ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj) F.val a.op) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison.{u,
        u + 1, u, 0} B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val (hK q).1 a
        ((hK q).2 a ha) hx hx')
  have hc : IsIso (((moduleBaseChangeAdj.{u, u + 1} (O.obj.map a.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
        ((sectionsRestrict O a).app F)) := hc₀
  have hs : IsIso (((moduleBaseChangeAdj.{u, u + 1} (O.obj.map a.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).homEquiv _ _).symm
        ((hypercohomologyEdge O x' q).app K ≫ (sectionsRestrict O a).app F ≫
          (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom).map
            (inv ((hypercohomologyEdge O x q).app K)))) := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' hc inferInstance)
  rwa [e]

/-- **The flat case of Stacks 0H15.** If the cohomology sheaves of `K` lie in `LQCoh^fbc(𝒪_𝒳)`
(at module universe `u + 1`) and `a : x ⟶ x'` is a morphism of `𝒳_{affine}` lying over a flat
morphism of schemes, the derived base change map
`RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` is a quasi-isomorphism. -/
theorem isIso_derivedSectionsBaseChange_of_flat
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    {x x' : 𝒳.val.val.obj} (a : x ⟶ x')
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)))
    (hx' : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')))
    (ha : Flat (B.inclusion.map (𝒳.val.val.p.map a).left)) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a K) := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits _
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (O.obj.map a.op).hom) :=
    Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits _
  apply isIso_homEquiv_symm_of_isIso_homology
  · exact fun q => isIso_baseChangeHomologyComparison_of_flat _ _ _
      (flat_structureSheaf_map_of_flat B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        B.topology le_rfl a ha hx hx') _ q
  · exact isIso_homEquiv_symm_homology_derivedSectionsRestrict B S hS 𝒳 E h K hK a hx hx' ha

end FlatCase

end AlgebraicGeometry.Stack.FlatFppf

end
