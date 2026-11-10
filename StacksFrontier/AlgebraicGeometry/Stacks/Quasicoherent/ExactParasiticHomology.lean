module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleAffineCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentToParasiticZero
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule

/-!
# Exactness in `QCoh(𝒪_𝒳)` is exactness up to parasitic modules (Stacks 0776)

Let `𝒳` be an algebraic stack and let `α : 𝓕 ⟶ 𝓖`, `β : 𝓖 ⟶ 𝓗` be maps of quasi-coherent
`𝒪_𝒳`-modules with `β ∘ α = 0`. **Stacks 0776** says that the following are equivalent:

1. the complex `𝓕 ⟶ 𝓖 ⟶ 𝓗` is exact at `𝓖` in the abelian category `QCoh(𝒪_𝒳)`;
2. `Ker(β)/Im(α)`, computed in `Mod(𝒳_étale, 𝒪_𝒳)`, is parasitic;
3. `Ker(β)/Im(α)`, computed in `Mod(𝒳_fppf, 𝒪_𝒳)`, is parasitic.

The source's proof runs through `LQCoh^fbc(𝒪_𝒳)` (**Stacks 0771**) and the exactness of the
restriction to a flat chart (**Stacks 076X**, **Stacks 0GQD**). The proof here reads all three
conditions on the sections over flat objects, where the kernel of `β` in `QCoh(𝒪_𝒳)` has the
sections of the kernel of `β` on sections
(`AlgebraicGeometry.Stack.AlgebraicStacks.injective_and_range_eq_ker_of_isLimit_kernelFork`, from
**Stacks 0779** part (2)):

* (1) ⇒ (2), (3). If the complex is exact in `QCoh(𝒪_𝒳)`, the induced map `𝓕 ⟶ Ker_{QCoh}(β)`
  is an epimorphism of quasi-coherent modules, hence surjective on the sections over every affine
  object (`AlgebraicGeometry.Stack.AlgebraicStacks.surjective_app_of_epi_of_isAffineOver`, the
  faithfully flat descent half of **Stacks 03DW**). So `𝓕(x) ⟶ 𝓖(x) ⟶ 𝓗(x)` is exact at every
  flat object `x` lying over an affine scheme. Every flat object is covered, in the étale and so
  in the fppf topology, by such objects, and a section of the homology at a flat object is
  locally the class of a cycle; so it vanishes locally, hence vanishes.
* (2) or (3) ⇒ (1). The cokernel `𝓒` of `𝓕 ⟶ Ker_{QCoh}(β)` in `QCoh(𝒪_𝒳)` is the cokernel in
  `Mod(𝒪_𝒳)`. A section of `𝓒` at a flat object is locally the image of a section of
  `Ker_{QCoh}(β)`, that is of a cycle; the class of that cycle in the homology vanishes, so the
  cycle is locally a boundary, and the section of `𝓒` vanishes locally. So `𝓒` is quasi-coherent
  and parasitic, hence zero
  (`AlgebraicGeometry.Stack.eq_zero_of_isQuasicoherentOnSite_of_isParasitic`), and
  `𝓕 ⟶ Ker_{QCoh}(β)` is an epimorphism, which is exactness.

No comparison of the étale and the fppf homology is needed: each is compared with exactness in
`QCoh(𝒪_𝒳)` directly.

## Main results

* `Stacks.SheafOfModules.ExactSections.exists_covering_of_exact`: in an abelian category of sheaves
  of modules, a cycle of an exact short complex is locally a boundary.
* `AlgebraicGeometry.FibredSite.exists_affine_flat_etale_ofArrows`: every object is covered, for
  the étale topology, by objects lying over affine schemes along flat morphisms.
* `AlgebraicGeometry.Stack.AlgebraicStacks.surjective_app_of_epi_of_isAffineOver`: an epimorphism
  of quasi-coherent modules is surjective on sections over affine objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks.tfae_exact_isParasitic_homology`: **Stacks 0776**.

## References

* [Stacks Project, Tag 0776](https://stacks.math.columbia.edu/tag/0776)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w v' u'

namespace Stacks.SheafOfModules.ExactSections

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The sections of the cycles of a short complex of sheaves of modules.** At every object,
the sections of `S.cycles` map injectively onto the kernel of `S.g` on sections: the cycles are
a kernel, and kernels of sheaves of modules are computed on sections. -/
theorem iCycles_app_injective_and_range (T : ShortComplex (SheafOfModules.{u} R)) (U : Cᵒᵖ) :
    Function.Injective (T.iCycles.val.app U).hom ∧
      LinearMap.range (T.iCycles.val.app U).hom = LinearMap.ker (T.g.val.app U).hom := by
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U
  have hl : IsLimit ((KernelFork.ofι T.iCycles T.iCycles_g).map G) :=
    KernelFork.mapIsLimit _ T.cyclesIsKernel G
  have hE : (ShortComplex.mk _ _
      ((KernelFork.ofι T.iCycles T.iCycles_g).map_condition G)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hl
  exact ⟨(ModuleCat.mono_iff_injective _).1 (mono_of_isLimit_fork hl), hE.moduleCat_range_eq_ker⟩

/-- The composite `T.X₁ ⟶ T.cycles ⟶ T.X₂` on sections is `T.f`. -/
private theorem iCycles_app_toCycles_app (T : ShortComplex (SheafOfModules.{u} R)) (U : Cᵒᵖ)
    (t : T.X₁.val.obj U) :
    T.iCycles.val.app U (T.toCycles.val.app U t) = T.f.val.app U t := by
  rw [← T.toCycles_i]
  rfl

/-- **An epimorphism of sheaves of modules lifts sections locally.** -/
theorem exists_covering_restrict_eq_of_epi {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Epi f]
    {U : C} (s : N.val.obj (op U)) :
    ∃ T ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
      ∃ t : M.val.obj (op V), f.val.app (op V) t = N.val.map g.op s :=
  ⟨_, (ImageSubsheaf.isLocallySurjective_of_epi f).imageSieve_mem s, fun _ _ hg => hg⟩

/-- **A cycle of an exact short complex of sheaves of modules is locally a boundary.** -/
theorem exists_covering_of_exact (T : ShortComplex (SheafOfModules.{u} R)) (hT : T.Exact)
    {U : C} (s : T.X₂.val.obj (op U)) (hs : T.g.val.app (op U) s = 0) :
    ∃ W ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), W g →
      ∃ t : T.X₁.val.obj (op V), T.f.val.app (op V) t = T.X₂.val.map g.op s := by
  have : Epi T.toCycles := T.exact_iff_epi_toCycles.1 hT
  obtain ⟨d, hd⟩ : s ∈ LinearMap.range (T.iCycles.val.app (op U)).hom := by
    rwa [(iCycles_app_injective_and_range T (op U)).2]
  obtain ⟨W, hW, hWs⟩ := exists_covering_restrict_eq_of_epi T.toCycles d
  refine ⟨W, hW, fun V g hg => ?_⟩
  obtain ⟨t, ht⟩ := hWs g hg
  refine ⟨t, ?_⟩
  rw [← T.toCycles_i, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, ht, PresheafOfModules.naturality_apply]
  exact congrArg _ hd

end Stacks.SheafOfModules.ExactSections

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type*} [Category* 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Every object of the associated étale site is covered by objects lying over affine schemes
along flat morphisms.** The family is the cartesian lift of an affine open covering of the scheme
below the object, which is a chosen étale covering family of the big site and consists of open
immersions up to isomorphism. -/
theorem exists_affine_flat_etale_ofArrows (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))) ∧
        (∀ j, Flat (B.inclusion.map (p.map (φ j)).left)) ∧
          Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .etale W := by
  classical
  let U := (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  obtain ⟨V, hV, ⟨α, hα⟩, β, hβ⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj W).left U
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine (U.X (β j)) := by
      change IsAffine (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    have hIso : IsIso e.hom := e.isIso_hom
    exact @IsAffine.of_isIso _ _ e.hom hIso inferInstance
  have hVflat : ∀ j, Flat (B.inclusion.map (V.f j)) := by
    intro j
    obtain ⟨e, he⟩ := hβ j
    change Flat ((V.map B.inclusion).f j)
    rw [← he]
    infer_instance
  have hVet : IsEtaleCovering ⟨(p.obj W).left, V⟩ := by
    change (V.map B.inclusion).presieve₀ ∈ Scheme.precoverage @Etale _
    refine (Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).2 ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, z, rfl⟩ := U.exists_eq x
      obtain ⟨e, he⟩ := hα i
      refine ⟨α i, e.hom.base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he]
    · obtain ⟨e, he⟩ := hβ j
      rw [← he]
      infer_instance
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .etale (p.obj W) := by
    change Sieve.ofArrows Vobj vmap ∈ (B.etaleTopology.over (B.obj hS)) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows V.X V.f ∈ B.etaleTopology (p.obj W).left
    have hpre : V.presieve₀ ∈ B.etalePrecoverage (p.obj W).left := ⟨V, rfl, hV, hVet⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j
    exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hfac : ∀ j, p.map (φ j) = eqToHom (hdom j) ≫ vmap j := by
    intro j
    have := hφ j
    simpa using IsHomLift.fac' p (vmap j) (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    simp [hfac j]
  have : p.IsFibered := hp.isFibered
  have heq : ∀ {V₁ V₂ : BigFppfOver B S hS} (h : V₁ = V₂) (m : V₂ ⟶ p.obj W),
      Flat (B.inclusion.map m.left) → Flat (B.inclusion.map (eqToHom h ≫ m).left) := by
    rintro _ _ rfl m hm
    simpa using hm
  refine ⟨V.I₀, y, φ, fun j => ?_, fun j => ?_, ?_⟩
  · rw [hdom j]
    exact hVaff j
  · rw [hfac j]
    exact heq (hdom j) (vmap j) (hVflat j)
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .etale) y φ fun j => hp.isStronglyCartesian (φ j)).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .etale).superset_covering ?_ hBcover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, a, rfl⟩ := hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **A sieve on a flat object containing every arrow out of a flat object lying over an affine
scheme is a covering sieve** of the étale site of `𝒳`, and so of every finer site. -/
theorem mem_associatedTopology_of_forall_flatObject_isAffine {x : 𝒳.val.val.obj}
    (hx : flatObject B S hS 𝒳.val x) (T : Sieve x)
    (hT : ∀ ⦃y : 𝒳.val.val.obj⦄ (f : y ⟶ x), flatObject B S hS 𝒳.val y →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) → T f) :
    T ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale x := by
  obtain ⟨I, y, φ, haff, hflat, hcov⟩ := FibredSite.exists_affine_flat_etale_ofArrows B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rintro Z g ⟨Z', a, b, ⟨j⟩, rfl⟩
  exact T.downward_closed (hT (φ j) (flatObject_of_flat B S hS 𝒳 (φ j) (hflat j) hx) (haff j)) a

/-- The sieve of the arrows along which a section of a sheaf of modules restricts to zero. -/
private def vanishingSieve {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R} {U : C}
    (s : M.val.obj (op U)) : Sieve U where
  arrows _ g := M.val.map g.op s = 0
  downward_closed := by
    intro Y Y' g hg e
    rw [op_comp, PresheafOfModules.map_comp_apply]
    change M.val.map e.op (M.val.map g.op s) = 0
    rw [hg]
    exact LinearMap.map_zero _

/-- A section vanishes if it vanishes locally on each member of a covering family. -/
private theorem eq_zero_of_forall_pullback_vanishingSieve_mem {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : SheafOfModules.{u} R} {U : C}
    (s : M.val.obj (op U)) (E : PreZeroHypercover.{w} U) (hE : Sieve.generate E.presieve₀ ∈ J U)
    (h : ∀ i, (vanishingSieve s).pullback (E.f i) ∈ J (E.X i)) : s = 0 := by
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero s (J.transitive hE (vanishingSieve s) ?_)
    fun _ g hg => hg
  rintro Y g ⟨Y', a, b, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable a (h i)

/-- **An epimorphism of quasi-coherent modules is surjective on the sections over an affine
object.** A section of the target is, on a covering sieve, a value of the epimorphism; the sieve
contains a finite family of affine objects whose rings of functions are jointly faithfully flat
over the ring of the base; over affine objects the sections of a quasi-coherent module are a base
change of each other (**Descent, Proposition 03DX**), and membership in an image descends along a
faithfully flat base change. This is the descent half of **Stacks 03DW**. -/
theorem surjective_app_of_epi_of_isAffineOver
    {P N : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)}
    (hP : P.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (b : P ⟶ N) [Epi b]
    {x : 𝒳.val.val.obj} (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) :
    Function.Surjective (b.val.app (op x)) := by
  classical
  intro n
  let p := 𝒳.val.val.p
  let hp := 𝒳.val.isFiberedInGroupoids
  obtain ⟨R, hR, hRn⟩ := Stacks.SheafOfModules.ExactSections.exists_covering_restrict_eq_of_epi b n
  have hS' : (Sieve.overEquiv (Over.mk (𝟙 x))).symm R ∈
      ((BigFppfOver.associatedTopology B S hS p .fppf).over x) (Over.mk (𝟙 x)) := by
    rw [GrothendieckTopology.mem_over_iff]
    simpa using hR
  obtain ⟨k, Y, a, haff, hmem, -, hfppf⟩ :=
    FibredSite.exists_finite_affine_fppf_ofArrows_le_over B S hS p hp (𝟙 x) hx _ hS'
  let A := FibredSite.objRing B S hS p x
  let Bi : Fin k → Type u := fun i => FibredSite.objRing B S hS p (Y i).left
  let (i : Fin k) : Algebra A (Bi i) := FibredSite.objAlgebra B S hS p (a i).left
  let (i : Fin k) : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) :=
    FibredSite.objAlgebra B S hS p (a i).left
  have : Module.FaithfullyFlat A (∀ i, Bi i) :=
    FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS p Y a hx haff
      hfppf (fun _ => rfl)
  let := FibredSite.objModule B S hS p hp P x
  let := FibredSite.objModule B S hS p hp N x
  let (i : Fin k) := FibredSite.objModule B S hS p hp P (Y i).left
  let (i : Fin k) := FibredSite.objModule B S hS p hp N (Y i).left
  let (i : Fin k) : Module A (P.val.obj (op (Y i).left)) :=
    Module.compHom _ (algebraMap A (Bi i))
  let (i : Fin k) : Module A (N.val.obj (op (Y i).left)) :=
    Module.compHom _ (algebraMap A (Bi i))
  have (i : Fin k) : IsScalarTower A (Bi i) (P.val.obj (op (Y i).left)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have (i : Fin k) : IsScalarTower A (Bi i) (N.val.obj (op (Y i).left)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let bT : P.val.obj (op x) →ₗ[A] N.val.obj (op x) :=
    { toFun := b.val.app (op x)
      map_add' := map_add _
      map_smul' := fun c m => (b.val.app (op x)).hom.map_smul c m }
  let bW (i : Fin k) : P.val.obj (op (Y i).left) →ₗ[Bi i] N.val.obj (op (Y i).left) :=
    { toFun := b.val.app (op (Y i).left)
      map_add' := map_add _
      map_smul' := fun c m => (b.val.app (op (Y i).left)).hom.map_smul c m }
  obtain ⟨q, hq⟩ := Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange A Bi bT bW
    (fun i => FibredSite.restrictionLinear P (a i).left)
    (fun i => FibredSite.restrictionLinear N (a i).left)
    (fun i q => (PresheafOfModules.naturality_apply b.val (a i).left.op q).symm)
    (fun i => (FibredSite.bijective_liftBaseChange_of_eq_restriction P hP (a i).left hx (haff i)
      _ fun _ => rfl).2)
    (fun i => (FibredSite.bijective_liftBaseChange_of_eq_restriction N hN (a i).left hx (haff i)
      _ fun _ => rfl).1)
    (n := n) fun i => hRn (a i).left ((Sieve.overEquiv_symm_iff _ _).1 (hmem i))
  exact ⟨q, hq⟩

/-- The restriction of quasi-coherent modules to the sheaves of modules of one of the associated
sites changes no presheaf of modules and no map between them, so it is additive. -/
instance additive_toSiteModules (τ : SiteKind) :
    (FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ).Additive where
  map_add := rfl

/-- The short complex of sheaves of modules on the site of `τ` underlying a short complex of
quasi-coherent modules. -/
abbrev siteShortComplex (τ : SiteKind) {F G H : quasicoherentModules B S hS 𝒳} (α : F ⟶ G)
    (β : G ⟶ H) (w : α ≫ β = 0) :
    ShortComplex (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ)) :=
  (ShortComplex.mk α β w).map
    (FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)

variable {B S hS 𝒳}

/-- **Exactness in `QCoh(𝒪_𝒳)` gives exactness on sections over flat affine objects.** -/
theorem exists_eq_of_exact_of_flatObject {F G H : quasicoherentModules B S hS 𝒳} {α : F ⟶ G}
    {β : G ⟶ H} {w : α ≫ β = 0} (hex : (ShortComplex.mk α β w).Exact) {x : 𝒳.val.val.obj}
    (hx : flatObject B S hS 𝒳.val x)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)))
    (g : G.obj.val.obj (op x)) (hg : β.hom.val.app (op x) g = 0) :
    ∃ f : F.obj.val.obj (op x), α.hom.val.app (op x) f = g := by
  have : Epi (kernel.lift β α w) := (ShortComplex.mk α β w).exact_iff_epi_kernel_lift.1 hex
  have : (quasicoherentInclusion B S hS 𝒳).IsLeftAdjoint :=
    (coheratorAdjunction B S hS 𝒳).isLeftAdjoint
  obtain ⟨hinj, hrange⟩ := injective_and_range_eq_ker_of_isLimit_kernelFork B S hS 𝒳 β
    (kernelIsKernel β) x hx
  obtain ⟨κ, hκ⟩ : g ∈ LinearMap.range ((kernel.ι β).hom.val.app (op x)).hom := by
    change g ∈ LinearMap.range ((KernelFork.ofι (kernel.ι β) (kernel.condition β)).ι.hom.val.app
      (op x)).hom
    rwa [hrange]
  obtain ⟨f, hf⟩ := surjective_app_of_epi_of_isAffineOver B S hS 𝒳 F.property (kernel β).property
    ((quasicoherentInclusion B S hS 𝒳).map (kernel.lift β α w)) haff κ
  refine ⟨f, ?_⟩
  have h1 : α.hom.val.app (op x) f =
      (kernel.ι β).hom.val.app (op x) ((kernel.lift β α w).hom.val.app (op x) f) :=
    (congrArg (fun φ => (φ.hom.val.app (op x)) f) (kernel.lift_ι β α w)).symm
  rw [h1, ← hκ]
  exact congrArg _ hf

open Stacks.SheafOfModules.ExactSections in
/-- **Exactness in `QCoh(𝒪_𝒳)` makes the homology in `Mod(𝒳_τ, 𝒪_𝒳)` parasitic**, for a topology
`τ` at least as fine as the étale one. At a flat object a section of the homology is, on a
covering by flat objects, the class of a cycle; on a flat object over an affine scheme that cycle
is a boundary, by `AlgebraicGeometry.Stack.AlgebraicStacks.exists_eq_of_exact_of_flatObject`; and
such objects cover every flat object. -/
theorem isParasitic_homology_of_exact (τ : SiteKind)
    (hτ : BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale ≤
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    {F G H : quasicoherentModules B S hS 𝒳} {α : F ⟶ G} {β : G ⟶ H} {w : α ≫ β = 0}
    (hex : (ShortComplex.mk α β w).Exact) :
    IsParasitic B S hS 𝒳 τ (siteShortComplex B S hS 𝒳 τ α β w).homology.val := by
  intro x hx
  let T := siteShortComplex B S hS 𝒳 τ α β w
  let J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
  suffices key : ∀ h : T.homology.val.obj (op x), h = 0 from
    ⟨fun h₁ h₂ => (key h₁).trans (key h₂).symm⟩
  intro h
  obtain ⟨R, hR, hRh⟩ := exists_covering_restrict_eq_of_epi T.homologyπ h
  obtain ⟨E, hEflat, hEcov, hEle⟩ :=
    exists_flatObject_covering_le_of_mem_associatedTopology B S hS 𝒳 τ hx R hR
  refine eq_zero_of_forall_pullback_vanishingSieve_mem h E hEcov fun i => hτ _
    (mem_associatedTopology_of_forall_flatObject_isAffine B S hS 𝒳 (hEflat i) _
      fun v e hv hva => ?_)
  obtain ⟨c, hc⟩ := hRh (E.f i) (hEle _ _ (E.presieve₀_f i))
  let c' := T.cycles.val.map e.op c
  have hk : T.iCycles.val.app (op v) c' ∈ LinearMap.ker (T.g.val.app (op v)).hom := by
    rw [← (iCycles_app_injective_and_range T (op v)).2]
    exact ⟨c', rfl⟩
  obtain ⟨f, hf⟩ := exists_eq_of_exact_of_flatObject hex hv hva _ hk
  have hc' : c' = T.toCycles.val.app (op v) f :=
    (iCycles_app_injective_and_range T (op v)).1
      (hf.symm.trans (iCycles_app_toCycles_app T (op v) f).symm)
  change T.homology.val.map (e ≫ E.f i).op h = 0
  rw [op_comp, PresheafOfModules.map_comp_apply]
  change T.homology.val.map e.op (T.homology.val.map (E.f i).op h) = 0
  rw [← hc, ← PresheafOfModules.naturality_apply]
  change T.homologyπ.val.app (op v) c' = 0
  rw [hc']
  change (T.toCycles ≫ T.homologyπ).val.app (op v) f = 0
  rw [T.toCycles_comp_homologyπ]
  rfl

open Stacks.SheafOfModules.ExactSections in
/-- **The cokernel of the map to a kernel on flat objects is parasitic when the homology is.**
Let `ι : 𝓚 ⟶ 𝓖` be a map of quasi-coherent modules which on the sections over every flat object is
an injection onto the kernel of `β`, let `α' : 𝓕 ⟶ 𝓚` lift `α`, and let `π : 𝓚 ⟶ 𝓒` be killed by
`α'` and be an epimorphism of modules. If the homology of `𝓕 ⟶ 𝓖 ⟶ 𝓗` in `Mod(𝒳_τ, 𝒪_𝒳)`, for a
topology `τ` coarser than the fppf one, is parasitic, then so is `𝓒`: a section of `𝓒` at a flat
object comes locally from a section of `𝓚`, that is from a cycle, which is locally a boundary. -/
theorem isParasitic_of_isParasitic_homology (τ : SiteKind)
    {F G H Kq Cq : quasicoherentModules B S hS 𝒳} {α : F ⟶ G} {β : G ⟶ H} {w : α ≫ β = 0}
    (ι : Kq ⟶ G) (α' : F ⟶ Kq) (hα' : α' ≫ ι = α)
    (hK : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      Function.Injective (ι.hom.val.app (op x)).hom ∧
        LinearMap.range (ι.hom.val.app (op x)).hom = LinearMap.ker (β.hom.val.app (op x)).hom)
    (π : Kq ⟶ Cq) (hπ : α' ≫ π = 0) [Epi ((quasicoherentInclusion B S hS 𝒳).map π)]
    (hpar : IsParasitic B S hS 𝒳 τ (siteShortComplex B S hS 𝒳 τ α β w).homology.val) :
    IsParasitic B S hS 𝒳 .fppf Cq.obj.val := by
  let T := siteShortComplex B S hS 𝒳 τ α β w
  let Jf := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
  let Jτ := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
  intro x hx
  suffices key : ∀ c : Cq.obj.val.obj (op x), c = 0 from
    ⟨fun c₁ c₂ => (key c₁).trans (key c₂).symm⟩
  intro c
  obtain ⟨R, hR, hRc⟩ := exists_covering_restrict_eq_of_epi
    ((quasicoherentInclusion B S hS 𝒳).map π) c
  obtain ⟨E, hEflat, hEcov, hEle⟩ :=
    exists_flatObject_covering_le_of_mem_associatedTopology B S hS 𝒳 .fppf hx R hR
  refine eq_zero_of_forall_pullback_vanishingSieve_mem c E hEcov fun j => ?_
  obtain ⟨κ, hκ⟩ := hRc (E.f j) (hEle _ _ (E.presieve₀_f j))
  obtain ⟨c', hc'⟩ : ι.hom.val.app (op (E.X j)) κ ∈
      LinearMap.range (T.iCycles.val.app (op (E.X j))).hom := by
    rw [(iCycles_app_injective_and_range T (op (E.X j))).2]
    change _ ∈ LinearMap.ker (β.hom.val.app (op (E.X j))).hom
    rw [← (hK _ (hEflat j)).2]
    exact ⟨κ, rfl⟩
  have hπ' : (ShortComplex.mk T.toCycles T.homologyπ T.toCycles_comp_homologyπ).g.val.app
      (op (E.X j)) c' = 0 := (hpar _ (hEflat j)).elim _ _
  obtain ⟨W₂, hW₂, hW₂s⟩ := exists_covering_of_exact
    (ShortComplex.mk T.toCycles T.homologyπ T.toCycles_comp_homologyπ)
    (ShortComplex.exact_of_g_is_cokernel _ T.homologyIsCokernel) c' hπ'
  obtain ⟨E₂, hE₂flat, hE₂cov, hE₂le⟩ :=
    exists_flatObject_covering_le_of_mem_associatedTopology B S hS 𝒳 τ (hEflat j) W₂ hW₂
  refine BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p τ _
    (Jτ.superset_covering ?_ hE₂cov)
  rintro V e ⟨V', a₂, b₂, ⟨l⟩, rfl⟩
  refine ((vanishingSieve c).pullback (E.f j)).downward_closed ?_ a₂
  obtain ⟨t, ht⟩ := hW₂s (E₂.f l) (hE₂le _ _ (E₂.presieve₀_f l))
  let g₂ := (E₂.f l).op
  have e1 : ι.hom.val.app (op (E₂.X l)) (Kq.obj.val.map g₂ κ) =
      G.obj.val.map g₂ (ι.hom.val.app (op (E.X j)) κ) :=
    PresheafOfModules.naturality_apply ι.hom.val g₂ κ
  have e3 : G.obj.val.map g₂ (T.iCycles.val.app (op (E.X j)) c') =
      T.iCycles.val.app (op (E₂.X l)) (T.cycles.val.map g₂ c') :=
    (PresheafOfModules.naturality_apply T.iCycles.val g₂ c').symm
  have e6 : ι.hom.val.app (op (E₂.X l)) (α'.hom.val.app (op (E₂.X l)) t) =
      α.hom.val.app (op (E₂.X l)) t :=
    congrArg (fun φ => (φ.hom.val.app (op (E₂.X l))) t) hα'
  have hres : Kq.obj.val.map g₂ κ = α'.hom.val.app (op (E₂.X l)) t := by
    apply (hK _ (hE₂flat l)).1
    refine e1.trans ((congrArg (G.obj.val.map g₂) hc'.symm).trans (e3.trans
      ((congrArg (T.iCycles.val.app (op (E₂.X l))) ht.symm).trans
        ((iCycles_app_toCycles_app T _ t).trans e6.symm))))
  have f1 : Cq.obj.val.map (E₂.f l ≫ E.f j).op c =
      Cq.obj.val.map g₂ (Cq.obj.val.map (E.f j).op c) := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
  have f2 : Cq.obj.val.map g₂ (π.hom.val.app (op (E.X j)) κ) =
      π.hom.val.app (op (E₂.X l)) (Kq.obj.val.map g₂ κ) :=
    (PresheafOfModules.naturality_apply π.hom.val g₂ κ).symm
  have f3 : π.hom.val.app (op (E₂.X l)) (α'.hom.val.app (op (E₂.X l)) t) = 0 :=
    congrArg (fun φ => (φ.hom.val.app (op (E₂.X l))) t) hπ
  change Cq.obj.val.map (E₂.f l ≫ E.f j).op c = 0
  rw [f1]
  exact (congrArg (Cq.obj.val.map g₂) hκ.symm).trans
    (f2.trans ((congrArg (π.hom.val.app (op (E₂.X l))) hres).trans f3))

/-- **Parasitic homology in `Mod(𝒳_τ, 𝒪_𝒳)` gives exactness in `QCoh(𝒪_𝒳)`**, for a topology `τ`
coarser than the fppf one. The cokernel in `QCoh(𝒪_𝒳)` of the map from `𝓕` to the kernel of `β` is
quasi-coherent and parasitic (`isParasitic_of_isParasitic_homology`), hence zero. -/
theorem exact_of_isParasitic_homology (τ : SiteKind)
    {F G H : quasicoherentModules B S hS 𝒳} {α : F ⟶ G} {β : G ⟶ H} {w : α ≫ β = 0}
    (hpar : IsParasitic B S hS 𝒳 τ (siteShortComplex B S hS 𝒳 τ α β w).homology.val) :
    (ShortComplex.mk α β w).Exact := by
  let i := quasicoherentInclusion B S hS 𝒳
  have : i.IsLeftAdjoint := (coheratorAdjunction B S hS 𝒳).isLeftAdjoint
  have hC := isParasitic_of_isParasitic_homology τ (kernel.ι β) (kernel.lift β α w)
    (kernel.lift_ι β α w)
    (fun x hx => injective_and_range_eq_ker_of_isLimit_kernelFork B S hS 𝒳 β (kernelIsKernel β)
      x hx)
    (cokernel.π (kernel.lift β α w)) (cokernel.condition _) hpar
  have : (i.obj (cokernel (kernel.lift β α w))).IsQuasicoherentOnSite :=
    (cokernel (kernel.lift β α w)).property
  have h0 : 𝟙 (i.obj (cokernel (kernel.lift β α w))) = 0 :=
    eq_zero_of_isQuasicoherentOnSite_of_isParasitic B S hS 𝒳
      (T := i.obj (cokernel (kernel.lift β α w))) hC _
  have hz : IsZero (cokernel (kernel.lift β α w)) := by
    rw [IsZero.iff_id_eq_zero]
    exact i.map_injective (by rwa [i.map_id, i.map_zero])
  exact (ShortComplex.mk α β w).exact_iff_epi_kernel_lift.2
    (Preadditive.epi_of_cokernel_zero (hz.eq_of_tgt _ _))

/-- **Stacks 0776.** Let `𝒳` be an algebraic stack and let `α : 𝓕 ⟶ 𝓖` and `β : 𝓖 ⟶ 𝓗` be maps in
`QCoh(𝒪_𝒳)` with `β ∘ α = 0`. The following are equivalent:

1. in the abelian category `QCoh(𝒪_𝒳)` the complex `𝓕 ⟶ 𝓖 ⟶ 𝓗` is exact at `𝓖`;
2. `Ker(β)/Im(α)` computed in `Mod(𝒳_étale, 𝒪_𝒳)` is parasitic;
3. `Ker(β)/Im(α)` computed in `Mod(𝒳_fppf, 𝒪_𝒳)` is parasitic.

The abelian structure of `QCoh(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.AlgebraicStacks.instAbelianQuasicoherentModules`; `Ker(β)/Im(α)`
computed in `Mod(𝒳_τ, 𝒪_𝒳)` is the homology of the complex `𝓕 ⟶ 𝓖 ⟶ 𝓗` regarded as a complex of
sheaves of modules on the site of `τ` (**Stacks 06TP**), and parasitic is **Stacks 0773**. -/
@[stacks 0776]
theorem tfae_exact_isParasitic_homology {F G H : quasicoherentModules B S hS 𝒳} (α : F ⟶ G)
    (β : G ⟶ H) (w : α ≫ β = 0) :
    List.TFAE [(ShortComplex.mk α β w).Exact,
      IsParasitic B S hS 𝒳 .etale ((ShortComplex.mk α β w).map
        (FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .etale)).homology.val,
      IsParasitic B S hS 𝒳 .fppf ((ShortComplex.mk α β w).map
        (FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).homology.val] := by
  tfae_have 1 → 2 := isParasitic_homology_of_exact .etale le_rfl
  tfae_have 1 → 3 := isParasitic_homology_of_exact .fppf
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
  tfae_have 2 → 1 := exact_of_isParasitic_homology .etale
  tfae_have 3 → 1 := exact_of_isParasitic_homology .fppf
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
