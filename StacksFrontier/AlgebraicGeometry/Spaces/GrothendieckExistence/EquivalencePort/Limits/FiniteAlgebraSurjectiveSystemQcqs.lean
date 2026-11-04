module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AssemblyFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The symmetric-algebra system of a finite quasi-coherent algebra

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `𝒜` be a
finite quasi-coherent `𝒪_X`-algebra. By Stacks 086Y there is a finitely presented `𝒪_X`-module
`ℱ` with an epimorphism `ℱ ⟶ 𝒜`, which induces a locally surjective morphism `Sym(ℱ) ⟶ 𝒜` of
sheaves of algebras. Finite sets of generators of its kernel `𝒥` (through the extension property
of Stacks 0829) give sheaves of ideals `(ℰ)` of `Sym(ℱ)`. Every quotient `Sym(ℱ)/(ℰ)` is
quasi-coherent of finite presentation, every local section of `𝒥` lies locally in one of the
ideals, and for some finite set of generators the quotient is integral. These are the finite
algebras of finite presentation of Stacks 086Z.

All names are in the namespace `AlgebraicGeometry.Space.C1573`.

## Main definitions

* `symAlg`: the symmetric algebra `Sym(ℱ)`.
* `symLift`: the morphism `Sym(ℱ) ⟶ 𝒜` induced by `ℱ ⟶ 𝒜`.
* `kerIdeal`: the sheaf of ideals of `Sym(ℱ)` attached to a finite set of generators of the
  kernel.

## Main results

* `exists_isFinitePresentationOnSite_epi_underlyingModule`: a finite quasi-coherent algebra on a
  quasi-compact quasi-separated algebraic space is a quotient of a finitely presented module.
* `isIntegral_of_surjective_symmetricAlgebra`: a quotient of a symmetric algebra in which the
  images of finitely many generators of the module satisfy monic equations is integral.
* `isLocallySurjective_symLift`: `Sym(ℱ) ⟶ 𝒜` is locally surjective.
* `memSieve_kerIdeal_mem`: a section of `Sym(ℱ)` killed by `Sym(ℱ) ⟶ 𝒜` lies locally in one of
  the ideals.
* `isFinitePresentation_idealQuotient_kerIdeal`: every quotient `Sym(ℱ)/(ℰ)` is of finite
  presentation.
* `exists_isIntegral_idealQuotient_kerIdeal`: for some finite set of generators the quotient is
  integral.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- **The underlying module of a finite quasi-coherent algebra is of finite type.** -/
theorem C1573.isFiniteTypeOnSite_underlyingModule_of_quasicoherentAlgebra_isFinite
    {Y : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS Y) (hA : A.obj.IsFinite) :
    SheafOfModules.IsFiniteTypeOnSite (AlgebraSheaf.underlyingModule A.obj) :=
  isFiniteTypeOnSite_of_forall_affine_moduleFinite B S hS Y.1 Y.2 _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ A.property)
    fun C hC => hA C hC

/-- **A finite quasi-coherent algebra on a quasi-compact quasi-separated algebraic space is a
quotient of a module of finite presentation** (Stacks 086Y). -/
theorem C1573.exists_isFinitePresentationOnSite_epi_underlyingModule {Y : AlgebraicSpaces B S hS}
    (A : QuasicoherentAlgebra B S hS Y) (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj) (hA : A.obj.IsFinite) :
    ∃ (G : Modules.{u, u} B S hS Y.1 Y.2) (_ : G.IsQuasicoherentOnSite)
      (_ : SheafOfModules.IsFinitePresentationOnSite G)
      (p : G ⟶ AlgebraSheaf.underlyingModule A.obj), Epi p := by
  have := isFiniteTypeOnSite_underlyingModule_of_quasicoherentAlgebra_isFinite A hA
  obtain ⟨G, hG, p, hp⟩ := exists_isFinitePresentation_epi_of_isFiniteTypeOnSite B S hS Y.2 hqc
    (AlgebraSheaf.underlyingModule A.obj)
    (isLocallyFpGenerated_of_isQuasiCompactSpace B S hS B.contains_terminal Y.2 hqc hqs _
      A.property)
  have hG' := AffineExtension.isFinitePresentationOnSite_of_isFinitePresentation B S hS Y.2 G hG
  exact ⟨G, inferInstance, hG', p, hp⟩


/-- **A quotient of a symmetric algebra in which the images of finitely many generators of the
module satisfy monic equations is integral.** -/
theorem C1573.isIntegral_of_surjective_symmetricAlgebra {R C M : Type*} [CommRing R] [CommRing C]
    [AddCommGroup M] [Module R M] (c : R →+* C) (θ : SymmetricAlgebra R M →+* C)
    (hθ : Function.Surjective θ) (hcomp : θ.comp (algebraMap R (SymmetricAlgebra R M)) = c)
    {n : ℕ} (γ : Fin n → M) (hγ : Submodule.span R (Set.range γ) = ⊤)
    (hmon : ∀ k, ∃ P : Polynomial R, P.Monic ∧
      θ (P.eval₂ (algebraMap R (SymmetricAlgebra R M)) (SymmetricAlgebra.ι R M (γ k))) = 0) :
    c.IsIntegral := by
  let : Algebra R C := c.toAlgebra
  have hint : ∀ z : SymmetricAlgebra R M, c.IsIntegralElem (θ z) := by
    intro z
    induction z using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [← RingHom.comp_apply, hcomp]; exact c.isIntegralElem_map
    | ι m =>
      have hm : m ∈ Submodule.span R (Set.range γ) := by rw [hγ]; exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        obtain ⟨P, hPm, hP⟩ := hmon k
        refine ⟨P, hPm, ?_⟩
        rw [Polynomial.hom_eval₂, hcomp] at hP
        exact hP
      | zero => rw [map_zero, map_zero]; exact c.isIntegralElem_zero
      | add y y' _ _ hy hy' => rw [map_add, map_add]; exact RingHom.IsIntegralElem.add c hy hy'
      | smul r y _ hy =>
        rw [map_smul, Algebra.smul_def, map_mul, ← RingHom.comp_apply, hcomp]
        exact RingHom.IsIntegralElem.mul c c.isIntegralElem_map hy
    | mul a b ha hb => rw [map_mul]; exact RingHom.IsIntegralElem.mul c ha hb
    | add a b ha hb => rw [map_add]; exact RingHom.IsIntegralElem.add c ha hb
  intro y
  obtain ⟨z, rfl⟩ := hθ y
  exact hint z


section System

variable {Y : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS Y)
  {G : Modules.{u, u} B S hS Y.1 Y.2} (p : G ⟶ AlgebraSheaf.underlyingModule A.obj)

/-- The symmetric algebra `Sym(ℱ)` of `ℱ`, as a sheaf of algebras. -/
abbrev C1573.symAlg : AlgebraSheaf.{u, u} B S hS Y.1 Y.2 := symmetricAlgebraSheaf B S hS Y G

/-- The morphism `Sym(ℱ) ⟶ 𝒜` induced by `ℱ ⟶ 𝒜`. -/
abbrev C1573.symLift : symAlg (G := G) ⟶ A.obj := SymAlgSheaf.algebraLift B S hS Y A.obj G p

/-- **The morphism `Sym(ℱ) ⟶ 𝒜` is locally surjective when `ℱ ⟶ 𝒜` is an epimorphism**: every
local section of `𝒜` is locally the image of a section of `ℱ`, and the morphism restricts to
`ℱ ⟶ 𝒜` in degree one. -/
theorem C1573.isLocallySurjective_symLift [Epi p] :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1) (symLift A p).right.hom := by
  have hp := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p
  refine ⟨fun {U} t => ?_⟩
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_ (hp.imageSieve_mem t)
  rintro V g ⟨s, hs⟩
  refine ⟨(symmetricAlgebra B S hS Y G).ungradedIncl 1
    ((symmetricAlgebraGen B S hS Y G).val.app (op V) s), ?_⟩
  exact (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS Y A.obj G p (op V) s).trans hs

/-- The morphism of underlying modules of `Sym(ℱ) ⟶ 𝒜`. -/
abbrev C1573.symLiftMod : AlgebraSheaf.underlyingModule (symAlg (G := G)) ⟶
    AlgebraSheaf.underlyingModule A.obj :=
  AlgebraSheaf.underlyingModuleMap (symLift A p)

/-- **A section of `Sym(ℱ)` killed by `Sym(ℱ) ⟶ 𝒜` comes from the kernel.** -/
theorem C1573.exists_kernel_lift (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : (symAlg (G := G)).right.obj.obj U) (ha : ((symLift A p).right.hom.app U).hom a = 0) :
    ∃ k : (kernel (symLiftMod A p)).val.obj U,
      (((kernel.ι (symLiftMod A p)).val.app U k :
        (AlgebraSheaf.underlyingModule (symAlg (G := G))).val.obj U) :
          (symAlg (G := G)).right.obj.obj U) = a :=
  ((SheafOfModules.exact_kernel_ι_val_app (symLiftMod A p) U) a).1 ha

variable (hG : G.IsQuasicoherentOnSite)
include hG

/-- The underlying module of `Sym(ℱ)` is cartesian on affine charts when `ℱ` is quasi-coherent. -/
theorem C1573.isCartesianOnAffineCharts_symAlg :
    IsCartesianOnAffineCharts (AlgebraSheaf.underlyingModule (symAlg (G := G))) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
    (SymAlgSheaf.isQuasicoherent_symmetricAlgebraSheaf B S hS Y G hG)

/-- The kernel of `Sym(ℱ) ⟶ 𝒜`, as a morphism of underlying modules, is cartesian on affine
charts. -/
theorem C1573.isCartesianOnAffineCharts_kernel_symLiftMod :
    IsCartesianOnAffineCharts (kernel (symLiftMod A p)) :=
  isCartesianOnAffineCharts_kernel _ (isCartesianOnAffineCharts_symAlg hG)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ A.property)

variable (hqc : IsQuasiCompactSpace B S hS Y.obj)
  (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)

/-- The sheaf of ideals of `Sym(ℱ)` attached to a finite set of generators of the kernel. -/
abbrev C1573.kerIdeal (s : Finset (KernelIdealSystem.Gen (kernel (symLiftMod A p)))) :
    (symAlg (G := G)).IdealSheaf :=
  KernelIdealSystem.ideal (symAlg (G := G)) (kernel.ι (symLiftMod A p))
    (isCartesianOnAffineCharts_kernel_symLiftMod A p hG)
    (chartExtensionProperty_id B.contains_terminal hqc hqs
      (isCartesianOnAffineCharts_kernel_symLiftMod A p hG)) s

/-- **A section of `Sym(ℱ)` over an affine chart killed by `Sym(ℱ) ⟶ 𝒜` lies in one ideal of the
system.** -/
theorem C1573.exists_mem_kerIdeal {W : SmallEtale B S hS Y.1} (hW : IsAffine (chartScheme W))
    (a : (symAlg (G := G)).right.obj.obj (op W))
    (ha : ((symLift A p).right.hom.app (op W)).hom a = 0) :
    ∃ x, a ∈ (kerIdeal A p hG hqc hqs {x}).obj (op W) := by
  obtain ⟨k, hk⟩ := exists_kernel_lift A p _ a ha
  obtain ⟨x, hx⟩ := KernelIdealSystem.exists_mem_ideal (symAlg (G := G))
    (kernel.ι (symLiftMod A p)) (isCartesianOnAffineCharts_kernel_symLiftMod A p hG)
    (chartExtensionProperty_id B.contains_terminal hqc hqs
      (isCartesianOnAffineCharts_kernel_symLiftMod A p hG)) hW k
  refine ⟨x, ?_⟩
  rw [← hk]
  exact hx

/-- **Every section of `Sym(ℱ)` killed by `Sym(ℱ) ⟶ 𝒜` lies, locally, in one of the ideals of the
system.** -/
theorem C1573.memSieve_kerIdeal_mem (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : (symAlg (G := G)).right.obj.obj U) (ha : ((symLift A p).right.hom.app U).hom a = 0) :
    Stacks.Sites.memSieve (O := (symAlg (G := G)).right) (kerIdeal A p hG hqc hqs) a ∈
      SmallEtale.topology B S hS Y.1 U.unop := by
  obtain ⟨U⟩ := U
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS Y.1 U)
  rintro V g hg
  obtain ⟨O, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  refine (Stacks.Sites.memSieve (O := (symAlg (G := G)).right)
    (kerIdeal A p hG hqc hqs) a).downward_closed ?_ h
  set i := openChartInclusion B S hS Y.1 U O.down.1 with hi
  set a' := ((symAlg (G := G)).right.obj.map i.op).hom a with ha'
  have hfa' : ((symLift A p).right.hom.app (op (openChart B S hS Y.1 U O.down.1))).hom a' = 0 :=
    (NatTrans.naturality_apply (symLift A p).right.hom i.op a).trans
      ((congrArg _ ha).trans (map_zero _))
  obtain ⟨x, hx⟩ := exists_mem_kerIdeal A p hG hqc hqs
    (isAffine_chartScheme_openChart B S hS Y.1 U O.down) a' hfa'
  exact ⟨{x}, hx⟩


/-- `Sym(ℱ)` is a quasi-coherent sheaf of algebras when `ℱ` is quasi-coherent. -/
theorem C1573.isQuasicoherent_symAlg : (symAlg (G := G)).IsQuasicoherent :=
  SymAlgSheaf.isQuasicoherent_symmetricAlgebraSheaf B S hS Y G hG

/-- The ideal `(ℰ)` of `Sym(ℱ)` attached to a finite set of generators of the kernel is a
quasi-coherent module. -/
theorem C1573.isQuasicoherentOnSite_idealModule_kerIdeal
    (s : Finset (KernelIdealSystem.Gen (kernel (symLiftMod A p)))) :
    (AlgebraSheaf.idealModule (symAlg (G := G))
      (kerIdeal A p hG hqc hqs s)).IsQuasicoherentOnSite :=
  KernelIdealSystem.isQuasicoherentOnSite_idealModule_ideal _ _ _ _
    (isCartesianOnAffineCharts_symAlg hG) s

/-- The quotient `Sym(ℱ)/(ℰ)` is a quasi-coherent sheaf of algebras. -/
theorem C1573.isQuasicoherent_idealQuotient_kerIdeal
    (s : Finset (KernelIdealSystem.Gen (kernel (symLiftMod A p)))) :
    ((symAlg (G := G)).idealQuotient (kerIdeal A p hG hqc hqs s)).IsQuasicoherent :=
  AlgebraSheaf.isQuasicoherent_idealQuotient _ _ (isQuasicoherent_symAlg hG)
    (isQuasicoherentOnSite_idealModule_kerIdeal A p hG hqc hqs s)

/-- The quotient `Sym(ℱ)/(ℰ)` is of finite presentation when `ℱ` is of finite presentation. -/
theorem C1573.isFinitePresentation_idealQuotient_kerIdeal
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (s : Finset (KernelIdealSystem.Gen (kernel (symLiftMod A p)))) :
    ((symAlg (G := G)).idealQuotient (kerIdeal A p hG hqc hqs s)).IsFinitePresentation :=
  AlgebraSheaf.isFinitePresentation_idealQuotient _ _ (isQuasicoherent_symAlg hG)
    (isQuasicoherentOnSite_idealModule_kerIdeal A p hG hqc hqs s)
    (SymAlgSheaf.isFinitePresentation_symmetricAlgebraSheaf B S hS Y G hG hGfp)
    (fun W hW => KernelIdealSystem.fg_sectionIdeal_ideal _ _ _ _
      (isCartesianOnAffineCharts_symAlg hG) s W hW)

/-- **For some finite set of generators the quotient is integral** (the last step of the proof of
Stacks 086Z): over an affine surjective étale chart `U`, the images in `𝒜(U)` of generators of
`ℱ(U)` satisfy monic equations, whose values in `Sym(ℱ)(U)` lie in the kernel and hence in one
ideal of the system. -/
theorem C1573.exists_isIntegral_idealQuotient_kerIdeal (hA : A.obj.IsFinite)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ s, ((symAlg (G := G)).idealQuotient (kerIdeal A p hG hqc hqs s)).IsIntegral := by
  classical
  obtain ⟨U, q, hU, hqs', hqe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).mp hqc
  have hqe' := presheaf_etale_of_isEtale B S hS hqe
  set W0 : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk q, hqe'⟩ with hW0def
  have hW0 : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W0) := hU
  have hW0c : IsAffine (chartScheme W0) := hU
  clear_value W0
  have : Module.FinitePresentation (chartRing B S hS Y.1 Y.2 W0)
      ((SymAlgSheaf.FM B S hS Y G).val.obj (op W0)) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hGfp W0 hW0
  obtain ⟨n, γ, hγ⟩ := Module.Finite.exists_fin (R := chartRing B S hS Y.1 Y.2 W0)
    (M := (SymAlgSheaf.FM B S hS Y G).val.obj (op W0))
  let σ := SymAlgSheaf.symSectionsRingHom B S hS Y G W0
  have hcomp : ∀ {C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (f : symAlg (G := G) ⟶ C),
      ((f.right.hom.app (op W0)).hom.comp σ).comp (algebraMap (chartRing B S hS Y.1 Y.2 W0)
        (SymmetricAlgebra (chartRing B S hS Y.1 Y.2 W0)
          ((SymAlgSheaf.FM B S hS Y G).val.obj (op W0)))) = C.algebraMap (op W0) := fun f =>
    RingHom.ext fun r => (congrArg (f.right.hom.app (op W0)).hom
      (RingHom.congr_fun (SymAlgSheaf.symSectionsRingHom_comp_algebraMap B S hS Y G W0) r)).trans
      (f.comm (op W0) r)
  let ψ := ((symLift A p).right.hom.app (op W0)).hom.comp σ
  have hAint : (ψ.comp (algebraMap (chartRing B S hS Y.1 Y.2 W0)
      (SymmetricAlgebra (chartRing B S hS Y.1 Y.2 W0)
        ((SymAlgSheaf.FM B S hS Y G).val.obj (op W0))))).IsIntegral := by
    rw [hcomp (symLift A p)]; exact RingHom.IsIntegral.of_finite (hA W0 hW0)
  have hmon : ∀ k, ∃ P : Polynomial (chartRing B S hS Y.1 Y.2 W0), P.Monic ∧
      ψ (P.eval₂ (algebraMap _ _) (SymmetricAlgebra.ι _ _ (γ k))) = 0 := by
    intro k
    obtain ⟨P, hPm, hP⟩ := hAint (ψ (SymmetricAlgebra.ι _ _ (γ k)))
    exact ⟨P, hPm, (Polynomial.hom_eval₂ (p := P) (f := algebraMap _ _) (g := ψ) _).trans hP⟩
  choose P hPm hP using hmon
  have hgen : ∀ k, ∃ x : KernelIdealSystem.Gen (kernel (symLiftMod A p)),
      σ ((P k).eval₂ (algebraMap _ _) (SymmetricAlgebra.ι _ _ (γ k))) ∈
        (kerIdeal A p hG hqc hqs {x}).obj (op W0) :=
    fun k => exists_mem_kerIdeal A p hG hqc hqs hW0c _ (hP k)
  choose x hx using hgen
  refine ⟨Finset.univ.image x, ?_⟩
  let s := Finset.univ.image x
  let C := (symAlg (G := G)).idealQuotient (kerIdeal A p hG hqc hqs s)
  let θ := (((symAlg (G := G)).toIdealQuotient (kerIdeal A p hG hqc hqs s)).right.hom.app
    (op W0)).hom.comp σ
  have hθs : Function.Surjective θ :=
    (AlgebraSheaf.surjective_toIdealQuotient_app _ _ (isQuasicoherent_symAlg hG)
      (isQuasicoherentOnSite_idealModule_kerIdeal A p hG hqc hqs s) W0 hW0).comp
      (SymAlgSheaf.symSectionsRingHom_bijective B S hS Y G hG W0 hW0).2
  have hint0 : (θ.comp (algebraMap (chartRing B S hS Y.1 Y.2 W0)
      (SymmetricAlgebra (chartRing B S hS Y.1 Y.2 W0)
        ((SymAlgSheaf.FM B S hS Y G).val.obj (op W0))))).IsIntegral := by
    refine isIntegral_of_surjective_symmetricAlgebra (R := chartRing B S hS Y.1 Y.2 W0) _ θ hθs
      rfl γ hγ fun k => ⟨P k, hPm k, ?_⟩
    refine AlgebraSheaf.toIdealQuotient_apply_eq_zero _ _ (op W0) _ ?_
    exact KernelIdealSystem.ideal_mono _ _ _ _
      (Finset.singleton_subset_iff.2 (Finset.mem_image_of_mem x (Finset.mem_univ k))) _ (hx k)
  have hint : RingHom.IsIntegral (C.algebraMap (op W0)) :=
    hcomp ((symAlg (G := G)).toIdealQuotient (kerIdeal A p hG hqc hqs s)) ▸ hint0
  subst hW0def
  exact AlgebraSheaf.isIntegral_of_isIntegral_affineChart B S hS
    ⟨C, isQuasicoherent_idealQuotient_kerIdeal A p hG hqc hqs s⟩
    (isFinitePresentation_idealQuotient_kerIdeal A p hG hqc hqs hGfp s).isFiniteType hqs' hqe' hU
    hint


end System


end AlgebraicGeometry.Space

end
