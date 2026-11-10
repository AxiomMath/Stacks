module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.CommonRefinement
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen

/-!
# The Euler characteristic of a coherent triple is well defined

The Euler characteristic of a prepared extension (`PreparedExtension.eulerCharacteristic`) and
**Stacks Tag 0F25**: two prepared extensions of the same coherent triple have the same Euler
characteristic (`PreparedExtension.eulerCharacteristic_eq`,
`preparedExtension_lengthIndex_eq`). The proof passes from the common refinement to the closed
fibre and compares length indices. It also proves the exactness statements used for
additivity: global sections on an affine scheme are exact on quasi-coherent modules
(`specSections_shortExact`), and reduction modulo a scalar acting regularly, and reduction to
the closed fibre, keep a short exact sequence short exact.

This file is part of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic`; see there
for the overview and references.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

-- The complete-lattice structure on `F.Submodule` already exists upstream; it is made available
-- locally rather than re-declared, because an anonymous `local instance` with this type gets a
-- derived name that collides with the identical one in
-- `StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic`.
attribute [local instance] SheafOfModules.Submodule.instCompleteLattice

/-- A left adjoint between preadditive categories with binary biproducts is additive. -/
private theorem additive_of_isLeftAdjoint {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] (F : C ⥤ D) [F.IsLeftAdjoint] :
    F.Additive := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The reduction of a linear map modulo a scalar, as a map of the quotients by the submodules
it spans. -/
private noncomputable def scalarQuotMap {A : Type u} [CommRing A] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (r : A) (g : M →ₗ[A] N) :
    (M ⧸ Ideal.span {r} • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) :=
  Submodule.mapQ _ _ g (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

/-- The functor carrying a module to the quasi-coherent module it generates is additive. -/
private instance additive_tildeFunctor (R : CommRingCat.{u}) :
    (tilde.functor R).Additive := by
  have : (tilde.functor R).IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  exact additive_of_isLeftAdjoint _

private theorem scalarQuotMap_mk {A : Type u} [CommRing A] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (r : A) (g : M →ₗ[A] N)
    (x : M) :
    scalarQuotMap r g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) := rfl

private theorem specPullbackSectionsIso_natural
    (R S : CommRingCat.{u}) (φ : R ⟶ S) {G H : (Spec R).Modules}
    [G.IsQuasicoherent] [H.IsQuasicoherent] (g : G ⟶ H) :
    (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.pullback (Spec.map φ)).map g) ≫
        (specPullbackSectionsIso R S φ H).hom =
        (specPullbackSectionsIso R S φ G).hom ≫
        (ModuleCat.extendScalars φ.hom).map ((moduleSpecΓFunctor (R := R)).map g) := by
  have hnatInv : (asIso G.fromTildeΓ).inv ≫
      (tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map g) =
      g ≫ (asIso H.fromTildeΓ).inv := by
    apply (cancel_mono (asIso H.fromTildeΓ).hom).1
    calc
      ((asIso G.fromTildeΓ).inv ≫
          (tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map g)) ≫
          (asIso H.fromTildeΓ).hom = (asIso G.fromTildeΓ).inv ≫
            ((tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map g) ≫
              (asIso H.fromTildeΓ).hom) :=
          Category.assoc _ _ _
      _ = (asIso G.fromTildeΓ).inv ≫ (G.fromTildeΓ ≫ g) :=
        congrArg ((asIso G.fromTildeΓ).inv ≫ ·) ((tilde.adjunction (R := R)).counit.naturality g)
      _ = g ≫ (asIso H.fromTildeΓ).inv ≫ (asIso H.fromTildeΓ).hom := by simp
  let p := Scheme.Modules.pullback (Spec.map φ)
  let E := ModuleCat.extendScalars φ.hom
  let N_R := moduleSpecΓFunctor (R := R)
  let N_S := moduleSpecΓFunctor (R := S)
  let aG := (p.mapIso (asIso G.fromTildeΓ).symm).hom
  let aH := (p.mapIso (asIso H.fromTildeΓ).symm).hom
  let bG := AlgebraicGeometry.pullbackTildeIso R S φ |>.app (N_R.obj G)
  let bH := AlgebraicGeometry.pullbackTildeIso R S φ |>.app (N_R.obj H)
  let cG := (tilde.toTildeΓNatIso (R := S)).symm.app (E.obj (N_R.obj G))
  let cH := (tilde.toTildeΓNatIso (R := S)).symm.app (E.obj (N_R.obj H))
  have hpull : N_S.map (p.map g) ≫ N_S.map aH =
      N_S.map aG ≫ N_S.map (p.map ((tilde.functor (R := R)).map
        ((moduleSpecΓFunctor (R := R)).map g))) := by
    have h : p.map g ≫ aH = aG ≫ p.map ((tilde.functor (R := R)).map
        ((moduleSpecΓFunctor (R := R)).map g)) := by
      change p.map g ≫ p.map (asIso H.fromTildeΓ).inv =
        p.map (asIso G.fromTildeΓ).inv ≫ p.map ((tilde.functor (R := R)).map
          ((moduleSpecΓFunctor (R := R)).map g))
      exact ((p.map_comp _ _).symm.trans
        (congrArg p.map hnatInv.symm)).trans (p.map_comp _ _)
    exact ((N_S.map_comp _ _).symm.trans
      (congrArg N_S.map h)).trans (N_S.map_comp _ _)
  have hT : p.map ((tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map g)) ≫
      bH.hom = bG.hom ≫ (tilde.functor (R := S)).map
        (E.map ((moduleSpecΓFunctor (R := R)).map g)) := by
    have h := (AlgebraicGeometry.pullbackTildeIso R S φ).hom.naturality
      ((moduleSpecΓFunctor (R := R)).map g)
    simpa [bG, bH, E, N_R, Functor.comp_map, Functor.comp_obj] using h
  have hTΓ : N_S.map
      (p.map ((tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map g))) ≫
      N_S.map bH.hom = N_S.map bG.hom ≫ N_S.map ((tilde.functor (R := S)).map
        (E.map ((moduleSpecΓFunctor (R := R)).map g))) := by
    simpa only [Functor.map_comp] using congrArg (fun k => N_S.map k) hT
  have hC : N_S.map ((tilde.functor (R := S)).map
      (E.map ((moduleSpecΓFunctor (R := R)).map g))) ≫ cH.hom =
      cG.hom ≫ E.map ((moduleSpecΓFunctor (R := R)).map g) := by
    have h := ((tilde.toTildeΓNatIso (R := S)).symm.hom).naturality
      (E.map ((moduleSpecΓFunctor (R := R)).map g))
    simpa [cG, cH, E, N_R, N_S, Functor.comp_map, Functor.comp_obj] using h
  change N_S.map (p.map g) ≫ N_S.map aH ≫ N_S.map bH.hom ≫ cH.hom =
    N_S.map aG ≫ N_S.map bG.hom ≫ cG.hom ≫
      E.map ((moduleSpecΓFunctor (R := R)).map g)
  calc
    _ = (N_S.map (p.map g) ≫ N_S.map aH) ≫ N_S.map bH.hom ≫ cH.hom := by
      simp [Category.assoc]
    _ = (N_S.map aG ≫ N_S.map (p.map ((tilde.functor (R := R)).map
          ((moduleSpecΓFunctor (R := R)).map g)))) ≫
        N_S.map bH.hom ≫ cH.hom :=
      congrArg (fun t => t ≫ N_S.map bH.hom ≫ cH.hom) hpull
    _ = N_S.map aG ≫
        (N_S.map (p.map ((tilde.functor (R := R)).map
          ((moduleSpecΓFunctor (R := R)).map g))) ≫ N_S.map bH.hom) ≫ cH.hom := by
      simp [Category.assoc]
    _ = N_S.map aG ≫
        (N_S.map bG.hom ≫ N_S.map ((tilde.functor (R := S)).map
          (E.map ((moduleSpecΓFunctor (R := R)).map g)))) ≫ cH.hom :=
      congrArg (fun t => N_S.map aG ≫ t ≫ cH.hom) hTΓ
    _ = N_S.map aG ≫ N_S.map bG.hom ≫
        (N_S.map ((tilde.functor (R := S)).map
          (E.map ((moduleSpecΓFunctor (R := R)).map g))) ≫ cH.hom) := by
      simp [Category.assoc]
    _ = N_S.map aG ≫ N_S.map bG.hom ≫
        (cG.hom ≫ E.map ((moduleSpecΓFunctor (R := R)).map g)) :=
      congrArg (fun t => N_S.map aG ≫ N_S.map bG.hom ≫ t) hC
    _ = N_S.map aG ≫ N_S.map bG.hom ≫ cG.hom ≫
        E.map ((moduleSpecΓFunctor (R := R)).map g) := by
      simp

/-- Restricting scalars to `A` of the base change of an `A`-module `M` along `A → A / fA` is
`M ⧸ fM`. This is `TensorProduct.quotTensorEquivQuotSMul`, stated once at the
extension-of-scalars spelling of its source: that spelling and the tensor product are the same
object but not the same expression, and pinning them together here is what lets
`closedFibreQuotientIso` and its naturality be stated between literally the same objects. -/
private noncomputable def extendScalarsQuotIso (A : Type u) [CommRing A] (f : A)
    (M : ModuleCat.{u} A) :
    (restrictScalarsQuot A f).obj
        ((ModuleCat.extendScalars
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))).hom).obj M) ≅
      ModuleCat.of A (M ⧸ Ideal.span {f} • (⊤ : Submodule A M)) := by
  with_unfolding_all exact
    (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {f})).toModuleIso

private noncomputable def closedFibreQuotientIso
    (A : Type u) [CommRing A] (f : A) (G : (baseScheme A).Modules)
    [G.IsQuasicoherent] :
    (closedFibreSectionsFunctor A f).obj G ≅
      ModuleCat.of A (((moduleSpecΓFunctor (R := .of A)).obj G) ⧸
        Ideal.span {f} • (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj G))) :=
  (restrictScalarsQuot A f).mapIso
      (specPullbackSectionsIso (.of A) (.of (A ⧸ Ideal.span {f}))
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) G) ≪≫
    extendScalarsQuotIso A f ((moduleSpecΓFunctor (R := .of A)).obj G)

private lemma closedFibreQuotientIso_naturality
    (A : Type u) [CommRing A] (f : A)
    {G H : (baseScheme A).Modules} [G.IsQuasicoherent] [H.IsQuasicoherent]
    (g : G ⟶ H) :
    (closedFibreSectionsFunctor A f).map g ≫ (closedFibreQuotientIso A f H).hom =
      (closedFibreQuotientIso A f G).hom ≫
        ModuleCat.ofHom (scalarQuotMap f ((moduleSpecΓFunctor (R := .of A)).map g).hom) := by
  have hmap : (closedFibreSectionsFunctor A f).map g =
      (restrictScalarsQuot A f).map
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).map
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {f}))))).map g)) := rfl
  simp only [closedFibreQuotientIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [hmap, ← Category.assoc, ← Functor.map_comp,
    specPullbackSectionsIso_natural (.of A) (.of (A ⧸ Ideal.span {f}))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) g,
    Functor.map_comp, Category.assoc, Category.assoc]
  refine congrArg (fun morphism => (restrictScalarsQuot A f).map
    (specPullbackSectionsIso (.of A) (.of (A ⧸ Ideal.span {f}))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) G).hom ≫ morphism) ?_
  apply ModuleCat.hom_ext
  with_unfolding_all
    apply TensorProduct.ext
    ext scalar value
    obtain ⟨scalar, rfl⟩ := Ideal.Quotient.mk_surjective scalar
    change (TensorProduct.quotTensorEquivQuotSMul
        ((moduleSpecΓFunctor (R := .of A)).obj H) (Ideal.span {f}))
        (Ideal.Quotient.mk (Ideal.span {f}) scalar ⊗ₜ[A]
          ((moduleSpecΓFunctor (R := .of A)).map g).hom value) =
      scalarQuotMap f ((moduleSpecΓFunctor (R := .of A)).map g).hom
        ((TensorProduct.quotTensorEquivQuotSMul
          ((moduleSpecΓFunctor (R := .of A)).obj G) (Ideal.span {f}))
          (Ideal.Quotient.mk (Ideal.span {f}) scalar ⊗ₜ[A] value))
    simp only [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      scalarQuotMap_mk, map_smul]

private lemma ambient_refinement_mono
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    {G H : (baseScheme A).Modules} [G.IsCoherent] [H.IsCoherent]
    (g : G ⟶ H)
    (hregG : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (hg : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map g)) : Mono g := by
  let R := Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι
  have : IsIso (R.map g) := hg
  have : (kernel g).IsCoherent := SheafOfModules.kernel_isCoherent g
  have hzero : IsZero (R.obj (kernel g)) :=
    (isZero_kernel_of_mono (R.map g)).of_iso (PreservesKernel.iso R g)
  obtain ⟨n, hn⟩ := maximalIdealPower_smul_top_eq_bot A (kernel g)
    (SheafOfModules.kernel_isCoherent g) hzero
  have hreg := regular_of_mono A f (kernel.ι g) hregG ⊤
  have hpow : IsSMulRegular ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) (f ^ n) :=
    IsSMulRegular.pow n hreg
  have hmem : f ^ n ∈ IsLocalRing.maximalIdeal A ^ n := Ideal.pow_mem_pow hf n
  have : Subsingleton ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) := by
    refine ⟨fun value other => hpow ?_⟩
    have hz (value : (moduleSpecΓFunctor (R := .of A)).obj (kernel g)) :
        f ^ n • value = 0 := by
      have hm := Submodule.smul_mem_smul hmem
        (show value ∈ (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj
          (kernel g))) from trivial)
      rwa [hn] at hm
    exact (hz value).trans (hz other).symm
  have hzΓ : IsZero ((moduleSpecΓFunctor (R := .of A)).obj (kernel g)) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have : (kernel g).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have := additive_tildeFunctor (.of A)
  have hzker : IsZero (kernel g) :=
    ((tilde.functor (.of A)).map_isZero hzΓ).of_iso (asIso (kernel g).fromTildeΓ).symm
  exact Abelian.mono_of_kernel_ι_eq_zero g (hzker.eq_of_src _ _)

private lemma ambient_refinement_cokernel_finiteLength
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {G H : (baseScheme A).Modules} [G.IsCoherent] [H.IsCoherent]
    (g : G ⟶ H)
    (hg : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map g)) :
    IsFiniteLength A (((moduleSpecΓFunctor (R := .of A)).obj H) ⧸
      LinearMap.range ((moduleSpecΓFunctor (R := .of A)).map g).hom) := by
  let R := Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι
  have : R.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction _).isLeftAdjoint
  have : IsIso (R.map g) := hg
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have : H.IsQuasicoherent := isQuasicoherent_of_isCoherent H
  have : (cokernel g).IsCoherent := SheafOfModules.cokernel_isCoherent g
  have hzero : IsZero (R.obj (cokernel g)) :=
    (isZero_cokernel_of_epi (R.map g)).of_iso (PreservesCokernel.iso R g)
  exact ModuleCat.isFiniteLength_of_iso
    (specSectionsCokernelIso g ≪≫ ModuleCat.cokernelIsoRangeQuotient _)
    (finiteLength_globalSections_of_isZero_restrict A (cokernel g)
      (SheafOfModules.cokernel_isCoherent g) hzero)

private lemma reduction_finiteLength_correction
    (A : Type u) [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (r : A) (g : M →ₗ[A] N) (hinj : Function.Injective g)
    (hregN : Function.Injective ((LinearMap.lsmul A N) r))
    (hC : IsFiniteLength A (N ⧸ LinearMap.range g)) :
    IsFiniteLength A (LinearMap.ker (Module.linearMapSnakeInput A M N g hinj r).L₃.f.hom) ∧
      IsFiniteLength A ((Module.linearMapSnakeInput A M N g hinj r).L₃.X₂ ⧸
        LinearMap.range (Module.linearMapSnakeInput A M N g hinj r).L₃.f.hom) := by
  let S := Module.linearMapSnakeInput A M N g hinj r
  let C := N ⧸ LinearMap.range g
  let μC : C →ₗ[A] C := (LinearMap.lsmul A C) r
  have : Epi S.L₂.g :=
    (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  have : Epi S.L₃.g := S.epi_L₃_g
  let eC : S.L₃.X₃ ≅ ModuleCat.of A (C ⧸ LinearMap.range μC) :=
    IsColimit.coconePointUniqueUpToIso S.h₃τ₃
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom μC))
  have hc₃ : IsFiniteLength A S.L₃.X₃ := ModuleCat.isFiniteLength_of_iso eC.symm
    (IsFiniteLength.of_surjective hC (Submodule.mkQ_surjective _))
  have hrange : LinearMap.range S.L₃.f.hom = LinearMap.ker S.L₃.g.hom :=
    S.L₃_exact.moduleCat_range_eq_ker
  let e : (S.L₃.X₂ ⧸ LinearMap.range S.L₃.f.hom) ≃ₗ[A] S.L₃.X₃ :=
    (Submodule.quotEquivOfEq _ _ hrange).trans
      (LinearMap.quotKerEquivOfSurjective S.L₃.g.hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance))
  have hc := e.symm.isFiniteLength hc₃
  refine ⟨?_, hc⟩
  rw [← Module.length_ne_top_iff,
    Module.lengthIndex_zero_of_finiteLength_correction A M N r g hinj hregN hC]
  exact Module.length_ne_top_iff.mpr hc

private noncomputable def scalarCokernelIso
    {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    (r : A) :
    IsColimit (CokernelCofork.ofπ
      (ModuleCat.ofHom (Ideal.span {r} • (⊤ : Submodule A M)).mkQ)
      (show ModuleCat.ofHom ((LinearMap.lsmul A M) r) ≫
          ModuleCat.ofHom (Ideal.span {r} • (⊤ : Submodule A M)).mkQ = 0 from by
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_comp, ModuleCat.hom_zero, Submodule.ideal_span_singleton_smul]
        exact (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero)) := by
  apply ModuleCat.isColimitCokernelCofork
  · rw [Submodule.ideal_span_singleton_smul]
    exact LinearMap.exact_lsmul_mkQ_smul_top M r
  · exact Submodule.mkQ_surjective _

private lemma reduction_index_and_finiteLength
    (A : Type u) [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (r : A) (g : M →ₗ[A] N) (hinj : Function.Injective g)
    (hregN : Function.Injective ((LinearMap.lsmul A N) r))
    (hC : IsFiniteLength A (N ⧸ LinearMap.range g)) :
    let reduced := scalarQuotMap r g
    IsFiniteLength A (LinearMap.ker reduced) ∧
      IsFiniteLength A ((N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) ⧸
        LinearMap.range reduced) ∧
      ((Module.length A ((N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) ⧸
          LinearMap.range reduced)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker reduced)).toNat : ℤ) = 0 := by
  intro reduced
  let S := Module.linearMapSnakeInput A M N g hinj r
  let eM : S.L₃.X₁ ≅ ModuleCat.of A (M ⧸ Ideal.span {r} • (⊤ : Submodule A M)) :=
    S.h₃τ₁.coconePointUniqueUpToIso (scalarCokernelIso M r)
  let eN : S.L₃.X₂ ≅ ModuleCat.of A (N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) :=
    S.h₃τ₂.coconePointUniqueUpToIso (scalarCokernelIso N r)
  have hM : S.v₂₃.τ₁ ≫ eM.hom =
      ModuleCat.ofHom (Ideal.span {r} • (⊤ : Submodule A M)).mkQ :=
    S.h₃τ₁.comp_coconePointUniqueUpToIso_hom (scalarCokernelIso M r)
      WalkingParallelPair.one
  have hN : S.v₂₃.τ₂ ≫ eN.hom =
      ModuleCat.ofHom (Ideal.span {r} • (⊤ : Submodule A N)).mkQ :=
    S.h₃τ₂.comp_coconePointUniqueUpToIso_hom (scalarCokernelIso N r)
      WalkingParallelPair.one
  have : Epi S.v₂₃.τ₁ := S.epi_v₂₃_τ₁
  have hcomm : S.L₃.f ≫ eN.hom = eM.hom ≫ ModuleCat.ofHom reduced := by
    apply (cancel_epi S.v₂₃.τ₁).mp
    rw [← Category.assoc, S.v₂₃.comm₁₂, Category.assoc, hN,
      ← Category.assoc, hM]
    apply ModuleCat.hom_ext
    ext value
    rfl
  obtain ⟨hk, hc⟩ := reduction_finiteLength_correction A M N r g hinj hregN hC
  obtain ⟨hk', hc'⟩ := ModuleCat.isFiniteLength_kernel_cokernel_of_iso S.L₃.f
    (ModuleCat.ofHom reduced) eM eN hcomm hk hc
  refine ⟨hk', hc', ?_⟩
  have heq := ModuleCat.lengthIndex_eq_of_iso S.L₃.f (ModuleCat.ofHom reduced) eM eN hcomm
  change _ = ((Module.length A ((N ⧸ Ideal.span {r} • (⊤ : Submodule A N)) ⧸
    LinearMap.range reduced)).toNat : ℤ) -
      ((Module.length A (LinearMap.ker reduced)).toNat : ℤ) at heq
  apply heq.symm.trans
  have hz := Module.lengthIndex_zero_of_finiteLength_correction A M N r g hinj hregN hC
  change Module.length A (LinearMap.ker S.L₃.f.hom) =
    Module.length A (S.L₃.X₂ ⧸ LinearMap.range S.L₃.f.hom) at hz
  rw [hz, sub_self]

private lemma closedFibre_refinement_index_and_finiteLength
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (T : CoherentTriple A f) (P : PreparedExtension A f T)
    (G : (baseScheme A).Modules) [G.IsCoherent] (a : G ⟶ P.F')
    (hregG : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V) ((baseScheme A).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))
    (ha : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).map a)) :
    let reduced := (closedFibreSectionsFunctor A f).map a
    IsFiniteLength A (LinearMap.ker reduced.hom) ∧
      IsFiniteLength A (((closedFibreSectionsFunctor A f).obj P.F') ⧸
        LinearMap.range reduced.hom) ∧
      ((Module.length A (((closedFibreSectionsFunctor A f).obj P.F') ⧸
          LinearMap.range reduced.hom)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker reduced.hom)).toNat : ℤ) = 0 := by
  intro reduced
  have : P.F'.IsCoherent := P.coherent
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : Mono a := ambient_refinement_mono A f hf a hregG ha
  have : (moduleSpecΓFunctor (R := .of A)).IsRightAdjoint :=
    (tilde.adjunction (R := .of A)).isRightAdjoint
  have : Mono ((moduleSpecΓFunctor (R := .of A)).map a) := inferInstance
  let map := ((moduleSpecΓFunctor (R := .of A)).map a).hom
  obtain ⟨hk, hc, hz⟩ := reduction_index_and_finiteLength A
    ((moduleSpecΓFunctor (R := .of A)).obj G)
    ((moduleSpecΓFunctor (R := .of A)).obj P.F') f map
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    (regular_globalSections_injective P)
    (ambient_refinement_cokernel_finiteLength A a ha)
  let eG := closedFibreQuotientIso A f G
  let eP := closedFibreQuotientIso A f P.F'
  let quotientMap := scalarQuotMap f map
  have hnat : reduced ≫ eP.hom = eG.hom ≫ ModuleCat.ofHom quotientMap :=
    closedFibreQuotientIso_naturality A f a
  have hnat' : ModuleCat.ofHom quotientMap ≫ eP.inv = eG.inv ≫ reduced := by
    apply (cancel_epi eG.hom).mp
    calc
      eG.hom ≫ ModuleCat.ofHom quotientMap ≫ eP.inv =
          reduced ≫ eP.hom ≫ eP.inv := by rw [← Category.assoc, ← hnat, Category.assoc]
      _ = reduced := by simp
      _ = eG.hom ≫ eG.inv ≫ reduced := by simp
  obtain ⟨hk', hc'⟩ := ModuleCat.isFiniteLength_kernel_cokernel_of_iso
    (ModuleCat.ofHom quotientMap) reduced eG.symm eP.symm hnat' hk hc
  refine ⟨hk', hc', ?_⟩
  rw [ModuleCat.lengthIndex_eq_of_iso reduced (ModuleCat.ofHom quotientMap) eG eP hnat]
  exact hz

/-- The index of the closed-fibre map of a prepared extension — the length of its cokernel
minus the length of its kernel — does not depend on the prepared extension chosen. This is
**Stacks Project, Tag 0F25** with the two lengths written out, the form the proof produces. -/
public theorem preparedExtension_lengthIndex_eq
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (T : CoherentTriple A f) (P Q : PreparedExtension A f T) :
    ((Module.length A (cokernel P.closedFibreMap).carrier).toNat : ℤ) -
        ((Module.length A (kernel P.closedFibreMap).carrier).toNat : ℤ) =
      ((Module.length A (cokernel Q.closedFibreMap).carrier).toNat : ℤ) -
        ((Module.length A (kernel Q.closedFibreMap).carrier).toNat : ℤ) := by
  obtain ⟨G, a, b, hG, hregG, ha, hb, hopen, hclosed⟩ :=
    exists_compatible_coherent_refinement A f T P Q
  have : G.IsCoherent := hG
  let reducedA := (closedFibreSectionsFunctor A f).map a
  let reducedB := (closedFibreSectionsFunctor A f).map b
  obtain ⟨hka, hca, hia⟩ :=
    closedFibre_refinement_index_and_finiteLength A f hf T P G a hregG ha
  obtain ⟨hkb, hcb, hib⟩ :=
    closedFibre_refinement_index_and_finiteLength A f hf T Q G b hregG hb
  have hcomm : P.closedFibreMap.hom.comp reducedA.hom =
      Q.closedFibreMap.hom.comp reducedB.hom := by
    have heq := congrArg (fun morphism => (closedFibreGammaFunctor A f).map morphism) hclosed
    simp only [Functor.map_comp] at heq
    change reducedA ≫ P.closedFibreMap = reducedB ≫ Q.closedFibreMap at heq
    exact congrArg ModuleCat.Hom.hom heq
  have hfin (R : PreparedExtension A f T) : _ ∧ _ :=
    ⟨ModuleCat.isFiniteLength_of_iso (ModuleCat.kernelIsoKer R.closedFibreMap)
      (kernel_finiteLength A f T R),
      ModuleCat.isFiniteLength_of_iso (ModuleCat.cokernelIsoRangeQuotient R.closedFibreMap)
        (cokernel_finiteLength A f T R)⟩
  obtain ⟨hku, hcu⟩ := hfin P
  obtain ⟨hkv, hcv⟩ := hfin Q
  obtain ⟨hkcomp, hccomp⟩ := Module.finiteLength_kernel_cokernel_comp
    reducedA.hom P.closedFibreMap.hom hka hca hku hcu
  obtain ⟨hkcomp', hccomp'⟩ := Module.finiteLength_kernel_cokernel_comp
    reducedB.hom Q.closedFibreMap.hom hkb hcb hkv hcv
  have hindex := Module.lengthIndex_eq_of_common_refinement A reducedA.hom reducedB.hom
    P.closedFibreMap.hom Q.closedFibreMap.hom hcomm hka hca hkb hcb hku hkv
    hkcomp hccomp hkcomp' hccomp' (hia.trans hib.symm)
  simp only [ModuleCat.length_eq_of_iso (ModuleCat.kernelIsoKer _),
    ModuleCat.length_eq_of_iso (ModuleCat.cokernelIsoRangeQuotient _)]
  exact hindex

/-- The Euler characteristic of a prepared extension of a coherent triple: the length of the
cokernel of its closed-fibre map minus the length of its kernel. Both lengths are finite, by
`Stacks.Algebraization.cokernel_finiteLength` and `Stacks.Algebraization.kernel_finiteLength`.
This is the quantity whose independence of the prepared extension is **Stacks Project,
Tag 0F25**. -/
public noncomputable def PreparedExtension.eulerCharacteristic
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T : CoherentTriple A f} (P : PreparedExtension A f T) : ℤ :=
  ((Module.length A (cokernel P.closedFibreMap).carrier).toNat : ℤ) -
    ((Module.length A (kernel P.closedFibreMap).carrier).toNat : ℤ)

/-- **Stacks Project, Tag 0F25.** The Euler characteristic of a coherent triple does not depend
on the prepared extension used to compute it: any two prepared extensions of the same triple have
the same Euler characteristic. -/
@[stacks 0F25]
public theorem PreparedExtension.eulerCharacteristic_eq
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (T : CoherentTriple A f) (P Q : PreparedExtension A f T) :
    P.eulerCharacteristic = Q.eulerCharacteristic := by
  unfold PreparedExtension.eulerCharacteristic
  exact preparedExtension_lengthIndex_eq A f hf T P Q



/-! ### Exactness of global sections on an affine scheme -/

/-- **Global sections on an affine scheme are exact on quasi-coherent modules.** A short exact
sequence of quasi-coherent modules on `Spec R` has short exact global sections. -/
private theorem specSections_shortExact {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules)
    [hq₁ : S.X₁.IsQuasicoherent] [hq₂ : S.X₂.IsQuasicoherent] [hq₃ : S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have h₁ : IsIso S.X₁.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).1 hq₁
  have h₂ : IsIso S.X₂.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).1 hq₂
  have h₃ : IsIso S.X₃.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).1 hq₃
  have hlim := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have hcolim := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  have e : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ≅ S :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ h₁) (@asIso _ _ _ _ _ h₂) (@asIso _ _ _ _ _ h₃)
      ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.f).symm
      ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.g).symm
  have hmap : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    (ShortComplex.shortExact_iff_of_iso e).mpr hS
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ((S.map (moduleSpecΓFunctor (R := R))).exact_map_iff_of_faithful
      (tilde.functor R)).mp hmap.exact
  · exact (tilde.functor R).mono_of_mono_map hmap.mono_f
  · exact (tilde.functor R).epi_of_epi_map hmap.epi_g


/-! ### Reduction of a short exact sequence modulo a scalar -/

/-- Membership in the submodule spanned by a scalar is divisibility by that scalar. -/
private theorem mem_scalarSmulTop {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] (r : A) (x : M) :
    x ∈ Ideal.span {r} • (⊤ : Submodule A M) ↔ ∃ y : M, r • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩⟩

/-- **Reduction modulo a scalar keeps a short exact sequence left exact** when the scalar acts
regularly on the third term: the first reduced map stays injective. -/
private theorem scalarQuotMap_injective {A : Type u} [CommRing A] {M N P : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (r : A) (g : M →ₗ[A] N) (h : N →ₗ[A] P)
    (hg : Function.Injective g) (hgh : Function.Exact g h)
    (hreg : IsSMulRegular P r) : Function.Injective (scalarQuotMap r g) := by
  rw [← LinearMap.ker_eq_bot]
  refine le_antisymm (fun z hz => ?_) bot_le
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {r} • (⊤ : Submodule A M)) z
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hx : g x ∈ Ideal.span {r} • (⊤ : Submodule A N) := by
    have hz' := LinearMap.mem_ker.mp hz
    rw [Submodule.mkQ_apply, scalarQuotMap_mk, Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  obtain ⟨n, hn⟩ := (mem_scalarSmulTop r (g x)).mp hx
  have hhn : h n = 0 := hreg (by
    simp only [smul_zero]
    rw [← map_smul, hn, hgh.apply_apply_eq_zero x])
  obtain ⟨m, hm⟩ := (hgh n).mp hhn
  refine (mem_scalarSmulTop r x).mpr ⟨m, hg ?_⟩
  rw [map_smul, hm, hn]

/-- Reduction modulo a scalar keeps the second map of a short exact sequence surjective. -/
private theorem scalarQuotMap_surjective {A : Type u} [CommRing A] {N P : Type u}
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (r : A) (h : N →ₗ[A] P) (hh : Function.Surjective h) :
    Function.Surjective (scalarQuotMap r h) := fun z => by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {r} • (⊤ : Submodule A P)) z
  obtain ⟨n, rfl⟩ := hh x
  exact ⟨Submodule.Quotient.mk n, rfl⟩

/-- Reduction modulo a scalar keeps a short exact sequence exact in the middle. -/
private theorem scalarQuotMap_exact {A : Type u} [CommRing A] {M N P : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (r : A) (g : M →ₗ[A] N) (h : N →ₗ[A] P) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) :
    Function.Exact (scalarQuotMap r g) (scalarQuotMap r h) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {r} • (⊤ : Submodule A N)) z
    have hn : h n ∈ Ideal.span {r} • (⊤ : Submodule A P) := by
      have hz' := LinearMap.mem_ker.mp hz
      rw [Submodule.mkQ_apply, scalarQuotMap_mk, Submodule.Quotient.mk_eq_zero] at hz'
      exact hz'
    obtain ⟨p, hp⟩ := (mem_scalarSmulTop r (h n)).mp hn
    obtain ⟨n₀, hn₀⟩ := hh p
    obtain ⟨m, hm⟩ := (hgh (n - r • n₀)).mp (by
      rw [map_sub, map_smul, hn₀, hp, sub_self])
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    rw [Submodule.mkQ_apply, scalarQuotMap_mk]
    refine (Submodule.Quotient.eq _).mpr ((mem_scalarSmulTop r _).mpr ⟨-n₀, ?_⟩)
    rw [hm, smul_neg]
    abel
  · rw [LinearMap.range_le_ker_iff]
    refine LinearMap.ext fun z => ?_
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {r} • (⊤ : Submodule A M)) z
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, scalarQuotMap_mk, scalarQuotMap_mk,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, hgh.apply_apply_eq_zero m]
    exact Submodule.zero_mem _

/-- Global sections on the closed fibre are an additive functor. -/
private instance additive_moduleSpecΓFunctor_quot (A : Type u) [CommRing A] (f : A) :
    (moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).Additive :=
  ⟨by intro M N φ ψ; ext x; rfl⟩

/-- Restriction of scalars along the quotient map is additive. -/
private instance additive_restrictScalarsQuot (A : Type u) [CommRing A] (f : A) :
    (restrictScalarsQuot A f).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩

/-- Global sections on the closed fibre, as `A`-modules, is an additive functor. -/
instance additive_closedFibreGammaFunctor (A : Type u) [CommRing A] (f : A) :
    (closedFibreGammaFunctor A f).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩

/-- Pullback along the closed immersion is additive. -/
private instance additive_pullback_closedImmersion (A : Type u) [CommRing A] (f : A) :
    (Scheme.Modules.pullback (closedImmersion A f)).Additive := by
  have : (Scheme.Modules.pullback (closedImmersion A f)).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (closedImmersion A f)).isLeftAdjoint
  exact additive_of_isLeftAdjoint _

/-- Reduction to the closed fibre, taken on global sections, is an additive functor. -/
instance additive_closedFibreSectionsFunctor (A : Type u) [CommRing A] (f : A) :
    (closedFibreSectionsFunctor A f).Additive where
  map_add := by
    intro M N φ ψ
    change (restrictScalarsQuot A f).map
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).map
          ((Scheme.Modules.pullback (closedImmersion A f)).map (φ + ψ))) = _
    rw [Functor.map_add (F := Scheme.Modules.pullback (closedImmersion A f)),
      Functor.map_add (F := moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))),
      Functor.map_add (F := restrictScalarsQuot A f)]
    rfl

/-- A short complex of modules is short exact when its maps are injective, exact and surjective. -/
private theorem shortExact_of_function {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)}
    (hinj : Function.Injective S.f.hom) (hex : Function.Exact S.f.hom S.g.hom)
    (hsurj : Function.Surjective S.g.hom) : S.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex
  mono_f := (ModuleCat.mono_iff_injective _).mpr hinj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr hsurj

/-- A short exact sequence of modules has injective, exact and surjective maps. -/
private theorem function_of_shortExact {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) : Function.Injective S.f.hom ∧ Function.Exact S.f.hom S.g.hom ∧
      Function.Surjective S.g.hom :=
  ⟨(ModuleCat.mono_iff_injective _).mp hS.mono_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact,
    (ModuleCat.epi_iff_surjective _).mp hS.epi_g⟩

/-- **Reduction to the closed fibre keeps a short exact sequence short exact** when `f` acts
regularly on the global sections of the third term. -/
theorem closedFibreSections_shortExact
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (SC : ShortComplex (baseScheme A).Modules)
    [SC.X₁.IsQuasicoherent] [SC.X₂.IsQuasicoherent] [SC.X₃.IsQuasicoherent]
    (hSC : SC.ShortExact)
    (hreg : IsSMulRegular ((moduleSpecΓFunctor (R := .of A)).obj SC.X₃) f) :
    (SC.map (closedFibreSectionsFunctor A f)).ShortExact := by
  obtain ⟨hinj, hex, hsurj⟩ := function_of_shortExact (specSections_shortExact SC hSC)
  have hSQSE : (ShortComplex.mk
      (ModuleCat.ofHom (scalarQuotMap f ((moduleSpecΓFunctor (R := .of A)).map SC.f).hom))
      (ModuleCat.ofHom (scalarQuotMap f ((moduleSpecΓFunctor (R := .of A)).map SC.g).hom))
      (by
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
        refine LinearMap.ext fun z => ?_
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
          (Ideal.span {f} • (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj SC.X₁))) z
        rw [LinearMap.comp_apply, Submodule.mkQ_apply, scalarQuotMap_mk, scalarQuotMap_mk,
          LinearMap.zero_apply]
        exact (congrArg _ (hex.apply_apply_eq_zero m)).trans
          (Submodule.Quotient.mk_zero _))).ShortExact :=
    shortExact_of_function (scalarQuotMap_injective f _ _ hinj hex hreg)
      (scalarQuotMap_exact f _ _ hex hsurj) (scalarQuotMap_surjective f _ hsurj)
  refine (ShortComplex.shortExact_iff_of_iso ?_).mpr hSQSE
  exact ShortComplex.isoMk (closedFibreQuotientIso A f SC.X₁)
    (closedFibreQuotientIso A f SC.X₂) (closedFibreQuotientIso A f SC.X₃)
    (closedFibreQuotientIso_naturality A f SC.f).symm
    (closedFibreQuotientIso_naturality A f SC.g).symm

/-- **Global sections on the closed fibre keep a short exact sequence short exact.** -/
theorem closedFibreGamma_shortExact
    (A : Type u) [CommRing A] (f : A)
    (SC : ShortComplex (closedFibre A f).Modules)
    [SC.X₁.IsQuasicoherent] [SC.X₂.IsQuasicoherent] [SC.X₃.IsQuasicoherent]
    (hSC : SC.ShortExact) :
    (SC.map (closedFibreGammaFunctor A f)).ShortExact := by
  obtain ⟨hinj, hex, hsurj⟩ := function_of_shortExact (specSections_shortExact SC hSC)
  exact shortExact_of_function hinj hex hsurj

end Stacks.Algebraization

end
