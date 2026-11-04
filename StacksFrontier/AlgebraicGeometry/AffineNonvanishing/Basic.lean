module

public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# An affine open meets a nonvanishing locus in an affine open

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s ∈ Γ(X, L)`. For every affine open
`U ⊆ X` the intersection `U ∩ X_s` is affine ([Stacks, Tag 01PV]).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`: for an invertible module
  `L` on a scheme `X` and `s ∈ Γ(X, L)`, the intersection of an affine open with `X_s` is affine.

## References

* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpStalk grpGerm stalkMapL)

universe u

namespace Stacks.SheafOfModules

/-- A morphism of sheaves of modules can only shrink the nonvanishing locus: the image of a
global section vanishes wherever the section does. -/
theorem nonvanishingLocus_sectionsMap_subset {X : RingedSpace.{u, u}}
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    {L M : SheafOfModules.{u} (structureSheafRing X)} (φ : L ⟶ M) (s : L.sections) :
    nonvanishingLocus M (SheafOfModules.sectionsMap φ s) ⊆ nonvanishingLocus L s := by
  intro x hx
  by_contra hs
  refine hx ?_
  have hmem : stalkMapL X L.val M.val φ.val x
      (grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))) ∈
      IsLocalRing.maximalIdeal (ringStalk X x) •
        (⊤ : Submodule (ringStalk X x) (grpStalk X M.val x)) :=
    map_mem_smul_top _ (stalkMapL X L.val M.val φ.val x) (not_not.mp hs)
  rwa [stalkMapL_germ X φ.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))] at hmem

/-- A finite projective module has a finite dual basis: elements `v i` and functionals `φ i`
with `∑ φ i p • v i = p` for every `p`. -/
theorem exists_finite_dualBasis {R : Type u} [CommRing R] {P : Type u}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    ∃ n : ℕ, ∃ v : Fin n → P, ∃ φ : Fin n → P →ₗ[R] R,
      ∀ p : P, ∑ i, φ i p • v i = p := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  let b := Pi.basisFun R (Fin n)
  refine ⟨n, fun i => f (b i), fun i => (LinearMap.proj i).comp g, fun p => ?_⟩
  calc
    ∑ i, ((LinearMap.proj i).comp g) p • f (b i) = f (∑ i, (g p i) • b i) := by
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_smul]
    _ = f (g p) := by
      refine congrArg f ?_
      simpa [b, Pi.basisFun_repr] using b.sum_repr (g p)
    _ = p := by
      simpa [LinearMap.comp_apply] using congrArg (fun k : P →ₗ[R] P => k p) hfg

/-- The dual basis of `Stacks.SheafOfModules.exists_finite_dualBasis` with the functionals read
as morphisms in `ModuleCat R`. -/
theorem exists_finite_dualBasis_moduleCat {R : Type u} [CommRing R] (P : ModuleCat.{u} R)
    [Module.Finite R P] [Module.Projective R P] :
    ∃ n : ℕ, ∃ v : Fin n → P, ∃ φ : Fin n → (P ⟶ ModuleCat.of R R),
      ∀ p : P, ∑ i, (φ i).hom p • v i = p := by
  obtain ⟨n, v, φ, hφ⟩ := exists_finite_dualBasis (R := R) (P := P)
  exact ⟨n, v, fun i => ModuleCat.ofHom (φ i), fun p => by simpa using hφ p⟩

/-- The global sections of an invertible module on an affine spectrum form a finite projective
module. -/
theorem finite_and_projective_moduleSpecΓ (R : Type u) [CommRing R]
    (L : (Spec (CommRingCat.of R)).Modules)
    [IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L] :
    Module.Finite R (moduleSpecΓFunctor.obj L) ∧
      Module.Projective R (moduleSpecΓFunctor.obj L) := by
  have := Scheme.isQuasicoherent_of_isInvertible _ L
  have hiso : IsIso L.fromTildeΓ := inferInstance
  let e : tilde (R := CommRingCat.of R) (ModuleCat.of R (moduleSpecΓFunctor.obj L)) ≅ L :=
    @asIso _ _ _ _ L.fromTildeΓ hiso
  have hL := (Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one _ L).1 ‹_›
  have hpt : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank
      (tilde (R := CommRingCat.of R) (ModuleCat.of R (moduleSpecΓFunctor.obj L))) 1 := by
    intro x
    obtain ⟨U, hxU, ⟨ψ⟩⟩ :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules L 1 hL x
    exact ⟨U, hxU, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ ψ⟩⟩
  obtain ⟨ι, g, hspan, hb⟩ :=
    (tilde_isFiniteLocallyFreeOfRank_iff R (moduleSpecΓFunctor.obj L) 1).mp hpt
  exact Module.finite_and_projective_of_isFiniteLocallyFree
    ⟨ι, g, hspan, fun i => ⟨Module.Free.of_basis (hb i).some,
      Module.Finite.of_basis (hb i).some⟩⟩

section SpecMorphisms

variable {R : Type u} [CommRing R]

/-- A functional on the module of global sections of a quasi-coherent module `M` on `Spec R`,
read as a morphism `M ⟶ 𝒪` of sheaves of modules through the identification
`e : Γ(M)^~ ≅ M`. -/
noncomputable def ofModuleCatMap (M : (Spec (CommRingCat.of R)).Modules)
    (e : tilde (R := CommRingCat.of R) (moduleSpecΓFunctor.obj M) ≅ M)
    (f : moduleSpecΓFunctor.obj M ⟶ ModuleCat.of R R) :
    M ⟶ SheafOfModules.unit
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace) :=
  e.inv ≫ AlgebraicGeometry.tilde.map f

/-- On global sections, `Stacks.SheafOfModules.ofModuleCatMap` is the functional it came from,
followed by the unit of `(·)^~ ⊣ Γ`. -/
theorem moduleSpecΓFunctor_map_ofModuleCatMap (M : (Spec (CommRingCat.of R)).Modules)
    (e : tilde (R := CommRingCat.of R) (moduleSpecΓFunctor.obj M) ≅ M)
    (f : moduleSpecΓFunctor.obj M ⟶ ModuleCat.of R R) (he : e.hom = M.fromTildeΓ) :
    moduleSpecΓFunctor.map (ofModuleCatMap M e f) =
      f ≫ (AlgebraicGeometry.tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app
        (ModuleCat.of (CommRingCat.of R) R) := by
  dsimp [ofModuleCatMap]
  rw (transparency := .default) [Functor.map_comp]
  have hη : moduleSpecΓFunctor.map e.inv =
      (AlgebraicGeometry.tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app
        (moduleSpecΓFunctor.obj M) := by
    refine (cancel_mono (moduleSpecΓFunctor.map e.hom)).1 ?_
    calc
      moduleSpecΓFunctor.map e.inv ≫ moduleSpecΓFunctor.map e.hom = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.inv_hom_id]
        simp
      _ = (AlgebraicGeometry.tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app
            (moduleSpecΓFunctor.obj M) ≫ moduleSpecΓFunctor.map e.hom := by
        rw [he]
        exact (AlgebraicGeometry.tilde.adjunction.right_triangle_components M).symm
  rw [hη]
  have hn := (AlgebraicGeometry.tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.naturality f
  exact hn.symm

/-- The global value of the image of a global section under a morphism of sheaves of modules on
an affine scheme is the image under the induced map of modules of global sections. -/
theorem sectionsMap_eval_top {M N : (Spec (CommRingCat.of R)).Modules} (φ : M ⟶ N)
    (s : M.sections) :
    (SheafOfModules.sectionsMap φ s).eval (op ⊤) =
      (moduleSpecΓFunctor.map φ).hom (s.eval (op ⊤)) := rfl

/-- The global value of the section `Stacks.SheafOfModules.ofModuleCatMap` produces: it is the
value of the functional on the global section, read in `Γ(Spec R, 𝒪)` through
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem sectionsMap_ofModuleCatMap_eval_top (M : (Spec (CommRingCat.of R)).Modules)
    (e : tilde (R := CommRingCat.of R) (moduleSpecΓFunctor.obj M) ≅ M)
    (f : moduleSpecΓFunctor.obj M ⟶ ModuleCat.of R R)
    (s : M.sections) (he : e.hom = M.fromTildeΓ) :
    (SheafOfModules.sectionsMap (ofModuleCatMap M e f) s).eval (op ⊤) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (f.hom (s.eval (op ⊤))) := by
  rw (transparency := .default)
    [sectionsMap_eval_top, moduleSpecΓFunctor_map_ofModuleCatMap M e f he]
  rfl

/-- The basic open of the value of a functional on a global section `s` is contained in the
nonvanishing locus of `s`. -/
theorem basicOpen_le_nonvanishingOpen_of_moduleCatMap
    (L : (Spec (CommRingCat.of R)).Modules)
    [IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L]
    (s : L.sections) (f : moduleSpecΓFunctor.obj L ⟶ ModuleCat.of R R) :
    ((Spec (CommRingCat.of R)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (f.hom (s.eval (op ⊤)))) : Set _) ≤
      nonvanishingLocus (X := (Spec (CommRingCat.of R)).toRingedSpace) L s := by
  have := Scheme.isQuasicoherent_of_isInvertible _ L
  have hiso : IsIso L.fromTildeΓ := inferInstance
  let e : tilde (R := CommRingCat.of R) (moduleSpecΓFunctor.obj L) ≅ L :=
    @asIso _ _ _ _ L.fromTildeΓ hiso
  have ha := sectionsMap_ofModuleCatMap_eval_top L e f s rfl
  refine le_trans (le_of_eq ?_)
    (nonvanishingLocus_sectionsMap_subset (ofModuleCatMap L e f) s)
  rw [← ha]
  exact (nonvanishingLocus_unit_eq_basicOpen (Spec (CommRingCat.of R)).toRingedSpace
    (SheafOfModules.sectionsMap (ofModuleCatMap L e f) s)).symm

/-- For a global section `s` of an invertible module on `Spec R` there are finitely many
`r i ∈ Γ(Spec R, ⊤)` whose restrictions to the nonvanishing locus `X_s` generate the unit ideal
and whose basic opens lie in `X_s`. -/
theorem exists_spanning_coefficients_of_nonvanishingOpen
    (L : (Spec (CommRingCat.of R)).Modules)
    [IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L]
    (s : L.sections) :
    ∃ (n : ℕ) (r : Fin n → Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))),
      Ideal.span (Set.range fun i => (Spec (CommRingCat.of R)).presheaf.map
          (Opens.leTop (nonvanishingOpen
            (X := (Spec (CommRingCat.of R)).toRingedSpace) L s)).op (r i)) = ⊤ ∧
        ∀ i, (Spec (CommRingCat.of R)).basicOpen (r i) ≤
          nonvanishingOpen (X := (Spec (CommRingCat.of R)).toRingedSpace) L s := by
  classical
  obtain ⟨hfin, hproj⟩ := finite_and_projective_moduleSpecΓ R L
  obtain ⟨n, v, φ, hdual⟩ := exists_finite_dualBasis_moduleCat (moduleSpecΓFunctor.obj L)
  set V := nonvanishingOpen (X := (Spec (CommRingCat.of R)).toRingedSpace) L s with hVdef
  set p : Γ(L, (⊤ : (Spec (CommRingCat.of R)).Opens)) := s.eval (op ⊤) with hpdef
  set t : Γ(L, V) := s.eval (op V) with htdef
  set w : Fin n → Γ(L, (⊤ : (Spec (CommRingCat.of R)).Opens)) := fun i => v i with hwdef
  set r : Fin n → Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ((φ i).hom p) with hrdef
  have hsmul : ∀ i, (φ i).hom p • v i = r i • w i := by
    intro i
    refine (Scheme.Modules.smul_Spec_def ((φ i).hom p) (w i)).trans ?_
    refine congrArg (fun c => c • w i) ?_
    rw [show (Opens.leTop (⊤ : (Spec (CommRingCat.of R)).Opens)).op =
        𝟙 (op (⊤ : (Spec (CommRingCat.of R)).Opens)) from Subsingleton.elim _ _]
    simp [hrdef]
  have htop : ∑ i, r i • w i = p :=
    (Finset.sum_congr rfl fun i _ => (hsmul i).symm).trans (hdual p)
  have hrelV : ∑ i, (Spec (CommRingCat.of R)).presheaf.map V.leTop.op (r i) •
      L.presheaf.map V.leTop.op (w i) = t := by
    calc
      _ = L.presheaf.map V.leTop.op (∑ i, r i • w i) := by
        rw [map_sum]
        exact (Finset.sum_congr rfl fun i _ =>
          Scheme.Modules.map_smul L V.leTop (r i) (w i)).symm
      _ = L.presheaf.map V.leTop.op p := congrArg _ htop
      _ = t := L.val.sections_property s V.leTop.op
  have hbij : Function.Bijective
      (fun c : Γ(Spec (CommRingCat.of R), V) => c • t) :=
    bijective_smul_eval_of_le_nonvanishingOpen
      (X := (Spec (CommRingCat.of R)).toRingedSpace) L s V le_rfl
  have hex : ∀ i, ∃ c : Γ(Spec (CommRingCat.of R), V),
      c • t = L.presheaf.map V.leTop.op (w i) := fun i => hbij.2 _
  choose c hc using hex
  have hone : (∑ i, (Spec (CommRingCat.of R)).presheaf.map V.leTop.op (r i) * c i) • t =
      (1 : Γ(Spec (CommRingCat.of R), V)) • t := by
    rw [one_smul, Finset.sum_smul]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hrelV
    rw [mul_smul, hc i]
  have hspan : ∑ i, (Spec (CommRingCat.of R)).presheaf.map V.leTop.op (r i) * c i = 1 :=
    hbij.1 hone
  refine ⟨n, r, ?_, fun i => ?_⟩
  · refine (Ideal.eq_top_iff_one _).2 ?_
    rw [← hspan]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right (c i) _ ?_
    exact Ideal.subset_span ⟨i, rfl⟩
  · exact basicOpen_le_nonvanishingOpen_of_moduleCatMap L s (φ i)

/-- The nonvanishing locus of a global section of an invertible module on `Spec R` is affine. -/
theorem isAffineOpen_nonvanishingOpen_spec (L : (Spec (CommRingCat.of R)).Modules)
    [IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L]
    (s : L.sections) :
    IsAffineOpen (nonvanishingOpen (X := (Spec (CommRingCat.of R)).toRingedSpace) L s) := by
  obtain ⟨n, r, hspan, hle⟩ := exists_spanning_coefficients_of_nonvanishingOpen L s
  refine AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen
    (nonvanishingOpen (X := (Spec (CommRingCat.of R)).toRingedSpace) L s)
    (Set.range fun i => (Spec (CommRingCat.of R)).presheaf.map
      (Opens.leTop (nonvanishingOpen
        (X := (Spec (CommRingCat.of R)).toRingedSpace) L s)).op (r i)) hspan ?_
  rintro _ ⟨i, rfl⟩
  rw [Scheme.basicOpen_res, inf_eq_right.mpr (hle i)]
  exact (isAffineOpen_top (Spec (CommRingCat.of R))).basicOpen (r i)

end SpecMorphisms

section Transport

open RingedSpaceModuleAdjunction

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
private instance isInvertible_modulePullback_scheme {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] :
    IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      ((modulePullback f.toLRSHom.toShHom).obj L) :=
  @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
    f.toLRSHom.toShHom L hL

/-- For a morphism of schemes, the nonvanishing locus of a pulled-back section of the pulled-back
invertible module is the preimage of the nonvanishing locus. -/
@[ega "II 4.6.13.1"]
theorem preimage_nonvanishingOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]
    (s : L.sections) :
    letI : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
        ((modulePullback f.toLRSHom.toShHom).obj L) :=
      @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
        f.toLRSHom.toShHom L hL
    f ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s =
      nonvanishingOpen (X := X.toRingedSpace)
        ((modulePullback f.toLRSHom.toShHom).obj L)
        (modulePullbackSection f.toLRSHom L s) :=
  TopologicalSpace.Opens.ext (preimage_nonvanishingLocus f.toLRSHom L s)

/-- The nonvanishing locus of a global section of an invertible module on an affine scheme is
affine. -/
theorem isAffineOpen_nonvanishingOpen_of_isAffine (Y : Scheme.{u}) [IsAffine Y]
    (L : Y.Modules)
    [hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]
    (s : L.sections) :
    IsAffineOpen (nonvanishingOpen (X := Y.toRingedSpace) L s) := by
  set e : Y ≅ Spec (CommRingCat.of
    (Y.presheaf.obj (op (⊤ : Y.Opens)) : Type u)) := Y.isoSpec with hedef
  have hS := isAffineOpen_nonvanishingOpen_spec
    ((modulePullback e.inv.toLRSHom.toShHom).obj L) (modulePullbackSection e.inv.toLRSHom L s)
  have hpre := preimage_nonvanishingOpen e.inv L s
  have hEq : e.hom ⁻¹ᵁ nonvanishingOpen
      (X := (Spec (CommRingCat.of (Y.presheaf.obj (op (⊤ : Y.Opens)) : Type u))).toRingedSpace)
      ((modulePullback e.inv.toLRSHom.toShHom).obj L)
      (modulePullbackSection e.inv.toLRSHom L s) =
      nonvanishingOpen (X := Y.toRingedSpace) L s := by
    rw [← hpre, ← Scheme.Hom.comp_preimage]
    simp
  exact hEq ▸ hS.preimage e.hom

end Transport

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules RingedSpaceModuleAdjunction

/-- For an invertible module `L` on a scheme `X` and a global section `s` of `L`, every affine
open `U ⊆ X` meets the nonvanishing locus `X_s` in an affine open. -/
@[stacks 01PV, ega "II 5.5.8", sga "6 II 2.2.3.1"]
public theorem isAffineOpen_inf_nonvanishingOpen {X : Scheme.{u}} (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (U ⊓ nonvanishingOpen (X := X.toRingedSpace) L s) := by
  have : IsAffine U.toScheme := hU
  have hAff := isAffineOpen_nonvanishingOpen_of_isAffine U.toScheme
    ((modulePullback U.ι.toLRSHom.toShHom).obj L) (modulePullbackSection U.ι.toLRSHom L s)
  have hpre := preimage_nonvanishingOpen U.ι L s
  have hImage : IsAffineOpen
      (U.ι ''ᵁ (U.ι ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace) L s)) :=
    (U.ι.isAffineOpen_iff_of_isOpenImmersion).2 (by rw [hpre]; exact hAff)
  simpa only [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using hImage

end AlgebraicGeometry.Scheme.Modules

end
