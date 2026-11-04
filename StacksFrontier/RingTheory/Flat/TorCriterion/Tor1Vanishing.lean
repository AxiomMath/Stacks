module

public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Flatness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of `Tor₁` for modules annihilated by an ideal

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` an `R`-module such that `M/IM` is flat over
`R/I` and `Tor₁^R(R/I, M) = 0`. Then `Tor₁^R(N, M) = 0` for every `R`-module `N` annihilated by
`I`; this is the first step towards the flatness criteria of
`StacksFrontier.RingTheory.Flat.TorCriterion.NilpotentIdeal`.

## Main definitions

* `Tor1Vanishes`: the vanishing of `Tor₁^R(N, M)`, for the `Tor` bifunctor of `ModuleCat R`.

## Main results

* `tor1_vanishes_of_submodule`: `Tor₁` vanishes on `N` if it vanishes on `P` and on `N ⧸ P`.
* `tor1_vanishes_of_smul_eq_bot`: `Tor₁^R(N, M) = 0` for every `N` annihilated by `I`.

## Implementation notes

`Tor1Vanishes R N M` resolves the second variable, as `CategoryTheory.Tor` does.

## References

* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

/-- `Tor₁^R(N, M) = 0`, expressed via the categorical `Tor` bifunctor on
`ModuleCat R`: the degree-`1` Tor object is a zero object. -/
abbrev Tor1Vanishes (R : Type u) [CommRing R] (N M : Type u)
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] : Prop :=
  Limits.IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))

/-! ## Vanishing of `Tor₁` on zero modules and along submodules -/

section TorPrimitives

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]



namespace Tor1VanishesAux

/-- The short complex `0 → P → N → N⧸P → 0` in `ModuleCat R`. -/
noncomputable def shortCx {N : Type u} [AddCommGroup N] [Module R N] (P : Submodule R N) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom P.subtype) (ModuleCat.ofHom P.mkQ) (by ext x; simp)

/-- The morphism `(tensoringRight Y).map (ofHom φ)` is `LinearMap.rTensor Y φ`. -/
theorem mapped_hom {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (φ : A →ₗ[R] B) (Y : ModuleCat.{u} R) :
    ConcreteCategory.hom (((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj Y).map
        (ModuleCat.ofHom φ))
      = LinearMap.rTensor Y φ := by
  apply TensorProduct.ext'
  intro a y
  rw [show ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj Y).map (ModuleCat.ofHom φ)
        = MonoidalCategoryStruct.whiskerRight (ModuleCat.ofHom φ) Y from rfl,
      ModuleCat.MonoidalCategory.whiskerRight_def]
  simp

/-- Tensoring the short exact sequence `0 → P → N → N⧸P → 0` with a flat module `Y`
keeps it short exact. -/
@[ega "0 6.1.1" "partial",
  ega "III 6.1.1" "special case",
  sga "3 VIIB 0.3.7" "special case",
  sga "3 VIIB 0.3.8" "Forward implication",
  sga "7 VII 3.7.6" "partial"]
theorem mapShortCx_shortExact {N : Type u} [AddCommGroup N] [Module R N] (P : Submodule R N)
    (Y : ModuleCat.{u} R) [Module.Flat R Y] :
    ((shortCx P).map ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj Y)).ShortExact := by
  have hexact : Function.Exact ⇑P.subtype ⇑P.mkQ := by
    rw [LinearMap.exact_iff]; simp [Submodule.ker_mkQ, Submodule.range_subtype]
  have hrt := Module.Flat.rTensor_exact Y hexact
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    simp only [shortCx,
      ShortComplex.map_g, ShortComplex.map_f, mapped_hom] at hx ⊢
    exact (hrt x).mp hx
  · rw [ModuleCat.mono_iff_injective]
    simp only [shortCx, ShortComplex.map_f, mapped_hom]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.coe_injective
  · rw [ModuleCat.epi_iff_surjective]
    simp only [shortCx, ShortComplex.map_g, mapped_hom]
    exact LinearMap.rTensor_surjective Y (Submodule.mkQ_surjective P)

/-- The functor `X ↦ (X ⊗ -) applied levelwise to a fixed chain complex `Pr`. -/
noncomputable def torPhi (Pr : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :
    ModuleCat.{u} R ⥤ HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ) where
  obj X := (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj Pr
  map {X Y} f := (NatTrans.mapHomologicalComplex ((MonoidalCategory.tensoringLeft (ModuleCat.{u}
      R)).map f) (ComplexShape.down ℕ)).app Pr
  map_id X := by simp only [CategoryTheory.Functor.map_id]; ext n; simp
  map_comp {X Y Z} f g := by simp only [CategoryTheory.Functor.map_comp]; ext n; simp

/-- The functor `torPhi Pr` preserves zero morphisms. -/
instance torPhiPZM (Pr : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :
    (torPhi Pr).PreservesZeroMorphisms where
  map_zero X Y := by
    change (NatTrans.mapHomologicalComplex ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map
        (0 : X ⟶ Y)) (ComplexShape.down ℕ)).app Pr = 0
    rw [Functor.map_zero]; ext n; rfl

/-- The differentials of `torPhi Pr` at `X` are `LinearMap.lTensor X` of those of `Pr`. -/
private theorem torPhi_d_hom (Pr : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ))
    (X : ModuleCat.{u} R) (i j : ℕ) :
    ModuleCat.Hom.hom (((torPhi Pr).obj X).d i j)
      = LinearMap.lTensor X (ModuleCat.Hom.hom (Pr.d i j)) := by
  apply TensorProduct.ext'; intro s b; rfl

/-- For a projective resolution `Pr` of `M`, applying `torPhi Pr.complex` to the short exact
sequence `0 → P → N → N⧸P → 0` gives a short exact sequence of chain complexes. -/
theorem mappedSES_shortExact {N : Type u} [AddCommGroup N] [Module R N] (P : Submodule R N)
    (Pr : ProjectiveResolution (ModuleCat.of R M)) :
    ((shortCx P).map (torPhi Pr.complex)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have key : ((shortCx P).map (torPhi Pr.complex)).map (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.down ℕ) i)
      = (shortCx P).map ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj (Pr.complex.X i))
          := rfl
  rw [key]
  have : Module.Flat R (Pr.complex.X i) := inferInstance
  exact mapShortCx_shortExact P (Pr.complex.X i)

/-- An exact short complex in `ModuleCat R` whose outer two objects are zero has a
zero middle object. -/
theorem middle_zero (S : ShortComplex (ModuleCat.{u} R)) (h : S.Exact)
    (h1 : Limits.IsZero S.X₁) (h3 : Limits.IsZero S.X₃) : Limits.IsZero S.X₂ := by
  have hg : Mono S.g := h.mono_g (h1.eq_of_src _ _)
  rw [Limits.IsZero.iff_id_eq_zero]
  have h0 : S.g = 0 := h3.eq_of_tgt _ _
  rw [← cancel_mono S.g]; simp [h0]

/-- `Tor₁(X, M)` is isomorphic to the degree-`1` homology of `torPhi Pr` applied to `X`,
using a chosen projective resolution `Pr` of `M`. -/
noncomputable def torIsoHomology (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : Type u)
    [AddCommGroup X] [Module R X] :
    ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R X)).obj (ModuleCat.of R M)
      ≅ ((torPhi Pr.complex).obj (ModuleCat.of R X)).homology 1 :=
  (eqToIso (by rw [Tor_obj])).trans
    (Pr.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R
        X)) 1)

end Tor1VanishesAux

open Tor1VanishesAux in
/-- `Tor₁^R(N, M) = 0` when `N` is the zero module. -/
theorem tor1_isZero_of_subsingleton (N : Type u) [AddCommGroup N] [Module R N]
    [Subsingleton N] : Tor1Vanishes R N M := by
  let Pr : ProjectiveResolution (ModuleCat.of R M) := ProjectiveResolution.of (ModuleCat.of R M)
  refine Limits.IsZero.of_iso ?_ (torIsoHomology Pr N)
  have hsub : Subsingleton (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj
      (ModuleCat.of R N)).obj (Pr.complex.X 1)) := by
    show Subsingleton (TensorProduct R N (Pr.complex.X 1)); infer_instance
  have hX1 : Limits.IsZero (((torPhi Pr.complex).obj (ModuleCat.of R N)).X 1) :=
    @ModuleCat.isZero_of_subsingleton R _
      (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R N)).obj
          (Pr.complex.X 1))
      hsub
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX1

open Tor1VanishesAux in
/-- Two-out-of-three for `Tor₁` along a submodule `P ≤ N`: if `Tor₁^R(P, M) = 0` and
`Tor₁^R(N ⧸ P, M) = 0`, then `Tor₁^R(N, M) = 0`. -/
theorem tor1_vanishes_of_submodule (N : Type u) [AddCommGroup N] [Module R N]
    (P : Submodule R N)
    (hP : Tor1Vanishes R P M)
    (hQ : Tor1Vanishes R (N ⧸ P) M) :
    Tor1Vanishes R N M := by
  let Pr : ProjectiveResolution (ModuleCat.of R M) := ProjectiveResolution.of (ModuleCat.of R M)
  have hSE := mappedSES_shortExact P Pr
  have hexact := hSE.homology_exact₂ 1
  have h1 : Limits.IsZero (((shortCx P).map (torPhi Pr.complex)).X₁.homology 1) :=
    Limits.IsZero.of_iso hP (torIsoHomology Pr (P : Type u)).symm
  have h3 : Limits.IsZero (((shortCx P).map (torPhi Pr.complex)).X₃.homology 1) :=
    Limits.IsZero.of_iso hQ (torIsoHomology Pr (N ⧸ P)).symm
  have hmid : Limits.IsZero (((shortCx P).map (torPhi Pr.complex)).X₂.homology 1) :=
    middle_zero _ hexact h1 h3
  exact Limits.IsZero.of_iso hmid (torIsoHomology Pr N)

end TorPrimitives

/-! ## Modules annihilated by `I` -/

section ChangeOfRings

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]


open Tor1VanishesAux in
/-- `Tor₁` vanishes on a quotient by a submodule `P ≤ Fr` when `Tor₁^R(Fr, M) = 0` and, for
every projective resolution of `M`, the degree-`0` map induced on homology by `P ↪ Fr` after
tensoring the resolution is a monomorphism: then `Tor₁^R(Fr ⧸ P, M) = 0`. -/
theorem tor1_vanishes_of_quotient_rTensor_injective
    {Fr : Type u} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr)
    (hF : Tor1Vanishes R Fr M)
    (hmono : ∀ Pr : ProjectiveResolution (ModuleCat.of R M),
        Mono (HomologicalComplex.homologyMap ((shortCx P).map (torPhi Pr.complex)).f 0)) :
    Tor1Vanishes R (Fr ⧸ P) M := by
  let Pr : ProjectiveResolution (ModuleCat.of R M) := ProjectiveResolution.of (ModuleCat.of R M)
  set S := (shortCx P).map (torPhi Pr.complex) with hSdef
  have hS : S.ShortExact := mappedSES_shortExact P Pr
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down]
  have hX2 : Limits.IsZero (S.X₂.homology 1) :=
    Limits.IsZero.of_iso hF (torIsoHomology Pr Fr).symm
  have e3 := hS.homology_exact₃ 1 0 hrel
  have hg0 : HomologicalComplex.homologyMap S.g 1 = 0 := hX2.eq_of_src _ _
  have hδmono : Mono (hS.δ 1 0 hrel) := e3.mono_g hg0
  have hz : hS.δ 1 0 hrel ≫ HomologicalComplex.homologyMap S.f 0 = 0 := hS.δ_comp 1 0 hrel
  have hδ0 : hS.δ 1 0 hrel = 0 := by
    have := hmono Pr
    rw [← cancel_mono (HomologicalComplex.homologyMap S.f 0), Limits.zero_comp, hz]
  have hX3 : Limits.IsZero (S.X₃.homology 1) := by
    rw [Limits.IsZero.iff_id_eq_zero, ← cancel_mono (hS.δ 1 0 hrel)]
    simp [hδ0]
  exact Limits.IsZero.of_iso hX3 (torIsoHomology Pr (Fr ⧸ P))

namespace Tor1VanishesAux

open CategoryTheory.Limits TensorProduct

/-- The "augmentation" map at degree `0` of the tensored resolution:
`X ⊗ Pr.X 0 → X ⊗ M`, given by `lTensor X (Pr.π.f 0)`. -/
noncomputable def augX (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    ((torPhi Pr.complex).obj X).X 0 ⟶ ModuleCat.of R (X ⊗[R] M) :=
  ModuleCat.ofHom (LinearMap.lTensor X (ModuleCat.Hom.hom (Pr.π.f 0)))

set_option backward.isDefEq.respectTransparency false in
/-- Right-exactness of `X ⊗ –`: the tensored sequence
`X ⊗ Pr.X 1 → X ⊗ Pr.X 0 → X ⊗ M` is exact (the augmentation tensored). -/
theorem augX_exact (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    Function.Exact (ModuleCat.Hom.hom (((torPhi Pr.complex).obj X).d 1 0))
      (LinearMap.lTensor X (ModuleCat.Hom.hom (Pr.π.f 0))) := by
  have hex : Function.Exact (ModuleCat.Hom.hom (Pr.complex.d 1 0))
      (ModuleCat.Hom.hom (Pr.π.f 0)) := by
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp Pr.exact₀
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (Pr.π.f 0)) := by
    rw [← ModuleCat.epi_iff_surjective]; infer_instance
  have key := lTensor_exact X hex hsurj
  rw [torPhi_d_hom]; exact key

/-- The degree-`1` differential of `X ⊗ Pr` composed with the augmentation `augX Pr X` is zero,
so `augX Pr X` factors through the degree-`0` opcycles. -/
theorem augX_dcomp (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    ((torPhi Pr.complex).obj X).d 1 0 ≫ augX Pr X = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
  exact (augX_exact Pr X).apply_apply_eq_zero z

/-- The cokernel short complex `X ⊗ Pr.X 1 → X ⊗ Pr.X 0 → X ⊗ M`. -/
noncomputable def cokerSC (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (((torPhi Pr.complex).obj X).d 1 0) (augX Pr X) (augX_dcomp Pr X)

/-- The short complex `X ⊗ Pr.X 1 → X ⊗ Pr.X 0 → X ⊗ M` is exact at its middle object, which is
right-exactness of `X ⊗ –` applied to the augmentation of `Pr`. -/
theorem cokerSC_exact (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    (cokerSC Pr X).Exact := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (augX_exact Pr X)

/-- The augmentation `X ⊗ Pr.X 0 → X ⊗ M` is an epimorphism, since `Pr.π.f 0` is surjective and
`X ⊗ –` preserves surjections. -/
instance cokerSC_epi (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    Epi (cokerSC Pr X).g := by
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective (LinearMap.lTensor X (ModuleCat.Hom.hom (Pr.π.f 0)))
  apply LinearMap.lTensor_surjective; rw [← ModuleCat.epi_iff_surjective]; infer_instance

/-- In the chain-complex shape `ComplexShape.down ℕ`, the degree preceding `0` is `1`. -/
theorem cokerHprev : (ComplexShape.down ℕ).prev 0 = 1 :=
  (ComplexShape.down ℕ).prev_eq' (by simp [ComplexShape.down] : (ComplexShape.down ℕ).Rel 1 0)

/-- The isomorphism between the degree-`0` opcycles of `X ⊗ Pr` and `X ⊗ M`, both cokernels of
`X ⊗ d₁₀`. -/
noncomputable def cokerIso (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    ((torPhi Pr.complex).obj X).opcycles 0 ≅ ModuleCat.of R (X ⊗[R] M) :=
  IsColimit.coconePointUniqueUpToIso
    (((torPhi Pr.complex).obj X).opcyclesIsCokernel 1 0 cokerHprev)
    ((cokerSC_exact Pr X).gIsCokernel)

/-- The isomorphism `cokerIso Pr X` is the one compatible with the two cokernel
projections: `pOpcycles 0` followed by it is the augmentation `augX Pr X`. -/
theorem pOpcycles_cokerIso (Pr : ProjectiveResolution (ModuleCat.of R M)) (X : ModuleCat.{u} R) :
    ((torPhi Pr.complex).obj X).pOpcycles 0 ≫ (cokerIso Pr X).hom = augX Pr X := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (((torPhi Pr.complex).obj X).opcyclesIsCokernel 1 0 cokerHprev)
    ((cokerSC_exact Pr X).gIsCokernel) WalkingParallelPair.one
  simpa [cokerIso, cokerSC, CokernelCofork.π_ofπ] using h

/-- The naturality square identifying `opcyclesMap S.f 0` with `rTensor M P.subtype`,
computed at the level of the underlying maps `P ⊗ Pr.X 0 → Fr ⊗ M`. -/
theorem augX_naturality {Fr : Type u} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr)
    (Pr : ProjectiveResolution (ModuleCat.of R M)) :
    ((shortCx P).map (torPhi Pr.complex)).f.f 0 ≫ augX Pr (ModuleCat.of R Fr)
      = augX Pr (ModuleCat.of R P) ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p x
  rfl

end Tor1VanishesAux

set_option backward.isDefEq.respectTransparency false in
open Tor1VanishesAux in
/-- If `rTensor M P.subtype : P ⊗_R M → Fr ⊗_R M` is injective, then the map induced on degree-`0`
homology by `P ↪ Fr` after tensoring a projective resolution of `M` is a monomorphism. -/
theorem tor0_homologyMap_mono_of_rTensor_injective
    {Fr : Type u} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr)
    (hrt : Function.Injective (LinearMap.rTensor M P.subtype))
    (Pr : ProjectiveResolution (ModuleCat.of R M)) :
    Mono (HomologicalComplex.homologyMap ((shortCx P).map (torPhi Pr.complex)).f 0) := by
  set S := (shortCx P).map (torPhi Pr.complex) with hSdef
  have hsq : HomologicalComplex.opcyclesMap S.f 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom
      = (cokerIso Pr (ModuleCat.of R P)).hom ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
    have hepi : Epi (S.X₁.pOpcycles 0) := inferInstance
    rw [← cancel_epi (S.X₁.pOpcycles 0)]
    have hPF : S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0
        = S.f.f 0 ≫ S.X₂.pOpcycles 0 := HomologicalComplex.p_opcyclesMap S.f 0
    have hcfr : S.X₂.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom = augX Pr (ModuleCat.of R
        Fr) :=
      pOpcycles_cokerIso Pr (ModuleCat.of R Fr)
    have hcp : S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom = augX Pr (ModuleCat.of R P)
        :=
      pOpcycles_cokerIso Pr (ModuleCat.of R P)
    calc S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0 ≫
          (cokerIso Pr (ModuleCat.of R Fr)).hom
        = (S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0) ≫
          (cokerIso Pr (ModuleCat.of R Fr)).hom := by
          rw [Category.assoc]
      _ = S.f.f 0 ≫ (S.X₂.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom) := by
          rw [hPF, Category.assoc]
      _ = S.f.f 0 ≫ augX Pr (ModuleCat.of R Fr) := by rw [hcfr]
      _ = augX Pr (ModuleCat.of R P) ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype) :=
          augX_naturality P Pr
      _ = (S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom) ≫
          ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
          rw [hcp]
      _ = S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom ≫
          ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
          rw [Category.assoc]
  have hmono_op : Mono (HomologicalComplex.opcyclesMap S.f 0) := by
    have hrt_mono : Mono (ModuleCat.ofHom (LinearMap.rTensor M P.subtype)) := by
      rw [ModuleCat.mono_iff_injective]; exact hrt
    have : HomologicalComplex.opcyclesMap S.f 0
        = (cokerIso Pr (ModuleCat.of R P)).hom ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype)
            ≫ (cokerIso Pr (ModuleCat.of R Fr)).inv := by
      rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this]
    have : Mono ((cokerIso Pr (ModuleCat.of R P)).hom ≫ ModuleCat.ofHom (LinearMap.rTensor M
        P.subtype)) :=
      mono_comp _ _
    exact mono_comp _ _
  have hnat := HomologicalComplex.homologyι_naturality S.f 0
  have heq : HomologicalComplex.homologyMap S.f 0
      = S.X₁.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.f 0 ≫ inv (S.X₂.homologyι 0) := by
    rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  have : Mono (HomologicalComplex.opcyclesMap S.f 0 ≫ inv (S.X₂.homologyι 0)) :=
    mono_comp _ _
  exact mono_comp _ _

/-- Given a short exact sequence `0 → K →[ι] F →[π] N → 0` of `R`-modules with
`Tor₁^R(F, M) = 0` and `rTensor M ι : K ⊗_R M → F ⊗_R M` injective, we have
`Tor₁^R(N, M) = 0`. -/
theorem tor1_vanishes_of_shortExact_rTensor_injective
    {K Fr N : Type u} [AddCommGroup K] [Module R K] [AddCommGroup Fr] [Module R Fr]
    [AddCommGroup N] [Module R N]
    (ι : K →ₗ[R] Fr) (π : Fr →ₗ[R] N)
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : Function.Exact ι π)
    (hF : Tor1Vanishes R Fr M)
    (hrt : Function.Injective (LinearMap.rTensor M ι)) :
    Tor1Vanishes R N M := by
  set P : Submodule R Fr := LinearMap.range ι with hPdef
  have hkerP : LinearMap.ker π = P := (LinearMap.exact_iff).mp hex
  let e : N ≃ₗ[R] (Fr ⧸ P) :=
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.trans
      (Submodule.quotEquivOfEq (LinearMap.ker π) P hkerP)
  have hrt' : Function.Injective (LinearMap.rTensor M P.subtype) := by
    set g : K ≃ₗ[R] P := LinearEquiv.ofInjective ι hι with hgdef
    have hcomp : P.subtype.comp (g.toLinearMap) = ι := by
      ext k; rfl
    have hrTcomp : LinearMap.rTensor M ι
        = (LinearMap.rTensor M P.subtype).comp (LinearMap.rTensor M g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp, hcomp]
    have hgsurj : Function.Surjective (LinearMap.rTensor M g.toLinearMap) := by
      have : LinearMap.rTensor M g.toLinearMap
          = (TensorProduct.congr g (LinearEquiv.refl R M)).toLinearMap := by
        ext k m; rfl
      rw [this]; exact (TensorProduct.congr g (LinearEquiv.refl R M)).surjective
    have hcompinj : Function.Injective
        ((LinearMap.rTensor M P.subtype) ∘ (LinearMap.rTensor M g.toLinearMap)) := by
      have := hrt
      rw [hrTcomp] at this
      exact this
    exact Function.Injective.of_comp_right hcompinj hgsurj
  have hquot : Tor1Vanishes R (Fr ⧸ P) M :=
    tor1_vanishes_of_quotient_rTensor_injective P hF
      (fun Pr => tor0_homologyMap_mono_of_rTensor_injective P hrt' Pr)
  have hiso : ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)
      ≅ ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (Fr ⧸ P))).obj (ModuleCat.of R M) :=
    ((Tor (ModuleCat.{u} R) 1).mapIso e.toModuleIso).app (ModuleCat.of R M)
  exact Limits.IsZero.of_iso hquot hiso

/-- For `R/I`-modules `X, Y` and an `R/I`-linear map `f : X → Y`, if `f ⊗_{R/I} 1` on
`(R/I) ⊗_R M` is injective then so is `f ⊗_R 1 = rTensor M (f.restrictScalars R)`. -/
theorem rTensor_restrictScalars_injective
    {X Y : Type u} [AddCommGroup X] [Module R X] [Module (R ⧸ I) X] [IsScalarTower R (R ⧸ I) X]
    [AddCommGroup Y] [Module R Y] [Module (R ⧸ I) Y] [IsScalarTower R (R ⧸ I) Y]
    (f : X →ₗ[R ⧸ I] Y)
    (hfM : Function.Injective (LinearMap.rTensor ((R ⧸ I) ⊗[R] M) f)) :
    Function.Injective (LinearMap.rTensor M (f.restrictScalars R)) := by
  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R⧸I) (R⧸I) X M
  let eY := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R⧸I) (R⧸I) Y M
  have hnat : ∀ t : X ⊗[R⧸I] ((R⧸I) ⊗[R] M),
      (LinearMap.rTensor M (f.restrictScalars R)) (eX t)
        = eY ((LinearMap.rTensor ((R⧸I) ⊗[R] M) f) t) := by
    intro t
    induction t with
    | zero => simp
    | tmul x m' =>
        induction m' with
        | zero => simp
        | tmul a m =>
            show (LinearMap.rTensor M (f.restrictScalars R)) (eX (x ⊗ₜ[R⧸I] (a ⊗ₜ[R] m)))
              = eY ((LinearMap.rTensor ((R⧸I) ⊗[R] M) f) (x ⊗ₜ[R⧸I] (a ⊗ₜ[R] m)))
            rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
            rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
            simp only [LinearMap.restrictScalars_apply, map_smul]
            rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro u v huv
  obtain ⟨u', rfl⟩ := eX.surjective u
  obtain ⟨v', rfl⟩ := eX.surjective v
  rw [hnat, hnat] at huv
  rw [hfM (eY.injective huv)]

/-- The base-change `(R/I) ⊗_R M ≅ M/IM` upgraded to an `R/I`-linear equivalence
(the underlying `R`-linear map is `TensorProduct.quotTensorEquivQuotSMul`). -/
@[ega "III 1.1.3" "(f)"]
noncomputable def quotTensorRIEquiv :
    (R⧸I) ⊗[R] M ≃ₗ[R⧸I] (M ⧸ (I • (⊤ : Submodule R M))) where
  toFun := TensorProduct.quotTensorEquivQuotSMul M I
  map_add' := map_add _
  map_smul' := by
    intro c x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine x.induction_on ?_ ?_ ?_
    · simp
    · intro a m
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [show (Ideal.Quotient.mk I r) • ((Ideal.Quotient.mk I s) ⊗ₜ[R] m)
            = (Ideal.Quotient.mk I (r * s)) ⊗ₜ[R] m by
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]]
      rw [quotTensorEquivQuotSMul_mk_tmul, quotTensorEquivQuotSMul_mk_tmul]
      simp only [RingHom.id_apply, mul_smul]
      rfl
    · intro a b ha hb
      simp only [map_add, smul_add, ha, hb]
  invFun := (TensorProduct.quotTensorEquivQuotSMul M I).symm
  left_inv := (TensorProduct.quotTensorEquivQuotSMul M I).left_inv
  right_inv := (TensorProduct.quotTensorEquivQuotSMul M I).right_inv

/-- For an `R/I`-submodule `P ≤ Fr` of an `R/I`-module `Fr`, the `R`-linear map
`rTensor M (P.subtype.restrictScalars R) : P ⊗_R M → Fr ⊗_R M` is injective, provided `M/IM` is
flat over `R/I`. -/
@[sga "3 VIB 11.7" "special case"]
theorem rTensor_subtype_restrictScalars_injective
    {Fr : Type u} [AddCommGroup Fr] [Module R Fr] [Module (R ⧸ I) Fr] [IsScalarTower R (R ⧸ I) Fr]
    (P : Submodule (R ⧸ I) Fr)
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Function.Injective (LinearMap.rTensor M ((P.subtype).restrictScalars R)) := by
  have hflat : Module.Flat (R ⧸ I) ((R⧸I) ⊗[R] M) :=
    Module.Flat.of_linearEquiv (quotTensorRIEquiv I)
  have hfM : Function.Injective (LinearMap.rTensor ((R⧸I) ⊗[R] M) P.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap P.subtype Subtype.coe_injective
  exact rTensor_restrictScalars_injective I P.subtype hfM

set_option backward.isDefEq.respectTransparency false in
/-- `Finsupp.mapRange` of an exact pair of linear maps is exact (computed
componentwise; `ι →₀ -` is exact). -/
theorem finsupp_mapRange_exact (ι : Type u) {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact ((Finsupp.mapRange.linearMap f : (ι →₀ A) →ₗ[R] (ι →₀ B)))
      (Finsupp.mapRange.linearMap g) := by
  classical
  rw [LinearMap.exact_iff] at h ⊢
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxi : ∀ i, g (x i) = 0 := by
      intro i; have := Finsupp.ext_iff.mp hx i
      simpa [Finsupp.mapRange.linearMap, Finsupp.mapRange_apply] using this
    have hpre : ∀ i, ∃ a : A, f a = x i := by
      intro i; have : x i ∈ g.ker := by rw [LinearMap.mem_ker]; exact hxi i
      rw [h] at this; exact this
    choose F hF using hpre
    set F' : ι → A := fun i => if i ∈ x.support then F i else 0 with hF'def
    have hF'x : ∀ i, f (F' i) = x i := by
      intro i
      by_cases hi : i ∈ x.support
      · simp only [hF'def, hi, ite_true]; exact hF i
      · simp only [hF'def, hi, ite_false, map_zero]
        rw [Finsupp.mem_support_iff, not_not] at hi; exact hi.symm
    refine ⟨Finsupp.onFinset x.support F' ?_, ?_⟩
    · intro i hi; by_contra hni; apply hi; simp only [hF'def, hni, ite_false]
    · apply Finsupp.ext; intro i; change f (F' i) = x i; exact hF'x i
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]; apply Finsupp.ext; intro i; change g (f (y i)) = 0
    have : f (y i) ∈ f.range := ⟨y i, rfl⟩
    rw [← h, LinearMap.mem_ker] at this; exact this

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `TensorProduct.finsuppLeft` in the second tensor factor:
`finsuppLeft ∘ lTensor (ι →₀ S) φ = mapRange (lTensor S φ) ∘ finsuppLeft`. -/
theorem finsuppLeft_lTensor_conj (ι : Type u) [DecidableEq ι] (S : Type u)
    [AddCommGroup S] [Module R S]
    (P Q : Type u) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] Q) :
    (TensorProduct.finsuppLeft R R S Q ι).toLinearMap ∘ₗ LinearMap.lTensor (ι →₀ S) φ
      = (Finsupp.mapRange.linearMap (LinearMap.lTensor S φ)) ∘ₗ
        (TensorProduct.finsuppLeft R R S P ι).toLinearMap := by
  ext x s p i
  simp only [LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, Finsupp.lsingle_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul]
  rw [TensorProduct.finsuppLeft_apply_tmul, TensorProduct.finsuppLeft_apply_tmul]
  simp [Finsupp.sum_single_index, Finsupp.mapRange.linearMap, LinearMap.lTensor_tmul]

/-- `TensorProduct.finsuppLeft` conjugates `lTensor (ι →₀ S) φ` to
`Finsupp.mapRange (lTensor S φ)`. -/
theorem finsuppLeft_lTensor_sq (ι : Type u) [DecidableEq ι] (S : Type u)
    [AddCommGroup S] [Module R S]
    (P Q : Type u) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] Q) :
    LinearMap.lTensor (ι →₀ S) φ ∘ₗ (TensorProduct.finsuppLeft R R S P ι).symm.toLinearMap
      = (TensorProduct.finsuppLeft R R S Q ι).symm.toLinearMap ∘ₗ
        Finsupp.mapRange.linearMap (LinearMap.lTensor S φ) := by
  have h := finsuppLeft_lTensor_conj ι S P Q φ
  apply LinearMap.ext
  intro z
  have key := LinearMap.congr_fun h ((TensorProduct.finsuppLeft R R S P ι).symm z)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at key ⊢
  rw [LinearEquiv.apply_symm_apply] at key
  rw [← key, LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
open Tor1VanishesAux in
/-- Exactness in degree `1` of the tensored complex passes to direct sums: if `S ⊗ Pr` is exact at
degree `1`, so is `(ι →₀ S) ⊗ Pr`. -/
theorem tor1_finsupp_exactAt (ι : Type u) (S : Type u) [AddCommGroup S] [Module R S]
    (Pr : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ))
    (hCexact : ((torPhi Pr).obj (ModuleCat.of R S)).ExactAt 1) :
    ((torPhi Pr).obj (ModuleCat.of R (ι →₀ S))).ExactAt 1 := by
  classical
  set C := (torPhi Pr).obj (ModuleCat.of R S) with hCdef
  set D := (torPhi Pr).obj (ModuleCat.of R (ι →₀ S)) with hDdef
  have hp1 : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (by simp [ComplexShape.down] : (ComplexShape.down ℕ).Rel 2 1)
  have hn1 : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (by simp [ComplexShape.down] : (ComplexShape.down ℕ).Rel 1 0)
  rw [HomologicalComplex.exactAt_iff' C 2 1 0 hp1 hn1] at hCexact
  rw [HomologicalComplex.exactAt_iff' D 2 1 0 hp1 hn1]
  have hCfun : Function.Exact (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d 2 1)))
      (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d 1 0))) := by
    have h : Function.Exact (ModuleCat.Hom.hom (C.d 2 1)) (ModuleCat.Hom.hom (C.d 1 0)) :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hCexact
    rwa [hCdef, torPhi_d_hom, torPhi_d_hom] at h
  have hSfun : Function.Exact
      (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d 2 1))) : (ι →₀ _)
          →ₗ[R] _)
      (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d 1 0)))) :=
    finsupp_mapRange_exact ι _ _ hCfun
  let Sf := ModuleCat.ofHom (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom
      (Pr.d 2 1))) : (ι →₀ (S ⊗[R] (Pr.X 2))) →ₗ[R] (ι →₀ (S ⊗[R] (Pr.X 1))))
  let Sg := ModuleCat.ofHom (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom
      (Pr.d 1 0))) : (ι →₀ (S ⊗[R] (Pr.X 1))) →ₗ[R] (ι →₀ (S ⊗[R] (Pr.X 0))))
  have hSfg : Sf ≫ Sg = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; exact hSfun.apply_apply_eq_zero z
  let Sfin : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk Sf Sg hSfg
  have hSfinExact : Sfin.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hSfun
  have hiso : Sfin ≅ D.sc' 2 1 0 := by
    refine ShortComplex.isoMk
      (TensorProduct.finsuppLeft R R S (Pr.X 2) ι).symm.toModuleIso
      (TensorProduct.finsuppLeft R R S (Pr.X 1) ι).symm.toModuleIso
      (TensorProduct.finsuppLeft R R S (Pr.X 0) ι).symm.toModuleIso ?_ ?_
    all_goals
      apply ModuleCat.hom_ext
      exact finsuppLeft_lTensor_sq ι S _ _ _
  exact ShortComplex.exact_of_iso hiso hSfinExact

open Tor1VanishesAux in
/-- `Tor₁` vanishes on a free `R ⧸ I`-module: if `Tor₁^R(R ⧸ I, M) = 0` then
`Tor₁^R(ι →₀ (R ⧸ I), M) = 0`, since `Tor₁` commutes with direct sums in its first variable. -/
theorem tor1_vanishes_finsupp (ι : Type u) (H2 : Tor1Vanishes R (R ⧸ I) M) :
    Tor1Vanishes R (ι →₀ (R ⧸ I)) M := by
  classical
  let Pr : ProjectiveResolution (ModuleCat.of R M) := ProjectiveResolution.of (ModuleCat.of R M)
  have hC : Limits.IsZero (((torPhi Pr.complex).obj (ModuleCat.of R (R ⧸ I))).homology 1) :=
    Limits.IsZero.of_iso H2 (torIsoHomology Pr (R ⧸ I)).symm
  have hCexact : ((torPhi Pr.complex).obj (ModuleCat.of R (R ⧸ I))).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]; exact hC
  have hDexact : ((torPhi Pr.complex).obj (ModuleCat.of R (ι →₀ (R ⧸ I)))).ExactAt 1 :=
    tor1_finsupp_exactAt ι (R ⧸ I) Pr.complex hCexact
  have hD :
      Limits.IsZero (((torPhi Pr.complex).obj (ModuleCat.of R (ι →₀ (R ⧸ I)))).homology 1) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]; exact hDexact
  exact Limits.IsZero.of_iso hD (torIsoHomology Pr (ι →₀ (R ⧸ I)))

/-- If `M/IM` is flat over `R/I`, `Tor₁^R(R/I, M) = 0` and `N` is annihilated by `I`, then there
is a short exact sequence of `R`-modules `0 → K →[ι] F →[π] N → 0` with `Tor₁^R(F, M) = 0` and
`rTensor M ι : K ⊗_R M → F ⊗_R M` injective. -/
theorem exists_free_presentation_of_smul_eq_bot
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (H2 : Tor1Vanishes R (R ⧸ I) M)
    (N : Type u) [AddCommGroup N] [Module R N]
    (hN : I • (⊤ : Submodule R N) = ⊥) :
    ∃ (K Fr : Type u) (_ : AddCommGroup K) (_ : Module R K)
      (_ : AddCommGroup Fr) (_ : Module R Fr)
      (ι : K →ₗ[R] Fr) (π : Fr →ₗ[R] N),
      Function.Injective ι ∧ Function.Surjective π ∧ Function.Exact ι π ∧
      Tor1Vanishes R Fr M ∧ Function.Injective (LinearMap.rTensor M ι) := by
  have htor : Module.IsTorsionBySet R N (I : Set R) := by
    intro n r
    have : (r:R) • (n:N) ∈ I • (⊤ : Submodule R N) :=
      Submodule.smul_mem_smul r.2 Submodule.mem_top
    rw [hN] at this; simpa using this
  let hRI : Module (R ⧸ I) N := htor.module
  have hST : IsScalarTower R (R ⧸ I) N := by
    refine ⟨fun r x n => ?_⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show (Ideal.Quotient.mk I r' : R ⧸ I) • n = r' • n from rfl, ← smul_assoc]; rfl
  let Fr := N →₀ (R ⧸ I)
  let π : Fr →ₗ[R ⧸ I] N := Finsupp.linearCombination (R ⧸ I) id
  let Ksub : Submodule (R ⧸ I) Fr := LinearMap.ker π
  have hfin : Tor1Vanishes R Fr M := tor1_vanishes_finsupp I N H2
  have hrtinj : Function.Injective (LinearMap.rTensor M ((Ksub.subtype).restrictScalars R)) :=
    rTensor_subtype_restrictScalars_injective I Ksub H1
  refine ⟨Ksub, Fr, inferInstance, inferInstance, inferInstance, inferInstance,
    Ksub.subtype.restrictScalars R, π.restrictScalars R, ?_, ?_, ?_, hfin, hrtinj⟩
  · exact Subtype.coe_injective
  · intro n
    refine ⟨Finsupp.single n 1, ?_⟩
    show π (Finsupp.single n 1) = n
    rw [Finsupp.linearCombination_single]; simp
  · rw [LinearMap.exact_iff]
    show LinearMap.ker (π.restrictScalars R) = LinearMap.range (Ksub.subtype.restrictScalars R)
    apply le_antisymm
    · intro x hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro _ ⟨⟨y, hy⟩, rfl⟩; exact hy

/-- If `M ⧸ IM` is flat over `R ⧸ I` and `Tor₁^R(R ⧸ I, M) = 0`, then `Tor₁^R(N, M) = 0` for every
`R`-module `N` annihilated by `I`. -/
@[sga "1 IV 5.2" "B = A/I: (ii) ⇒ (i)", sga "1 IV 5.3" "special case", sga "3 VIB 12.7" "partial"]
theorem tor1_vanishes_of_smul_eq_bot
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (H2 : Tor1Vanishes R (R ⧸ I) M)
    (N : Type u) [AddCommGroup N] [Module R N]
    (hN : I • (⊤ : Submodule R N) = ⊥) :
    Tor1Vanishes R N M := by
  obtain ⟨K, Fr, _, _, _, _, ι, π, hι, hπ, hex, hF, hrt⟩ :=
    exists_free_presentation_of_smul_eq_bot I H1 H2 N hN
  exact tor1_vanishes_of_shortExact_rTensor_injective ι π hι hπ hex hF hrt

end ChangeOfRings
