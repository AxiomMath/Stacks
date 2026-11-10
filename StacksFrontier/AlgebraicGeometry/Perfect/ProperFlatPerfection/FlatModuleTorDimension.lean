module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a flat quasi-coherent module has finite Tor dimension

Let `g : Y ⟶ W` be a morphism of schemes with `W` affine and `Y` quasi-compact and
quasi-separated, and let `𝒢` be a quasi-coherent `𝒪_Y`-module which is flat over `W`. Then
`Rg_*𝒢` has finite Tor dimension on `W`.

This is the Tor-dimension half of the proof of [Stacks, Tag 0B91] (2) over an affine base, the
step the source obtains from [Stacks, Tag 08EV] through [Stacks, Tag 0DJQ]. It is proved here
directly, along the route of
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target`, which does
the same for a perfect morphism and a complex of finite Tor dimension.

## Main results

* `AlgebraicGeometry.hasTorAmplitude_schemeDerivedPushforward_tildeSingle_of_flat`: for
  `φ : R ⟶ S` and an `S`-module `M` flat over `R`, `R(Spec φ)_*M̃` has Tor amplitude in `[0, 0]`.
* `AlgebraicGeometry.hasTorAmplitude_schemeDerivedPushforward_single_of_isAffine`: the same for
  a morphism of affine schemes and a quasi-coherent module flat over the target.
* `AlgebraicGeometry.hasFiniteTorDimension_derivedPushforward_of_twoOpenCover`: the cover step
  of the induction, the relative Mayer–Vietoris triangle of [Stacks, Tag 08HZ] read with
  [Stacks, Tag 08CK] and [Stacks, Tag 08CJ].
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_single_of_isFlatOver`: **the
  Tor-dimension half over an affine base.**

## Implementation notes

The base case is [Stacks, Tag 0A9F] at a module, `R(Spec φ)_*M̃ ≅ (M_R)~`, followed by
[Stacks, Tag 08E9], which reads the Tor amplitude of `(M_R)~` off the module `M_R`; a flat
module placed in degree zero is its own flat representative in `[0, 0]`
([Stacks, Tag 0654]). An affine scheme is moved to the spectrum of its ring of global sections
along `AlgebraicGeometry.Scheme.isoSpec`, as in
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine`. Flatness of
`Γ(Y, 𝒢)` over `Γ(W, 𝒪_W)` is [Stacks, Tag 01U4].

The induction over the opens of `Y` is that of [Stacks, Tag 08DR], in the two-open-cover shape
`Stacks.Cohomology.DerivedBaseChange.compact_open_immersion_induction_on`; the property carried
is quantified over every quasi-coherent module flat over `W`, which restriction to an open
preserves ([Stacks, Tag 02JZ]).

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The affine base case at a ring map.** For `φ : R ⟶ S` and an `S`-module `M` which is flat
over `R`, the derived direct image `R(Spec φ)_*M̃` has Tor amplitude in `[0, 0]` on `Spec R`:
by [Stacks, Tag 0A9F] it is `(M_R)~`, and by [Stacks, Tag 08E9] its Tor amplitude is that of the
flat module `M_R` placed in degree zero. -/
theorem hasTorAmplitude_schemeDerivedPushforward_tildeSingle_of_flat {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} S)
    (hM : Module.Flat R ((ModuleCat.restrictScalars φ.hom).obj M)) :
    HasTorAmplitude (Spec R).toRingedSpace
      ((schemeDerivedPushforward (Spec.map φ)).obj
        (DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) 0).obj M))))
      0 0 := by
  refine FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec R).toRingedSpace)
    ((hasTorAmplitude_tilde_iff _ 0 0).2 ?_) (affinePushforwardTildeDerivedObjIso' φ _)
  rw [StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative]
  refine ⟨((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).obj
    ((HomologicalComplex.single _ _ 0).obj M), ?_, ?_, ?_,
    ⟨(ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.app _⟩⟩
  · intro i
    by_cases hi : i = 0
    · subst hi
      exact Module.Flat.of_linearEquiv ((ModuleCat.restrictScalars φ.hom).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).toLinearEquiv
    · have hz : IsZero ((ModuleCat.restrictScalars φ.hom).obj
          (((HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) 0).obj M).X i)) :=
        Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
      have := (ModuleCat.isZero_iff_subsingleton.1 hz)
      change Module.Flat R ((ModuleCat.restrictScalars φ.hom).obj
          (((HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) 0).obj M).X i))
      infer_instance
  · infer_instance
  · infer_instance

/-- **The affine base case at a morphism of affine schemes.** For `h : Z ⟶ W` with `Z` and `W`
affine and a quasi-coherent `𝒪_Z`-module `𝒢` flat over `W`, `Rh_*𝒢` has Tor amplitude in
`[0, 0]`. The square of `AlgebraicGeometry.isPullback_isoSpec` moves the question to
`Spec Γ(Z, ⊤) ⟶ Spec Γ(W, ⊤)`, where `𝒢` is `Γ(Z, 𝒢)~`, a module flat over `Γ(W, ⊤)` by
[Stacks, Tag 01U4]. -/
theorem hasTorAmplitude_schemeDerivedPushforward_single_of_isAffine {Z W : Scheme.{u}}
    [IsAffine Z] [IsAffine W] (h : Z ⟶ W) (B : Z.Modules) [B.IsQuasicoherent]
    (hB : IsFlatOver h.toLRSHom.toShHom B) :
    HasTorAmplitude W.toRingedSpace
      ((schemeDerivedPushforward h).obj ((DerivedCategory.singleFunctor Z.Modules 0).obj B))
      0 0 := by
  have hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤ := by simp
  let N : ModuleCat.{u} Γ(Z, ⊤) := ModuleCat.of Γ(Z, ⊤) Γ(B, ⊤)
  have h12 := (isFlatOver_tfae h B).out 1 2
  have hflat : Module.Flat Γ(W, ⊤)
      ((ModuleCat.restrictScalars (h.appLE ⊤ ⊤ hle).hom).obj N) :=
    h12.mp hB ⊤ (isAffineOpen_top Z) ⊤ (isAffineOpen_top W) hle
  let eB : (Scheme.Modules.restrictFunctor Z.isoSpec.inv).obj B ≅ tilde N :=
    (Scheme.Modules.restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := Z)).symm).app B ≪≫
      (Stacks.Modules.tildeIsoRestrictFromSpec B (isAffineOpen_top Z)).symm
  let hTZ : (Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj B) ≅
      DerivedCategory.Q.obj (((tilde.functor Γ(Z, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{u} Γ(Z, ⊤)) (ComplexShape.up ℤ) 0).obj N)) :=
    ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategorySingleFunctor 0).app B ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eB ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (tilde N) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (tilde.functor Γ(Z, ⊤))
          (ComplexShape.up ℤ) 0).app N).symm
  refine (hasTorAmplitude_restrictFunctor_iso_iff W.isoSpec.symm _ 0 0).1 ?_
  exact FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec Γ(W, ⊤)).toRingedSpace)
    (hasTorAmplitude_schemeDerivedPushforward_tildeSingle_of_flat (h.appLE ⊤ ⊤ hle) N hflat)
    (schemeDerivedPushforwardRestrictOpenIso h W.isoSpec.inv (Spec.map (h.appLE ⊤ ⊤ hle))
      Z.isoSpec.inv (isPullback_isoSpec h hle) _ ≪≫
      (schemeDerivedPushforward (Spec.map (h.appLE ⊤ ⊤ hle))).mapIso hTZ)

open Stacks.SchemeCohomology (hom) in
open Stacks.Cohomology.RelativeMayerVietoris in
/-- **The cover step of the Mayer–Vietoris induction.** If `Z = U ∪ V` and the three restricted
direct images over `U`, `V` and `U ∩ V` have finite Tor dimension on `W`, so does `RG_*B`. This
is the relative Mayer–Vietoris triangle of [Stacks, Tag 08HZ], with [Stacks, Tag 08CK] at its
biproduct vertex and [Stacks, Tag 08CJ] (1) at the vertex being bounded. -/
theorem hasFiniteTorDimension_derivedPushforward_of_twoOpenCover {Z W : Scheme.{u}}
    (G : Z ⟶ W) (U V : Z.Opens) (hUV : U ⊔ V = ⊤) (B : DerivedCategory Z.Modules)
    (hU : HasFiniteTorDimension W.toRingedSpace
      ((canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom U.ι))).obj B))
    (hV : HasFiniteTorDimension W.toRingedSpace
      ((canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom V.ι))).obj B))
    (hUV' : HasFiniteTorDimension W.toRingedSpace
      ((canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom (U ⊓ V).ι))).obj B)) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward G).obj B) := by
  obtain ⟨a₂, b₂, h₂⟩ := hasFiniteTorDimension_biprod.{u, u + 1} (X := W.toRingedSpace)
    ((canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom U.ι))).obj B)
    ((canonicalRightDerived (restrictedPushforwardAlong (hom G) (hom V.ι))).obj B) hU hV
  obtain ⟨a₃, b₃, h₃⟩ := hUV'
  have hT := canonicalPushforwardTriangle_distinguished (hom G) (hom U.ι) (hom V.ι)
    (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
  have hmain := FlatOpcycles.hasTorAmplitude_obj₁.{u, u + 1} (X := W.toRingedSpace) _ hT
    (min (a₂ - 1) a₃) (max (b₂ - 1) b₃) ?_ ?_
  · erw [canonicalPushforwardTriangle_obj₁] at hmain
    exact ⟨_, _, hmain⟩
  · erw [canonicalPushforwardTriangle_obj₂]
    exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h₂ (by omega) (by omega)
  · erw [canonicalPushforwardTriangle_obj₃]
    exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h₃ (min_le_right _ _)
      (le_max_right _ _)

/-- Flatness over the target survives restriction to an open of the source
([Stacks, Tag 02JZ], an open immersion being flat). -/
theorem isFlatOver_restrict_ι {P T : Scheme.{u}} (h : P ⟶ T) (V : P.Opens) (G : P.Modules)
    (hG : IsFlatOver h.toLRSHom.toShHom G) :
    IsFlatOver (V.ι ≫ h).toLRSHom.toShHom (G.restrict V.ι) := by
  refine (isFlatOver_iff_of_iso _
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app G)).2 fun p => ?_
  exact (isFlatOverAt_pullback_ι_iff h V G p).2 (hG _)

/-- **The Tor-dimension half over an affine base.** Let `g : Y ⟶ W` be a morphism of schemes
with `W` affine and `Y` quasi-compact and quasi-separated, and let `𝒢` be a quasi-coherent
`𝒪_Y`-module flat over `W`. Then `Rg_*𝒢` has finite Tor dimension on `W`.

The induction of [Stacks, Tag 08DR] is run on the property "for every quasi-coherent module on
`Z` flat over `W`, its derived direct image along `jZ ≫ g` has finite Tor dimension"; the affine
case is `hasTorAmplitude_schemeDerivedPushforward_single_of_isAffine` and the cover step is
`hasFiniteTorDimension_derivedPushforward_of_twoOpenCover`. -/
@[sga "6 0 3.1" "special case"]
theorem hasFiniteTorDimension_schemeDerivedPushforward_single_of_isFlatOver
    {Y W : Scheme.{u}} [IsAffine W] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : Y ⟶ W) (B : Y.Modules) [B.IsQuasicoherent]
    (hB : IsFlatOver g.toLRSHom.toShHom B) :
    HasFiniteTorDimension W.toRingedSpace
      ((schemeDerivedPushforward g).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj B)) := by
  set P : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop := fun Z jZ =>
    ∀ B : Z.Modules, B.IsQuasicoherent → IsFlatOver (jZ ≫ g).toLRSHom.toShHom B →
      HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward (jZ ≫ g)).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj B))
  have hP : P Y (𝟙 Y) := by
    refine Stacks.Cohomology.DerivedBaseChange.compact_open_immersion_induction_on P ?_ ?_
    · intro Z _ _ _ jZ _ B hqcB hflB
      exact ⟨0, 0, hasTorAmplitude_schemeDerivedPushforward_single_of_isAffine (jZ ≫ g) B hflB⟩
    · intro Z _ _ jZ _ U V hUV hPU hPV hPUV B hqcB hflB
      have key : ∀ O : Z.Opens, P O.toScheme (O.ι ≫ jZ) →
          HasFiniteTorDimension W.toRingedSpace
            ((Stacks.Cohomology.RelativeMayerVietoris.canonicalRightDerived
              (Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong
                (Stacks.SchemeCohomology.hom (jZ ≫ g)) (Stacks.SchemeCohomology.hom O.ι))).obj
              ((DerivedCategory.singleFunctor Z.Modules 0).obj B)) := by
        intro O hO
        have hqcO : (B.restrict O.ι).IsQuasicoherent :=
          Scheme.Modules.isQuasicoherent_restrictFunctor (f := O.ι) B
        have hflO : IsFlatOver ((O.ι ≫ jZ) ≫ g).toLRSHom.toShHom (B.restrict O.ι) := by
          rw [Category.assoc]
          exact isFlatOver_restrict_ι (jZ ≫ g) O B hflB
        obtain ⟨a, b, hab⟩ := hO _ hqcO hflO
        rw [Category.assoc] at hab
        exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso (X := W.toRingedSpace) hab
          ((restrictedDerivedPushforwardRestrictFunctorIso (jZ ≫ g) O.ι).app _ ≪≫
            (schemeDerivedPushforward (O.ι ≫ jZ ≫ g)).mapIso
              (((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategorySingleFunctor 0).app B))⟩
      exact hasFiniteTorDimension_derivedPushforward_of_twoOpenCover (jZ ≫ g) U V hUV _
        (key U hPU) (key V hPV) (key (U ⊓ V) hPUV)
  have hfin := hP B inferInstance (by rwa [Category.id_comp])
  rwa [Category.id_comp] at hfin

end AlgebraicGeometry
