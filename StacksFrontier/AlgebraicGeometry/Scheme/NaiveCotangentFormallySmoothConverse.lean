module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentEtale
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Support

/-!
# Formal smoothness and the naive cotangent complex

A morphism of schemes `f : X ⟶ Y` is formally smooth if and only if `H⁻¹(NL_{X/Y}) = 0` and
`H⁰(NL_{X/Y}) = Ω_{X/Y}` is locally projective. This file proves that these two conditions imply
formal smoothness, and states the equivalence.

## Main results

* `Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`:
  `f` is formally smooth if and only if `H⁻¹(NL_{X/Y}) = 0` and `H⁰(NL_{X/Y})` is locally
  projective.
* `Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero`:
  the two conditions imply that `f` is formally smooth.
* `Stacks.Smooth.formallySmooth_appLE_of_isZero_homology_negOne_of_isLocallyProjective`: under
  the two conditions, `Γ(Y, V) ⟶ Γ(X, U)` is formally smooth for affine opens with `f(U) ⊆ V`.
* `Stacks.Smooth.subsingleton_h1Cotangent_appLE_of_isZero_homology_negOne`: if
  `H⁻¹(NL_{X/Y}) = 0`, then `H¹(L_{Γ(X,U)⁄Γ(Y,V)}) = 0` on affine opens with `f(U) ⊆ V`.
* `Stacks.Smooth.projective_kaehlerDifferential_appLE_of_isLocallyProjective_homology_zero`: if
  `H⁰(NL_{X/Y})` is locally projective, then `Ω[Γ(X,U)⁄Γ(Y,V)]` is projective on affine opens
  with `f(U) ⊆ V`.
* `Stacks.Smooth.subsingleton_tensor_h1Cotangent_of_subsingleton_ker_baseChange`: for a flat
  `A`-algebra `T`, if the differential of `NL_{A/R} ⊗_A T` is injective, then
  `T ⊗_A H¹(L_{A/R}) = 0`.
* `Stacks.Smooth.notMem_support_of_subsingleton_tensor`: if `T` is the localisation of `A` at a
  prime `p` and `T ⊗_A M = 0`, then `p` is not in the support of `M`.

## References

* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09)
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TensorProduct

universe u

namespace Stacks.Smooth

/-! ### Ring-theoretic lemmas -/

/-- Let `T` be a flat `A`-algebra. If the differential of `NL_{A/R} ⊗_A T` is injective, then
`T ⊗_A H¹(L_{A/R})` is zero. -/
theorem subsingleton_tensor_h1Cotangent_of_subsingleton_ker_baseChange {R A T : Type u}
    [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra A T] [Module.Flat A T]
    (h : Subsingleton (LinearMap.ker (LinearMap.baseChange T
      (Algebra.Generators.self R A).toExtension.cotangentComplex))) :
    Subsingleton (T ⊗[A] Algebra.H1Cotangent R A) := by
  have hd : Function.Injective (LinearMap.baseChange T
      (Algebra.Generators.self R A).toExtension.cotangentComplex) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : LinearMap.ker _) 0)
  have hι : Function.Injective (LinearMap.baseChange T (Algebra.Extension.h1Cotangentι
      (P := (Algebra.Generators.self R A).toExtension))) := by
    simpa [LinearMap.baseChange_eq_lTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := T)
        (Algebra.Extension.h1Cotangentι (P := (Algebra.Generators.self R A).toExtension))
        Algebra.Extension.h1Cotangentι_injective
  have hcomp : (Algebra.Generators.self R A).toExtension.cotangentComplex ∘ₗ
      Algebra.Extension.h1Cotangentι = 0 := LinearMap.ext fun z => z.2
  refine subsingleton_of_forall_eq 0 fun z => hι (hd ?_)
  rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]
  simp

/-- If `T` is a localisation of `A` at a prime `p` and `T ⊗_A M` is zero, then `p` does not lie
in the support of `M`. -/
theorem notMem_support_of_subsingleton_tensor {A M T : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] [CommRing T] [Algebra A T] (p : PrimeSpectrum A)
    [IsLocalization.AtPrime T p.asIdeal] (h : Subsingleton (T ⊗[A] M)) :
    p ∉ Module.support A M := by
  have : IsLocalizedModule p.asIdeal.primeCompl (TensorProduct.mk A T M 1) :=
    (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl T _).mpr
      (TensorProduct.isBaseChange A M T)
  rw [Module.notMem_support_iff]
  exact (IsLocalizedModule.iso p.asIdeal.primeCompl
    (TensorProduct.mk A T M 1)).subsingleton_congr.mpr h

/-! ### Affine charts -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} {U : X.Opens}

/-- For affine opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V` and a point `x ∈ U`, the vanishing
`H⁻¹(NL_{X/Y}) = 0` implies that the differential of `NL_{Γ(X,U)⁄Γ(Y,V)} ⊗_{Γ(X,U)} 𝒪_{X,x}` is
injective. -/
theorem subsingleton_ker_baseChange_cotangentComplex_stalk
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1))) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U) :
    letI := algebraAppLE f hUV
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    Subsingleton (LinearMap.ker (LinearMap.baseChange ↑(X.presheaf.stalk x)
      (Algebra.Generators.self Γ(Y, V) Γ(X, U)).toExtension.cotangentComplex)) := by
  let := algebraAppLE f hUV
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f (hUV hx)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hUV hx
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
  have _ : IsScalarTower Γ(Y, V) Γ(X, U) ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hUV hx
  have _ : IsScalarTower Γ(Y, V)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hUV hx (hUV hx)
  have hq :=
    Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom
      f hUV hx (hUV hx) hV hU
  have hinj :=
    (Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff f).mp hneg x
  have _ : Subsingleton (NaiveCotangent.H₁ (NaiveCotangent.nlOfExtension
      (Algebra.Generators.self
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
        ↑(X.presheaf.stalk x)).toExtension)) :=
    ⟨fun a b => Subtype.ext (hinj (a.2.trans b.2.symm))⟩
  exact ⟨fun a b => hq.1.1 (Subsingleton.elim _ _)⟩

/-- For affine opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V`, the vanishing `H⁻¹(NL_{X/Y}) = 0`
implies that `H¹(L_{Γ(X,U)⁄Γ(Y,V)})` is zero. -/
theorem subsingleton_h1Cotangent_appLE_of_isZero_homology_negOne
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1))) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    Subsingleton (Algebra.H1Cotangent Γ(Y, V) Γ(X, U)) := by
  let := algebraAppLE f hUV
  refine Module.support_eq_empty_iff (R := Γ(X, U))
    (M := Algebra.H1Cotangent Γ(Y, V) Γ(X, U)) |>.mp
    (Set.eq_empty_iff_forall_notMem.mpr fun p => ?_)
  obtain ⟨x, hxp⟩ := (Scheme.homeoOfIso hU.isoSpec).surjective p
  have hp : hU.primeIdealOf x = p := hxp
  subst hp
  let := X.presheaf.algebra_section_stalk x
  have := hU.isLocalization_stalk x
  have : Module.Flat Γ(X, U) ↑(X.presheaf.stalk x.1) :=
    IsLocalization.flat _ (hU.primeIdealOf x).asIdeal.primeCompl
  exact notMem_support_of_subsingleton_tensor (T := ↑(X.presheaf.stalk x.1)) _
    (subsingleton_tensor_h1Cotangent_of_subsingleton_ker_baseChange
      (subsingleton_ker_baseChange_cotangentComplex_stalk f hneg hU hV hUV x.2))

/-- For affine opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V`, local projectivity of `H⁰(NL_{X/Y})`
implies that `Ω[Γ(X,U)⁄Γ(Y,V)]` is a projective `Γ(X, U)`-module. -/
theorem projective_kaehlerDifferential_appLE_of_isLocallyProjective_homology_zero
    (hproj : Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0))
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    Module.Projective Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)] := by
  let := algebraAppLE f hUV
  have h₁ : Module.Projective Γ(X, U) Γ(Scheme.Hom.relativeDifferentials f, U) :=
    @Module.Projective.of_equiv' Γ(X, U) _
      Γ(Scheme.Hom.relativeDifferentials f, U) _
      ((Scheme.Hom.relativeDifferentials f).val.obj (.op U)).isModule
      Γ((Scheme.naiveCotangentComplex f).homology 0, U) _
      (((Scheme.naiveCotangentComplex f).homology 0).val.obj (.op U)).isModule
      (hproj U hU)
      (AlgebraicGeometry.sectionsLinearEquivOfIso
        (Scheme.naiveCotangentComplexHomologyZeroIso f) U)
  have h₂ : Module.Projective Γ(X, U) Γ(cotangentSheaf f, U) :=
    @Module.Projective.of_equiv' Γ(X, U) _
      Γ(cotangentSheaf f, U) _ ((cotangentSheaf f).val.obj (.op U)).isModule
      Γ(Scheme.Hom.relativeDifferentials f, U) _
      ((Scheme.Hom.relativeDifferentials f).val.obj (.op U)).isModule
      h₁
      (AlgebraicGeometry.sectionsLinearEquivOfIso (Scheme.Hom.cotangentSheafIso f) U)
  exact @Module.Projective.of_equiv' Γ(X, U) _
    Ω[Γ(X, U)⁄Γ(Y, V)] _ _
    Γ(cotangentSheaf f, U) _ ((cotangentSheaf f).val.obj (.op U)).isModule h₂
    (cotangentSectionsEquiv f hU hV hUV).symm

/-- If `H⁻¹(NL_{X/Y}) = 0` and `H⁰(NL_{X/Y})` is locally projective, then for affine opens
`U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V` the ring map `Γ(Y, V) ⟶ Γ(X, U)` is formally smooth. -/
theorem formallySmooth_appLE_of_isZero_homology_negOne_of_isLocallyProjective
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1)))
    (hproj : Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0))
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (f.appLE V U hUV).hom.FormallySmooth := by
  let := algebraAppLE f hUV
  exact ⟨projective_kaehlerDifferential_appLE_of_isLocallyProjective_homology_zero
      f hproj hU hV hUV,
    subsingleton_h1Cotangent_appLE_of_isZero_homology_negOne f hneg hU hV hUV⟩

/-! ### The equivalence -/

/-- If the degree `-1` cohomology sheaf of the naive cotangent complex of `f : X ⟶ Y` vanishes
and its degree `0` cohomology sheaf is locally projective, then `f` is formally smooth. -/
theorem formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1)))
    (hproj : Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0)) :
    AlgebraicGeometry.FormallySmooth f :=
  formallySmooth_of_formallySmooth_appLE f fun _ hU _ hV hUV =>
    formallySmooth_appLE_of_isZero_homology_negOne_of_isLocallyProjective f hneg hproj hU hV hUV

/-- A morphism of schemes `f : X ⟶ Y` is formally smooth if and only if the degree `-1`
cohomology sheaf of its naive cotangent complex vanishes and its degree `0` cohomology sheaf is
locally projective. -/
@[stacks 0D0L]
theorem formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero :
    AlgebraicGeometry.FormallySmooth f ↔
      (IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
        Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0)) :=
  ⟨fun hf => ⟨isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth f hf,
    isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth f hf⟩,
  fun h => formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero f
    h.1 h.2⟩

end Stacks.Smooth

end
