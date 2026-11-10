module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapSections
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension

/-!
# A surjection of quasi-coherent modules gives a closed immersion of vector bundles

Let `X` be a scheme and `f : ℱ ⟶ 𝒢` a morphism of quasi-coherent `𝒪_X`-modules, with induced
morphism of vector bundles `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)`. Over an affine open `V` of `X` the vector bundles
are the spectra of `Sym_{Γ(X, V)}(Γ(ℱ, V))` and `Sym_{Γ(X, V)}(Γ(𝒢, V))`, and `𝐕(f)` is the
spectrum of the algebra map induced by `Γ(f, V)`. In particular, if `f` is an epimorphism then
`𝐕(f)` is a closed immersion, since `Γ(f, V)` is then surjective.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.vectorBundleSections`: the identification of the sections of
  `𝐕(ℱ)` over the preimage of an affine open `V` with `Sym_{Γ(X, V)}(Γ(ℱ, V))`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.vectorBundleMap_appLE_vectorBundleSections`: `𝐕(f)` on the
  sections over the preimage of an affine open is the algebra map of symmetric algebras induced
  by `Γ(f, V)`.
* `AlgebraicGeometry.Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi`: a surjection of
  quasi-coherent modules induces a closed immersion of vector bundles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSections

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The identification of the sections of the vector bundle `𝐕(ℱ)` over the preimage of an affine
open `V` with the symmetric algebra `Sym_{Γ(X, V)}(Γ(ℱ, V))`. -/
def vectorBundleSections (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) :
    SymmetricAlgebra Γ(X, V) Γ(F, V) →+* Γ(vectorBundle X F, vectorBundleToBase X F ⁻¹ᵁ V) :=
  ((vectorBundlePushforwardIso X (F := F)).inv.right.hom.app (op V)).hom.comp
    (symSectionsRingEquiv F hV).toRingHom

/-- The forward map of `vectorBundlePushforwardIso` on sections over `V` is a left inverse of the
inverse map. -/
private theorem hom_app_inv_app (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens) :
    Function.LeftInverse
      ((vectorBundlePushforwardIso X (F := F)).hom.right.hom.app (op V)).hom
      ((vectorBundlePushforwardIso X (F := F)).inv.right.hom.app (op V)).hom :=
  fun w => congrArg (fun g : symmetricAlgebraSheaf X F ⟶ symmetricAlgebraSheaf X F =>
    (g.right.hom.app (op V)).hom w) (vectorBundlePushforwardIso X (F := F)).inv_hom_id

/-- The map `vectorBundleSections F hV` from `Sym_{Γ(X, V)}(Γ(ℱ, V))` to the sections of `𝐕(ℱ)`
over the preimage of the affine open `V` is bijective. -/
theorem vectorBundleSections_bijective (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) : Function.Bijective (vectorBundleSections F hV) :=
  ⟨fun x y hxy =>
    (symSectionsRingEquiv F hV).injective <| (hom_app_inv_app F V).injective hxy,
    fun y => by
      obtain ⟨z, hz⟩ := Stacks.RelativeSpecClosedImmersion.surjective_app_of_algebraIso
        (vectorBundlePushforwardIso X (F := F)).symm (op V) y
      obtain ⟨a, rfl⟩ := (symSectionsRingEquiv F hV).surjective z
      exact ⟨a, hz⟩⟩

/-- **`𝐕(f)` on sections over the preimage of an affine open** is the algebra map of symmetric
algebras induced by `Γ(f, V)`. -/
theorem vectorBundleMap_appLE_vectorBundleSections (f : F ⟶ G) {V : X.Opens}
    (hV : IsAffineOpen V)
    (hle : vectorBundleToBase X G ⁻¹ᵁ V ≤
      (vectorBundleMap X f).left ⁻¹ᵁ (vectorBundleToBase X F ⁻¹ᵁ V))
    (a : SymmetricAlgebra Γ(X, V) Γ(F, V)) :
    (vectorBundleMap X f).left.appLE (vectorBundleToBase X F ⁻¹ᵁ V)
        (vectorBundleToBase X G ⁻¹ᵁ V) hle (vectorBundleSections F hV a) =
      vectorBundleSections G hV
        (SymPow.symAlgMap (Stacks.AlgebraicGeometry.QcohLimits.appₗ f V) a) := by
  have h1 := pushforwardAlgebraMap_app (vectorBundleMap X f) V hle
  have h2 := pushforwardAlgebraMap_vectorBundleMap X f
  rw [h2] at h1
  change _ = ((vectorBundlePushforwardIso X (F := G)).inv.right.hom.app (op V)).hom
    (symSectionsRingEquiv G hV (SymPow.symAlgMap (Stacks.AlgebraicGeometry.QcohLimits.appₗ f V) a))
  rw [← symmetricAlgebraSheafMap_symSectionsRingEquiv hV f a]
  refine (congrArg (fun φ => (CommRingCat.Hom.hom φ)
    (((vectorBundlePushforwardIso X (F := F)).inv.right.hom.app (op V)).hom
      (symSectionsRingEquiv F hV a))) h1).symm.trans ?_
  change ((vectorBundlePushforwardIso X (F := G)).inv.right.hom.app (op V)).hom
    (((symmetricAlgebraSheafMap X f).right.hom.app (op V)).hom
      (((vectorBundlePushforwardIso X (F := F)).hom.right.hom.app (op V)).hom
        (((vectorBundlePushforwardIso X (F := F)).inv.right.hom.app (op V)).hom
          (symSectionsRingEquiv F hV a)))) = _
  rw [hom_app_inv_app F V]

/-- **A surjection of quasi-coherent modules induces a closed immersion of vector bundles**: over
an affine open of the base, `𝐕(f)` is the spectrum of the algebra map of symmetric algebras
induced by the surjection `Γ(f, V)`. -/
theorem isClosedImmersion_vectorBundleMap_of_epi (f : F ⟶ G) [Epi f] :
    IsClosedImmersion (vectorBundleMap X f).left := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : X.affineOpens => vectorBundleToBase X F ⁻¹ᵁ (U : X.Opens))
    ((vectorBundleToBase X F).iSup_preimage_eq_top (iSup_affineOpens_eq_top X)) fun U => ?_
  have hpre : (vectorBundleMap X f).left ⁻¹ᵁ (vectorBundleToBase X F ⁻¹ᵁ (U : X.Opens)) =
      vectorBundleToBase X G ⁻¹ᵁ (U : X.Opens) :=
    congrArg (fun g : vectorBundle X G ⟶ X => g ⁻¹ᵁ (U : X.Opens))
      (vectorBundleMap_left_comp X f)
  refine Stacks.FiniteFactorization.isClosedImmersion_morphismRestrict _ _
    (isAffineOpen_preimage_vectorBundleToBase X F U) (by
      rw [hpre]; exact isAffineOpen_preimage_vectorBundleToBase X G U) ?_
  refine Stacks.RelativeSpecClosedImmersion.surjective_app_of_surjective_appLE _ hpre hpre.ge ?_
  intro y
  obtain ⟨b, rfl⟩ := (vectorBundleSections_bijective G U.2).2 y
  obtain ⟨a, rfl⟩ := SymPow.symAlgMap_surjective (f := Stacks.AlgebraicGeometry.QcohLimits.appₗ f U)
    (Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X f U U.2) b
  exact ⟨vectorBundleSections F U.2 a, vectorBundleMap_appLE_vectorBundleSections f U.2 _ a⟩

end AlgebraicGeometry.Scheme.Modules

end
