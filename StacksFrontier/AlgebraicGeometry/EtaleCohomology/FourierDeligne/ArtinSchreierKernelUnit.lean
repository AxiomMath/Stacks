module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelProduct

/-!
# The unit of the tensor product of étale sheaves and trivial Artin–Schreier kernels

The unit of the tensor product of sheaves of `Λ`-modules on Mathlib's small étale site
(`CategoryTheory.Sheaf.monoidalCategory`) is the constant sheaf on `Λ`, lifted to the module
universe: it is the sheafification of the constant presheaf with value the unit `ULift Λ` of the
large-universe tensor product of modules. Consequently a pulled back Artin–Schreier sheaf
`(e ≫ Spec φ)⁻¹ L_ψ(g)` with `φ g = c^q - c` is the unit; this is the triviality of the kernel
`L_ψ(t(x + u))` of the composite of two Fourier transforms on the antidiagonal `x + u = 0`, in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) through Laumon's Fourier
transform.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleTensorUnitIso`: `𝟙_ ≅ Λ_X`.

## Main results

* `Stacks.ArtinSchreier.nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_tensorUnit`:
  `(e ≫ Spec φ)⁻¹ L_ψ(g) ≅ 𝟙_` when `φ g = c^q - c`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- **The unit of the tensor product of étale sheaves of `Λ`-modules is the constant sheaf `Λ`**:
the unit of `CategoryTheory.Sheaf.monoidalCategory` is the sheafification of the constant presheaf
on the unit `ULift Λ` of the large-universe tensor product of modules. -/
def etaleModuleTensorUnitIso (Λ : Type) [CommRing Λ] (X : Scheme.{u}) :
    𝟙_ (EtaleModules.{u, 0} Λ X) ≅
      etaleModuleConstantSheaf Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) X :=
  Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
  [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of A'))]
  (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (hX : schemeSizeBelow B.cutoff (Spec (.of A))) (hX' : schemeSizeBelow B.cutoff (Spec (.of A')))
  {Y : Scheme.{u}} (e : Y ⟶ Spec (.of A'))

include hX' in
/-- **`(e ≫ Spec φ)⁻¹ L_ψ(g)` is the unit `𝟙_` of the tensor product when `φ g = c^q - c`**, the
base point of `L_ψ(g)` being the image of a geometric point of `Spec A'`. -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_tensorUnit
    (c : A') (hc : φ g = c ^ Fintype.card k - c) {h : Y ⟶ Spec (.of A)}
    (hh : h = e ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A')))
    (hy : y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)) = x) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      𝟙_ (EtaleModules.{u, 0} Λ Y)) := by
  obtain ⟨a⟩ := nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf k g φ Λ ψ
    B hX hX' e c hc hh p₀ y hy
  exact ⟨a ≪≫ (etaleModuleTensorUnitIso Λ Y).symm⟩

end Stacks.ArtinSchreier
