module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.DiagonalTorLocalization
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.ExteriorTensorTor

/-!
# Reduction to the diagonal at the local rings of `X × X`

Let `k` be a field, `A` a commutative `k`-algebra and `M`, `N` two `A`-modules. Let `B` be a
localization of `A ⊗[k] A` which carries a retraction `d : B → A` of the multiplication map, that
is, a ring map with `d ∘ φ = lmul'` for the structural map `φ : A ⊗[k] A → B`. Then for every `i`

`Tor_i^B(A, B ⊗_{A ⊗[k] A} (M ⊗[k] N)) ≅ Tor_i^A(M, N)`

as `B`-modules, both sides carrying the action of `B` through `d` where they are `A`-modules.

This is [Stacks, Tag 0B0T] part (1) at the local rings of `X × X` along the diagonal.

## Main results

* `Stacks.Intersection.Diagonal.localizationBaseChangeIso` — base change along a localization
  `R → B` of a `B`-module read back over `R` returns the module.
* `Stacks.Intersection.Diagonal.localizationBaseChangeRestrictIso` — base change to `B` of an
  `A`-module restricted along `R → A` is the module read over `B` through a retraction
  `d : B → A`.
* `Stacks.Intersection.Diagonal.diagonalTorLocalizedIso` — **the reduction to the diagonal over a
  localization of `A ⊗[k] A`, in every degree.**

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 00M8](https://stacks.math.columbia.edu/tag/00M8)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace Stacks.Intersection.Diagonal

section Localized

variable {R B : Type u} [CommRing R] [CommRing B]

/-- **Base change along a localization undoes restriction of scalars.** If `B` is a localization
of `R` at a multiplicative set `T`, through a ring map `φ`, then for every `B`-module `Q` the
canonical map `B ⊗_R Q → Q` is an isomorphism. -/
noncomputable def localizationBaseChangeIso (φ : R →+* B) (T : Submonoid R)
    (hT : letI := φ.toAlgebra; IsLocalization T B) (Q : ModuleCat.{u} B) :
    (ModuleCat.extendScalars φ).obj ((ModuleCat.restrictScalars φ).obj Q) ≅ Q :=
  letI := φ.toAlgebra
  letI := hT
  letI : IsScalarTower R B ((ModuleCat.restrictScalars φ).obj Q) :=
    ⟨fun r b q ↦ mul_smul (φ r) b q⟩
  haveI : IsLocalizedModule T (LinearMap.id (R := R)
      (M := ((ModuleCat.restrictScalars φ).obj Q : Type u))) :=
    isLocalizedModule_id T _ B
  (IsLocalizedModule.isBaseChange T B (LinearMap.id (R := R)
    (M := ((ModuleCat.restrictScalars φ).obj Q : Type u)))).equiv.toModuleIso

/-- **Base change to a localization is harmless on a module that already lives over the
retraction.** Let `B` be a localization of `R` through `φ`, let `ψ : R → A` be a second ring map
and let `d : B → A` satisfy `ψ = d ∘ φ`. Then for every `A`-module `P` the base change to `B` of
`P` read over `R` through `ψ` is `P` read over `B` through `d`. -/
noncomputable def localizationBaseChangeRestrictIso {A : Type u} [CommRing A] (φ : R →+* B)
    (T : Submonoid R) (hT : letI := φ.toAlgebra; IsLocalization T B) (ψ : R →+* A)
    (d : B →+* A) (hd : ψ = d.comp φ) (P : ModuleCat.{u} A) :
    (ModuleCat.extendScalars φ).obj ((ModuleCat.restrictScalars ψ).obj P) ≅
      (ModuleCat.restrictScalars d).obj P :=
  (ModuleCat.extendScalars φ).mapIso (ModuleCat.restrictScalarsComp'App φ d ψ hd P) ≪≫
    localizationBaseChangeIso φ T hT ((ModuleCat.restrictScalars d).obj P)

end Localized

section Stalk

attribute [local instance] exteriorModule diagonalAlgebra diagonalModule diagonalIsScalarTower

variable {k A B : Type u} [Field k] [CommRing A] [Algebra k A] [CommRing B]

/-- **Reduction to the diagonal over a localization of `A ⊗[k] A`, in all degrees
(Stacks 0B0T part (1) at the local rings of `X × X`).** Let `k` be a field, `A` a commutative
`k`-algebra, and let `B` be a localization of `A ⊗[k] A` through `φ` which carries a retraction
`d : B → A` of the multiplication map, `lmul' = d ∘ φ`. Then for `A`-modules `M`, `N` and every
degree `i` there is an isomorphism of `B`-modules

`Tor_i^B(A, B ⊗_{A ⊗[k] A} (M ⊗[k] N)) ≅ Tor_i^A(M, N)`,

both `A`-modules being read over `B` through `d`. -/
noncomputable def diagonalTorLocalizedIso (φ : A ⊗[k] A →+* B) (T : Submonoid (A ⊗[k] A))
    (hT : letI := φ.toAlgebra; IsLocalization T B) (d : B →+* A)
    (hd : (Algebra.TensorProduct.lmul' k (S := A)).toRingHom = d.comp φ) (i : ℕ)
    (M N : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] :
    ((Tor (ModuleCat.{u} B) i).obj
          ((ModuleCat.restrictScalars d).obj (ModuleCat.of A A))).obj
        ((ModuleCat.extendScalars φ).obj (extObj (k := k) M N)) ≅
      (ModuleCat.restrictScalars d).obj
        (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj (ModuleCat.of A N)) :=
  letI := φ.toAlgebra
  letI := hT
  haveI : Module.Flat (A ⊗[k] A) B := IsLocalization.flat B T
  (((Tor (ModuleCat.{u} B) i).mapIso
        (localizationBaseChangeRestrictIso φ T hT
          (Algebra.TensorProduct.lmul' k (S := A)).toRingHom d hd (ModuleCat.of A A))).app
      ((ModuleCat.extendScalars φ).obj (extObj (k := k) M N))).symm ≪≫
    (torBaseChangeIsoOfUniverse (S := A ⊗[k] A) (S' := B) i (ModuleCat.of (A ⊗[k] A) A)
      (extObj (k := k) M N)).symm ≪≫
    (ModuleCat.extendScalars φ).mapIso (diagonalTorIso i M N) ≪≫
    localizationBaseChangeRestrictIso φ T hT
      (Algebra.TensorProduct.lmul' k (S := A)).toRingHom d hd
      (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj (ModuleCat.of A N))

end Stalk

end Stacks.Intersection.Diagonal

end
