module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.SymmetricQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationLocallySurjective
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass

/-!
# The normal cone inside the vector bundle of a virtual normal bundle

Let `i : Z ⟶ X` be an immersion of schemes and `𝒩` a virtual normal bundle for `i`
(Stacks 0FBQ): a finite locally free `𝒪_Z`-module with a surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}`. Write
`N = 𝐕(𝒩^∨) = Spec_Z(Sym(𝒩^∨))`. The construction preceding Stacks 0FBK uses the canonical
closed immersions

  `C_ZX ⟶ N_ZX ⟶ N`,

the first being Divisors, Equation 0637 — the relative spectrum of the surjection
`Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks 0632 — and the second the relative spectrum of the surjection
`Sym(𝒩^∨) ⟶ Sym(𝒞_{Z/X})` induced by `σ`. This file proves that both are closed immersions and
assembles the composite `C_ZX ⟶ N` over `Z`.

The conormal sheaf in the definition of a virtual normal bundle is
`Stacks.Thickenings.immersionConormalSheaf`, the pullback of the categorical kernel of
`𝒪 ⟶ i_* 𝒪_Z` along the closed factor of `i`; the normal bundle is built from the degree-one
piece `𝒞_{Z/X,1}` of the conormal algebra. The two are identified by the degree-one
identification of Stacks 0632 (`Stacks.Conormal.conormalDegreeOneIso`).

## Main definitions

* `Stacks.Conormal.immersionConormalSheafIsoDegreeOne` — `𝒞_{Z/X} ≅ 𝒞_{Z/X,1}`.
* `Stacks.Chow.VirtualNormalBundle.bundleEmbedding` — the closed immersion `N_ZX ⟶ N`.
* `Stacks.Chow.VirtualNormalBundle.coneEmbedding` — the closed immersion `C_ZX ⟶ N` over `Z`.

## Main results

* `Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle` — **`C_ZX ⟶ N_ZX` is a closed
  immersion.**

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- Every homogeneous component of the canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is locally
surjective: in negative degrees the target vanishes, in nonnegative degrees this is
`Stacks.Conormal.isLocallySurjective_conormalSymmetricHom_app`. -/
theorem isLocallySurjective_conormalSymmetricHom_app_int (n : ℤ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((conormalSymmetricHom i).app n).val) := by
  rcases lt_or_ge n 0 with hn | hn
  · refine Presheaf.isLocallySurjective_of_surjective _ _ ?_
    intro W y
    refine ⟨0, ?_⟩
    have hsub : Subsingleton ↥(((conormalAlgebra i).algebra.piece n).val.obj W) :=
      Stacks.subsingleton_of_isZero ((conormalAlgebra i).negative_isZero n hn) W
    exact @Subsingleton.elim _ hsub _ _
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact isLocallySurjective_conormalSymmetricHom_app i m

/-- **Divisors, Equation 0637: the canonical morphism `C_ZX ⟶ N_ZX` is a closed immersion**, the
relative spectrum of the surjection `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks 0632. -/
instance isClosedImmersion_normalConeToNormalBundle :
    IsClosedImmersion (normalConeToNormalBundle i) :=
  Stacks.RelativeSpec.isClosedImmersion_relativeSpectrumMapOfAlgebraHom_of_isLocallySurjective
    (normalBundleSituation i) (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i)
    (Stacks.RelativeSpec.isLocallySurjective_gradedAlgebraSheafMap Z (conormalSymmetricHom i)
      (Scheme.Modules.symmetricAlgebra_mul_comm Z (conormalSheafDegreeOne i))
      (conormalAlgebra i).mul_comm_int (isLocallySurjective_conormalSymmetricHom_app_int i))

/-- **The conormal sheaf of an immersion is the degree-one piece of its conormal algebra**: the
conormal sheaf `Stacks.Thickenings.immersionConormalSheaf` of the definition of a virtual normal
bundle is `Stacks.Conormal.conormalSheaf` (both are the pullback, along the closed factor of `i`,
of the kernel of `𝒪 ⟶ i_* 𝒪_Z`), and this is the degree-one identification of Stacks 0632. -/
def immersionConormalSheafIsoDegreeOne :
    Stacks.Thickenings.immersionConormalSheaf i ≅ conormalSheafDegreeOne i :=
  @asIso _ _ _ _ (conormalDegreeOneHom i) (conormalDegreeOneHom_isIso i)

theorem immersionConormalSheafIsoDegreeOne_hom :
    (immersionConormalSheafIsoDegreeOne i).hom = conormalDegreeOneHom i := rfl

end Stacks.Conormal

namespace Stacks.Chow.VirtualNormalBundle

open Stacks.AlgebraicGeometry.ReflexiveModules

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)

/-- The surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X,1}` onto the degree-one piece of the conormal algebra. -/
def surjectionDegreeOne : dualSheaf 𝒩.bundle ⟶ Stacks.Conormal.conormalSheafDegreeOne i :=
  𝒩.surjection ≫ (Stacks.Conormal.immersionConormalSheafIsoDegreeOne i).hom

instance epi_surjectionDegreeOne : Epi 𝒩.surjectionDegreeOne := by
  let e := Stacks.Conormal.immersionConormalSheafIsoDegreeOne i
  refine ⟨fun {W} g h hgh => ?_⟩
  have h1 : 𝒩.surjection ≫ (e.hom ≫ g) = 𝒩.surjection ≫ (e.hom ≫ h) :=
    (Category.assoc _ _ _).symm.trans (hgh.trans (Category.assoc _ _ _))
  have h2 : e.hom ≫ g = e.hom ≫ h := (cancel_epi 𝒩.surjection).1 h1
  have h3 : e.inv ≫ e.hom ≫ g = e.inv ≫ e.hom ≫ h := congrArg (fun k => e.inv ≫ k) h2
  exact (Iso.inv_hom_id_assoc e g).symm.trans (h3.trans (Iso.inv_hom_id_assoc e h))

/-- **The closed immersion `N_ZX ⟶ N`**, the relative spectrum of the surjection
`Sym(𝒩^∨) ⟶ Sym(𝒞_{Z/X})` induced by `σ`. -/
def bundleEmbedding :
    Scheme.Modules.vectorBundle Z (Stacks.Conormal.conormalSheafDegreeOne i) ⟶
      Scheme.Modules.vectorBundle Z (dualSheaf 𝒩.bundle) :=
  (Scheme.Modules.vectorBundleMap Z 𝒩.surjectionDegreeOne).left

instance isClosedImmersion_bundleEmbedding : IsClosedImmersion 𝒩.bundleEmbedding :=
  Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi 𝒩.surjectionDegreeOne

theorem bundleEmbedding_toBase :
    𝒩.bundleEmbedding ≫ Scheme.Modules.vectorBundleToBase Z (dualSheaf 𝒩.bundle) =
      Scheme.Modules.vectorBundleToBase Z (Stacks.Conormal.conormalSheafDegreeOne i) :=
  Scheme.Modules.vectorBundleMap_left_comp Z 𝒩.surjectionDegreeOne

/-- **The closed immersion `C_ZX ⟶ N`** of the construction preceding Stacks 0FBK: the canonical
closed immersion `C_ZX ⟶ N_ZX` of Divisors, Equation 0637, followed by `N_ZX ⟶ N`. -/
def coneEmbedding :
    Stacks.Conormal.normalCone i ⟶ Scheme.Modules.vectorBundle Z (dualSheaf 𝒩.bundle) :=
  Stacks.Conormal.normalConeToNormalBundle i ≫ 𝒩.bundleEmbedding

instance isClosedImmersion_coneEmbedding : IsClosedImmersion 𝒩.coneEmbedding := by
  unfold coneEmbedding
  infer_instance

/-- The closed immersion `C_ZX ⟶ N` is a morphism over `Z`. -/
theorem coneEmbedding_toBase :
    𝒩.coneEmbedding ≫ Scheme.Modules.vectorBundleToBase Z (dualSheaf 𝒩.bundle) =
      Stacks.Conormal.normalConeToBase i := by
  rw [coneEmbedding, Category.assoc, bundleEmbedding_toBase,
    Stacks.Conormal.normalConeToNormalBundle_toBase]

end Stacks.Chow.VirtualNormalBundle

end
