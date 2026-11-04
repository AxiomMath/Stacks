module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelChart
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapSubscheme

/-!
# The infinitesimal neighbourhoods of the non-algebraizable example are the level schemes

For `A = k[x,y][[t]]`, `I = (t)` and `U` the punctured spectrum of `A`, the closed subscheme of
`U` cut out by the `n`-th power of `I𝒪_U` is the punctured spectrum of `A/tⁿA`, compatibly with
the two structure morphisms to `U`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.ker_levelToAmbient` — the kernel ideal sheaf of
  the closed immersion `Spec(A/tⁿA) ⟶ Spec(A)` is the `n`-th power of the ideal sheaf of `(t)`.
* `Stacks.Algebraization.NonAlgebraizableExample.idealOnOpen_pow_eq_comap_ker` — hence the `n`-th
  power of `I𝒪_U` is the restriction of that kernel to `U`.
* `Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen` — the closed
  subscheme of `U` it cuts out is `levelOpen`, compatibly with the structure morphisms to `U`.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The structure map `Spec(A/tⁿA) ⟶ Spec(A)` is a closed immersion. -/
public instance isClosedImmersion_levelToAmbient (n : ℕ) :
    IsClosedImmersion (levelToAmbient k n) :=
  IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of (AmbientRing k)) ((idealT k) ^ n)

/-- The kernel of the map `Γ(Spec A, ⊤) ⟶ Γ(Spec(A/tⁿA), ⊤)` on global functions is the image of
`(t)ⁿ` under the comparison of `A` with the global functions of its spectrum. -/
public theorem ker_appTop_levelToAmbient (n : ℕ) :
    RingHom.ker (levelToAmbient k n).appTop.hom =
      ((idealT k) ^ n).map
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv) := by
  have hcomap : ((idealT k) ^ n).comap
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).hom) =
      ((idealT k) ^ n).map
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv) :=
    (Ideal.map_symm
      (Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).commRingCatIsoToRingEquiv).symm
  have hinj : Function.Injective
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (levelRing k n))).hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (levelRing k n))).commRingCatIsoToRingEquiv.injective
  have h := congrArg RingHom.ker (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk ((idealT k) ^ n)))))
  simp only [CommRingCat.hom_comp] at h
  rw [RingHom.ker_comp_of_injective _ hinj, ← RingHom.comap_ker] at h
  rw [h, CommRingCat.hom_ofHom, Ideal.mk_ker, hcomap]

/-- The kernel ideal sheaf of the closed immersion `Spec(A/tⁿA) ⟶ Spec(A)` is the `n`-th power of
the ideal sheaf attached to `I = (t)`. -/
@[stacks 0EHE "Spec(A/t^n A) is the closed subscheme of Spec(A) cut out by I^n"]
public theorem ker_levelToAmbient (n : ℕ) :
    (levelToAmbient k n).ker =
      Scheme.IdealSheafData.ofIdealTop ((idealT k).map
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv)) ^ n := by
  rw [Scheme.ker_of_isAffine, ker_appTop_levelToAmbient, Ideal.map_pow,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_pow]

/-- The `n`-th power of the ideal sheaf `I𝒪_U` on the punctured spectrum of `A` is the
restriction to `U` of the ideal sheaf cutting out `Spec(A/tⁿA)` in `Spec(A)`. -/
@[stacks 0EHE "(I O_U)^n is the restriction to U of the ideal sheaf of Spec(A/t^n A)"]
public theorem idealOnOpen_pow_eq_comap_ker (n : ℕ) :
    idealOnOpen (situation k) ^ n = (levelToAmbient k n).ker.comap (situation k).U.ι :=
  (Stacks.IdealSheaf.comap_pow _ (situation k).U.ι n).symm.trans
    (congrArg (fun K => Scheme.IdealSheafData.comap K (situation k).U.ι)
      (ker_levelToAmbient k n).symm)

/-- The closed subscheme of the punctured spectrum `U` of `A` cut out by the `n`-th power of
`I𝒪_U` is the punctured spectrum of `A/tⁿA`, compatibly with the two morphisms to `U`: the closed
immersion of the subscheme and the structure map
`Stacks.Algebraization.NonAlgebraizableExample.levelStructureMap`. -/
@[stacks 0EHE "V((I O_U)^n) is the punctured spectrum of A/t^n A"]
public theorem exists_subschemeIso_levelOpen (n : ℕ) :
    ∃ e : (idealOnOpen (situation k) ^ n).subscheme ≅ (levelOpen k n).toScheme,
      e.hom ≫ levelStructureMap k n = (idealOnOpen (situation k) ^ n).subschemeι :=
  Scheme.IdealSheafData.exists_subschemeIso_resLE (levelToAmbient k n)
    (preimage_U_levelToAmbient k n) (idealOnOpen_pow_eq_comap_ker k n)

end Stacks.Algebraization.NonAlgebraizableExample

end
