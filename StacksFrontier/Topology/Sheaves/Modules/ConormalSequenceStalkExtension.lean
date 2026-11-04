module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksFrontier.Topology.Sheaves.Modules.TensorDifferentialsSheafStalk

/-!
# The conormal sequence of a locally surjective morphism is stalkwise a cotangent complex

Let `a : R ⟶ A` be a morphism of sheaves of commutative rings on a topological space `X`, let
`φ : A ⟶ B` be a locally surjective one and let `x` be a point of `X`.  The surjection
`Aₓ → Bₓ` on stalks is an extension of `Bₓ` over `Rₓ` in the sense of
`Algebra.Extension`, and the stalk at `x` of the left-hand map of the conormal sequence of `φ`
is the cotangent complex of that extension.

## Main definitions

* `Stacks.Sites.Conormal.stalkExtension`: the extension `Aₓ → Bₓ` of `Bₓ` over `Rₓ`, whose
  underlying ring is the stalk of `A`.
* `Stacks.Sites.Conormal.stalkQuotientLinearEquiv`: the identification `Aₓ/Iₓ ≅ Bₓ`, as an
  `Aₓ`-linear equivalence.
* `Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv`: the identification of the stalk of
  `B ⊗[A] Ω[A/R]` with the cotangent space of the extension.
* `Stacks.Sites.Conormal.stalkExtensionHom`: the morphism of stalk extensions induced by a
  morphism `A₁ ⟶ A₂` of two such presentations of `B`.

## Main results

* `Stacks.Sites.Conormal.stalkExtension_ker`: the kernel of the extension is the kernel `Iₓ` of
  the map on stalks.
* `Stacks.Sites.Conormal.conormalSequenceStalkMapF_eq_cotangentComplex`: under the
  identifications `Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv` and
  `Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv`, the stalk of the left-hand map of the
  conormal sequence is the cotangent complex of the extension.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS)
* [Stacks Project, Tag 07BM](https://stacks.math.columbia.edu/tag/07BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.Sites.Conormal

open Stacks.RelativeDifferentialStalk (algebraStalk)

/-! ### The quotient of the stalk by the kernel -/

section Quotient

variable {X : TopCat.{u}} {A B : X.Presheaf CommRingCat.{u}} (φ : A ⟶ B) (x : X)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]

/-- **The identification `Aₓ/Iₓ ≅ Bₓ` is an isomorphism of `Aₓ`-algebras.**  Both sides carry
the action of `Aₓ` through the surjection `Aₓ → Bₓ`. -/
def stalkQuotientAlgEquiv :
    letI := algebraStalk φ x
    (ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ≃ₐ[ToType (A.stalk x)] ToType (B.stalk x) :=
  letI := algebraStalk φ x
  { stalkQuotientRingEquiv φ x with commutes' := fun _ ↦ rfl }

/-- The identification `Aₓ/Iₓ ≅ Bₓ`, as an `Aₓ`-linear equivalence. -/
def stalkQuotientLinearEquiv :
    letI := algebraStalk φ x
    (ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ≃ₗ[ToType (A.stalk x)] ToType (B.stalk x) :=
  letI := algebraStalk φ x
  (stalkQuotientAlgEquiv φ x).toLinearEquiv

/-- The identification `Aₓ/Iₓ ≅ Bₓ` carries the class of `y` to its image in `Bₓ`. -/
@[simp]
theorem stalkQuotientLinearEquiv_mk (y : ToType (A.stalk x)) :
    letI := algebraStalk φ x
    stalkQuotientLinearEquiv φ x (Ideal.Quotient.mk (stalkKernelIdeal φ x) y) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom y := rfl

end Quotient

/-! ### Composites of maps on stalks -/

section Functorial

variable {X : TopCat.{u}} {O₁ O₂ O₃ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- Taking stalks turns a commuting triangle of morphisms of sheaves of commutative rings into a
commuting triangle of ring homomorphisms. -/
theorem stalkFunctor_map_comp_apply (f : O₁ ⟶ O₂) (g : O₂ ⟶ O₃) (k : O₁ ⟶ O₃) (hk : f ≫ g = k)
    (x : X) (y : ToType (TopCat.Presheaf.stalk O₁.obj x)) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map g.hom).hom
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.hom).hom y) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map k.hom).hom y :=
  congr($(congrArg CommRingCat.Hom.hom
    (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map_comp f.hom g.hom).symm.trans
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).congr_map
        (Sheaf.hom_ext_iff.mp hk)))) y)

end Functorial

/-! ### The extension given by the map on stalks -/

section Extension

variable {X : TopCat.{u}} (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : R ⟶ A) (φ : A ⟶ B) (c : R ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- The algebra structure on the stalk of `B` over the stalk of `R` induced by `c : R ⟶ B`. -/
abbrev stalkAlgebraBase :
    Algebra (ToType (TopCat.Presheaf.stalk R.obj x)) (ToType (TopCat.Presheaf.stalk B.obj x)) :=
  algebraStalk c.hom x

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] in
/-- The stalks of `R`, `A` and `B` form a tower, because taking stalks is functorial. -/
theorem stalkIsScalarTower (hc : a ≫ φ = c) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    letI := stalkAlgebraBase R B c x
    IsScalarTower (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk A.obj x)) (ToType (TopCat.Presheaf.stalk B.obj x)) :=
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  let := stalkAlgebraBase R B c x
  IsScalarTower.of_algebraMap_eq fun y ↦ (stalkFunctor_map_comp_apply a φ c hc x y).symm

/-- **The map on stalks as an extension.**  For a locally surjective `φ : A ⟶ B` and a morphism
`a : R ⟶ A`, the surjection `Aₓ → Bₓ` presents `Bₓ` as a quotient of the `Rₓ`-algebra `Aₓ`. -/
def stalkExtension (hc : a ≫ φ = c) :
    letI := stalkAlgebraBase R B c x
    Algebra.Extension.{u} (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) :=
  letI := stalkAlgebraBase R B c x
  { Ring := ToType (TopCat.Presheaf.stalk A.obj x)
    commRing := inferInstance
    algebra₁ := algebraStalk a.hom x
    algebra₂ := algebraStalk φ.hom x
    isScalarTower := stalkIsScalarTower R A B a φ c x hc
    σ := Function.surjInv (stalkMap_surjective φ.hom x)
    algebraMap_σ := fun y ↦ Function.surjInv_eq (stalkMap_surjective φ.hom x) y }

/-- The underlying ring of the extension is the stalk of `A`. -/
theorem stalkExtension_ring (hc : a ≫ φ = c) :
    letI := stalkAlgebraBase R B c x
    (stalkExtension R A B a φ c x hc).Ring = ToType (TopCat.Presheaf.stalk A.obj x) := rfl

/-- The kernel of the extension is the kernel `Iₓ` of the map on stalks. -/
theorem stalkExtension_ker (hc : a ≫ φ = c) :
    letI := stalkAlgebraBase R B c x
    (stalkExtension R A B a φ c x hc).ker = stalkKernelIdeal φ.hom x := rfl

/-- The cotangent module of the extension is the conormal module `Iₓ/Iₓ²`. -/
theorem stalkExtension_cotangent (hc : a ≫ φ = c) :
    letI := stalkAlgebraBase R B c x
    (stalkExtension R A B a φ c x hc).Cotangent = (stalkKernelIdeal φ.hom x).Cotangent := rfl

/-- The cotangent space of the extension is `Bₓ ⊗[Aₓ] Ω[Aₓ/Rₓ]`. -/
theorem stalkExtension_cotangentSpace (hc : a ≫ φ = c) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    letI := stalkAlgebraBase R B c x
    (stalkExtension R A B a φ c x hc).CotangentSpace =
      (ToType (TopCat.Presheaf.stalk B.obj x) ⊗[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))) := rfl

/-! ### The cotangent space and the tensor-differentials sheaf -/

section Kaehler

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- **The stalk of `B ⊗[A] Ω[A/R]` is the cotangent space of the extension.**  The stalk is
`(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]` and the identification `Aₓ/Iₓ ≅ Bₓ` turns it into
`Bₓ ⊗[Aₓ] Ω[Aₓ/Rₓ]`. -/
def cotangentSpaceStalkLinearEquiv :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A.obj x)]
      (ToType (TopCat.Presheaf.stalk B.obj x) ⊗[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))) :=
  letI := algebraStalk a.hom x
  letI := algebraStalk φ.hom x
  (tensorDifferentialsSheafStalkLinearEquiv R A B a φ x).trans
    (TensorProduct.congr (stalkQuotientLinearEquiv φ.hom x)
      (LinearEquiv.refl (ToType (TopCat.Presheaf.stalk A.obj x))
        (KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x)))))

/-- **The stalk of the left-hand map of the conormal sequence is the cotangent complex of the
extension.**  Both send the conormal class of `y ∈ Iₓ` to `1 ⊗ d y`. -/
theorem conormalSequenceStalkMapF_eq_cotangentComplex (hc : a ≫ φ = c)
    (y : stalkKernelIdeal φ.hom x) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    letI := stalkAlgebraBase R B c x
    cotangentSpaceStalkLinearEquiv R A B a φ x
        (conormalSequenceStalkMapF R A B a φ x
          ((conormalSheafStalkLinearEquiv A B φ x).symm
            ((stalkKernelIdeal φ.hom x).toCotangent y))) =
      (stalkExtension R A B a φ c x hc).cotangentComplex (Algebra.Extension.Cotangent.mk y) := by
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  let := stalkAlgebraBase R B c x
  let e := LinearEquiv.refl (ToType (TopCat.Presheaf.stalk A.obj x))
    (KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk A.obj x)))
  refine (congrArg (TensorProduct.congr (stalkQuotientLinearEquiv φ.hom x) e)
    (conormalSequenceStalkMapF_toCotangent R A B a φ x y)).trans <|
    (TensorProduct.congr_tmul (stalkQuotientLinearEquiv φ.hom x) e 1 _).trans ?_
  exact congrArg (fun b : ToType (TopCat.Presheaf.stalk B.obj x) ↦
      b ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x)) (y : ToType (TopCat.Presheaf.stalk A.obj x)))
    (map_one (stalkQuotientRingEquiv φ.hom x))

end Kaehler

end Extension

/-! ### Morphisms of extensions from morphisms of presentations -/

section Comparison

variable {X : TopCat.{u}} (R A₁ A₂ B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (c : R ⟶ B) (h : A₁ ⟶ A₂)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] (x : X)

/-- **A morphism of presentations induces a morphism of the stalk extensions.**  For
`h : A₁ ⟶ A₂` compatible with the structural morphisms from `R` and with the surjections onto
`B`, the stalk of `h` at `x` is a morphism of the extensions of `Bₓ` over `Rₓ` given by `φ₁` and
`φ₂`. -/
def stalkExtensionHom (hc₁ : a₁ ≫ φ₁ = c) (hc₂ : a₂ ≫ φ₂ = c) (ha : a₁ ≫ h = a₂)
    (hφ : h ≫ φ₂ = φ₁) :
    letI := stalkAlgebraBase R B c x
    (stalkExtension R A₁ B a₁ φ₁ c x hc₁).Hom (stalkExtension R A₂ B a₂ φ₂ c x hc₂) :=
  letI := stalkAlgebraBase R B c x
  { toRingHom := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map h.hom).hom
    toRingHom_algebraMap := stalkFunctor_map_comp_apply a₁ h a₂ ha x
    algebraMap_toRingHom := stalkFunctor_map_comp_apply h φ₂ φ₁ hφ x }

/-- The underlying ring homomorphism of the induced morphism of extensions is the stalk of
`h`. -/
theorem stalkExtensionHom_toRingHom (hc₁ : a₁ ≫ φ₁ = c) (hc₂ : a₂ ≫ φ₂ = c) (ha : a₁ ≫ h = a₂)
    (hφ : h ≫ φ₂ = φ₁) :
    letI := stalkAlgebraBase R B c x
    (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ).toRingHom =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map h.hom).hom := rfl

end Comparison

end Stacks.Sites.Conormal

end

end
