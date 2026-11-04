module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicStalk

/-!
# The fibre of `ℒ_ξ` at the generic point of a prime divisor

Let `X` be a decent algebraic space over `S`, let `Z ⊆ X` be a prime divisor with generic point
`ξ`, write `B = 𝒪^h_{X, ξ}` for the henselian local ring there and let `ℒ` be an `𝒪_X`-module.
The canonical morphism `c_ξ : Spec(B) ⟶ X` of Stacks 0ENK pulls `ℒ` back to `ℒ_ξ = c_ξ^*ℒ`, a
`B`-module.  Section 72.8 of the source, having chosen a generator `t_ξ` of `ℒ_ξ`, passes to the
*fibre*

`ℒ_ξ ⊗_B κ(ξ)`,

and calls the image of `t_ξ` there `t_ξ|_Z`.  This file builds that fibre and that image, and
proves the two properties the source uses: the image of a generator is nonzero, and it generates
the fibre as a `κ(ξ)`-vector space.  So the fibre is the one-dimensional `κ(ξ)`-vector space with
basis `t_ξ|_Z`, and `t_ξ|_Z ≠ 0`.

The residue field `κ(ξ)` is read here as the residue field of `B`.  By Stacks 0EN0,
`AlgebraicGeometry.Space.exists_residueFieldEquiv_residueField`, that field is the residue field
of `X` at `ξ`, which — `ξ` being the generic point of the integral closed subspace `Z` — is the
function field of `Z`; this is why the source can read `t_ξ|_Z` as a meromorphic section of
`ℒ|_Z`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericModuleFibre` is the fibre `ℒ_ξ ⊗_B κ(ξ)`, as a
  `κ(ξ)`-module.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction` is the reduction
  `ℒ_ξ ⟶ ℒ_ξ ⊗_B κ(ξ)`, `t_ξ ↦ t_ξ|_Z`, as a map of `B`-modules.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction_ne_zero`: the reduction of a
  nonzero generator of `ℒ_ξ` is nonzero.  This is the source's "its image in the fibre is a
  *nonzero* meromorphic section".
* `AlgebraicGeometry.Space.PrimeDivisor.span_genericFibreReduction_eq_top`: the reduction of a
  generator of `ℒ_ξ` generates the fibre over `κ(ξ)`.

## Implementation notes

The fibre is taken as `κ(ξ) ⊗_B ℒ_ξ` rather than `ℒ_ξ ⊗_B κ(ξ)`, so that the `κ(ξ)`-module
structure is the one `Mathlib.LinearAlgebra.TensorProduct` puts on a tensor product whose left
factor is a `κ(ξ)`-module; the two are exchanged by `TensorProduct.comm` and the source's order
is the other one.

That the reduction of a generator is nonzero is elementary and does not need Nakayama's lemma:
`1 ⊗ t` vanishes exactly when `t ∈ 𝔪_B ℒ_ξ`, and with `ℒ_ξ = B t` that says `t = y t` for some
`y ∈ 𝔪_B`, whence `(1 - y) t = 0` with `1 - y` a unit of the local ring `B`, so `t = 0`.

The module `ℒ` ranges over `Modules.{u, u}`, as for
`AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalk`: the pullback of modules of Stacks
03LU exists only at the module universe of the structure rings, and so therefore does `ℒ_ξ`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point))
    R]
  (hR : B.Contains (Spec (.of R)))

/-- **The fibre `ℒ_ξ ⊗_B κ(ξ)` of `ℒ_ξ` at the generic point of a prime divisor**, where
`B = 𝒪^h_{X, ξ}` and `κ(ξ)` is its residue field, as a `κ(ξ)`-module.

By Stacks 0EN0 the field `κ(ξ)` is the residue field of `X` at `ξ`, hence the function field of
`Z`. -/
abbrev PrimeDivisor.genericModuleFibre (L : Modules.{u, u} B S hS X hX) : Type u :=
  IsLocalRing.ResidueField R ⊗[R] (Z.genericModuleStalk B S hS hX hdec R hR L)

/-- **The reduction `ℒ_ξ ⟶ ℒ_ξ ⊗_B κ(ξ)`, `t_ξ ↦ t_ξ|_Z`**, of Section 72.8 of the source: a
section of `ℒ_ξ = c_ξ^*ℒ` on `Spec(𝒪^h_{X, ξ})` is sent to its image `1 ⊗ t_ξ` in the fibre at
the closed point. -/
def PrimeDivisor.genericFibreReduction (L : Modules.{u, u} B S hS X hX) :
    Z.genericModuleStalk B S hS hX hdec R hR L →ₗ[R]
      Z.genericModuleFibre B S hS hX hdec R hR L :=
  TensorProduct.mk R (IsLocalRing.ResidueField R)
    (Z.genericModuleStalk B S hS hX hdec R hR L) 1

omit [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point))
    R] in
/-- The reduction of a section of `ℒ_ξ` to the fibre is the pure tensor `1 ⊗ t_ξ`. -/
@[simp]
theorem PrimeDivisor.genericFibreReduction_apply (L : Modules.{u, u} B S hS X hX)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L) :
    Z.genericFibreReduction B S hS hX hdec R hR L t =
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] t :=
  rfl

omit [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point))
    R] in
/-- **The reduction `t_ξ|_Z` of a nonzero generator `t_ξ` of `ℒ_ξ` is nonzero**: the image of a
nonzero generator of `ℒ_ξ` in the fibre `ℒ_ξ ⊗_B κ(ξ)` is a nonzero section. -/
theorem PrimeDivisor.genericFibreReduction_ne_zero (L : Modules.{u, u} B S hS X hX)
    {t : Z.genericModuleStalk B S hS hX hdec R hR L}
    (hspan : Submodule.span R {t} = ⊤) (ht : t ≠ 0) :
    Z.genericFibreReduction B S hS hX hdec R hR L t ≠ 0 := by
  intro h
  have hone : ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] t) = 0 := h
  have hquot : Submodule.Quotient.mk
      (p := IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Z.genericModuleStalk B S hS hX hdec R hR L))) t = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (IsLocalRing.maximalIdeal R) t, hone,
      map_zero]
  rw [Submodule.Quotient.mk_eq_zero, ← hspan, Submodule.mem_smul_span_singleton] at hquot
  obtain ⟨y, hy, hyt⟩ := hquot
  have hzero : (1 - y) • t = 0 := by rw [sub_smul, one_smul, hyt, sub_self]
  obtain ⟨v, hv⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits y
    ((IsLocalRing.mem_maximalIdeal y).mp hy)
  exact ht (((IsUnit.smul_eq_zero ⟨v, hv⟩).mp hzero))

omit [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point))
    R] in
/-- **The reduction `t_ξ|_Z` of a generator `t_ξ` of `ℒ_ξ` generates the fibre over `κ(ξ)`.**
Together with `AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction_ne_zero` this says
that for a nonzero generator the fibre is the one-dimensional `κ(ξ)`-vector space with basis
`t_ξ|_Z`, which is how Section 72.8 of the source reads it. -/
theorem PrimeDivisor.span_genericFibreReduction_eq_top (L : Modules.{u, u} B S hS X hX)
    {t : Z.genericModuleStalk B S hS hX hdec R hR L}
    (hspan : Submodule.span R {t} = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
        {Z.genericFibreReduction B S hS hX hdec R hR L t} = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m =>
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
        (hspan.ge (Submodule.mem_top :
          m ∈ (⊤ : Submodule R (Z.genericModuleStalk B S hS hX hdec R hR L))))
      refine Submodule.mem_span_singleton.mpr
        ⟨algebraMap R (IsLocalRing.ResidueField R) r * a, ?_⟩
      rw [PrimeDivisor.genericFibreReduction_apply, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one, ← hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Generic

end AlgebraicGeometry.Space

end
