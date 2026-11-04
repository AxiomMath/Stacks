module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFirstProjectionFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomBasePoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.BaseChange

/-!
# The fundamental group of a geometric fibre of the first projection of Laumon's plane

Let `pr₁ : 𝔸² = Spec k'[x][t] → 𝔸¹_x` be the first projection of the plane of Laumon's argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) and `u : Spec Ω[t] → 𝔸²` its fibre over a
point `Spec φ : Spec Ω → 𝔸¹_x`, `Ω` separably closed
(`Stacks.EtaleCohomology.isPullback_laumonFamilyPr₁_fibre`). For a geometric point `ȳ` of the fibre
and a change of base point `t : F_z̄ ≅ F_{u(ȳ)}` on `𝔸²`, write `Φ = φ_t ∘ u_* : π₁(Spec Ω[t], ȳ) →
π₁(𝔸², z̄)`. Then:

* `pr₁_* ∘ Φ` is trivial
  (`Stacks.EtaleCohomology.etaleFundamentalGroupMap_laumonFamilyPr₁_fibre_eq_one`): `u ≫ pr₁`
  factors through `Spec Ω`, whose fundamental group is trivial (Tag 0BSV), and homomorphisms
  induced by equal morphisms are inner conjugate;
* the character of the Artin–Schreier cover of `g ∈ k'[x][t]` composed with `Φ` is the character
  of the Artin–Schreier cover of `φ[t](g)` on the fibre
  (`Stacks.EtaleCohomology.torsorCover_character_laumonFamily_fibre`), by the invariance of the
  character of a torsor under induced homomorphisms and its compatibility with base change.

So on the fibre over `x̄` the representation `pr₁^*σ₁ ⊗ ψ'(-χ_g)` of the family sheaf becomes the
character `ψ'(-χ_{h(x̄) t})` of the fibre.

## Main results

* `Stacks.EtaleCohomology.etaleFundamentalGroupMap_laumonFamilyPr₁_fibre_eq_one`.
* `Stacks.EtaleCohomology.torsorCover_character_laumonFamily_fibre`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

variable (k' : Type u) [Field k'] {Ω : Type u} [Field Ω] (φ : Polynomial k' →+* Ω)

/-- **The fundamental group of a separably closed field is trivial** (Tag 0BSV for the field
`Ω`, a henselian local ring with separably closed residue field). -/
theorem subsingleton_etaleFundamentalGroup_spec_of_isSepClosed [IsSepClosed Ω]
    (x : GeometricPoint (Spec (.of Ω))) :
    Subsingleton (EtaleFundamentalGroup (Spec (.of Ω)) x) := by
  have : IsSepClosed (IsLocalRing.ResidueField Ω) := IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective (IsLocalRing.residue Ω)
      ⟨(IsLocalRing.residue Ω).injective, Ideal.Quotient.mk_surjective⟩).symm
  exact subsingleton_etaleFundamentalGroup_of_isSepClosed_residueField Ω x

/-- **`pr₁_*` kills the fundamental group of a geometric fibre of `pr₁`**: for the fibre
`u : Spec Ω[t] → 𝔸²` over `Spec φ`, `Ω` separably closed, and a change of base point
`t : F_z̄ ≅ F_{u(ȳ)}`, the composite `π₁(Spec Ω[t], ȳ) → π₁(𝔸², z̄) → π₁(𝔸¹_x, pr₁(z̄))` is
trivial. -/
theorem etaleFundamentalGroupMap_laumonFamilyPr₁_fibre_eq_one [IsSepClosed Ω]
    (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    {z : GeometricPoint (Spec (.of (Polynomial (Polynomial k'))))}
    (t : finiteEtaleFiberFunctor z ≅
      finiteEtaleFiberFunctor (y.map (Spec.map (CommRingCat.ofHom (mapRingHom φ)))))
    (γ : EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y) :
    etaleFundamentalGroupMap (laumonFamilyPr₁ k') z (etaleFundamentalGroupBasePointHom t
      (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (mapRingHom φ))) y γ)) = 1 := by
  let uφ := Spec.map (CommRingCat.ofHom (mapRingHom φ))
  let f' : Spec (.of (Polynomial Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))
  let s : Spec (.of Ω) ⟶ Spec (.of (Polynomial k')) := Spec.map (CommRingCat.ofHom φ)
  have hsq : uφ ≫ laumonFamilyPr₁ k' = f' ≫ s := (isPullback_laumonFamilyPr₁_fibre k' φ).w
  obtain ⟨t₂⟩ := nonempty_finiteEtaleFiberFunctorIso (x := z.map (laumonFamilyPr₁ k'))
    (x' := (y.map f').map s)
  have h₁ := ((isEtaleFundamentalGroupHomInducedBy_map uφ y).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z)
  have h₂ := ((isEtaleFundamentalGroupHomInducedBy_map f' y).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_map s (y.map f'))).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₂)
  obtain ⟨g, hg⟩ := h₂.isInnerConjugate_of_eq h₁ (by
    rw [Category.comp_id, Category.comp_id, hsq])
  have := subsingleton_etaleFundamentalGroup_spec_of_isSepClosed (y.map f')
  refine (hg γ).trans ?_
  change g * (etaleFundamentalGroupBasePointHom t₂) ((etaleFundamentalGroupMap s (y.map f'))
    ((etaleFundamentalGroupMap f' y) γ)) * g⁻¹ = 1
  rw [show etaleFundamentalGroupMap f' y γ = 1 from Subsingleton.elim _ _, map_one, map_one,
    mul_one, mul_inv_cancel]

variable {k'} [Fintype k'] [Algebra k' Ω] (hφ : ∀ a : k', φ (C a) = algebraMap k' Ω a)

/-- `φ[t] : k'[x][t] → Ω[t]` as a homomorphism of `k'`-algebras, when `φ` restricts to the
structure map on the constants. -/
public def laumonFibreMapAlgHom : Polynomial (Polynomial k') →ₐ[k'] Polynomial Ω :=
  { mapRingHom φ with
    commutes' := fun a => by
      change mapRingHom φ (C (C a)) = C (algebraMap k' Ω a)
      rw [coe_mapRingHom, map_C, hφ] }

include hφ in
/-- **The Artin–Schreier character of `g` on a geometric fibre of `pr₁`**: composed with
`Φ = φ_t ∘ u_*`, the character of the Artin–Schreier cover of `g ∈ k'[x][t]` is the character of
the Artin–Schreier cover of `φ[t](g)` on `Spec Ω[t]`, for any points of the fibres. -/
theorem torsorCover_character_laumonFamily_fibre (g : Polynomial (Polynomial k'))
    (g' : Polynomial Ω)
    (hg : mapRingHom φ g = g') (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    {z : GeometricPoint (Spec (.of (Polynomial (Polynomial k'))))}
    (t : finiteEtaleFiberFunctor z ≅
      finiteEtaleFiberFunctor (y.map (Spec.map (CommRingCat.ofHom (mapRingHom φ)))))
    (p₀ : (finiteEtaleFiberFunctor z).obj (cover k' (Polynomial (Polynomial k')) g))
    (p : (finiteEtaleFiberFunctor y).obj (cover k' (Polynomial Ω) g'))
    (γ : EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y) :
    (torsorCover k' (Polynomial (Polynomial k')) g).character z p₀
      (etaleFundamentalGroupBasePointHom t
        (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (mapRingHom φ))) y γ)) =
      (torsorCover k' (Polynomial Ω) g').character y p γ := by
  subst hg
  let φA := laumonFibreMapAlgHom φ hφ
  let uφ := Spec.map (CommRingCat.ofHom (mapRingHom φ))
  have h₁ := (isEtaleFundamentalGroupHomInducedBy_map uφ y).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)
  exact ((isEtaleFundamentalGroupHomInducedBy_map uφ y).character_eq_of_eq
    (torsorCover k' (Polynomial (Polynomial k')) g) h₁ (Category.comp_id _).symm
    (finiteEtaleFiberProjection uφ y (cover k' (Polynomial (Polynomial k')) g)
      ((finiteEtaleFiberFunctor y).map (coverBaseChangeHom k' g φA) p)) p₀ γ).trans
    (torsorCover_character_map k' g φA y p γ).symm

end Stacks.EtaleCohomology

end
