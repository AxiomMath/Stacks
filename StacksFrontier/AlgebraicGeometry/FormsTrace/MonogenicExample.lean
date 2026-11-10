module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.Proposition
public import StacksFrontier.RingTheory.FormsTrace.MonogenicExample
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks, Example 0FLD on the spectrum

Let `A` be a ring and `B` a finite `A`-algebra with a power basis, for instance
`B = A[x]/(f)` for a monic `f`. Then `g = Spec(A → B) : Spec B → Spec A` is finite syntomic, and
Proposition 0FLC gives the map of de Rham complexes `Θ_{Spec B/Spec A}`
(`AlgebraicGeometry.Scheme.Hom.formsTrace`). On global sections, through the identifications
`Γ(Spec R, Ω^p_{Spec R/ℤ}) = Ω^p_{Γ(Spec R, 𝒪)}`
(`AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv`) and `Γ(Spec R, 𝒪) = R`
(`AlgebraicGeometry.Scheme.ΓSpecIso`), this map is the trace map
`Θ_{B/A} = Stacks.FormsTrace.frameTrace A B` of rings
(`AlgebraicGeometry.absoluteFormsSectionsEquiv_formsTrace_app_top`). So the computations of
Example 0FLD (`StacksFrontier.RingTheory.FormsTrace.MonogenicExample`) are computations of the map
of
Proposition 0FLC.

## Main results

* `AlgebraicGeometry.isFinite_specMap_of_powerBasis`,
  `AlgebraicGeometry.syntomic_specMap_of_powerBasis`: `Spec B → Spec A` is finite syntomic.
* `AlgebraicGeometry.absoluteFormsSectionsEquiv_formsTrace_app_top`: on global sections the map of
  Proposition 0FLC is `Θ_{B/A}`.
* `AlgebraicGeometry.formsTrace_app_top_eq_frameTrace`: **Stacks, Example 0FLD**, the
  identification of the map `Θ_{B/A}` of the example with that of Proposition 0FLC.

## References

* [Stacks Project, Tag 0FLD](https://stacks.math.columbia.edu/tag/0FLD)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Polynomial KaehlerDifferential Stacks.FormsTrace

universe u

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- `Spec B → Spec A` is finite for an algebra with a power basis. -/
theorem isFinite_specMap_of_powerBasis (pb : PowerBasis A B) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : Module.Finite A B := .of_basis pb.basis
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- `Spec B → Spec A` is syntomic for an algebra with a power basis. -/
theorem syntomic_specMap_of_powerBasis (pb : PowerBasis A B) :
    Syntomic (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Syntomic), CommRingCat.hom_ofHom, RingHom.syntomic_iff,
    show (algebraMap A B).toAlgebra = ‹Algebra A B› from Algebra.algebra_ext _ _ fun _ => rfl]
  exact syntomic_of_powerBasis pb

/-- **On global sections the map of Proposition 0FLC is `Θ_{B/A}`.** Let `B` have a power basis
of positive dimension over `A` and let `g = Spec(A → B) : Spec B → Spec A`, with `A` and `B`
mapping to the global sections by the canonical isomorphisms. For a `p`-form `x` of `B`, the map
`Θ^p_{Spec B/Spec A}` of Proposition 0FLC sends the global section of `Ω^p_{Spec B/ℤ}`
corresponding to `x` to the global section of `Ω^p_{Spec A/ℤ}` corresponding to
`Θ_{B/A}(x) = frameTrace A B p x`; here `Γ(Spec R, Ω^p) = Ω^p_{Γ(Spec R, 𝒪)}` and the forms of
`R` are carried to those of `Γ(Spec R, 𝒪)` along `R ≅ Γ(Spec R, 𝒪)`. -/
theorem absoluteFormsSectionsEquiv_formsTrace_app_top (pb : PowerBasis A B) (hdim : 0 < pb.dim)
    (g : Spec (.of B) ⟶ Spec (.of A)) (hgdef : g = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    [hfin : IsFinite g] (hg : Syntomic g) [Algebra A Γ(Spec (.of A), ⊤)]
    [Algebra B Γ(Spec (.of B), g ⁻¹ᵁ ⊤)]
    (hA : algebraMap A Γ(Spec (.of A), ⊤) = (Scheme.ΓSpecIso (.of A)).inv.hom)
    (hB : algebraMap B Γ(Spec (.of B), g ⁻¹ᵁ ⊤) = (Scheme.ΓSpecIso (.of B)).inv.hom)
    (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    Scheme.absoluteFormsSectionsEquiv (Spec (.of A)) (isAffineOpen_top _) p
        ((g.formsTrace hg p).app ⊤
          ((Scheme.absoluteFormsSectionsEquiv (Spec (.of B))
              ((isAffineOpen_top _).preimage g) p).symm
            (formsMap B Γ(Spec (.of B), g ⁻¹ᵁ ⊤) p x))) =
      formsMap A Γ(Spec (.of A), ⊤) p (frameTrace A B p x) := by
  have hR : IsAffineOpen (⊤ : (Spec (.of A)).Opens) := isAffineOpen_top _
  let := (g.app ⊤).hom.toAlgebra
  let : Algebra A Γ(Spec (.of B), g ⁻¹ᵁ ⊤) :=
    ((g.app ⊤).hom.comp (algebraMap A Γ(Spec (.of A), ⊤))).toAlgebra
  let eA : A ≃+* Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let eB : B ≃+* Γ(Spec (.of B), g ⁻¹ᵁ ⊤) :=
    (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
  have heB : ∀ r, algebraMap B Γ(Spec (.of B), g ⁻¹ᵁ ⊤) r = eB r := fun r => by
    rw [hB]
    rfl
  have hcomm : ∀ r, eB (algebraMap A B r) = algebraMap _ _ (eA r) := fun r => by
    subst hgdef
    exact congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
  have : IsScalarTower A Γ(Spec (.of A), ⊤) Γ(Spec (.of B), g ⁻¹ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B Γ(Spec (.of B), g ⁻¹ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (g.app ⊤).hom (algebraMap A Γ(Spec (.of A), ⊤) r) = _
      rw [hA, heB, hcomm]
      rfl
  let pb' := powerBasisOfRingEquiv eA eB hcomm pb
  have := isPushout_of_powerBasis pb pb' rfl (heB _)
  have : NeZero pb'.dim := ⟨hdim.ne'⟩
  let F : AnyFrame Γ(Spec (.of A), ⊤) Γ(Spec (.of B), g ⁻¹ᵁ ⊤) := ⟨pb'.dim, powerBasisFrame pb' rfl⟩
  rw [g.absoluteFormsSectionsEquiv_formsTrace_app_of_frame hg p hR F.frame
      ((Scheme.absoluteFormsSectionsEquiv (Spec (.of B)) (hR.preimage g) p).symm
        (formsMap B Γ(Spec (.of B), g ⁻¹ᵁ ⊤) p x)),
    LinearEquiv.apply_symm_apply, ← frameTrace_eq F]
  exact frameTrace_formsMap_of_isPushout Γ(Spec (.of A), ⊤) Γ(Spec (.of B), g ⁻¹ᵁ ⊤)
    (subsingleton_or_nonempty_anyFrame_of_powerBasis pb) (Or.inr ⟨F⟩) p x

/-- **Stacks, Example 0FLD: the map `Θ_{B/A}` is the one of Proposition 0FLC.** Let `B` have a
power basis of positive dimension over `A`, for instance `B = A[x]/(f)` with `f` monic of degree
`d ≥ 1`. Then `Spec B → Spec A` is finite syntomic (`isFinite_specMap_of_powerBasis`,
`syntomic_specMap_of_powerBasis`), and on global sections the map of de Rham complexes
`Θ_{Spec B/Spec A}` given by `Scheme.Hom.formsTrace` is the trace map `Θ_{B/A} = frameTrace A B`
on the forms of `B`: the global section of `Ω^p_{Spec B/ℤ}` corresponding to a `p`-form `x` of `B`
goes to the global section of `Ω^p_{Spec A/ℤ}` corresponding to `Θ_{B/A}(x)` (with `A`, `B`
identified with their rings of global sections by the canonical isomorphisms). -/
@[stacks 0FLD "the map `Θ_{B/A} : Ω^•_B → Ω^•_A` of the example is the map of Proposition 0FLC \
for `Spec B → Spec A` on global sections"]
theorem formsTrace_app_top_eq_frameTrace (pb : PowerBasis A B) (hdim : 0 < pb.dim)
    [Algebra A Γ(Spec (.of A), ⊤)]
    [Algebra B Γ(Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤)]
    (hA : algebraMap A Γ(Spec (.of A), ⊤) = (Scheme.ΓSpecIso (.of A)).inv.hom)
    (hB : algebraMap B Γ(Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤) =
      (Scheme.ΓSpecIso (.of B)).inv.hom)
    (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    haveI := isFinite_specMap_of_powerBasis pb
    Scheme.absoluteFormsSectionsEquiv (Spec (.of A)) (isAffineOpen_top _) p
        (((Spec.map (CommRingCat.ofHom (algebraMap A B))).formsTrace
            (syntomic_specMap_of_powerBasis pb) p).app ⊤
          ((Scheme.absoluteFormsSectionsEquiv (Spec (.of B))
              ((isAffineOpen_top _).preimage (Spec.map (CommRingCat.ofHom (algebraMap A B))))
                p).symm
            (formsMap B Γ(Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤) p
              x))) =
      formsMap A Γ(Spec (.of A), ⊤) p (frameTrace A B p x) :=
  absoluteFormsSectionsEquiv_formsTrace_app_top pb hdim
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) rfl (hfin := isFinite_specMap_of_powerBasis pb)
    (syntomic_specMap_of_powerBasis pb) hA hB p x

end AlgebraicGeometry

end
