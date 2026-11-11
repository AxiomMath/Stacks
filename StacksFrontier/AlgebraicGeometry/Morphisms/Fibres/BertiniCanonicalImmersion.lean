module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent

/-!
# [Stacks, Tag 0FD6] with hypothesis (3) on the canonical morphism `φ_{L,ψ} : X → 𝐏(V)`

Hypothesis (3) of [Stacks, Tag 0FD6] is that the morphism `φ_{L,ψ} : X → 𝐏(V)` of
[Stacks, Tag 0FCY] is an immersion. That morphism is basis free: it is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, the
unique morphism classifying `(L, ψ)`. This file attaches it to the standing situation of
[Stacks, Tag 0G47] and states the tag with hypothesis (3) read on it.

The bridge to the basis-wise spelling `Stacks.Bertini.FamilyDivisors.IsImmersive` used by the
proof is the coordinate square of [Stacks, Tag 0FCY]
(`Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.`
`morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso`): followed by the coordinate
isomorphism `𝐏(V) ≅ ℙⁿ_k` of a basis, `φ_{L,ψ}` is the morphism to `ℙⁿ_k` of [Stacks, Tag 01ND]
for the sections of that basis, and composing with an isomorphism neither creates nor destroys an
immersion.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.linearSections`: `ψ` as a `k`-linear map into `Γ(X, L)` with
  the `k`-module structure of [Stacks, Tag 0FCY].
* `Stacks.Bertini.FamilyDivisors.canonicalMorphism`: the canonical morphism
  `φ_{L,ψ} : X → 𝐏(V)` of [Stacks, Tag 0FCY], defined from hypothesis (2).

## Main results

* `Stacks.Bertini.FamilyDivisors.isImmersive_iff_isImmersion_canonicalMorphism`: the basis-wise
  hypothesis (3) at any basis is the immersion property of the canonical morphism.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_isImmersion_`
  `canonicalMorphism`: **[Stacks, Tag 0FD6]**.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- `X` as a scheme over `Spec k`, through the structure morphism of the standing situation. -/
@[instance_reducible]
def overBase : D.X.Over (Spec (.of D.k)) := ⟨D.toBase⟩

attribute [local instance] overBase globalSectionsModule

/-- **`ψ : V → Γ(X, L)` as a `k`-linear map** for the `k`-module structure on `Γ(X, L)` through
the structure morphism used by [Stacks, Tag 0FCY]. -/
def linearSections : D.V →ₗ[D.k] Γ(D.L, ⊤) where
  toFun := D.sectionOf
  map_add' := D.sectionOf_add
  map_smul' := D.sectionOf_smul

/-- **Hypothesis (2) in the form of [Stacks, Tag 0FCY]**: if the image of `ψ` generates `L`, the
nonvanishing opens of the sections `ψ(v)` cover `X`. -/
theorem iSup_nonvanishingOpen_eq_top_of_generates (hgen : D.Generates) :
    ⨆ v : D.V, nonvanishingOpen D.X D.L (D.linearSections v) = ⊤ :=
  eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2
    ((Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem _).1 hgen x)

/-- **The canonical morphism `φ_{L,ψ} : X → 𝐏(V)` of [Stacks, Tag 0FCY]** attached to the linear
system of the standing situation, whose image generates `L`. It is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, which
involves no choice of basis. -/
def canonicalMorphism (hgen : D.Generates) : D.X ⟶ projectiveSpaceOfModule D.k D.V :=
  morphismOfGeneratingSections D.k D.V D.L D.linearSections
    (D.iSup_nonvanishingOpen_eq_top_of_generates hgen)

/-- **The coordinate square of [Stacks, Tag 0FCY] in the standing situation**: the canonical
morphism followed by the coordinate isomorphism `𝐏(V) ≅ ℙⁿ_k` of a basis is the morphism to
`ℙⁿ_k` of [Stacks, Tag 01ND] for the sections of that basis. -/
theorem canonicalMorphism_comp_basisProjectiveSpaceOfModuleIso (hgen : D.Generates) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) D.k D.V) :
    D.canonicalMorphism hgen ≫ (basisProjectiveSpaceOfModuleIso b).hom.left =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver (fun i => D.sectionOf (b i))
        (D.generatesBy_basis hgen b) D.toBase :=
  morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso b D.linearSections
    (D.iSup_nonvanishingOpen_eq_top_of_generates hgen)

/-- **Hypothesis (3) read at a basis is hypothesis (3) on the canonical morphism**: for every
basis of `V`, the morphism `X → 𝐏(V)` built from that basis is an immersion exactly when the
canonical morphism `φ_{L,ψ}` of [Stacks, Tag 0FCY] is. -/
theorem isImmersive_iff_isImmersion_canonicalMorphism (hgen : D.Generates) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) D.k D.V) :
    D.IsImmersive b (D.generatesBy_basis hgen b) ↔ IsImmersion (D.canonicalMorphism hgen) := by
  rw [D.isImmersive_iff_isImmersion_toProjectiveSpaceOver,
    ← D.canonicalMorphism_comp_basisProjectiveSpaceOfModuleIso hgen b]
  have : IsIso (basisProjectiveSpaceOfModuleIso b).hom.left :=
    ((Over.forget _).mapIso (basisProjectiveSpaceOfModuleIso b)).isIso_hom
  have : IsOpenImmersion (basisProjectiveSpaceOfModuleIso b).hom.left := IsOpenImmersion.of_isIso _
  have hi : IsImmersion (basisProjectiveSpaceOfModuleIso b).hom.left := inferInstance
  exact @IsImmersion.comp_iff _ _ _ _ _ hi

/-- **[Stacks, Tag 0FD6].** In the standing situation of [Stacks, Tag 0G47] — a field `k`, a
scheme `X` over `k`, an invertible `𝒪_X`-module `L`, a finite dimensional `k`-vector space `V`
with a basis, and a `k`-linear map `ψ : V → Γ(X, L)` — assume that

1. `X` is smooth over `k`,
2. the image of `ψ` generates `L`,
3. the corresponding morphism `φ_{L,ψ} : X → 𝐏(V)` of [Stacks, Tag 0FCY] is an immersion.

Then for general `v ∈ V ⊗_k k'` the scheme `H_v` is smooth over `k'`: there is a nonempty open
`U ⊂ 𝔸^r_k` such that for every field extension `k'/k` and every `v ∈ V ⊗_k k'` whose coordinate
tuple is a `k'`-point of `U`, the zero scheme `H_v = Z(ψ(v)) ⊂ X_{k'}` is smooth over `k'`.

Hypothesis (1) is the instance `[Smooth D.toBase]`, (2) is `hgen`, and (3) is `himm`, stated on
the basis-free morphism `Stacks.Bertini.FamilyDivisors.canonicalMorphism`. The base field is
arbitrary, and `dim V` may be `0`. The proof transports (3) to every basis by
`Stacks.Bertini.FamilyDivisors.isImmersive_iff_isImmersion_canonicalMorphism` and applies
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor`. -/
@[stacks 0FD6 "hypothesis (3) is stated on the canonical morphism phi_(L, psi) : X -> P(V) of \
Tag 0FCY; arbitrary base field, any dim V"]
theorem forGeneral_smooth_specializedDivisor_of_isImmersion_canonicalMorphism [Smooth D.toBase]
    (hgen : D.Generates) (himm : IsImmersion (D.canonicalMorphism hgen)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.forGeneral_smooth_specializedDivisor hgen fun _ b =>
    (D.isImmersive_iff_isImmersion_canonicalMorphism hgen b).2 himm

end Stacks.Bertini.FamilyDivisors

end
