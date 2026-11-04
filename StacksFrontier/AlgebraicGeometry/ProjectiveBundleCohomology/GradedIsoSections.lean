module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoCohomology
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# Global sections of the twisting sheaves across a graded ring isomorphism

Let `ψ : 𝒜 →+*ᵍ ℬ` be an isomorphism of nonnegatively graded rings. The comparison of the
twisting sheaves along `Proj.map ψ` carries the canonical section of `𝒪_{Proj 𝒜}(k)` attached to
a homogeneous element `a` to the canonical section of `𝒪_{Proj ℬ}(k)` attached to `ψ a`, and it is
bijective on global sections. So the canonical map `𝒜_k → Γ(Proj 𝒜, 𝒪(k))` is bijective exactly
when `ℬ_k → Γ(Proj ℬ, 𝒪(k))` is, and the global sections of the twists vanish together.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bijective_degreeSection_of_inverse`
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistSections_eq_of_inverse`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistSections

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a)

/-- The comparison of global sections along a graded ring isomorphism, landing over `⊤`. -/
public def topSectionsMap (d : ℤ) (s : (twistingSheaf 𝒜 d).val.obj (op ⊤)) :
    (twistingSheaf ℬ d).val.obj (op ⊤) :=
  ⟨fun y => (Stacks.ProjTwistComparison.sectionsMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) d ⊤
      s).1 ⟨y.1, trivial⟩,
    fun y => by
      obtain ⟨W, hW, i, h⟩ := (Stacks.ProjTwistComparison.sectionsMap ψ
        (irrelevant_le_map_of_inverse ψ χ hψχ) d ⊤ s).2 ⟨y.1, trivial⟩
      exact ⟨W, hW, homOfLE le_top, h⟩⟩

/-- `topSectionsMap` is computed pointwise by the fibre comparison
`Stacks.ProjTwistComparison.fibreMap`. -/
public theorem topSectionsMap_apply (d : ℤ) (s : (twistingSheaf 𝒜 d).val.obj (op ⊤))
    (y : (⊤ : Opens (ProjectiveSpectrum.top ℬ))) :
    (topSectionsMap ψ χ hψχ d s).1 y =
      Stacks.ProjTwistComparison.fibreMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) y.1
        (s.1 ⟨_, trivial⟩) := rfl

include hψχ hχψ in
/-- The comparison of global sections along a graded ring isomorphism is bijective. -/
public theorem bijective_topSectionsMap (d : ℤ) :
    Function.Bijective (topSectionsMap ψ χ hψχ d) := by
  have hb := Stacks.ProjTwistComparison.bijective_sectionsMap ψ
    (isAwayDegreewise_one ψ χ hψχ hχψ) (SetLike.one_mem_graded 𝒜)
    (irrelevant_le_map_of_inverse ψ χ hψχ) d ⊤ fun x hx =>
      x.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hx)
  refine ⟨fun s t h => hb.1 (Subtype.ext (funext fun y => ?_)), fun t => ?_⟩
  · exact congrArg (fun r : (twistingSheaf ℬ d).val.obj (op ⊤) => r.1 ⟨y.1, trivial⟩) h
  · obtain ⟨s, hs⟩ := hb.2 ⟨fun y => t.1 ⟨y.1, trivial⟩, fun y => by
      obtain ⟨W, hW, i, h⟩ := t.2 ⟨y.1, trivial⟩
      exact ⟨W, hW, homOfLE fun _ _ => trivial, h⟩⟩
    exact ⟨s, Subtype.ext (funext fun y =>
      congrArg (fun r => r.1 ⟨y.1, trivial⟩) hs)⟩

/-- **The comparison carries canonical sections to canonical sections.** -/
public theorem topSectionsMap_degreeSection (k : ℕ) (a : 𝒜 k) :
    topSectionsMap ψ χ hψχ (k : ℤ) (degreeSection 𝒜 k a) =
      degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩ := by
  refine Subtype.ext (funext fun y => ?_)
  rw [topSectionsMap_apply, degreeSection_apply, degreeSection_apply]
  exact Stacks.ProjTwistComparison.fibreMap_mk ψ _ y.1 _ _ |>.trans (by
    congr 1
    exact Subtype.ext (map_one ψ))

include hψχ hχψ in
/-- **Bijectivity of the canonical map on global sections is invariant under graded ring
isomorphisms.** -/
public theorem bijective_degreeSection_of_inverse (k : ℕ)
    (h : Function.Bijective (degreeSection 𝒜 k)) :
    Function.Bijective (degreeSection ℬ k) := by
  have hsurj : ∀ b : ℬ k, ∃ a : 𝒜 k, (⟨ψ a, ψ.map_mem a.2⟩ : ℬ k) = b := fun b =>
    ⟨⟨χ b, χ.map_mem b.2⟩, Subtype.ext (hψχ b)⟩
  have hcomp : ∀ a : 𝒜 k, degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩ =
      topSectionsMap ψ χ hψχ (k : ℤ) (degreeSection 𝒜 k a) := fun a =>
    (topSectionsMap_degreeSection ψ χ hψχ k a).symm
  have hT := bijective_topSectionsMap ψ χ hψχ hχψ (k : ℤ)
  refine ⟨fun b b' hbb => ?_, fun t => ?_⟩
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    rw [hcomp, hcomp] at hbb
    rw [h.1 (hT.1 hbb)]
  · obtain ⟨s, rfl⟩ := hT.2 t
    obtain ⟨a, rfl⟩ := h.2 s
    exact ⟨_, hcomp a⟩

include hψχ hχψ in
/-- **The global sections of a twisting sheaf vanish together across a graded ring
isomorphism.** -/
public theorem twistSections_eq_of_inverse (d : ℤ)
    (h : ∀ s t : (twistingSheaf 𝒜 d).val.obj (op ⊤), s = t)
    (s t : (twistingSheaf ℬ d).val.obj (op ⊤)) : s = t := by
  obtain ⟨s, rfl⟩ := (bijective_topSectionsMap ψ χ hψχ hχψ d).2 s
  obtain ⟨t, rfl⟩ := (bijective_topSectionsMap ψ χ hψχ hχψ d).2 t
  rw [h s t]

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
