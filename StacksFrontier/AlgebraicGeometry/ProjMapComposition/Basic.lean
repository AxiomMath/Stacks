module

public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01MZ: the scheme morphism induced by a composite graded ring homomorphism

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings. Tag
01MZ asserts three things about the composite `ψ.comp φ`: that its domain of definition is
the image under `U(ψ).ι` of `V = r_ψ⁻¹(U(φ))`, that the induced scheme morphism is the
composite of the two, and that the maps on all twists compose.

The first is `Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_comp`, already available.
This file proves the second: transported along the canonical isomorphism
`V ≅ U(ψ.comp φ)`, the morphism `r_{ψ.comp φ}` is `(r_ψ ∣_ U(φ)) ≫ r_φ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp`: the composition law for the scheme
  morphisms, in the shape Tag 01MZ states it — with the identification of domains fed to
  `AlgebraicGeometry.Scheme.isoOfEq` and the image identification to
  `AlgebraicGeometry.Scheme.Hom.isoImage`.
* `Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapDomainCompIso_inv_morphismRestrict`:
  the local form, on the standard open `D₊((ψ ∘ φ) f)` of the cover, which is where the
  mathematics happens.

## Route

Both morphisms in `mapHom_comp` start from `V`, which is not a domain of definition, so the
extensionality lemma `mapDomain_hom_ext` does not apply to them directly. Cancelling the
isomorphism `e` first turns the goal into an equality of two morphisms out of
`U(ψ.comp φ)`, and that *is* a domain of definition, so `mapDomain_hom_ext` reduces the
statement to the standard opens `D₊((ψ ∘ φ) f)` of its cover. There `homOfLE_mapHom` replaces
`r_{ψ.comp φ}` by the affine `mapAwayHom 𝒜 𝒞 (ψ.comp φ)`, and `mapAwayHom_comp` — the local
composition law, proved from `HomogeneousLocalization.Away.map_map` — factors it through
`mapAwayHomRes`. What is then left is a statement about open immersions only, with no graded
algebra in it: after cancelling the mono `U(φ).ι` both sides become
`mapAwayHom ℬ 𝒞 ψ`, one through `mapAwayHomRes_ι` and the other through `homOfLE_mapHom`, once
`e.inv ≫ V.ι` has been identified with a single `Scheme.homOfLE` by cancelling
`(mapDomain ℬ 𝒞 ψ).ι` against the two open-immersion isomorphisms that make up `e`.

## Implementation notes

Two transparency gotchas, both inherited from `ProjTwistChain.MY`.

* `GradedRingHom.comp` is made `implicit_reducible` locally, so that `(ψ.comp φ) f` and
  `ψ (φ f)` are interchangeable; `mapAwayHomRes` is stated with the former and
  `mapAwayHom ℬ 𝒞 ψ` with the latter. The two `≤` proofs that mediate this are introduced by
  explicitly typed `have`s rather than by `rw`, which cannot unify them.
* `Scheme.homOfLE` is proof-irrelevant in its `≤` argument but `rw` still needs the open
  subsets to match syntactically, so the collapse of the `homOfLE` chain is done inside a
  `have` whose statement names the target `≤` proof, and the chain itself is closed by
  cancelling `(mapDomain ℬ 𝒞 ψ).ι`.

## The other two assertions

The third assertion of Tag 01MZ, that the maps on every twist `𝒪(n)` compose, is
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`, in
`StacksFrontier/AlgebraicGeometry/ProjTwistCompTwistMap/Comp.lean`: it is proved for an arbitrary
composable pair, with no hypothesis that a domain of definition is everything, over Tag 01MY's
comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` on the twists. The first
assertion is `mapDomain_comp`. This file carries the second.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

attribute [local implicit_reducible] GradedRingHom.comp

universe u w w' w''

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The local form of the composition law for the scheme morphisms of Tag 01MZ: on the
standard open `D₊((ψ ∘ φ) f)` of the cover of `U(ψ ∘ φ)`, the comparison isomorphism followed
by the restriction of `r_ψ` is the factorization `mapAwayHomRes` of the local morphism of `ψ`
through `D₊(φ f)`. -/
public theorem homOfLE_mapDomainCompIso_inv_morphismRestrict (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    ((AlgebraicGeometry.Proj 𝒞).homOfLE
          (basicOpen_le_mapDomain 𝒜 𝒞 (ψ.comp φ) hd hf) ≫
        ((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
          (AlgebraicGeometry.Proj 𝒞).isoOfEq
            (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).inv) ≫
        (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) =
      mapAwayHomRes 𝒜 ℬ 𝒞 φ ψ hd hf ≫
        (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ φ hd hf) := by
  have hmem : φ f ∈ ℬ d := mem_of_mem 𝒜 ℬ φ hf
  have hle : AlgebraicGeometry.Proj.basicOpen 𝒞 ((ψ.comp φ) f) ≤ mapDomain ℬ 𝒞 ψ :=
    basicOpen_le_mapDomain ℬ 𝒞 ψ hd hmem
  have hlocal : (AlgebraicGeometry.Proj 𝒞).homOfLE hle ≫ mapHom ℬ 𝒞 ψ =
      mapAwayHom ℬ 𝒞 ψ hd hmem := homOfLE_mapHom ℬ 𝒞 ψ hd hmem
  have hchain : ((AlgebraicGeometry.Proj 𝒞).homOfLE
          (basicOpen_le_mapDomain 𝒜 𝒞 (ψ.comp φ) hd hf) ≫
        ((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
          (AlgebraicGeometry.Proj 𝒞).isoOfEq
            (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).inv) ≫
        (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι =
      (AlgebraicGeometry.Proj 𝒞).homOfLE hle := by
    rw [← cancel_mono (mapDomain ℬ 𝒞 ψ).ι]
    simp only [Category.assoc, Iso.trans_inv, Scheme.Opens.isoImage_ι_inv_ι,
      Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]
  rw [← cancel_mono (mapDomain 𝒜 ℬ φ).ι]
  simp only [Category.assoc]
  rw [morphismRestrict_ι, Scheme.homOfLE_ι, mapAwayHomRes_ι, ← hlocal]
  simp only [← Category.assoc]
  rw [hchain]

/-- **Stacks 01MZ**: the scheme morphism induced by a composite graded ring homomorphism is
the composite of the two induced morphisms. The identification `mapDomain_comp` of the domain
of the composite is used to compare the two sides: `e` is the canonical isomorphism from
`V = r_ψ⁻¹(U(φ))` to `U(ψ ∘ φ)`. -/
@[ega "II 2.8.4"]
public theorem mapHom_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    let V := mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ
    let e := ((mapDomain ℬ 𝒞 ψ).ι.isoImage V) ≪≫
      (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm
    e.hom ≫ mapHom 𝒜 𝒞 (ψ.comp φ) =
      ((mapHom ℬ 𝒞 ψ) ∣_ mapDomain 𝒜 ℬ φ) ≫ mapHom 𝒜 ℬ φ := by
  intro V e
  rw [← Iso.eq_inv_comp]
  refine mapDomain_hom_ext 𝒜 𝒞 (ψ.comp φ) _ _ fun d hd g hg => ?_
  rw [homOfLE_mapHom 𝒜 𝒞 (ψ.comp φ) hd hg, mapAwayHom_comp 𝒜 ℬ 𝒞 φ ψ hd hg,
    ← homOfLE_mapHom 𝒜 ℬ φ hd hg]
  simp only [e, V, ← Category.assoc]
  rw [homOfLE_mapDomainCompIso_inv_morphismRestrict 𝒜 ℬ 𝒞 φ ψ hd hg]

section Factorizations

universe w'''

variable {D : Type u} {ν : Type w'''} [CommRing D] [SetLike ν D] [AddSubgroupClass ν D]
  (𝒟 : ℕ → ν) [GradedRing 𝒟]

/-- Equal graded ring homomorphisms induce the same morphism of projective spectra, transported
along the equality of domains of definition they induce. -/
public theorem isoOfEq_mapDomain_hom_comp_mapHom {ψ₁ ψ₂ : 𝒜 →+*ᵍ ℬ} (h : ψ₁ = ψ₂) :
    ((AlgebraicGeometry.Proj ℬ).isoOfEq (congrArg (mapDomain 𝒜 ℬ) h)).hom ≫ mapHom 𝒜 ℬ ψ₂ =
      mapHom 𝒜 ℬ ψ₁ := by
  subst h
  rw [show congrArg (mapDomain 𝒜 ℬ) (rfl : ψ₁ = ψ₁) = rfl from rfl, Scheme.isoOfEq_rfl,
    Iso.refl_hom, Category.id_comp]

/-- The canonical identification of the domains of the two factorizations of a single graded
ring homomorphism `Θ : 𝒜 →+*ᵍ 𝒟`. Each factorization presents the domain of `r_Θ` as the inverse
image, under the morphism of its outer homomorphism, of the domain of its inner one — this is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_comp` — so the two inverse images are
canonically isomorphic. -/
public def factorizationIso (φ₁ : 𝒜 →+*ᵍ ℬ) (χ₁ : ℬ →+*ᵍ 𝒟) (φ₂ : 𝒜 →+*ᵍ 𝒞) (χ₂ : 𝒞 →+*ᵍ 𝒟)
    (h : χ₁.comp φ₁ = χ₂.comp φ₂) :
    (mapHom ℬ 𝒟 χ₁ ⁻¹ᵁ mapDomain 𝒜 ℬ φ₁).toScheme ≅
      (mapHom 𝒞 𝒟 χ₂ ⁻¹ᵁ mapDomain 𝒜 𝒞 φ₂).toScheme :=
  (((mapDomain ℬ 𝒟 χ₁).ι.isoImage (mapHom ℬ 𝒟 χ₁ ⁻¹ᵁ mapDomain 𝒜 ℬ φ₁) ≪≫
        (AlgebraicGeometry.Proj 𝒟).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒟 φ₁ χ₁).symm) ≪≫
      (AlgebraicGeometry.Proj 𝒟).isoOfEq (congrArg (mapDomain 𝒜 𝒟) h)) ≪≫
    ((mapDomain 𝒞 𝒟 χ₂).ι.isoImage (mapHom 𝒞 𝒟 χ₂ ⁻¹ᵁ mapDomain 𝒜 𝒞 φ₂) ≪≫
      (AlgebraicGeometry.Proj 𝒟).isoOfEq (mapDomain_comp 𝒜 𝒞 𝒟 φ₂ χ₂).symm).symm

/-- **The square of two factorizations of one graded ring homomorphism.** If
`χ₁ ∘ φ₁ = χ₂ ∘ φ₂` then the two composites of scheme morphisms that Tag 01MZ attaches to the
two factorizations agree, after the canonical identification `factorizationIso` of their
domains. Both are the morphism induced by the common composite. -/
public theorem factorizationIso_hom_comp (φ₁ : 𝒜 →+*ᵍ ℬ) (χ₁ : ℬ →+*ᵍ 𝒟) (φ₂ : 𝒜 →+*ᵍ 𝒞)
    (χ₂ : 𝒞 →+*ᵍ 𝒟) (h : χ₁.comp φ₁ = χ₂.comp φ₂) :
    (factorizationIso 𝒜 ℬ 𝒞 𝒟 φ₁ χ₁ φ₂ χ₂ h).hom ≫
        (mapHom 𝒞 𝒟 χ₂ ∣_ mapDomain 𝒜 𝒞 φ₂) ≫ mapHom 𝒜 𝒞 φ₂ =
      (mapHom ℬ 𝒟 χ₁ ∣_ mapDomain 𝒜 ℬ φ₁) ≫ mapHom 𝒜 ℬ φ₁ := by
  have h1 := mapHom_comp 𝒜 ℬ 𝒟 φ₁ χ₁
  have h2 := mapHom_comp 𝒜 𝒞 𝒟 φ₂ χ₂
  dsimp only at h1 h2
  have hc := isoOfEq_mapDomain_hom_comp_mapHom 𝒜 𝒟 h
  rw [← h1, ← h2, ← hc, factorizationIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

end Factorizations

end Stacks.AlgebraicGeometry.ProjTwistChain

end
