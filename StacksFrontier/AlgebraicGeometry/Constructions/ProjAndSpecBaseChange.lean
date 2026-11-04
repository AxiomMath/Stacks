module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cone over a projective spectrum, and a closed immersion of the base

Let `c` be cone data `(ℬ, ψ, τ, σ)` for a nonnegatively graded ring `A`, with cone
`π : L = Proj ℬ ⟶ P = Proj 𝒜`, and let `c'` be cone data `(ℬ', ψ', τ', σ')` for a second graded
ring `A'`, with cone `π' : L' = Proj ℬ' ⟶ Q = Proj 𝒜'`. A morphism of cone data consists of
graded ring homomorphisms `α : A → A'` and `β : B → B'`, surjective in every degree, which
commute with `ψ`, with `τ` and with `σ`. It induces closed immersions `i : Q ⟶ P` and
`j : L' ⟶ L` for which the squares

```
L' ⟶ L        Q ⟶ L'
↓    ↓        ↓    ↓
Q  ⟶ P        P ⟶ L
```

commute, the horizontal maps being `j` and `i`, the vertical ones `π'`, `π` and the two zero
sections. The structure morphisms to the affine bases match as well, `j` followed by `L → Spec A`
being `L' → Spec A'` followed by `Spec A' → Spec A`, and therefore so do the punctured cones:
`j⁻¹(U_L) = U_{L'}`, and over a standard open `D₊(f)` of `P` the punctured chart
`D₊(σ f · ψ f)` of `L` pulls back to the punctured chart `D₊(σ' (α f) · ψ' (α f))` of `L'`.
This is the compatibility that lets a decomposition of the sections of `(π|_U)_* 𝒪_U` over
`D₊(f)` be read over `D₊(α f)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom` is a morphism of cone data: the pair
  `(α, β)` of degreewise surjective graded homomorphisms compatible with `ψ`, `τ` and `σ`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.baseMap` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.coneMap` are the induced morphisms
  `Q ⟶ P` and `L' ⟶ L`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.puncturedConeMap` is the induced morphism
  of punctured cones, and
  `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.toPullback` the canonical morphism from
  `L'` to the base change `L ×_P Q`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.mapDomain_comp_eq_top`: a composite of everywhere-defined
  graded homomorphisms is everywhere defined.
* `Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_preimage_basicOpen`: the inverse image of a
  standard open under the morphism induced by an everywhere-defined graded homomorphism.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.isClosedImmersion_baseMap` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.isClosedImmersion_coneMap`: both induced
  morphisms are closed immersions.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.coneMap_comp_pi` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.zeroSection_comp_coneMap`: the cone
  projection and the zero section commute with the two closed immersions.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.coneMap_comp_toSpecA`: the structure
  morphisms to the affine bases commute with the two closed immersions.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.coneMap_preimage_openUInL`: the punctured
  cone over `Q` is the inverse image of the punctured cone over `P`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeDataHom.coneMap_preimage_openUInL_inf_basicOpen`:
  the punctured chart over `D₊(f)` pulls back to the punctured chart over `D₊(α f)`.

## Implementation notes

The two closed immersions are built from
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` rather than from
`AlgebraicGeometry.Proj.map`, so that they compose with `π` through
`Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top`, whose hypotheses
`ψ` meets while Mathlib's do not. Composability needs the domain of definition of a composite to
be everything, which is `mapDomain_comp_eq_top`.

`mapHomOfTop_preimage_basicOpen` is the inverse-image formula for `mapHomOfTop` at an arbitrary
everywhere-defined graded homomorphism; the corresponding statement for the cone projection,
`Stacks.AlgebraicGeometry.ProjAndSpec.pi_preimage_basicOpen`, is proved through declarations
private to its own file.

The compatibility of the punctured cones is read off the affine bases rather than from the
description of the punctured cone as a union of standard opens: the elements `σ f` are
homogeneous of degree zero, where the inverse-image formula for standard opens is unavailable,
whereas the open `U = Spec A ∖ V(A₊)` is a union of standard opens of an affine scheme, whose
inverse images are standard opens of the image elements.

That the square of `π` and the two closed immersions is *cartesian* does not follow from a
morphism of cone data: the data constrain `ℬ'` only through `ψ'`, `τ'` and `σ'`, and not as a
base change of `ℬ`. Only the canonical morphism `L' ⟶ L ×_P Q` is constructed here.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolynomialSections Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjAndSpec

universe u

/-! ### Composites of everywhere-defined homomorphisms -/

section Composite

variable {A B C : Type u} {σ τ υ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **A composite of everywhere-defined graded ring homomorphisms is everywhere defined.** The
domain of definition of the composite is the inverse image, under the morphism of the outer
homomorphism, of the domain of definition of the inner one. -/
theorem mapDomain_comp_eq_top (φ : 𝒜 →+*ᵍ ℬ) (ρ : ℬ →+*ᵍ 𝒞) (hdφ : mapDomain 𝒜 ℬ φ = ⊤)
    (hdρ : mapDomain ℬ 𝒞 ρ = ⊤) : mapDomain 𝒜 𝒞 (ρ.comp φ) = ⊤ := by
  rw [mapDomain_comp 𝒜 ℬ 𝒞 φ ρ, hdφ, Scheme.Hom.preimage_top,
    Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι, hdρ]

end Composite

/-! ### Standard opens and everywhere-defined homomorphisms -/

section Charts

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The inverse image of a standard open under the morphism induced by an everywhere-defined
graded ring homomorphism** is the standard open of the image element. -/
@[ega "II 2.8.1" "(2.8.1.1)", ega "II 3.7.2" "more general"]
theorem mapHomOfTop_preimage_basicOpen (φ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ φ = ⊤) (f : A)
    (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    mapHomOfTop 𝒜 ℬ φ hdom ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (φ f) := by
  rw [mapHomOfTop, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    mapHom_preimage_basicOpen 𝒜 ℬ φ f d hf hd, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, Category.assoc, topIso_inv_isoOfEq_hom_ι 𝒜 ℬ φ hdom,
    Scheme.Hom.id_preimage]

end Charts

/-- Two factorisations of the same graded ring homomorphism through everywhere-defined
homomorphisms induce the same composite of morphisms of projective spectra. -/
private theorem mapHomOfTop_comp_congr {A B B' C : Type u} {σ τ τ' υ : Type u}
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [SetLike τ' B'] [AddSubgroupClass τ' B'] [SetLike υ C] [AddSubgroupClass υ C]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (ℬ' : ℕ → τ') (𝒞 : ℕ → υ)
    [GradedRing 𝒜] [GradedRing ℬ] [GradedRing ℬ'] [GradedRing 𝒞]
    (φ : 𝒜 →+*ᵍ ℬ) (ρ : ℬ →+*ᵍ 𝒞) (φ' : 𝒜 →+*ᵍ ℬ') (ρ' : ℬ' →+*ᵍ 𝒞)
    (hφ : mapDomain 𝒜 ℬ φ = ⊤) (hρ : mapDomain ℬ 𝒞 ρ = ⊤)
    (hφ' : mapDomain 𝒜 ℬ' φ' = ⊤) (hρ' : mapDomain ℬ' 𝒞 ρ' = ⊤) (h : ρ.comp φ = ρ'.comp φ') :
    mapHomOfTop ℬ 𝒞 ρ hρ ≫ mapHomOfTop 𝒜 ℬ φ hφ =
      mapHomOfTop ℬ' 𝒞 ρ' hρ' ≫ mapHomOfTop 𝒜 ℬ' φ' hφ' := by
  have hd := mapDomain_comp_eq_top 𝒜 ℬ 𝒞 φ ρ hφ hρ
  have hd' := mapDomain_comp_eq_top 𝒜 ℬ' 𝒞 φ' ρ' hφ' hρ'
  rw [← mapHomOfTop_comp_of_mapDomain_eq_top 𝒜 ℬ 𝒞 φ ρ hφ hρ hd,
    ← mapHomOfTop_comp_of_mapDomain_eq_top 𝒜 ℬ' 𝒞 φ' ρ' hφ' hρ' hd',
    mapHomOfTop_congr 𝒜 𝒞 h hd hd']

/-! ### Morphisms of cone data -/

section BaseChange

variable {A B A' B' : Type u} {σ τ σ' τ' : Type u}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike σ' A'] [AddSubgroupClass σ' A'] [SetLike τ' B'] [AddSubgroupClass τ' B']
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒜' : ℕ → σ'} {ℬ' : ℕ → τ'}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒜'] [GradedRing ℬ']

omit [GradedRing 𝒜] [GradedRing 𝒜'] in
/-- **The inverse image of the open `U = Spec A ∖ V(A₊)`** along the morphism of affine schemes
of a graded ring homomorphism surjective in every degree is the corresponding open of
`Spec A'`. -/
theorem specMap_preimage_openU (α : 𝒜 →+*ᵍ 𝒜')
    (hα : ∀ d : ℕ, Function.Surjective (GradedRingHom.gradedAddHom α d)) :
    Spec.map (CommRingCat.ofHom (α : A →+* A')) ⁻¹ᵁ openU 𝒜 = openU 𝒜' := by
  have key : Spec.map (CommRingCat.ofHom (α : A →+* A')) ⁻¹ᵁ openU 𝒜 =
      ⨆ (d : ℕ) (_ : 0 < d) (f : 𝒜 d), specBasicOpen (α (f : A)) := by
    rw [openU, Scheme.Hom.preimage_iSup]
    refine iSup_congr fun d => ?_
    rw [Scheme.Hom.preimage_iSup]
    refine iSup_congr fun _ => ?_
    rw [Scheme.Hom.preimage_iSup]
    exact iSup_congr fun _ => rfl
  rw [key, openU]
  refine le_antisymm (iSup_le fun d => iSup_le fun hd => iSup_le fun f => ?_)
    (iSup_le fun d => iSup_le fun hd => iSup_le fun f => ?_)
  · exact le_iSup_of_le d (le_iSup_of_le hd
      (le_iSup_of_le ⟨α (f : A), α.map_mem f.2⟩ le_rfl))
  · obtain ⟨g, hg⟩ := hα d f
    have hgf : α (g : A) = (f : A') := Subtype.ext_iff.mp hg
    exact le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le g (by rw [hgf])))

/-- **A morphism of cone data**: a pair of graded ring homomorphisms `α : A → A'` and
`β : B → B'`, each surjective in every degree, commuting with `ψ`, with `τ` and with `σ`. It
presents the cone of `c'` over `Q = Proj 𝒜'` as sitting over the cone of `c` over `P = Proj 𝒜`
along the closed immersion `Q ⟶ P` induced by `α`. -/
structure ConeDataHom (c : ConeData 𝒜 ℬ) (c' : ConeData 𝒜' ℬ') where
  /-- The graded ring homomorphism `α : A → A'` cutting out `Q` inside `P`. -/
  alpha : 𝒜 →+*ᵍ 𝒜'
  /-- The graded ring homomorphism `β : B → B'` cutting out `L'` inside `L`. -/
  beta : ℬ →+*ᵍ ℬ'
  /-- `α` is surjective in every degree. -/
  surjective_alpha (d : ℕ) : Function.Surjective (GradedRingHom.gradedAddHom alpha d)
  /-- `β` is surjective in every degree. -/
  surjective_beta (d : ℕ) : Function.Surjective (GradedRingHom.gradedAddHom beta d)
  /-- `β ∘ ψ = ψ' ∘ α`. -/
  beta_comp_psi : beta.comp c.psi = c'.psi.comp alpha
  /-- `α ∘ τ = τ' ∘ β`. -/
  alpha_comp_tau : alpha.comp c.tau = c'.tau.comp beta
  /-- `σ' ∘ α = β ∘ σ`, as maps to `B'`. -/
  coe_sigma_alpha (a : A) : (c'.sigma (alpha a) : B') = beta (c.sigma a)

namespace ConeDataHom

variable {c : ConeData 𝒜 ℬ} {c' : ConeData 𝒜' ℬ'} (h : ConeDataHom c c')

/-! #### The two closed immersions -/

/-- `α` induces a morphism on all of `Q = Proj 𝒜'`, being surjective in every degree. -/
theorem mapDomain_alpha_eq_top : mapDomain 𝒜 𝒜' h.alpha = ⊤ :=
  RelativeProjChain.mapDomain_eq_top_of_eventually_surjective 𝒜 𝒜' h.alpha
    (Filter.Eventually.of_forall h.surjective_alpha)

/-- `β` induces a morphism on all of `L' = Proj ℬ'`, being surjective in every degree. -/
theorem mapDomain_beta_eq_top : mapDomain ℬ ℬ' h.beta = ⊤ :=
  RelativeProjChain.mapDomain_eq_top_of_eventually_surjective ℬ ℬ' h.beta
    (Filter.Eventually.of_forall h.surjective_beta)

/-- The morphism `i : Q = Proj 𝒜' ⟶ P = Proj 𝒜` induced by `α`. -/
def baseMap : AlgebraicGeometry.Proj 𝒜' ⟶ AlgebraicGeometry.Proj 𝒜 :=
  mapHomOfTop 𝒜 𝒜' h.alpha h.mapDomain_alpha_eq_top

/-- The morphism `j : L' = Proj ℬ' ⟶ L = Proj ℬ` induced by `β`. -/
def coneMap : AlgebraicGeometry.Proj ℬ' ⟶ AlgebraicGeometry.Proj ℬ :=
  mapHomOfTop ℬ ℬ' h.beta h.mapDomain_beta_eq_top

/-- **`i : Q ⟶ P` is a closed immersion.** -/
theorem isClosedImmersion_baseMap : IsClosedImmersion h.baseMap :=
  SegreClosedImmersion.isClosedImmersion_mapHomOfTop 𝒜 𝒜' h.alpha h.mapDomain_alpha_eq_top
    (Filter.Eventually.of_forall h.surjective_alpha)

/-- **`j : L' ⟶ L` is a closed immersion.** -/
theorem isClosedImmersion_coneMap : IsClosedImmersion h.coneMap :=
  SegreClosedImmersion.isClosedImmersion_mapHomOfTop ℬ ℬ' h.beta h.mapDomain_beta_eq_top
    (Filter.Eventually.of_forall h.surjective_beta)

/-! #### The commuting squares -/

/-- **The cone projection commutes with the two closed immersions**: `π ∘ j = i ∘ π'`. Both
composites are the morphism induced by `β ∘ ψ = ψ' ∘ α`. -/
theorem coneMap_comp_pi : h.coneMap ≫ pi c = pi c' ≫ h.baseMap := by
  rw [coneMap, pi, pi, baseMap]
  exact mapHomOfTop_comp_congr 𝒜 ℬ 𝒜' ℬ' c.psi h.beta h.alpha c'.psi (projMapDomain_psi_eq_top c)
    h.mapDomain_beta_eq_top h.mapDomain_alpha_eq_top (projMapDomain_psi_eq_top c')
    h.beta_comp_psi

/-- **The zero section commutes with the two closed immersions**: `j ∘ 0' = 0 ∘ i`. Both
composites are the morphism induced by `α ∘ τ = τ' ∘ β`. -/
theorem zeroSection_comp_coneMap :
    zeroSection c' ≫ h.coneMap = h.baseMap ≫ zeroSection c := by
  rw [zeroSection_eq_mapHomOfTop, zeroSection_eq_mapHomOfTop, coneMap, baseMap]
  exact (mapHomOfTop_comp_congr ℬ 𝒜 ℬ' 𝒜' c.tau h.alpha h.beta c'.tau
    (projMapDomain_tau_eq_top c) h.mapDomain_alpha_eq_top h.mapDomain_beta_eq_top
    (projMapDomain_tau_eq_top c') h.alpha_comp_tau).symm

/-- **The structure morphisms to the affine bases commute with the closed immersions**:
`L → Spec A` precomposed with `j` is `L' → Spec A'` followed by `Spec A' → Spec A`. -/
theorem coneMap_comp_toSpecA :
    h.coneMap ≫ toSpecA c =
      toSpecA c' ≫ Spec.map (CommRingCat.ofHom (h.alpha : A →+* A')) := by
  have hz : (zeroHom ℬ ℬ' h.beta).comp c.sigma.toRingHom =
      c'.sigma.toRingHom.comp (h.alpha : A →+* A') := by
    refine RingHom.ext fun a => Subtype.ext ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, coe_zeroHom_apply]
    exact (h.coe_sigma_alpha a).symm
  rw [coneMap, toSpecA, toSpecA, ← Category.assoc,
    mapHomOfTop_toSpecZero ℬ ℬ' h.beta h.mapDomain_beta_eq_top, Category.assoc,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hz]

/-! #### Standard opens -/

/-- **The inverse image under `i` of a standard open** of `P` is the standard open of the image
element: `i⁻¹(D₊(f)) = D₊(α f)`. -/
theorem baseMap_preimage_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    h.baseMap ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen 𝒜' (h.alpha f) :=
  mapHomOfTop_preimage_basicOpen 𝒜 𝒜' h.alpha h.mapDomain_alpha_eq_top f d hf hd

/-- **The inverse image under `j` of the chart `D₊(ψ f)` of `L`** is the chart `D₊(ψ' (α f))`
of `L'`. -/
theorem coneMap_preimage_basicOpen_psi (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    h.coneMap ⁻¹ᵁ Proj.basicOpen ℬ (c.psi f) = Proj.basicOpen ℬ' (c'.psi (h.alpha f)) := by
  rw [coneMap, mapHomOfTop_preimage_basicOpen ℬ ℬ' h.beta h.mapDomain_beta_eq_top (c.psi f) d
      (c.psi.map_mem hf) hd,
    show h.beta (c.psi f) = c'.psi (h.alpha f) from GradedRingHom.congr_fun h.beta_comp_psi f]

/-- **The inverse image under `j` of the part of `L` lying over `D₊(f)`** is the part of `L'`
lying over `D₊(α f)`. -/
theorem coneMap_preimage_pi_preimage_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    h.coneMap ⁻¹ᵁ (pi c ⁻¹ᵁ Proj.basicOpen 𝒜 f) =
      pi c' ⁻¹ᵁ Proj.basicOpen 𝒜' (h.alpha f) := by
  rw [pi_preimage_basicOpen c f d hf hd,
    pi_preimage_basicOpen c' (h.alpha f) d (h.alpha.map_mem hf) hd,
    h.coneMap_preimage_basicOpen_psi f d hf hd]

/-- **The inverse image under `j` of the punctured chart `D₊(σ f · ψ f)` of `L`** is the
punctured chart `D₊(σ' (α f) · ψ' (α f))` of `L'`. -/
theorem coneMap_preimage_basicOpen_sigma_mul_psi (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    h.coneMap ⁻¹ᵁ Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f) =
      Proj.basicOpen ℬ' ((c'.sigma (h.alpha f) : B') * c'.psi (h.alpha f)) := by
  have hmem : (c.sigma f : B) * c.psi f ∈ ℬ d := by
    simpa using SetLike.mul_mem_graded (c.sigma f).2 (c.psi.map_mem hf)
  have himg : h.beta ((c.sigma f : B) * c.psi f) =
      (c'.sigma (h.alpha f) : B') * c'.psi (h.alpha f) := by
    rw [map_mul, (h.coe_sigma_alpha f).symm,
      show h.beta (c.psi f) = c'.psi (h.alpha f) from GradedRingHom.congr_fun h.beta_comp_psi f]
  rw [coneMap, mapHomOfTop_preimage_basicOpen ℬ ℬ' h.beta h.mapDomain_beta_eq_top _ d hmem hd,
    himg]

/-! #### The punctured cones -/

/-- **The punctured cone over `Q` is the inverse image of the punctured cone over `P`**:
`j⁻¹(U_L) = U_{L'}`. The open `U = Spec A ∖ V(A₊)` pulls back to `U' = Spec A' ∖ V(A'₊)` along
`Spec A' → Spec A`, and the structure morphisms to the affine bases commute with `j`. -/
theorem coneMap_preimage_openUInL : h.coneMap ⁻¹ᵁ openUInL c = openUInL c' := by
  rw [openUInL, openUInL, ← Scheme.Hom.comp_preimage, h.coneMap_comp_toSpecA,
    Scheme.Hom.comp_preimage, specMap_preimage_openU h.alpha h.surjective_alpha]

/-- **The punctured chart over `D₊(f)` pulls back to the punctured chart over `D₊(α f)`**: the
part of `U_{L'}` lying over `D₊(α f)` is the inverse image of the part of `U_L` lying over
`D₊(f)`. This is the compatibility that transports a decomposition of the sections of
`(π|_U)_* 𝒪_U` over a standard open of `P` to one over the corresponding standard open of `Q`. -/
theorem coneMap_preimage_openUInL_inf_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    h.coneMap ⁻¹ᵁ (openUInL c ⊓ Proj.basicOpen ℬ (c.psi f)) =
      openUInL c' ⊓ Proj.basicOpen ℬ' (c'.psi (h.alpha f)) := by
  rw [openUInL_inf_basicOpen c f d hf hd,
    h.coneMap_preimage_basicOpen_sigma_mul_psi f d hf hd,
    openUInL_inf_basicOpen c' (h.alpha f) d (h.alpha.map_mem hf) hd]

/-- The morphism of punctured cones `U_{L'} ⟶ U_L` cut out by `j`. -/
def puncturedConeMap : (openUInL c').toScheme ⟶ (openUInL c).toScheme :=
  h.coneMap.resLE (openUInL c) (openUInL c') h.coneMap_preimage_openUInL.ge

/-- **The restricted cone projection commutes with the two closed immersions**: `π|_U` composed
with the morphism of punctured cones is `π'|_{U'}` followed by `i`. -/
theorem puncturedConeMap_comp_puncturedConeProj :
    h.puncturedConeMap ≫ (openUInL c).ι ≫ pi c =
      ((openUInL c').ι ≫ pi c') ≫ h.baseMap := by
  rw [← Category.assoc, puncturedConeMap, Scheme.Hom.resLE_comp_ι, Category.assoc,
    h.coneMap_comp_pi, Category.assoc]

/-! #### The comparison with the base change -/

/-- The canonical morphism from the cone over `Q` to the base change `L ×_P Q` of the cone over
`P`, given by `j` and `π'`. -/
def toPullback : AlgebraicGeometry.Proj ℬ' ⟶ Limits.pullback (pi c) h.baseMap :=
  Limits.pullback.lift h.coneMap (pi c') h.coneMap_comp_pi

/-- The comparison morphism to the base change followed by the first projection is `j`. -/
theorem toPullback_comp_fst :
    h.toPullback ≫ Limits.pullback.fst (pi c) h.baseMap = h.coneMap :=
  Limits.pullback.lift_fst _ _ _

/-- The comparison morphism to the base change followed by the second projection is `π'`. -/
theorem toPullback_comp_snd :
    h.toPullback ≫ Limits.pullback.snd (pi c) h.baseMap = pi c' :=
  Limits.pullback.lift_snd _ _ _

end ConeDataHom

end BaseChange

end Stacks.AlgebraicGeometry.ProjAndSpec

end
