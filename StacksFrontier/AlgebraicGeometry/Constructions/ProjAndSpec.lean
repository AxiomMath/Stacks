module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Morphism.Nested
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cone over a projective spectrum

Let `A` be a nonnegatively graded ring and let `B` be a second nonnegatively graded ring
equipped with

* a graded ring homomorphism `ψ : A → B`;
* a graded ring homomorphism `τ : B → A` with `τ ∘ ψ = id`;
* a ring isomorphism `σ : A ≃ B₀` which agrees with `ψ` on `A₀` and satisfies `τ ∘ σ = proj₀`;

subject to three divisibility conditions, recorded in `ConeData`, which hold for the truncation
algebra `B = ⨁_{d ≥ 0} A_{≥ d}`, where `ψ` sends `a ∈ A_d` to `a⁽ᵈ⁾`, where `τ` sends `a⁽ᵈ⁾` to
the degree `d` component of `a`, and where `σ a = a⁽⁰⁾`.

Write `X = Spec A`, `Z = Spec A₀`, `P = Proj A` and `L = Proj B`, the last a scheme over `X`
through `σ`. The first condition says precisely that `ψ` induces a morphism on all of `L`, and
`τ ∘ ψ = id` says the same for `τ` on all of `P`, because a graded homomorphism with a graded
section carries the irrelevant ideal of its target into the image of the irrelevant ideal of its
source. The two morphisms so obtained are the cone projection `π : L → P` and its zero section
`0 : P → L`. The projection is affine, with `π⁻¹(D₊(f)) = D₊(ψ f)` on standard opens; the zero
section is a closed immersion, satisfies `π ∘ 0 = id_P`, and has for image, set theoretically,
the part of `L` not lying over `U = X ∖ V(A₊)`. That part, the punctured cone, is itself affine
over `P`. Finally the two squares

```
P ⟶ L        L ⟶ P
↓   ↓        ↓   ↓
Z ⟶ X        X ⟶ Z
```

commute, the vertical maps being the structure morphisms `P → Z` and `L → X` and the horizontal
ones `0`, `π` and the two canonical morphisms between `Spec A` and `Spec A₀`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpec.ConeData` bundles the graded ring `B` together with the
  maps `ψ`, `τ` and `σ` and the conditions on them.
* `Stacks.AlgebraicGeometry.ProjAndSpec.pi` is the cone projection `π : L → P`, and
  `Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection` is the zero section `0 : P → L`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA` is the structure morphism `L → X`, and
  `Stacks.AlgebraicGeometry.ProjAndSpec.zToX`,
  `Stacks.AlgebraicGeometry.ProjAndSpec.xToZ` are the two morphisms between `X` and `Z`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.openU` is the open `U = X ∖ V(A₊)` of `X`, and
  `Stacks.AlgebraicGeometry.ProjAndSpec.openUInL` is its inverse image in `L`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top`: two
  everywhere-defined graded ring homomorphisms induce the composite morphism, with no inclusion
  of irrelevant ideals assumed.
* `Stacks.AlgebraicGeometry.ProjAndSpec.projMapDomain_psi_eq_top` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.projMapDomain_tau_eq_top`: `ψ` and `τ` induce morphisms
  on all of `Proj B` respectively all of `Proj A`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.pi_preimage_basicOpen`: `π⁻¹(D₊(f)) = D₊(ψ f)`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi`: `π` is affine.
* `Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_comp_pi`: `π ∘ 0 = id_P`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.isClosedImmersion_zeroSection`: `0` is a closed
  immersion.
* `Stacks.AlgebraicGeometry.ProjAndSpec.openUInL_eq_iSup` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.mem_openUInL_iff`: the part of `L` over `U` is the union
  of the standard opens `D₊(σ f)` for `f` homogeneous of positive degree.
* `Stacks.AlgebraicGeometry.ProjAndSpec.range_zeroSection`: the image of `0` is the complement of
  the part of `L` over `U`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.openUInL_inf_basicOpen` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi_restrict`: over `D₊(f)` the part of `L`
  over `U` is the standard open `D₊(σ f · ψ f)`, so the punctured cone is affine over `P`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.zeroSection_comp_toSpecA` and
  `Stacks.AlgebraicGeometry.ProjAndSpec.pi_comp_toSpecZero`: the two commuting squares.

## Implementation notes

Mathlib's `AlgebraicGeometry.Proj.map` is unavailable for `ψ`: it needs the plain inclusion
`B₊ ≤ (A₊).map ψ`, which already fails for the truncation algebra of `A = k[x]` with `x` in
degree two, where the degree one part of `(A₊).map ψ` vanishes while `B₁ = A_{≥ 1} ≠ 0`. Only the
radical inclusion holds, so `π` is built from
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`, the morphism glued from the maps of
degree-zero localizations, and `ConeData.psi_pow` records the radical inclusion in the elementary
form in which the truncation algebra supplies it. For `τ` the plain inclusion *is* available, for
free from the graded section `ψ`, so `0` is simultaneously Mathlib's morphism; this is what makes
`π ∘ 0 = id_P` reachable, through the composition law of Tag 01MZ rather than through Mathlib's
`AlgebraicGeometry.Proj.map_comp`, whose hypotheses `ψ` does not meet.

Affineness of `π` is checked chart by chart: the standard opens `D₊(f)` of positive-degree
homogeneous elements cover `P`, they are affine, and their inverse images are the standard opens
`D₊(ψ f)`, which are affine because `ψ f` is again homogeneous of positive degree. The same cover
computes the punctured cone: `ConeData.sigma_pow_mul_psi` makes `σ f` cut out, inside `D₊(ψ f)`,
the whole of the part lying over `U`, so that part is the standard open of `σ f · ψ f`, again
homogeneous of positive degree.

The two remaining conditions are used only for the image of the zero section.
`ConeData.sub_psi_tau_pow` says that `b - ψ (τ b)` is nilpotent modulo `σ (A₊)` for homogeneous
`b`, which is what makes a homogeneous prime containing `σ (A₊)` the contraction along `τ` of its
contraction along `ψ`; without it the two contractions need not be inverse to one another.

`specBasicOpen` exists because `PrimeSpectrum.basicOpen` has the prime spectrum, not the scheme
`Spec A`, as its ambient space: a supremum of opens formed at the first type is not recognized as
a supremum of opens of the scheme, and the inverse image of `U` along `L → X` cannot then be
computed.

The grading of `B` is indexed by an arbitrary `SetLike` carrier, as is that of `A`, but both
carriers live in the ring's universe: `AlgebraicGeometry.Proj.map`, with which the morphism
induced by `τ` is compared, declares them there.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolynomialSections Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjAndSpec

universe u

/-! ### The base `X = Spec A` and its closed subscheme `Z = Spec A₀` -/

section Base

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The closed immersion `Z = Spec A₀ ⟶ X = Spec A` induced by the projection `A → A₀`. -/
@[stacks 0EKG "the morphism Z → X"]
def zToX : Spec (CommRingCat.of (𝒜 0)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (GradedRing.projZeroRingHom' 𝒜))

/-- The morphism `X = Spec A ⟶ Z = Spec A₀` induced by the inclusion `A₀ → A`. -/
@[stacks 0EKG "the morphism X → Z"]
def xToZ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (𝒜 0)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝒜 0) A))

/-- The standard open `D(f)` of `X = Spec A`, as an open of the *scheme* `Spec A` rather than of
the prime spectrum of `A`. The two are the same open, but only with the scheme's carrier as the
ambient type do suprema of such opens interact with inverse images along morphisms of schemes. -/
def specBasicOpen (f : A) : (Spec (CommRingCat.of A)).Opens :=
  PrimeSpectrum.basicOpen f

/-- The open `U = X ∖ V(A₊)` of `X = Spec A`: the union of the standard opens `D(f)` of the
homogeneous elements `f` of positive degree. -/
@[stacks 0EKG "the open U ⊆ X"]
def openU : (Spec (CommRingCat.of A)).Opens :=
  ⨆ (d : ℕ) (_ : 0 < d) (f : 𝒜 d), specBasicOpen (f : A)

end Base

/-! ### Composing everywhere-defined induced morphisms -/

section Composition

variable {A B C : Type u} {σ τ υ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- The canonical isomorphism `Proj ℬ ≅ U(ψ)` for an everywhere-defined `ψ`. -/
private def domIso (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    AlgebraicGeometry.Proj ℬ ≅ (mapDomain 𝒜 ℬ ψ).toScheme :=
  (Scheme.topIso _).symm ≪≫ (AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
private theorem domIso_hom_ι (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    (domIso 𝒜 ℬ ψ hdom).hom ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ) := by
  rw [domIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  exact topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom

private theorem mapHomOfTop_eq_domIso_hom_comp (ψ : 𝒜 →+*ᵍ ℬ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    mapHomOfTop 𝒜 ℬ ψ hdom = (domIso 𝒜 ℬ ψ hdom).hom ≫ mapHom 𝒜 ℬ ψ := by
  rw [mapHomOfTop, domIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
private theorem domIso_hom_homOfLE (φ : 𝒜 →+*ᵍ ℬ) (ρ : ℬ →+*ᵍ 𝒞)
    (hdρ : mapDomain ℬ 𝒞 ρ = ⊤) (hdc : mapDomain 𝒜 𝒞 (ρ.comp φ) = ⊤) :
    (domIso 𝒜 𝒞 (ρ.comp φ) hdc).hom ≫
        (AlgebraicGeometry.Proj 𝒞).homOfLE (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ρ) =
      (domIso ℬ 𝒞 ρ hdρ).hom := by
  rw [← cancel_mono (mapDomain ℬ 𝒞 ρ).ι, Category.assoc, Scheme.homOfLE_ι,
    domIso_hom_ι 𝒜 𝒞 (ρ.comp φ) hdc, domIso_hom_ι ℬ 𝒞 ρ hdρ]

/-- **The composition law for everywhere-defined induced morphisms.** Unlike
`Stacks.AlgebraicGeometry.ProjBundleSurjection.mapHomOfTop_comp`, which compares both sides with
`AlgebraicGeometry.Proj.map`, this needs no inclusion of irrelevant ideals: it is the glueing
statement of Tag 01MZ with the canonical identification of the domains of definition replaced by
the isomorphisms `Proj ≅ U(ψ)`. -/
@[ega "II 2.8.4" "special case"]
theorem mapHomOfTop_comp_of_mapDomain_eq_top (φ : 𝒜 →+*ᵍ ℬ) (ρ : ℬ →+*ᵍ 𝒞)
    (hdφ : mapDomain 𝒜 ℬ φ = ⊤) (hdρ : mapDomain ℬ 𝒞 ρ = ⊤)
    (hdc : mapDomain 𝒜 𝒞 (ρ.comp φ) = ⊤) :
    mapHomOfTop 𝒜 𝒞 (ρ.comp φ) hdc = mapHomOfTop ℬ 𝒞 ρ hdρ ≫ mapHomOfTop 𝒜 ℬ φ hdφ := by
  have key := Tag07ZGMorphism.mapHom_comp' 𝒜 ℬ 𝒞 φ ρ
    ((AlgebraicGeometry.Proj 𝒞).homOfLE (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ρ) ≫ mapHom ℬ 𝒞 ρ ≫
      (domIso 𝒜 ℬ φ hdφ).hom)
    (by rw [Category.assoc, Category.assoc, domIso_hom_ι 𝒜 ℬ φ hdφ, Category.comp_id])
  rw [mapHomOfTop_eq_domIso_hom_comp 𝒜 𝒞 (ρ.comp φ) hdc, key,
    mapHomOfTop_eq_domIso_hom_comp ℬ 𝒞 ρ hdρ, mapHomOfTop_eq_domIso_hom_comp 𝒜 ℬ φ hdφ]
  simp only [Category.assoc]
  rw [← Category.assoc (domIso 𝒜 𝒞 (ρ.comp φ) hdc).hom,
    domIso_hom_homOfLE 𝒜 ℬ 𝒞 φ ρ hdρ hdc]

end Composition

/-! ### The identity -/

section Id

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The identity graded ring homomorphism induces the identity of `Proj`. -/
private theorem mapHomOfTop_id (hdom : mapDomain 𝒜 𝒜 (GradedRingHom.id 𝒜) = ⊤) :
    mapHomOfTop 𝒜 𝒜 (GradedRingHom.id 𝒜) hdom = 𝟙 (AlgebraicGeometry.Proj 𝒜) := by
  rw [mapHomOfTop_eq_map 𝒜 𝒜 (GradedRingHom.id 𝒜) (by simp) hdom]
  exact Proj.map_id

end Id

/-! ### The data of the cone -/

section Cone

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The algebraic data from which the cone `L = Proj ℬ` over `P = Proj 𝒜` is built: the two
graded ring homomorphisms `ψ : A → B` and `τ : B → A` with `τ ∘ ψ = id`, the identification
`σ : A ≃ B₀` through which `L` is a scheme over `X = Spec A`, the two formulas tying `σ` to `ψ`
and `τ`, and three divisibility conditions: `ψ` generates the irrelevant ideal of `B` up to
radicals, `b` is congruent to `ψ (τ b)` modulo `σ (A₊)` up to radicals, and `σ f` divides
`(σ g) ^ d * ψ f`. The truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` with `ψ a = a⁽ᵈ⁾` for
`a ∈ A_d`, `τ a⁽ᵈ⁾ = a_d` and `σ a = a⁽⁰⁾` is an example. -/
structure ConeData where
  /-- The graded ring homomorphism `ψ : A → B`. -/
  psi : 𝒜 →+*ᵍ ℬ
  /-- The graded ring homomorphism `τ : B → A`. -/
  tau : ℬ →+*ᵍ 𝒜
  /-- The identification of `A` with the degree-zero part of `B`. -/
  sigma : A ≃+* ℬ 0
  /-- `τ` is a left inverse of `ψ`; in particular `τ` is surjective. -/
  tau_psi (a : A) : tau (psi a) = a
  /-- Every homogeneous element of `B` of positive degree has a power in the ideal generated by
  the `ψ`-images of the positive-degree homogeneous elements of `A`. This is the radical
  inclusion `B₊ ≤ ((A₊).map ψ).radical`, written out on homogeneous elements. -/
  psi_pow (d : ℕ) (hd : 0 < d) (b : B) (hb : b ∈ ℬ d) :
    ∃ k : ℕ, b ^ k ∈ Ideal.span (psi '' ⋃ n > 0, (𝒜 n : Set A))
  /-- `ψ` and `σ` agree on the degree-zero part of `A`. -/
  psi_apply_of_mem_zero (a : A) (ha : a ∈ 𝒜 0) : psi a = (sigma a : B)
  /-- `τ ∘ σ` is the projection of `A` onto its degree-zero part. -/
  tau_sigma (a : A) : tau (sigma a : B) = GradedRing.projZeroRingHom 𝒜 a
  /-- For a homogeneous `b` of `B`, some power of `b - ψ (τ b)` lies in the ideal generated by
  the `σ`-images of the positive-degree homogeneous elements of `A`. For the truncation algebra
  and `b = a⁽ᵈ⁾` this difference is `a'⁽ᵈ⁾` with `a' = a - a_d ∈ A_{≥ d+1}`, whose `(d+1)`-st
  power is `(a'^d)⁽ᵈ(ᵈ⁺¹)⁾ · σ a'`. -/
  sub_psi_tau_pow (d : ℕ) (b : B) (hb : b ∈ ℬ d) :
    ∃ k : ℕ, (b - psi (tau b)) ^ k ∈
      Ideal.span ((fun a : A => (sigma a : B)) '' ⋃ n > 0, (𝒜 n : Set A))
  /-- For `f` homogeneous of degree `d` and `g` homogeneous of positive degree, `σ f` divides
  `(σ g) ^ d * ψ f`. For the truncation algebra and `g ∈ A_e` with `e ≥ 1` both sides are
  `(g ^ d * f)⁽ᵈ⁾`, the factor being `(g ^ d)⁽ᵈ⁾`. -/
  sigma_pow_mul_psi (d e : ℕ) (he : 0 < e) (f g : A) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    ∃ z : B, (sigma g : B) ^ d * psi f = (sigma f : B) * z

variable {𝒜 ℬ} (c : ConeData 𝒜 ℬ)

/-! ### The two domains of definition -/

/-- **Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for `τ`**, since `ψ` is a graded
section of it. -/
theorem irrelevant_le_map_tau :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map c.tau :=
  irrelevant_le_map_of_graded_section ℬ 𝒜 c.tau c.psi c.tau_psi

/-- `τ` induces a morphism on all of `P = Proj 𝒜`. -/
@[stacks 0EKG "τ defines a morphism on all of Proj(A)"]
theorem projMapDomain_tau_eq_top : mapDomain ℬ 𝒜 c.tau = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map ℬ 𝒜 c.tau (irrelevant_le_map_tau c)

/-- `ψ` induces a morphism on all of `L = Proj ℬ`: the power condition is exactly the radical
inclusion of irrelevant ideals that makes the standard opens `D₊(ψ f)` cover `Proj ℬ`. -/
@[stacks 0EKG "ψ defines a morphism on all of Proj(B)"]
theorem projMapDomain_psi_eq_top : mapDomain 𝒜 ℬ c.psi = ⊤ := by
  rw [mapDomain_eq_top_iff_irrelevant_le_radical]
  refine (HomogeneousIdeal.irrelevant_le ℬ).mpr fun i hi g hg => ?_
  change g ∈ (((HomogeneousIdeal.irrelevant 𝒜).map c.psi).radical).toIdeal
  rw [HomogeneousIdeal.coe_radical, HomogeneousIdeal.toIdeal_map,
    HomogeneousIdeal.irrelevant_eq_span, Ideal.map_span]
  exact c.psi_pow i hi g hg

/-- `τ` is surjective in every degree, `ψ` being a graded section. -/
theorem surjective_gradedAddHom_tau (d : ℕ) :
    Function.Surjective (GradedRingHom.gradedAddHom c.tau d) := fun a =>
  ⟨GradedRingHom.gradedAddHom c.psi d a, Subtype.ext (c.tau_psi (a : A))⟩

/-! ### The morphisms of the diagram -/

/-- The cone projection `π : L = Proj ℬ ⟶ P = Proj 𝒜`, induced by `ψ`. -/
@[stacks 0EKG "the cone projection π : L → P"]
def pi : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜 :=
  mapHomOfTop 𝒜 ℬ c.psi (projMapDomain_psi_eq_top c)

/-- The zero section `0 : P = Proj 𝒜 ⟶ L = Proj ℬ`, induced by `τ`. -/
@[stacks 0EKG "the zero section 0 : P → L"]
def zeroSection : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ :=
  mapHomOfSection ℬ 𝒜 c.tau c.psi c.tau_psi

/-- The zero section is the morphism induced by the everywhere-defined `τ`. -/
theorem zeroSection_eq_mapHomOfTop :
    zeroSection c = mapHomOfTop ℬ 𝒜 c.tau (projMapDomain_tau_eq_top c) :=
  rfl

/-- The structure morphism `L = Proj ℬ ⟶ X = Spec A`, using the identification `σ` of `A` with
the degree-zero part of `B`. -/
@[stacks 0EKG "the structure morphism L → X"]
def toSpecA : AlgebraicGeometry.Proj ℬ ⟶ Spec (CommRingCat.of A) :=
  Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom c.sigma.toRingHom)

/-- The inverse image in `L` of the open `U = X ∖ V(A₊)`. -/
@[stacks 0EKG "the open U ⊆ L"]
def openUInL : (AlgebraicGeometry.Proj ℬ).Opens :=
  toSpecA c ⁻¹ᵁ openU 𝒜

/-- **The standard open `D(f)` of `X` pulls back to the standard open `D₊(σ f)` of `L`.** -/
theorem toSpecA_preimage_specBasicOpen (f : A) :
    toSpecA c ⁻¹ᵁ specBasicOpen f = Proj.basicOpen ℬ ((c.sigma f : B)) :=
  Proj.toSpecZero_preimage_basicOpen ℬ (c.sigma f)

/-- **The inverse image of `U` in `L` is a union of standard opens**, namely those of the
`σ`-images of the positive-degree homogeneous elements of `A`. -/
theorem openUInL_eq_iSup :
    openUInL c =
      ⨆ (d : ℕ) (_ : 0 < d) (f : 𝒜 d), Proj.basicOpen ℬ ((c.sigma (f : A) : B)) := by
  simp only [openUInL, openU, Scheme.Hom.preimage_iSup, toSpecA_preimage_specBasicOpen]

/-- A point of `L` lies over `U` exactly when some positive-degree homogeneous element of `A`
has its `σ`-image outside the corresponding homogeneous prime. -/
theorem mem_openUInL_iff (y : AlgebraicGeometry.Proj ℬ) :
    y ∈ openUInL c ↔
      ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ (c.sigma f : B) ∉ y.asHomogeneousIdeal := by
  rw [openUInL_eq_iSup]
  simp only [TopologicalSpace.Opens.mem_iSup, Proj.mem_basicOpen, Subtype.exists]
  exact ⟨fun ⟨d, hd, f, hf, hfy⟩ => ⟨d, f, hd, hf, hfy⟩,
    fun ⟨d, f, hd, hf, hfy⟩ => ⟨d, hd, f, hf, hfy⟩⟩

/-! ### Standard opens and affineness -/

/-- **The inverse image under `π` of a standard open** of `P` is the standard open of the image
element: `π⁻¹(D₊(f)) = D₊(ψ f)`. -/
@[stacks 0EKG "π⁻¹ of a standard open"]
theorem pi_preimage_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    pi c ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (c.psi f) := by
  rw [pi, mapHomOfTop_eq_domIso_hom_comp, Scheme.Hom.comp_preimage,
    mapHom_preimage_basicOpen 𝒜 ℬ c.psi f d hf hd, ← Scheme.Hom.comp_preimage,
    domIso_hom_ι 𝒜 ℬ c.psi (projMapDomain_psi_eq_top c)]
  simp

/-- A morphism to `Proj 𝒜` is affine if the inverse images of the standard opens of
positive-degree homogeneous elements are affine. -/
private theorem isAffineHom_of_isAffineOpen_preimage_basicOpen {Y : Scheme.{u}}
    (g : Y ⟶ AlgebraicGeometry.Proj 𝒜)
    (h : ∀ (d : ℕ) (f : A), f ∈ 𝒜 d → 0 < d → IsAffineOpen (g ⁻¹ᵁ Proj.basicOpen 𝒜 f)) :
    IsAffineHom g := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨d, f, hd, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  exact ⟨Proj.basicOpen 𝒜 f, (Proj.mem_basicOpen 𝒜 f x).mpr hfx,
    Proj.isAffineOpen_basicOpen 𝒜 f hf hd, h d f hf hd⟩

/-- **The cone projection is affine.** The standard opens of positive-degree homogeneous elements
cover `P` and are affine, and their inverse images are again standard opens of positive-degree
homogeneous elements. -/
@[stacks 0EKG "π is affine"]
theorem isAffineHom_pi : IsAffineHom (pi c) := by
  refine isAffineHom_of_isAffineOpen_preimage_basicOpen _ fun d f hf hd => ?_
  rw [pi_preimage_basicOpen c f d hf hd]
  exact Proj.isAffineOpen_basicOpen ℬ (c.psi f) (c.psi.map_mem hf) hd

/-! ### The zero section -/

/-- **`π ∘ 0 = id_P`**: the zero section is a section of the cone projection. -/
@[stacks 0EKG "π ∘ 0 = id_P"]
theorem zeroSection_comp_pi : zeroSection c ≫ pi c = 𝟙 (AlgebraicGeometry.Proj 𝒜) := by
  have hcomp : c.tau.comp c.psi = GradedRingHom.id 𝒜 := GradedRingHom.ext c.tau_psi
  have hdc : mapDomain 𝒜 𝒜 (c.tau.comp c.psi) = ⊤ := by
    rw [hcomp, mapDomain_id 𝒜]
  rw [zeroSection_eq_mapHomOfTop, pi,
    ← mapHomOfTop_comp_of_mapDomain_eq_top 𝒜 ℬ 𝒜 c.psi c.tau _ _ hdc,
    mapHomOfTop_congr 𝒜 𝒜 hcomp hdc (mapDomain_id 𝒜), mapHomOfTop_id 𝒜]

/-- **The zero section is a closed immersion**, `τ` being surjective in every degree. -/
@[stacks 0EKG "0 : P → L is a closed immersion"]
theorem isClosedImmersion_zeroSection : IsClosedImmersion (zeroSection c) := by
  have : IsClosedImmersion (mapHom ℬ 𝒜 c.tau) :=
    RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective ℬ 𝒜 c.tau
      (Filter.Eventually.of_forall (surjective_gradedAddHom_tau c))
  rw [zeroSection_eq_mapHomOfTop, mapHomOfTop]
  infer_instance


/-! ### The image of the zero section -/

/-- The zero section is Mathlib's `AlgebraicGeometry.Proj.map` for `τ`, whose plain inclusion of
irrelevant ideals is available. -/
theorem zeroSection_eq_projMap :
    zeroSection c = Proj.map c.tau (irrelevant_le_map_tau c) :=
  mapHomOfTop_eq_map ℬ 𝒜 c.tau (irrelevant_le_map_tau c) (projMapDomain_tau_eq_top c)

/-- On points the zero section contracts a homogeneous prime of `A` along `τ`. -/
theorem asHomogeneousIdeal_zeroSection (p : AlgebraicGeometry.Proj 𝒜) :
    ((zeroSection c) p).asHomogeneousIdeal = p.asHomogeneousIdeal.comap c.tau := by
  rw [zeroSection_eq_projMap]
  rfl

/-- A homogeneous prime of `B` containing the `σ`-images of all positive-degree homogeneous
elements of `A` contains the ideal they generate. -/
private theorem span_sigma_le (y : ProjectiveSpectrum ℬ)
    (hy : ∀ (d : ℕ), 0 < d → ∀ f : A, f ∈ 𝒜 d → (c.sigma f : B) ∈ y.asHomogeneousIdeal) :
    Ideal.span ((fun a : A => (c.sigma a : B)) '' ⋃ n > 0, (𝒜 n : Set A)) ≤
      y.asHomogeneousIdeal.toIdeal := by
  rw [Ideal.span_le]
  rintro b ⟨a, ha, rfl⟩
  obtain ⟨n, hn, han⟩ := Set.mem_iUnion₂.mp ha
  exact hy n hn a han

/-- **Away from `U` the element `ψ (τ b)` is congruent to `b`.** For a homogeneous prime of `B`
containing `σ (A₊)` the difference `b - ψ (τ b)` lies in the prime, for every `b`: on a
homogeneous `b` this is the power condition on `b - ψ (τ b)`, and the general case follows by
decomposing `b`. -/
private theorem sub_psi_tau_mem (y : ProjectiveSpectrum ℬ)
    (hy : ∀ (d : ℕ), 0 < d → ∀ f : A, f ∈ 𝒜 d → (c.sigma f : B) ∈ y.asHomogeneousIdeal)
    (b : B) : b - c.psi (c.tau b) ∈ y.asHomogeneousIdeal.toIdeal := by
  classical
  have hhom : ∀ (d : ℕ) (x : B), x ∈ ℬ d →
      x - c.psi (c.tau x) ∈ y.asHomogeneousIdeal.toIdeal := fun d x hx => by
    obtain ⟨k, hk⟩ := c.sub_psi_tau_pow d x hx
    exact y.isPrime.mem_of_pow_mem k (span_sigma_le c y hy hk)
  rw [← DirectSum.sum_support_decompose ℬ b, map_sum, map_sum, ← Finset.sum_sub_distrib]
  exact Ideal.sum_mem _ fun i _ => hhom i _ (SetLike.coe_mem _)

/-- **A homogeneous prime of `B` containing `σ (A₊)` is the contraction along `τ` of its own
contraction along `ψ`.** -/
private theorem comap_psi_comap_tau (y : ProjectiveSpectrum ℬ)
    (hy : ∀ (d : ℕ), 0 < d → ∀ f : A, f ∈ 𝒜 d → (c.sigma f : B) ∈ y.asHomogeneousIdeal) :
    (y.asHomogeneousIdeal.comap c.psi).comap c.tau = y.asHomogeneousIdeal := by
  rw [HomogeneousIdeal.comap_comap]
  refine HomogeneousIdeal.ext (Ideal.ext fun b => ?_)
  have hsub := sub_psi_tau_mem c y hy b
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hb' : c.psi (c.tau b) ∈ y.asHomogeneousIdeal.toIdeal := hb
    simpa using Ideal.add_mem _ hb' hsub
  · simpa using Ideal.sub_mem _ hb hsub

/-- **The zero section maps onto the inverse image of `Z`.** Set theoretically the image of
`0 : P → L` is the complement of the part of `L` lying over `U = X ∖ V(A₊)`. A point of the image
contains `σ (A₊)` because `τ ∘ σ` kills the positive degrees; conversely a homogeneous prime of
`B` containing `σ (A₊)` is the image of its own contraction along `ψ`, which is relevant because
`ψ` is everywhere defined. -/
@[stacks 0EKG "the image of the zero section is the inverse image of Z"]
theorem range_zeroSection :
    Set.range (zeroSection c) = ((openUInL c : Set (AlgebraicGeometry.Proj ℬ)))ᶜ := by
  ext y
  simp only [Set.mem_range, Set.mem_compl_iff, SetLike.mem_coe, mem_openUInL_iff, not_exists,
    not_and, not_not]
  constructor
  · rintro ⟨p, rfl⟩ d f hd hf
    rw [asHomogeneousIdeal_zeroSection]
    change c.tau (c.sigma f : B) ∈ p.asHomogeneousIdeal
    rw [c.tau_sigma f, GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_ne 𝒜 hf (Nat.pos_iff_ne_zero.mp hd)]
    exact zero_mem _
  · intro hy
    refine ⟨⟨y.asHomogeneousIdeal.comap c.psi, y.isPrime.comap c.psi.toRingHom, fun hle => ?_⟩,
      ProjectiveSpectrum.ext ((asHomogeneousIdeal_zeroSection c _).trans
        (comap_psi_comap_tau c y fun d hd f hf => hy d f hd hf))⟩
    obtain ⟨d, f, hd, hf, hfy⟩ := (mem_mapDomain_iff 𝒜 ℬ c.psi y).mp
      (by rw [projMapDomain_psi_eq_top c]; trivial)
    exact hfy (((HomogeneousIdeal.irrelevant_le 𝒜).mp hle) d hd hf)

/-! ### The punctured cone over a standard open -/

/-- **Over a standard open of `P` the part of `L` lying over `U` is itself a standard open.** On
`D₊(ψ f)` no positive-degree homogeneous element of `A` other than the multiples of `f` is needed
to cut out the part lying over `U`, because `σ f` divides `(σ g) ^ d * ψ f` for every
positive-degree homogeneous `g`. -/
theorem openUInL_inf_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    openUInL c ⊓ Proj.basicOpen ℬ (c.psi f) =
      Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f) := by
  rw [Proj.basicOpen_mul]
  refine le_antisymm ?_ ?_
  · rintro y ⟨hyU, hyf⟩
    obtain ⟨e, g, he, hg, hgy⟩ := (mem_openUInL_iff c y).mp hyU
    refine ⟨fun hsf => ?_, hyf⟩
    obtain ⟨z, hz⟩ := c.sigma_pow_mul_psi d e he f g hf hg
    have h1 : (c.sigma g : B) ^ d * c.psi f ∈ y.asHomogeneousIdeal.toIdeal := by
      rw [hz]
      exact Ideal.mul_mem_right _ _ hsf
    rcases y.isPrime.mem_or_mem h1 with h2 | h2
    · exact hgy (y.isPrime.mem_of_pow_mem d h2)
    · exact hyf h2
  · refine inf_le_inf_right _ ?_
    rw [openUInL_eq_iSup]
    exact le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le ⟨f, hf⟩ le_rfl))

/-- **The punctured cone is affine over `P`.** Over the standard open `D₊(f)` the part of `L`
lying over `U` is the standard open `D₊(σ f · ψ f)` of a positive-degree homogeneous element,
hence affine. -/
@[stacks 0EKG "U → P is affine"]
theorem isAffineHom_pi_restrict : IsAffineHom ((openUInL c).ι ≫ pi c) := by
  refine isAffineHom_of_isAffineOpen_preimage_basicOpen _ fun d f hf hd => ?_
  rw [Scheme.Hom.comp_preimage, pi_preimage_basicOpen c f d hf hd]
  refine ((openUInL c).ι.isAffineOpen_iff_of_isOpenImmersion).mp ?_
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    openUInL_inf_basicOpen c f d hf hd]
  exact Proj.isAffineOpen_basicOpen ℬ _
    (by simpa using SetLike.mul_mem_graded (c.sigma f).2 (c.psi.map_mem hf)) hd

/-! ### The two commuting squares -/

/-- The degree-zero part of `ψ` is `σ` restricted to `A₀`. -/
private theorem zeroHom_psi :
    zeroHom 𝒜 ℬ c.psi = c.sigma.toRingHom.comp (algebraMap (𝒜 0) A) := by
  ext a
  rw [coe_zeroHom_apply, RingHom.comp_apply]
  exact c.psi_apply_of_mem_zero (a : A) a.2

/-- The degree-zero part of `τ`, precomposed with `σ`, is the projection of `A` onto `A₀`. -/
private theorem zeroHom_tau_comp_sigma :
    (zeroHom ℬ 𝒜 c.tau).comp c.sigma.toRingHom = GradedRing.projZeroRingHom' 𝒜 := by
  ext a
  rw [RingHom.comp_apply, coe_zeroHom_apply, GradedRing.coe_projZeroRingHom'_apply]
  exact c.tau_sigma a

/-- **The right square commutes**: `L → P → Z` equals `L → X → Z`. -/
@[stacks 0EKG "the square L → P, X → Z commutes"]
theorem pi_comp_toSpecZero :
    pi c ≫ Proj.toSpecZero 𝒜 = toSpecA c ≫ xToZ 𝒜 := by
  rw [pi, mapHomOfTop_toSpecZero 𝒜 ℬ c.psi (projMapDomain_psi_eq_top c), toSpecA, xToZ,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, zeroHom_psi c]

/-- **The left square commutes**: `P → L → X` equals `P → Z → X`. -/
@[stacks 0EKG "the square P → L, Z → X commutes"]
theorem zeroSection_comp_toSpecA :
    zeroSection c ≫ toSpecA c = Proj.toSpecZero 𝒜 ≫ zToX 𝒜 := by
  rw [toSpecA, zeroSection_eq_mapHomOfTop, ← Category.assoc,
    mapHomOfTop_toSpecZero ℬ 𝒜 c.tau (projMapDomain_tau_eq_top c), zToX, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, zeroHom_tau_comp_sigma c]

end Cone

end Stacks.AlgebraicGeometry.ProjAndSpec

end
