module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Basic

/-!
# The section-value dictionary of Stacks Tag 02NP

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `α : X ⟶ Proj A` a morphism of schemes, and `L` an
invertible `𝒪_X`-module identified with `α⁎𝒪(1)`. A degree-one element `y` of `A` gives a global
section `α⁎y` of `α⁎𝒪(1)`, hence a global section of `L`. For a family `y_0, …, y_n` of degree-one
elements, the ratio `s_k / s_i` (`Stacks.ProjectiveFromSections.ratio`) of the resulting sections
is the inverse image along `α` of the degree-zero fraction `y_k / y_i` of `A_{(y_i)}`, read as a
section of `𝒪_{Proj A}` over the standard open `D₊(y_i)` through
`AlgebraicGeometry.Proj.awayToSection`.

## Main definitions

* `Stacks.CoordinateDictionary.pullbackTwistOne`: `α⁎𝒪(1)`.
* `Stacks.CoordinateDictionary.coordSection`: the global section of `α⁎𝒪(1)` attached to a
  degree-one element of `A`.
* `Stacks.CoordinateDictionary.coordSectionOn`: the degree-one section of `p`, restricted to the
  standard open `D₊(q)`.
* `Stacks.CoordinateDictionary.awayCoord`: the degree-zero fraction `p / q` of `A_{(q)}`, for `p`
  and `q` homogeneous of degree one.
* `Stacks.CoordinateDictionary.pullbackAwayCoord`: its inverse image along `α`, a section of
  `𝒪_X`.

## Main results

* `Stacks.CoordinateDictionary.coordSectionOn_eq_smul`: on `D₊(q)` the degree-one section of `p`
  is the fraction `p/q` times the degree-one section of `q`.
* `Stacks.CoordinateDictionary.resM_coordSection`: the restriction of `α⁎y` to an open inside
  `α⁻¹(D₊(q))` is the inverse image of `coordSectionOn`.
* `Stacks.CoordinateDictionary.resM_coordSection_eq_smul`: `(α⁎p)|_W = α^♯(p/q) · (α⁎q)|_W`.
* `Stacks.CoordinateDictionary.resO_ratio_eq_pullbackAwayCoord`: for a family `s` of global
  sections of an invertible `L` carried to the sections `α⁎y_i` by an isomorphism
  `α⁎𝒪(1) ≅ L`, the ratio `s_k / s_i` restricted to `W` is `α^♯(y_k/y_i)`.
* `Stacks.CoordinateDictionary.pullbackAwayCoord_self`: `α^♯(y_i/y_i) = 1`.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.ProjectiveFromSections
open Stacks.TwistPullbackRatio (O1)

universe u w

namespace Stacks.CoordinateDictionary

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (α : X ⟶ AlgebraicGeometry.Proj 𝒜)

/-! ### The section attached to a degree-one element -/

/-- `α⁎𝒪(1)`, the inverse image along `α` of the degree-one twisting sheaf. -/
abbrev pullbackTwistOne : X.Modules :=
  (Scheme.Modules.pullback α).obj (O1 𝒜)

/-- The global section of `α⁎𝒪(1)` attached to a degree-one element of `A`: the inverse image
along `α` of the global section of `𝒪(1)` of [Stacks, Tag 01MP]. -/
def coordSection (y : 𝒜 1) : Γ(pullbackTwistOne 𝒜 α, ⊤) :=
  pullbackSectionHom α (O1 𝒜) ⊤ ⊤ (by simp) (degreeSection 𝒜 1 y)

/-- The degree-one section of `p`, restricted to the standard open `D₊(q)`. -/
def coordSectionOn (q : A) (p : 𝒜 1) :
    Γ(O1 𝒜, AlgebraicGeometry.Proj.basicOpen 𝒜 q) :=
  (O1 𝒜).val.map (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒜 q))).op
    (degreeSection 𝒜 1 p)

/-- The degree-zero fraction `p / q` of `A_{(q)}`, for `p` and `q` homogeneous of degree one. -/
def awayCoord {q : A} (hq : q ∈ 𝒜 1) (p : 𝒜 1) : Away 𝒜 q :=
  Away.mk 𝒜 hq 1 (p : A) (by simp)

/-- The inverse image along `α` of the fraction `p/q`, as a section of `𝒪_X` over an open
inside `α⁻¹(D₊(q))`. -/
def pullbackAwayCoord {q : A} (hq : q ∈ 𝒜 1) {W : X.Opens}
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 q) (p : 𝒜 1) : Γ(X, W) :=
  α.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 q) W hle
    ((AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom (awayCoord 𝒜 hq p))

/-! ### The identity -/

/-- On `D₊(q)` the degree-one section of `p` is the fraction `p/q` times the degree-one section of
`q`. -/
theorem coordSectionOn_eq_smul {q : A} (hq : q ∈ 𝒜 1) (p : 𝒜 1) :
    coordSectionOn 𝒜 q p =
      (AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom (awayCoord 𝒜 hq p) •
        coordSectionOn 𝒜 q ⟨q, hq⟩ :=
  Stacks.TwistPullbackRatio.degreeSection_res_eq 𝒜 p.2 hq

/-- The restriction of `α⁎y` to an open inside `α⁻¹(D₊(q))` is the inverse image of the
degree-one section of `y` read over `D₊(q)`. -/
theorem resM_coordSection {q : A} {W : X.Opens}
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 q) (y : 𝒜 1) :
    resM (le_top : W ≤ ⊤) (coordSection 𝒜 α y) =
      pullbackSectionHom α (O1 𝒜) (AlgebraicGeometry.Proj.basicOpen 𝒜 q) W hle
        (coordSectionOn 𝒜 q y) := by
  rw [coordSectionOn, AlgebraicGeometry.pullbackSectionHom_map α (O1 𝒜) ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 q) le_top W hle (by simp) (degreeSection 𝒜 1 y)]
  exact Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom α
    (O1 𝒜) ⊤ ⊤ W (homOfLE le_top) (by simp) (by simp) (degreeSection 𝒜 1 y)

/-- `(α⁎p)|_W = α^♯(p/q) · (α⁎q)|_W` on any open `W` inside `α⁻¹(D₊(q))`. -/
theorem resM_coordSection_eq_smul {q : A} (hq : q ∈ 𝒜 1) {W : X.Opens}
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 q) (p : 𝒜 1) :
    resM (le_top : W ≤ ⊤) (coordSection 𝒜 α p) =
      pullbackAwayCoord 𝒜 α hq hle p • resM (le_top : W ≤ ⊤) (coordSection 𝒜 α ⟨q, hq⟩) := by
  rw [resM_coordSection 𝒜 α hle p, resM_coordSection 𝒜 α hle ⟨q, hq⟩,
    coordSectionOn_eq_smul 𝒜 hq p, AlgebraicGeometry.pullbackSectionHom_smul]
  rfl

/-! ### The dictionary -/

section Ratio

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- Restriction of a global section commutes with a morphism of `𝒪_X`-modules. -/
theorem resM_app {M N : X.Modules} (φ : M ⟶ N) (t : Γ(M, ⊤)) (W : X.Opens) :
    resM (le_top : W ≤ ⊤) (φ.app ⊤ t) = φ.app W (resM (le_top : W ≤ ⊤) t) := by
  have h := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (le_top : W ≤ ⊤)).op) t
  simpa using h.symm

/-- Let `α : X ⟶ Proj A`, let `L` be an invertible `𝒪_X`-module and `e : α⁎𝒪(1) ≅ L` an
isomorphism, let `y : ι → A` be a family of degree-one elements and let `s i` be the section of `L`
that `e` attaches to `y i`. Then on any open `W` inside both `α⁻¹(D₊(y i))` and the nonvanishing
open of `s i`, the ratio `s_k / s_i` is the inverse image along `α` of the degree-zero fraction
`y_k / y_i`. -/
theorem resO_ratio_eq_pullbackAwayCoord {ι : Type*} (e : pullbackTwistOne 𝒜 α ≅ L)
    (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤)) (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i)))
    (i k : ι) {W : X.Opens} (hW : W ≤ nvCover s i)
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (y i : A)) :
    resO hW (ratio s i k) = pullbackAwayCoord 𝒜 α (y i).2 hle (y k) := by
  refine (eq_of_smul_eq_smul (s i) hW ?_).symm
  rw [resO_ratio_smul s hW k]
  have h : ∀ j, resT W (s j) = e.hom.app W (resM (le_top : W ≤ ⊤) (coordSection 𝒜 α (y j))) :=
    fun j => by rw [hs j]; exact resM_app e.hom _ W
  have hq : (⟨((y i : 𝒜 1) : A), (y i).2⟩ : 𝒜 1) = y i := rfl
  rw [h k, h i, resM_coordSection_eq_smul 𝒜 α (y i).2 hle (y k), hq,
    Scheme.Modules.Hom.app_smul]

/-- The fraction `y_i/y_i` has inverse image `1` along `α`. -/
theorem pullbackAwayCoord_self {ι : Type*} (e : pullbackTwistOne 𝒜 α ≅ L)
    (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤)) (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i)))
    (i : ι) {W : X.Opens} (hW : W ≤ nvCover s i)
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (y i : A)) :
    pullbackAwayCoord 𝒜 α (y i).2 hle (y i) = 1 := by
  rw [← resO_ratio_eq_pullbackAwayCoord 𝒜 α e y s hs i i hW hle, ratio_self, resO_one]

end Ratio

end Stacks.CoordinateDictionary

end
