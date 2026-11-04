module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartFractionDictionary

/-!
# The base-section dictionary: a degree-zero constant is a section of the base

The coordinate cut of [Stacks, Tag 02NP] runs two dictionaries at once. On the `Proj` side a
generator of an affine chart is a degree-zero fraction `b / y^D`, and
`Stacks.AwayFraction.mk_mem_closure_of_mem_adjoin` writes it as a polynomial **over the
degree-zero part `A₀` of the graded ring** in the coordinate ratios `y_m / y`. On the projective
space side the same generator has to be a polynomial in the chart coordinates `T_m / T_i` with
coefficients that are **sections of `𝒪_S`**, because that is what the chart `D₊(T_i) ⊓ pr⁻¹(V)`
of `ℙⁿ_S` offers. The two meet only once the degree-zero constants are known to be base sections,
and that is what this file proves.

The graded ring is the ring of global sections of a sheaf of graded algebras `A` over an affine
base, so the morphism `Proj A(S) ⟶ S` whose sections the comparison is about is
`Stacks.VeryAmpleAffineBase.projStructureHom`. Written out, that morphism **is** Mathlib's
`AlgebraicGeometry.Proj.toSpecZero` followed by the spectrum of the degree-zero structure map and
the affine identification of the base — `Stacks.BaseSectionDictionary.projStructureHom_eq`, which
holds by definition. No declaration in this development had compared the two before; the
comparison was recorded as the last missing ingredient of
`Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion`.

## Main results

* `Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen`: **the structure morphism of an
  absolute `Proj` on the sections of a standard open.** For `q` homogeneous of positive degree the
  ring map `Γ(Spec A₀, ⊤) ⟶ Γ(Proj A, D₊(q))` of `AlgebraicGeometry.Proj.toSpecZero` is
  `HomogeneousLocalization.fromZeroRingHom` followed by
  `AlgebraicGeometry.Proj.awayToSection`.
* `Stacks.BaseSectionDictionary.projStructureHom_eq`: the structure morphism of the absolute
  `Proj` of the graded ring of global sections is `AlgebraicGeometry.Proj.toSpecZero` followed by
  `Spec` of the degree-zero structure map and
  `AlgebraicGeometry.IsAffineOpen.fromSpec` of the base.
* `Stacks.BaseSectionDictionary.appLE_top_eq`: **the comparison of structure morphisms**, as an
  equality of ring maps `Γ(S, ⊤) ⟶ Γ(X, W)`.
* `Stacks.BaseSectionDictionary.pullbackAway_algebraMap_strZeroSheaf`: **the comparison in the
  form the coordinate cut consumes.** The inverse image along `α` of the degree-zero constant
  attached to a section `r` of `𝒪_S` is the inverse image of `r` along the structure morphism
  `f = α ≫ projStructureHom`.
* `Stacks.BaseSectionDictionary.pullbackAway_algebraMap_mem_range`: hence, when the degree-zero
  structure map is surjective, every inverse image of a degree-zero constant is a base section.

## Implementation notes

Everything is phrased with `AlgebraicGeometry.Scheme.Hom.appLE` and inverse images of opens.
The inequality arguments of `appLE` are taken as *named hypotheses* rather than written `le_top`
inline: `z ⁻¹ᵁ ⊤` is definitionally `⊤`, so an inline `le_top` elaborates at the collapsed type
and then no `rw` matches the resulting term, the pattern being present only up to `implicit`
transparency.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.VeryAmpleAffineBase

universe u w

namespace Stacks.BaseSectionDictionary

/-! ### Two pieces of `appLE` plumbing -/

/-- A presheaf on the opens of a scheme sends every endomorphism of an object to the identity. -/
private theorem presheaf_map_self {X : Scheme.{u}} {U : X.Opens}
    (f : Opposite.op U ⟶ Opposite.op U) : X.presheaf.map f = 𝟙 _ :=
  (congrArg X.presheaf.map (Subsingleton.elim f (𝟙 _))).trans (X.presheaf.map_id _)

/-- `AlgebraicGeometry.Scheme.Hom.appLE` at the two top opens is
`AlgebraicGeometry.Scheme.Hom.appTop`. -/
theorem appTop_eq_appLE {X Y : Scheme.{u}} (z : X ⟶ Y) (e : (⊤ : X.Opens) ≤ z ⁻¹ᵁ ⊤) :
    z.appLE ⊤ ⊤ e = z.appTop := by
  exact (congrArg (z.app ⊤ ≫ ·) (presheaf_map_self _)).trans (Category.comp_id _)

/-- The inclusion of an open subscheme, on the sections of that open, is
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
alias ι_appLE_top := Stacks.ChartDictionary.ι_appLE_top

/-- Two equal morphisms have the same ring map on a pair of opens. -/
theorem appLE_congr {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') (W : Z.Opens) (T : Y.Opens)
    (e : T ≤ g ⁻¹ᵁ W) (e' : T ≤ g' ⁻¹ᵁ W) : g.appLE W T e = g'.appLE W T e' := by
  subst h; rfl

/-- **The canonical morphism `Spec 𝒪_X(U) ⟶ X` of an affine open, on the sections of `U`**: it is
the inverse of `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem fromSpec_appLE_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  have hid : (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
      (Spec Γ(X, U)).presheaf.map (homOfLE e).op = 𝟙 Γ(Spec Γ(X, U), ⊤) := by
    rw [← Functor.map_comp]
    exact presheaf_map_self _
  calc hU.fromSpec.appLE U ⊤ e
      = hU.fromSpec.app U ≫ (Spec Γ(X, U)).presheaf.map (homOfLE e).op := rfl
    _ = ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op) ≫
          (Spec Γ(X, U)).presheaf.map (homOfLE e).op := by rw [hU.fromSpec_app_self]
    _ = (Scheme.ΓSpecIso Γ(X, U)).inv := by rw [Category.assoc, hid, Category.comp_id]

/-! ### The structure morphism of the absolute `Proj` on sections of a standard open -/

section Proj

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {q : A} {m : ℕ}

/-- **The structure morphism `Proj A ⟶ Spec A₀` on the sections of a standard open.** For `q`
homogeneous of positive degree the ring map from the global sections of `Spec A₀` to the sections
of `𝒪_{Proj A}` over `D₊(q)` is the inclusion `A₀ ⟶ A₍q₎` of the degree-zero constants followed
by the identification `A₍q₎ ⟶ Γ(Proj A, D₊(q))` of `AlgebraicGeometry.Proj.awayToSection`.

`AlgebraicGeometry.Proj.awayι_toSpecZero` is the same statement one chart down, as an equality of
morphisms out of `Spec A₍q₎`; this reads it on sections, the passage being
`AlgebraicGeometry.Proj.basicOpenToSpec_app_top` and the naturality of
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem toSpecZero_appLE_basicOpen (hq : q ∈ 𝒜 m) (hm : 0 < m)
    (e : AlgebraicGeometry.Proj.basicOpen 𝒜 q ≤
      AlgebraicGeometry.Proj.toSpecZero 𝒜 ⁻¹ᵁ ⊤) :
    (AlgebraicGeometry.Proj.toSpecZero 𝒜).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen 𝒜 q) e =
      (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers q)) ≫
        AlgebraicGeometry.Proj.awayToSection 𝒜 q := by
  have hmor : (AlgebraicGeometry.Proj.basicOpen 𝒜 q).ι ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 q hq hm).hom ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers q))) := by
    rw [← AlgebraicGeometry.Proj.awayι_toSpecZero 𝒜 q hq hm, AlgebraicGeometry.Proj.awayι,
      Category.assoc, Iso.hom_inv_id_assoc]
  have etop : (⊤ : (AlgebraicGeometry.Proj.basicOpen 𝒜 q).toScheme.Opens) ≤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 q).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 q :=
    fun x _ => x.2
  have hL : (AlgebraicGeometry.Proj.toSpecZero 𝒜).appLE ⊤
        (AlgebraicGeometry.Proj.basicOpen 𝒜 q) e ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 q).topIso.inv =
      ((AlgebraicGeometry.Proj.basicOpen 𝒜 q).ι ≫
        AlgebraicGeometry.Proj.toSpecZero 𝒜).appTop := by
    rw [← ι_appLE_top (AlgebraicGeometry.Proj.basicOpen 𝒜 q) etop,
      Scheme.Hom.appLE_comp_appLE, appTop_eq_appLE]
  have hbts : (AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 q).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 q))).hom ≫
        AlgebraicGeometry.Proj.awayToSection 𝒜 q ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 q).topIso.inv :=
    AlgebraicGeometry.Proj.basicOpenToSpec_app_top 𝒜 q
  have hR : ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 q hq hm).hom ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers q)))).appTop =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers q)) ≫
        AlgebraicGeometry.Proj.awayToSection 𝒜 q) ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 q).topIso.inv := by
    rw [Scheme.Hom.comp_appTop, AlgebraicGeometry.Proj.basicOpenIsoSpec_hom, hbts,
      ← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  refine (cancel_mono (AlgebraicGeometry.Proj.basicOpen 𝒜 q).topIso.inv).mp ?_
  rw [hL, hmor, hR]

end Proj

/-! ### The comparison of structure morphisms -/

section Base

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (hS : IsAffineOpen (⊤ : S.Opens))

/-- **The structure morphism of the absolute `Proj` of the graded ring of global sections is
`AlgebraicGeometry.Proj.toSpecZero`**, followed by the spectrum of the degree-zero structure map
and the affine identification of the base. The two sides are definitionally equal: the chart of a
relative `Proj` over an affine open is built from exactly that composite. -/
theorem projStructureHom_eq :
    projStructureHom A hS = AlgebraicGeometry.Proj.toSpecZero (A.grading ⊤) ≫
      Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec := rfl

variable {X : Scheme.{u}} (α : X ⟶ AlgebraicGeometry.Proj (A.grading ⊤))
  {q : A.sectionRing ⊤} {m : ℕ}

/-- **The comparison of structure morphisms**, as an equality of ring maps
`Γ(S, ⊤) ⟶ Γ(X, W)`. For `W` inside the chart `α⁻¹(D₊(q))` of a standard open of a homogeneous
element of positive degree, the inverse image along `α ≫ projStructureHom` of a section of the
base is its image under the degree-zero structure map, read as a degree-zero constant of `A₍q₎`
and pulled back along `α`.

This is the statement that the two dictionaries of the coordinate cut of [Stacks, Tag 02NP]
agree on the coefficients. -/
theorem appLE_top_eq (hq : q ∈ A.grading ⊤ m) (hm : 0 < m) {W : X.Opens}
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q)
    (hW : W ≤ (α ≫ projStructureHom A hS) ⁻¹ᵁ ⊤) :
    (α ≫ projStructureHom A hS).appLE ⊤ W hW =
      strZeroSheaf A ⊤ ≫
        CommRingCat.ofHom
            (algebraMap ((A.grading ⊤) 0) (Away (A.grading ⊤) q)) ≫
          AlgebraicGeometry.Proj.awayToSection (A.grading ⊤) q ≫
            α.appLE (AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q) W hle := by
  have e₂ : AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q ≤
      AlgebraicGeometry.Proj.toSpecZero (A.grading ⊤) ⁻¹ᵁ ⊤ := le_top
  have e₁ : (⊤ : (Spec (CommRingCat.of ((A.grading ⊤) 0))).Opens) ≤
      (Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec) ⁻¹ᵁ ⊤ := le_top
  have e₀ : (⊤ : (Spec Γ(S, ⊤)).Opens) ≤ hS.fromSpec ⁻¹ᵁ ⊤ := le_top
  have e₀' : (⊤ : (Spec (CommRingCat.of ((A.grading ⊤) 0))).Opens) ≤
      Spec.map (strZeroSheaf A ⊤) ⁻¹ᵁ ⊤ := le_top
  -- The base leg.
  have hbase : (Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec).appLE ⊤ ⊤ e₁ =
      strZeroSheaf A ⊤ ≫ (Scheme.ΓSpecIso (CommRingCat.of ((A.grading ⊤) 0))).inv := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (strZeroSheaf A ⊤)) hS.fromSpec ⊤ ⊤ ⊤ e₀ e₀',
      fromSpec_appLE_top hS e₀, appTop_eq_appLE, Scheme.ΓSpecIso_inv_naturality]
  -- The two legs over `Proj`.
  have hchain : (AlgebraicGeometry.Proj.toSpecZero (A.grading ⊤) ≫
        Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec).appLE ⊤
        (AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q) (le_top.trans_eq rfl) =
      strZeroSheaf A ⊤ ≫
        CommRingCat.ofHom (algebraMap ((A.grading ⊤) 0) (Away (A.grading ⊤) q)) ≫
          AlgebraicGeometry.Proj.awayToSection (A.grading ⊤) q := by
    rw [← Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Proj.toSpecZero (A.grading ⊤))
        (Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec) ⊤ ⊤
        (AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q) e₁ e₂,
      hbase, toSpecZero_appLE_basicOpen (A.grading ⊤) hq hm e₂, Category.assoc,
      Iso.inv_hom_id_assoc]
  have hcomp : α ≫ projStructureHom A hS = α ≫ (AlgebraicGeometry.Proj.toSpecZero
      (A.grading ⊤) ≫ Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec) :=
    congrArg (fun z => α ≫ z) (projStructureHom_eq A hS)
  rw [appLE_congr hcomp ⊤ W hW (hcomp ▸ hW),
    ← Scheme.Hom.appLE_comp_appLE α (AlgebraicGeometry.Proj.toSpecZero (A.grading ⊤) ≫
      Spec.map (strZeroSheaf A ⊤) ≫ hS.fromSpec) ⊤
      (AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q) W (le_top.trans_eq rfl) hle,
    hchain]
  simp only [Category.assoc]

/-- **The comparison in the form the coordinate cut of [Stacks, Tag 02NP] consumes.** The inverse
image along `α` of the degree-zero constant of `A₍q₎` attached to a section `r` of `𝒪_S` — that
is, `Stacks.CoordinateDictionary.pullbackAway` of `algebraMap` of the degree-zero structure map of
`r` — is the inverse image of `r` along the structure morphism `f`. -/
theorem pullbackAway_algebraMap_strZeroSheaf (hq : q ∈ A.grading ⊤ m) (hm : 0 < m)
    {W : X.Opens} (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q)
    {f : X ⟶ S} (hf : α ≫ projStructureHom A hS = f) (hW : W ≤ f ⁻¹ᵁ ⊤) (r : Γ(S, ⊤)) :
    Stacks.CoordinateDictionary.pullbackAway (A.grading ⊤) α hle
        (algebraMap ((A.grading ⊤) 0) (Away (A.grading ⊤) q) (strZeroSheaf A ⊤ r)) =
      (f.appLE ⊤ W hW).hom r := by
  have hW' : W ≤ (α ≫ projStructureHom A hS) ⁻¹ᵁ ⊤ := hf ▸ hW
  rw [appLE_congr hf.symm ⊤ W hW hW', appLE_top_eq A hS α hq hm hle hW']
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  rfl

/-- **Every inverse image of a degree-zero constant is a base section**, as soon as the
degree-zero structure map `Γ(S, ⊤) ⟶ A₀` is surjective. This is the form in which
`Stacks.CoordinateDictionary.pullbackAway_mk_mem_closure` becomes a statement about the sections
the morphism to `ℙⁿ_S` reaches: its generating set is the inverse images of the degree-zero
constants together with the coordinate ratios, and the first half is here replaced by base
sections. -/
theorem pullbackAway_algebraMap_mem_range (hq : q ∈ A.grading ⊤ m) (hm : 0 < m)
    {W : X.Opens} (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading ⊤) q)
    {f : X ⟶ S} (hf : α ≫ projStructureHom A hS = f) (hW : W ≤ f ⁻¹ᵁ ⊤)
    (hsurj : Function.Surjective (strZeroSheaf A ⊤)) (r₀ : (A.grading ⊤) 0) :
    Stacks.CoordinateDictionary.pullbackAway (A.grading ⊤) α hle
        (algebraMap ((A.grading ⊤) 0) (Away (A.grading ⊤) q) r₀) ∈
      Set.range (fun r : Γ(S, ⊤) => (f.appLE ⊤ W hW).hom r) := by
  obtain ⟨r, hr⟩ := hsurj r₀
  exact ⟨r, (pullbackAway_algebraMap_strZeroSheaf A hS α hq hm hle hf hW r).symm.trans
    (congrArg (fun z => Stacks.CoordinateDictionary.pullbackAway (A.grading ⊤) α hle
      (algebraMap ((A.grading ⊤) 0) (Away (A.grading ⊤) q) z)) hr)⟩

end Base

end Stacks.BaseSectionDictionary

end
