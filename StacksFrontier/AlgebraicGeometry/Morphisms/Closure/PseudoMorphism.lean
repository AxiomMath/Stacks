module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-morphisms of schemes

A *pseudo-map* from `X` to `Y` is a morphism into `Y` defined on a scheme-theoretically dense
open subscheme of `X`, and a *pseudo-morphism* is an equivalence class of pseudo-maps for the
relation "agree after restriction to a scheme-theoretically dense open". This is the variant of
the definition of a rational map in which the opens are required to be scheme-theoretically
dense rather than merely topologically dense. If `X` is reduced the two notions coincide.

## Main definitions

* `AlgebraicGeometry.Scheme.PseudoMap`: a morphism into `Y` defined on a scheme-theoretically
  dense open subscheme of `X`.
* `AlgebraicGeometry.Scheme.PseudoMap.equiv`: two pseudo-maps are equivalent if they agree
  after restriction to a scheme-theoretically dense open subscheme.
* `AlgebraicGeometry.Scheme.PseudoMorphism`: a pseudo-morphism from `X` to `Y` is an
  equivalence class of pseudo-maps.
* `AlgebraicGeometry.Scheme.PseudoMorphism.IsOver`: a pseudo-morphism of schemes over `S` is an
  `S`-pseudo-morphism if some pseudo-map in the equivalence class is an `S`-morphism.

## Main results

* `AlgebraicGeometry.Scheme.PseudoMap.equivalence_rel`: the relation on pseudo-maps is an
  equivalence relation.
* `AlgebraicGeometry.Scheme.PseudoMorphism.equivRationalMap`: for reduced `X`, pseudo-morphisms
  from `X` to `Y` are the same thing as rational maps from `X` to `Y`.
* `AlgebraicGeometry.Scheme.PseudoMorphism.isOver_iff_isOver_equivRationalMap`: that bijection
  matches the two notions of being a morphism over a base scheme.
* `AlgebraicGeometry.dense_of_isSchemeTheoreticallyDense`: a scheme-theoretically dense open
  subscheme is topologically dense.

## References

* [Stacks Project, Tag 01RX](https://stacks.math.columbia.edu/tag/01RX)
* [Stacks Project, Tag 01RS](https://stacks.math.columbia.edu/tag/01RS)
* [Stacks Project, Tag 01RF](https://stacks.math.columbia.edu/tag/01RF)
* [Stacks Project, Tag 056D](https://stacks.math.columbia.edu/tag/056D)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-- A scheme-theoretically dense open subscheme is topologically dense. -/
theorem dense_of_isSchemeTheoreticallyDense (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) : Dense (U : Set X) := by
  refine dense_iff_inter_open.2 fun O hO hOne => ?_
  by_contra hdis
  let V : X.Opens := ⟨O, hO⟩
  have hbot : V.ι ⁻¹ᵁ U = ⊥ :=
    le_antisymm (fun x hx => (hdis ⟨x.1, x.2, hx⟩).elim) bot_le
  have hdom : IsSchemeTheoreticallyDominant ((⊥ : V.toScheme.Opens).ι) := hbot ▸ hU V
  have hqc : QuasiCompact ((⊥ : V.toScheme.Opens).ι) := by
    refine ⟨fun P _ _ => ?_⟩
    convert isCompact_empty (X := (⊥ : V.toScheme.Opens).toScheme) using 1
    exact Set.eq_empty_iff_forall_notMem.mpr fun z _ => z.2.elim
  obtain ⟨x, hx⟩ := hOne
  have : Nonempty V.toScheme := ⟨⟨x, hx⟩⟩
  obtain ⟨z⟩ := (IsDominant.denseRange (f := (⊥ : V.toScheme.Opens).ι)).nonempty
  exact z.2.elim

namespace Scheme

/-- A pseudo-map from `X` to `Y` is a morphism into `Y` defined on a scheme-theoretically dense
open subscheme of `X`. This is the variant of `AlgebraicGeometry.Scheme.PartialMap` in which the
domain of definition is required to be scheme-theoretically dense. -/
@[stacks 01RX "the pseudo-maps: morphisms into `Y` defined on scheme-theoretically dense opens
of `X`, the objects whose equivalence classes the remark calls pseudo-morphisms"]
structure PseudoMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a pseudo-map. -/
  domain : X.Opens
  /-- The domain of definition of a pseudo-map is scheme-theoretically dense. -/
  isSchemeTheoreticallyDense_domain : Opens.IsSchemeTheoreticallyDense domain
  /-- The underlying morphism of a pseudo-map. -/
  hom : ↑domain ⟶ Y

variable (S) in
/-- A pseudo-map is an `S`-map if the underlying morphism is. -/
abbrev PseudoMap.IsOver [X.Over S] [Y.Over S] (f : X.PseudoMap Y) := f.hom.IsOver S

namespace PseudoMap

/-- The topologically dense partial map underlying a pseudo-map. -/
def toPartialMap (f : X.PseudoMap Y) : X.PartialMap Y where
  domain := f.domain
  dense_domain := dense_of_isSchemeTheoreticallyDense _ f.isSchemeTheoreticallyDense_domain
  hom := f.hom

/-- The domain of the partial map underlying a pseudo-map is its domain. -/
@[simp]
lemma toPartialMap_domain (f : X.PseudoMap Y) : f.toPartialMap.domain = f.domain := rfl

/-- The morphism of the partial map underlying a pseudo-map is its morphism. -/
@[simp]
lemma toPartialMap_hom (f : X.PseudoMap Y) : f.toPartialMap.hom = f.hom := rfl

/-- Two pseudo-maps are equal if and only if they have the same domain and their morphisms agree
under the identification of the domains. -/
lemma ext_iff (f g : X.PseudoMap Y) :
    f = g ↔ ∃ e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom := by
  refine ⟨by rintro rfl; simp, ?_⟩
  obtain ⟨U, hU, f⟩ := f
  obtain ⟨V, hV, g⟩ := g
  rintro ⟨rfl : U = V, e⟩
  congr 1
  simpa using e

/-- Two pseudo-maps with the same domain whose morphisms agree under the identification of the
domains are equal. -/
@[ext]
lemma ext (f g : X.PseudoMap Y) (e : f.domain = g.domain)
    (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g :=
  (ext_iff f g).mpr ⟨e, H⟩

/-- The restriction of a pseudo-map to a smaller scheme-theoretically dense domain. -/
@[simps hom domain]
noncomputable def restrict (f : X.PseudoMap Y) (U : X.Opens)
    (hU : Opens.IsSchemeTheoreticallyDense U) (hU' : U ≤ f.domain) : X.PseudoMap Y where
  domain := U
  isSchemeTheoreticallyDense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

/-- Two pseudo-maps are equivalent if they agree after restriction to a scheme-theoretically
dense open subscheme. -/
@[stacks 01RX "the equivalence relation on pseudo-maps: agreement after restriction to a
scheme-theoretically dense open", ega "IV 20.2.1"]
protected noncomputable def equiv (f g : X.PseudoMap Y) : Prop :=
  ∃ (W : X.Opens) (hW : Opens.IsSchemeTheoreticallyDense W) (hWl : W ≤ f.domain)
    (hWr : W ≤ g.domain), (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom

/-- Equivalence of pseudo-maps is reflexive. -/
@[refl]
lemma equiv.refl (f : X.PseudoMap Y) : f.equiv f :=
  ⟨f.domain, f.isSchemeTheoreticallyDense_domain, le_rfl, le_rfl, rfl⟩

/-- Equivalence of pseudo-maps is symmetric. -/
@[symm]
lemma equiv.symm {f g : X.PseudoMap Y} : f.equiv g → g.equiv f :=
  fun ⟨W, hW, hWl, hWr, e⟩ => ⟨W, hW, hWr, hWl, e.symm⟩

/-- Equivalence of pseudo-maps is transitive. -/
@[trans]
lemma equiv.trans {f g h : X.PseudoMap Y} : f.equiv g → g.equiv h → f.equiv h := by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, Opens.isSchemeTheoreticallyDense_inf W₁ W₂ hW₁ hW₂,
    inf_le_left.trans hW₁l, inf_le_right.trans hW₂r, ?_⟩
  simp only [restrict_hom] at e₁ e₂
  simp only [restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category.assoc, e₁, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_right hW₂r, ← e₂]
  simp only [homOfLE_homOfLE_assoc]
  rfl

/-- Equivalence of pseudo-maps is an equivalence relation. -/
@[stacks 01RX "equivalence relation, via stability of scheme-theoretic density under
intersection (Tag 01RF)"]
lemma equivalence_rel : Equivalence (@Scheme.PseudoMap.equiv X Y) where
  refl := equiv.refl
  symm := equiv.symm
  trans := equiv.trans

/-- The setoid of pseudo-maps under equivalence. -/
noncomputable instance : Setoid (X.PseudoMap Y) := ⟨@PseudoMap.equiv X Y, equivalence_rel⟩

/-- Equivalent pseudo-maps have equivalent underlying partial maps. -/
lemma toPartialMap_equiv {f g : X.PseudoMap Y} (h : f.equiv g) :
    f.toPartialMap.equiv g.toPartialMap := by
  obtain ⟨W, hW, hWl, hWr, e⟩ := h
  exact ⟨W, dense_of_isSchemeTheoreticallyDense W hW, hWl, hWr, e⟩

end PseudoMap

/-- A pseudo-morphism from `X` to `Y` is an equivalence class of pseudo-maps, where two
pseudo-maps are equivalent if they agree on a scheme-theoretically dense open subscheme. -/
@[stacks 01RX "the pseudo-morphisms from `X` to `Y`: the equivalence classes of pseudo-maps"]
noncomputable def PseudoMorphism (X Y : Scheme.{u}) : Type u :=
  @Quotient (X.PseudoMap Y) inferInstance

/-- A pseudo-map as a pseudo-morphism. -/
@[ega "IV 20.2.1"]
noncomputable def PseudoMap.toPseudoMorphism (f : X.PseudoMap Y) : X.PseudoMorphism Y :=
  Quotient.mk _ f

/-- Every pseudo-morphism is represented by a pseudo-map. -/
lemma PseudoMorphism.exists_rep (f : X.PseudoMorphism Y) :
    ∃ g : X.PseudoMap Y, g.toPseudoMorphism = f :=
  Quotient.exists_rep f

variable (S) in
/-- A pseudo-morphism is an `S`-pseudo-morphism if some pseudo-map in the equivalence class is
an `S`-morphism. -/
@[stacks 01RX "the `S`-pseudo-morphisms: the analogue for pseudo-morphisms of part (3) of the
definition of an `S`-rational map"]
class PseudoMorphism.IsOver [X.Over S] [Y.Over S] (f : X.PseudoMorphism Y) : Prop where
  exists_pseudoMap_over : ∃ g : X.PseudoMap Y, g.IsOver S ∧ g.toPseudoMorphism = f

/-- A pseudo-morphism as a rational map. -/
noncomputable def PseudoMorphism.toRationalMap (f : X.PseudoMorphism Y) : X.RationalMap Y :=
  Quotient.map PseudoMap.toPartialMap (fun _ _ h => PseudoMap.toPartialMap_equiv h) f

/-- The rational map of the pseudo-morphism of a pseudo-map is the rational map of its underlying
partial map. -/
@[simp]
lemma PseudoMap.toRationalMap_toPseudoMorphism (f : X.PseudoMap Y) :
    f.toPseudoMorphism.toRationalMap = f.toPartialMap.toRationalMap :=
  rfl

section IsReduced

variable [IsReduced X]

/-- A partial map from a reduced scheme as a pseudo-map. -/
@[ega "IV 20.2.16" "more general"]
noncomputable def PartialMap.toPseudoMap (f : X.PartialMap Y) : X.PseudoMap Y where
  domain := f.domain
  isSchemeTheoreticallyDense_domain := ((dense_open_tfae f.domain).out 1 3).mp f.dense_domain
  hom := f.hom

/-- The domain of the pseudo-map of a partial map is its domain. -/
@[simp]
lemma PartialMap.toPseudoMap_domain (f : X.PartialMap Y) :
    f.toPseudoMap.domain = f.domain := rfl

/-- The morphism of the pseudo-map of a partial map is its morphism. -/
@[simp]
lemma PartialMap.toPseudoMap_hom (f : X.PartialMap Y) : f.toPseudoMap.hom = f.hom := rfl

/-- Equivalent partial maps on a reduced scheme have equivalent associated pseudo-maps. -/
lemma PartialMap.toPseudoMap_equiv {f g : X.PartialMap Y} (h : f.equiv g) :
    f.toPseudoMap.equiv g.toPseudoMap := by
  obtain ⟨W, hW, hWl, hWr, e⟩ := h
  exact ⟨W, ((dense_open_tfae W).out 1 3).mp hW, hWl, hWr, e⟩

/-- A rational map from a reduced scheme as a pseudo-morphism. -/
noncomputable def RationalMap.toPseudoMorphism (f : X.RationalMap Y) : X.PseudoMorphism Y :=
  Quotient.map PartialMap.toPseudoMap (fun _ _ h => PartialMap.toPseudoMap_equiv h) f

/-- The pseudo-morphism of the rational map of a partial map is the pseudo-morphism of its
pseudo-map. -/
@[simp]
lemma PartialMap.toPseudoMorphism_toRationalMap (f : X.PartialMap Y) :
    f.toRationalMap.toPseudoMorphism = f.toPseudoMap.toPseudoMorphism :=
  rfl

/-- If `X` is reduced, pseudo-morphisms from `X` to `Y` are the same thing as rational maps from
`X` to `Y`. -/
@[stacks 01RX "agreement of pseudo-morphisms with rational maps for reduced `X`",
  ega "IV 20.2.7",
  ega "IV 20.4.3" "Identification"]
noncomputable def PseudoMorphism.equivRationalMap : X.PseudoMorphism Y ≃ X.RationalMap Y where
  toFun := PseudoMorphism.toRationalMap
  invFun := RationalMap.toPseudoMorphism
  left_inv := Quotient.ind fun _ => rfl
  right_inv := Quotient.ind fun _ => rfl

/-- `PseudoMorphism.equivRationalMap` sends a pseudo-morphism to its rational map. -/
@[simp]
lemma PseudoMorphism.equivRationalMap_apply (f : X.PseudoMorphism Y) :
    PseudoMorphism.equivRationalMap f = f.toRationalMap := rfl

/-- The inverse of `PseudoMorphism.equivRationalMap` sends a rational map to its
pseudo-morphism. -/
@[simp]
lemma PseudoMorphism.equivRationalMap_symm_apply (f : X.RationalMap Y) :
    PseudoMorphism.equivRationalMap.symm f = f.toPseudoMorphism := rfl

/-- The bijection between pseudo-morphisms and rational maps from a reduced scheme matches the
two notions of being a morphism over a base scheme. -/
@[ega "IV 20.2.7", ega "IV 20.4.3" "partial"]
lemma PseudoMorphism.isOver_iff_isOver_equivRationalMap [X.Over S] [Y.Over S]
    (f : X.PseudoMorphism Y) :
    f.IsOver S ↔ (PseudoMorphism.equivRationalMap f).IsOver S := by
  refine ⟨fun ⟨g, hg, hgf⟩ => ⟨g.toPartialMap, hg, by rw [← hgf]; rfl⟩,
    fun ⟨g, hg, hgf⟩ => ⟨g.toPseudoMap, hg, ?_⟩⟩
  rw [← PartialMap.toPseudoMorphism_toRationalMap, hgf]
  exact PseudoMorphism.equivRationalMap.symm_apply_apply f

end IsReduced

end Scheme

end AlgebraicGeometry
