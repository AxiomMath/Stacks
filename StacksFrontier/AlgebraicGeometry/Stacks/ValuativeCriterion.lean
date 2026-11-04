module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.DottedArrows.Composition

/-!
# The existence part of the valuative criterion for algebraic stacks

A *valuative square* for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a valuation
ring `R` with fraction field `K`, both of whose spectra lie in the chosen big fppf site, a
structure morphism `Spec R ⟶ S`, the canonical map `j : Spec K ⟶ Spec R` read in the
2-category of categories fibred in groupoids, a generic point `x : Spec K ⟶ 𝒳`, a special point
`y : Spec R ⟶ 𝒴` and a 2-morphism `γ : j ≫ y ⟶ x ≫ f` filling the square. The morphism `f`
*satisfies the existence part of the valuative criterion* when every such square admits a dotted
arrow after an extension `K'/K` of fields and a dominating valuation ring `R' ⊂ K'`.

This file defines the criterion and proves that it is stable under composition.

## Main definitions

* `AlgebraicGeometry.Stack.ValuativeSquare`: the solid part of a valuative square.
* `AlgebraicGeometry.Stack.ValuativeSquare.DominatingExtension`: a dominating extension of a
  valuative square.
* `AlgebraicGeometry.Stack.ValuativeCriterion.Existence`: the existence part of the valuative
  criterion.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionExistence_comp`: the existence part of the valuative
  criterion is stable under composition.
* `CategoryTheory.CatFiberedInGroupoids.lower_compat`: the pasting identity for a 2-commutative
  rectangle split into two squares, for arbitrary 1- and 2-morphisms of the 2-category of
  categories fibred in groupoids.

## Implementation notes

The 2-category of categories fibred in groupoids is strict: its associators are identities, by
`rfl`, and `assocInv_comp` and its companions cancel them. `ValuativeSquare.compRight` and
`ValuativeSquare.compUpper` are `@[implicit_reducible]`, so that their projections reduce at
reducible transparency.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLM](https://stacks.math.columbia.edu/tag/0CLM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

universe u w u₁ u₂ v₁ v₂

namespace CategoryTheory.CatFiberedInGroupoids

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

section Pasting

variable {W X Y Z : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- The 2-category of categories fibred in groupoids is strict, so an inverse associator
cancels against whatever follows it. -/
theorem assocInv_comp (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : ((u ≫ v) ≫ w) ⟶ V) : (α_ u v w).inv ≫ t = t := Category.id_comp t

/-- An associator cancels against whatever follows it. -/
theorem assocHom_comp (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : (u ≫ v ≫ w) ⟶ V) : (α_ u v w).hom ≫ t = t := Category.id_comp t

/-- An inverse associator cancels against whatever precedes it. -/
theorem comp_assocInv (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : V ⟶ (u ≫ v ≫ w)) : t ≫ (α_ u v w).inv = t := Category.comp_id t

/-- An associator cancels against whatever precedes it. -/
theorem comp_assocHom (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : V ⟶ ((u ≫ v) ≫ w)) : t ≫ (α_ u v w).hom = t := Category.comp_id t

/-- `assocInv_comp` with the source of `t` spelled as the source, rather than the target, of the
associator. -/
theorem assocInv_comp' (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : (u ≫ v ≫ w) ⟶ V) : (α_ u v w).inv ≫ t = t := Category.id_comp t

/-- `assocHom_comp` in the other spelling. -/
theorem assocHom_comp' (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : ((u ≫ v) ≫ w) ⟶ V) : (α_ u v w).hom ≫ t = t := Category.id_comp t

/-- `comp_assocInv` in the other spelling. -/
theorem comp_assocInv' (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : V ⟶ ((u ≫ v) ≫ w)) : t ≫ (α_ u v w).inv = t := Category.comp_id t

/-- `comp_assocHom` in the other spelling. -/
theorem comp_assocHom' (u : W ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) {V : W ⟶ Z}
    (t : V ⟶ (u ≫ v ≫ w)) : t ≫ (α_ u v w).hom = t := Category.comp_id t

/-- Componentwise extensionality for 2-morphisms: a 2-morphism of categories fibred in groupoids
is a natural transformation of the underlying functors, so two of them agree as soon as all their
components do. -/
theorem hom₂_ext_app {u v : W ⟶ Z} {η θ : u ⟶ v}
    (h : ∀ A, η.hom.toNatTrans.app A = θ.hom.toNatTrans.app A) : η = θ := by
  refine Bicategory.InducedBicategory.hom₂_ext ?_
  exact BasedNatTrans.ext _ _ (NatTrans.ext (funext h))

variable {A₀ A₁ A₂ A₃ A₄ A₅ : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- The normal form of the pasting of a 2-commutative square against a 2-commutative rectangle:
in this strict 2-category every associator in the pasting is an identity. -/
theorem pastingForm
    (j : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (y : A₂ ⟶ A₃)
    (k : A₀ ⟶ A₄) (j₀ : A₄ ⟶ A₂) (x : A₄ ⟶ A₅) (F : A₅ ⟶ A₃)
    (c : (j ≫ a) ⟶ (k ≫ j₀)) (γ : (j₀ ≫ y) ⟶ (x ≫ F)) :
    (α_ j a y).inv ≫ (c ▷ y) ≫ (α_ k j₀ y).hom ≫ (k ◁ γ) ≫ (α_ k x F).inv
      = (c ▷ y) ≫ (k ◁ γ) := by
  rw [assocInv_comp, assocHom_comp, comp_assocInv]
  rfl

end Pasting

section LowerCompat

variable {S₂ T₂ S₁ T₁ S₀ T₀ XX YY ZZ : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- A pasting identity in the 2-category of categories fibred in groupoids: given a 2-commutative
rectangle split into two squares by `c₁` and `c₂`, and a dotted arrow `(b₁, α₁, β₁)` for the lower
square whose pasting equation is `h₁`, the 2-cell assembled from `c₁`, `c₂` and the outer witness
`γ` is the pasting of `α₁` and `β₁` along the upper square. -/
theorem lower_compat
    (j₂ : S₂ ⟶ T₂) (a₂ : T₂ ⟶ T₁) (k₂ : S₂ ⟶ S₁) (j₁ : S₁ ⟶ T₁)
    (a₁ : T₁ ⟶ T₀) (k₁ : S₁ ⟶ S₀) (j₀ : S₀ ⟶ T₀)
    (x : S₀ ⟶ XX) (y : T₀ ⟶ ZZ) (F : XX ⟶ YY) (G : YY ⟶ ZZ)
    (c₂ : (j₂ ≫ a₂) ⟶ (k₂ ≫ j₁)) (c₁ : (j₁ ≫ a₁) ⟶ (k₁ ≫ j₀))
    (γ : (j₀ ≫ y) ⟶ (x ≫ F ≫ G))
    (b₁ : T₁ ⟶ YY) (α₁ : (j₁ ≫ b₁) ⟶ (k₁ ≫ (x ≫ F))) (β₁ : (a₁ ≫ y) ⟶ (b₁ ≫ G))
    (h₁ : (α_ j₁ a₁ y).inv ≫ (c₁ ▷ y) ≫ (α_ k₁ j₀ y).hom ≫
            (k₁ ◁ (γ ≫ (α_ x F G).inv)) ≫ (α_ k₁ (x ≫ F) G).inv
          = (j₁ ◁ β₁) ≫ (α_ j₁ b₁ G).inv ≫ (α₁ ▷ G)) :
    ((α_ j₂ (a₂ ≫ a₁) y).inv ≫
        (((α_ j₂ a₂ a₁).inv ≫ (c₂ ▷ a₁) ≫ (α_ k₂ j₁ a₁).hom ≫ (k₂ ◁ c₁) ≫
            (α_ k₂ k₁ j₀).inv) ▷ y) ≫
        (α_ (k₂ ≫ k₁) j₀ y).hom ≫ ((k₂ ≫ k₁) ◁ γ) ≫
          (α_ (k₂ ≫ k₁) x (F ≫ G)).inv) ≫ (α_ ((k₂ ≫ k₁) ≫ x) F G).inv
      = (j₂ ◁ ((α_ a₂ a₁ y).hom ≫ (a₂ ◁ β₁) ≫ (α_ a₂ b₁ G).inv)) ≫
          (α_ j₂ (a₂ ≫ b₁) G).inv ≫
          ((((α_ j₂ a₂ b₁).inv ≫ (c₂ ▷ b₁) ≫ (α_ k₂ j₁ b₁).hom ≫
              (k₂ ◁ (α₁ ≫ (α_ k₁ x F).inv)) ≫ (α_ k₂ (k₁ ≫ x) F).inv) ≫
            ((α_ k₂ k₁ x).inv ▷ F)) ▷ G) := by
  rw [pastingForm j₁ a₁ y k₁ j₀ (x ≫ F) G c₁ (γ ≫ (α_ x F G).inv),
    comp_assocInv x F G γ, assocInv_comp j₁ b₁ G (α₁ ▷ G)] at h₁
  simp only [Category.assoc]
  repeat first
    | rw [assocInv_comp] | rw [assocHom_comp] | rw [comp_assocInv] | rw [comp_assocHom]
    | rw [assocInv_comp'] | rw [assocHom_comp'] | rw [comp_assocInv'] | rw [comp_assocHom']
  refine hom₂_ext_app fun A => ?_
  have hc := fun B => congrArg (fun t : (j₁ ≫ a₁ ≫ y) ⟶ _ => t.hom.toNatTrans.app B) h₁
  have hn := β₁.hom.toNatTrans.naturality (c₂.hom.toNatTrans.app A)
  have hc' : ∀ B, y.hom.toFunctor.map (c₁.hom.toNatTrans.app B)
        ≫ γ.hom.toNatTrans.app (k₁.hom.toFunctor.obj B)
      = β₁.hom.toNatTrans.app (j₁.hom.toFunctor.obj B)
        ≫ G.hom.toFunctor.map (α₁.hom.toNatTrans.app B) := hc
  have hn' : y.hom.toFunctor.map (a₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A))
        ≫ β₁.hom.toNatTrans.app (j₁.hom.toFunctor.obj (k₂.hom.toFunctor.obj A))
      = β₁.hom.toNatTrans.app (a₂.hom.toFunctor.obj (j₂.hom.toFunctor.obj A))
        ≫ G.hom.toFunctor.map (b₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A)) := hn
  have e2 : α₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A)
        ≫ F.hom.toFunctor.map (𝟙 _)
      = α₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A) := by
    rw [Functor.map_id]
    exact Category.comp_id _
  refine Eq.trans (congrArg
    (fun t => y.hom.toFunctor.map (a₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A)
        ≫ c₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A)) ≫ t)
    (Category.comp_id (γ.hom.toNatTrans.app
      (k₁.hom.toFunctor.obj (k₂.hom.toFunctor.obj A))))) ?_
  refine Eq.trans ?_ (congrArg
    (fun t => β₁.hom.toNatTrans.app (a₂.hom.toFunctor.obj (j₂.hom.toFunctor.obj A))
        ≫ G.hom.toFunctor.map (b₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A) ≫ t))
    e2.symm)
  refine Eq.trans (congrArg
    (fun t => t ≫ γ.hom.toNatTrans.app (k₁.hom.toFunctor.obj (k₂.hom.toFunctor.obj A)))
    (y.hom.toFunctor.map_comp (a₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A))
      (c₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun t => y.hom.toFunctor.map (a₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A)) ≫ t)
    (hc' (k₂.hom.toFunctor.obj A))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun t => t ≫ G.hom.toFunctor.map (α₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A)))
    hn') ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg
    (fun t => β₁.hom.toNatTrans.app (a₂.hom.toFunctor.obj (j₂.hom.toFunctor.obj A)) ≫ t)
    (G.hom.toFunctor.map_comp (b₁.hom.toFunctor.map (c₂.hom.toNatTrans.app A))
      (α₁.hom.toNatTrans.app (k₂.hom.toFunctor.obj A))).symm

end LowerCompat

end CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The solid part of a 2-commutative valuative square for a 1-morphism `f` of algebraic stacks:
a valuation ring with its fraction field, both of whose spectra lie in the chosen big fppf site, a
structure morphism to `S`, the canonical map between the two spectra and its realisation `j` in
the 2-category of categories fibred in groupoids, a generic point `x` of `𝒳`, a special point `y`
of `𝒴`, and a 2-morphism `γ` making the square 2-commute. -/
structure ValuativeSquare (f : 𝒳 ⟶ 𝒴) where
  /-- The valuation ring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the valuation ring. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The spectrum of the valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R))
  /-- The spectrum of the fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K))
  /-- The structure morphism of the spectrum of the valuation ring. -/
  base : Spec (.of R) ⟶ S
  /-- The canonical map from the generic point to the spectrum of the valuation ring, read in the
  big fppf category over `S`. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
    siteObject B S hS ring_mem base
  /-- The canonical map is the one induced by the inclusion of the valuation ring in its fraction
  field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  /-- The left edge of the square: the canonical map, read as a 1-morphism of categories fibred
  in groupoids. -/
  j : schemeFibredCategory B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)) ⟶
    schemeFibredCategory B S hS (siteObject B S hS ring_mem base)
  /-- The left edge is the canonical map. -/
  j_canonical : j.hom.toFunctor = Over.map genericMap
  /-- The generic point of `𝒳`. -/
  x : schemeFibredCategory B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)) ⟶ 𝒳.1
  /-- The special point of `𝒴`. -/
  y : schemeFibredCategory B S hS (siteObject B S hS ring_mem base) ⟶ 𝒴.1
  /-- The 2-morphism making the square 2-commute. -/
  γ : (j ≫ y) ⟶ (x ≫ f.hom)

namespace ValuativeSquare

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {f : 𝒳 ⟶ 𝒴}

/-- An extension `K'/K` of fields together with a valuation ring `R' ⊂ K'` dominating `R`, and the
diagram of represented spectra it induces: the maps `specialOver`, `genericOver` and `genericMap`
of site objects, their realisations `a`, `k` and `j` as 1-morphisms of categories fibred in
groupoids, and the 2-morphism `commute` filling the square of spectra. -/
structure DominatingExtension (q : ValuativeSquare B S hS f) where
  /-- The dominating valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [valuationRing : ValuationRing R']
  /-- The extension of the fraction field. -/
  K' : Type u
  [field : Field K']
  [algebra : Algebra R' K']
  [isFractionRing : IsFractionRing R' K']
  /-- The map of valuation rings. -/
  ringMap : q.R →+* R'
  /-- The map of fraction fields. -/
  fieldMap : q.K →+* K'
  /-- The map of valuation rings is local: this is the domination condition. -/
  isLocalHom : IsLocalHom ringMap
  /-- The two maps are compatible with the inclusions of the valuation rings in their fraction
  fields. -/
  fraction_comm :
    (algebraMap R' K').comp ringMap = fieldMap.comp (algebraMap q.R q.K)
  /-- The spectrum of the dominating valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R'))
  /-- The spectrum of the extended fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K'))
  /-- The map of spectra of valuation rings, as a map of site objects. -/
  specialOver : siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base
  /-- `specialOver` is the map induced by `ringMap`. -/
  specialOver_left : (B.inclusion).map specialOver.left =
    Spec.map (CommRingCat.ofHom ringMap)
  /-- The map of spectra of fraction fields, as a map of site objects. -/
  genericOver : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  /-- `genericOver` is the map induced by `fieldMap`. -/
  genericOver_left : (B.inclusion).map genericOver.left =
    Spec.map (CommRingCat.ofHom fieldMap)
  /-- The canonical map of the extended square, as a map of site objects. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)
  /-- The canonical map of the extended square is the one induced by the inclusion of the
  dominating valuation ring in its fraction field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  /-- The left edge of the extended square. -/
  j : schemeFibredCategory B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    schemeFibredCategory B S hS
      (siteObject B S hS ring_mem
        (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base))
  /-- The left edge of the extended square is the canonical map. -/
  j_canonical : j.hom.toFunctor = Over.map genericMap
  /-- The map from the extended special point to the original one. -/
  a : schemeFibredCategory B S hS
      (siteObject B S hS ring_mem
        (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base)
  /-- `a` is the map induced by `specialOver`. -/
  a_canonical : a.hom.toFunctor = Over.map specialOver
  /-- The map from the extended generic point to the original one. -/
  k : schemeFibredCategory B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    schemeFibredCategory B S hS
      (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
  /-- `k` is the map induced by `genericOver`. -/
  k_canonical : k.hom.toFunctor = Over.map genericOver
  /-- The 2-morphism filling the square of represented spectra. -/
  commute : (j ≫ a) ⟶ (k ≫ q.j)

attribute [instance] DominatingExtension.commRing DominatingExtension.domain
  DominatingExtension.valuationRing DominatingExtension.field
  DominatingExtension.algebra DominatingExtension.isFractionRing

/-- The 2-morphism filling the outer rectangle of a dominating extension, obtained by pasting the
square of represented spectra with the original square. -/
noncomputable def DominatingExtension.inducedGamma
    {q : ValuativeSquare B S hS f} (e : q.DominatingExtension) :
    (e.j ≫ (e.a ≫ q.y)) ⟶ ((e.k ≫ q.x) ≫ f.hom) :=
  (α_ e.j e.a q.y).inv ≫ (e.commute ▷ q.y) ≫
    (α_ e.k q.j q.y).hom ≫ (e.k ◁ q.γ) ≫
      (α_ e.k q.x f.hom).inv

/-- The data of a dominating extension of `q` based at a morphism `w` equal to
`Spec.map (CommRingCat.ofHom ringMap) ≫ q.base`, together with a dotted arrow for the square it
induces, give a dominating extension of `q` admitting a dotted arrow. -/
theorem exists_of_rebase (q : ValuativeSquare B S hS f)
    (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [ValuationRing R₂]
    (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂]
    (ringMap : q.R →+* R₂) (fieldMap : q.K →+* K₂)
    (hlocal : IsLocalHom ringMap)
    (hfrac : (algebraMap R₂ K₂).comp ringMap = fieldMap.comp (algebraMap q.R q.K))
    (ring_mem : B.Contains (Spec (.of R₂))) (field_mem : B.Contains (Spec (.of K₂)))
    (w : Spec (.of R₂) ⟶ S)
    (hw : Spec.map (CommRingCat.ofHom ringMap) ≫ q.base = w)
    (wg : Spec (.of K₂) ⟶ S)
    (hwg : Spec.map (CommRingCat.ofHom (algebraMap R₂ K₂)) ≫ w = wg)
    (specialOver : siteObject B S hS ring_mem w ⟶ siteObject B S hS q.ring_mem q.base)
    (hspecialOver : (B.inclusion).map specialOver.left =
      Spec.map (CommRingCat.ofHom ringMap))
    (genericOver : siteObject B S hS field_mem wg ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
    (hgenericOver : (B.inclusion).map genericOver.left =
      Spec.map (CommRingCat.ofHom fieldMap))
    (genericMap : siteObject B S hS field_mem wg ⟶ siteObject B S hS ring_mem w)
    (hgenericMap : (B.inclusion).map genericMap.left =
      Spec.map (CommRingCat.ofHom (algebraMap R₂ K₂)))
    (j : schemeFibredCategory B S hS (siteObject B S hS field_mem wg) ⟶
      schemeFibredCategory B S hS (siteObject B S hS ring_mem w))
    (hj : j.hom.toFunctor = Over.map genericMap)
    (a : schemeFibredCategory B S hS (siteObject B S hS ring_mem w) ⟶
      schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base))
    (ha : a.hom.toFunctor = Over.map specialOver)
    (k : schemeFibredCategory B S hS (siteObject B S hS field_mem wg) ⟶
      schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
    (hk : k.hom.toFunctor = Over.map genericOver)
    (commute : (j ≫ a) ⟶ (k ≫ q.j))
    (dotted : Nonempty (DottedArrow (k ≫ q.x) j f.hom (a ≫ q.y)
      ((α_ j a q.y).inv ≫ (commute ▷ q.y) ≫ (α_ k q.j q.y).hom ≫ (k ◁ q.γ) ≫
        (α_ k q.x f.hom).inv))) :
    ∃ e : q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma) := by
  subst hwg
  subst hw
  exact ⟨{ R' := R₂, K' := K₂, ringMap := ringMap, fieldMap := fieldMap,
           isLocalHom := hlocal, fraction_comm := hfrac,
           ring_mem := ring_mem, field_mem := field_mem,
           specialOver := specialOver, specialOver_left := hspecialOver,
           genericOver := genericOver, genericOver_left := hgenericOver,
           genericMap := genericMap, genericMap_left := hgenericMap,
           j := j, j_canonical := hj, a := a, a_canonical := ha,
           k := k, k_canonical := hk, commute := commute }, dotted⟩

end ValuativeSquare

namespace ValuativeCriterion

/-- A 1-morphism of algebraic stacks satisfies the *existence part of the valuative criterion* when
every valuative square for it admits a dotted arrow after an extension of the fraction field and
passage to a dominating valuation ring. -/
@[stacks 0CLK]
abbrev Existence (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : ValuativeSquare B S hS f,
    ∃ e : q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma)

end ValuativeCriterion

/-! ### Composition -/

namespace ValuativeSquare

variable {𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴 ⟶ 𝒵}

/-- A valuative square for a composite `f ≫ g`, read as a valuative square for `g` by composing
its generic point with `f`. -/
@[implicit_reducible]
noncomputable def compRight (q : ValuativeSquare B S hS (f ≫ g)) :
    ValuativeSquare B S hS g :=
  { q with
    x := q.x ≫ f.hom
    γ := q.γ ≫ (α_ q.x f.hom g.hom).inv }

/-- The valuative square for `f` left behind by a dominating extension `e₁` of the lower square
and a dotted arrow `d₁` filling it: it lives over the extended valuation ring, its generic point
is the extended generic point of `q`, and its special point is the diagonal of `d₁`. -/
@[implicit_reducible]
noncomputable def compUpper (q : ValuativeSquare B S hS (f ≫ g))
    (e₁ : (compRight B S hS q).DominatingExtension)
    (d₁ : DottedArrow (e₁.k ≫ (compRight B S hS q).x) e₁.j g.hom
      (e₁.a ≫ (compRight B S hS q).y) e₁.inducedGamma) :
    ValuativeSquare B S hS f where
  R := e₁.R'
  K := e₁.K'
  ring_mem := e₁.ring_mem
  field_mem := e₁.field_mem
  base := Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base
  genericMap := e₁.genericMap
  genericMap_left := e₁.genericMap_left
  j := e₁.j
  j_canonical := e₁.j_canonical
  x := e₁.k ≫ q.x
  y := d₁.a
  γ := d₁.α ≫ (α_ e₁.k q.x f.hom).inv

/-- `Spec` turns a composite of ring homomorphisms into the composite of the two maps of
spectra, in the other order. -/
theorem specMap_ofHom_comp {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
    (φ : A →+* A') (ψ : A' →+* A'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ))
      = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp]
  rfl

/-- The inclusion of the site carries a composite of maps of site objects to the composite of
the images. -/
private theorem inclusion_map_comp_left {U V W : BigFppfOver B S hS} (u : U ⟶ V) (v : V ⟶ W)
    {p : B.inclusion.obj U.left ⟶ B.inclusion.obj V.left}
    {q : B.inclusion.obj V.left ⟶ B.inclusion.obj W.left}
    (hu : (B.inclusion).map u.left = p) (hv : (B.inclusion).map v.left = q) :
    (B.inclusion).map (u ≫ v).left = p ≫ q := by
  rw [Over.comp_left, B.inclusion.map_comp, hu, hv]

/-- Composing two 1-morphisms induced by maps of site objects gives the one induced by the
composite. -/
private theorem comp_hom_toFunctor_eq_over_map {U V W : BigFppfOver B S hS} {u : U ⟶ V}
    {v : V ⟶ W} {a : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V}
    {b : schemeFibredCategory B S hS V ⟶ schemeFibredCategory B S hS W}
    (ha : a.hom.toFunctor = Over.map u) (hb : b.hom.toFunctor = Over.map v) :
    (a ≫ b).hom.toFunctor = Over.map (u ≫ v) :=
  (congrArg₂ Functor.comp ha hb).trans (Over.mapComp_eq _ _).symm

end ValuativeSquare

open ValuativeSquare in
/-- The composition of two 1-morphisms of algebraic stacks satisfying the existence part of the
valuative criterion satisfies it as well. -/
@[stacks 0CLM]
theorem valuativeCriterionExistence_comp
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : ValuativeCriterion.Existence B S hS f)
    (hg : ValuativeCriterion.Existence B S hS g) :
    ValuativeCriterion.Existence B S hS (f ≫ g) := by
  intro q
  obtain ⟨e₁, ⟨d₁⟩⟩ := hg (compRight B S hS q)
  obtain ⟨e₂, ⟨d₂⟩⟩ := hf (compUpper B S hS q e₁ d₁)
  refine exists_of_rebase B S hS q e₂.R' e₂.K'
    (e₂.ringMap.comp e₁.ringMap) (e₂.fieldMap.comp e₁.fieldMap)
    ⟨fun a ha => e₁.isLocalHom.map_nonunit a
      (e₂.isLocalHom.map_nonunit _ ha)⟩ ?_ e₂.ring_mem e₂.field_mem
    (Spec.map (CommRingCat.ofHom e₂.ringMap) ≫
      Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) ?_
    (Spec.map (CommRingCat.ofHom (algebraMap e₂.R' e₂.K')) ≫
      Spec.map (CommRingCat.ofHom e₂.ringMap) ≫
        Spec.map (CommRingCat.ofHom e₁.ringMap) ≫ q.base) rfl
    (e₂.specialOver ≫ e₁.specialOver) ?_
    (e₂.genericOver ≫ e₁.genericOver) ?_
    e₂.genericMap e₂.genericMap_left
    e₂.j e₂.j_canonical
    (e₂.a ≫ e₁.a) ?_
    (e₂.k ≫ e₁.k) ?_
    ((α_ e₂.j e₂.a e₁.a).inv ≫ (e₂.commute ▷ e₁.a) ≫ (α_ e₂.k e₁.j e₁.a).hom ≫
      (e₂.k ◁ e₁.commute) ≫ (α_ e₂.k e₁.k q.j).inv) ?_
  · ext x
    have h1 := RingHom.congr_fun e₁.fraction_comm x
    have h2 := RingHom.congr_fun e₂.fraction_comm (e₁.ringMap x)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    exact h2.trans (congrArg e₂.fieldMap h1)
  · exact (congrArg (· ≫ q.base) (specMap_ofHom_comp e₁.ringMap e₂.ringMap)).trans
      (Category.assoc _ _ _)
  · exact (inclusion_map_comp_left B S hS _ _ e₂.specialOver_left e₁.specialOver_left).trans
      (specMap_ofHom_comp e₁.ringMap e₂.ringMap).symm
  · exact (inclusion_map_comp_left B S hS _ _ e₂.genericOver_left e₁.genericOver_left).trans
      (specMap_ofHom_comp e₁.fieldMap e₂.fieldMap).symm
  · exact comp_hom_toFunctor_eq_over_map B S hS e₂.a_canonical e₁.a_canonical
  · exact comp_hom_toFunctor_eq_over_map B S hS e₂.k_canonical e₁.k_canonical
  · refine ⟨DottedArrow.ofLowerUpper _ _ _ _ _ _
      { a := e₂.a ≫ d₁.a
        α := e₂.inducedGamma ≫ ((α_ e₂.k e₁.k q.x).inv ▷ f.hom)
        β := (α_ e₂.a e₁.a q.y).hom ≫ (e₂.a ◁ d₁.β) ≫ (α_ e₂.a d₁.a g.hom).inv
        compat := ?_ }
      { a := d₂.a
        α := d₂.α ≫ (α_ e₂.k e₁.k q.x).inv
        β := d₂.β
        compat := ?_ }⟩
    · exact CatFiberedInGroupoids.lower_compat e₂.j e₂.a e₂.k e₁.j e₁.a e₁.k q.j q.x q.y
        f.hom g.hom e₂.commute e₁.commute q.γ d₁.a d₁.α d₁.β d₁.compat
    · refine Eq.trans (congrArg
        (fun t => t ≫ ((α_ e₂.k e₁.k q.x).inv ▷ f.hom)) d₂.compat) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => (e₂.j ◁ d₂.β) ≫ t) (Category.assoc _ _ _)) ?_
      exact congrArg (fun t => (e₂.j ◁ d₂.β) ≫ (α_ e₂.j d₂.a f.hom).inv ≫ t)
        (Bicategory.comp_whiskerRight d₂.α ((α_ e₂.k e₁.k q.x).inv) f.hom).symm

end AlgebraicGeometry.Stack

end
