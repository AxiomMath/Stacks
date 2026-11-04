module

public import StacksFrontier.RingTheory.MilnorPatching.DerivedEssentialImage

/-!
# Stacks 0DL7 on rings, over an arbitrary fibre product

`MilnorPatching.isIso_homEquiv_symm_of_distinguished_glueingMap` is the ring-level isomorphism
step of Stacks 0DL7 for the fibre product `B ×_A A'` of `RingFibreProduct.Situation`. On an affine
étale chart of a pushout of algebraic spaces the ring of the chart is a fibre product only up to
isomorphism, and the identification of the two composites of the direct images arises as the
conjugate of the composite of derived extensions of scalars. This file supplies both: the
statement over any ring `B''` forming a cartesian square of commutative rings, and the
identification of the conjugate of the square of derived extensions of scalars with the square of
derived restrictions of scalars.

## Main definitions

* `MilnorPatching.derivedRestrictCompOfEqIso`: derived restriction of scalars along a composite
  `g ∘ f = h`, as in `MilnorPatching.derivedRestrictFstCompIso`.
* `MilnorPatching.derivedRestrictRingSquareIso`: the two composites of derived restrictions of
  scalars around a commutative square of rings; for a fibre product it is
  `MilnorPatching.derivedRestrictCompIso`
  (`MilnorPatching.derivedRestrictRingSquareIso_fibreProduct`).
* `MilnorPatching.derivedExtensionSquareIso`: the two composites of derived extensions of scalars
  around a commutative square of rings, through the chosen model along the diagonal.
* `MilnorPatching.derivedRestrictScalarsEquivalence`: derived restriction of scalars along a ring
  isomorphism is an equivalence.

## Main results

* `MilnorPatching.conjugateEquiv_compModelIso_inv`: the conjugate of the composition isomorphism
  `StacksDraft.DerivedExtensionScalarsModelComp.compModelIso` of derived extension of scalars is
  the composition isomorphism of derived restriction of scalars.
* `MilnorPatching.glueingConjugateIso_derivedExtensionSquareIso`: hence the conjugate of the
  square of derived extensions of scalars is the square of derived restrictions of scalars.
* `MilnorPatching.derivedRestrictCompOfEqIso_assoc`: associativity of the derived composition
  isomorphisms of restriction of scalars.
* `MilnorPatching.isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap`: **the
  ring-level isomorphism step of Stacks 0DL7 over an arbitrary cartesian square of rings**, for
  arbitrary adjunctions whose right adjoints are isomorphic to derived restriction of scalars.
* `MilnorPatching.isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap_derivedExtension`:
  the same for the derived change-of-rings adjunctions and the conjugate of the square of derived
  extensions of scalars, the form in which the space-level proof meets it.

## Implementation notes

The conjugate of `compModelIso` is identified by testing against the comparison of the composite
model (`StacksDraft.DerivedExtensionScalarsModelComp.comp_hom_ext`), using the normal forms of the
unit and counit of the derived change-of-rings adjunction at localized complexes. The bookkeeping
of these computations is done in lemmas over abstract categories, whose category instances are
implicit: at the derived categories of modules, terms such as `(F ⋙ G).obj X` and
`G.obj (F.obj X)` agree only up to unfolding, which keyed rewriting does not cross. The
general statement is transported to `RingFibreProduct.Situation.fibreProduct` along the ring
isomorphism given by the cartesian square
(`MilnorPatching.isIso_homEquiv_symm_of_equivalence`), the compatibility being the
associativity of the derived composition isomorphisms.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w₁ w₂ w₃ w₄ u

namespace MilnorPatching

open CochainComplex.DerivedExtensionScalars (derivedExtensionScalarsAdjunction
  totalDerivedExtensionScalars derivedExtensionScalarsAdjunction_unit_app
  derivedExtensionScalarsAdjunction_counit_app)

section Generic

/-- A functor preserves `f ≫ g = 𝟙`. -/
private theorem map_comp_map_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) : F.map f ≫ F.map g = 𝟙 _ := by
  rw [← F.map_comp, h, F.map_id]

variable {𝒟₀ 𝒟₁ : Type*} {_ : Category 𝒟₀} {_ : Category 𝒟₁} in
/-- The bookkeeping of `MilnorPatching.comp_unit_app_comp_map_compComparisonOfEq`, over abstract
categories: a composite of the unit of `f`, `Rf` of a factorized unit of `g`, and a composition
isomorphism of restrictions, read on complexes. -/
theorem comp_unit_comp_map_eq_of_factorizations (Rf : 𝒟₁ ⥤ 𝒟₀)
    {p q₁ q₂ q₃ t : 𝒟₀} {a₁ a₂ a₃ a₄ a₅ : 𝒟₁}
    (ηf : p ⟶ Rf.obj a₁) (ηg : a₁ ⟶ a₅) (rc : a₅ ⟶ a₄) (αP : a₁ ⟶ a₂) (ψ : a₂ ⟶ a₃)
    (invg : a₃ ⟶ a₄) (facg : a₄ ⟶ a₃) (σ : Rf.obj a₄ ⟶ t) (uf : p ⟶ q₁) (invf₁ : q₁ ⟶ Rf.obj a₂)
    (ψf : q₁ ⟶ q₂) (invf₂ : q₂ ⟶ Rf.obj a₃) (facf₂ : Rf.obj a₃ ⟶ q₂) (cmp : q₂ ⟶ q₃)
    (invh : q₃ ⟶ t) (uh : p ⟶ q₃)
    (inner : ηg ≫ rc = αP ≫ ψ ≫ invg) (h₆ : ηf ≫ Rf.map αP = uf ≫ invf₁)
    (h₇ : ψf ≫ invf₂ = invf₁ ≫ Rf.map ψ) (h₈ : σ = Rf.map facg ≫ facf₂ ≫ cmp ≫ invh)
    (hg : invg ≫ facg = 𝟙 _) (hf : invf₂ ≫ facf₂ = 𝟙 _) (h₉ : uf ≫ ψf ≫ cmp = uh) :
    (ηf ≫ Rf.map ηg) ≫ Rf.map rc ≫ σ = uh ≫ invh := by
  subst h₈ h₉
  rw [Category.assoc, ← Rf.map_comp_assoc ηg rc, inner, Rf.map_comp, Rf.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% map_comp_map_eq_id Rf hg, reassoc_of% h₆, ← reassoc_of% h₇, reassoc_of% hf]

variable {𝒟₀ 𝒟₂ : Type*} {_ : Category 𝒟₀} {_ : Category 𝒟₂} in
/-- The bookkeeping of `MilnorPatching.conjugateEquiv_compModelIso_inv`, over abstract
categories: the transpose of a unit against a comparison, read on complexes. -/
theorem map_comp_counit_comp_eq_of_factorizations (L : 𝒟₀ ⥤ 𝒟₂) (Rh : 𝒟₂ ⥤ 𝒟₀)
    {p y₁ y₂ q : 𝒟₀} {Y Z X V : 𝒟₂} (η₁ : p ⟶ y₁) (σY : y₁ ⟶ Rh.obj Y) (εY : L.obj (Rh.obj Y) ⟶ Y)
    (c : Y ⟶ Z) (rrc : y₁ ⟶ y₂) (σZ : y₂ ⟶ Rh.obj Z) (εZ : L.obj (Rh.obj Z) ⟶ Z) (qu : p ⟶ q)
    (inv : q ⟶ Rh.obj Z) (γP : L.obj p ⟶ X) (γq : L.obj q ⟶ V) (eu : X ⟶ V) (ec : V ⟶ Z)
    (hσ : σY ≫ Rh.map c = rrc ≫ σZ) (hε : εY ≫ c = L.map (Rh.map c) ≫ εZ)
    (hC : η₁ ≫ rrc ≫ σZ = qu ≫ inv) (hcounit : L.map inv ≫ εZ = γq ≫ ec)
    (hγ : L.map qu ≫ γq = γP ≫ eu) :
    L.map η₁ ≫ L.map σY ≫ εY ≫ c = γP ≫ eu ≫ ec := by
  rw [hε, ← L.map_comp_assoc, ← L.map_comp_assoc, Category.assoc, hσ, hC, L.map_comp,
    Category.assoc, hcounit, reassoc_of% hγ]

variable {𝒟 𝒟' : Type*} {_ : Category 𝒟} {_ : Category 𝒟'} in
/-- The bookkeeping of `MilnorPatching.derivedRestrictCompOfEqIso_assoc`, over abstract
categories. -/
theorem assoc_of_factorizations (Ra : 𝒟' ⥤ 𝒟) {P0 P1 P2 P3 P4 : 𝒟'}
    {Z2 Z3 Z4 Z5 T W0 W1 : 𝒟} (x₁ : P0 ⟶ P1) (x₂ : P1 ⟶ P2) (c₁ : P2 ⟶ P3) (i₁ : P3 ⟶ P4)
    (h₁ : P4 ⟶ P3) (fa₃ : Ra.obj P3 ⟶ Z3) (c₂ : Z3 ⟶ Z4) (i₃ : Z4 ⟶ T) (fa₂ : Ra.obj P2 ⟶ Z2)
    (ac₁ : Z2 ⟶ Z3) (C₁ : Ra.obj P0 ⟶ W0) (rf : W0 ⟶ W1) (C₂ : Ra.obj P1 ⟶ W1) (c₃ : Z2 ⟶ Z5)
    (iab : Z5 ⟶ W1) (hab : W1 ⟶ Z5) (c₄ : Z5 ⟶ Z4) (C₄ : W0 ⟶ T)
    (hi₁ : i₁ ≫ h₁ = 𝟙 _) (hnat : Ra.map c₁ ≫ fa₃ = fa₂ ≫ ac₁) (hC : C₁ ≫ rf = Ra.map x₁ ≫ C₂)
    (hC₂ : C₂ = Ra.map x₂ ≫ fa₂ ≫ c₃ ≫ iab) (hiab : iab ≫ hab = 𝟙 _)
    (hC₄ : C₄ = rf ≫ hab ≫ c₄ ≫ i₃) (hcx : ac₁ ≫ c₂ = c₃ ≫ c₄) :
    Ra.map (x₁ ≫ x₂ ≫ c₁ ≫ i₁) ≫ Ra.map h₁ ≫ fa₃ ≫ c₂ ≫ i₃ = C₁ ≫ C₄ := by
  subst hC₂ hC₄
  rw [reassoc_of% hC]
  simp only [Ra.map_comp, Category.assoc, reassoc_of% map_comp_map_eq_id Ra hi₁,
    reassoc_of% hnat, reassoc_of% hiab, reassoc_of% hcx]

variable {𝒟 𝒟' : Type*} {_ : Category 𝒟} {_ : Category 𝒟'} in
/-- The bookkeeping of the compatibility `hc` transported along a further restriction, over
abstract categories. -/
theorem hc_of_factorizations (Re : 𝒟' ⥤ 𝒟) {x₀ x₁ x₂ x₃ x₄ x₅ : 𝒟'} {y₀ y₁ y₂ y₃ : 𝒟}
    (cX : x₀ ⟶ x₁) (eFX : x₁ ⟶ x₂) (eIp : x₂ ⟶ x₃) (eJX : x₀ ⟶ x₄) (eFp : x₄ ⟶ x₅)
    (sqX : x₅ ⟶ x₃) (C₂a : Re.obj x₂ ⟶ y₀) (resI : y₀ ⟶ y₁) (C₂b : Re.obj x₃ ⟶ y₁)
    (C₁a : Re.obj x₄ ⟶ y₂) (resF : y₂ ⟶ y₃) (C₁b : Re.obj x₅ ⟶ y₃) (dX : y₃ ⟶ y₁)
    (hc : cX ≫ eFX ≫ eIp = eJX ≫ eFp ≫ sqX) (nat₂ : C₂a ≫ resI = Re.map eIp ≫ C₂b)
    (nat₁ : C₁a ≫ resF = Re.map eFp ≫ C₁b) (co : Re.map sqX ≫ C₂b = C₁b ≫ dX) :
    Re.map cX ≫ (Re.map eFX ≫ C₂a) ≫ resI = (Re.map eJX ≫ C₁a) ≫ resF ≫ dX := by
  have h := congrArg (fun z ↦ Re.map z ≫ C₂b) hc
  simp only [Re.map_comp, Category.assoc] at h
  simp only [Category.assoc, nat₂, reassoc_of% nat₁, h, co]

variable {C D 𝒞 : Type*} {_ : Category C} {_ : Category D} {_ : Category 𝒞} in
/-- The transpose, for an adjunction precomposed with an equivalence, of the image of a morphism
under the inverse of the equivalence. -/
theorem homEquiv_symm_map_inverse_comp (E : D ≌ C) {L : C ⥤ 𝒞} {R : 𝒞 ⥤ C} (adj : L ⊣ R)
    {X : C} {Y : 𝒞} (x : X ⟶ R.obj Y) :
    ((E.toAdjunction.comp adj).homEquiv (E.inverse.obj X) Y).symm (E.inverse.map x) =
      L.map (E.counit.app X) ≫ (adj.homEquiv X Y).symm x := by
  rw [Adjunction.comp_homEquiv, Equiv.symm_trans_apply, Adjunction.homEquiv_counit E.toAdjunction,
    Equivalence.toAdjunction_counit, Equivalence.counit_naturality,
    Adjunction.homEquiv_naturality_left_symm]

/-- If the transpose of the image under `E.inverse` of `x` is an isomorphism, so is that of `x`. -/
private theorem isIso_homEquiv_symm_of_isIso_map_inverse {C D 𝒞 : Type*} [Category C]
    [Category D] [Category 𝒞] (E : D ≌ C) {L : C ⥤ 𝒞} {R : 𝒞 ⥤ C} (adj : L ⊣ R) {X : C} {Y : 𝒞}
    (x : X ⟶ R.obj Y)
    (h : IsIso (((E.toAdjunction.comp adj).homEquiv (E.inverse.obj X) Y).symm (E.inverse.map x))) :
    IsIso ((adj.homEquiv X Y).symm x) := by
  rw [homEquiv_symm_map_inverse_comp E adj] at h
  exact IsIso.of_isIso_comp_left (L.map (E.counit.app X)) _

section TransportStep

open Pretriangulated

variable {𝒟 𝒟' 𝒟₁ 𝒟₂ 𝒟₀ : Type*} {_ : Category 𝒟} {_ : Category 𝒟'} {_ : Category 𝒟₁}
  {_ : Category 𝒟₂} {_ : Category 𝒟₀} [Preadditive 𝒟] [Preadditive 𝒟']
  [HasBinaryBiproducts 𝒟] [HasBinaryBiproducts 𝒟'] [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ]
  [HasZeroObject 𝒟] [HasZeroObject 𝒟'] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒟' n).Additive] [Pretriangulated 𝒟] [Pretriangulated 𝒟']
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}

/-- **The isomorphism step of Stacks 0DL7 is invariant under an equivalence of the first
corner.** Let `E : 𝒟' ≌ 𝒟` be an equivalence whose inverse is a triangulated functor. If the
isomorphism step holds for the glueing map of `(M, K', α)` with respect to the adjunctions
precomposed with `E` and the identification `c` whiskered by `E.inverse`, it holds with respect
to the original adjunctions and `c`. -/
theorem isIso_homEquiv_symm_of_equivalence (E : 𝒟' ≌ 𝒟) [E.inverse.CommShift ℤ]
    [E.inverse.IsTriangulated] [E.inverse.Additive]
    (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
    (c : Rf ⋙ Rj ≅ Ri ⋙ Rf') (c' : Rf ⋙ (Rj ⋙ E.inverse) ≅ Ri ⋙ (Rf' ⋙ E.inverse))
    (hc' : ∀ X, c'.inv.app X = E.inverse.map (c.inv.app X))
    (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K')
    (hA : ∀ {N : 𝒟'} (u' : N ⟶ (Rj ⋙ E.inverse).obj M ⊞ (Rf' ⋙ E.inverse).obj K')
      (w' : (Rj ⋙ E.inverse).obj (Rf.obj (Li.obj K')) ⟶ N⟦(1 : ℤ)⟧),
      Triangle.mk u' (glueingMap adjF adjI c' M K' α) w' ∈ distTriang 𝒟' →
      IsIso (((E.toAdjunction.comp adjJ).homEquiv _ _).symm (u' ≫ biprod.fst)) ∧
        IsIso (((E.toAdjunction.comp adjF').homEquiv _ _).symm (u' ≫ biprod.snd)))
    {M' : 𝒟} (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K') (w : Rj.obj (Rf.obj (Li.obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u (glueingMap adjF adjI c M K' α) w ∈ distTriang 𝒟) :
    IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
      IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)) := by
  let φ : E.inverse.obj (Rj.obj M ⊞ Rf'.obj K') ≅
      (Rj ⋙ E.inverse).obj M ⊞ (Rf' ⋙ E.inverse).obj K' :=
    { hom := biprod.lift (E.inverse.map biprod.fst) (E.inverse.map biprod.snd)
      inv := biprod.desc (E.inverse.map biprod.inl) (E.inverse.map biprod.inr)
      hom_inv_id := by
        rw [biprod.lift_desc, ← E.inverse.map_comp, ← E.inverse.map_comp, ← E.inverse.map_add,
          biprod.total, E.inverse.map_id]
      inv_hom_id := by
        apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
          simp [← E.inverse.map_comp] }
  have hGL : glueingMap adjF adjI c' M K' α =
      φ.inv ≫ E.inverse.map (glueingMap adjF adjI c M K' α) := by
    apply biprod.hom_ext'
    · simp only [φ, inl_glueingMap, biprod.inl_desc_assoc, ← E.inverse.map_comp]
      rfl
    · rw [inr_glueingMap]
      simp only [φ, biprod.inr_desc_assoc]
      rw [← E.inverse.map_comp, inr_glueingMap, E.inverse.map_neg, E.inverse.map_comp, hc']
      rfl
  have hT' : Triangle.mk (E.inverse.map u ≫ φ.hom) (glueingMap adjF adjI c' M K' α)
      (E.inverse.map w ≫ (E.inverse.commShiftIso (1 : ℤ)).hom.app M') ∈ distTriang 𝒟' := by
    refine isomorphic_distinguished _ (E.inverse.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) φ.symm (Iso.refl _) ?_ ?_ ?_)
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) φ.hom_inv_id).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
    · exact (Category.comp_id _).trans hGL
    · exact (congrArg (_ ≫ ·) ((shiftFunctor 𝒟' (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ha, hb⟩ := hA _ _ hT'
  have hfst : (E.inverse.map u ≫ φ.hom) ≫ biprod.fst = E.inverse.map (u ≫ biprod.fst) := by
    simp [φ]
  have hsnd : (E.inverse.map u ≫ φ.hom) ≫ biprod.snd = E.inverse.map (u ≫ biprod.snd) := by
    simp [φ]
  rw [hfst] at ha
  rw [hsnd] at hb
  exact ⟨isIso_homEquiv_symm_of_isIso_map_inverse E adjJ _ ha,
    isIso_homEquiv_symm_of_isIso_map_inverse E adjF' _ hb⟩

end TransportStep

end Generic

section Composition

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u} B)]
  (f : R →+* A) (g : A →+* B) (h : R →+* B) (hfg : g.comp f = h)
  (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
  (α : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
  (G : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
  (β : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]

/-- **Derived restriction of scalars along a composite.** For `g ∘ f = h`, derived restriction
along `g` followed by derived restriction along `f` is derived restriction along `h`. -/
abbrev derivedRestrictCompOfEqIso :
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} h).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
    (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} h)
    (ModuleCat.restrictScalarsComp'.{u} f g h hfg.symm).symm

/-- The derived change-of-rings adjunction (Stacks 0GMT) for the chosen model
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of derived extension of
scalars. -/
abbrev chosenDerivedExtensionScalarsAdjunction {R T : Type u} [CommRing R] [CommRing T]
    [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (ModuleCat.{u} T)]
    (k : R →+* T) :
    (totalDerivedExtensionScalars.{u, u, u} k).functor ⊣
      (ModuleCat.restrictScalars.{u} k).mapDerivedCategory :=
  @derivedExtensionScalarsAdjunction.{u, u, u} R T _ _ k _ _
    (totalDerivedExtensionScalars.{u, u, u} k).functor
    (totalDerivedExtensionScalars.{u, u, u} k).comparison
    (totalDerivedExtensionScalars.{u, u, u} k).isLeftDerived

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat A)]
  [HasDerivedCategory (ModuleCat B)] in
/-- The unit of extension of scalars along a composite, as the composite of the two units
followed by the composition isomorphisms, on modules. -/
theorem unit_comp_restrictScalars_map_unit_extendScalarsComp (M : ModuleCat.{u} R) :
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
        (ModuleCat.restrictScalars.{u} f).map
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
            ((ModuleCat.extendScalars.{u, u, u} f).obj M)) ≫
        (ModuleCat.restrictScalars.{u} f).map ((ModuleCat.restrictScalars.{u} g).map
          ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
            f g).inv.app M)) ≫
        (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
          ((ModuleCat.extendScalars.{u, u, u} (g.comp f)).obj M) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).unit.app M := by
  have h₁ := StacksDraft.DerivedExtensionScalarsModelComp.unit_extendScalarsComp'.{u, u, u, u}
    f g M
  have h₂ := (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.naturality
    ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).inv.app M)
  simp only [Functor.comp_map] at h₂
  rw [h₂]
  have h₃ : (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
        (ModuleCat.restrictScalars.{u} f).map
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
            ((ModuleCat.extendScalars.{u, u, u} f).obj M)) ≫
        (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
          ((ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.extendScalars.{u, u, u} g).obj M) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).unit.app M ≫
        (ModuleCat.restrictScalars.{u} (g.comp f)).map
          ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
            f g).hom.app M) := h₁
  have h₄ := congrArg (fun z ↦ z ≫ (ModuleCat.restrictScalars.{u} (g.comp f)).map
    ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
      f g).inv.app M)) h₃
  simp only [Category.assoc] at h₄
  rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id] at h₄
  exact h₄.trans (Category.comp_id _)

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat A)]
  [HasDerivedCategory (ModuleCat B)] in
/-- `MilnorPatching.unit_comp_restrictScalars_map_unit_extendScalarsComp` degreewise, on
cochain complexes. -/
theorem unit_comp_restrictScalars_map_unit_extendScalarsComp_complex
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P ≫
      ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso
            (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).symm
            (ComplexShape.up ℤ)).hom.app P)) ≫
      (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm (ComplexShape.up ℤ)).hom.app
          (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P := by
  ext n : 1
  simpa [Functor.mapHomologicalComplexCompIso, Adjunction.mapHomologicalComplex] using
    unit_comp_restrictScalars_map_unit_extendScalarsComp f g (P.X n)

/-- **The unit of the composite derived adjunction, against the composite comparison.** -/
theorem comp_unit_app_comp_map_compComparisonOfEq (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((derivedExtensionScalarsAdjunction.{u, u, u} f F α).comp
        (derivedExtensionScalarsAdjunction.{u, u, u} g G β)).unit.app (DerivedCategory.Q.obj P) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u, w₁, w₂, w₃}
            f g F α G β (g.comp f) rfl).app P)) ≫
      (derivedRestrictCompOfEqIso f g (g.comp f) rfl).hom.app
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app P) ≫
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) := by
  have e₂ :
      (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u, w₁, w₂, w₃}
      f g F α G β (g.comp f) rfl).app P =
      G.map (α.app P) ≫ β.app (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).symm
          (ComplexShape.up ℤ)).hom.app P) := by
    simp only [StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq,
      eqToHom_refl, Category.comp_id]
    rfl
  have e₃ := ((derivedExtensionScalarsAdjunction.{u, u, u} g G β).unit.naturality (α.app P)).symm
  have e₄ := derivedExtensionScalarsAdjunction_unit_app.{u, u, u}
    g G β (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have e₅ := ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.naturality
    ((Functor.mapHomologicalComplexCompIso
      (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).symm
      (ComplexShape.up ℤ)).hom.app P))
  have e₆ := derivedExtensionScalarsAdjunction_unit_app.{u, u, u}
    f F α P
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at e₃ e₅
  have inner : (derivedExtensionScalarsAdjunction.{u, u, u} g G β).unit.app
        (F.obj (DerivedCategory.Q.obj P)) ≫
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
        ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u, w₁, w₂, w₃}
            f g F α G β (g.comp f) rfl).app P) =
      α.app P ≫ DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso
            (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).symm
            (ComplexShape.up ℤ)).hom.app P)) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) := by
    rw [e₂]
    refine (congrArg (_ ≫ ·)
      (((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map_comp _ _).trans
        (congrArg (_ ≫ ·)
          ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map_comp _ _)))).trans ?_
    rw [reassoc_of% e₃, reassoc_of% e₄]
    refine congrArg (α.app P ≫ ·) ?_
    refine Eq.trans ?_ (congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _).symm)
    exact (congrArg (_ ≫ ·) e₅.symm).trans (Category.assoc _ _ _).symm
  have e₇ := ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.naturality
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso
            (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g).symm
            (ComplexShape.up ℤ)).hom.app P)))
  simp only [Functor.comp_obj, Functor.comp_map] at e₇
  have e₈ := Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q (ModuleCat.restrictScalars.{u} g)
    (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
    (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm
    (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have e₉ := unit_comp_restrictScalars_map_unit_extendScalarsComp_complex f g P
  refine Eq.trans (congrArg (· ≫ _) (Adjunction.comp_unit_app _ _ _)) ?_
  exact comp_unit_comp_map_eq_of_factorizations (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
    (inner := inner) (h₆ := e₆) (h₇ := e₇) (h₈ := e₈)
    (hg := Iso.inv_hom_id_app _ _) (hf := Iso.inv_hom_id_app _ _)
    (h₉ := by rw [← e₉]; simp only [CategoryTheory.Functor.map_comp, Category.assoc])

/-- **The derived composition isomorphism of extension of scalars is conjugate to the derived
composition isomorphism of restriction of scalars.** For ring maps `f : R →+* A`,
`g : A →+* B` with `g ∘ f = h`, arbitrary models `F`, `G` of derived extension of scalars along
`f` and `g`, and the derived change-of-rings adjunctions, the conjugate of
`StacksDraft.DerivedExtensionScalarsModelComp.compModelIso` (`(- ⊗ᴸ_R A) ⊗ᴸ_A B ≅ - ⊗ᴸ_R B`) is
`MilnorPatching.derivedRestrictCompOfEqIso`. -/
theorem conjugateEquiv_compModelIso_inv :
    conjugateEquiv ((derivedExtensionScalarsAdjunction.{u, u, u} f F α).comp
        (derivedExtensionScalarsAdjunction.{u, u, u} g G β))
      (chosenDerivedExtensionScalarsAdjunction h)
      (StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, w₁, w₂, w₃}
        f g F α G β h hfg (hFld := ‹_›) (hGld := ‹_›)).inv =
      (derivedRestrictCompOfEqIso f g h hfg).hom := by
  subst hfg
  rw [← Equiv.eq_symm_apply]
  refine StacksDraft.DerivedExtensionScalarsModelComp.comp_hom_ext f g F α G β _ rfl _ _ _
    (hFld := ‹_›) (hGld := ‹_›) (fun P ↦ ?_)
  have hm := StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison.{u,
    u, u, u, w₁, w₂, w₃} f g F α G β (g.comp f) rfl P (hFld := ‹_›) (hGld := ‹_›)
  have hL : (StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, w₁, w₂, w₃}
        f g F α G β (g.comp f) rfl (hFld := ‹_›) (hGld := ‹_›)).inv.app (DerivedCategory.Q.obj P) ≫
      (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{u, u, u, u, w₁, w₂, w₃}
        f g F α G β (g.comp f) rfl).app P =
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P := by
    rw [← hm, Iso.inv_hom_id_app_assoc]
  rw [hL, conjugateEquiv_symm_apply_app]
  simp only [Category.assoc]
  symm
  have hC := comp_unit_app_comp_map_compComparisonOfEq f g F α G β P
  have hcounit := @derivedExtensionScalarsAdjunction_counit_app.{u, u, u} R B _ _ (g.comp f) _ _
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived
    (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have hγ := (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.naturality
    (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app P)
  simp only [Functor.comp_obj, Functor.comp_map] at hγ
  have htri : DerivedCategory.Q.map
      (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app P)) ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).counit.app
          (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp,
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).left_triangle_components P)]
    exact DerivedCategory.Q.map_id _
  refine (map_comp_counit_comp_eq_of_factorizations _ _ (c := _) (rrc := _) (σZ := _)
    (εZ := _) (hσ := ((derivedRestrictCompOfEqIso f g (g.comp f) rfl).hom.naturality _).symm)
    (hε := ((chosenDerivedExtensionScalarsAdjunction (g.comp f)).counit.naturality _).symm)
    (hC := hC) (hcounit := hcounit) (hγ := hγ)).trans ?_
  exact (congrArg (_ ≫ ·) htri).trans (Category.comp_id _)

end Composition

section Associativity

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [HasDerivedCategory.{w₁} (ModuleCat.{u} R)] [HasDerivedCategory.{w₂} (ModuleCat.{u} S)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u} T)] [HasDerivedCategory.{w₄} (ModuleCat.{u} U)]
  (a : R →+* S) (b : S →+* T) (c : T →+* U) (ab : R →+* T) (bc : S →+* U) (abc : R →+* U)
  (hab : b.comp a = ab) (hbc : c.comp b = bc) (habc : bc.comp a = abc) (habc' : c.comp ab = abc)

/-- **The derived composition isomorphisms of restriction of scalars are associative.** -/
theorem derivedRestrictCompOfEqIso_assoc :
    Functor.whiskerRight (derivedRestrictCompOfEqIso b c bc hbc).hom
        (ModuleCat.restrictScalars.{u} a).mapDerivedCategory ≫
      (derivedRestrictCompOfEqIso a bc abc habc).hom =
    Functor.whiskerLeft (ModuleCat.restrictScalars.{u} c).mapDerivedCategory
        (derivedRestrictCompOfEqIso a b ab hab).hom ≫
      (derivedRestrictCompOfEqIso ab c abc habc').hom := by
  subst hab hbc habc
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} U) (ComplexShape.up ℤ)) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q,
    Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q]
  have hnat := ((ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} b c (c.comp b) rfl).symm (ComplexShape.up ℤ)).hom.app K))
  have hC := (derivedRestrictCompOfEqIso a b (b.comp a) rfl).hom.naturality
    ((ModuleCat.restrictScalars.{u} c).mapDerivedCategoryFactors.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat hC
  exact assoc_of_factorizations (ModuleCat.restrictScalars.{u} a).mapDerivedCategory
    (hi₁ := Iso.inv_hom_id_app _ _) (hnat := hnat) (hC := hC.symm)
    (hC₂ := Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q _ _ _ _ _)
    (hiab := Iso.inv_hom_id_app _ _)
    (hC₄ := Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q _ _ _ _ _)
    (hcx := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1)

end Associativity

section Square

variable {B'' B A A' : Type u} [CommRing B''] [CommRing B] [CommRing A] [CommRing A']
  [HasDerivedCategory.{w₁} (ModuleCat.{u} B'')] [HasDerivedCategory.{w₂} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u} A')] [HasDerivedCategory.{w₄} (ModuleCat.{u} A)]
  (p₁ : B'' →+* B) (toBase : B →+* A) (p₂ : B'' →+* A') (surj : A' →+* A) (q : B'' →+* A)
  (h₁ : toBase.comp p₁ = q) (h₂ : surj.comp p₂ = q)

/-- **Derived restriction of scalars around a commutative square of rings**:
`res_{p₁} ∘ res_{toBase} ≅ res_{p₂} ∘ res_{surj}`, both being derived restriction along `q`. -/
def derivedRestrictRingSquareIso :
    (ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} surj).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} p₂).mapDerivedCategory :=
  derivedRestrictCompOfEqIso p₁ toBase q h₁ ≪≫ (derivedRestrictCompOfEqIso p₂ surj q h₂).symm

/-- For a fibre product of rings, `MilnorPatching.derivedRestrictRingSquareIso` is
`MilnorPatching.derivedRestrictCompIso`. -/
theorem derivedRestrictRingSquareIso_fibreProduct {A A' B : Type u} [CommRing A] [CommRing A']
    [CommRing B] {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
    (s : RingFibreProduct.Situation toBase surjection I)
    [HasDerivedCategory.{w₁} (ModuleCat.{u} s.fibreProduct)]
    [HasDerivedCategory.{w₂} (ModuleCat.{u} B)] [HasDerivedCategory.{w₃} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] :
    derivedRestrictRingSquareIso (fibreProductFst I s) toBase (fibreProductSnd I s) surjection
      (fibreProductToBase I s) (toBase_comp_fibreProductFst I s) rfl = derivedRestrictCompIso I s :=
  rfl

variable {𝒟 𝒟' : Type*} {_ : Category 𝒟} {_ : Category 𝒟'} in
/-- The bookkeeping of `MilnorPatching.map_derivedRestrictRingSquareIso_comp`, over abstract
categories. -/
theorem square_of_assoc (Re : 𝒟' ⥤ 𝒟) {x₀ x₁ x₂ : 𝒟'} {y₀ y₂ y₃ : 𝒟}
    (C₁ : x₀ ≅ x₁) (C₂ : x₂ ≅ x₁) (D₂ : Re.obj x₂ ⟶ y₂) (Ceq : Re.obj x₁ ⟶ y₃) (G₂ : y₂ ≅ y₃)
    (D₁ : Re.obj x₀ ⟶ y₀) (G₁ : y₀ ⟶ y₃)
    (a₁ : Re.map C₁.hom ≫ Ceq = D₁ ≫ G₁) (a₂ : Re.map C₂.hom ≫ Ceq = D₂ ≫ G₂.hom) :
    Re.map (C₁.hom ≫ C₂.inv) ≫ D₂ = D₁ ≫ G₁ ≫ G₂.inv := by
  have : D₂ = Re.map C₂.hom ≫ Ceq ≫ G₂.inv := by
    rw [reassoc_of% a₂, Iso.hom_inv_id, Category.comp_id]
  rw [this, Re.map_comp, Category.assoc, ← Re.map_comp_assoc C₂.inv C₂.hom, Iso.inv_hom_id,
    Re.map_id, Category.id_comp, reassoc_of% a₁]

include h₁ in
/-- **Restricting the square of derived restrictions along a further ring map.** For
`e : P →+* B''` with composites `f₁ = p₁ ∘ e`, `f₂ = p₂ ∘ e` and `q' = toBase ∘ f₁ = surj ∘ f₂`,
the square `MilnorPatching.derivedRestrictRingSquareIso` for `p₁, p₂` followed by restriction along
`e` is the square for `f₁, f₂`, through the composition isomorphisms. -/
theorem map_derivedRestrictRingSquareIso_comp {P : Type u} [CommRing P]
    [HasDerivedCategory.{w} (ModuleCat.{u} P)] (e : P →+* B'') (f₁ : P →+* B) (f₂ : P →+* A')
    (q' : P →+* A) (he₁ : p₁.comp e = f₁) (he₂ : p₂.comp e = f₂) (hq₁ : toBase.comp f₁ = q')
    (hq₂ : surj.comp f₂ = q') (X : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.restrictScalars.{u} e).mapDerivedCategory.map
        ((derivedRestrictRingSquareIso p₁ toBase p₂ surj q h₁ h₂).hom.app X) ≫
      (derivedRestrictCompOfEqIso e p₂ f₂ he₂).hom.app
        ((ModuleCat.restrictScalars.{u} surj).mapDerivedCategory.obj X) =
    (derivedRestrictCompOfEqIso e p₁ f₁ he₁).hom.app
        ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj X) ≫
      (derivedRestrictRingSquareIso f₁ toBase f₂ surj q' hq₁ hq₂).hom.app X := by
  have hqe : q.comp e = q' := by rw [← h₁, RingHom.comp_assoc, he₁, hq₁]
  have a₁ := congrArg (fun τ ↦ τ.app X) (derivedRestrictCompOfEqIso_assoc e p₁ toBase f₁ q q'
    he₁ h₁ hqe hq₁)
  have a₂ := congrArg (fun τ ↦ τ.app X) (derivedRestrictCompOfEqIso_assoc e p₂ surj f₂ q q'
    he₂ h₂ hqe hq₂)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at a₁ a₂
  exact square_of_assoc _ ((derivedRestrictCompOfEqIso p₁ toBase q h₁).app X)
    ((derivedRestrictCompOfEqIso p₂ surj q h₂).app X) _ _
    ((derivedRestrictCompOfEqIso f₂ surj q' hq₂).app X) _ _ a₁ a₂

variable (F₁ : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} B))
  (α₁ : DerivedCategory.Q ⋙ F₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} p₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F₁.IsLeftDerivedFunctor α₁
    (HomologicalComplex.quasiIso (ModuleCat.{u} B'') (ComplexShape.up ℤ))]
  (F₂ : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} A'))
  (α₂ : DerivedCategory.Q ⋙ F₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} p₂).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F₂.IsLeftDerivedFunctor α₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} B'') (ComplexShape.up ℤ))]
  (G₁ : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₁ : DerivedCategory.Q ⋙ G₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₁.IsLeftDerivedFunctor β₁ (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
  (G₂ : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₂ : DerivedCategory.Q ⋙ G₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} surj).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₂.IsLeftDerivedFunctor β₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ))]

/-- **The 2-cell of derived extension of scalars around a commutative square of rings**:
`(- ⊗ᴸ_{B''} B) ⊗ᴸ_B A ≅ - ⊗ᴸ_{B''} A ≅ (- ⊗ᴸ_{B''} A') ⊗ᴸ_{A'} A`, through the chosen model
of derived extension of scalars along `q`. -/
abbrev derivedExtensionSquareIso : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂ :=
  StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, w₁, w₂, w₄}
      p₁ toBase F₁ α₁ G₁ β₁ q h₁ (hFld := ‹_›) (hGld := ‹_›) ≪≫
    (StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, w₁, w₃, w₄}
      p₂ surj F₂ α₂ G₂ β₂ q h₂ (hFld := ‹_›) (hGld := ‹_›)).symm

/-- **The conjugate of the square of derived extensions of scalars is the square of derived
restrictions of scalars.** Under the derived change-of-rings adjunctions, the identification
`Rf ⋙ Rj ≅ Ri ⋙ Rf'` conjugate to `MilnorPatching.derivedExtensionSquareIso`
(`MilnorPatching.glueingConjugateIso`) is `MilnorPatching.derivedRestrictRingSquareIso`. -/
theorem glueingConjugateIso_derivedExtensionSquareIso :
    glueingConjugateIso (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁)
        (derivedExtensionScalarsAdjunction.{u, u, u} surj G₂ β₂)
        (derivedExtensionScalarsAdjunction.{u, u, u} p₁ F₁ α₁)
        (derivedExtensionScalarsAdjunction.{u, u, u} p₂ F₂ α₂)
        (derivedExtensionSquareIso p₁ toBase p₂ surj q h₁ h₂ F₁ α₁ F₂ α₂ G₁ β₁ G₂ β₂) =
      derivedRestrictRingSquareIso p₁ toBase p₂ surj q h₁ h₂ := by
  have r₁ := conjugateEquiv_compModelIso_inv p₁ toBase q h₁ F₁ α₁ G₁ β₁
  have r₂ := conjugateEquiv_compModelIso_inv p₂ surj q h₂ F₂ α₂ G₂ β₂
  have hX : conjugateEquiv (chosenDerivedExtensionScalarsAdjunction q)
      ((derivedExtensionScalarsAdjunction.{u, u, u} p₂ F₂ α₂).comp
        (derivedExtensionScalarsAdjunction.{u, u, u} surj G₂ β₂))
      (StacksDraft.DerivedExtensionScalarsModelComp.compModelIso.{u, u, u, u, w₁, w₃, w₄}
        p₂ surj F₂ α₂ G₂ β₂ q h₂ (hFld := ‹_›) (hGld := ‹_›)).hom =
      (derivedRestrictCompOfEqIso p₂ surj q h₂).inv := by
    refine (Iso.inv_ext ?_).symm
    rw [← r₂, conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id]
  ext1
  show conjugateEquiv _ _ (_ ≫ _) = _
  rw [← conjugateEquiv_comp _ (chosenDerivedExtensionScalarsAdjunction q), r₁, Iso.symm_inv, hX]
  rfl

end Square

section Equivalence

variable {R T : Type u} [CommRing R] [CommRing T] [HasDerivedCategory.{w₁} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} T)]

/-- **Derived restriction of scalars along a ring isomorphism is an equivalence**: for
`eh : R →+* T` and `ei : T →+* R` inverse to each other, derived restriction along `eh` is an
equivalence `D(T) ≌ D(R)` with inverse derived restriction along `ei`. -/
def derivedRestrictScalarsEquivalence (eh : R →+* T) (ei : T →+* R)
    (h₁ : eh.comp ei = RingHom.id T) (h₂ : ei.comp eh = RingHom.id R) :
    DerivedCategory (ModuleCat.{u} T) ≌ DerivedCategory (ModuleCat.{u} R) :=
  CategoryTheory.Equivalence.mk (ModuleCat.restrictScalars.{u} eh).mapDerivedCategory
    (ModuleCat.restrictScalars.{u} ei).mapDerivedCategory
    (derivedRestrictCompOfEqIso ei eh (RingHom.id T) h₁ ≪≫
      Dualizing.mapDerivedCategoryIdIso).symm
    (derivedRestrictCompOfEqIso eh ei (RingHom.id R) h₂ ≪≫
      Dualizing.mapDerivedCategoryIdIso)

end Equivalence

section Pullback

open Pretriangulated StacksDraft.PseudoCoherence

variable {B'' B A A' : Type u} [CommRing B''] [CommRing B] [CommRing A] [CommRing A']
  [HasDerivedCategory.{w₁} (ModuleCat.{u} B'')] [HasDerivedCategory.{w₂} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u} A')] [HasDerivedCategory.{w₄} (ModuleCat.{u} A)]
  {p₁ : B'' →+* B} {toBase : B →+* A} {p₂ : B'' →+* A'} {surj : A' →+* A} {q : B'' →+* A}

/-- **The ring-level statement of Stacks 0DL7 over an arbitrary fibre product of rings.**
`MilnorPatching.isIso_homEquiv_symm_of_distinguished_glueingMap` with the fibre product
`B ×_A A'` replaced by any ring `B''` forming a cartesian square of commutative rings with
`B → A` and a surjection `A' → A` with nil kernel. The data are transported to the fibre product
along the ring isomorphism, which induces an equivalence of derived categories by derived
restriction of scalars. -/
theorem isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap
    (h₁ : toBase.comp p₁ = q) (h₂ : surj.comp p₂ = q)
    (hpb : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom surj))
    (hsurj : Function.Surjective surj) (hnil : RingHom.ker surj ≤ nilradical A')
    {Lj : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} B)}
    {Rj : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B'')}
    (adjJ : Lj ⊣ Rj) (eJ : Rj ≅ (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory)
    {Lf' : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} A')}
    {Rf' : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} B'')}
    (adjF' : Lf' ⊣ Rf') (eF' : Rf' ≅ (ModuleCat.restrictScalars.{u} p₂).mapDerivedCategory)
    {Lf : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A)}
    {Rf : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (adjF : Lf ⊣ Rf) (eF : Rf ≅ (ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory)
    {Li : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A)}
    {Ri : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A')}
    (adjI : Li ⊣ Ri) (eI : Ri ≅ (ModuleCat.restrictScalars.{u} surj).mapDerivedCategory)
    (c : Rf ⋙ Rj ≅ Ri ⋙ Rf')
    (hc : ∀ X : DerivedCategory (ModuleCat.{u} A),
      c.hom.app X ≫ eF'.hom.app (Ri.obj X) ≫
          (ModuleCat.restrictScalars.{u} p₂).mapDerivedCategory.map (eI.hom.app X) =
        eJ.hom.app (Rf.obj X) ≫
          (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory.map (eF.hom.app X) ≫
          (derivedRestrictRingSquareIso p₁ toBase p₂ surj q h₁ h₂).hom.app X)
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : Lf.obj M ≅ Li.obj K') {M' : DerivedCategory (ModuleCat.{u} B'')}
    (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K') (w : Rj.obj (Rf.obj (Li.obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u (glueingMap adjF adjI c M K' α.hom) w ∈
      distTriang (DerivedCategory (ModuleCat.{u} B''))) :
    IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
      IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)) := by
  let I := RingHom.ker surj
  let s : RingFibreProduct.Situation toBase surj I := ⟨hsurj, rfl⟩
  have hI : HenselianPair A' I := by
    have := (etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical I hnil).2
    exact henselianPair_of_henselianRing A' I
  let := HasDerivedCategory.standard (ModuleCat.{u} s.fibreProduct)
  have hcone : IsPullback s.pullbackCone.fst s.pullbackCone.snd (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom surj) := IsPullback.of_isLimit s.pullbackConeIsLimit
  let e := hpb.isoIsPullback _ _ hcone
  let eh : B'' →+* s.fibreProduct := e.hom.hom
  let ei : s.fibreProduct →+* B'' := e.inv.hom
  have hi₁ : p₁.comp ei = fibreProductFst I s :=
    congrArg CommRingCat.Hom.hom (hpb.isoIsPullback_inv_fst _ _ hcone)
  have hi₂ : p₂.comp ei = fibreProductSnd I s :=
    congrArg CommRingCat.Hom.hom (hpb.isoIsPullback_inv_snd _ _ hcone)
  have hhi : eh.comp ei = RingHom.id _ := congrArg CommRingCat.Hom.hom e.inv_hom_id
  have hih : ei.comp eh = RingHom.id _ := congrArg CommRingCat.Hom.hom e.hom_inv_id
  let E := derivedRestrictScalarsEquivalence eh ei hhi hih
  let Rei := (ModuleCat.restrictScalars.{u} ei).mapDerivedCategory
  let eJ' : Rj ⋙ Rei ≅ derivedRestrictFst I s :=
    Functor.isoWhiskerRight eJ Rei ≪≫ derivedRestrictCompOfEqIso ei p₁ _ hi₁
  let eF'' : Rf' ⋙ Rei ≅ derivedRestrictSnd I s :=
    Functor.isoWhiskerRight eF' Rei ≪≫ derivedRestrictCompOfEqIso ei p₂ _ hi₂
  let c' : Rf ⋙ (Rj ⋙ Rei) ≅ Ri ⋙ (Rf' ⋙ Rei) := Functor.isoWhiskerRight c Rei
  have hc' : ∀ X : DerivedCategory (ModuleCat.{u} A),
      c'.hom.app X ≫ eF''.hom.app (Ri.obj X) ≫ (derivedRestrictSnd I s).map (eI.hom.app X) =
        eJ'.hom.app (Rf.obj X) ≫ (derivedRestrictFst I s).map (eF.hom.app X) ≫
          (derivedRestrictCompIso I s).hom.app X := fun X ↦
    hc_of_factorizations Rei _ _ _ _ _ _ _ _ _ _ _ _ _ (hc X)
      ((derivedRestrictCompOfEqIso ei p₂ _ hi₂).hom.naturality (eI.hom.app X)).symm
      ((derivedRestrictCompOfEqIso ei p₁ _ hi₁).hom.naturality (eF.hom.app X)).symm
      (map_derivedRestrictRingSquareIso_comp p₁ toBase p₂ surj q h₁ h₂ ei _ _ _ hi₁ hi₂
        (toBase_comp_fibreProductFst I s) rfl X)
  let : E.inverse.Additive := (inferInstance : Rei.Additive)
  let : E.inverse.CommShift ℤ := (inferInstance : Rei.CommShift ℤ)
  let : E.inverse.IsTriangulated := (inferInstance : Rei.IsTriangulated)
  exact isIso_homEquiv_symm_of_equivalence E adjJ adjF' adjF adjI c c' (fun _ ↦ rfl) M K' α.hom
    (fun u' w' hT' ↦ isIso_homEquiv_symm_of_distinguished_glueingMap I s hI
      (E.toAdjunction.comp adjJ) eJ' (E.toAdjunction.comp adjF') eF'' adjF eF adjI eI c' hc'
      M hM K' hK' α u' w' hT') u w hT

variable (p₁ toBase p₂ surj q)
  (F₁ : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} B))
  (α₁ : DerivedCategory.Q ⋙ F₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} p₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F₁.IsLeftDerivedFunctor α₁
    (HomologicalComplex.quasiIso (ModuleCat.{u} B'') (ComplexShape.up ℤ))]
  (F₂ : DerivedCategory (ModuleCat.{u} B'') ⥤ DerivedCategory (ModuleCat.{u} A'))
  (α₂ : DerivedCategory.Q ⋙ F₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} p₂).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [F₂.IsLeftDerivedFunctor α₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} B'') (ComplexShape.up ℤ))]
  (G₁ : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₁ : DerivedCategory.Q ⋙ G₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₁.IsLeftDerivedFunctor β₁ (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
  (G₂ : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₂ : DerivedCategory.Q ⋙ G₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} surj).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₂.IsLeftDerivedFunctor β₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ))]

/-- **The ring-level statement of Stacks 0DL7 for the derived change-of-rings adjunctions,
over an arbitrary fibre product of rings.** Let `B''` form a cartesian square of commutative rings
with `p₁ : B'' → B`, `p₂ : B'' → A'`, `toBase : B → A` and a surjection `surj : A' → A` with nil
kernel, let `F₁, F₂, G₁, G₂` be any models of derived extension of scalars along the four maps,
with the derived change-of-rings adjunctions, and let the identification
`Rf ⋙ Rj ≅ Ri ⋙ Rf'` be the conjugate of the square of derived extensions of scalars
(`MilnorPatching.derivedExtensionSquareIso`). For pseudo-coherent `M ∈ D(B)` and `K' ∈ D(A')`, any
`α : M ⊗ᴸ_B A ≅ K' ⊗ᴸ_{A'} A` and any distinguished triangle on the glueing map of `(M, K', α)`,
the maps `M' ⊗ᴸ_{B''} B ⟶ M` and `M' ⊗ᴸ_{B''} A' ⟶ K'` adjoint to the two components of the first
map are isomorphisms. -/
theorem isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap_derivedExtension
    (h₁ : toBase.comp p₁ = q) (h₂ : surj.comp p₂ = q)
    (hpb : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom surj))
    (hsurj : Function.Surjective surj) (hnil : RingHom.ker surj ≤ nilradical A')
    (M : DerivedCategory (ModuleCat.{u} B)) (hM : IsPseudoCoherentIn M)
    (K' : DerivedCategory (ModuleCat.{u} A')) (hK' : IsPseudoCoherentIn K')
    (α : G₁.obj M ≅ G₂.obj K') {M' : DerivedCategory (ModuleCat.{u} B'')}
    (u : M' ⟶ (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory.obj M ⊞
      (ModuleCat.restrictScalars.{u} p₂).mapDerivedCategory.obj K')
    (w : (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory.obj
      ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj (G₂.obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u (glueingMap (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁)
        (derivedExtensionScalarsAdjunction.{u, u, u} surj G₂ β₂)
        (glueingConjugateIso (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁)
          (derivedExtensionScalarsAdjunction.{u, u, u} surj G₂ β₂)
          (derivedExtensionScalarsAdjunction.{u, u, u} p₁ F₁ α₁)
          (derivedExtensionScalarsAdjunction.{u, u, u} p₂ F₂ α₂)
          (derivedExtensionSquareIso p₁ toBase p₂ surj q h₁ h₂ F₁ α₁ F₂ α₂ G₁ β₁ G₂ β₂))
        M K' α.hom) w ∈ distTriang (DerivedCategory (ModuleCat.{u} B''))) :
    IsIso (((derivedExtensionScalarsAdjunction.{u, u, u} p₁ F₁ α₁).homEquiv _ _).symm
        (u ≫ biprod.fst)) ∧
      IsIso (((derivedExtensionScalarsAdjunction.{u, u, u} p₂ F₂ α₂).homEquiv _ _).symm
        (u ≫ biprod.snd)) :=
  isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap h₁ h₂ hpb hsurj hnil
    (derivedExtensionScalarsAdjunction.{u, u, u} p₁ F₁ α₁) (Iso.refl _)
    (derivedExtensionScalarsAdjunction.{u, u, u} p₂ F₂ α₂) (Iso.refl _)
    (derivedExtensionScalarsAdjunction.{u, u, u} toBase G₁ β₁) (Iso.refl _)
    (derivedExtensionScalarsAdjunction.{u, u, u} surj G₂ β₂) (Iso.refl _) _
    (fun X ↦ by
      rw [glueingConjugateIso_derivedExtensionSquareIso]
      simp)
    M hM K' hK' α u w hT

end Pullback

end MilnorPatching
