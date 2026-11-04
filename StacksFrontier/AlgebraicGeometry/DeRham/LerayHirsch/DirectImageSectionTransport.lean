module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LocalLerayHirsch
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.PowerSummandsSection
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OpenImmersionRestrictionIsIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdditiveAnyModel

/-!
# Transporting the section of `c ⊕ Rp_*θ` along isomorphisms and to opens of the base

Let `p : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, `ξ ∈ H^n_{dR}(X/S)` and
`θ = ξ'[-n] : Ω^•_{X/S}[-n] ⟶ Ω^•_{X/S}` the untwisted morphism of Remark 0FU7. Say that `p` has a
*section of `c ⊕ Rp_*θ`* if there are `τ : Rp_*Ω^•_{X/S} ⟶ Ω^•_{Y/S}` and
`ν : Rp_*Ω^•_{X/S} ⟶ Rp_*(Ω^•_{X/S}[-n])` with `c ≫ τ = 𝟙`, `c ≫ ν = 0` and
`τ ≫ c + ν ≫ Rp_*θ = 𝟙`, for `c : Ω^•_{Y/S} ⟶ Rp_*Ω^•_{X/S}` the canonical map
(`AlgebraicGeometry.DeRhamLerayHirsch.HasDirectImageSection`). This is the property of the
exceptional divisor of a blowing up with smooth centre on which the proof of [Stacks, Tag 0FUW]
rests. This file shows that it is invariant under an isomorphism `X' ≅ X` over `Y`, and that it
restricts to opens `Y' ⊆ Y`: if `X' = X ×_Y Y'` has the section for the pulled back class, then
so does the restriction of `p` to `Y'`, in the derived category of `Y'`.

Both rest on the compatibility of the canonical maps of de Rham complexes with composition
(Section 07HX) and with the morphisms `ξ'` (Remark 0FU7, `deRhamComparisonQ_comp_classMorphism`),
and on the computation of derived sections over opens through open immersions
([Stacks, Tags 0D5V, 0D5W]).

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.HasDirectImageSection`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.classUntwisted_comp_deRhamComparisonQ`: the canonical map
  of a square intertwines the untwisted morphisms of a class and of its pullback.
* `AlgebraicGeometry.DeRhamLerayHirsch.HasDirectImageSection.of_isIso`: invariance under an
  isomorphism over the base.
* `AlgebraicGeometry.DeRhamLerayHirsch.exists_section_mapDerivedCategory_of_restrict`: the section
  over an open of the base.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace CategoryTheory

/-- **Untwisting an intertwining.** If `c : T ⟶ G(T')` intertwines `ξ : T ⟶ T[n]` and
`ξ' : T' ⟶ T'[n]` through the commutation of `G` with the shift, then it intertwines the
untwisted morphisms `ξ[-n] ≫ (T[n][-n] ≅ T)` and `ξ'[-n] ≫ (T'[n][-n] ≅ T')`, through the
translate of `c`. -/
theorem untwist_comp_eq_comp_map_untwist {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D) [G.CommShift ℤ] {T : D} {T' : C} (n : ℤ)
    (ξ : T ⟶ T⟦n⟧) (ξ' : T' ⟶ T'⟦n⟧) (c : T ⟶ G.obj T')
    (h : c ≫ G.map ξ' = ξ ≫ c⟦n⟧' ≫ (G.commShiftIso n).inv.app T') :
    (ξ⟦-n⟧' ≫ (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app T) ≫ c =
      (c⟦-n⟧' ≫ (G.commShiftIso (-n)).inv.app T') ≫
        G.map (ξ'⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app T') := by
  have h' : c ≫ G.map ξ' ≫ (G.commShiftIso n).hom.app T' = ξ ≫ c⟦n⟧' := by
    rw [← Category.assoc, h]
    simp
  have hn := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality c
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Category.assoc, Category.assoc, ← shift_comp_shiftFunctorCompIsoId_hom_app_eq_map G n ξ',
    ← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h']

namespace Limits

/-- **Transporting a section along an isomorphism of arrows.** Let `c : A ⟶ R`, `Θ : W ⟶ R` and
`c' : A' ⟶ R'`, `Θ' : W' ⟶ R'` correspond under isomorphisms `A ≅ A'`, `R ≅ R'` and `W ≅ W'`. If
`c'` has a retraction `τ'` with `τ' ≫ c' + ν' ≫ Θ' = 𝟙` for some `ν'`, then `c` has a retraction
`τ` with `τ ≫ c + ν ≫ Θ = 𝟙` for some `ν`. -/
theorem exists_retraction_and_section_of_arrowIso {C : Type*} [Category* C] [Preadditive C]
    {A A' R R' W W' : C} (c : A ⟶ R) (c' : A' ⟶ R') (Θ : W ⟶ R) (Θ' : W' ⟶ R') (δ : A ≅ A')
    (α : R ≅ R') (β : W ≅ W') (hc : c ≫ α.hom = δ.hom ≫ c') (hΘ : Θ ≫ α.hom = β.hom ≫ Θ')
    (H : ∃ (τ : R' ⟶ A') (ν : R' ⟶ W'), c' ≫ τ = 𝟙 A' ∧ τ ≫ c' + ν ≫ Θ' = 𝟙 R') :
    ∃ (τ : R ⟶ A) (ν : R ⟶ W), c ≫ τ = 𝟙 A ∧ τ ≫ c + ν ≫ Θ = 𝟙 R := by
  obtain ⟨τ, ν, h₁, h₂⟩ := H
  have hc' : δ.inv ≫ c = c' ≫ α.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hΘ' : β.inv ≫ Θ = Θ' ≫ α.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hΘ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨α.hom ≫ τ ≫ δ.inv, α.hom ≫ ν ≫ β.inv, ?_, ?_⟩
  · rw [← Category.assoc, hc, Category.assoc, ← Category.assoc c', h₁, Category.id_comp,
      Iso.hom_inv_id]
  · simp only [Category.assoc, hc', hΘ']
    rw [← Preadditive.comp_add, ← Category.assoc τ, ← Category.assoc ν, ← Preadditive.add_comp, h₂,
      Category.id_comp, Iso.hom_inv_id]

end Limits

/-- **A section of the image of `c ⊕ Θ` under a functor, from one of the image of a comparable
pair.** Let `c : A ⟶ R` and `Θ : W ⟶ R`, and `c₁ : A₁ ⟶ R₁` and `Θ₁ : W₁ ⟶ R₁`, be compared by
`a : A ⟶ A₁` and maps `x, x', y, y'` into `Θ₀ : W₀ ⟶ R₀`, with `c ≫ x = a ≫ c₁ ≫ y`,
`Θ ≫ x = x' ≫ Θ₀` and `Θ₁ ≫ y = y' ≫ Θ₀`. If `y`, `y'` are isomorphisms, and so are the images of
`a`, `x`, `x'` under `F`, then a retraction of `F(c₁)` completing `F(c₁) ⊕ F(Θ₁)` to a split
epimorphism gives one of `F(c)`. -/
theorem Functor.exists_retraction_and_section_map_of_comp_eq {C D : Type*} [Category* C]
    [Category* D] [Preadditive D] (F : C ⥤ D) {A R W A₁ R₁ W₁ R₀ W₀ : C} (c : A ⟶ R)
    (Θ : W ⟶ R) (c₁ : A₁ ⟶ R₁) (Θ₁ : W₁ ⟶ R₁) (Θ₀ : W₀ ⟶ R₀) (a : A ⟶ A₁) (x : R ⟶ R₀)
    (x' : W ⟶ W₀) (y : R₁ ⟶ R₀) (y' : W₁ ⟶ W₀) (hy : IsIso y) (hy' : IsIso y')
    (ha : IsIso (F.map a)) (hx : IsIso (F.map x)) (hx' : IsIso (F.map x'))
    (h₁ : c ≫ x = a ≫ c₁ ≫ y) (h₂ : Θ ≫ x = x' ≫ Θ₀) (h₃ : Θ₁ ≫ y = y' ≫ Θ₀)
    (H : ∃ (τ : F.obj R₁ ⟶ F.obj A₁) (ν : F.obj R₁ ⟶ F.obj W₁),
      F.map c₁ ≫ τ = 𝟙 _ ∧ τ ≫ F.map c₁ + ν ≫ F.map Θ₁ = 𝟙 _) :
    ∃ (τ : F.obj R ⟶ F.obj A) (ν : F.obj R ⟶ F.obj W),
      F.map c ≫ τ = 𝟙 _ ∧ τ ≫ F.map c + ν ≫ F.map Θ = 𝟙 _ := by
  have e₁ : c ≫ x ≫ CategoryTheory.inv y = a ≫ c₁ := by
    rw [← Category.assoc, h₁]
    simp
  have h₃' : CategoryTheory.inv y' ≫ Θ₁ = Θ₀ ≫ CategoryTheory.inv y := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, h₃]
  have e₂ : Θ ≫ x ≫ CategoryTheory.inv y = x' ≫ CategoryTheory.inv y' ≫ Θ₁ := by
    rw [← Category.assoc, h₂, h₃', Category.assoc]
  refine Limits.exists_retraction_and_section_of_arrowIso (F.map c) (F.map c₁) (F.map Θ)
    (F.map Θ₁) (asIso (F.map a)) (asIso (F.map x) ≪≫ (F.mapIso (asIso y)).symm)
    (asIso (F.map x') ≪≫ (F.mapIso (asIso y')).symm) ?_ ?_ H
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
    simp only [← F.map_comp]
    rw [e₁]
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
      Category.assoc]
    simp only [← F.map_comp]
    rw [e₂]

end CategoryTheory

namespace AlgebraicGeometry.DeRhamLerayHirsch

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardCompIso)

attribute [local instance] isOpenImmersion_inverseImageBaseMap

/-- The transport between the derived direct images along two equal morphisms is natural. -/
theorem derivedPushforward_map_comp_eqToHom {A B : RingedSpace.{u, u}} {k k' : A ⟶ B} (e : k = k')
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))} (θ : K ⟶ L) :
    (derivedPushforward k).map θ ≫ eqToHom (congrArg (fun k => (derivedPushforward k).obj L) e) =
      eqToHom (congrArg (fun k => (derivedPushforward k).obj K) e) ≫
        (derivedPushforward k').map θ := by
  subst e
  simp

/-- If derived sections over `U` send `c` to an isomorphism, they induce bijections on homology. -/
private theorem bijective_homology_map_derivedSectionsOverOpen {Z : RingedSpace.{u, u}}
    (U : Opens Z.carrier) {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    (c : K ⟶ L)
    (hc : IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Z U).map c))
    (k : ℤ) :
    Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Z U).map c)).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 (Functor.map_isIso _ _)

section Square

variable {X X' S S' : Scheme.{u}} (ι : X' ⟶ X) (p' : X' ⟶ S') (p : X ⟶ S) (h₀ : S' ⟶ S)
  (w : ι ≫ p = p' ≫ h₀)

/-- **The canonical map of a square intertwines the untwisted morphisms of Remark 0FU7**: for
`ξ ∈ H^n_{dR}(X/S)` with pullback `ι^*ξ`, `θ_ξ ≫ c = c[-n] ≫ Rh_*θ_{ι^*ξ}`. -/
theorem classUntwisted_comp_deRhamComparisonQ (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n) :
    classUntwisted p n ξ ≫ deRhamComparisonQ ι p' p h₀ w =
      ((deRhamComparisonQ ι p' p h₀ w)⟦-n⟧' ≫
          ((derivedPushforward (inverseImageBaseMap ι p' p h₀ w)).commShiftIso (-n)).inv.app _) ≫
        (derivedPushforward (inverseImageBaseMap ι p' p h₀ w)).map
          (classUntwisted p' n (deRhamPullbackSquare ι p' p h₀ w n ξ)) :=
  untwist_comp_eq_comp_map_untwist _ n _ _ _ (deRhamComparisonQ_comp_classMorphism ι p' p h₀ w n ξ)

/-- **The canonical map of a square in which `ι` is an isomorphism and `h₀` an open immersion is
an isomorphism**: it induces isomorphisms on derived sections over every open. -/
theorem isIso_deRhamComparisonQ_of_isIso [IsIso ι] [IsOpenImmersion h₀] :
    IsIso (deRhamComparisonQ ι p' p h₀ w) := by
  refine Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen
    (B := Set.univ) (Opens.isBasis_iff_nbhd.2 fun {U} {x} hx => ⟨U, Set.mem_univ _, hx, le_rfl⟩)
    _ fun V _ k => ?_
  have := isIso_derivedSectionsOverOpen_map_deRhamComparisonQ ι p' p h₀ w V
    (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  exact bijective_homology_map_derivedSectionsOverOpen V _ this k

end Square

variable {X X' Y S : Scheme.{u}}

/-- **The section of `c ⊕ Rp_*θ`**: for `p : X ⟶ Y`, `g : Y ⟶ S` and `ξ ∈ H^n_{dR}(X/S)`, there are
`τ : Rp_*Ω^•_{X/S} ⟶ Ω^•_{Y/S}` and `ν : Rp_*Ω^•_{X/S} ⟶ Rp_*(Ω^•_{X/S}[-n])` with `c ≫ τ = 𝟙`,
`c ≫ ν = 0` and `τ ≫ c + ν ≫ Rp_*θ = 𝟙`, for `c` the canonical map and `θ` the untwisted morphism
of `ξ`. -/
def HasDirectImageSection (p : X ⟶ Y) (g : Y ⟶ S) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) n) : Prop :=
  ∃ (τ : (relativeDirectImage p g).obj (deRhamObject (p ≫ g)) ⟶ deRhamObject g)
    (ν : (relativeDirectImage p g).obj (deRhamObject (p ≫ g)) ⟶
      (relativeDirectImage p g).obj ((deRhamObject (p ≫ g))⟦-n⟧)),
    deRhamDirectImageMap p g ≫ τ = 𝟙 _ ∧ deRhamDirectImageMap p g ≫ ν = 0 ∧
      τ ≫ deRhamDirectImageMap p g +
        ν ≫ (relativeDirectImage p g).map (classUntwisted (p ≫ g) n ξ) = 𝟙 _

/-- **Pasting a naturality square onto an intertwining.** If `θ ≫ c = cs ≫ Ra(θ')`, then the image
under `Rb` of this square, followed by a transformation `μ : Ra ⋙ Rb ⟶ Rc` and a pair of maps
`e₁, e₂` into `Rc'` intertwining `Rc(θ')` and `Rc'(θ')`, intertwines `Rb(θ)` and `Rc'(θ')`. -/
theorem _root_.CategoryTheory.map_comp_app_comp_eq_of_comp_eq {C₁ C₂ C₃ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] (Rb : C₂ ⥤ C₃) (Ra : C₁ ⥤ C₂) (Rc Rc' : C₁ ⥤ C₃)
    (μ : Ra ⋙ Rb ⟶ Rc) {T₁ T₂ : C₂} {K₁ K₂ : C₁} (θ : T₁ ⟶ T₂) (c : T₂ ⟶ Ra.obj K₂)
    (cs : T₁ ⟶ Ra.obj K₁) (θ' : K₁ ⟶ K₂) (h : θ ≫ c = cs ≫ Ra.map θ')
    (e₁ : Rc.obj K₁ ⟶ Rc'.obj K₁) (e₂ : Rc.obj K₂ ⟶ Rc'.obj K₂)
    (he : Rc.map θ' ≫ e₂ = e₁ ≫ Rc'.map θ') :
    Rb.map θ ≫ Rb.map c ≫ μ.app K₂ ≫ e₂ = (Rb.map cs ≫ μ.app K₁ ≫ e₁) ≫ Rc'.map θ' := by
  have hn := μ.naturality θ'
  simp only [Functor.comp_map] at hn
  rw [← Rb.map_comp_assoc, h, Rb.map_comp_assoc, reassoc_of% hn, he]
  simp only [Category.assoc]

/-- A transformation `μ : Ra ⋙ Rb ⟶ Rc`, followed by maps `e₁, e₂` into `Rc'` intertwining `Rc(θ')`
and `Rc'(θ')`, intertwines `Rb(Ra(θ'))` and `Rc'(θ')`. -/
theorem _root_.CategoryTheory.map_map_comp_app_comp_eq {C₁ C₂ C₃ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] (Rb : C₂ ⥤ C₃) (Ra : C₁ ⥤ C₂) (Rc Rc' : C₁ ⥤ C₃)
    (μ : Ra ⋙ Rb ⟶ Rc) {K₁ K₂ : C₁} (θ' : K₁ ⟶ K₂) (e₁ : Rc.obj K₁ ⟶ Rc'.obj K₁)
    (e₂ : Rc.obj K₂ ⟶ Rc'.obj K₂) (he : Rc.map θ' ≫ e₂ = e₁ ≫ Rc'.map θ') :
    Rb.map (Ra.map θ') ≫ μ.app K₂ ≫ e₂ = (μ.app K₁ ≫ e₁) ≫ Rc'.map θ' := by
  have hn := μ.naturality θ'
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, he]
  simp only [Category.assoc]

/-- **Transporting a normalised section along isomorphisms out of the target**: if
`c' ≫ x = c` and `Θ' ≫ x = x' ≫ Θ` with `x` and `x'` isomorphisms, a normalised section of
`c' ⊕ Θ'` gives one of `c ⊕ Θ`. -/
theorem _root_.CategoryTheory.Limits.exists_retraction_and_section_of_comp_eq {C : Type*}
    [Category* C] [Preadditive C] {A R R' W W' : C} (c : A ⟶ R) (c' : A ⟶ R') (Θ : W ⟶ R)
    (Θ' : W' ⟶ R') (x : R' ⟶ R) (x' : W' ⟶ W) (hx : IsIso x) (hx' : IsIso x') (hc : c' ≫ x = c)
    (hΘ : Θ' ≫ x = x' ≫ Θ)
    (H : ∃ (τ : R' ⟶ A) (ν : R' ⟶ W'), c' ≫ τ = 𝟙 A ∧ c' ≫ ν = 0 ∧ τ ≫ c' + ν ≫ Θ' = 𝟙 R') :
    ∃ (τ : R ⟶ A) (ν : R ⟶ W), c ≫ τ = 𝟙 A ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ Θ = 𝟙 R :=
  Limits.exists_retraction_and_section_of_iso c c' Θ Θ' (asIso x).symm (asIso x').symm
    (by rw [Iso.symm_hom, asIso_inv, ← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (by rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq, hΘ]) H

/-- The section of `c ⊕ Rp_*θ` only depends on the class. -/
theorem HasDirectImageSection.of_eq {p : X ⟶ Y} {g : Y ⟶ S} {n : ℤ}
    {ξ ξ' : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) n}
    (h : HasDirectImageSection p g n ξ) (e : ξ = ξ') : HasDirectImageSection p g n ξ' :=
  e ▸ h

/-- The comparison of the direct image along a composite `c = a ≫ q` with the composite of
direct images, at an object of the source. -/
abbrev compDirectImage {Y' : Scheme.{u}} (a : X' ⟶ Y') (q : Y' ⟶ Y) (c : X' ⟶ Y) (hc : a ≫ q = c)
    (g : Y ⟶ S) (s : X' ⟶ S) (wa : a ≫ q ≫ g = s ≫ 𝟙 S) (wq : q ≫ g = (q ≫ g) ≫ 𝟙 S)
    (wc : c ≫ g = s ≫ 𝟙 S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase s)))) :
    (derivedPushforward (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).obj
        ((derivedPushforward (inverseImageBaseMap a s (q ≫ g) (𝟙 S) wa)).obj K) ⟶
      (derivedPushforward (inverseImageBaseMap c s g (𝟙 S) wc)).obj K :=
  (derivedPushforwardCompIso (inverseImageBaseMap a s (q ≫ g) (𝟙 S) wa)
      (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).hom.app K ≫
    eqToHom (congrArg (fun k => (derivedPushforward k).obj K)
      (inverseImageBaseMap_comp q g (q ≫ g) (𝟙 S) wq a s (𝟙 S) wa c (𝟙 S) wc hc
        (Category.id_comp _)))

/-- The canonical map `compDirectImage a q c hc g s wa wq wc K` is an isomorphism. -/
instance {Y' : Scheme.{u}} (a : X' ⟶ Y') (q : Y' ⟶ Y) (c : X' ⟶ Y) (hc : a ≫ q = c)
    (g : Y ⟶ S) (s : X' ⟶ S) (wa : a ≫ q ≫ g = s ≫ 𝟙 S) (wq : q ≫ g = (q ≫ g) ≫ 𝟙 S)
    (wc : c ≫ g = s ≫ 𝟙 S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase s)))) :
    IsIso (compDirectImage a q c hc g s wa wq wc K) := by
  unfold compDirectImage
  infer_instance

/-- **The canonical maps of a composable pair of squares over `S` compose** (Section 07HX). -/
theorem comp_compDirectImage {Y' : Scheme.{u}} (a : X' ⟶ Y') (q : Y' ⟶ Y) (c : X' ⟶ Y)
    (hc : a ≫ q = c) (g : Y ⟶ S) (s : X' ⟶ S) (wa : a ≫ q ≫ g = s ≫ 𝟙 S)
    (wq : q ≫ g = (q ≫ g) ≫ 𝟙 S) (wc : c ≫ g = s ≫ 𝟙 S) :
    deRhamComparisonQ q (q ≫ g) g (𝟙 S) wq ≫
        (derivedPushforward (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).map
          (deRhamComparisonQ a s (q ≫ g) (𝟙 S) wa) ≫
        compDirectImage a q c hc g s wa wq wc (deRhamObject s) =
      deRhamComparisonQ c s g (𝟙 S) wc :=
  deRhamComparisonQ_comp q g (q ≫ g) (𝟙 S) wq a s (𝟙 S) wa c (𝟙 S) wc hc (Category.id_comp _)

/-- **The untwisted morphisms along a composable pair of squares over `S`.** For a class `ξ` on
the middle term and its pullback along `a`, the direct image along `q` of `θ_ξ`, followed by that
of the canonical map of `a` and the comparison of direct images, is the direct image along `q` of
the translated canonical map of `a`, followed by the comparison and the direct image along `c` of
`θ_{a^*ξ}`. -/
theorem map_classUntwisted_comp_compDirectImage {Y' : Scheme.{u}} (a : X' ⟶ Y') (q : Y' ⟶ Y)
    (c : X' ⟶ Y) (hc : a ≫ q = c) (g : Y ⟶ S) (s : X' ⟶ S) (wa : a ≫ q ≫ g = s ≫ 𝟙 S)
    (wq : q ≫ g = (q ≫ g) ≫ 𝟙 S) (wc : c ≫ g = s ≫ 𝟙 S) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (q ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (q ≫ g))) n) :
    (derivedPushforward (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).map
        (classUntwisted (q ≫ g) n ξ) ≫
      (derivedPushforward (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).map
          (deRhamComparisonQ a s (q ≫ g) (𝟙 S) wa) ≫
        compDirectImage a q c hc g s wa wq wc (deRhamObject s) =
      ((derivedPushforward (inverseImageBaseMap q (q ≫ g) g (𝟙 S) wq)).map
          ((deRhamComparisonQ a s (q ≫ g) (𝟙 S) wa)⟦-n⟧' ≫
            ((derivedPushforward (inverseImageBaseMap a s (q ≫ g) (𝟙 S) wa)).commShiftIso
              (-n)).inv.app _) ≫
        compDirectImage a q c hc g s wa wq wc ((deRhamObject s)⟦-n⟧)) ≫
      (derivedPushforward (inverseImageBaseMap c s g (𝟙 S) wc)).map
        (classUntwisted s n (deRhamPullbackSquare a s (q ≫ g) (𝟙 S) wa n ξ)) :=
  map_comp_app_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ _
    (classUntwisted_comp_deRhamComparisonQ a s (q ≫ g) (𝟙 S) wa n ξ) _ _
    (derivedPushforward_map_comp_eqToHom
      (inverseImageBaseMap_comp q g (q ≫ g) (𝟙 S) wq a s (𝟙 S) wa c (𝟙 S) wc hc
        (Category.id_comp _)) _)

/-- **The section of `c ⊕ Rp_*θ` is invariant under an isomorphism over the base**: if
`φ : X' ⟶ X` is an isomorphism with `φ ≫ p = p'` and `p` has the section for `ξ`, then `p'` has the
section for `φ^*ξ`. -/
theorem HasDirectImageSection.of_isIso (φ : X' ⟶ X) [IsIso φ] (p : X ⟶ Y) (p' : X' ⟶ Y)
    (g : Y ⟶ S) (hp : φ ≫ p = p') (w : φ ≫ p ≫ g = (p' ≫ g) ≫ 𝟙 S) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) n)
    (h : HasDirectImageSection p g n ξ) :
    HasDirectImageSection p' g n (deRhamPullbackSquare φ (p' ≫ g) (p ≫ g) (𝟙 S) w n ξ) := by
  have wq : p ≫ g = (p ≫ g) ≫ 𝟙 S := (Category.comp_id _).symm
  have wc : p' ≫ g = (p' ≫ g) ≫ 𝟙 S := (Category.comp_id _).symm
  have hcφ := isIso_deRhamComparisonQ_of_isIso φ (p' ≫ g) (p ≫ g) (𝟙 S) w
  unfold HasDirectImageSection at h ⊢
  have hA : IsIso ((derivedPushforward (inverseImageBaseMap p (p ≫ g) g (𝟙 S) wq)).map
      (deRhamComparisonQ φ (p' ≫ g) (p ≫ g) (𝟙 S) w) ≫
        compDirectImage φ p p' hp g (p' ≫ g) w wq wc (deRhamObject (p' ≫ g))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _
      ((derivedPushforward (inverseImageBaseMap p (p ≫ g) g (𝟙 S) wq)).mapIso
        (@asIso _ _ _ _ _ hcφ)).isIso_hom inferInstance
  have hA' : IsIso ((derivedPushforward (inverseImageBaseMap p (p ≫ g) g (𝟙 S) wq)).map
      ((deRhamComparisonQ φ (p' ≫ g) (p ≫ g) (𝟙 S) w)⟦-n⟧' ≫
        ((derivedPushforward (inverseImageBaseMap φ (p' ≫ g) (p ≫ g) (𝟙 S) w)).commShiftIso
          (-n)).inv.app _) ≫
        compDirectImage φ p p' hp g (p' ≫ g) w wq wc ((deRhamObject (p' ≫ g))⟦-n⟧)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _
      ((derivedPushforward (inverseImageBaseMap p (p ≫ g) g (𝟙 S) wq)).mapIso
        (((shiftFunctor _ (-n)).mapIso (@asIso _ _ _ _ _ hcφ)) ≪≫
          ((derivedPushforward (inverseImageBaseMap φ (p' ≫ g) (p ≫ g) (𝟙 S) w)).commShiftIso
            (-n)).symm.app _)).isIso_hom inferInstance
  exact Limits.exists_retraction_and_section_of_comp_eq _ _ _ _ _ _ hA hA'
    (comp_compDirectImage φ p p' hp g (p' ≫ g) w wq wc)
    (map_classUntwisted_comp_compDirectImage φ p p' hp g (p' ≫ g) w wq wc n ξ) h

section Restrict

variable {Y' : Scheme.{u}} (ι : X' ⟶ X) [IsOpenImmersion ι] (p : X ⟶ Y) (p' : X' ⟶ Y')
  (j : Y' ⟶ Y) [IsOpenImmersion j] (g : Y ⟶ S) (wι : ι ≫ p ≫ g = (p' ≫ j ≫ g) ≫ 𝟙 S)
  (wj : j ≫ g = (j ≫ g) ≫ 𝟙 S)

/-- After restriction to `Y'`, the canonical map of the square `(Y' ⟶ Y, 𝟙 S)` is invertible. -/
theorem isIso_mapDerivedCategory_map_deRhamComparisonQ :
    IsIso ((RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        (deRhamComparisonQ j (j ≫ g) g (𝟙 S) wj)) := by
  refine Stacks.Cohomology.OpenImmersionSections.isIso_mapDerivedCategory_map_of_bijective _ _
    fun W hW k => ?_
  rw [inverseImageBaseMap_base] at hW
  have := isIso_derivedSectionsOverOpen_map_deRhamComparisonQ j (j ≫ g) g (𝟙 S) wj W
    (fun x hx => hW hx)
  exact bijective_homology_map_derivedSectionsOverOpen W _ this k

variable (hrange : ∀ x : X, p.base x ∈ Set.range j.base → x ∈ Set.range ι.base)

include hrange in
/-- The preimage under `p` of an open inside the image of `j` lies inside the image of `ι`. -/
theorem opensMap_obj_le_opensRange (W : Opens Y) (hW : (W : Set Y) ⊆ Set.range j.base) :
    (RingedSpaceModuleAdjunction.opensMap (baseMap p g)).obj W ≤ ι.opensRange := by
  intro x hx
  refine hrange x (hW ?_)
  have : (baseMap p g).hom.base x ∈ W := hx
  rwa [inverseImageBaseMap_base] at this

/-- Over opens of the base inside the image of `j`, a morphism that is invertible on derived
sections over the preimages under `p` of these opens has invertible direct image along `p`. -/
private theorem isIso_mapDerivedCategory_map_relativeDirectImage_map
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase (p ≫ g))))}
    (f : K ⟶ L)
    (hf : ∀ W : Opens Y, (W : Set Y) ⊆ Set.range j.base → IsIso
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (inverseImageBase (p ≫ g)) ((RingedSpaceModuleAdjunction.opensMap (baseMap p g)).obj W)).map
          f)) :
    IsIso ((RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((relativeDirectImage p g).map f)) := by
  refine Stacks.Cohomology.OpenImmersionSections.isIso_mapDerivedCategory_map_of_bijective _ _
    fun W hW k => ?_
  rw [inverseImageBaseMap_base] at hW
  refine (Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff
    (baseMap p g) W _ k).2 ?_
  exact bijective_homology_map_derivedSectionsOverOpen _ f (hf W hW) k

include hrange in
/-- After restriction to `Y'`, the direct image along `p` of the canonical map of
`(ι, 𝟙 S)` is invertible. -/
theorem isIso_mapDerivedCategory_map_map_deRhamComparisonQ :
    IsIso ((RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((relativeDirectImage p g).map (deRhamComparisonQ ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι))) := by
  exact isIso_mapDerivedCategory_map_relativeDirectImage_map p j g wj _ fun W hW =>
    isIso_derivedSectionsOverOpen_map_deRhamComparisonQ ι _ _ _ wι _
      (opensMap_obj_le_opensRange ι p j g hrange W hW)

include hrange in
/-- After restriction to `Y'`, the direct image along `p` of the translated canonical map of
`(ι, 𝟙 S)` is invertible. -/
theorem isIso_mapDerivedCategory_map_map_shift_deRhamComparisonQ (n : ℤ) :
    IsIso ((RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((relativeDirectImage p g).map
          ((deRhamComparisonQ ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι)⟦-n⟧' ≫
            ((derivedPushforward (inverseImageBaseMap ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι)).commShiftIso
              (-n)).inv.app _))) := by
  refine isIso_mapDerivedCategory_map_relativeDirectImage_map p j g wj _ fun W hW => ?_
  have := isIso_derivedSectionsOverOpen_map_shift _ _
    (isIso_derivedSectionsOverOpen_map_deRhamComparisonQ ι _ _ _ wι _
      (opensMap_obj_le_opensRange ι p j g hrange W hW)) (-n)
  rw [Functor.map_comp]
  infer_instance

/-- An image of a composite whose first factor has invertible image and whose second factor is
invertible is invertible. -/
theorem _root_.CategoryTheory.Functor.isIso_map_comp_of_isIso_map {C D : Type*}
    [Category* C] [Category* D]
    (F : C ⥤ D) {A B E : C} (f : A ⟶ B) (k : B ⟶ E) [IsIso (F.map f)] [IsIso k] :
    IsIso (F.map (f ≫ k)) := by
  rw [F.map_comp]
  infer_instance

include hrange in
/-- **The section of `c ⊕ Rp_*θ` over an open of the base.** Let `j : Y' ⟶ Y` be an open
immersion and `ι : X' ⟶ X` an open immersion with `ι ≫ p = p' ≫ j` whose image contains every
point of `X` mapping into the image of `j`. If `p'` has the section of `c ⊕ Rp'_*θ` for the
pullback of `ξ`, then, after restriction `j^* : D(Y, g⁻¹𝒪_S) ⥤ D(Y', (j ≫ g)⁻¹𝒪_S)`, the canonical
map `c` of `p` has a retraction `τ` with `τ ≫ c + ν ≫ Rp_*θ = 𝟙` for some `ν`. -/
theorem exists_section_mapDerivedCategory_of_restrict (hw : ι ≫ p = p' ≫ j) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) n)
    (h : HasDirectImageSection p' (j ≫ g) n
      (deRhamPullbackSquare ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι n ξ)) :
    ∃ (τ : (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.obj
          ((relativeDirectImage p g).obj (deRhamObject (p ≫ g))) ⟶
        (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.obj (deRhamObject g))
      (ν : (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.obj
          ((relativeDirectImage p g).obj (deRhamObject (p ≫ g))) ⟶
        (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.obj
          ((relativeDirectImage p g).obj ((deRhamObject (p ≫ g))⟦-n⟧))),
      (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
          (deRhamDirectImageMap p g) ≫ τ = 𝟙 _ ∧
        τ ≫ (RingedSpaceModuleAdjunction.modulePullback
          (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
            (deRhamDirectImageMap p g) +
          ν ≫ (RingedSpaceModuleAdjunction.modulePullback
            (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
              ((relativeDirectImage p g).map (classUntwisted (p ≫ g) n ξ)) = 𝟙 _ := by
  have wq : p ≫ g = (p ≫ g) ≫ 𝟙 S := (Category.comp_id _).symm
  have wr : p' ≫ j ≫ g = (p' ≫ j ≫ g) ≫ 𝟙 S := (Category.comp_id _).symm
  have wc : (p' ≫ j) ≫ g = (p' ≫ j ≫ g) ≫ 𝟙 S := by rw [Category.assoc]; exact wr
  have ha := isIso_mapDerivedCategory_map_deRhamComparisonQ j g wj
  have := isIso_mapDerivedCategory_map_map_deRhamComparisonQ ι p p' j g wι wj hrange
  have := isIso_mapDerivedCategory_map_map_shift_deRhamComparisonQ ι p p' j g wι wj hrange n
  have hx := Functor.isIso_map_comp_of_isIso_map
    (RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory
    ((relativeDirectImage p g).map (deRhamComparisonQ ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι))
    (compDirectImage ι p (p' ≫ j) hw g (p' ≫ j ≫ g) wι wq wc (deRhamObject (p' ≫ j ≫ g)))
  have hx' := Functor.isIso_map_comp_of_isIso_map
    (RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory
    ((relativeDirectImage p g).map
      ((deRhamComparisonQ ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι)⟦-n⟧' ≫
        ((derivedPushforward (inverseImageBaseMap ι (p' ≫ j ≫ g) (p ≫ g) (𝟙 S) wι)).commShiftIso
          (-n)).inv.app _))
    (compDirectImage ι p (p' ≫ j) hw g (p' ≫ j ≫ g) wι wq wc ((deRhamObject (p' ≫ j ≫ g))⟦-n⟧))
  unfold HasDirectImageSection at h
  obtain ⟨τ, ν, h₁, -, h₃⟩ := h
  have key : ∀ {A} (z : A ⟶ A), z = 𝟙 A → (RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((derivedPushforward (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).map z) = 𝟙 _ := by
    rintro A z rfl
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  refine Functor.exists_retraction_and_section_map_of_comp_eq _ _ _ _ _ _ _ _ _
    (compDirectImage p' j (p' ≫ j) rfl g (p' ≫ j ≫ g) wr wj wc (deRhamObject (p' ≫ j ≫ g)))
    (compDirectImage p' j (p' ≫ j) rfl g (p' ≫ j ≫ g) wr wj wc
      ((deRhamObject (p' ≫ j ≫ g))⟦-n⟧)) inferInstance inferInstance ha hx hx'
    ((comp_compDirectImage ι p (p' ≫ j) hw g (p' ≫ j ≫ g) wι wq wc).trans
      (comp_compDirectImage p' j (p' ≫ j) rfl g (p' ≫ j ≫ g) wr wj wc).symm)
    (map_classUntwisted_comp_compDirectImage ι p (p' ≫ j) hw g (p' ≫ j ≫ g) wι wq wc n ξ)
    (map_map_comp_app_comp_eq _ _ _ _ _ _ _ _ (derivedPushforward_map_comp_eqToHom
      (inverseImageBaseMap_comp j g (j ≫ g) (𝟙 S) wj p' (p' ≫ j ≫ g) (𝟙 S) wr (p' ≫ j) (𝟙 S) wc
        rfl (Category.id_comp _)) _))
    ⟨(RingedSpaceModuleAdjunction.modulePullback
        (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((derivedPushforward (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).map τ),
      (RingedSpaceModuleAdjunction.modulePullback
        (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).mapDerivedCategory.map
        ((derivedPushforward (inverseImageBaseMap j (j ≫ g) g (𝟙 S) wj)).map ν), ?_, ?_⟩
  · refine Eq.trans ?_ (key _ h₁)
    simp only [Functor.map_comp]
    all_goals rfl
  · refine Eq.trans ?_ (key _ h₃)
    simp only [Functor.map_comp, Functor.map_add]
    all_goals rfl

end Restrict

end AlgebraicGeometry.DeRhamLerayHirsch

end
