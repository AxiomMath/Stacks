module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartAssembly
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsEquivBaseChange
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorizationGlue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 0B3V]: sections of a projective bundle and invertible quotients

Let `X` be a scheme, `ℰ` a quasi-coherent `𝒪_X`-module with no further hypothesis, and
`π : 𝐏(ℰ) ⟶ X` its projective bundle — `Stacks.RelativeProj.projectiveBundle X ℰ` with
projection `Stacks.RelativeProj.projectiveBundleToBase X ℰ`, the object of Tag 01OB. Tag 0B3V
asserts:

1. a bijection between the sections `σ` of `π` and the surjections `ℰ → 𝓛` onto invertible
   modules, up to isomorphism of quotients;
2. in this case `σ` is a closed immersion;
3. a canonical isomorphism `Ker(ℰ → 𝓛) ⊗ 𝓛^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}`;
4. both the bijection and the isomorphism are compatible with base change.

The tag has no numbered parts, so it is registered once, on
`Stacks.RelativeProj.projectiveBundle_sections_classification`, whose statement is the
conjunction of the clauses written in terms of the canonical constructions on `𝐏(ℰ)`:

* the bijection is `Stacks.RelativeProj.projectiveBundleSectionsEquiv`, with the normalization
  `Stacks.RelativeProj.projectiveBundleSectionsEquiv_eq_iff` (`σ` goes to the class of `σ^*` of
  the tautological quotient);
* the closed immersion is
  `Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`;
* the isomorphism is `Stacks.RelativeProj.projectiveBundleConormalIso`, pinned by
  `Stacks.RelativeProj.projectiveBundleConormalIso_hom`;
* the base-change clauses are `Stacks.RelativeProj.projectiveBundleSectionsEquiv_baseChange` and
  `Stacks.RelativeProj.projectiveBundleConormalIso_baseChange`, along the base-change morphism
  `Stacks.RelativeProj.projectiveBundleBaseChange`.

## Implementation notes

The canonical map `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` and its two properties
(`isIso_conormalCanonicalMap`, `conormalCanonicalMap_baseChange`) were computed over a second
presentation of the same scheme, `Stacks.ProjectiveBundleConormal.bundle ℰ`, which is used here
only as proof machinery. A section `σ` of `𝐏(ℰ)` is carried to it as `σ ≫ b⁻¹` for the
comparison `b = Stacks.RelativeProj.bundlePresentationIso ℰ` (`presentationSection`), the
classifying isomorphism along `presentationTwistIso`, and the conormal sheaf back along
`conormalPresentationIso`: the base-change map `Stacks.Conormal.conormalBaseChangeMap` of the
square `σ ≫ b⁻¹ = 𝟙 ≫ (σ ≫ b⁻¹)`, invertible because the square's other edges are isomorphisms
(`Stacks.Conormal.isIso_conormalBaseChangeMap_of_isIso`, from the flat case
`Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`).

Transporting the base-change clause between the two presentations is
`Stacks.Conormal.conormalBaseChangeMap_comp_unit_square`. It rests on the identification
`Stacks.Conormal.conormalBaseChangeMap_eq_immersionConormalSheafMap` of the base-change map with
the canonical map of [Stacks, Tag 01R4], whose composition law is
`Stacks.Immersion.immersionConormalSheafMap_comp`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.Modules

/-- **Pulling a quotient map back along a section, across an isomorphism of total spaces.** Let
`ρ : R ⟶ B` and `π : P ⟶ B` be two morphisms with `g ≫ ρ = π`, let `t : ρ^*M ⟶ T`, and let
`f : B ⟶ P` and `τ : B ⟶ R` be sections with `f ≫ g = τ`. Then pulling back the transported
quotient `π^*M ⟶ g^*T` along `f` and identifying `f^*g^*T` with `τ^*T` gives the pull back of `t`
along `τ`. -/
theorem pullback_section_transport {B P R : Scheme.{u}} (f : B ⟶ P) (g : P ⟶ R) (ρ : R ⟶ B)
    (π : P ⟶ B) (τ : B ⟶ R) (hρ : g ≫ ρ = π) (h : f ≫ g = τ) (hf : f ≫ π = 𝟙 B)
    (hτ : τ ≫ ρ = 𝟙 B) {M : B.Modules} {T : R.Modules}
    (t : (Scheme.Modules.pullback ρ).obj M ⟶ T) :
    ((Scheme.Modules.pullbackId B).inv.app M ≫ (Scheme.Modules.pullbackCongr hf).inv.app M ≫
        (Scheme.Modules.pullbackComp f π).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr hρ).inv.app M ≫
          (Scheme.Modules.pullbackComp g ρ).inv.app M ≫ (Scheme.Modules.pullback g).map t)) ≫
        ((Scheme.Modules.pullbackComp f g).hom.app T ≫
          (Scheme.Modules.pullbackCongr h).hom.app T) =
      (Scheme.Modules.pullbackId B).inv.app M ≫ (Scheme.Modules.pullbackCongr hτ).inv.app M ≫
        (Scheme.Modules.pullbackComp τ ρ).inv.app M ≫ (Scheme.Modules.pullback τ).map t := by
  simp only [Category.assoc]
  subst h hρ
  have key := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity (f := f) (g := g) (h := ρ)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at key
  have nat := (Scheme.Modules.pullbackComp f g).hom.naturality t
  simp only [Functor.comp_map] at nat
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc,
    NatTrans.id_app]
  rw [nat]
  have key' : (Scheme.Modules.pullbackComp f (g ≫ ρ)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g ρ).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback ρ).obj M) =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (f ≫ g) ρ).inv.app M := by
    rw [← Iso.cancel_iso_hom_right _ _ ((Scheme.Modules.pullbackComp (f ≫ g) ρ).app M)]
    simp only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    simpa using key
  rw [reassoc_of% key']
  simp

/-- `Stacks.Modules.pullback_section_transport` with the target of the transported quotient
identified with `g^*T` through an isomorphism `ψ`. -/
theorem pullback_section_transport_of_iso {B P R : Scheme.{u}} (f : B ⟶ P) (g : P ⟶ R)
    (ρ : R ⟶ B) (π : P ⟶ B) (τ : B ⟶ R) (hρ : g ≫ ρ = π) (h : f ≫ g = τ) (hf : f ≫ π = 𝟙 B)
    (hτ : τ ≫ ρ = 𝟙 B) {M : B.Modules} {T : R.Modules} {D : P.Modules}
    (u : (Scheme.Modules.pullback π).obj M ⟶ D) (ψ : D ≅ (Scheme.Modules.pullback g).obj T)
    (t : (Scheme.Modules.pullback ρ).obj M ⟶ T)
    (hu : u ≫ ψ.hom = (Scheme.Modules.pullbackCongr hρ).inv.app M ≫
      (Scheme.Modules.pullbackComp g ρ).inv.app M ≫ (Scheme.Modules.pullback g).map t) :
    ((Scheme.Modules.pullbackId B).inv.app M ≫ (Scheme.Modules.pullbackCongr hf).inv.app M ≫
        (Scheme.Modules.pullbackComp f π).inv.app M ≫ (Scheme.Modules.pullback f).map u) ≫
        ((Scheme.Modules.pullback f).map ψ.hom ≫ (Scheme.Modules.pullbackComp f g).hom.app T ≫
          (Scheme.Modules.pullbackCongr h).hom.app T) =
      (Scheme.Modules.pullbackId B).inv.app M ≫ (Scheme.Modules.pullbackCongr hτ).inv.app M ≫
        (Scheme.Modules.pullbackComp τ ρ).inv.app M ≫ (Scheme.Modules.pullback τ).map t := by
  rw [← pullback_section_transport f g ρ π τ hρ h hf hτ t, ← hu, Functor.map_comp]
  simp only [Category.assoc]

end Stacks.Modules

namespace Stacks.Conormal

/-! ### Functoriality of the base-change map of conormal sheaves -/

section Functoriality

variable {Z Z' W W' : Scheme.{u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}
  [IsImmersion i] [IsImmersion j]

/-- `Stacks.Conormal.conormalBaseChangeMap` is the canonical map of [Stacks, Tag 01R4],
`Stacks.Immersion.immersionConormalSheafMap`: the two are built from the same map of ideal
sheaves, conjugated by the two identifications of the conormal sheaf with `i^*ℐ_i`, which are
inverse to each other
(`Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf`). -/
theorem conormalBaseChangeMap_eq_immersionConormalSheafMap (comm : i ≫ k = f ≫ j) :
    conormalBaseChangeMap comm =
      Stacks.Immersion.immersionConormalSheafMap i j f k (comm_toShHom comm) := by
  rw [Stacks.Immersion.immersionConormalSheafMap,
    Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf,
    Stacks.Immersion.conormalSheafSelfIso_eq_symm_conormalSheafIsoPullbackSelf]
  rfl

/-- The base-change map only depends on the left edge of the square through its type. -/
theorem conormalBaseChangeMap_congr {f' : Z ⟶ W} (hf : f = f') {k' : Z' ⟶ W'} (hk : k = k')
    (comm : i ≫ k = f ≫ j) (comm' : i ≫ k' = f' ≫ j) :
    conormalBaseChangeMap comm' =
      (Scheme.Modules.pullbackCongr hf).inv.app (conormalSheaf j) ≫ conormalBaseChangeMap comm := by
  subst hf hk
  exact (Category.id_comp _).symm

/-- **[Stacks, Tag 01R4] / [Stacks, Tag 04G2] part (3): the base-change map of a vertically
stacked pair of squares is the composite of the two base-change maps.** This is
`Stacks.Immersion.immersionConormalSheafMap_comp` read through
`conormalBaseChangeMap_eq_immersionConormalSheafMap`. -/
theorem conormalBaseChangeMap_comp {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}}
    {i₁ : Z₁ ⟶ X₁} {i₂ : Z₂ ⟶ X₂} {i₃ : Z₃ ⟶ X₃}
    [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃]
    {f₁ : Z₁ ⟶ Z₂} {g₁ : X₁ ⟶ X₂} (comm₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    {f₂ : Z₂ ⟶ Z₃} {g₂ : X₂ ⟶ X₃} (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃) :
    conormalBaseChangeMap (Stacks.Immersion.square_comp comm₁ comm₂) =
      (Scheme.Modules.pullbackComp f₁ f₂).inv.app (conormalSheaf i₃) ≫
        (Scheme.Modules.pullback f₁).map (conormalBaseChangeMap comm₂) ≫
          conormalBaseChangeMap comm₁ := by
  rw [conormalBaseChangeMap_eq_immersionConormalSheafMap,
    conormalBaseChangeMap_eq_immersionConormalSheafMap,
    conormalBaseChangeMap_eq_immersionConormalSheafMap]
  exact Stacks.Immersion.immersionConormalSheafMap_comp i₁ i₂ i₃ f₁ g₁ comm₁ f₂ g₂ comm₂

/-- **The base-change map of a square whose other two edges are isomorphisms is an isomorphism.**
Such a square is cartesian and an isomorphism is flat, so this is
`Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`. -/
theorem isIso_conormalBaseChangeMap_of_isIso [IsIso f] [IsIso k] (comm : i ≫ k = f ≫ j) :
    IsIso (conormalBaseChangeMap comm) := by
  rw [conormalBaseChangeMap_eq_immersionConormalSheafMap]
  exact Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i j f k
    (IsPullback.of_vert_isIso ⟨comm⟩)

end Functoriality

section Unitality

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (C : X.Modules)

/-- Unitality of the pullback pseudofunctor on the left, read at one module. -/
theorem pullbackId_inv_comp_pullbackComp_id_hom :
    (Scheme.Modules.pullbackId X').inv.app ((Scheme.Modules.pullback g).obj C) ≫
        (Scheme.Modules.pullbackComp (𝟙 X') g).hom.app C ≫
          (Scheme.Modules.pullbackCongr (Category.id_comp g).symm).inv.app C = 𝟙 _ := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality g) C
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at key
  have hI : (Scheme.Modules.pullbackComp (𝟙 X') g).symm.app C ≪≫
      (Scheme.Modules.pullbackId X').app ((Scheme.Modules.pullback g).obj C) =
        eqToIso (by simp) := Iso.ext (by simpa using key)
  have h2 : (Scheme.Modules.pullbackId X').inv.app ((Scheme.Modules.pullback g).obj C) ≫
      (Scheme.Modules.pullbackComp (𝟙 X') g).hom.app C = eqToHom (by simp) :=
    congrArg Iso.inv hI
  rw [reassoc_of% h2]
  simp [Scheme.Modules.pullbackCongr]

/-- Unitality of the pullback pseudofunctor on the right, read at one module. -/
theorem pullback_map_pullbackId_inv_comp_pullbackComp_hom :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId X).inv.app C) ≫
        (Scheme.Modules.pullbackComp g (𝟙 X)).hom.app C ≫
          (Scheme.Modules.pullbackCongr (Category.comp_id g).symm).inv.app C = 𝟙 _ := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality g) C
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at key
  have hI : (Scheme.Modules.pullbackComp g (𝟙 X)).symm.app C ≪≫
      (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackId X).app C) =
        eqToIso (by simp) := Iso.ext (by simpa using key)
  have h2 : (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId X).inv.app C) ≫
      (Scheme.Modules.pullbackComp g (𝟙 X)).hom.app C = eqToHom (by simp) :=
    congrArg Iso.inv hI
  rw [reassoc_of% h2]
  simp [Scheme.Modules.pullbackCongr]

end Unitality

section Presentation

/-- The bookkeeping of `conormalBaseChangeMap_comp_unit_square`, in a bare category, where the
pullback functors' `Category` instances do not get in the way of `rw`. -/
private theorem comp_eq_of_paste {D : Type*} [Category D]
    {A A₀ A₁ A₂ A₃ B B₁ T T' : D}
    (mcb : A ⟶ B) (i₁ : B ⟶ B₁) (mS' : B₁ ⟶ T) (i₀ : A ⟶ A₀) (m₁ : A₀ ⟶ B₁)
    (c₁ : A ⟶ A₁) (p₁ : A₁ ⟶ A₀) (gi : A ⟶ T') (gS : T' ⟶ A₂) (mc : A₂ ⟶ T)
    (c₂ : A ⟶ A₃) (p₂ : A₃ ⟶ T') (cf : A₃ ⟶ A₁) (M₁ : A₁ ⟶ T) (M₂ : A₃ ⟶ T)
    (nat : mcb ≫ i₁ = i₀ ≫ m₁) (hU₁ : i₀ = c₁ ≫ p₁) (hU₂ : gi = c₂ ≫ p₂)
    (P₁ : M₁ = p₁ ≫ m₁ ≫ mS') (P₂ : M₂ = p₂ ≫ gS ≫ mc) (C : M₂ = cf ≫ M₁)
    (hc : c₁ = c₂ ≫ cf) :
    mcb ≫ i₁ ≫ mS' = gi ≫ gS ≫ mc := by
  rw [reassoc_of% nat, hU₁, hU₂]
  simp only [Category.assoc]
  rw [← P₁, ← P₂, C, hc, Category.assoc]

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (C : X.Modules)

/-- `pullbackId_inv_comp_pullbackComp_id_hom`, solved for the unitor. -/
theorem pullbackId_inv_app_pullback_obj :
    (Scheme.Modules.pullbackId X').inv.app ((Scheme.Modules.pullback g).obj C) =
      (Scheme.Modules.pullbackCongr (Category.id_comp g).symm).hom.app C ≫
        (Scheme.Modules.pullbackComp (𝟙 X') g).inv.app C := by
  have h := pullbackId_inv_comp_pullbackComp_id_hom g C
  refine Eq.trans ?_ ((congrArg (· ≫ _) h).trans (Category.id_comp _))
  simp [Scheme.Modules.pullbackCongr]

/-- `pullback_map_pullbackId_inv_comp_pullbackComp_hom`, solved for the unitor. -/
theorem pullback_map_pullbackId_inv_app :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId X).inv.app C) =
      (Scheme.Modules.pullbackCongr (Category.comp_id g).symm).hom.app C ≫
        (Scheme.Modules.pullbackComp g (𝟙 X)).inv.app C := by
  have h := pullback_map_pullbackId_inv_comp_pullbackComp_hom g C
  refine Eq.trans ?_ ((congrArg (· ≫ _) h).trans (Category.id_comp _))
  simp [Scheme.Modules.pullbackCongr]

private theorem pullbackCongr_unit_paste :
    (Scheme.Modules.pullbackCongr (Category.id_comp g).symm).hom.app C =
      (Scheme.Modules.pullbackCongr (Category.comp_id g).symm).hom.app C ≫
        (Scheme.Modules.pullbackCongr
          ((Category.id_comp g).trans (Category.comp_id g).symm)).inv.app C := by
  simp [Scheme.Modules.pullbackCongr]

/-- **Transporting the base-change map of conormal sheaves along a change of ambient
presentation.** Let `σ, σ'` be immersions into `P, P'` and `τ, τ'` immersions into `B, B'`, with
`σ ≫ a = τ`, `σ' ≫ a' = τ'`, and squares `σ' ≫ kp = g ≫ σ`, `τ' ≫ kb = g ≫ τ` whose ambient
edges are related by `a' ≫ kb = kp ≫ a`. Then reading the `τ`-square's base-change map through the
identifications of the `a`-squares gives the `σ`-square's base-change map. Both sides are the
base-change map of the stacked square (`conormalBaseChangeMap_comp`), up to the unitors of the
pullback pseudofunctor. -/
theorem conormalBaseChangeMap_comp_unit_square {P P' B B' : Scheme.{u}}
    {σ : X ⟶ P} {σ' : X' ⟶ P'} {τ : X ⟶ B} {τ' : X' ⟶ B'}
    [IsImmersion σ] [IsImmersion σ'] [IsImmersion τ] [IsImmersion τ']
    {a : P ⟶ B} {a' : P' ⟶ B'} {kp : P' ⟶ P} {kb : B' ⟶ B}
    (S : σ ≫ a = 𝟙 X ≫ τ) (S' : σ' ≫ a' = 𝟙 X' ≫ τ') (cb : τ' ≫ kb = g ≫ τ)
    (c : σ' ≫ kp = g ≫ σ) (hk : a' ≫ kb = kp ≫ a) :
    conormalBaseChangeMap cb ≫ (Scheme.Modules.pullbackId X').inv.app (conormalSheaf τ') ≫
        conormalBaseChangeMap S' =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId X).inv.app (conormalSheaf τ)) ≫
        (Scheme.Modules.pullback g).map (conormalBaseChangeMap S) ≫ conormalBaseChangeMap c := by
  have nat := (Scheme.Modules.pullbackId X').inv.naturality (conormalBaseChangeMap cb)
  exact comp_eq_of_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nat
    (pullbackId_inv_app_pullback_obj g (conormalSheaf τ))
    (pullback_map_pullbackId_inv_app g (conormalSheaf τ))
    (conormalBaseChangeMap_comp S' cb) (conormalBaseChangeMap_comp c S)
    (conormalBaseChangeMap_congr ((Category.id_comp g).trans (Category.comp_id g).symm) hk
      (Stacks.Immersion.square_comp S' cb) (Stacks.Immersion.square_comp c S))
    (pullbackCongr_unit_paste g _)

end Presentation

end Stacks.Conormal

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-! ### The presentation `bundle ℰ` the conormal sheaf was computed over -/

/-- **The tautological quotient map pulled back along a section** `τ` of `bundle ℰ ⟶ X`, read as
a map out of `ℰ` through the identifications `ℰ ≅ 𝟙^*ℰ ≅ (τ ≫ π)^*ℰ ≅ τ^*π^*ℰ`. It is the
hypothesis of `conormalCanonicalMap`. -/
def sectionQuotientMap (τ : X ⟶ (bundle E).scheme) (hτ : τ ≫ (bundle E).toBase = 𝟙 X) :
    E ⟶ (Scheme.Modules.pullback τ).obj (tautologicalTwist E (symPieces E)) :=
  (Scheme.Modules.pullbackId X).inv.app E ≫ (Scheme.Modules.pullbackCongr hτ).inv.app E ≫
    (Scheme.Modules.pullbackComp τ (bundle E).toBase).inv.app E ≫
      (Scheme.Modules.pullback τ).map (tautologicalMap E (symPieces E))

/-- The tautological twist of `Stacks.RelativeProj.projectiveBundle` is, by definition, the
pullback of the tautological twist of `bundle ℰ` along the comparison of the two presentations. -/
def twistPresentationIso :
    (Stacks.RelativeProj.tautologicalDatum E).twist ≅
      (Scheme.Modules.pullback (Stacks.RelativeProj.bundlePresentationIso E).inv).obj
        (tautologicalTwist E (symPieces E)) :=
  Iso.refl _

/-- For `b = Stacks.RelativeProj.bundlePresentationIso ℰ`, the universal quotient of
`Stacks.RelativeProj.tautologicalDatum ℰ` followed by `twistPresentationIso` is the pullback along
`b⁻¹` of the tautological map of `bundle ℰ`, read through `π^*ℰ ≅ (b⁻¹ ≫ π)^*ℰ ≅ b⁻¹^*π^*ℰ`. -/
theorem tautologicalDatum_univ_comp_twistPresentationIso :
    (Stacks.RelativeProj.tautologicalDatum E).univ ≫ (twistPresentationIso E).hom =
      (Scheme.Modules.pullbackCongr
          (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase E)).inv.app E ≫
        (Scheme.Modules.pullbackComp (Stacks.RelativeProj.bundlePresentationIso E).inv
          (Stacks.RelativeProj.symGradedBundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback (Stacks.RelativeProj.bundlePresentationIso E).inv).map
          (tautologicalMap E (isQuasicoherentPieces_of_isQuasicoherent E)) :=
  (Category.comp_id _).trans (Stacks.RelativeProj.tautologicalDatumUniv_eq E)

end Stacks.ProjectiveBundleConormal

namespace Stacks.RelativeProj

open Stacks.ProjectiveBundleConormal

attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

section Sections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- A section `σ` of `𝐏(ℰ) ⟶ X`, read at the presentation `bundle ℰ` the conormal sheaf was
computed over: `σ ≫ b⁻¹` for the comparison `b = bundlePresentationIso ℰ`. -/
abbrev presentationSection (σ : X ⟶ projectiveBundle X E) : X ⟶ (bundle E).scheme :=
  σ ≫ (bundlePresentationIso E).inv

/-- If `σ` is a section of `𝐏(ℰ) ⟶ X`, then `presentationSection ℰ σ` is a section of
`bundle ℰ ⟶ X`. -/
theorem presentationSection_comp_toBase (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) :
    presentationSection E σ ≫ (bundle E).toBase = 𝟙 X :=
  (Category.assoc _ _ _).trans
    ((congrArg (σ ≫ ·) (bundlePresentationIso_inv_comp_toBase E)).trans hσ)

/-- The identification of the pullback of `𝒪(1)` along a section `σ` with the pullback of the
tautological twist of `bundle ℰ` along `presentationSection ℰ σ`. -/
def presentationTwistIso (σ : X ⟶ projectiveBundle X E) :
    (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅
      (Scheme.Modules.pullback (presentationSection E σ)).obj
        (tautologicalTwist E (symPieces E)) :=
  (Scheme.Modules.pullback σ).mapIso (twistPresentationIso E) ≪≫
    (Scheme.Modules.pullbackComp σ (bundlePresentationIso E).inv).app
      (tautologicalTwist E (symPieces E)) ≪≫
    (Scheme.Modules.pullbackCongr (rfl : presentationSection E σ = _)).app
      (tautologicalTwist E (symPieces E))

/-- The underlying map of `presentationTwistIso` is `σ^*` of `twistPresentationIso` followed by
the identification `σ^*b⁻¹^* ≅ (σ ≫ b⁻¹)^*` of pullbacks. -/
theorem presentationTwistIso_hom (σ : X ⟶ projectiveBundle X E) :
    (presentationTwistIso E σ).hom =
      (Scheme.Modules.pullback σ).map (twistPresentationIso E).hom ≫
        (Scheme.Modules.pullbackComp σ (bundlePresentationIso E).inv).hom.app
          (tautologicalTwist E (symPieces E)) ≫
        (Scheme.Modules.pullbackCongr (rfl : presentationSection E σ = _)).hom.app
          (tautologicalTwist E (symPieces E)) :=
  rfl

/-- The quotient a section `σ` pulls back from the canonical datum is the quotient
`presentationSection ℰ σ` pulls back from `bundle ℰ`, through `presentationTwistIso`. -/
theorem pullbackQuotientMap_comp_presentationTwistIso (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) :
    (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ (presentationTwistIso E σ).hom =
      sectionQuotientMap E (presentationSection E σ) (presentationSection_comp_toBase E σ hσ) := by
  have hu := tautologicalDatum_univ_comp_twistPresentationIso E
  have key := Stacks.Modules.pullback_section_transport_of_iso σ
    (bundlePresentationIso E).inv (symGradedBundle E).toBase
    (projectiveBundleToBase X E) (presentationSection E σ)
    (bundlePresentationIso_inv_comp_toBase E) rfl hσ (presentationSection_comp_toBase E σ hσ)
    (tautologicalDatum E).univ (twistPresentationIso E)
    (tautologicalMap E (isQuasicoherentPieces_of_isQuasicoherent E)) hu
  rw [TautologicalDatum.pullbackQuotientMap, presentationTwistIso_hom, sectionQuotientMap]
  exact key

/-- **The bijection is the classifying map**: `σ` goes to the class of `Q` exactly when `σ^*` of
the tautological quotient `π^*ℰ ⟶ 𝒪(1)` is `Q.q` up to an isomorphism of targets. -/
theorem projectiveBundleSectionsEquiv_eq_iff (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) (Q : Stacks.Divisors.InvertibleQuotient X E) :
    projectiveBundleSectionsEquiv ⟨σ, hσ⟩ =
        Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid X E) Q ↔
      ∃ e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L,
        (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q :=
  (tautologicalDatum E).sectionsEquivInvertibleQuotients_eq_iff σ hσ Q

end Sections

section Conormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)

/-- The comparison `e` of a section `σ` classifying `q`, carried to the presentation `bundle ℰ`. -/
def presentationClassifyingIso {σ : X ⟶ projectiveBundle X E}
    (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L) :
    (Scheme.Modules.pullback (presentationSection E σ)).obj
        (tautologicalTwist E (symPieces E)) ≅ Q.L :=
  (presentationTwistIso E σ).symm ≪≫ e

/-- If `e` carries `σ^*` of the tautological quotient to `q`, then `presentationClassifyingIso`
carries the tautological quotient of `bundle ℰ` pulled back along `presentationSection ℰ σ` to
`q`. -/
theorem sectionQuotientMap_comp_presentationClassifyingIso {σ : X ⟶ projectiveBundle X E}
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
    (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q) :
    sectionQuotientMap E (presentationSection E σ) (presentationSection_comp_toBase E σ hσ) ≫
      (presentationClassifyingIso E Q e).hom = Q.q := by
  change _ ≫ (presentationTwistIso E σ).inv ≫ e.hom = Q.q
  rw [← pullbackQuotientMap_comp_presentationTwistIso E σ hσ]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans hqe)

/-- The square `σ ≫ b⁻¹ = 𝟙 ≫ (σ ≫ b⁻¹)` comparing a section with its presentation. -/
theorem presentationSection_square (σ : X ⟶ projectiveBundle X E) :
    σ ≫ (bundlePresentationIso E).inv = 𝟙 X ≫ presentationSection E σ :=
  (Category.id_comp _).symm

/-- **The conormal sheaf of a section is that of its presentation**:
`𝒞_{σ ≫ b⁻¹} ≅ 𝒞_σ`, the base-change map `Stacks.Conormal.conormalBaseChangeMap` of the square
`presentationSection_square`, whose other two edges are isomorphisms. -/
def conormalPresentationIso (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    Stacks.Conormal.conormalSheaf (presentationSection E σ) ≅ Stacks.Conormal.conormalSheaf σ :=
  haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
  (Scheme.Modules.pullbackId X).symm.app _ ≪≫
    @asIso _ _ _ _ (Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E σ))
      (Stacks.Conormal.isIso_conormalBaseChangeMap_of_isIso (presentationSection_square E σ))

/-- The underlying map of `conormalPresentationIso` is the inverse unitor of the pullback along
`𝟙 X` followed by the base-change map of `presentationSection_square`. -/
theorem conormalPresentationIso_hom (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    (conormalPresentationIso E σ hσ).hom =
      (Scheme.Modules.pullbackId X).inv.app _ ≫
        Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E σ) :=
  rfl

/-- **[Stacks, Tag 0B3V]: the canonical isomorphism `Ker(ℰ → 𝓛) ⊗ 𝓛^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}`**,
for `σ` a section of `𝐏(ℰ) ⟶ X` matched with the invertible quotient `q : ℰ → 𝓛` through
`e : σ^*𝒪(1) ≅ 𝓛` (`projectiveBundleSectionsEquiv_eq_iff`), the conormal sheaf being that of the
closed immersion `σ` (`isClosedImmersion_of_section_projectiveBundleToBase`).

It is the canonical map `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` — `σ^*` of the
factorisation through the ideal sheaf of `σ` of the map `(π^*Ker q) ⊗ 𝒪(-1) ⟶ 𝒪` that the
tautological map induces, locally `k ⊗ s^{-1} ↦ k/s` — computed at the presentation of `𝐏(ℰ)` it
was built on, followed by the identification `conormalPresentationIso` of conormal sheaves. -/
def projectiveBundleConormalIso {σ : X ⟶ projectiveBundle X E}
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
    (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    kernel Q.q ⊗
        Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1) ≅
      Stacks.Conormal.conormalSheaf σ :=
  haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
  haveI := isIso_conormalCanonicalMap E Q (presentationSection_comp_toBase E σ hσ)
    (presentationClassifyingIso E Q e)
    (sectionQuotientMap_comp_presentationClassifyingIso E Q hσ e hqe)
  asIso (conormalCanonicalMap E Q (presentationSection_comp_toBase E σ hσ)
      (presentationClassifyingIso E Q e)
      (sectionQuotientMap_comp_presentationClassifyingIso E Q hσ e hqe)) ≪≫
    conormalPresentationIso E σ hσ

/-- The underlying map of `projectiveBundleConormalIso` is the canonical map
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at `presentationSection ℰ σ`, followed by
the underlying map of `conormalPresentationIso`. -/
theorem projectiveBundleConormalIso_hom {σ : X ⟶ projectiveBundle X E}
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
    (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    (projectiveBundleConormalIso E Q hσ e hqe).hom =
      conormalCanonicalMap E Q (presentationSection_comp_toBase E σ hσ)
          (presentationClassifyingIso E Q e)
          (sectionQuotientMap_comp_presentationClassifyingIso E Q hσ e hqe) ≫
        (Scheme.Modules.pullbackId X).inv.app _ ≫
          Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E σ) :=
  rfl

end Conormal

section BaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]

/-- **The bijection is compatible with base change**: for `g : X' ⟶ X`, a section `σ'` of
`𝐏(g^*ℰ) ⟶ X'` lying over a section `σ` of `𝐏(ℰ) ⟶ X` (along the base-change morphism
`projectiveBundleBaseChange`) goes to the base change of the class `σ` goes to. -/
theorem projectiveBundleSectionsEquiv_baseChange (σ : X ⟶ projectiveBundle X E)
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
    (σ' : X' ⟶ projectiveBundle X' ((Scheme.Modules.pullback g).obj E))
    (hσ' : σ' ≫ projectiveBundleToBase X' ((Scheme.Modules.pullback g).obj E) = 𝟙 X')
    (comm : σ' ≫ projectiveBundleBaseChange g E _ (Iso.refl _) = g ≫ σ) :
    projectiveBundleSectionsEquiv ⟨σ', hσ'⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass g (Iso.refl _)
        (projectiveBundleSectionsEquiv ⟨σ, hσ⟩) := by
  obtain rfl : σ' = sectionBaseChange g E σ hσ :=
    (isPullback_projectiveBundleToBase_baseChange g E _ (Iso.refl _)).hom_ext
      (hσ'.trans (sectionBaseChange_comp_projectiveBundleToBase g E σ hσ).symm)
      (comm.trans (sectionBaseChange_comp_projectiveBundleBaseChange g E σ hσ).symm)
  exact projectiveBundleSectionsEquiv_sectionBaseChange g E σ hσ

variable (E' : X'.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- The presentations of two sections lying over each other lie over each other. -/
theorem presentationSection_comp_bundleBaseChangeHom {σ : X ⟶ projectiveBundle X E}
    {σ' : X' ⟶ projectiveBundle X' E'} (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    presentationSection E' σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ presentationSection E σ :=
  (Category.assoc _ _ _).trans ((congrArg (σ' ≫ ·)
    (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g E E' hE).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (bundlePresentationIso E).inv) comm).trans
        (Category.assoc _ _ _))))

/-- **The base-change maps of conormal sheaves at the two presentations agree**, through the
identifications `conormalPresentationIso`. Both composites are the base-change map of the square
obtained by stacking, by `Stacks.Conormal.conormalBaseChangeMap_comp`, up to the unitors of the
pullback pseudofunctor. -/
theorem conormalBaseChangeMap_presentation {σ : X ⟶ projectiveBundle X E}
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X) {σ' : X' ⟶ projectiveBundle X' E'}
    (hσ' : σ' ≫ projectiveBundleToBase X' E' = 𝟙 X')
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X' E' σ' hσ'
    Stacks.Conormal.conormalBaseChangeMap
        (presentationSection_comp_bundleBaseChangeHom g E E' hE comm) ≫
      (Scheme.Modules.pullbackId X').inv.app _ ≫
        Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E' σ') =
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId X).inv.app _) ≫
      (Scheme.Modules.pullback g).map
        (Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E σ)) ≫
      Stacks.Conormal.conormalBaseChangeMap comm := by
  have := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
  have := isClosedImmersion_of_section_projectiveBundleToBase X' E' σ' hσ'
  exact Stacks.Conormal.conormalBaseChangeMap_comp_unit_square g (presentationSection_square E σ)
    (presentationSection_square E' σ') (presentationSection_comp_bundleBaseChangeHom g E E' hE comm)
    comm (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g E E' hE).symm

variable (Q : Stacks.Divisors.InvertibleQuotient X E)
  (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)

/-- The bookkeeping of `projectiveBundleConormalIso_baseChange`, in a bare category, where the
two `Category` instances on sheaves of modules do not get in the way of `rw`. -/
private theorem comp_eq_of_square {D : Type*} [Category D] {A A' B B' C C' T T' : D}
    (s : A ⟶ A') (m' : A' ⟶ B') (u' : B' ⟶ C') (v' : C' ⟶ T) (Gmuv : A ⟶ T')
    (Gm : A ⟶ B) (Gu : B ⟶ C) (Gv : C ⟶ T') (cb : B ⟶ B') (c : T' ⟶ T)
    (h1 : s ≫ m' = Gm ≫ cb) (h2 : cb ≫ u' ≫ v' = Gu ≫ Gv ≫ c)
    (hG : Gmuv = Gm ≫ Gu ≫ Gv) :
    s ≫ m' ≫ u' ≫ v' = Gmuv ≫ c := by
  rw [reassoc_of% h1, h2, hG]
  simp only [Category.assoc]

include hq in
/-- **The canonical conormal isomorphism is compatible with base change**, on `𝐏(ℰ)` itself:
for sections `σ`, `σ'` matched with `q`, `q'` and lying over each other along the base-change
morphism `projectiveBundleBaseChange`, the square formed by `g^*` of `projectiveBundleConormalIso`,
`projectiveBundleConormalIso`, the base change of the source
`Stacks.Divisors.conormalSourceBaseChange` and the base-change map of conormal sheaves
`Stacks.Conormal.conormalBaseChangeMap` commutes. -/
theorem projectiveBundleConormalIso_baseChange {σ : X ⟶ projectiveBundle X E}
    (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
    (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q)
    {σ' : X' ⟶ projectiveBundle X' E'} (hσ' : σ' ≫ projectiveBundleToBase X' E' = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalDatum E').twist ≅ Q'.L)
    (hqe' : (tautologicalDatum E').pullbackQuotientMap σ' hσ' ≫ e'.hom = Q'.q)
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
    haveI := isClosedImmersion_of_section_projectiveBundleToBase X' E' σ' hσ'
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (projectiveBundleConormalIso E' Q' hσ' e' hqe').hom =
      (Scheme.Modules.pullback g).map (projectiveBundleConormalIso E Q hσ e hqe).hom ≫
        Stacks.Conormal.conormalBaseChangeMap comm := by
  have := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
  have := isClosedImmersion_of_section_projectiveBundleToBase X' E' σ' hσ'
  have h1 := conormalCanonicalMap_baseChange g E E' hE Q Q' hL hq
    (presentationSection_comp_toBase E σ hσ) (presentationClassifyingIso E Q e)
    (sectionQuotientMap_comp_presentationClassifyingIso E Q hσ e hqe)
    (presentationSection_comp_toBase E' σ' hσ') (presentationClassifyingIso E' Q' e')
    (sectionQuotientMap_comp_presentationClassifyingIso E' Q' hσ' e' hqe')
    (presentationSection_comp_bundleBaseChangeHom g E E' hE comm)
  have h2 := conormalBaseChangeMap_presentation g E E' hE hσ hσ' comm
  rw [projectiveBundleConormalIso_hom, projectiveBundleConormalIso_hom]
  exact comp_eq_of_square (h1 := h1) (h2 := h2) (hG :=
    ((Scheme.Modules.pullback g).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((Scheme.Modules.pullback g).map_comp _ _)))

end BaseChange

section Classification

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- **[Stacks, Tag 0B3V].** Let `X` be a scheme, `ℰ` a quasi-coherent `𝒪_X`-module and
`π : 𝐏(ℰ) ⟶ X` its projective bundle (`projectiveBundle`, `projectiveBundleToBase`), with
tautological quotient `π^*ℰ ⟶ 𝒪(1)` (`tautologicalDatum ℰ`). Then:

1. **the bijection**: `projectiveBundleSectionsEquiv` is a bijection from the sections `σ` of `π`
   onto the invertible quotients `q : ℰ → 𝓛` up to isomorphism, sending `σ` to the class of
   `σ^*` of the tautological quotient — `σ` goes to the class of `q` exactly when there is
   `e : σ^*𝒪(1) ≅ 𝓛` carrying `σ^*` of the tautological quotient to `q`;
2. every section `σ` is a closed immersion;
3. **the canonical isomorphism** `projectiveBundleConormalIso : Ker(q) ⊗ 𝓛^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}`
   for `σ` matched with `q` through `e`, whose underlying map is the canonical map
   `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` (locally `k ⊗ s^{-1} ↦ k/s`) read
   through the base-change map of conormal sheaves along the presentation comparison
   `bundlePresentationIso` of `𝐏(ℰ)`;
4. **compatibility with base change** along any morphism `g : X' ⟶ X`, for sections lying over
   each other along `projectiveBundleBaseChange`: the bijection sends `σ'` to the base change
   `Stacks.ProjectiveBundleQuotients.baseChangeClass` of the class of `σ`; and the square formed
   by `g^*` of the canonical isomorphism at `σ`, the canonical isomorphism at `σ'`, the base
   change `Stacks.Divisors.conormalSourceBaseChange` of the source and the base-change map
   `Stacks.Conormal.conormalBaseChangeMap` of conormal sheaves commutes.

No hypothesis is placed on `X`, `X'`, `g`, or on `ℰ` beyond quasi-coherence. -/
@[stacks 0B3V,
  ega "II 4.2.10" "special case",
  ega "II 4.2.3" "Case Y = X",
  sga "4 XVIII 1.3.3" "partial"]
theorem projectiveBundle_sections_classification :
    (∀ (σ : X ⟶ projectiveBundle X E) (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
        (Q : Stacks.Divisors.InvertibleQuotient X E),
      projectiveBundleSectionsEquiv ⟨σ, hσ⟩ =
          Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid X E) Q ↔
        ∃ e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L,
          (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q) ∧
    (∀ (σ : X ⟶ projectiveBundle X E), σ ≫ projectiveBundleToBase X E = 𝟙 X →
      IsClosedImmersion σ) ∧
    (∀ (Q : Stacks.Divisors.InvertibleQuotient X E) (σ : X ⟶ projectiveBundle X E)
        (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
        (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
        (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q),
      haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
      (projectiveBundleConormalIso E Q hσ e hqe).hom =
        conormalCanonicalMap E Q (presentationSection_comp_toBase E σ hσ)
            (presentationClassifyingIso E Q e)
            (sectionQuotientMap_comp_presentationClassifyingIso E Q hσ e hqe) ≫
          (Scheme.Modules.pullbackId X).inv.app _ ≫
            Stacks.Conormal.conormalBaseChangeMap (presentationSection_square E σ)) ∧
    (∀ (X' : Scheme.{u}) (g : X' ⟶ X) (σ : X ⟶ projectiveBundle X E)
        (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
        (σ' : X' ⟶ projectiveBundle X' ((Scheme.Modules.pullback g).obj E))
        (hσ' : σ' ≫ projectiveBundleToBase X' ((Scheme.Modules.pullback g).obj E) = 𝟙 X'),
        σ' ≫ projectiveBundleBaseChange g E _ (Iso.refl _) = g ≫ σ →
      projectiveBundleSectionsEquiv ⟨σ', hσ'⟩ =
        Stacks.ProjectiveBundleQuotients.baseChangeClass g (Iso.refl _)
          (projectiveBundleSectionsEquiv ⟨σ, hσ⟩)) ∧
    (∀ (X' : Scheme.{u}) (g : X' ⟶ X) (E' : X'.Modules) [E'.IsQuasicoherent]
        (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
        (Q : Stacks.Divisors.InvertibleQuotient X E)
        (Q' : Stacks.Divisors.InvertibleQuotient X' E')
        (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
        (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)
        (σ : X ⟶ projectiveBundle X E) (hσ : σ ≫ projectiveBundleToBase X E = 𝟙 X)
        (e : (Scheme.Modules.pullback σ).obj (tautologicalDatum E).twist ≅ Q.L)
        (hqe : (tautologicalDatum E).pullbackQuotientMap σ hσ ≫ e.hom = Q.q)
        (σ' : X' ⟶ projectiveBundle X' E') (hσ' : σ' ≫ projectiveBundleToBase X' E' = 𝟙 X')
        (e' : (Scheme.Modules.pullback σ').obj (tautologicalDatum E').twist ≅ Q'.L)
        (hqe' : (tautologicalDatum E').pullbackQuotientMap σ' hσ' ≫ e'.hom = Q'.q)
        (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ),
      haveI := isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ
      haveI := isClosedImmersion_of_section_projectiveBundleToBase X' E' σ' hσ'
      (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
          (projectiveBundleConormalIso E' Q' hσ' e' hqe').hom =
        (Scheme.Modules.pullback g).map (projectiveBundleConormalIso E Q hσ e hqe).hom ≫
          Stacks.Conormal.conormalBaseChangeMap comm) :=
  ⟨fun σ hσ Q => projectiveBundleSectionsEquiv_eq_iff E σ hσ Q,
    fun σ hσ => isClosedImmersion_of_section_projectiveBundleToBase X E σ hσ,
    fun Q _ hσ e hqe => projectiveBundleConormalIso_hom E Q hσ e hqe,
    fun _ g σ hσ σ' hσ' comm => projectiveBundleSectionsEquiv_baseChange g E σ hσ σ' hσ' comm,
    fun _ g E' _ hE Q Q' hL hq _ hσ e hqe _ hσ' e' hqe' comm =>
      projectiveBundleConormalIso_baseChange g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm⟩

end Classification

end Stacks.RelativeProj

end
