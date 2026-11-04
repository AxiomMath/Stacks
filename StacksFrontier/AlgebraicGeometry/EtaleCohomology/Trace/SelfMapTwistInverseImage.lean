module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSetsVerticalPasting

/-!
# The self-map twist under inverse image along an equivariant morphism

Let `f : Y ⟶ S` be a morphism of schemes with an endomorphism `φ` of `Y` over `S`, and let
`g : U ⟶ Y` be a morphism with an endomorphism `φ_U` of `U` such that `φ_U ≫ g = g ≫ φ`. Put
`f_U = g ≫ f`. For a sheaf `M` of `Λ`-modules on `S_étale`, the inverse image along `g` of the
self-map twist `f^{-1} M ⟶ φ_* f^{-1} M` (`Stacks.EtaleCohomology.selfMapTwist`), followed by the
base change map `g^{-1} φ_* ⟶ φ_{U,*} g^{-1}`, is, through `g^{-1} f^{-1} ≅ f_U^{-1}`, the
self-map twist of `f_U^{-1} M` along `φ_U`.

Dually, for a composite `f_W = p ≫ m` and an endomorphism `φ_U` over `p`, the self-map twist of
`p^{-1}(m^{-1} M)` along `φ_U` is, through `p^{-1} m^{-1} ≅ f_W^{-1}`, the self-map twist of
`f_W^{-1} M`.  Both are proved by transposing along the inverse image adjunctions, from the unit
formulas `Stacks.EtaleCohomology.unit_comp_map_selfMapTwist`,
`Stacks.EtaleCohomology.unit_comp_map_selfMapRestriction` and
`Stacks.EtaleCohomology.unit_comp_map_etaleModuleBaseChange`.

## Main results

* `Stacks.EtaleCohomology.inverseImage_map_selfMapTwist_comp_baseChange`.
* `Stacks.EtaleCohomology.selfMapTwist_comp_selfMapRestrictionIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {U Y S : Scheme.{u}} (f : Y ⟶ S) (g : U ⟶ Y) (fU : U ⟶ S)
  (hU : fU = g ≫ f) (φ : Y ⟶ Y) (w : φ ≫ f = f) (φU : U ⟶ U) (wU : φU ≫ fU = fU)
  (hi : φU ≫ g = g ≫ φ)

/-- The direct-image transfer `g_* φ_{U,*} ⟶ φ_* g_*` is inverse to the comparison
`φ_* g_* ≅ (φ_U ≫ g)_* ≅ g_* φ_{U,*}`. -/
lemma directImageTwistTransfer_comp_comp (N : EtaleModules.{u, 0} Λ U) :
    (directImageTwistTransfer Λ g φU φ hi).app N ≫
        (etaleModuleDirectImageComp.{u, 0} Λ g φ (φU ≫ g) hi).hom.app N ≫
        (etaleModuleDirectImageComp.{u, 0} Λ φU g (φU ≫ g) rfl).inv.app N = 𝟙 _ := by
  simp [directImageTwistTransfer]

include hU in
/-- **The inverse image of the self-map twist along an equivariant morphism is the self-map
twist.** -/
theorem inverseImage_map_selfMapTwist_comp_baseChange (M : EtaleModules.{u, 0} Λ S) :
    (etaleModuleInverseImage.{u, 0} Λ g).map ((selfMapTwist.{u, 0} Λ f φ w).app M) ≫
        (etaleModuleBaseChange Λ φ φU g g hi).app ((etaleModuleInverseImage.{u, 0} Λ f).obj M) ≫
        (etaleModuleDirectImage.{u, 0} Λ φU).map
          ((selfMapRestrictionIso.{u, 0} Λ f g fU hU).hom.app M) =
      (selfMapRestrictionIso.{u, 0} Λ f g fU hU).hom.app M ≫
        (selfMapTwist.{u, 0} Λ fU φU wU).app M := by
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ g).homEquiv _ _).injective
  have hR := selfMapTwist_comp_map_selfMapRestriction Λ f g fU hU φ w φU wU hi M
  have hB := unit_comp_map_etaleModuleBaseChange Λ φ φU g g hi
    ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
  have hn := (etaleModuleDirectImageComp.{u, 0} Λ φU g (φU ≫ g) rfl).inv.naturality
    ((selfMapRestrictionIso.{u, 0} Λ f g fU hU).hom.app M)
  have hn' := (etaleModuleDirectImageComp.{u, 0} Λ g φ (φU ≫ g) hi).hom.naturality
    ((selfMapRestrictionIso.{u, 0} Λ f g fU hU).hom.app M)
  have hT := directImageTwistTransfer_comp_comp Λ g φ φU hi
    ((etaleModuleInverseImage.{u, 0} Λ fU).obj M)
  rw [selfMapRestriction_app] at hR
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn hn' hR hB ⊢
  simp only [Functor.map_comp, Category.assoc] at hR
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [(etaleModuleInverseImageAdj.{u, 0} Λ g).unit_naturality_assoc, reassoc_of% hB, ← hn,
    ← reassoc_of% hn', reassoc_of% hR]
  simp only [hT]
  exact whisker_eq _ (whisker_eq _ (Category.comp_id _))

/-! ### The self-map twist along a composite -/

section Composite

variable {V : Scheme.{u}} (p : U ⟶ V) (m : V ⟶ S) (fW : U ⟶ S) (hW : fW = p ≫ m)
  (wp : φU ≫ p = p) (wW : φU ≫ fW = fW)

/-- Inverting a commutative square of isomorphisms. -/
private lemma inv_comp_of_hom_comp {D : Type*} [Category D] {P Q R T : D} (e₁ : P ≅ Q)
    (e₂ : Q ≅ T) (e₃ : P ≅ R) (e₄ : R ≅ T) (h : e₁.hom ≫ e₂.hom = e₃.hom ≫ e₄.hom) :
    e₄.inv ≫ e₃.inv = e₂.inv ≫ e₁.inv := by
  rw [← Iso.trans_inv, ← Iso.trans_inv]
  exact congrArg Iso.inv (Iso.ext h).symm

include wp hW in
/-- The identifications `φ_{U,*} ⋙ p_* ≅ p_*` and `φ_{U,*} ⋙ f_{W,*} ≅ f_{W,*}` are compatible
with `p_* ⋙ m_* ≅ f_{W,*}`. -/
lemma selfMapDirectImageComp_inv_comp_directImageComp_inv (N : EtaleModules.{u, 0} Λ U) :
    (selfMapDirectImageComp.{u, 0} Λ fW φU wW).inv.app N ≫
        (etaleModuleDirectImageComp.{u, 0} Λ p m fW hW).inv.app
          ((etaleModuleDirectImage.{u, 0} Λ φU).obj N) =
      (etaleModuleDirectImageComp.{u, 0} Λ p m fW hW).inv.app N ≫
        (etaleModuleDirectImage.{u, 0} Λ m).map
          ((selfMapDirectImageComp.{u, 0} Λ p φU wp).inv.app N) := by
  have h := smallEtalePushforwardComp'_assoc_app φU p m p wp.symm fW hW fW hW wW.symm
    (ModuleCat.{u + 1} Λ) N
  exact inv_comp_of_hom_comp ((etaleModuleDirectImage.{u, 0} Λ m).mapIso
    ((selfMapDirectImageComp.{u, 0} Λ p φU wp).app N))
    ((etaleModuleDirectImageComp.{u, 0} Λ p m fW hW).app N)
    ((etaleModuleDirectImageComp.{u, 0} Λ p m fW hW).app _)
    ((selfMapDirectImageComp.{u, 0} Λ fW φU wW).app N) h

include hW in
/-- **The self-map twist along a composite.**  For `f_W = p ≫ m` and `φ_U` over `p`, the twist of
`p^{-1}(m^{-1} M)` along `φ_U` is, through `p^{-1} m^{-1} ≅ f_W^{-1}`, the twist of
`f_W^{-1} M`. -/
theorem selfMapTwist_comp_selfMapRestrictionIso (M : EtaleModules.{u, 0} Λ S) :
    (selfMapTwist.{u, 0} Λ p φU wp).app ((etaleModuleInverseImage.{u, 0} Λ m).obj M) ≫
        (etaleModuleDirectImage.{u, 0} Λ φU).map
          ((selfMapRestrictionIso.{u, 0} Λ m p fW hW).hom.app M) =
      (selfMapRestrictionIso.{u, 0} Λ m p fW hW).hom.app M ≫
        (selfMapTwist.{u, 0} Λ fW φU wW).app M := by
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ p).homEquiv _ _).injective
  have hA := unit_comp_map_selfMapTwist Λ p φU wp ((etaleModuleInverseImage.{u, 0} Λ m).obj M)
  have hn := (selfMapDirectImageComp.{u, 0} Λ p φU wp).inv.naturality
    ((selfMapRestrictionIso.{u, 0} Λ m p fW hW).hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hA hn
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% hA, ← hn]
  have hB : (selfMapRestriction.{u, 0} Λ m p fW hW).app M ≫
      (etaleModuleDirectImage.{u, 0} Λ p).map ((selfMapTwist.{u, 0} Λ fW φU wW).app M) =
      (selfMapRestriction.{u, 0} Λ m p fW hW).app M ≫
        (selfMapDirectImageComp.{u, 0} Λ p φU wp).inv.app
          ((etaleModuleInverseImage.{u, 0} Λ fW).obj M) := by
    apply ((etaleModuleInverseImageAdj.{u, 0} Λ m).homEquiv _ _).injective
    have hR := unit_comp_map_selfMapRestriction Λ m p fW hW M
    have hT := unit_comp_map_selfMapTwist Λ fW φU wW M
    have hc := (etaleModuleDirectImageComp.{u, 0} Λ p m fW hW).inv.naturality
      ((selfMapTwist.{u, 0} Λ fW φU wW).app M)
    have hK := selfMapDirectImageComp_inv_comp_directImageComp_inv Λ φU p m fW hW wp wW
      ((etaleModuleInverseImage.{u, 0} Λ fW).obj M)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hR hT hc hK ⊢
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [reassoc_of% hR, ← hc, reassoc_of% hT, hK, reassoc_of% hR]
  rw [selfMapRestriction_app] at hB
  simpa only [Category.assoc] using hB.symm

end Composite

end Stacks.EtaleCohomology

end
