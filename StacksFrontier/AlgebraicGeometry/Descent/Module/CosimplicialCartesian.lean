module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CartesianDegreeZero
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Cosimplicial
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic

/-!
# The category of cartesian cosimplicial modules, and base change between them

A cosimplicial module `M` over a cosimplicial commutative `R`-algebra `A` is cartesian when
every transition map `M_n ⟶ M_m` induces an isomorphism `M_n ⊗_{A_n, A(φ)} A_m ⟶ M_m`
(`CategoryTheory.CosimplicialModule.Cartesian`).  Read through the identification of cosimplicial
modules with presheaves of modules on `SimplexCategoryᵒᵖ`, this is the cartesian condition of
`Stacks.PresheafOfModules.cartesianModules`, so the cartesian cosimplicial `A`-modules form a full
subcategory, and the change-of-rings functor `M ↦ M ⊗_{A} B` of a morphism `A ⟶ B` of cosimplicial
`R`-algebras restricts to a functor between those subcategories.

## Main definitions

* `CategoryTheory.CosimplicialModule.CartesianCosimplicialModule`: the category of cartesian
  cosimplicial modules over a cosimplicial commutative algebra.
* `CategoryTheory.CosimplicialModule.ringPresheafMap`: the morphism of presheaves of commutative
  rings attached to a morphism of cosimplicial commutative algebras.
* `CategoryTheory.CosimplicialModule.cartesianBaseChange`: the functor `M ↦ M ⊗_{A} B` between the
  categories of cartesian cosimplicial modules.
* `CategoryTheory.CosimplicialModule.cartesianBaseChangeCompIso` and
  `CategoryTheory.CosimplicialModule.cartesianBaseChangeIdIso`: that functor is functorial in the
  morphism of cosimplicial algebras, up to isomorphism.

## Main results

* `CategoryTheory.CosimplicialModule.cartesian_iff`: the cartesian condition on a cosimplicial
  module is the cartesian condition on the corresponding presheaf of modules.
* `CategoryTheory.CosimplicialModule.homotopyBaseChangeIso`: a cosimplicial homotopy from `f` to
  `g` gives an isomorphism between base change along `f` and base change along `g`, and
  `CategoryTheory.CosimplicialModule.nonempty_iso_cartesianBaseChange_of_homotopic` extends this to
  homotopic morphisms.
* `CategoryTheory.CosimplicialModule.isEquivalence_cartesianBaseChange_of_homotopyEquivalence`:
  **Stacks 039Y (4)**, base change along a homotopy equivalence of cosimplicial `R`-algebras is an
  equivalence between the categories of cartesian modules.

## Implementation notes

A cosimplicial homotopy from `f` to `g` is a simplicial homotopy between the opposite morphisms;
in degree `n` it consists of ring maps `h_i : A_{n+1} ⟶ B_n`.  For a cartesian `A`-module `M` the
isomorphism `B ⊗_f M ≅ B ⊗_g M` is built in degree zero as
`B_0 ⊗_{f_0} M_0 ≅ B_0 ⊗_{h_0} M_1 ≅ B_0 ⊗_{g_0} M_0`, from the cartesian isomorphisms of `M`
along the two cofaces `⦋0⦌ ⟶ ⦋1⦌` (`Stacks.PresheafOfModules.transport`), and is extended to all
degrees by `Stacks.PresheafOfModules.homOfDegreeZero`, which asks for the compatibility in degree
one only.  That compatibility, checked by the transport identities over `⦋2⦌`
(`Stacks.PresheafOfModules.homotopyTransport_one` and
`Stacks.PresheafOfModules.homotopyTransport_zero`), is all that the source's "triviality" needs.

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory Opposite Stacks.PresheafOfModules Simplicial

universe u v w r m


namespace Stacks.PresheafOfModules

open Simplicial

section HomotopyTransport

/-! ### The two-dimensional identities behind homotopy invariance

Let `M` be a cartesian module over a cosimplicial ring `R`.  The transport maps of `M` between
degrees `0`, `1` and `2` satisfy the identities below; they are what makes a cosimplicial homotopy
induce a morphism of base changes (`CategoryTheory.CosimplicialModule.homotopyBaseChangeIso`).
The ring maps out of `R_2`, `R_1` and `R_0` are arbitrary, subject to the displayed relations,
which a cosimplicial homotopy provides. -/

variable {R : SimplexCategoryᵒᵖᵒᵖ ⥤ CommRingCat.{r}}
  {M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
  {T : Type r} [CommRing T]

/-- The coface `δ i : ⦋0⦌ ⟶ ⦋1⦌`, as a morphism of the indexing category. -/
abbrev cof₀ (i : Fin 2) : op (op ⦋0⦌) ⟶ (op (op ⦋1⦌) : SimplexCategoryᵒᵖᵒᵖ) :=
  (SimplexCategory.δ (n := 0) i).op.op

/-- The coface `δ i : ⦋1⦌ ⟶ ⦋2⦌`, as a morphism of the indexing category. -/
abbrev cof₁ (i : Fin 3) : op (op ⦋1⦌) ⟶ (op (op ⦋2⦌) : SimplexCategoryᵒᵖᵒᵖ) :=
  (SimplexCategory.δ (n := 1) i).op.op

/-- The vertex `i` of `⦋2⦌`, as a morphism of the indexing category. -/
abbrev vert₂ (i : Fin 3) : op (op ⦋0⦌) ⟶ (op (op ⦋2⦌) : SimplexCategoryᵒᵖᵒᵖ) :=
  (SimplexCategory.const ⦋0⦌ ⦋2⦌ i).op.op

/-- The composite of the cofaces `δ i : ⦋0⦌ ⟶ ⦋1⦌` and `δ j : ⦋1⦌ ⟶ ⦋2⦌` is the vertex `k` of
`⦋2⦌`, where `k` is the image of `0`. -/
theorem cof₀_comp_cof₁ (i : Fin 2) (j : Fin 3) (k : Fin 3)
    (h : (SimplexCategory.δ j).toOrderHom ((SimplexCategory.δ i).toOrderHom 0) = k) :
    cof₀ i ≫ cof₁ j = vert₂ k :=
  congrArg (fun φ : ⦋0⦌ ⟶ ⦋2⦌ => φ.op.op)
    (SimplexCategory.Hom.ext_zero_left (SimplexCategory.δ i ≫ SimplexCategory.δ j) _ h)

variable [IsIso (restrictionBaseChange M (cof₀ 0))] [IsIso (restrictionBaseChange M (cof₀ 1))]
  [IsIso (restrictionBaseChange M (cof₁ 0))] [IsIso (restrictionBaseChange M (cof₁ 1))]
  [IsIso (restrictionBaseChange M (cof₁ 2))] [IsIso (restrictionBaseChange M (vert₂ 0))]
  [IsIso (restrictionBaseChange M (vert₂ 1))] [IsIso (restrictionBaseChange M (vert₂ 2))]

omit [IsIso (restrictionBaseChange M (cof₀ 1))] [IsIso (restrictionBaseChange M (cof₁ 2))]
  [IsIso (restrictionBaseChange M (vert₂ 0))] [IsIso (restrictionBaseChange M (vert₂ 1))]
  [IsIso (restrictionBaseChange M (vert₂ 2))] in
/-- The degree-one component of the base-change morphism of a homotopy, at the coface `δ 1`. -/
theorem homotopyTransport_one (H₀ H₁ : R.obj (op (op ⦋2⦌)) →+* T)
    (f₁ g₁ s c : R.obj (op (op ⦋1⦌)) →+* T) (sf sg : R.obj (op (op ⦋0⦌)) →+* T)
    (hf₁ : f₁ = H₁.comp (R.map (cof₁ 2)).hom) (hg₁ : g₁ = H₀.comp (R.map (cof₁ 0)).hom)
    (hc₀ : c = H₀.comp (R.map (cof₁ 1)).hom) (hc₁ : c = H₁.comp (R.map (cof₁ 1)).hom)
    (hs : s = H₀.comp (R.map (cof₁ 2)).hom)
    (hsf : sf = s.comp (R.map (cof₀ 1)).hom) (hsf' : sf = f₁.comp (R.map (cof₀ 1)).hom)
    (hsg : sg = s.comp (R.map (cof₀ 0)).hom) (hsg' : sg = g₁.comp (R.map (cof₀ 1)).hom) :
    transport M (cof₀ 1) f₁ sf hsf' ≫ (transport M (cof₁ 2) H₁ f₁ hf₁ ≫
        inv (transport M (cof₁ 1) H₁ c hc₁) ≫ transport M (cof₁ 1) H₀ c hc₀ ≫
          inv (transport M (cof₁ 0) H₀ g₁ hg₁)) =
      transport M (cof₀ 1) s sf hsf ≫ inv (transport M (cof₀ 0) s sg hsg) ≫
        transport M (cof₀ 1) g₁ sg hsg' := by
  have hw : sf = H₀.comp (R.map (vert₂ 0)).hom := by
    rw [hsf, hs, ringHom_comp_map_comp, cof₀_comp_cof₁ 1 2 0 rfl]
  have hw' : sf = H₁.comp (R.map (vert₂ 0)).hom := by
    rw [hsf', hf₁, ringHom_comp_map_comp, cof₀_comp_cof₁ 1 2 0 rfl]
  have hv : sg = H₀.comp (R.map (vert₂ 1)).hom := by
    rw [hsg', hg₁, ringHom_comp_map_comp, cof₀_comp_cof₁ 1 0 1 rfl]
  rw [← cancel_mono (transport M (cof₁ 0) H₀ g₁ hg₁)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [transport_comp_of_eq M (cof₀ 1) (cof₁ 0) (vert₂ 1) (cof₀_comp_cof₁ 1 0 1 rfl) H₀ g₁ sg
      hg₁ hsg' hv,
    inv_transport_comp_transport M (cof₀ 0) (cof₁ 2) (vert₂ 1) (cof₀_comp_cof₁ 0 2 1 rfl) H₀ s
      sg hs hsg hv,
    transport_comp_of_eq M (cof₀ 1) (cof₁ 2) (vert₂ 0) (cof₀_comp_cof₁ 1 2 0 rfl) H₀ s sf
      hs hsf hw,
    ← Category.assoc, transport_comp_of_eq M (cof₀ 1) (cof₁ 2) (vert₂ 0)
      (cof₀_comp_cof₁ 1 2 0 rfl) H₁ f₁ sf hf₁ hsf' hw',
    ← Category.assoc, ← transport_eq_comp_inv M (cof₀ 1) (cof₁ 1) (vert₂ 0)
      (cof₀_comp_cof₁ 1 1 0 rfl) H₁ c sf hc₁ (by rw [hc₁, ringHom_comp_map_comp,
        cof₀_comp_cof₁ 1 1 0 rfl, ← hw']) hw',
    transport_comp_of_eq M (cof₀ 1) (cof₁ 1) (vert₂ 0) (cof₀_comp_cof₁ 1 1 0 rfl) H₀ c sf
      hc₀ _ hw]

omit [IsIso (restrictionBaseChange M (cof₀ 1))] [IsIso (restrictionBaseChange M (cof₁ 2))]
  [IsIso (restrictionBaseChange M (vert₂ 0))] [IsIso (restrictionBaseChange M (vert₂ 1))] in
/-- The degree-one component of the base-change morphism of a homotopy, at the coface `δ 0`. -/
theorem homotopyTransport_zero (H₀ H₁ : R.obj (op (op ⦋2⦌)) →+* T)
    (f₁ g₁ s c : R.obj (op (op ⦋1⦌)) →+* T) (sf sg : R.obj (op (op ⦋0⦌)) →+* T)
    (hf₁ : f₁ = H₁.comp (R.map (cof₁ 2)).hom) (hg₁ : g₁ = H₀.comp (R.map (cof₁ 0)).hom)
    (hc₀ : c = H₀.comp (R.map (cof₁ 1)).hom) (hc₁ : c = H₁.comp (R.map (cof₁ 1)).hom)
    (hs : s = H₁.comp (R.map (cof₁ 0)).hom)
    (hsf : sf = s.comp (R.map (cof₀ 1)).hom) (hsf' : sf = f₁.comp (R.map (cof₀ 0)).hom)
    (hsg : sg = s.comp (R.map (cof₀ 0)).hom) (hsg' : sg = g₁.comp (R.map (cof₀ 0)).hom) :
    transport M (cof₀ 0) f₁ sf hsf' ≫ (transport M (cof₁ 2) H₁ f₁ hf₁ ≫
        inv (transport M (cof₁ 1) H₁ c hc₁) ≫ transport M (cof₁ 1) H₀ c hc₀ ≫
          inv (transport M (cof₁ 0) H₀ g₁ hg₁)) =
      transport M (cof₀ 1) s sf hsf ≫ inv (transport M (cof₀ 0) s sg hsg) ≫
        transport M (cof₀ 0) g₁ sg hsg' := by
  have hv₁ : sf = H₁.comp (R.map (vert₂ 1)).hom := by
    rw [hsf', hf₁, ringHom_comp_map_comp, cof₀_comp_cof₁ 0 2 1 rfl]
  have hv₂ : sg = H₁.comp (R.map (vert₂ 2)).hom := by
    rw [hsg, hs, ringHom_comp_map_comp, cof₀_comp_cof₁ 0 0 2 rfl]
  have hv₂' : sg = H₀.comp (R.map (vert₂ 2)).hom := by
    rw [hsg', hg₁, ringHom_comp_map_comp, cof₀_comp_cof₁ 0 0 2 rfl]
  have hcs : sg = c.comp (R.map (cof₀ 0)).hom := by
    rw [hc₁, ringHom_comp_map_comp, cof₀_comp_cof₁ 0 1 2 rfl, ← hv₂]
  rw [← cancel_mono (transport M (cof₁ 0) H₀ g₁ hg₁)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [transport_comp_of_eq M (cof₀ 0) (cof₁ 0) (vert₂ 2) (cof₀_comp_cof₁ 0 0 2 rfl) H₀ g₁ sg
      hg₁ hsg' hv₂',
    inv_transport_eq_comp_inv M (cof₀ 0) (cof₁ 0) (vert₂ 2) (cof₀_comp_cof₁ 0 0 2 rfl) H₁ s sg
      hs hsg hv₂,
    transport_eq_comp_inv M (cof₀ 1) (cof₁ 0) (vert₂ 1) (cof₀_comp_cof₁ 1 0 1 rfl) H₁ s sf
      hs hsf hv₁,
    ← Category.assoc, transport_comp_of_eq M (cof₀ 0) (cof₁ 2) (vert₂ 1)
      (cof₀_comp_cof₁ 0 2 1 rfl) H₁ f₁ sf hf₁ hsf' hv₁,
    inv_transport_eq_of_comp M (cof₀ 0) (cof₁ 1) (vert₂ 2) (cof₀_comp_cof₁ 0 1 2 rfl) H₁ c sg
      hc₁ hcs hv₂]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [transport_comp_of_eq M (cof₀ 0) (cof₁ 1) (vert₂ 2) (cof₀_comp_cof₁ 0 1 2 rfl) H₀ c sg
      hc₀ hcs hv₂']

end HomotopyTransport

end Stacks.PresheafOfModules

namespace CategoryTheory.CosimplicialModule

variable {R : Type u} [CommRing R] {A B : CosimplicialObject (CommAlgCat.{v, u} R)}

/-- A cosimplicial module is cartesian exactly when it is cartesian as a presheaf of modules on
`SimplexCategoryᵒᵖ`: the base-change map of a cosimplicial transition map is the base-change
comparison of the corresponding restriction map. -/
theorem cartesian_iff (M : CosimplicialModule.{u, v, max w v} A) :
    M.Cartesian ↔ cartesianModules (cosimplicialRingPresheaf A) M :=
  ⟨fun h _ _ g => h g.unop.unop, fun h _ _ g => h g.op.op⟩

/-- The category of cartesian cosimplicial modules over a cosimplicial commutative algebra: the
full subcategory of the cosimplicial `A`-modules on those that are cartesian. -/
abbrev CartesianCosimplicialModule (A : CosimplicialObject (CommAlgCat.{v, u} R)) :=
  (cartesianModules.{0, 0, v, max w v} (cosimplicialRingPresheaf A)).FullSubcategory

/-- The morphism of presheaves of commutative rings on `SimplexCategoryᵒᵖ` attached to a morphism
of cosimplicial commutative `R`-algebras. -/
def ringPresheafMap (α : A ⟶ B) : cosimplicialRingPresheaf A ⟶ cosimplicialRingPresheaf B :=
  Functor.whiskerLeft (unopUnop SimplexCategory)
    (Functor.whiskerRight α (forget₂ (CommAlgCat R) CommRingCat))

/-- **The base-change functor `M ↦ M ⊗_{A} B` on cartesian cosimplicial modules**, attached to a
morphism `A ⟶ B` of cosimplicial commutative `R`-algebras.  This is the functor of
Stacks 039Y (4). -/
noncomputable def cartesianBaseChange (α : A ⟶ B) :
    CartesianCosimplicialModule.{u, v, w} A ⥤ CartesianCosimplicialModule.{u, v, w} B :=
  Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRings (ringPresheafMap α)

/-- Base change on cartesian cosimplicial modules is functorial in the morphism of cosimplicial
algebras, up to isomorphism: `M ⊗_A D` is `(M ⊗_A B) ⊗_B D`. -/
noncomputable def cartesianBaseChangeCompIso {D : CosimplicialObject (CommAlgCat.{v, u} R)}
    (α : A ⟶ B) (α' : B ⟶ D) :
    cartesianBaseChange.{u, v, w} α ⋙ cartesianBaseChange.{u, v, w} α' ≅
      cartesianBaseChange.{u, v, w} (α ≫ α') :=
  Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRingsCompIso
    (ringPresheafMap α) (ringPresheafMap α')

/-- Base change along the identity of a cosimplicial algebra is the identity, up to
isomorphism. -/
noncomputable def cartesianBaseChangeIdIso (A : CosimplicialObject (CommAlgCat.{v, u} R)) :
    cartesianBaseChange.{u, v, w} (𝟙 A) ≅
      Functor.id (CartesianCosimplicialModule.{u, v, w} A) :=
  Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRingsIdIso (cosimplicialRingPresheaf A)

section HomotopyInvariance

open Stacks.PresheafOfModules.ChangeOfRings

variable {f g : A ⟶ B} (H : SimplicialObject.Homotopy (NatTrans.op f) (NatTrans.op g))

/-- The ring maps `A_{n+1} ⟶ B_n` of a cosimplicial homotopy, read as the components of the
simplicial homotopy between the opposite morphisms. -/
abbrev homotopyRingMap (n : ℕ) (i : Fin (n + 1)) :
    (cosimplicialRingPresheaf A).obj (op (op ⦋n + 1⦌)) →+*
      (cosimplicialRingPresheaf B).obj (op (op ⦋n⦌)) :=
  ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map (H.h i).unop).hom

/-- The ring map `A_n ⟶ B_n` of a morphism of cosimplicial algebras. -/
abbrev componentRingMap (α : A ⟶ B) (n : SimplexCategory) :
    (cosimplicialRingPresheaf A).obj (op (op n)) →+*
      (cosimplicialRingPresheaf B).obj (op (op n)) :=
  ((ringPresheafMap α).app (op (op n))).hom

/-- Naturality of the ring maps `A_n ⟶ B_n` of a morphism of cosimplicial algebras with respect
to the transition maps. -/
theorem componentRingMap_naturality (α : A ⟶ B) {X Y : SimplexCategoryᵒᵖᵒᵖ} (φ : X ⟶ Y) :
    ((cosimplicialRingPresheaf B).map φ).hom.comp ((ringPresheafMap α).app X).hom =
      ((ringPresheafMap α).app Y).hom.comp ((cosimplicialRingPresheaf A).map φ).hom :=
  (congrArg CommRingCat.Hom.hom ((ringPresheafMap α).naturality φ)).symm

/-- The degree-zero component of `f` is the homotopy map `h_0 : A_1 ⟶ B_0` composed with the
coface `δ 1`. -/
theorem homotopyRingMap_zero_cof_one :
    componentRingMap f ⦋0⦌ =
      (homotopyRingMap H 0 0).comp ((cosimplicialRingPresheaf A).map (cof₀ 1)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_last_comp_δ_last 0)).symm

/-- The degree-zero component of `g` is the homotopy map `h_0 : A_1 ⟶ B_0` composed with the
coface `δ 0`. -/
theorem homotopyRingMap_zero_cof_zero :
    componentRingMap g ⦋0⦌ =
      (homotopyRingMap H 0 0).comp ((cosimplicialRingPresheaf A).map (cof₀ 0)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_zero_comp_δ_zero 0)).symm

/-- The degree-one component of `f` is the homotopy map `h_1 : A_2 ⟶ B_1` composed with the
coface `δ 2`. -/
theorem homotopyRingMap_one_cof_two :
    componentRingMap f ⦋1⦌ =
      (homotopyRingMap H 1 1).comp ((cosimplicialRingPresheaf A).map (cof₁ 2)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_last_comp_δ_last 1)).symm

/-- The degree-one component of `g` is the homotopy map `h_0 : A_2 ⟶ B_1` composed with the
coface `δ 0`. -/
theorem homotopyRingMap_zero_cof₁_zero :
    componentRingMap g ⦋1⦌ =
      (homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 0)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_zero_comp_δ_zero 1)).symm

/-- The two homotopy maps `h_0, h_1 : A_2 ⟶ B_1` agree after composition with the coface
`δ 1 : A_1 ⟶ A_2`. -/
theorem homotopyRingMap_cof₁_one :
    (homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom =
      (homotopyRingMap H 1 1).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_succ_comp_δ_castSucc_succ (n := 0) 0)).symm

/-- The homotopy map `h_0 : A_1 ⟶ B_0` followed by the coface `δ 0` of `B` is the homotopy map
`h_1 : A_2 ⟶ B_1` composed with the coface `δ 0` of `A`. -/
theorem homotopyRingMap_face_zero :
    ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (homotopyRingMap H 0 0) =
      (homotopyRingMap H 1 1).comp ((cosimplicialRingPresheaf A).map (cof₁ 0)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_succ_comp_δ_castSucc_of_lt (n := 0) 0 0 le_rfl)).symm

/-- The homotopy map `h_0 : A_1 ⟶ B_0` followed by the coface `δ 1` of `B` is the homotopy map
`h_0 : A_2 ⟶ B_1` composed with the coface `δ 2` of `A`. -/
theorem homotopyRingMap_face_one :
    ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (homotopyRingMap H 0 0) =
      (homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 2)).hom :=
  (congrArg (fun φ => ((forget₂ (CommAlgCat.{v, u} R) CommRingCat).map φ.unop).hom)
    (H.h_castSucc_comp_δ_succ_of_lt (n := 0) 1 0 (by decide))).symm


variable (M : PresheafOfModules.{max w v} (ringPresheaf (cosimplicialRingPresheaf A)))
  (hM : cartesianModules (cosimplicialRingPresheaf A) M)

include hM in
/-- The degree-zero component `B_0 ⊗_{f_0} M_0 ⟶ B_0 ⊗_{g_0} M_0` of the isomorphism of base
changes defined by a cosimplicial homotopy `h` from `f` to `g`: with `h_0 : A_1 ⟶ B_0` the
homotopy in degree `0`, so that `f_0 = h_0 ∘ δ¹` and `g_0 = h_0 ∘ δ⁰`, it is
`B_0 ⊗_{f_0} M_0 ≅ B_0 ⊗_{h_0} M_1 ≅ B_0 ⊗_{g_0} M_0`, both steps being transport maps. -/
noncomputable def homotopyBaseChangeZero :
    (ModuleCat.extendScalars (componentRingMap f ⦋0⦌)).obj (M.obj (op (op ⦋0⦌))) ⟶
      (ModuleCat.extendScalars (componentRingMap g ⦋0⦌)).obj (M.obj (op (op ⦋0⦌))) :=
  haveI := hM (cof₀ 0)
  transport M (cof₀ 1) (homotopyRingMap H 0 0) (componentRingMap f ⦋0⦌)
      (homotopyRingMap_zero_cof_one H) ≫
    inv (transport M (cof₀ 0) (homotopyRingMap H 0 0) (componentRingMap g ⦋0⦌)
      (homotopyRingMap_zero_cof_zero H))

/-- The degree-zero component of the morphism of base changes of a homotopy is an isomorphism. -/
instance : IsIso (homotopyBaseChangeZero H M hM) := by
  have := hM (cof₀ 0); have := hM (cof₀ 1)
  unfold homotopyBaseChangeZero
  infer_instance

include hM in
/-- The degree-one component of the base-change isomorphism of a homotopy: the two homotopy maps
`A_2 ⟶ B_1` connect `f_1` and `g_1` in two steps of transport maps. -/
noncomputable def homotopyBaseChangeOne :
    (ModuleCat.extendScalars (componentRingMap f ⦋1⦌)).obj (M.obj (op (op ⦋1⦌))) ⟶
      (ModuleCat.extendScalars (componentRingMap g ⦋1⦌)).obj (M.obj (op (op ⦋1⦌))) :=
  haveI := hM (cof₁ 0); haveI := hM (cof₁ 1)
  transport M (cof₁ 2) (homotopyRingMap H 1 1) (componentRingMap f ⦋1⦌)
      (homotopyRingMap_one_cof_two H) ≫
    inv (transport M (cof₁ 1) (homotopyRingMap H 1 1)
      ((homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom)
      (homotopyRingMap_cof₁_one H)) ≫
    transport M (cof₁ 1) (homotopyRingMap H 1 0)
      ((homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom) rfl ≫
    inv (transport M (cof₁ 0) (homotopyRingMap H 1 0) (componentRingMap g ⦋1⦌)
      (homotopyRingMap_zero_cof₁_zero H))

/-- The compatibility of `homotopyBaseChangeZero` and `homotopyBaseChangeOne` with a coface
`δ i : ⦋0⦌ ⟶ ⦋1⦌`, reduced to the identity `key` between transport maps. -/
private theorem homotopyBaseChange_cof_aux_of (i : Fin 2)
    [IsIso (restrictionBaseChange M (cof₀ 0))] [IsIso (restrictionBaseChange M (cof₀ 1))]
    (key : transport M (cof₀ i) (componentRingMap f ⦋1⦌)
        (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap f ⦋0⦌))
        (componentRingMap_naturality f _) ≫ homotopyBaseChangeOne H M hM =
      transport M (cof₀ 1) (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp
          (homotopyRingMap H 0 0))
        (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap f ⦋0⦌))
        (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_one H)) ≫
      inv (transport M (cof₀ 0) (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp
          (homotopyRingMap H 0 0))
        (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap g ⦋0⦌))
        (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_zero H))) ≫
        transport M (cof₀ i) (componentRingMap g ⦋1⦌)
          (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap g ⦋0⦌))
          (componentRingMap_naturality g _)) :
    (ModuleCat.extendScalarsSemilinear (componentRingMap f ⦋0⦌)
        ((cosimplicialRingPresheaf B).map (cof₀ i)).hom
        (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap f ⦋0⦌)) rfl
          (M.obj (op (op ⦋0⦌))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ i)).hom).map
          (transport M (cof₀ i) (componentRingMap f ⦋1⦌) _
            (componentRingMap_naturality f (cof₀ i)))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ i)).hom).map
          (homotopyBaseChangeOne H M hM) =
      homotopyBaseChangeZero H M hM ≫
        (ModuleCat.extendScalarsSemilinear (componentRingMap g ⦋0⦌)
          ((cosimplicialRingPresheaf B).map (cof₀ i)).hom
          (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (componentRingMap g ⦋0⦌)) rfl
            (M.obj (op (op ⦋0⦌))) ≫
          (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ i)).hom).map
            (transport M (cof₀ i) (componentRingMap g ⦋1⦌) _
              (componentRingMap_naturality g (cof₀ i)))) := by
  rw [homotopyBaseChangeZero, Category.assoc, Category.assoc,
    inv_transport_comp_extendScalarsSemilinear_assoc M (cof₀ 0)
      ((cosimplicialRingPresheaf B).map (cof₀ i)).hom (homotopyRingMap H 0 0)
      (componentRingMap g ⦋0⦌) (homotopyRingMap_zero_cof_zero H)
      (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (homotopyRingMap H 0 0)) rfl _ rfl
      (congrArg (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp ·)
        (homotopyRingMap_zero_cof_zero H)),
    transport_comp_extendScalarsSemilinear_assoc M (cof₀ 1)
      ((cosimplicialRingPresheaf B).map (cof₀ i)).hom (homotopyRingMap H 0 0)
      (componentRingMap f ⦋0⦌) (homotopyRingMap_zero_cof_one H)
      (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp (homotopyRingMap H 0 0)) rfl _ rfl
      (congrArg (((cosimplicialRingPresheaf B).map (cof₀ i)).hom.comp ·)
        (homotopyRingMap_zero_cof_one H)),
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun φ => ModuleCat.extendScalarsSemilinear (componentRingMap f ⦋0⦌)
      ((cosimplicialRingPresheaf B).map (cof₀ i)).hom _ rfl (M.obj (op (op ⦋0⦌))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ i)).hom).map φ) key

include hM in
/-- The compatibility of `homotopyBaseChangeZero` and `homotopyBaseChangeOne` with the coface
`δ 1 : ⦋0⦌ ⟶ ⦋1⦌`, with the transition maps of the base changes written out as extension of
scalars followed by transport. -/
theorem homotopyBaseChange_cof_1_aux :
    (ModuleCat.extendScalarsSemilinear (componentRingMap f ⦋0⦌)
        ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom
        (((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (componentRingMap f ⦋0⦌)) rfl
          (M.obj (op (op ⦋0⦌))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom).map
          (transport M (cof₀ 1) (componentRingMap f ⦋1⦌) _
            (componentRingMap_naturality f (cof₀ 1)))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom).map
          (homotopyBaseChangeOne H M hM) =
      homotopyBaseChangeZero H M hM ≫
        (ModuleCat.extendScalarsSemilinear (componentRingMap g ⦋0⦌)
          ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom
          (((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (componentRingMap g ⦋0⦌)) rfl
            (M.obj (op (op ⦋0⦌))) ≫
          (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom).map
            (transport M (cof₀ 1) (componentRingMap g ⦋1⦌) _
              (componentRingMap_naturality g (cof₀ 1)))) := by
  have := hM (cof₀ 0); have := hM (cof₀ 1); have := hM (cof₁ 0); have := hM (cof₁ 1)
  have := hM (cof₁ 2); have := hM (vert₂ 0); have := hM (vert₂ 1); have := hM (vert₂ 2)
  refine homotopyBaseChange_cof_aux_of H M hM 1 ?_
  rw [homotopyBaseChangeOne]
  exact homotopyTransport_one (homotopyRingMap H 1 0) (homotopyRingMap H 1 1)
    (componentRingMap f ⦋1⦌)
    (componentRingMap g ⦋1⦌)
    (((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (homotopyRingMap H 0 0))
    ((homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom)
    (((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (componentRingMap f ⦋0⦌))
    (((cosimplicialRingPresheaf B).map (cof₀ 1)).hom.comp (componentRingMap g ⦋0⦌))
    (homotopyRingMap_one_cof_two H) (homotopyRingMap_zero_cof₁_zero H) rfl
    (homotopyRingMap_cof₁_one H) (homotopyRingMap_face_one H)
    (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_one H)) (componentRingMap_naturality f _)
    (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_zero H)) (componentRingMap_naturality g _)

include hM in
/-- The components `homotopyBaseChangeZero` and `homotopyBaseChangeOne` commute with the
transition maps of the base changes along the coface `δ 1 : ⦋0⦌ ⟶ ⦋1⦌`. -/
theorem homotopyBaseChange_cof_1 :
    ((changeOfRings (ringPresheafMap f)).obj M).map (cof₀ 1) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 1)).hom).map
          (homotopyBaseChangeOne H M hM) =
      homotopyBaseChangeZero H M hM ≫ ((changeOfRings (ringPresheafMap g)).obj M).map (cof₀ 1) := by
  rw [changeOfRings_map_eq (ringPresheafMap f) M (cof₀ 1) (componentRingMap_naturality f _),
    changeOfRings_map_eq (ringPresheafMap g) M (cof₀ 1) (componentRingMap_naturality g _)]
  exact homotopyBaseChange_cof_1_aux H M hM

include hM in
/-- The compatibility of `homotopyBaseChangeZero` and `homotopyBaseChangeOne` with the coface
`δ 0 : ⦋0⦌ ⟶ ⦋1⦌`, with the transition maps of the base changes written out as extension of
scalars followed by transport. -/
theorem homotopyBaseChange_cof_0_aux :
    (ModuleCat.extendScalarsSemilinear (componentRingMap f ⦋0⦌)
        ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom
        (((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (componentRingMap f ⦋0⦌)) rfl
          (M.obj (op (op ⦋0⦌))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom).map
          (transport M (cof₀ 0) (componentRingMap f ⦋1⦌) _
            (componentRingMap_naturality f (cof₀ 0)))) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom).map
          (homotopyBaseChangeOne H M hM) =
      homotopyBaseChangeZero H M hM ≫
        (ModuleCat.extendScalarsSemilinear (componentRingMap g ⦋0⦌)
          ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom
          (((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (componentRingMap g ⦋0⦌)) rfl
            (M.obj (op (op ⦋0⦌))) ≫
          (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom).map
            (transport M (cof₀ 0) (componentRingMap g ⦋1⦌) _
              (componentRingMap_naturality g (cof₀ 0)))) := by
  have := hM (cof₀ 0); have := hM (cof₀ 1); have := hM (cof₁ 0); have := hM (cof₁ 1)
  have := hM (cof₁ 2); have := hM (vert₂ 0); have := hM (vert₂ 1); have := hM (vert₂ 2)
  refine homotopyBaseChange_cof_aux_of H M hM 0 ?_
  rw [homotopyBaseChangeOne]
  exact homotopyTransport_zero (homotopyRingMap H 1 0) (homotopyRingMap H 1 1)
    (componentRingMap f ⦋1⦌)
    (componentRingMap g ⦋1⦌)
    (((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (homotopyRingMap H 0 0))
    ((homotopyRingMap H 1 0).comp ((cosimplicialRingPresheaf A).map (cof₁ 1)).hom)
    (((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (componentRingMap f ⦋0⦌))
    (((cosimplicialRingPresheaf B).map (cof₀ 0)).hom.comp (componentRingMap g ⦋0⦌))
    (homotopyRingMap_one_cof_two H) (homotopyRingMap_zero_cof₁_zero H) rfl
    (homotopyRingMap_cof₁_one H) (homotopyRingMap_face_zero H)
    (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_one H)) (componentRingMap_naturality f _)
    (congrArg (RingHom.comp _) (homotopyRingMap_zero_cof_zero H)) (componentRingMap_naturality g _)

include hM in
/-- The components `homotopyBaseChangeZero` and `homotopyBaseChangeOne` commute with the
transition maps of the base changes along the coface `δ 0 : ⦋0⦌ ⟶ ⦋1⦌`. -/
theorem homotopyBaseChange_cof_0 :
    ((changeOfRings (ringPresheafMap f)).obj M).map (cof₀ 0) ≫
        (ModuleCat.restrictScalars ((cosimplicialRingPresheaf B).map (cof₀ 0)).hom).map
          (homotopyBaseChangeOne H M hM) =
      homotopyBaseChangeZero H M hM ≫ ((changeOfRings (ringPresheafMap g)).obj M).map (cof₀ 0) := by
  rw [changeOfRings_map_eq (ringPresheafMap f) M (cof₀ 0) (componentRingMap_naturality f _),
    changeOfRings_map_eq (ringPresheafMap g) M (cof₀ 0) (componentRingMap_naturality g _)]
  exact homotopyBaseChange_cof_0_aux H M hM


/-- **The morphism of base changes defined by a cosimplicial homotopy.**  It is the morphism of
cartesian `B`-modules `B ⊗_f M ⟶ B ⊗_g M` determined in degree zero by
`CategoryTheory.CosimplicialModule.homotopyBaseChangeZero`. -/
noncomputable def homotopyBaseChangeHom :
    (changeOfRings (ringPresheafMap f)).obj M ⟶ (changeOfRings (ringPresheafMap g)).obj M :=
  homOfDegreeZero (cartesianModules_changeOfRings (ringPresheafMap f) M hM)
    (homotopyBaseChangeZero H M hM) (homotopyBaseChangeOne H M hM)
    (fun x => ConcreteCategory.congr_hom (homotopyBaseChange_cof_1 H M hM) x)
    (fun x => ConcreteCategory.congr_hom (homotopyBaseChange_cof_0 H M hM) x)

/-- The degree-zero component of `homotopyBaseChangeHom` is `homotopyBaseChangeZero`. -/
theorem homotopyBaseChangeHom_app_zero :
    (homotopyBaseChangeHom H M hM).app (op (op ⦋0⦌)) = homotopyBaseChangeZero H M hM :=
  homOfDegreeZero_app_zero _ _ _ _ _

/-- The morphism of base changes defined by a cosimplicial homotopy is an isomorphism. -/
instance isIso_homotopyBaseChangeHom : IsIso (homotopyBaseChangeHom H M hM) := by
  have : IsIso ((homotopyBaseChangeHom H M hM).app (op (op ⦋0⦌))) := by
    rw [homotopyBaseChangeHom_app_zero]
    exact inferInstanceAs (IsIso (homotopyBaseChangeZero H M hM))
  exact isIso_of_cartesian_of_isIso_app_zero
    (cartesianModules_changeOfRings (ringPresheafMap f) M hM)
    (cartesianModules_changeOfRings (ringPresheafMap g) M hM) _

/-- The degree-zero component of the morphism of base changes of a homotopy is natural in the
cartesian module. -/
theorem homotopyBaseChangeZero_naturality
    {M' : PresheafOfModules.{max w v} (ringPresheaf (cosimplicialRingPresheaf A))}
    (hM' : cartesianModules (cosimplicialRingPresheaf A) M') (a : M ⟶ M') :
    (ModuleCat.extendScalars (componentRingMap f ⦋0⦌)).map (a.app (op (op ⦋0⦌))) ≫
        homotopyBaseChangeZero H M' hM' =
      homotopyBaseChangeZero H M hM ≫
        (ModuleCat.extendScalars (componentRingMap g ⦋0⦌)).map (a.app (op (op ⦋0⦌))) := by
  have := hM (cof₀ 0); have := hM' (cof₀ 0)
  rw [homotopyBaseChangeZero, homotopyBaseChangeZero, ← Category.assoc, transport_naturality,
    Category.assoc, Category.assoc, inv_transport_naturality]

/-- The morphism of base changes of a homotopy is natural in the cartesian module. -/
theorem homotopyBaseChangeHom_naturality
    {M' : PresheafOfModules.{max w v} (ringPresheaf (cosimplicialRingPresheaf A))}
    (hM' : cartesianModules (cosimplicialRingPresheaf A) M') (a : M ⟶ M') :
    (changeOfRings (ringPresheafMap f)).map a ≫ homotopyBaseChangeHom H M' hM' =
      homotopyBaseChangeHom H M hM ≫ (changeOfRings (ringPresheafMap g)).map a := by
  refine hom_ext_of_cartesian_app_zero (cartesianModules_changeOfRings (ringPresheafMap f) M hM)
    ?_
  rw [PresheafOfModules.comp_app, PresheafOfModules.comp_app, homotopyBaseChangeHom_app_zero,
    homotopyBaseChangeHom_app_zero, changeOfRings_map_app, changeOfRings_map_app]
  exact homotopyBaseChangeZero_naturality H M hM hM' a

end HomotopyInvariance

section HomotopyInvarianceFunctor

open Stacks.PresheafOfModules.ChangeOfRings

variable {f g : A ⟶ B} (H : SimplicialObject.Homotopy (NatTrans.op f) (NatTrans.op g))

/-- **Base change along homotopic morphisms gives isomorphic functors on cartesian modules.**
A cosimplicial homotopy from `f` to `g` gives an isomorphism `M ⊗_f B ≅ M ⊗_g B` of cartesian
`B`-modules, natural in the cartesian `A`-module `M`. -/
noncomputable def homotopyBaseChangeIso :
    cartesianBaseChange.{u, v, w} f ≅ cartesianBaseChange.{u, v, w} g :=
  NatIso.ofComponents
    (fun M => (cartesianModules _).fullyFaithfulι.preimageIso
      (@asIso _ _ _ _ (homotopyBaseChangeHom H M.obj M.property)
        (isIso_homotopyBaseChangeHom H M.obj M.property)))
    (fun {M M'} a => (cartesianModules _).ι.map_injective
      (homotopyBaseChangeHom_naturality H M.obj M.property M'.property a.hom))

end HomotopyInvarianceFunctor


/-- **Base change along a morphism with a two-sided inverse up to isomorphism of functors is an
equivalence.**  If `β : B ⟶ A` is such that base change along `α ≫ β` and along `β ≫ α` are
isomorphic to the identity functors on cartesian modules, then base change along `α` is an
equivalence of categories between the cartesian `A`-modules and the cartesian `B`-modules.  This
is the formal content of Stacks 039Y (4), with the homotopies replaced by what they are used
for. -/
theorem isEquivalence_cartesianBaseChange_of_iso (α : A ⟶ B) (β : B ⟶ A)
    (eA : cartesianBaseChange.{u, v, w} (α ≫ β) ≅
      Functor.id (CartesianCosimplicialModule.{u, v, w} A))
    (eB : cartesianBaseChange.{u, v, w} (β ≫ α) ≅
      Functor.id (CartesianCosimplicialModule.{u, v, w} B)) :
    (cartesianBaseChange.{u, v, w} α).IsEquivalence :=
  (Equivalence.mk (cartesianBaseChange.{u, v, w} α) (cartesianBaseChange.{u, v, w} β)
    (eA.symm ≪≫ (cartesianBaseChangeCompIso.{u, v, w} α β).symm)
    (cartesianBaseChangeCompIso.{u, v, w} β α ≪≫ eB)).isEquivalence_functor

/-- **Base change along homotopic morphisms gives isomorphic functors on cartesian modules**, for
*homotopic* in the sense of Simplicial, Definition 019K/019M through the opposite category: the
equivalence relation generated by the existence of a cosimplicial homotopy. -/
theorem nonempty_iso_cartesianBaseChange_of_homotopic {f g : A ⟶ B}
    (h : Relation.EqvGen (fun p q : B.op ⟶ A.op => Nonempty (SimplicialObject.Homotopy p q))
      (NatTrans.op f) (NatTrans.op g)) :
    Nonempty (cartesianBaseChange.{u, v, w} f ≅ cartesianBaseChange.{u, v, w} g) := by
  have op_removeOp : ∀ p : B.op ⟶ A.op, NatTrans.op (NatTrans.removeOp p) = p := fun p => by
    ext
    rfl
  have key : ∀ p q : B.op ⟶ A.op,
      Relation.EqvGen (fun p q : B.op ⟶ A.op => Nonempty (SimplicialObject.Homotopy p q)) p q →
      ∀ f g : A ⟶ B, NatTrans.op f = p → NatTrans.op g = q →
        Nonempty (cartesianBaseChange.{u, v, w} f ≅ cartesianBaseChange.{u, v, w} g) := by
    intro p q h
    induction h with
    | rel p q h =>
      rintro f g rfl rfl
      obtain ⟨H⟩ := h
      exact ⟨homotopyBaseChangeIso H⟩
    | refl p =>
      rintro f g hf hg
      obtain rfl : f = g := by
        have := congrArg NatTrans.removeOp (hf.trans hg.symm)
        exact NatTrans.ext (funext fun X => congrArg (fun φ => φ.app X) this)
      exact ⟨Iso.refl _⟩
    | symm p q _ ih =>
      rintro f g hf hg
      obtain ⟨e⟩ := ih g f hg hf
      exact ⟨e.symm⟩
    | trans p q r _ _ ih ih' =>
      rintro f g hf hg
      obtain ⟨e⟩ := ih f (NatTrans.removeOp q) hf (op_removeOp q)
      obtain ⟨e'⟩ := ih' (NatTrans.removeOp q) g (op_removeOp q) hg
      exact ⟨e ≪≫ e'⟩
  exact key _ _ h f g rfl rfl

/-- **Stacks 039Y (4).**  If `α : A_• ⟶ B_•` is a homotopy equivalence of cosimplicial
`R`-algebras, then the functor `M_• ↦ M_• ⊗_{A_•} B_•` is an equivalence of categories between
the cartesian `A_•`-modules and the cartesian `B_•`-modules.

A homotopy equivalence is taken in the sense of Simplicial, Definition 019N, through the opposite
category (cosimplicial homotopies being simplicial homotopies of the opposite objects,
Simplicial, Lemma 019X), exactly as in Stacks 039Y (3) here
(`CategoryTheory.Arrow.cechConerve_homotopyEquivalent_const_of_section`).  The proof is the
source's "triviality": base change along homotopic morphisms gives isomorphic functors
(`CategoryTheory.CosimplicialModule.nonempty_iso_cartesianBaseChange_of_homotopic`), so a homotopy
inverse `β` makes base change along `α ≫ β` and along `β ≫ α` isomorphic to the identities, and
base change is functorial (`CategoryTheory.CosimplicialModule.cartesianBaseChangeCompIso`). -/
@[stacks 039Y "(4): base change along a homotopy equivalence of cosimplicial algebras is an \
  equivalence of the categories of cartesian modules"]
theorem isEquivalence_cartesianBaseChange_of_homotopyEquivalence (α : A ⟶ B)
    (hα : SimplicialObject.homotopyEquivalences (CommAlgCat.{v, u} R)ᵒᵖ (NatTrans.op α)) :
    (cartesianBaseChange.{u, v, w} α).IsEquivalence := by
  obtain ⟨b, h₁, h₂⟩ := hα
  obtain ⟨eB⟩ := nonempty_iso_cartesianBaseChange_of_homotopic.{u, v, w}
    (f := NatTrans.removeOp b ≫ α) (g := 𝟙 B) h₁
  obtain ⟨eA⟩ := nonempty_iso_cartesianBaseChange_of_homotopic.{u, v, w}
    (f := α ≫ NatTrans.removeOp b) (g := 𝟙 A) h₂
  exact isEquivalence_cartesianBaseChange_of_iso.{u, v, w} α (NatTrans.removeOp b)
    (eA ≪≫ cartesianBaseChangeIdIso.{u, v, w} A) (eB ≪≫ cartesianBaseChangeIdIso.{u, v, w} B)

end CategoryTheory.CosimplicialModule

end
