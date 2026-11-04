module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque sheaves are closed under finite biproducts

A sheaf of abelian groups `F` on a topological space is *flasque* when all its restriction maps
`F(U) ⟶ F(V)` are surjective. This file shows that the property is stable under isomorphism and
under finite biproducts.

## Main definitions

* `TopCat.Sheaf.biproductObjIsoProduct`: the underlying presheaf of a finite biproduct of
  sheaves is the product of the underlying presheaves.
* `TopCat.Sheaf.prodSectionsIso`: the sections of a finite product of presheaves are the product
  of their sections.

## Main results

* `TopCat.Sheaf.IsFlasque.of_iso`: flasqueness transfers along an isomorphism of sheaves.
* `TopCat.Sheaf.isFlasque_biproduct`: a finite biproduct of flasque sheaves is flasque.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {Y : TopCat.{u}}

section Biproducts

/-- The underlying presheaf of a finite biproduct of sheaves of abelian groups is the product of
their underlying presheaves. -/
noncomputable def biproductObjIsoProduct {I : Type*} [Finite I]
    [HasFiniteBiproducts (TopCat.Sheaf AddCommGrpCat.{u} Y)]
    (A : I → TopCat.Sheaf AddCommGrpCat.{u} Y) :
    (⨁ A).obj ≅ ∏ᶜ fun i => (A i).obj := by
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} Y
  let D := Discrete.functor A
  let c : D ⋙ G ≅ Discrete.functor (fun i => G.obj (A i)) :=
    Discrete.compNatIsoDiscrete A G
  exact (G.mapIso (biproduct.isoProduct A)).trans
    (preservesLimitIso G D ≪≫ HasLimit.isoOfNatIso c)

/-- The sections over `U` of a finite product of presheaves of abelian groups form the product of
their sections over `U`. -/
noncomputable def prodSectionsIso {I : Type*} [Finite I]
    (A : I → TopCat.Presheaf AddCommGrpCat.{u} Y) (U : Opens Y) :
    (∏ᶜ fun i => A i).obj (op U) ≅ ∏ᶜ fun i => (A i).obj (op U) := by
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let D := Discrete.functor A
  let c : D ⋙ E ≅ Discrete.functor (fun i => E.obj (A i)) :=
    Discrete.compNatIsoDiscrete A E
  exact preservesLimitIso E D ≪≫ HasLimit.isoOfNatIso c

/-- Flasqueness transfers along an isomorphism of sheaves of abelian groups. -/
theorem IsFlasque.of_iso {A B : TopCat.Sheaf AddCommGrpCat.{u} Y} (e : A ≅ B)
    (hB : B.IsFlasque) : A.IsFlasque := by
  refine ⟨fun {U V} i => ?_⟩
  have : Epi (B.obj.map i) := hB.epi i
  let c := (sheafToPresheaf _ _).mapIso e
  have hnat : A.obj.map i ≫ (c.app V).hom = (c.app U).hom ≫ B.obj.map i :=
    e.hom.hom.naturality i
  rw [← epi_comp_iff_of_isIso (A.obj.map i) (c.app V).hom, hnat]
  infer_instance

/-- A finite biproduct of flasque sheaves of abelian groups is flasque. -/
theorem isFlasque_biproduct {I : Type*} [Finite I]
    [HasFiniteBiproducts (TopCat.Sheaf AddCommGrpCat.{u} Y)]
    (A : I → TopCat.Sheaf AddCommGrpCat.{u} Y) (hA : ∀ i, (A i).IsFlasque) :
    (⨁ A).IsFlasque := by
  classical
  constructor
  intro U V i
  let eAB := biproductObjIsoProduct (Y := Y) (I := I) A
  let cU := asIso (eAB.hom.app U)
  let cV := asIso (eAB.hom.app V)
  let pU := prodSectionsIso (fun j => (A j).obj) U.unop
  let pV := prodSectionsIso (fun j => (A j).obj) V.unop
  let dU := cU.trans pU
  let dV := cV.trans pV
  let f := (⨁ A).obj.map i
  let g := (∏ᶜ fun j => (A j).obj).map i
  let g' : (∏ᶜ fun j => (A j).obj.obj U) ⟶ (∏ᶜ fun j => (A j).obj.obj V) :=
    Limits.Pi.map fun j => (A j).obj.map i
  have h1 : f ≫ cV.hom = cU.hom ≫ g := eAB.hom.naturality i
  have h2 : g ≫ pV.hom = pU.hom ≫ g' := by
    apply limit.hom_ext
    intro j
    have hp : ∀ W : (Opens Y)ᵒᵖ, (prodSectionsIso (fun k => (A k).obj) W.unop).hom ≫
        limit.π (Discrete.functor (fun k => (A k).obj.obj W)) j =
        (limit.π (Discrete.functor (fun k => (A k).obj)) j).app W := fun W => by
      dsimp [prodSectionsIso]
      simp [Category.assoc, preservesLimitIso_hom_π, HasLimit.isoOfNatIso_hom_π]
    dsimp [g, g']
    calc
      _ = (∏ᶜ fun k => (A k).obj).map i ≫
            (limit.π (Discrete.functor (fun k => (A k).obj)) j).app V := by
            rw [Category.assoc, hp V]
      _ = (limit.π (Discrete.functor (fun k => (A k).obj)) j).app U ≫ (A j.as).obj.map i :=
            (limit.π (Discrete.functor (fun k => (A k).obj)) j).naturality i
      _ = pU.hom ≫ (Limits.Pi.map (fun k => (A k).obj.map i) ≫
            limit.π (Discrete.functor (fun k => (A k).obj.obj V)) j) := by
            rw [Limits.Pi.map_π, ← Category.assoc, hp U]
  have hnat : f ≫ dV.hom = dU.hom ≫ g' := by
    dsimp [dU, dV]
    rw [← Category.assoc, h1, Category.assoc, h2]
    simp [Category.assoc]
  have : ∀ j, Epi ((A j).obj.map i) := fun j => (hA j).epi i
  rw [← epi_comp_iff_of_isIso f dV.hom, hnat]
  infer_instance

end Biproducts

end TopCat.Sheaf

end
