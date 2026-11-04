module

public import StacksFrontier.Topology.Simplicial.ConstantSpace

/-!
# Sheaves on the site of a constant simplicial space

Let `X` be a topological space and `X_•` the constant simplicial space with value `X`
(`Stacks.Topology.Simplicial.constantSpace`). All its spaces are `X` and all its face and
degeneracy maps are the identity of `X`, so in the description of sheaves on `X_{•,Zar}` by systems
`(F_n, F(φ))` (`Stacks.Topology.Simplicial.sheafEquivalenceSimplicialSheafSystem`) each `F_n` is a
sheaf on `X` and each `F(φ) : F_m → F_n` is an `id_X`-map, that is, a morphism of sheaves on `X`.
The identities `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id` then say that `[n] ↦ F_n` is a functor
on the simplex category: a sheaf on `X_{•,Zar}` is the same thing as a cosimplicial object in the
category of sheaves on `X`.

## Main definitions

* `Stacks.Topology.Simplicial.ConstantSpace.systemToCosimplicial` and `cosimplicialToSystem`:
  a system of sheaves on the constant simplicial space as a cosimplicial sheaf on `X`, and back.
* `Stacks.Topology.Simplicial.ConstantSpace.systemCosimplicialEquivalence`: the resulting
  equivalence of categories.
* `Stacks.Topology.Simplicial.ConstantSpace.sheafCosimplicialEquivalence`: sheaves on `X_{•,Zar}`
  are cosimplicial sheaves on `X`.

## Implementation notes

The spaces of the constant simplicial space are definitionally `X`, its maps are definitionally
`𝟙 X`, and the inverse image of an open of `X` along `𝟙 X` is definitionally that open. So an
`id_X`-map `F_m → F_n` *is* a morphism of sheaves on `X`, and the two functors of the equivalence
are mutually inverse on the nose; the unit and counit have identity components.

The equivalence holds for sheaves with values in any category.

## References

* [Stacks Project, Tag 09VK](https://stacks.math.columbia.edu/tag/09VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Topology.Simplicial

add_to_stacks 09VK "the constant simplicial topological space `X_•` with value `X`" constantSpace

namespace ConstantSpace

variable (X : TopCat.{u}) (A : Type w) [Category.{v} A]

/-- A system of sheaves on the constant simplicial space on `X` is a cosimplicial sheaf on `X`:
the transition `id_X`-map `F(φ) : F_m → F_n` along `φ : [m] → [n]` is a morphism of sheaves. -/
def systemToCosimplicial :
    SimplicialSheafSystem (constantSpace X) A ⥤ CosimplicialObject (TopCat.Sheaf A X) where
  obj S :=
    { obj n := S.component (op n)
      map {n m} f := ObjectProperty.homMk
        { app V := (S.transition f.op).app V
          naturality _ _ h := (S.transition f.op).naturality h }
      map_id n := by
        apply Sheaf.hom_ext
        ext V
        exact eq_of_heq (S.transition_id (op n) V)
      map_comp f g := by
        apply Sheaf.hom_ext
        ext V
        exact (eq_of_heq (S.transition_comp g.op f.op V)).symm }
  map {S T} α :=
    { app n := α.componentHom (op n)
      naturality n m f := by
        apply Sheaf.hom_ext
        ext V
        exact α.naturality f.op V }
  map_id S := rfl
  map_comp α β := rfl

/-- The cosimplicial sheaf attached to a system `S` takes the value `S_n` at `[n]`. -/
@[simp]
theorem systemToCosimplicial_obj_obj (S : SimplicialSheafSystem (constantSpace X) A)
    (n : SimplexCategory) : ((systemToCosimplicial X A).obj S).obj n = S.component (op n) :=
  rfl

/-- On an open `V`, the morphism of sheaves attached to `f : [n] → [m]` by the cosimplicial sheaf
of a system `S` is the transition map `S(f)` on `V`. -/
@[simp]
theorem systemToCosimplicial_obj_map_hom_app (S : SimplicialSheafSystem (constantSpace X) A)
    {n m : SimplexCategory} (f : n ⟶ m) (V : (Opens X)ᵒᵖ) :
    (((systemToCosimplicial X A).obj S).map f).hom.app V = (S.transition f.op).app V :=
  rfl

/-- A cosimplicial sheaf on `X` is a system of sheaves on the constant simplicial space on `X`:
the morphism of sheaves `F_m → F_n` along `φ : [m] → [n]` is an `id_X`-map. -/
def cosimplicialToSystem :
    CosimplicialObject (TopCat.Sheaf A X) ⥤ SimplicialSheafSystem (constantSpace X) A where
  obj C :=
    { component n := C.obj n.unop
      transition {n m} φ :=
        { app V := (C.map φ.unop).hom.app V
          naturality h := (C.map φ.unop).hom.naturality h }
      transition_id n V := by
        refine heq_of_eq ?_
        change (C.map (𝟙 n.unop)).hom.app V = 𝟙 _
        rw [C.map_id]
        rfl
      transition_comp φ ψ V := by
        refine heq_of_eq ?_
        change (C.map ψ.unop).hom.app V ≫ (C.map φ.unop).hom.app V =
          (C.map (ψ.unop ≫ φ.unop)).hom.app V
        rw [C.map_comp]
        rfl }
  map {C D} α :=
    { componentHom n := α.app n.unop
      naturality φ V := by
        change (C.map φ.unop ≫ α.app _).hom.app V = (α.app _ ≫ D.map φ.unop).hom.app V
        rw [α.naturality] }
  map_id C := rfl
  map_comp α β := rfl

/-- **A system of sheaves on the constant simplicial space on `X` is the same thing as a
cosimplicial sheaf on `X`.** -/
@[stacks 09VK "systems `(F_n, F(φ))` on the constant simplicial space `X_•` are cosimplicial
  objects in the category of sheaves on `X`"]
def systemCosimplicialEquivalence :
    SimplicialSheafSystem (constantSpace X) A ≌ CosimplicialObject (TopCat.Sheaf A X) where
  functor := systemToCosimplicial X A
  inverse := cosimplicialToSystem X A
  unitIso := NatIso.ofComponents (fun S => Iso.refl S) (fun α => by
    apply SimplicialSheafSystem.Hom.ext
    intro n
    change α.componentHom n ≫ 𝟙 _ = 𝟙 _ ≫ α.componentHom n
    simp)
  counitIso := NatIso.ofComponents (fun C => Iso.refl C) (fun α => by
    ext n
    change α.app n ≫ 𝟙 _ = 𝟙 _ ≫ α.app n
    simp)
  functor_unitIso_comp S := by
    ext n
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- **A sheaf on `X_{•,Zar}` is the same thing as a cosimplicial object in the category of
sheaves on `X`.** The equivalence is the description of Lemma 09VM
(`Stacks.Topology.Simplicial.sheafEquivalenceSimplicialSheafSystem`) followed by
`systemCosimplicialEquivalence`; the sheaf in degree `[n]` of the cosimplicial object attached to
a sheaf `F` is the restriction `F_n` of `F` to the opens of the `n`-th copy of `X`. -/
@[stacks 09VK "by Lemma 09VM a sheaf on `X_{•,Zar}` is the same thing as a cosimplicial object in
  the category of sheaves on `X`"]
def sheafCosimplicialEquivalence :
    Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) A ≌
      CosimplicialObject (TopCat.Sheaf A X) :=
  (sheafEquivalenceSimplicialSheafSystem (constantSpace X) A).toEquivalence.trans
    (systemCosimplicialEquivalence X A)

/-- The sheaf in degree `[n]` of the cosimplicial sheaf attached to a sheaf on `X_{•,Zar}` is its
component in degree `n` in the description of Lemma 09VM. -/
theorem sheafCosimplicialEquivalence_functor_obj_obj
    (F : Sheaf (SimplicialOpen.grothendieckTopology (constantSpace X)) A) (n : SimplexCategory) :
    ((sheafCosimplicialEquivalence X A).functor.obj F).obj n =
      ((sheafEquivalenceSimplicialSheafSystem (constantSpace X) A).toEquivalence.functor.obj
        F).component (op n) :=
  rfl

end ConstantSpace

end Stacks.Topology.Simplicial

end
