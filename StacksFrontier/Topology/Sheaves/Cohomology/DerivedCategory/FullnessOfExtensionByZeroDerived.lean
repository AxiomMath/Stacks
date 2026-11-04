module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Extension by zero is fully faithful on unbounded derived categories

Let `X` be a topological space, `𝒪` a sheaf of rings on it and `U ⊆ X` an open subset. Extension
by zero `j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` is left adjoint to restriction `j^*` with invertible unit, and
`j_!` is fully faithful on the unbounded derived categories.

## Main results

* `Stacks.DerivedGlueing.isIso_unit_of_comp_iso` — the unit of an adjunction whose composite is
  isomorphic to the identity is invertible.
* `Stacks.DerivedGlueing.fullyFaithful_mapDerivedCategory_of_isIso_unit` and
  `Stacks.DerivedGlueing.full_mapDerivedCategory_of_isIso_unit` — an exact left adjoint with
  exact right adjoint and invertible unit is fully faithful on unbounded derived categories.
* `Stacks.DerivedGlueing.fullyFaithful_jShriek_mapDerivedCategory` and
  `Stacks.DerivedGlueing.full_jShriek_mapDerivedCategory` — extension by zero along an arbitrary
  open is fully faithful on unbounded derived categories.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_map_of_fullyFaithful` — a fully faithful functor
  commuting with the shift preserves the vanishing of a shifted `Hom` group.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_jShriek` — the vanishing of `Ext^i(K, L)` over an
  open and of `Ext^i(j_!K, j_!L)` over the whole space are equivalent.

## References

* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe w₁ w₂ v₁ v₂ u₁ u₂ u

/-! ### The unit of an adjunction whose composite is isomorphic to the identity -/

section Unit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The unit of an adjunction `L ⊣ R` is invertible as soon as `L ⋙ R` is isomorphic to the
identity, by an isomorphism `θ` not assumed to be the unit. -/
theorem isIso_unit_of_comp_iso {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (θ : L ⋙ R ≅ 𝟭 C) :
    IsIso adj.unit := by
  have (X : C) : IsIso (adj.unit.app X) := by
    have hts : θ.hom.app X ≫ θ.inv.app X = 𝟙 _ := θ.hom_inv_id_app X
    set r := (L ⋙ R).map (θ.inv.app X) ≫ R.map (adj.counit.app (L.obj X)) ≫ θ.hom.app X
      with hr
    have hunit : adj.unit.app X ≫ r = 𝟙 X := by
      have hnat : θ.hom.app X ≫ adj.unit.app X =
          adj.unit.app ((L ⋙ R).obj X) ≫ (L ⋙ R).map (θ.hom.app X) := adj.unit.naturality _
      have htri : adj.unit.app ((L ⋙ R).obj X) ≫ R.map (adj.counit.app (L.obj X)) =
          𝟙 ((L ⋙ R).obj X) := adj.right_triangle_components (L.obj X)
      rw [← cancel_epi (θ.hom.app X), hr, ← Category.assoc, hnat, Category.assoc,
        ← Functor.map_comp_assoc, hts, CategoryTheory.Functor.map_id, Category.id_comp,
        ← Category.assoc, htri, Category.id_comp]
      exact (Category.comp_id _).symm
    have hα : (adj.unit ≫ θ.hom).app X ≫ θ.inv.app X ≫ r = 𝟙 X := by
      rw [NatTrans.comp_app, Category.assoc, reassoc_of% hts, hunit]
    have : IsIso ((adj.unit ≫ θ.hom).app X) :=
      ⟨⟨_, hα, ((adj.unit ≫ θ.hom).naturality (θ.inv.app X ≫ r)).trans hα⟩⟩
    rw [show adj.unit.app X = (adj.unit ≫ θ.hom).app X ≫ θ.inv.app X by simp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Unit

/-! ### Full faithfulness on unbounded derived categories -/

section Derived

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- An exact left adjoint with exact right adjoint and invertible unit is fully faithful on
unbounded derived categories. -/
def fullyFaithful_mapDerivedCategory_of_isIso_unit (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₁) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) [IsIso adj.unit] :
    F.mapDerivedCategory.FullyFaithful :=
  have := comp_preservesFiniteLimits F G
  have := comp_preservesFiniteColimits F G
  letI θ : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
    mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryCongr (asIso adj.unit).symm ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso
  letI := isIso_unit_of_comp_iso (Adjunction.mapDerivedCategory adj) θ
  (Adjunction.mapDerivedCategory adj).fullyFaithfulLOfIsIsoUnit

/-- An exact left adjoint with exact right adjoint and invertible unit is full on unbounded
derived categories. -/
theorem full_mapDerivedCategory_of_isIso_unit (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₁) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) [IsIso adj.unit] :
    F.mapDerivedCategory.Full :=
  (fullyFaithful_mapDerivedCategory_of_isIso_unit F G adj).full

/-- A fully faithful functor commuting with the shift preserves the vanishing of a shifted `Hom`
group. -/
theorem subsingleton_shiftedHom_map_of_fullyFaithful
    (F : DerivedCategory C₁ ⥤ DerivedCategory C₂) [F.Full] [F.Faithful] [F.CommShift ℤ]
    (K L : DerivedCategory C₁) (i : ℤ) (h : Subsingleton (ShiftedHom K L i)) :
    Subsingleton (ShiftedHom (F.obj K) (F.obj L) i) :=
  Equiv.subsingleton
    ((Iso.homCongr (Iso.refl (F.obj K)) ((F.commShiftIso i).app L).symm).trans
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm)

end Derived

/-! ### Extension by zero along an arbitrary open -/

section JShriek

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- Extension by zero along an open is fully faithful on unbounded derived categories. -/
def fullyFaithful_jShriek_mapDerivedCategory (U : Opens T) :
    (jShriek U O).mapDerivedCategory.FullyFaithful :=
  letI := isIso_jShriekAdjunction_unit U O
  fullyFaithful_mapDerivedCategory_of_isIso_unit (jShriek U O) (jStar U O)
    (jShriekAdjunction U O)

/-- Extension by zero along an open is full on unbounded derived categories. -/
theorem full_jShriek_mapDerivedCategory (U : Opens T) :
    (jShriek U O).mapDerivedCategory.Full :=
  (fullyFaithful_jShriek_mapDerivedCategory O U).full

/-- For objects `K` and `L` of the derived category of modules on the open subspace `U` and
`i : ℤ`, `Ext^i(j_!K, j_!L) = 0` if and only if `Ext^i(K, L) = 0`. -/
theorem subsingleton_shiftedHom_jShriek (U : Opens T)
    (K L : DerivedCategory (SheafOfModules.{u} (resRing U O))) (i : ℤ) :
    Subsingleton (ShiftedHom ((jShriek U O).mapDerivedCategory.obj K)
        ((jShriek U O).mapDerivedCategory.obj L) i) ↔
      Subsingleton (ShiftedHom K L i) := by
  have := faithful_jShriek_mapDerivedCategory O U
  have := full_jShriek_mapDerivedCategory O U
  exact ⟨fun h ↦ subsingleton_shiftedHom_of_faithful (jShriek U O).mapDerivedCategory K L i h,
    fun h ↦ subsingleton_shiftedHom_map_of_fullyFaithful
      (jShriek U O).mapDerivedCategory K L i h⟩

end JShriek

end Stacks.DerivedGlueing

end
