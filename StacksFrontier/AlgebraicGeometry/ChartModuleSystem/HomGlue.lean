module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Sheaf
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# Gluing morphisms of sheaves of modules from compatible maps on charts

Let `I` be an affine chart index of a scheme `Y` and `K` a property of charts such that every
chart can be refined, near each of its points, to a chart with `K`. A family of linear maps
`Γ(F, V c) → Γ(G, V c)`, one for every chart `c` with `K c`, which commutes with the restriction
maps along refinements, is the family of components of a unique morphism of sheaves of modules
`F ⟶ G` (Stacks 009U).

## Main definitions

* `AlgebraicGeometry.Scheme.AffineChartIndex.homOfCompatible`: the glued morphism.

## Main results

* `AlgebraicGeometry.Scheme.AffineChartIndex.homOfCompatible_app`: its components are the given
  maps.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.AffineChartIndex

variable {Y : Scheme.{u}} (I : Y.AffineChartIndex) (K : I.ι → Prop)
  (hK : ∀ (c : I.ι) {y : Y}, y ∈ (I.V c).1 → ∃ c', I.Refines c' c ∧ K c' ∧ y ∈ (I.V c').1)
  (W : {c : I.ι // K c} → Y.Opens) (hW : ∀ c, W c = (I.V c.1).1) {F G : Y.Modules}
  (φ : ∀ c : {c : I.ι // K c}, Γ(F, W c) →ₗ[Γ(Y, W c)] Γ(G, W c))
  (hφ : ∀ (c c' : {c : I.ι // K c}) (_ : I.Refines c'.1 c.1) (i : W c' ⟶ W c)
    (s : Γ(F, W c)), φ c' (F.presheaf.map i.op s) = G.presheaf.map i.op (φ c s))

include hK hW in
/-- The charts with `K` form a basis of the topology. -/
theorem isBasis_of_refines : Opens.IsBasis (Set.range W) := by
  obtain rfl : W = fun c => (I.V c.1).1 := funext hW
  refine Opens.isBasis_iff_nbhd.mpr fun {W y} hy => ?_
  obtain ⟨c, hyc⟩ := I.exists_mem y
  obtain ⟨c', -, hyc', hc'W⟩ := I.exists_refines_le hyc hy
  obtain ⟨c'', hc'', hKc'', hyc''⟩ := hK c' hyc'
  exact ⟨_, ⟨⟨c'', hKc''⟩, rfl⟩, hyc'', (I.le_of_refines hc'').trans hc'W⟩

/-- The components of the glued morphism, as morphisms of modules of sections. -/
def homOfCompatibleApp (c : {c : I.ι // K c}) :
    F.val.obj (op (W c)) ⟶ G.val.obj (op (W c)) :=
  ModuleCat.ofHom (φ c)

include hK hW hφ in
/-- The given maps are compatible with all restriction maps between the charts. -/
theorem isCompatibleOnBasis_homOfCompatibleApp :
    Stacks.BasisRestriction.IsCompatibleOnBasis F G W (I.homOfCompatibleApp K W φ) := by
  obtain rfl : W = fun c => (I.V c.1).1 := funext hW
  intro a b hba s
  have hex : ∀ z : {z : Y // z ∈ (I.V b.1).1}, ∃ c : {c : I.ι // K c},
      I.Refines c.1 a.1 ∧ I.Refines c.1 b.1 ∧ z.1 ∈ (I.V c.1).1 := fun z => by
    obtain ⟨c₀, h₁, h₂, hz⟩ := I.exists_refines_refines (hba z.2) z.2
    obtain ⟨c, hc, hKc, hzc⟩ := hK c₀ hz
    exact ⟨⟨c, hKc⟩, I.refines_trans hc h₁, I.refines_trans hc h₂, hzc⟩
  choose κ hκa hκb hκz using hex
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover G (fun z => (I.V (κ z).1).1)
    (fun z => I.le_of_refines (hκb z)) (fun y hy => ⟨⟨y, hy⟩, hκz ⟨y, hy⟩⟩) _ _ fun z => ?_
  change G.presheaf.map (homOfLE (I.le_of_refines (hκb z))).op
      (φ b (F.presheaf.map (homOfLE hba).op s)) =
    G.presheaf.map (homOfLE (I.le_of_refines (hκb z))).op
      (G.presheaf.map (homOfLE hba).op (φ a s))
  rw [← hφ b (κ z) (hκb z)]
  have e₁ := Scheme.Modules.presheaf_map_comp_apply F (homOfLE hba).op
    (homOfLE (I.le_of_refines (hκb z))).op (s : Γ(F, (I.V a.1).1))
  have e₂ := Scheme.Modules.presheaf_map_comp_apply G (homOfLE hba).op
    (homOfLE (I.le_of_refines (hκb z))).op (φ a s)
  refine (congrArg (φ (κ z)) e₁).trans (((hφ a (κ z) (hκa z) _ s).trans ?_).trans e₂.symm)
  rfl

/-- **The morphism of sheaves of modules glued from compatible maps on charts** (Stacks 009U).
The charts are given as a family of opens `W c` equal to `(I.V c).1`. -/
def homOfCompatible : F ⟶ G :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis F G W (I.homOfCompatibleApp K W φ)
    (I.isBasis_of_refines K hK W hW) (I.isCompatibleOnBasis_homOfCompatibleApp K hK W hW φ hφ)

/-- The glued morphism has the given maps as its components on the charts. -/
theorem homOfCompatible_app (c : {c : I.ι // K c}) (s : Γ(F, W c)) :
    (I.homOfCompatible K hK W hW φ hφ).app (W c) s = φ c s := by
  have h := Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app F G W
    (I.homOfCompatibleApp K W φ) (I.isBasis_of_refines K hK W hW)
    (I.isCompatibleOnBasis_homOfCompatibleApp K hK W hW φ hφ) c
  exact congrArg (fun g : F.val.obj (op (W c)) ⟶ G.val.obj (op (W c)) => g s) h

end AlgebraicGeometry.Scheme.AffineChartIndex

end
