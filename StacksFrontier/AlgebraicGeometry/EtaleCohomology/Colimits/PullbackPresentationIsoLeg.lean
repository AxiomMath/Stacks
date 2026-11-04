module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# A colimit presentation of a system of isomorphisms has invertible legs

Let `X = lim X_i` be the limit of an inverse system of schemes over a preordered set `I` with a
least element `i₀`, let `(E_i, φ_{i'i})` be a system of abelian sheaves on the `X_i` all of whose
transition maps `φ_{i'i} : f_{i'i}⁻¹E_i ⟶ E_{i'}` are isomorphisms, and let
`ψ_i : f_i⁻¹E_i ⟶ B` present a sheaf `B` on `X` as the colimit of the inverse images
`f_i⁻¹E_i` (in the sense of [Stacks, Tag 0EZL]). Then the leg `ψ_{i₀}` is an isomorphism:
the inverses of the transition maps to the least index form a compatible family, by the cocycle
condition of the system and the associativity of the comparisons of inverse images, and the map
it induces out of `B` inverts `ψ_{i₀}`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isIso_leg_of_isIso_map` .
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
  (E : EtaleSheafSystem D Ab.{u + 1})

/-- The map of a pulled back system along the projections of a cone: `f_{i'}⁻¹E_{i'} ⟶ f_i⁻¹E_i`
read through the comparison of inverse images, for `a : i ⟶ j` in `Iᵒᵖ`. -/
abbrev pullbackSystemMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (c.π.app j)).obj (E.obj j) ⟶
      (smallEtalePullbackAb (c.π.app i)).obj (E.obj i) :=
  (conePullbackComp c a).inv.app (E.obj j) ≫ (smallEtalePullbackAb (c.π.app i)).map (E.map a)

/-- **The cocycle condition of a pulled back system.** -/
theorem pullbackSystemMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    pullbackSystemMap c E (a ≫ b) =
      pullbackSystemMap c E (i := j) (j := k) b ≫ pullbackSystemMap c E (i := i) (j := j) a := by
  have hp := smallEtalePullbackAbComp'_assoc_app (c.π.app i) (D.map a) (D.map b) (c.π.app j)
    (c.w a).symm (D.map (a ≫ b)) (D.map_comp a b) (c.π.app k) (c.w b).symm (c.w (a ≫ b)).symm
    (E.obj k)
  have hE := E.map_comp a b
  rw [systemPullbackComp_eq] at hE
  have hnat : (smallEtalePullbackAb (c.π.app j)).map (E.map b) ≫
      (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app
        (E.obj j) =
      (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app
          ((smallEtalePullbackAb (D.map b)).obj (E.obj k)) ≫
        (smallEtalePullbackAb (c.π.app i)).map ((smallEtalePullbackAb (D.map a)).map (E.map b)) :=
    (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.naturality
      (E.map b)
  have hp' : (smallEtalePullbackAbComp' (c.π.app j) (D.map b) (c.π.app k) (c.w b).symm).inv.app
        (E.obj k) ≫
      (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app
        ((smallEtalePullbackAb (D.map b)).obj (E.obj k)) =
      (smallEtalePullbackAbComp' (c.π.app i) (D.map (a ≫ b)) (c.π.app k)
          (c.w (a ≫ b)).symm).inv.app (E.obj k) ≫
        (smallEtalePullbackAb (c.π.app i)).map
          ((smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
            (D.map_comp a b)).inv.app (E.obj k)) := by
    rw [← cancel_epi ((smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j)
        (c.w a).symm).hom.app ((smallEtalePullbackAb (D.map b)).obj (E.obj k)) ≫
      (smallEtalePullbackAbComp' (c.π.app j) (D.map b) (c.π.app k) (c.w b).symm).hom.app
        (E.obj k))]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [reassoc_of% hp, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app]
    exact ((smallEtalePullbackAb (c.π.app i)).map_id _).symm
  dsimp only [pullbackSystemMap]
  rw [conePullbackComp_eq, conePullbackComp_eq, conePullbackComp_eq, ← hE]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hp']

/-- **A colimit presentation of a system of isomorphisms has invertible legs.** If every transition
map of the system `E` is an isomorphism and `ψ` presents `B` as the colimit of the inverse images
`f_i⁻¹E_i`, then the leg at a least index is an isomorphism. -/
theorem isIso_leg_of_isIso_map {B : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ψ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (E.obj i) ⟶ B)
    (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), pullbackSystemMap c E (i := i) (j := j) a ≫ ψ i = ψ j)
    (hpres : IsPullbackColimitPresentation c B E ψ)
    (hE : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsIso (E.map a)) (i₀ : I) (hi₀ : ∀ i : I, i₀ ≤ i) :
    IsIso (ψ (Opposite.op i₀)) := by
  have hT : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsIso (pullbackSystemMap c E (i := i) (j := j) a) := by
    intro i j a
    have := hE a
    dsimp only [pullbackSystemMap]
    infer_instance
  let a₀ : ∀ i : Iᵒᵖ, i ⟶ Opposite.op i₀ := fun i => (homOfLE (hi₀ i.unop)).op
  let τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (E.obj i) ⟶
      (smallEtalePullbackAb (c.π.app (Opposite.op i₀))).obj (E.obj (Opposite.op i₀)) :=
    fun i => have := hT (a₀ i); inv (pullbackSystemMap c E (i := i) (j := Opposite.op i₀) (a₀ i))
  have hτ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (conePullbackComp c a).inv.app (E.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (E.map a) ≫ τ i = τ j := by
    intro i j a
    rw [← Category.assoc]
    show pullbackSystemMap c E (i := i) (j := j) a ≫ τ i = τ j
    have hc := pullbackSystemMap_comp c E a (a₀ j)
    rw [show a ≫ a₀ j = a₀ i from Subsingleton.elim _ _] at hc
    have := hT a
    have := hT (a₀ j)
    show _ ≫ inv (pullbackSystemMap c E (i := i) (j := Opposite.op i₀) (a₀ i)) =
      inv (pullbackSystemMap c E (i := j) (j := Opposite.op i₀) (a₀ j))
    rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
    exact hc.symm
  obtain ⟨χ, hχ, -⟩ := hpres _ τ hτ
  have := hT (a₀ (Opposite.op i₀))
  refine ⟨χ ≫ pullbackSystemMap c E (i := Opposite.op i₀) (j := Opposite.op i₀)
    (a₀ (Opposite.op i₀)), ?_, ?_⟩
  · rw [← Category.assoc, hχ]
    simp only [τ, IsIso.inv_hom_id]
  · obtain ⟨χ', -, hu⟩ := hpres B ψ (fun a => by rw [← Category.assoc]; exact hψ a)
    have h1 := hu (𝟙 B) (fun i => Category.comp_id _)
    have h2 := hu (χ ≫ pullbackSystemMap c E (i := Opposite.op i₀) (j := Opposite.op i₀)
        (a₀ (Opposite.op i₀)) ≫ ψ (Opposite.op i₀))
      (fun i => by
        have := hT (a₀ i)
        rw [← Category.assoc, hχ, hψ (a₀ (Opposite.op i₀))]
        simp only [τ, IsIso.inv_comp_eq]
        exact (hψ (a₀ i)).symm)
    rw [Category.assoc]
    exact h2.trans h1.symm

end Stacks.EtaleCohomology.LimitHigherDirectImage
