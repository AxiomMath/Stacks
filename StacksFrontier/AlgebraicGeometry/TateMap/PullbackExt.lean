module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.TateMap.Glue

/-!
# Morphisms out of a pullback of modules

A morphism `b^*M ⟶ N` of sheaves of modules is determined by its values on the pullbacks of
sections of `M`, restricted to any family of opens covering the preimages of the members of a
basis.

## Main results

* `AlgebraicGeometry.TateMap.hom_ext_of_pullbackSection`: two morphisms `b^*M ⟶ N` agreeing on
  the restricted pullbacks of sections over a basis are equal.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.TateMap

/-- **Morphisms out of a pullback are determined by their values on pulled-back sections.** Let
`b : Y' ⟶ Y`, and let `P V V'` single out pairs of opens with `V' ≤ b⁻¹ V`. If the opens `V` for
which the `V'` with `P V V'` cover `b⁻¹ V` form a basis of `Y`, then two morphisms
`b^*M ⟶ N` agreeing on the pullbacks of the sections over `V` restricted to every such `V'` are
equal. -/
theorem hom_ext_of_pullbackSection {Y Y' : Scheme.{u}} (b : Y' ⟶ Y) {M : Y.Modules}
    {N : Y'.Modules} (φ ψ : (Scheme.Modules.pullback b).obj M ⟶ N)
    (P : Y.Opens → Y'.Opens → Prop) (hP : ∀ V V', P V V' → V' ≤ b ⁻¹ᵁ V)
    (hbasis : ∀ W : Y.Opens, ∀ y ∈ W, ∃ V : Y.Opens, y ∈ V ∧ V ≤ W ∧
      ∀ y' ∈ b ⁻¹ᵁ V, ∃ V', P V V' ∧ y' ∈ V')
    (heq : ∀ V V' (hVV' : P V V') (s : Γ(M, V)),
      φ.app V' (Scheme.Modules.pullbackSection b M V V' (hP V V' hVV') s) =
        ψ.app V' (Scheme.Modules.pullbackSection b M V V' (hP V V' hVV') s)) :
    φ = ψ := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction b
  apply (adj.homEquiv M N).injective
  let κ := {V : Y.Opens // ∀ y' ∈ b ⁻¹ᵁ V, ∃ V', P V V' ∧ y' ∈ V'}
  refine hom_ext_of_basis (fun k : κ ↦ k.1) (fun W y hy ↦ ?_) _ _ fun k s ↦ ?_
  · obtain ⟨V, hyV, hVW, hV⟩ := hbasis W y hy
    exact ⟨⟨V, hV⟩, hyV, hVW⟩
  · obtain ⟨V, hV⟩ := k
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    let F : TopCat.Sheaf Ab Y' := ⟨N.presheaf, N.isSheaf⟩
    let ι := {V' : Y'.Opens // P V V'}
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun i : ι ↦ i.1) (b ⁻¹ᵁ V)
      (fun i ↦ homOfLE (hP V i.1 i.2)) (fun y' hy' ↦ ?_) _ _ fun i ↦ ?_
    · obtain ⟨V', hVV', hy'V'⟩ := hV y' hy'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V', hVV'⟩, hy'V'⟩
    · let u : Γ((Scheme.Modules.pullback b).obj M, b ⁻¹ᵁ V) :=
        ((adj.unit.app M).val.app (op V)) s
      have nat : ∀ χ : (Scheme.Modules.pullback b).obj M ⟶ N,
          F.1.map (homOfLE (hP V i.1 i.2)).op (χ.app (b ⁻¹ᵁ V) u) =
            χ.app i.1 (((Scheme.Modules.pullback b).obj M).presheaf.map
              (homOfLE (hP V i.1 i.2)).op u) := fun χ ↦
        (congr($(χ.mapPresheaf.naturality (homOfLE (hP V i.1 i.2)).op) u)).symm
      show F.1.map (homOfLE (hP V i.1 i.2)).op (φ.app (b ⁻¹ᵁ V) u) =
        F.1.map (homOfLE (hP V i.1 i.2)).op (ψ.app (b ⁻¹ᵁ V) u)
      exact (nat φ).trans ((heq V i.1 i.2 s).trans (nat ψ).symm)

end AlgebraicGeometry.TateMap
