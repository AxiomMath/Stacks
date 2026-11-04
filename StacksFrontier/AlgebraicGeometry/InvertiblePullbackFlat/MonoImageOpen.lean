module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators

/-!
# The largest open on which a section lifts along a monomorphism of sheaves of modules

Let `φ : ℱ ⟶ 𝒢` be a monomorphism of sheaves of modules on a topological space and `σ` a section
of `𝒢` over an open `P`. The opens `W ≤ P` on which `σ` lifts to a section of `ℱ` are closed
under passing to a larger one: the lifts over two such opens agree on the intersection, because
`φ` is injective on sections there, so they glue. The union of all of them therefore carries a
lift, and every lift is a restriction of that one.

This is what the penultimate paragraph of [Stacks, Tag 0BD7] needs of `φ^*(g) s`. That argument
produces, at each point of `X`, *some* open on which the product is a regular section; the
saturation argument of the last paragraph needs the product to be regular on every open where it
could be, since a point of a fibre at which it is regular has to be compared with a point
elsewhere on the same fibre. The open produced here is that largest one.

## Main results

* `Stacks.SheafOfModules.exists_le_forall_le_map_eq_app`: the largest open with a lift, with the
  lift, and with the restriction property that makes it largest.

## Implementation notes

The gluing is `TopCat.Sheaf.existsUnique_gluing` for the underlying presheaf of abelian groups,
whose sheaf condition is the field `SheafOfModules.isSheaf`; the index type is the opens that
carry a lift, with the lift chosen by `choose`. Injectivity on sections is
`CategoryTheory.SheafOfModules.app_injective_of_mono`, and it is used twice: once for the
compatibility of the chosen lifts and once to identify an arbitrary lift with the chosen one.

Restrictions are written with `PresheafOfModules.map` and the inclusions are left as arbitrary
morphisms of opens wherever possible, since `Opens` morphisms are a subsingleton and a general
morphism saves converting `TopologicalSpace.Opens.infLELeft` and
`TopologicalSpace.Opens.leSupr` into `homOfLE` form inside the proof.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {T : Type u} [TopologicalSpace T]
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    [HasWeakSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
    {N₁ N₂ : _root_.SheafOfModules.{u} R}

/-- **The largest open on which a section lifts along a monomorphism.** For `φ : ℱ ⟶ 𝒢` a
monomorphism of sheaves of modules and `σ` a section of `𝒢` over `P`, there is an open `V ≤ P`
carrying a lift of `σ|_V` such that every open `W ≤ P` carrying a lift is contained in `V`, with
its lift the restriction of the one over `V`. -/
theorem exists_le_forall_le_map_eq_app (φ : N₁ ⟶ N₂) (hφ : Mono φ)
    (P : Opens T) (σ : N₂.val.obj (op P)) :
    ∃ (V : Opens T) (hVP : V ≤ P) (u : N₁.val.obj (op V)),
      N₂.val.map (homOfLE hVP).op σ = φ.val.app (op V) u ∧
        ∀ (W : Opens T) (hWP : W ≤ P) (v : N₁.val.obj (op W)),
          N₂.val.map (homOfLE hWP).op σ = φ.val.app (op W) v →
          ∃ hWV : W ≤ V, N₁.val.map (homOfLE hWV).op u = v := by
  classical
  have hinj := CategoryTheory.SheafOfModules.app_injective_of_mono hφ
  have hres : ∀ (W₁ W₂ : Opens T) (h₁ : W₁ ≤ P) (l : W₂ ⟶ W₁) (h₃ : W₂ ≤ P),
      N₂.val.map l.op (N₂.val.map (homOfLE h₁).op σ) = N₂.val.map (homOfLE h₃).op σ :=
    fun W₁ W₂ h₁ l h₃ => (N₂.val.map_comp_apply (homOfLE h₁).op l.op σ).symm.trans
      (N₂.val.congr_map_apply (Subsingleton.elim _ _) σ)
  let Ix : Type u := {W : Opens T // ∃ (hWP : W ≤ P) (v : N₁.val.obj (op W)),
    N₂.val.map (homOfLE hWP).op σ = φ.val.app (op W) v}
  choose hleP w hw using fun i : Ix => i.2
  have key : ∀ (k : Ix) (W : Opens T) (l : W ⟶ (k : Opens T)) (hWP : W ≤ P),
      N₂.val.map l.op (φ.val.app (op (k : Opens T)) (w k))
        = N₂.val.map (homOfLE hWP).op σ :=
    fun k W l hWP => (congrArg (fun x => N₂.val.map l.op x) (hw k)).symm.trans
      (hres (k : Opens T) W (hleP k) l hWP)
  have hcpt0 : ∀ (i j : Ix) (W : Opens T) (lL : W ⟶ (i : Opens T)) (lR : W ⟶ (j : Opens T))
      (hWP : W ≤ P), N₁.val.map lL.op (w i) = N₁.val.map lR.op (w j) :=
    fun i j W lL lR hWP => hinj (op W)
      ((PresheafOfModules.naturality_apply φ.val lL.op (w i)).trans
        ((key i W lL hWP).trans ((key j W lR hWP).symm.trans
          (PresheafOfModules.naturality_apply φ.val lR.op (w j)).symm)))
  have hglue : ∀ (i : Ix) (V : Opens T) (hVP : V ≤ P) (l : (i : Opens T) ⟶ V)
      (uu : N₁.val.obj (op V)), N₁.val.map l.op uu = w i →
      N₂.val.map l.op (N₂.val.map (homOfLE hVP).op σ)
        = N₂.val.map l.op (φ.val.app (op V) uu) := by
    intro i V hVP l uu hl
    exact (hres V (i : Opens T) hVP l (hleP i)).trans ((hw i).trans
      ((congrArg (fun x => φ.val.app (op (i : Opens T)) x) hl).symm.trans
        (PresheafOfModules.naturality_apply φ.val l.op uu)))
  have hcpt : TopCat.Presheaf.IsCompatible (X := TopCat.of T) N₁.val.presheaf
      (Subtype.val : Ix → Opens T) w := fun i j =>
    hcpt0 i j _ _ _ (le_trans inf_le_left (hleP i))
  obtain ⟨u, hu, -⟩ := TopCat.Sheaf.existsUnique_gluing
    (⟨N₁.val.presheaf, N₁.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of T))
    (Subtype.val : Ix → Opens T) w hcpt
  refine ⟨iSup (Subtype.val : Ix → Opens T), iSup_le hleP, u, ?_, ?_⟩
  · exact TopCat.Sheaf.eq_of_locally_eq
      (⟨N₂.val.presheaf, N₂.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of T))
      (Subtype.val : Ix → Opens T) _ _ fun i => hglue i _ (iSup_le hleP) _ u (hu i)
  · intro W hWP v h
    refine ⟨le_iSup (Subtype.val : Ix → Opens T) ⟨W, hWP, v, h⟩, ?_⟩
    exact (N₁.val.congr_map_apply (Subsingleton.elim _ _) u).trans
      ((hu ⟨W, hWP, v, h⟩).trans (hinj (op W) ((hw ⟨W, hWP, v, h⟩).symm.trans h)))

end Stacks.SheafOfModules

end
