module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic

/-!
# Morphisms into a torsion-free module, and into the structure sheaf

Let `X` be a scheme. A morphism of `𝒪_X`-modules from a torsion module, every local section of
which is torsion in the sense of `IsTorsionSection`, to a torsion-free module is zero. On a
preirreducible scheme, a morphism whose source vanishes on a nonempty open and whose target has
injective restriction maps to nonempty opens is zero. The structure sheaf of an integral scheme
has injective restriction maps to nonempty opens, so on an integral scheme every morphism into
`𝒪_X` from a module vanishing on a nonempty open is zero.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.hom_eq_zero_of_isTorsionFree`: a morphism from a
  torsion module to a torsion-free module is zero.
* `Stacks.AlgebraicGeometry.ReflexiveModules.hom_eq_zero_of_eq_zero_on_nonempty_open`: on a
  preirreducible space, a morphism whose source vanishes on a nonempty open and whose target
  has injective restriction maps to nonempty opens is zero.
* `Stacks.AlgebraicGeometry.ReflexiveModules.unitModule_presheaf_map_injective`: on an integral
  scheme the restriction maps of the structure sheaf, viewed as a module over itself, to
  nonempty opens are injective.
* `Stacks.AlgebraicGeometry.ReflexiveModules.hom_unitModule_eq_zero_of_eq_zero_on_nonempty_open`:
  on an integral scheme, a morphism into the structure sheaf from a module vanishing on a
  nonempty open is zero.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- If every local section of `F` is torsion and `G` is torsion free, then every morphism
`F ⟶ G` is zero. -/
theorem hom_eq_zero_of_isTorsionFree {F G : X.Modules}
    (hF : ∀ (U : X.Opens) (s : Γ(F, U)), IsTorsionSection F s)
    (hG : IsTorsionFree G) (φ : F ⟶ G) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [Scheme.Modules.Hom.zero_app]
  ext s
  refine hG U (Scheme.Modules.Hom.app φ U s) fun x hx ↦ ?_
  obtain ⟨W, hWU, hxW, a, hga, has⟩ := exists_annihilator_of_isTorsionSection hx (hF U s x hx)
  refine ⟨X.presheaf.germ W x hxW a, hga, ?_⟩
  have hres : G.presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app φ U s) =
      Scheme.Modules.Hom.app φ W (F.presheaf.map (homOfLE hWU).op s) :=
    (PresheafOfModules.naturality_apply φ.val (homOfLE hWU).op s).symm
  have hzero : G.presheaf.germ W x hxW
      (a • Scheme.Modules.Hom.app φ W (F.presheaf.map (homOfLE hWU).op s)) = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, has, map_zero, map_zero]
  rw [← G.presheaf.germ_res_apply (homOfLE hWU) x hxW, hres]
  exact (G.val.germ_smul x W hxW a _).symm.trans hzero

/-- On a preirreducible scheme, a morphism `F ⟶ G` is zero when every section of `F` over an
open contained in a nonempty open `W` is zero and the restriction maps of `G` to nonempty opens
are injective. -/
theorem hom_eq_zero_of_eq_zero_on_nonempty_open [PreirreducibleSpace X] {F G : X.Modules}
    (hG : ∀ {U V : X.Opens} (i : V ⟶ U), Nonempty V → Function.Injective (G.presheaf.map i.op))
    {W : X.Opens} [hW : Nonempty W]
    (hF : ∀ V ≤ W, ∀ s : Γ(F, V), s = 0) (φ : F ⟶ G) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [Scheme.Modules.Hom.zero_app]
  ext s
  show Scheme.Modules.Hom.app φ U s = 0
  rcases isEmpty_or_nonempty U with hUe | hUne
  · have h0 : U = ⊥ := by
      rw [← Opens.not_nonempty_iff_eq_bot]
      exact fun hne ↦ hUe.false ⟨hne.some, hne.some_mem⟩
    rw [hF U (h0 ▸ bot_le) s, map_zero]
  · have hinf : ((U ⊓ W : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter U.isOpen W.isOpen
        (Set.nonempty_coe_sort.mp hUne) (Set.nonempty_coe_sort.mp hW)
    have hres : F.presheaf.map (homOfLE (inf_le_left : (U ⊓ W : X.Opens) ≤ U)).op s = 0 :=
      hF (U ⊓ W) inf_le_right _
    refine hG (homOfLE (inf_le_left : (U ⊓ W : X.Opens) ≤ U))
      (Set.nonempty_coe_sort.mpr hinf) ?_
    rw [map_zero, ← Scheme.Modules.Hom.app_presheaf_map, hres, map_zero]

/-- On an integral scheme, a morphism into the structure sheaf from a module whose sections over
every open contained in a nonempty open `W` are zero is itself zero. -/
theorem hom_unitModule_eq_zero_of_eq_zero_on_nonempty_open [IsIntegral X] {F : X.Modules}
    {W : X.Opens} [Nonempty W] (hF : ∀ V ≤ W, ∀ s : Γ(F, V), s = 0)
    (φ : F ⟶ X.unitModule) : φ = 0 :=
  hom_eq_zero_of_eq_zero_on_nonempty_open
    (fun i hV ↦ let := hV; (map_injective_of_isIntegral _) i) (W := W) hF φ

end Stacks.AlgebraicGeometry.ReflexiveModules

end
