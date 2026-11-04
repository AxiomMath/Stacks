module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# Effacing a degree-one `Ext`-class between coherent modules by a coherent epimorphism

Let `X` be a scheme and let `F`, `G` be coherent `𝒪_X`-modules. Every class in `Ext^1_X(F, G)`
dies after restriction along an epimorphism `E ⟶ F` **whose source is again coherent**: the class
is the class of an extension `0 → G → E → F → 0` of `F` by `G`, the middle term of such an
extension is coherent because coherent modules are closed under extensions, and the class of an
extension is killed by its own surjection.

## Why the coherence of the effacing module is the point

`Stacks.ExtEffacement.exists_epi_precomp_eq_zero` already effaces a positive-degree class, in
any abelian category with enough injective resolutions, but the epimorphism it produces comes
out of an injective resolution and its source is in no sense coherent — not even
quasi-coherent. That is not enough for the dévissage of [Stacks, Tag 0G2H]: there the effacing
epimorphism `α : F'' ⟶ F` is fed to Artin--Rees, which needs `F''` and `ker α` coherent, and to
the inductive hypothesis of the induction on the degree, which is a statement about coherent
modules. The source of the tag obtains the coherent effacement from
`D^b_{Coh}(𝒪_X) = D^b(Coh(𝒪_X))`, which computes the `Ext`-groups in the abelian category of
coherent modules, where every Yoneda extension has coherent terms by construction.

In degree `1` no such input is needed, because `Ext^1` *is* the group of extensions
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`) and an extension
of a coherent module by a coherent module is coherent
(`AlgebraicGeometry.CoherentAbelian.isCoherent_X₂_of_shortExact`, [Stacks, Tag 01BY] (4)). That
is the whole content of this file. In degrees `≥ 2` a Yoneda extension in `Mod(𝒪_X)`
representing the class has middle terms with no reason to be coherent, and nothing in
`Mod(𝒪_X)` refines them, so the degree-`1` argument does not generalize.

The general-degree statement is
`Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos`, in
`StacksFrontier/AlgebraicGeometry/Duality/ExtensionZeroCoherent/CoherentExtEffacement.lean`. It is
the source's own argument, through `D^b_{Coh}(𝒪_X) = D^b(Coh(𝒪_X))` as described above:
[Stacks, Tag 0FDB] read on `Ext`-groups
(`Stacks.ExtEffacement.bijective_mapExtAddHom_coherentInModules`) moves the class into
`Coh(𝒪_X)`, where every Yoneda extension has coherent terms, and
`CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero` effaces it there. This file stays as it is:
it is the degree-one case with no derived-category input at all.

## Main results

* `Stacks.ExtEffacement.exists_shortExact_isCoherent_extClass_eq`: **a degree-one `Ext`-class
  between coherent modules is the class of an extension by a coherent module.**
* `Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero`: **a degree-one `Ext`-class
  between coherent modules is effaced by an epimorphism from a coherent module.**

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w u

namespace Stacks.ExtEffacement

/-- **A degree-one `Ext`-class between coherent modules is the class of an extension by a
coherent module.** Every element of `Ext^1_X(F, G)` is the class of an extension
`0 → G → E → F → 0` of `F` by `G` ([Stacks, Tag 06XV]), and the middle term of such an extension
is coherent when `F` and `G` are ([Stacks, Tag 01BY] (4)). -/
public theorem exists_shortExact_isCoherent_extClass_eq {X : Scheme.{u}}
    [HasExt.{w} X.Modules] (F G : X.Modules) [hF : F.IsCoherent] [hG : G.IsCoherent]
    (ξ : Ext.{w} F G 1) :
    ∃ (E : X.Modules) (i : G ⟶ E) (p : E ⟶ F) (w : i ≫ p = 0)
      (hS : (ShortComplex.mk i p w).ShortExact), E.IsCoherent ∧ hS.extClass = ξ := by
  obtain ⟨E, i, p, w, hS, hext⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum X.Modules F G).1 ξ
  exact ⟨E, i, p, w, hS,
    AlgebraicGeometry.CoherentAbelian.isCoherent_X₂_of_shortExact hS hG hF, hext⟩

/-- **A degree-one `Ext`-class between coherent modules is effaced by an epimorphism from a
coherent module.** Write the class as the class of an extension `0 → G → E → F → 0`, which
`Stacks.ExtEffacement.exists_shortExact_isCoherent_extClass_eq` does with `E` coherent; the
surjection `E ⟶ F` of an extension kills the class of that extension, which is
`CategoryTheory.ShortComplex.ShortExact.comp_extClass`.

This is the degree-one case of the effacement the dévissage of [Stacks, Tag 0G2H] runs on, and
unlike `Stacks.ExtEffacement.exists_epi_precomp_eq_zero` it produces a *coherent* source, which
is what Artin--Rees and the inductive hypothesis of that dévissage need. -/
public theorem exists_isCoherent_epi_mk₀_comp_eq_zero {X : Scheme.{u}} [HasExt.{w} X.Modules]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (ξ : Ext.{w} F G 1) :
    ∃ (E : X.Modules) (p : E ⟶ F), E.IsCoherent ∧ Epi p ∧
      (Ext.mk₀ p).comp ξ (zero_add 1) = 0 := by
  obtain ⟨E, i, p, w, hS, hcoh, hext⟩ := exists_shortExact_isCoherent_extClass_eq F G ξ
  refine ⟨E, p, hcoh, hS.epi_g, ?_⟩
  rw [← hext]
  exact hS.comp_extClass

end Stacks.ExtEffacement

end
