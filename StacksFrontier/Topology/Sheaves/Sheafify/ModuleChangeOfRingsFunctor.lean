module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0088 — the constructions of "Sheafification of presheaves of modules"

Section 6.20 of the Stacks Project (tag 0088) contains, besides its three numbered lemmas
0089, 008A and 008B, three constructions. For a morphism `O₁ ⟶ O₂` of sheaves of rings on a
topological space `X`:

* the **restriction functor** `Mod(O₂) ⥤ Mod(O₁)`. The section's observation is that
  restriction of scalars of a sheaf of `O₂`-modules is again a *sheaf* of `O₁`-modules, so the
  presheaf-level functor of Section 006P descends to sheaves;
* the **tensor product sheaf**
  `O₂ ⊗_{O₁} G = (O₂ ⊗_{p, O₁} G)^#`,
  defined as the sheafification of the presheaf-level change of rings of Section 006P, the
  presheaf `O₂ ⊗_{p, O₁} G` being in general not a sheaf; and
* the resulting **change of rings functor** `Mod(O₁) ⥤ Mod(O₂)`.

All three are already constructed on this branch, so nothing is rebuilt here; this file only
attaches tag 0088 to them, so that the development does not acquire a second restriction,
tensor product or change-of-rings functor for sheaves of modules.

## Main results

Tag 0088 is registered against:

* `SheafOfModules.restrictScalars` — Mathlib's restriction functor `Mod(O₂) ⥤ Mod(O₁)` along a
  morphism of sheaves of rings on a site. Its `obj` keeps the sheaf condition of the source,
  which is the section's observation.
* `Stacks.Sheafify.ModuleStalkTensor.tensorSheaf` — the tensor product sheaf `O₂ ⊗_{O₁} G` on a
  topological space, built as the sheafification of the explicit sectionwise presheaf
  `U ↦ O₂(U) ⊗_{O₁(U)} G(U)`. This is the object tags 008A and 008B are stated about, in
  `StacksFrontier/Topology/Sheaves/Sheafify/ModuleChangeOfRingsSheaf.lean` and in
  `StacksFrontier/Topology/Sheaves/Sheafify/ModuleStalkTensor.lean` respectively.
* `Stacks.Sheaves.ModuleAdjunction.extendScalars` — the change of rings functor
  `Mod(O₁) ⥤ Mod(O₂)` for sheaves of rings on an arbitrary small site, hence in particular on
  the site of opens of `X`. That it is the section's functor, namely sheafification of the
  presheaf-level change of rings, is
  `Stacks.Sheaves.ModuleAdjunction.extendScalarsIso`; that it is left adjoint to restriction of
  scalars (Lemma 008A) is `Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction`.

## Implementation notes

The functor is taken at the site-level generality of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposModuleAdjunction.lean` rather than
re-specialised to a topological space. That file's `extendScalars` is stated for an arbitrary
small site `(C, J)` and arbitrary (not necessarily commutative) sheaves of rings
`R₁ R₂ : Sheaf J RingCat`, which covers the section's hypotheses — a sheaf of modules on `X` is
a sheaf of modules for `Opens.grothendieckTopology X` — and is strictly more general than them.

The two models of `O₂ ⊗_{p,O₁} G` present in the development, the explicit sectionwise one of
`Stacks.Sheafify.ModuleStalkTensor.tensorPresheafOfModules` and the abstract left adjoint of
restriction of scalars registered against tag 006R, agree, both being left adjoint to
restriction of scalars; no comparison isomorphism between their sheafifications is constructed
here.
-/

@[expose] public section

add_to_stacks 0088 "the restriction functor `Mod(O₂) ⥤ Mod(O₁)`"
  SheafOfModules.restrictScalars
add_to_sga "4 IV 11.1.4" SheafOfModules.restrictScalars
add_to_sga "4 IV 11.1.5" SheafOfModules.restrictScalars
add_to_sga "4 IV 13.2.1" "special case" SheafOfModules.restrictScalars
add_to_sga "4 XVIII 3.1.12.1" SheafOfModules.restrictScalars

add_to_stacks 0088 "the tensor product sheaf `O₂ ⊗_{O₁} G = (O₂ ⊗_{p,O₁} G)^#`, at the explicit
  sectionwise model of the presheaf tensor product"
  Stacks.Sheafify.ModuleStalkTensor.tensorSheaf

add_to_stacks 0088 "the change of rings functor `Mod(O₁) ⥤ Mod(O₂)`"
  Stacks.Sheaves.ModuleAdjunction.extendScalars


end
