module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Glueing a morphism out of a tensor product sheaf: the local datum on pure tensors

`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/Restrict.lean` glues a family of morphisms of the
restrictions of two sheaves of modules to the members of a cover, and the compatibility it asks
for is an identity of `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp`s: the two members act
equally on the sections over an open of the base seen by both charts.

When the source is a *tensor product* sheaf that identity is out of reach directly, because a
section of a tensor product sheaf over an open is not a pure tensor — the sheaf is a
sheafification, and a section is only locally a finite sum of pure tensors. This file reduces the
identity to the pure tensors, which is the form in which a comparison morphism out of a tensor
product is ever computable.

The reduction is not an application of a `hom_ext` principle for tensor sheaves such as
`AlgebraicGeometry.RingedSpaceThickening.tensorSheaf_hom_ext`: those compare two *morphisms of
sheaves*, while a `localApp` is a map on the sections over one open and is not the action of a
morphism of sheaves on the source. What makes the reduction work instead is that a `localApp`
commutes with the restriction maps (`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_map`) and
that the target is a sheaf, so the identity is local on the open; and locally the section becomes
a finite sum of pure tensors by
`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_eq_of_toTensorSheafSection`: **two morphisms
  of the restrictions of a tensor product sheaf to two open subschemes have the same `localApp` on
  a common image open as soon as their `localApp`s agree on the images of pure tensors of local
  sections over the opens below it.** Nothing is assumed of the scheme, of the two open
  immersions, or of the three sheaves of modules.

## Implementation notes

The covering sieve produced by `exists_sieve_sum_toTensorSheafSection` is turned into an indexed
family of opens by choosing, for each point of the open, a member of the sieve containing it:
membership of a sieve in `TopologicalSpace.Opens.grothendieckTopology` is exactly that statement
pointwise, so the family is indexed by the points of the open and its supremum contains the open.
The separation half of the sheaf axiom is then `TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`,
as in `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine`.

The sum is distributed over the two `localApp`s by `map_sum` applied outright rather than by
`rw`: rewriting with `map_sum` here leaves a goal that is not type-correct, because the two
spellings `AlgebraicGeometry.Scheme.ringCatSheaf` and `CategoryTheory.Sheaf.toRingCat` of the
structure ring sheaf are interchanged by the rewrite and instance search does not follow.

The source is written `AlgebraicGeometry.Scheme.Modules.restrict` applied to the tensor product
sheaf rather than with dot notation: the tensor product is typed over
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` of the underlying ringed space,
which is the same sheaf of rings as the scheme's but is not the spelling that resolves the field
`restrict`.

## No tag is claimed

No `stacks` attribute is attached, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/Basic.lean`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- Restricting a `localApp` to a smaller open is the sum of the `localApp`s of the pieces, when
the restriction of the section is such a sum. -/
private theorem restrict_localApp_eq_sum {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (ψ : M.restrict f ⟶ N.restrict f) {V B : Y.Opens} (hV : V ≤ f ''ᵁ ⊤)
    (hB : B ≤ V) {s : Γ(M, V)} {n : ℕ} {m : Fin n → Γ(M, B)}
    (hs : M.presheaf.map (homOfLE hB).op s = ∑ j, m j) :
    N.presheaf.map (homOfLE hB).op (localApp f ψ (image_preimage_eq_self f hV) s) =
      ∑ j, localApp f ψ (image_preimage_eq_self f (hB.trans hV)) (m j) := by
  rw [← localApp_map f ψ (image_preimage_eq_self f hV) (image_preimage_eq_self f (hB.trans hV)) hB,
    hs]
  exact map_sum (ConcreteCategory.hom (localApp f ψ (image_preimage_eq_self f (hB.trans hV)))) _ _

/-- **Two morphisms of the restrictions of a tensor product sheaf to two open subschemes have the
same action on the sections over a common image open as soon as they agree on the images of pure
tensors of local sections.** -/
public theorem localApp_eq_of_toTensorSheafSection {X Z₁ Z₂ : Scheme.{u}}
    (f : Z₁ ⟶ X) (g : Z₂ ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    {F G N : X.Modules}
    (ψ : Scheme.Modules.restrict ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) f ⟶
      N.restrict f)
    (ψ' : Scheme.Modules.restrict ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) g ⟶
      N.restrict g)
    {V : X.Opens} {W₁ : Z₁.Opens} {W₂ : Z₂.Opens}
    (h₁ : f ''ᵁ W₁ = V) (h₂ : g ''ᵁ W₂ = V)
    (hpt : ∀ (V₀ : X.Opens) (p₁ : f ''ᵁ (f ⁻¹ᵁ V₀) = V₀) (p₂ : g ''ᵁ (g ⁻¹ᵁ V₀) = V₀)
      (a : ToType (F.val.obj (op V₀))) (b : ToType (G.val.obj (op V₀))),
      localApp f ψ p₁ (toTensorSheafSection X.toRingedSpace F G (op V₀) (a ⊗ₜ b))
        = localApp g ψ' p₂ (toTensorSheafSection X.toRingedSpace F G (op V₀) (a ⊗ₜ b))) :
    localApp f ψ h₁ = localApp g ψ' h₂ := by
  have hVf : V ≤ f ''ᵁ (⊤ : Z₁.Opens) := h₁ ▸ Scheme.Hom.image_mono f le_top
  have hVg : V ≤ g ''ᵁ (⊤ : Z₂.Opens) := h₂ ▸ Scheme.Hom.image_mono g le_top
  rw [localApp_congr f ψ h₁ (image_preimage_eq_self f hVf),
    localApp_congr g ψ' h₂ (image_preimage_eq_self g hVg)]
  refine ConcreteCategory.hom_ext _ _ fun t => ?_
  obtain ⟨S, hS, hsum⟩ := Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection
    X.toRingedSpace F G V t
  choose B kB hkB hxB using fun x : V => hS x.1 x.2
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf N.isSheaf
    (fun x : V => B x) (fun x => (kB x).le) (fun y hy => ?_) fun x => ?_
  · exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxB ⟨y, hy⟩⟩
  obtain ⟨n, a, b, hab⟩ := hsum (kB x) (hkB x)
  have hBV : B x ≤ V := (kB x).le
  refine (restrict_localApp_eq_sum f ψ hVf hBV hab).trans (Eq.trans ?_
    (restrict_localApp_eq_sum g ψ' hVg hBV hab).symm)
  exact Finset.sum_congr rfl fun j _ => hpt (B x) _ _ (a j) (b j)

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
