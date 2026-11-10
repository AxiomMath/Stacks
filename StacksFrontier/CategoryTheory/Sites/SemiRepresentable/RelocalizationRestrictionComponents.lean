module

public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.RelocalizationRestriction

/-!
# Restriction along `r_f`, read through the product description of sheaves

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`.
Sheaves on the componentwise localization site `C/M` are families of sheaves on the slice sites
`C/M_i` (`CategoryTheory.SemiRepresentable.restrictSheaf`). This file reads restriction along the
componentwise relocalization functor `r_f` through that description: on the component indexed by
`i` it is the component indexed by `f(i)`, restricted along `Over.map (f.φ i)`.

Both halves are definitional, because `Sigma.incl i ⋙ Sigma.desc F` *is* `F i` and restriction of
sheaves is precomposition of the underlying presheaf: the comparison of the two functors is an
equality, and the comparison of
`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso` with the componentwise
`CategoryTheory.SemiRepresentable.overMapPullbackIso` is the identity on sections.

## Main results

* `CategoryTheory.SemiRepresentable.componentOverMap_sheafPushforwardContinuous_comp_restrictSheaf`
  — restriction along `r_f` followed by the product description of sheaves on `C/M` is the
  product description on `C/N` followed by the componentwise restrictions along the
  `Over.map (f.φ i)`, reindexed along `f`.
* `CategoryTheory.SemiRepresentable.restrictSheaf_map_relocalizationForgetPushforwardIso_hom` and
  `.restrictSheaf_map_relocalizationForgetPushforwardIso_inv`: under that identification, the
  front face `relocalizationForgetPushforwardIso` of the cube of Stacks 0D8E is the family of its
  one-object cases `overMapPullbackIso (f.φ i)`.

## Implementation notes

The first result is an equality of functors proved by `rfl`, not an isomorphism: both sides send a
sheaf `F` on `C/N` to the family `i ↦ (Over.map (f.φ i)).op ⋙ (Sigma.incl (f i)).op ⋙ F.obj` of
restricted presheaves, and send a morphism to the corresponding family of whiskerings.

The second pair is proved on sections. Both isomorphisms are instances of Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`, whose component at a sheaf `X` is
`X.obj` applied to the comparison of the underlying site functors; here those comparisons are
`eqToIso` of an equality whose two sides agree on objects by `rfl`, respectively `Iso.refl`, so
both components are the identity.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

/-- **Restriction along `r_f` is componentwise restriction along the `Over.map (f.φ i)`.** Read
through the product description of sheaves on the componentwise localization sites, restriction
along the componentwise relocalization functor of `f : M ⟶ N` takes the component indexed by
`f(i)` and restricts it along `Over.map (f.φ i)`. -/
theorem componentOverMap_sheafPushforwardContinuous_comp_restrictSheaf :
    (componentOverMap f).sheafPushforwardContinuous (Type u) (componentwiseTopology J M)
          (componentwiseTopology J N) ⋙ restrictSheaf J M (Type u) =
      restrictSheaf J N (Type u) ⋙
        Functor.pi' (fun i : M.I =>
          Pi.eval (fun j : N.I => Sheaf (J.over (N.obj j)) (Type u)) (f.f i) ⋙
            (Over.map (f.φ i)).sheafPushforwardContinuous (Type u)
              (J.over (M.obj i)) (J.over (N.obj (f.f i)))) :=
  rfl

/-- **The front face of the cube of Stacks 0D8E is componentwise its one-object case.** Under the
product description of sheaves on `C/M`, the `i`-th component of
`relocalizationForgetPushforwardIso f` is `overMapPullbackIso (f.φ i)`. -/
theorem restrictSheaf_map_relocalizationForgetPushforwardIso_hom (X : Sheaf J (Type u))
    (i : M.I) :
    (restrictSheaf J M (Type u)).map
          ((relocalizationForgetPushforwardIso J f (componentwiseTopology J M) rfl
            (componentwiseTopology J N) rfl).hom.app X) i =
      (overMapPullbackIso J (f.φ i)).hom.app X := by
  rw [relocalizationForgetPushforwardIso_eq]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun Z => ?_)
  change X.obj.map
      ((eqToIso (componentOverMap_comp_componentOverForget f)).inv.app
        ((CategoryTheory.Sigma.incl (C := fun j : M.I => Over (M.obj j)) i).obj Z.unop)).op =
    X.obj.map ((Iso.refl (Over.map (f.φ i) ⋙ Over.forget (N.obj (f.f i)))).inv.app Z.unop).op
  have hid : (eqToIso (componentOverMap_comp_componentOverForget f)).inv.app
        ((CategoryTheory.Sigma.incl (C := fun j : M.I => Over (M.obj j)) i).obj Z.unop) =
      𝟙 (Z.unop.left) := by
    simp only [eqToIso.inv, eqToHom_app]
    rfl
  rw [hid, show (Iso.refl (Over.map (f.φ i) ⋙ Over.forget (N.obj (f.f i)))).inv.app Z.unop =
      𝟙 (Z.unop.left) from rfl]
  rfl

/-- The inverse form of `restrictSheaf_map_relocalizationForgetPushforwardIso_hom`. -/
theorem restrictSheaf_map_relocalizationForgetPushforwardIso_inv (X : Sheaf J (Type u))
    (i : M.I) :
    (restrictSheaf J M (Type u)).map
          ((relocalizationForgetPushforwardIso J f (componentwiseTopology J M) rfl
            (componentwiseTopology J N) rfl).inv.app X) i =
      (overMapPullbackIso J (f.φ i)).inv.app X := by
  rw [relocalizationForgetPushforwardIso_eq]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun Z => ?_)
  change X.obj.map
      ((eqToIso (componentOverMap_comp_componentOverForget f)).hom.app
        ((CategoryTheory.Sigma.incl (C := fun j : M.I => Over (M.obj j)) i).obj Z.unop)).op =
    X.obj.map ((Iso.refl (Over.map (f.φ i) ⋙ Over.forget (N.obj (f.f i)))).hom.app Z.unop).op
  have hid : (eqToIso (componentOverMap_comp_componentOverForget f)).hom.app
        ((CategoryTheory.Sigma.incl (C := fun j : M.I => Over (M.obj j)) i).obj Z.unop) =
      𝟙 (Z.unop.left) := by
    simp only [eqToIso.hom, eqToHom_app]
    rfl
  rw [hid, show (Iso.refl (Over.map (f.φ i) ⋙ Over.forget (N.obj (f.f i)))).hom.app Z.unop =
      𝟙 (Z.unop.left) from rfl]
  rfl

end CategoryTheory.SemiRepresentable

end
