module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport

/-!
# Vanishing of right derived functors along an equivalence of the source

Let `Φ : C ⥤ C'` be an additive equivalence of abelian categories with injective resolutions,
let `F : C ⥤ D` and `F' : C' ⥤ D'` be additive functors, and let `E : D' ⥤ D` be an additive
functor preserving homology which reflects zero objects (for instance a restriction of
scalars). If `F ≅ Φ ⋙ F' ⋙ E`, then for every object `X` of `C` and every `n`

`Rⁿ F (X) = 0 ↔ Rⁿ F' (Φ X) = 0`.

This is the shape of the comparison of cohomology along an equivalence of sites, where `F` and
`F'` are the global sections over the two sites and `E` restricts scalars along the ring map of
global sections.

## Main results

* `CategoryTheory.Functor.isZero_rightDerived_obj_iff_of_iso_comp`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {C' : Type*} [Category* C'] [Abelian C'] [HasInjectiveResolutions C']
  {D : Type*} [Category* D] [Abelian D] {D' : Type*} [Category* D'] [Abelian D']

/-- **Vanishing of right derived functors is transported along an equivalence of the source.**
If `Φ : C ⥤ C'` is an additive equivalence, `E : D' ⥤ D` an additive functor preserving homology
and reflecting zero objects, and `F ≅ Φ ⋙ F' ⋙ E`, then `Rⁿ F (X)` vanishes exactly when
`Rⁿ F' (Φ X)` does. -/
theorem isZero_rightDerived_obj_iff_of_iso_comp (Φ : C ⥤ C') [Φ.IsEquivalence] [Φ.Additive]
    (F : C ⥤ D) (F' : C' ⥤ D') (E : D' ⥤ D) [F.Additive] [F'.Additive] [E.Additive]
    [E.PreservesHomology] (hE : ∀ Y : D', IsZero (E.obj Y) → IsZero Y)
    (e : F ≅ Φ ⋙ F' ⋙ E) (X : C) (n : ℕ) :
    IsZero ((F.rightDerived n).obj X) ↔ IsZero ((F'.rightDerived n).obj (Φ.obj X)) := by
  have : Φ.PreservesInjectiveObjects := inferInstance
  have : Φ.PreservesHomology := inferInstance
  rw [((Functor.rightDerivedIsoOfNatIso e n).app X).isZero_iff,
    ((Φ.compRightDerivedIso (F' ⋙ E) n).app X).isZero_iff]
  change IsZero (((F' ⋙ E).rightDerived n).obj (Φ.obj X)) ↔ _
  rw [((Functor.rightDerivedCompIso F' E n).app (Φ.obj X)).isZero_iff]
  exact ⟨hE _, E.map_isZero⟩

end CategoryTheory.Functor

end
