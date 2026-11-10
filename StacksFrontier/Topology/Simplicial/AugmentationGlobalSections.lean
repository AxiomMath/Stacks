module

public import StacksFrontier.Topology.Simplicial.AugmentationFibrePartTwo
public import StacksFrontier.Topology.Simplicial.AugmentationFibreCohomology

/-!
# Global sections of the direct image along an augmentation

Let `X` be a simplicial topological space and `a : X → Y` an augmentation, with morphism of topoi
`a : Sh(X_Zar) → Sh(Y)` of Stacks 09W4. The global sections of `a_*F` are the global sections of
`F`:

`Γ(Y, a_*F) = Γ(X_Zar, F)`,

naturally in the abelian sheaf `F` on `X_Zar`. This is the underived identity behind
`RΓ(X_Zar, -) = RΓ(Y, -) ∘ Ra_*` (Cohomology on Sites, Remark 21.14.4, Stacks 08J6).

## Main definitions

* `fibreImageEquivalenceTop`: over the whole target, the comparison of sites of the fibre is an
  equivalence.
* `augmentationPushforwardAbGlobalSectionsIso`: the natural isomorphism
  `Γ(Y, a_*F) ≅ Γ(X_Zar, F)`.

## Implementation notes

By part (2) of the proof of Stacks 0D84
(`Stacks.Topology.Simplicial.augmentationFibreSections_iso_fibreRestrictedSections`), the
sections of `a_*F` over an open `V` of `Y` are the global sections of the restriction of `F` to
the fibre `X ×_Y V`. Over `V = Y` the comparison of sites `(X ×_Y Y)_Zar → X_Zar` is an
equivalence, its quasi-inverse being intersection with the fibre, so the restriction has the
global sections of `F`: global sections are limits over the site, and a limit is unchanged by
precomposition with an initial functor.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y)

/-- Over the whole target, the comparison of sites of the fibre is left adjoint to intersection
with the fibre with an invertible unit. -/
theorem isIso_fibreImageAdjunction_unit_top (W : SimplicialOpen (fibreSpace X Y a ⊤)) :
    IsIso ((fibreImageAdjunction X Y a ⊤).unit.app W) := by
  refine ⟨⟨{ base := 𝟙 W.degree
             le := by
               rintro x ⟨z, hz, hzx⟩
               obtain rfl := fibrePt_injective X Y a ⊤ W.degree hzx
               change (fibreSpace X Y a ⊤).map (𝟙 W.degree) z ∈ W.toOpens
               rwa [ConcreteCategory.congr_hom ((fibreSpace X Y a ⊤).map_id W.degree) z] },
      ?_, ?_⟩⟩ <;>
    exact SimplicialOpen.Hom.ext _ _ (Category.id_comp _)

/-- Over the whole target, the comparison of sites of the fibre is an equivalence. -/
def fibreImageEquivalenceTop : SimplicialOpen (fibreSpace X Y a ⊤) ≌ SimplicialOpen X :=
  have := isIso_fibreImageAdjunction_unit_top X Y a
  have : ∀ U, IsIso ((fibreImageAdjunction X Y a ⊤).counit.app U) := fun U =>
    isIso_fibreImageAdjunction_counit X Y a ⊤ (U := U) (fun _ _ => trivial)
  (fibreImageAdjunction X Y a ⊤).toEquivalence

/-- Over the whole target, the opposite of the comparison of sites of the fibre is an initial
functor. -/
instance initial_fibreImage_top_op : (fibreImage X Y a ⊤).op.Initial :=
  have : (fibreImage X Y a ⊤).op.IsLeftAdjoint :=
    ((fibreImageEquivalenceTop X Y a).symm.toAdjunction.op).isLeftAdjoint
  inferInstance

/-- Global sections of the restriction to the fibre over the whole target are global sections. -/
def fibreRestrictedSectionsTopIso :
    fibreRestrictedSections X Y a ⊤ ≅ Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{u} :=
  Functor.isoWhiskerLeft (fibreRestrictionAb X Y a ⊤)
      (Sheaf.ΓNatIsoLim (SimplicialOpen.grothendieckTopology (fibreSpace X Y a ⊤)) Ab.{u}) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) Ab.{u})
      (Functor.Initial.limIso (fibreImage X Y a ⊤).op) ≪≫
    (Sheaf.ΓNatIsoLim (SimplicialOpen.grothendieckTopology X) Ab.{u}).symm

/-- **`Γ(Y, a_*F) = Γ(X_Zar, F)`**, naturally in the abelian sheaf `F` on `X_Zar`, for an
augmentation `a : X → Y` of a simplicial space. -/
def augmentationPushforwardAbGlobalSectionsIso :
    augmentationPushforwardAb X Y a ⋙ Sheaf.Γ (Opens.grothendieckTopology Y) Ab.{u} ≅
      Sheaf.Γ (SimplicialOpen.grothendieckTopology X) Ab.{u} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop) ≪≫
    (augmentationFibreSections_iso_fibreRestrictedSections X Y a ⊤ :) ≪≫
    fibreRestrictedSectionsTopIso X Y a

end Stacks.Topology.Simplicial

end
