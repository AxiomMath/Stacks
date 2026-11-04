module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSlice

/-!
# Restriction from the slice at a subterminal sheaf is fully faithful

Let `F` be a presheaf of sets on a site `(C, J)` whose values are subsingletons, and let
`j : D ⥤ C` be a fully faithful functor whose essential image is the support of `F`.  A sheaf
over `F` has no sections outside that essential image, so a morphism between two such sheaves is
determined by, and may be built from, its restriction along `j`.  That is the content of this
file: the comparison functor `Sh(C)/F ⥤ Sh(D)` of restriction along `j` is fully faithful.

## Main results

* `CategoryTheory.Stacks.Topos.Subterminal.sliceRestriction` — the comparison functor.
* `CategoryTheory.Stacks.Topos.Subterminal.faithful_sliceRestriction` and
  `CategoryTheory.Stacks.Topos.Subterminal.full_sliceRestriction`.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Stacks.Topos.Subterminal

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : Cᵒᵖ ⥤ Type w} {j : D ⥤ C} [j.Full] [j.Faithful]
  [∀ X : Cᵒᵖ, Subsingleton (F.obj X)]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [j.IsContinuous K J]
  (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U) (hF : Presheaf.IsSheaf J F)

/-- **Restriction along `j`, read on the slice at `F`.**  A sheaf over `F` is forgotten to a
sheaf on `C` and restricted along `j`. -/
noncomputable abbrev sliceRestriction :
    Over (⟨F, hF⟩ : Sheaf J (Type w)) ⥤ Sheaf K (Type w) :=
  Over.forget _ ⋙ j.sheafPushforwardContinuous (Type w) K J

omit [j.Full] [j.Faithful] [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
include hsupp in
/-- A sheaf over `F` is supported on the essential image of `j`: a section of it over `U` maps
to a section of `F` over `U`, and `F` has one only on that essential image. -/
theorem essImage_of_over (T : Over (⟨F, hF⟩ : Sheaf J (Type w))) (U : Cᵒᵖ)
    (t : T.left.obj.obj U) : j.essImage U.unop :=
  hsupp U.unop ⟨T.hom.hom.app U t⟩

omit [j.Full] [j.Faithful] [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
include hsupp in
/-- **Two morphisms of sheaves over `F` are equal as soon as their restrictions along `j` are.** -/
theorem over_hom_ext {T T' : Over (⟨F, hF⟩ : Sheaf J (Type w))} {α β : T ⟶ T'}
    (hres : (sliceRestriction (j := j) (K := K) hF).map α =
      (sliceRestriction (j := j) (K := K) hF).map β) : α = β := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine natTrans_ext_of_essImage (fun {U} t ↦ essImage_of_over hsupp hF T (op U) t) fun B ↦ ?_
  exact congrArg (fun m ↦ NatTrans.app (InducedCategory.Hom.hom m) (op B)) hres

omit [j.Full] [j.Faithful] [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
include hsupp in
/-- Restriction along `j` from sheaves over `F` to sheaves on `D` is faithful. -/
theorem faithful_sliceRestriction : (sliceRestriction (j := j) (K := K) hF).Faithful where
  map_injective := over_hom_ext hsupp hF

omit [j.Faithful] in
include hsupp in
/-- **Every morphism between the restrictions comes from one over `F`.** Restriction along `j`
from sheaves over `F` to sheaves on `D` is full. -/
theorem full_sliceRestriction : (sliceRestriction (j := j) (K := K) hF).Full where
  map_surjective {T T'} γ := by
    refine ⟨Over.homMk (ObjectProperty.homMk (extendNatTrans T.left.obj T'.left.obj
      (fun U t ↦ essImage_of_over hsupp hF T U t) γ.hom)) ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      ext U t
      exact Subsingleton.elim _ _
    · apply ObjectProperty.hom_ext
      exact whiskerLeft_extendNatTrans T.left.obj T'.left.obj _ γ.hom

end Stacks.Topos.Subterminal

end CategoryTheory

end
