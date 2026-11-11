module

public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# Sheaves vanishing on the image of a covering family

Let `F : (C, J) ⥤ (D, K)` be a continuous functor of sites which is essentially surjective, and
let `P` be a covering family of objects of `(C, J)`
(`CategoryTheory.GrothendieckTopology.IsCoveringFamily`). A sheaf `G` on `(D, K)` whose sections
vanish over the images `F(Y)` of the objects `Y` with `P` is zero: restricted along `F` it is a
sheaf on `(C, J)` vanishing on a covering family, so its sections vanish over every `F(Y)`, and
every object of `D` is isomorphic to one of these.

The typical application is to an equivalence of sites `F`, along which a covering family of one
site (for instance the affine charts of the small étale site of an algebraic space) is carried to
the other (a small model of it).

## Main results

* `CategoryTheory.Sheaf.isZero_sections_of_isCoveringFamily_of_isContinuous`
* `CategoryTheory.Sheaf.isZero_of_isCoveringFamily_of_isContinuous`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {D : Type*} [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {A : Type*} [Category A] [HasZeroMorphisms A]

/-- **The sections of a sheaf vanish everywhere when they vanish over the image of a covering
family** under a continuous, essentially surjective functor of sites. -/
theorem isZero_sections_of_isCoveringFamily_of_isContinuous (F : C ⥤ D) [F.IsContinuous J K]
    [F.EssSurj] (G : Sheaf K A) {P : ObjectProperty C} (hP : J.IsCoveringFamily P)
    (h : ∀ Y : C, P Y → IsZero (G.obj.obj (op (F.obj Y)))) (X : D) :
    IsZero (G.obj.obj (op X)) := by
  let G' : Sheaf J A := ⟨F.op ⋙ G.obj, F.op_comp_isSheaf J K G⟩
  obtain ⟨R, hR, hRP⟩ := hP (F.objPreimage X)
  have h' : IsZero (G'.obj.obj (op (F.objPreimage X))) :=
    isZero_sections_of_isZero_sections_of_covering G' R hR fun {Y} {_} hf => h Y (hRP hf)
  exact h'.of_iso (G.obj.mapIso (F.objObjPreimageIso X).op)

/-- **A sheaf whose sections vanish over the image of a covering family** under a continuous,
essentially surjective functor of sites **is zero**. -/
theorem isZero_of_isCoveringFamily_of_isContinuous (F : C ⥤ D) [F.IsContinuous J K]
    [F.EssSurj] (G : Sheaf K A) {P : ObjectProperty C} (hP : J.IsCoveringFamily P)
    (h : ∀ Y : C, P Y → IsZero (G.obj.obj (op (F.obj Y)))) : IsZero G :=
  isZero_of_forall_isZero_sections G
    (isZero_sections_of_isCoveringFamily_of_isContinuous F G hP h)

end CategoryTheory.Sheaf

end
