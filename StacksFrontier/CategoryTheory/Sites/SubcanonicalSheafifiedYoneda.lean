module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Sheafified representables over a subcanonical site

On a subcanonical site the representable presheaf `h_U` is already a sheaf, so sheafifying it
changes nothing: the sheafified Yoneda embedding `U ↦ h_U^#`
(`CategoryTheory.Sheaf.sheafifiedYoneda`) agrees with the direct Yoneda embedding into sheaves
(`CategoryTheory.GrothendieckTopology.uliftYoneda`), and is therefore fully faithful.

## Main definitions

* `CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`: the comparison isomorphism.

## Implementation notes

The isomorphism is the counit of the sheafification adjunction, which is invertible because
sheafification is reflective, transported along
`CategoryTheory.GrothendieckTopology.uliftYonedaCompSheafToPresheaf`, the identification of the
underlying presheaf of `h_U` with `h_U` itself which subcanonicity provides.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.Subcanonical] [HasWeakSheafify J (Type max u v)]

/-- On a subcanonical site the sheafified Yoneda embedding `U ↦ h_U^#` agrees with the Yoneda
embedding into sheaves, because the representable presheaves are already sheaves. -/
noncomputable def sheafifiedYonedaIsoUliftYoneda' :
    sheafifiedYoneda J ≅ GrothendieckTopology.uliftYoneda.{u} J := by
  let Gl := presheafToSheaf J (Type max u v)
  let Gr := sheafToPresheaf J (Type max u v)
  let adj : Gl ⊣ Gr := sheafificationAdjunction J (Type max u v)
  exact
    (Functor.isoWhiskerRight
      (GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u} J).symm Gl) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _

end CategoryTheory.Sheaf

end
