module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreInclusion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreSheaf
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex

/-!
# The complex `s(-)` does not see sheafification

Let `(C, J)` be a small site and let `Δ × C` carry the topology `K` it inherits from `(C, J)`
along the projection `π : Δ × C ⥤ C` of [Stacks, Tag 09D0]. The complex `s(-)` of the prose
preceding [Stacks, Tag 09D2] — `Stacks.SimplicialModules.mooreAbSheafCochain`, the Moore complex
of the curried simplicial abelian presheaf, **sheafified in each degree** — therefore inverts
every morphism of abelian presheaves on `Δ × C` which `K`-sheafification inverts:

`Stacks.SimplicialModules.isIso_mooreAbSheafCochain_map_of_W`.

The module documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteFlatBaseChange.lean`
asserts this informally — "since `s(-)` sheafifies in each degree this loses nothing and assumes
less, a sheaf of modules having an underlying presheaf of modules with the same `s(-)`" — and uses
it to justify stating the column and row steps of [Stacks, Tag 08RX] for *presheaves* of modules
on `Δ × C`. This file proves it, which is what lets those presheaf-level conclusions be read at
sheaf level, as the module-coefficient assembly of [Stacks, Tag 09D2] needs: there the
base-changed side is the *sheaf*-level extension of scalars, i.e. the sheafification of the
presheaf-level change of rings the column step speaks about.

## Why it is true

`s(-)` in cohomological degree `-n` is `(presheafToSheaf J)` applied to the restriction of the
presheaf to the fibre `{n} × C`, and that restriction is precomposition with the fibre inclusion
`i_n : C ⥤ Δ × C` (`Stacks.SimplicialModules.fibreInclusion`), which is a **cocontinuous**
functor of sites (`Stacks.SimplicialModules.isCocontinuous_fibreInclusion`). Precomposition with
a cocontinuous functor preserves local injectivity and local surjectivity
(`CategoryTheory.Presheaf.isLocallyInjective_whisker`,
`CategoryTheory.Presheaf.isLocallySurjective_whisker`), and on both sites the morphisms
sheafification inverts are exactly the locally bijective ones. So each degree of the map is
inverted by `presheafToSheaf J`, and a morphism of complexes all of whose components are
invertible is invertible.

The degreewise reading is organised through
`Stacks.SimplicialModules.simplicialSheafify`, the simplicial abelian *sheaf* on `C` attached to
an abelian presheaf on `Δ × C`, and the identification
`Stacks.SimplicialModules.mooreAbSheafCochainIsoSimplicialSheafify` of `s(-)` with its Moore
complex, which is `AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso`
moving the sheafification functor through the alternating-face-map complex.

## Main definitions

* `Stacks.SimplicialModules.simplicialSheafify`: an abelian presheaf on `Δ × C`, curried and
  sheafified in each simplicial degree.
* `Stacks.SimplicialModules.mooreAbSheafCochainIsoSimplicialSheafify`: `s(-)` is the
  alternating-face-map complex of that simplicial abelian sheaf.

## Main results

* `Stacks.SimplicialModules.w_whiskerLeft_fibreInclusion`: restriction to a fibre carries a
  morphism inverted by `K`-sheafification to one inverted by `J`-sheafification.
* `Stacks.SimplicialModules.isIso_mooreAbSheafCochain_map_of_W`: **`s(-)` inverts the morphisms
  `K`-sheafification inverts.**
* `Stacks.SimplicialModules.isIso_mooreSheafCochain_map_of_W`: the same for a morphism of
  presheaves of modules on `Δ × C` whose underlying morphism of abelian presheaves is inverted by
  sheafification.

## What this is not

It is not [Stacks, Tag 09D2] and carries no tag: it mentions neither `L π_!` nor the derived
tensor product. It is the statement that the complex `s(-)` is a functor on *sheaves* in
disguise.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.SimplicialModules

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **An abelian presheaf on `Δ × C`, curried and sheafified in each simplicial degree.** In
simplicial degree `n` it is the sheafification of the restriction of the presheaf to the fibre
`{n} × C`. -/
abbrev simplicialSheafify :
    ((SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  simplicialCurry AddCommGrpCat.{u} ⋙
    (SimplicialObject.whiskering (Cᵒᵖ ⥤ AddCommGrpCat.{u})
      (Sheaf J AddCommGrpCat.{u})).obj (presheafToSheaf J AddCommGrpCat.{u})

/-- In simplicial degree `n` the simplicial abelian sheaf of
`Stacks.SimplicialModules.simplicialSheafify` is the sheafification of the restriction of the
presheaf along the fibre inclusion `i_n`. -/
lemma simplicialSheafify_obj_obj (F : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    ((simplicialSheafify J).obj F).obj n =
      (presheafToSheaf J AddCommGrpCat.{u}).obj ((fibreInclusion C n.unop).op ⋙ F) :=
  rfl

/-- The same in degree `n` for a morphism. -/
lemma simplicialSheafify_map_app {F G : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    (n : SimplexCategoryᵒᵖ) :
    ((simplicialSheafify J).map f).app n =
      (presheafToSheaf J AddCommGrpCat.{u}).map
        (Functor.whiskerLeft (fibreInclusion C n.unop).op f) :=
  rfl

/-- **The complex `s(-)` is the alternating-face-map complex of the simplicial abelian sheaf
`Stacks.SimplicialModules.simplicialSheafify`.** Sheafification is additive, so it moves through
the alternating-face-map complex. -/
def mooreAbSheafCochainIsoSimplicialSheafify :
    mooreAbSheafCochain J ≅
      simplicialSheafify J ⋙ alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{u}) :=
  Functor.isoWhiskerLeft (simplicialCurry AddCommGrpCat.{u})
    (alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
      (presheafToSheaf J AddCommGrpCat.{u}))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- **Restriction to a fibre preserves the morphisms sheafification inverts.** The fibre inclusion
`i_n : C ⥤ Δ × C` is cocontinuous, and precomposition with a cocontinuous functor preserves local
injectivity and local surjectivity; on both sites those two together are exactly invertibility
under sheafification. -/
theorem w_whiskerLeft_fibreInclusion
    {F G : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    (hf : (projectionTopology C J).W f) (n : SimplexCategory) :
    J.W (Functor.whiskerLeft (fibreInclusion C n).op f) := by
  have h₁ := hf.isLocallyInjective
  have h₂ := hf.isLocallySurjective
  have := Presheaf.isLocallyInjective_whisker J (projectionTopology C J) (fibreInclusion C n) f
  have := Presheaf.isLocallySurjective_whisker J (projectionTopology C J) (fibreInclusion C n) f
  exact J.W_of_isLocallyBijective _

/-- **Currying and sheafifying in each degree inverts the morphisms sheafification inverts.** A
morphism of simplicial objects is invertible as soon as each of its components is, and in
simplicial degree `n` the component is `presheafToSheaf J` applied to the restriction of the
morphism to the fibre `{n} × C`. -/
theorem isIso_simplicialSheafify_map_of_W
    {F G : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    (hf : (projectionTopology C J).W f) :
    IsIso ((simplicialSheafify J).map f) := by
  let : ∀ n : SimplexCategoryᵒᵖ, IsIso (((simplicialSheafify J).map f).app n) := fun n => by
    rw [simplicialSheafify_map_app]
    exact (J.W_iff _).1 (w_whiskerLeft_fibreInclusion J f hf n.unop)
  exact NatIso.isIso_of_isIso_app _

/-- **The complex `s(-)` inverts the morphisms sheafification inverts.** It is the
alternating-face-map complex of `Stacks.SimplicialModules.simplicialSheafify`, which inverts
them. -/
theorem isIso_mooreAbSheafCochain_map_of_W
    {F G : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    (hf : (projectionTopology C J).W f) :
    IsIso ((mooreAbSheafCochain J).map f) := by
  have := isIso_simplicialSheafify_map_of_W J f hf
  have : IsIso ((simplicialSheafify J ⋙
      alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{u})).map f) :=
    inferInstanceAs (IsIso ((alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{u})).map
      ((simplicialSheafify J).map f)))
  set e := mooreAbSheafCochainIsoSimplicialSheafify J with he
  have key : (mooreAbSheafCochain J).map f =
      (e.app F).hom ≫
        (simplicialSheafify J ⋙
          alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{u})).map f ≫
        (e.app G).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv (e.app G)).2 (e.hom.naturality f)
  rw [key]
  infer_instance

/-- **The complex `s(F_•)` of a simplicial module inverts the morphisms sheafification inverts.**
This is `Stacks.SimplicialModules.isIso_mooreAbSheafCochain_map_of_W` read at the underlying
abelian presheaf of a presheaf of modules on `Δ × C`. -/
theorem isIso_mooreSheafCochain_map_of_W
    {O : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}}
    {P Q : PresheafOfModules.{u} (Stacks.ringPresheaf O)} (u : P ⟶ Q)
    (hu : (projectionTopology C J).W
      ((PresheafOfModules.toPresheaf (Stacks.ringPresheaf O)).map u)) :
    IsIso ((mooreSheafCochain J O).map u) :=
  isIso_mooreAbSheafCochain_map_of_W J _ hu

end Stacks.SimplicialModules

end
