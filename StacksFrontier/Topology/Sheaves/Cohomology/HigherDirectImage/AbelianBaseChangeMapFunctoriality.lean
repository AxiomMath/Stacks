module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# Functoriality of the degreewise map on bounded below homotopy categories

`Stacks.Cohomology.BaseChange.mapPlus` applies a natural transformation `τ : E ⟶ H` of
additive functors degreewise on bounded below homotopy categories. This file equips it with
the functoriality it needs in order to descend an identity between underived base change
maps to the derived ones: it is compatible with identities, composition and whiskering, and
it is compatible with `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`, the
comparison between the degreewise image of a composite of additive functors and the
composite of the degreewise images.

The main result is the degreewise image of a *pasting identity*. Writing a commutative
square of additive functors as a transformation `τ : P ⋙ U ⟶ V ⋙ P'`, a horizontal pasting
of two such squares expresses the square of the outer rectangle in terms of the squares of
the two factors, read through comparisons `U₁ ⋙ U₂ ≅ U` and `V₁ ⋙ V₂ ≅ V` of the two
composite horizontal legs. `Stacks.Cohomology.BaseChange.mapSquarePlus_paste_app` says that
the degreewise image of such an identity is the pasting of the degreewise images, the two
leg comparisons being replaced by their images under
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`.

## Main definitions

* `Stacks.Cohomology.BaseChange.mapPlusIso`: the degreewise image of an isomorphism of
  additive functors.
* `Stacks.Cohomology.BaseChange.mapSquarePlus`: the degreewise image of a square
  `τ : F ⋙ G ⟶ G' ⋙ F'`, as a transformation between the composites of the degreewise
  images. This is the normalized form in which a square enters
  `Stacks.Cohomology.BaseChange.onHomotopy`.

## Main results

* `Stacks.Cohomology.BaseChange.mapPlus_id` and
  `Stacks.Cohomology.BaseChange.mapPlus_comp`: `mapPlus` is functorial.
* `Stacks.Cohomology.BaseChange.mapPlus_whiskerLeft_app`,
  `Stacks.Cohomology.BaseChange.mapPlus_whiskerRight_app`,
  `Stacks.Cohomology.BaseChange.mapSquarePlus_whiskerLeft` and
  `Stacks.Cohomology.BaseChange.mapSquarePlus_whiskerRight`: `mapPlus` of a whiskering is
  the whiskering of `mapPlus`, degreewise and in conjugated form.
* `Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_hom_app_hom`: the comparison
  `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso e` is, degreewise, `mapPlus e.hom`.
* `Stacks.Cohomology.BaseChange.paste_mapHomologicalComplex_app` and
  `Stacks.Cohomology.BaseChange.paste_mapHomotopyCategory_app`: the pasting identity applied
  degreewise to a complex, resp. to an object of the homotopy category.
* `Stacks.Cohomology.BaseChange.mapPlus_paste_app` and
  `Stacks.Cohomology.BaseChange.mapSquarePlus_paste_app`: **the degreewise image of a
  pasting identity is the pasting of the degreewise images**, for `mapPlus` and for
  `mapSquarePlus`.

## Implementation notes

*Why there are cancellation lemmas rather than identities.* For additive `F : A ⥤ B` and
`G : B ⥤ C`, the two functors `(F ⋙ G).mapHomotopyCategoryPlus` and
`F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus` are not equal — the induced functor
on the homotopy category is a `CategoryTheory.Quotient.lift`, and a composite of lifts is
not a lift of a composite — but they agree on *objects*, definitionally. Hence
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` has identity
components, yet the equation `component = 𝟙` cannot be used to rewrite: replacing a
component by `𝟙 X` forces the two ends of the surrounding composite to be the *same*
object, where they are merely definitionally equal, and the surrounding term stops being
type-correct. The usable form is therefore the four cancellation lemmas
`mapHomotopyCategoryPlusCompIso_refl_hom_comp` and friends, which rewrite a whole composite
and so keep the ambient term type-correct.

*Why the pasting identity is proved at three levels.* The hypothesis of the pasting law is
an identity of components of underived natural transformations, one for each *object* of the
source category. Turning it into an identity of maps of complexes is the business of
`paste_mapHomologicalComplex_app`, where `HomologicalComplex.Hom.ext` reduces to the
object-level hypothesis in each degree; `paste_mapHomotopyCategory_app` pushes that through
the quotient by homotopy, and `mapSquarePlus_paste_app` through the inclusion of the bounded
below subcategory. Each level is a separate declaration so that no single elaboration has to
traverse all three.

*Everything is generic.* No statement here mentions sheaves. The intended instances are the
small étale and the topological base change maps, whose concrete coefficient categories make
even `simp` on these rearrangements expensive; stated on variables they are cheap.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChange

/-! ### `mapPlus` is functorial -/

section Functoriality

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- The component of `mapPlus τ`, as a morphism of the ambient homotopy category. -/
theorem mapPlus_app_hom {E H : A ⥤ B} [E.Additive] [H.Additive] (τ : E ⟶ H)
    (K : HomotopyCategory.Plus A) :
    ((mapPlus τ).app K).hom =
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj := rfl

/-- `mapPlus` takes the identity to the identity. -/
theorem mapPlus_id (E : A ⥤ B) [E.Additive] :
    mapPlus (𝟙 E) = 𝟙 E.mapHomotopyCategoryPlus := by
  ext K
  rw [mapPlus_app_hom, NatTrans.mapHomotopyCategory_id]
  rfl

/-- `mapPlus` is compatible with composition. -/
theorem mapPlus_comp {E H I : A ⥤ B} [E.Additive] [H.Additive] [I.Additive]
    (τ : E ⟶ H) (τ' : H ⟶ I) :
    mapPlus (τ ≫ τ') = mapPlus τ ≫ mapPlus τ' := by
  ext K
  rw [mapPlus_app_hom, NatTrans.mapHomotopyCategory_comp]
  rfl

/-- The degreewise image of an isomorphism of additive functors. -/
def mapPlusIso {E H : A ⥤ B} [E.Additive] [H.Additive] (e : E ≅ H) :
    E.mapHomotopyCategoryPlus ≅ H.mapHomotopyCategoryPlus where
  hom := mapPlus e.hom
  inv := mapPlus e.inv
  hom_inv_id := by rw [← mapPlus_comp, e.hom_inv_id, mapPlus_id]
  inv_hom_id := by rw [← mapPlus_comp, e.inv_hom_id, mapPlus_id]

/-- The image under `mapPlus` of an isomorphism of additive functors is an isomorphism. -/
instance mapPlus_isIso {E H : A ⥤ B} [E.Additive] [H.Additive] (e : E ≅ H) :
    IsIso (mapPlus e.hom) :=
  (mapPlusIso e).isIso_hom

end Functoriality

/-! ### Compatibility with the comparison for a composite -/

section CompIso

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

/-- **The comparison for a composite is, degreewise, `mapPlus` of the comparison.** The two
functors `(F ⋙ G).mapHomotopyCategoryPlus` and the composite of the degreewise images agree
on objects, and under that identification
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso e` has the same components as
`mapPlus e.hom`. -/
theorem mapHomotopyCategoryPlusCompIso_hom_app_hom {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapHomotopyCategoryPlusCompIso e).hom.app K).hom =
      ((mapPlus e.hom).app K).hom := rfl

/-- The inverse half of `mapHomotopyCategoryPlusCompIso_hom_app_hom`. -/
theorem mapHomotopyCategoryPlusCompIso_inv_app_hom {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapHomotopyCategoryPlusCompIso e).inv.app K).hom =
      ((mapPlus e.inv).app K).hom := rfl

/-- `mapHomotopyCategoryPlusCompIso_hom_app_hom` in the bounded below homotopy category
itself, rather than in the ambient one. -/
theorem mapHomotopyCategoryPlusCompIso_hom_app {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusCompIso e).hom.app K = (mapPlus e.hom).app K := rfl

/-- `mapHomotopyCategoryPlusCompIso_inv_app_hom` in the bounded below homotopy category
itself. -/
theorem mapHomotopyCategoryPlusCompIso_inv_app {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusCompIso e).inv.app K = (mapPlus e.inv).app K := rfl

variable {F : A ⥤ B} {G : B ⥤ C} [F.Additive] [G.Additive]
  {K : HomotopyCategory.Plus A}

/-- The comparison for a composite at the identity isomorphism cancels on the left. -/
theorem mapHomotopyCategoryPlusCompIso_refl_hom_comp {Z : HomotopyCategory.Plus C}
    (f : (F ⋙ G).mapHomotopyCategoryPlus.obj K ⟶ Z) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K ≫ f = f :=
  Category.id_comp f

/-- The comparison for a composite at the identity isomorphism cancels on the right. -/
theorem mapHomotopyCategoryPlusCompIso_refl_comp_hom {Z : HomotopyCategory.Plus C}
    (f : Z ⟶ (F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus).obj K) :
    f ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K = f :=
  Category.comp_id f

/-- The inverse comparison for a composite at the identity isomorphism cancels on the
left. -/
theorem mapHomotopyCategoryPlusCompIso_refl_inv_comp {Z : HomotopyCategory.Plus C}
    (f : (F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus).obj K ⟶ Z) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K ≫ f = f :=
  Category.id_comp f

/-- The inverse comparison for a composite at the identity isomorphism cancels on the
right. -/
theorem mapHomotopyCategoryPlusCompIso_refl_comp_inv {Z : HomotopyCategory.Plus C}
    (f : Z ⟶ (F ⋙ G).mapHomotopyCategoryPlus.obj K) :
    f ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K = f :=
  Category.comp_id f

end CompIso

/-! ### Whiskering -/

section Whisker

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

/-- **`mapPlus` of a right whiskering is, degreewise, the right whiskering of `mapPlus`.**
The statement typechecks because `(E ⋙ G).mapHomotopyCategoryPlus` and the composite of the
degreewise images agree on objects. -/
theorem mapPlus_whiskerRight_app {E H : A ⥤ B} [E.Additive] [H.Additive] (τ : E ⟶ H)
    (G : B ⥤ C) [G.Additive] (K : HomotopyCategory.Plus A) :
    (mapPlus (Functor.whiskerRight τ G)).app K =
      (Functor.whiskerRight (mapPlus τ) G.mapHomotopyCategoryPlus).app K := rfl

/-- **`mapPlus` of a left whiskering is, degreewise, the left whiskering of `mapPlus`.** -/
theorem mapPlus_whiskerLeft_app (G : A ⥤ B) [G.Additive] {E H : B ⥤ C}
    [E.Additive] [H.Additive] (τ : E ⟶ H) (K : HomotopyCategory.Plus A) :
    (mapPlus (Functor.whiskerLeft G τ)).app K =
      (Functor.whiskerLeft G.mapHomotopyCategoryPlus (mapPlus τ)).app K := rfl

end Whisker

/-! ### The degreewise image of a square -/

section Square

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- **The degreewise image of a square** `τ : F ⋙ G ⟶ G' ⋙ F'`, as a transformation between
the composites of the degreewise images. This is the shape in which a square enters
`Stacks.Cohomology.BaseChange.onHomotopy`. -/
def mapSquarePlus (τ : F ⋙ G ⟶ G' ⋙ F') :
    F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⟶
      G'.mapHomotopyCategoryPlus ⋙ F'.mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom ≫
    mapPlus τ ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv

/-- `mapSquarePlus` unfolded: this is the factor that appears inside
`Stacks.Cohomology.BaseChange.onHomotopy`. -/
theorem mapSquarePlus_eq (τ : F ⋙ G ⟶ G' ⋙ F') :
    mapSquarePlus F F' G G' τ =
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom ≫
        mapPlus τ ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv := rfl

/-- The components of `mapSquarePlus` are those of `mapPlus`: the two conjugating
comparisons have identity components. The statement typechecks because
`(F ⋙ G).mapHomotopyCategoryPlus` and the composite of the degreewise images agree on
objects. -/
theorem mapSquarePlus_app (τ : F ⋙ G ⟶ G' ⋙ F') (K : HomotopyCategory.Plus A) :
    (mapSquarePlus F F' G G' τ).app K = (mapPlus τ).app K :=
  (mapHomotopyCategoryPlusCompIso_refl_hom_comp
      ((mapPlus τ).app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K)).trans
    (mapHomotopyCategoryPlusCompIso_refl_comp_inv ((mapPlus τ).app K))

end Square

section SquareWhisker

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

/-- **The degreewise image of a right whiskering is the right whiskering of the degreewise
image.** A right whiskering `Functor.whiskerRight τ G : E ⋙ G ⟶ H ⋙ G` is a square with
`G` on both horizontal legs; this is the conjugated form of
`mapPlus_whiskerRight_app`, with the comparisons for the two composites absorbed into
`mapSquarePlus`. -/
theorem mapSquarePlus_whiskerRight {E H : A ⥤ B} [E.Additive] [H.Additive] (τ : E ⟶ H)
    (G : B ⥤ C) [G.Additive] :
    mapSquarePlus E G G H (Functor.whiskerRight τ G) =
      Functor.whiskerRight (mapPlus τ) G.mapHomotopyCategoryPlus :=
  NatTrans.ext (funext (mapSquarePlus_app _ _ _ _ _))

/-- **The degreewise image of a left whiskering is the left whiskering of the degreewise
image.** -/
theorem mapSquarePlus_whiskerLeft (G : A ⥤ B) [G.Additive] {E H : B ⥤ C}
    [E.Additive] [H.Additive] (τ : E ⟶ H) :
    mapSquarePlus G H E G (Functor.whiskerLeft G τ) =
      Functor.whiskerLeft G.mapHomotopyCategoryPlus (mapPlus τ) :=
  NatTrans.ext (funext (mapSquarePlus_app _ _ _ _ _))

end SquareWhisker

/-! ### The pasting identity, degreewise -/

section PasteComplexes

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Preadditive A₀] [Preadditive A₁] [Preadditive A₂]
  [Preadditive B₀] [Preadditive B₁] [Preadditive B₂]
  {P₀ : A₀ ⥤ B₀} {P₁ : A₁ ⥤ B₁} {P₂ : A₂ ⥤ B₂}
  {U₁ : B₀ ⥤ B₁} {U₂ : B₁ ⥤ B₂} {U : B₀ ⥤ B₂}
  {V₁ : A₀ ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A₀ ⥤ A₂}
  [P₀.Additive] [P₁.Additive] [P₂.Additive]
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [V₁.Additive] [V₂.Additive] [V.Additive]
  (cU : U₁ ⋙ U₂ ≅ U) (cV : V₁ ⋙ V₂ ≅ V)
  (τ : P₀ ⋙ U ⟶ V ⋙ P₂) (τ₁ : P₀ ⋙ U₁ ⟶ V₁ ⋙ P₁) (τ₂ : P₁ ⋙ U₂ ⟶ V₂ ⋙ P₂)

/-- **A pasting identity between squares of additive functors, applied degreewise to a
complex.** The hypothesis is the pasting identity at each object of the source category; the
conclusion is the same identity for the induced transformations on complexes, where it holds
in every degree by the hypothesis. -/
theorem paste_mapHomologicalComplex_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (L : HomologicalComplex A₀ c) :
    (NatTrans.mapHomologicalComplex τ c).app L =
      (NatTrans.mapHomologicalComplex cU.inv c).app ((P₀.mapHomologicalComplex c).obj L) ≫
        (U₂.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex τ₁ c).app L) ≫
          (NatTrans.mapHomologicalComplex τ₂ c).app ((V₁.mapHomologicalComplex c).obj L) ≫
            (P₂.mapHomologicalComplex c).map
              ((NatTrans.mapHomologicalComplex cV.hom c).app L) := by
  ext i
  simpa using hτ (L.X i)

/-- **The pasting identity on the homotopy category.** The image of
`paste_mapHomologicalComplex_app` under the quotient by homotopy. -/
theorem paste_mapHomotopyCategory_app {ι : Type*} (c : ComplexShape ι)
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (M : HomotopyCategory A₀ c) :
    (NatTrans.mapHomotopyCategory τ c).app M =
      (NatTrans.mapHomotopyCategory cU.inv c).app ((P₀.mapHomotopyCategory c).obj M) ≫
        (U₂.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory τ₁ c).app M) ≫
          (NatTrans.mapHomotopyCategory τ₂ c).app ((V₁.mapHomotopyCategory c).obj M) ≫
            (P₂.mapHomotopyCategory c).map
              ((NatTrans.mapHomotopyCategory cV.hom c).app M) := by
  obtain ⟨L⟩ := M
  refine Eq.trans (congrArg (fun z => (HomotopyCategory.quotient B₂ c).map z)
    (paste_mapHomologicalComplex_app cU cV τ τ₁ τ₂ c hτ L)) ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

end PasteComplexes

section PastePlus

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  (P₀ : A₀ ⥤ B₀) (P₁ : A₁ ⥤ B₁) (P₂ : A₂ ⥤ B₂)
  (U₁ : B₀ ⥤ B₁) (U₂ : B₁ ⥤ B₂) (U : B₀ ⥤ B₂)
  (V₁ : A₀ ⥤ A₁) (V₂ : A₁ ⥤ A₂) (V : A₀ ⥤ A₂)
  [P₀.Additive] [P₁.Additive] [P₂.Additive]
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [V₁.Additive] [V₂.Additive] [V.Additive]
  (cU : U₁ ⋙ U₂ ≅ U) (cV : V₁ ⋙ V₂ ≅ V)
  (τ : P₀ ⋙ U ⟶ V ⋙ P₂) (τ₁ : P₀ ⋙ U₁ ⟶ V₁ ⋙ P₁) (τ₂ : P₁ ⋙ U₂ ⟶ V₂ ⋙ P₂)

/-- **The degreewise image on `HomotopyCategory.Plus` of a pasting identity between squares
of additive functors is the pasting of the degreewise images.** The two comparisons `cU` and
`cV` of the composite horizontal legs are replaced by their degreewise images under
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`, and nothing else changes: no
associator and no comparison for a composite enters, because the functors
`(P ⋙ W).mapHomotopyCategoryPlus` and `P.mapHomotopyCategoryPlus ⋙
W.mapHomotopyCategoryPlus` agree on objects.

The hypothesis is exactly the underived pasting identity evaluated at each object, which is
the form in which the pasting law for mates is proved. -/
theorem mapPlus_paste_app
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (K : HomotopyCategory.Plus A₀) :
    (mapPlus τ).app K =
      (Functor.mapHomotopyCategoryPlusCompIso cU).inv.app
          (P₀.mapHomotopyCategoryPlus.obj K) ≫
        U₂.mapHomotopyCategoryPlus.map ((mapPlus τ₁).app K) ≫
          (mapPlus τ₂).app (V₁.mapHomotopyCategoryPlus.obj K) ≫
            P₂.mapHomotopyCategoryPlus.map
              ((Functor.mapHomotopyCategoryPlusCompIso cV).hom.app K) := by
  ext
  exact paste_mapHomotopyCategory_app cU cV τ τ₁ τ₂ (ComplexShape.up ℤ) hτ K.obj

/-- **The pasting law for `mapSquarePlus`**: the same statement as `mapPlus_paste_app` in
the normalized square form in which a square enters
`Stacks.Cohomology.BaseChange.onHomotopy`. -/
theorem mapSquarePlus_paste_app
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (K : HomotopyCategory.Plus A₀) :
    (mapSquarePlus P₀ P₂ U V τ).app K =
      (Functor.mapHomotopyCategoryPlusCompIso cU).inv.app
          (P₀.mapHomotopyCategoryPlus.obj K) ≫
        U₂.mapHomotopyCategoryPlus.map ((mapSquarePlus P₀ P₁ U₁ V₁ τ₁).app K) ≫
          (mapSquarePlus P₁ P₂ U₂ V₂ τ₂).app (V₁.mapHomotopyCategoryPlus.obj K) ≫
            P₂.mapHomotopyCategoryPlus.map
              ((Functor.mapHomotopyCategoryPlusCompIso cV).hom.app K) := by
  refine (mapSquarePlus_app P₀ P₂ U V τ K).trans
    ((mapPlus_paste_app P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ τ₁ τ₂ hτ K).trans ?_)
  simp only [mapSquarePlus_app]
  rfl

end PastePlus

end Stacks.Cohomology.BaseChange

end
