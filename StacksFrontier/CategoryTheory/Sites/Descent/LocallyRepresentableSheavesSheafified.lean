module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Effective descent data and representability for sheaves of large sets

Let `(C, J)` be a site with `C : Type u` and `Category.{v} C`, and let `S : C`. The abstract-site
analogue of Stacks 02W5 part (2) says that the canonical descent datum of a sheaf `G` on the slice
site `C/S` relative to a covering `{f i : X i ⟶ S}` is effective exactly when `G` is
representable. The form of that statement in
`CategoryTheory.GrothendieckTopology.effectiveDescentData_toDescentData_iff` is about sheaves of
`Type v`-valued sets and the Yoneda embedding `(J.over S).yoneda`; it is restated here for sheaves
of `Type (max u v)`-valued sets and the sheafified Yoneda embedding
`CategoryTheory.Sheaf.sheafifiedYoneda`.

The two are genuinely different statements, not instances of one another. A site whose objects
live in a strictly larger universe than its morphisms — the small étale site of a scheme, whose
objects form a `Type (u + 1)` and whose morphisms form a `Type u` — has no `Type v`-valued
sheafification and does not satisfy the hypothesis
`HasLimitsOfSize.{max u v, max u v} (Type v)` of the `Type v`-valued statement, whereas
`HasLimitsOfSize.{max u v, max u v} (Type (max u v))` and
`HasWeakSheafify (J.over S) (Type (max u v))` are both instances for every site.

## Main definitions

* `CategoryTheory.GrothendieckTopology.effectiveDescentDataSheafified`: the effective descent
  data of sheaves of `Type (max u v)`-valued sets, those in the essential image of the canonical
  descent datum of a sheafified representable.

## Main results

* `CategoryTheory.GrothendieckTopology.effectiveDescentDataSheafified_toDescentData_iff` is the
  abstract-site analogue of Stacks 02W5 part (2) for sheaves of `Type (max u v)`-valued sets:
  the canonical descent datum of `G` is effective if and only if the underlying presheaf of `G`
  is representable. For descent data of schemes, Stacks 02W5 is proved in
  `StacksFrontier.AlgebraicGeometry.Descent.DescentDataSheaves`.
* `CategoryTheory.GrothendieckTopology.essImage_uliftYoneda_iff` and
  `CategoryTheory.Sheaf.essImage_sheafifiedYoneda_iff`: on a subcanonical site a sheaf of
  `Type (max u v)`-valued sets is a sheafified representable exactly when its underlying presheaf
  is representable.
* `CategoryTheory.Functor.FullyFaithful.essImage_comp_iff`: a fully faithful functor neither
  adds nor removes objects from an essential image computed after it.

## Implementation notes

Representability of the underlying presheaf is `CategoryTheory.Functor.IsRepresentable`, which is
polymorphic in the universe of the values of the presheaf: for `G.obj : (Over S)ᵒᵖ ⥤ Type max u v`
it says that there are an object `Z` over `S` and a natural bijection `(W ⟶ Z) ≃ G(W)`, the two
sides living in different universes. So the conclusion of part (2) needs no restatement, only the
hypotheses do; what changes is that an isomorphism `h_Z ≅ G.obj` of presheaves must be replaced by
an isomorphism `CategoryTheory.uliftYoneda.obj Z ≅ G.obj`, which is
`CategoryTheory.Functor.RepresentableBy.equivUliftYonedaIso`.

Only one step of the original proof is universe-sensitive, the identification of the essential
image of the Yoneda embedding with representability; it is isolated here as
`CategoryTheory.Sheaf.essImage_sheafifiedYoneda_iff`. Everything else is the glueing equivalence
Stacks 04TS, which is already polymorphic in its coefficient category, together with the formal
fact `CategoryTheory.Functor.FullyFaithful.essImage_comp_iff`. In particular nothing from
Stacks 02W5 part (1) is used, there or here.

The embedding used is `CategoryTheory.Sheaf.sheafifiedYoneda (J.over S)`; on a subcanonical site
it agrees with `CategoryTheory.GrothendieckTopology.uliftYoneda` by
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, and the version of the main result for the
latter needs no sheafification hypothesis at all.

## References

* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe t v₃ v₂ v₁ u₃ u₂ u₁ v u

namespace CategoryTheory

/-! ### Essential images and fully faithful functors -/

/-- A fully faithful functor `T` neither adds nor removes objects from an essential image taken
after it: an object `T.obj Z` is in the essential image of `F ⋙ T` exactly when `Z` is in the
essential image of `F`. -/
theorem Functor.FullyFaithful.essImage_comp_iff {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D] {T : C ⥤ D}
    (hT : T.FullyFaithful) (F : B ⥤ C) (Z : C) :
    (F ⋙ T).essImage (T.obj Z) ↔ F.essImage Z :=
  ⟨fun ⟨W, ⟨e⟩⟩ => ⟨W, ⟨hT.preimageIso e⟩⟩, fun ⟨W, ⟨e⟩⟩ => ⟨W, ⟨T.mapIso e⟩⟩⟩

/-! ### Sheafified representables on a subcanonical site -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- On a subcanonical site, a sheaf of `Type (max u v)`-valued sets is in the essential image of
the Yoneda embedding `U ↦ h_U` into sheaves exactly when its underlying presheaf is
representable. -/
@[sga "3 I 1.1" "partial", sga "3 IV 4.5.5" "partial"]
theorem GrothendieckTopology.essImage_uliftYoneda_iff [J.Subcanonical]
    (F : Sheaf J (Type max u v)) :
    (GrothendieckTopology.uliftYoneda.{u} J).essImage F ↔ F.obj.IsRepresentable := by
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    exact ((Functor.RepresentableBy.equivUliftYonedaIso.{u} F.obj Z).symm
      ((GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u} J).symm.app Z ≪≫
        (sheafToPresheaf J (Type max u v)).mapIso e)).isRepresentable
  · intro hF
    obtain ⟨Z, ⟨r⟩⟩ := hF.has_representation
    exact ⟨Z, ⟨(fullyFaithfulSheafToPresheaf J (Type max u v)).preimageIso
      ((GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u} J).app Z ≪≫
        Functor.RepresentableBy.equivUliftYonedaIso.{u} F.obj Z r)⟩⟩

/-- On a subcanonical site, a sheaf of `Type (max u v)`-valued sets is a sheafified representable
exactly when its underlying presheaf is representable. Sheafification changes nothing on such a
site, so this is `CategoryTheory.GrothendieckTopology.essImage_uliftYoneda_iff`. -/
theorem Sheaf.essImage_sheafifiedYoneda_iff [J.Subcanonical]
    [HasWeakSheafify J (Type max u v)] (F : Sheaf J (Type max u v)) :
    (Sheaf.sheafifiedYoneda J).essImage F ↔ F.obj.IsRepresentable := by
  rw [← J.essImage_uliftYoneda_iff F,
    Functor.essImage_eq_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J)]

/-! ### Effective descent data for sheaves of large sets -/

namespace GrothendieckTopology

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The *effective* descent data for a family `{f i : X i ⟶ S}` in sheaves of
`Type (max u v)`-valued sets: those isomorphic to the canonical descent datum of a sheafified
representable `h_Z^#`, for `Z` an object of the site over `S`. This is
`CategoryTheory.GrothendieckTopology.effectiveDescentData` with the Yoneda embedding of the slice
site replaced by its sheafified `ULift` form. -/
def effectiveDescentDataSheafified [J.Subcanonical]
    [HasWeakSheafify (J.over S) (Type max u v)] :
    ObjectProperty ((J.pseudofunctorOver (Type max u v)).DescentData f) :=
  (Sheaf.sheafifiedYoneda (J.over S) ⋙
    (J.pseudofunctorOver (Type max u v)).toDescentData f).essImage

/-- **An abstract-site analogue of Stacks 02W5, part (2), for sheaves of large sets.** Let
`(C, J)` be a subcanonical site with `C : Type u` and `Category.{v} C`, let `{f i : X i ⟶ S}` be
a covering of an object `S` of `C`, and let `G` be a sheaf of `Type (max u v)`-valued sets on
the slice site `C/S`. Then the canonical descent datum of `G` is effective — isomorphic to the
descent datum of a sheafified representable — if and only if the underlying presheaf of `G` is
representable. -/
@[sga "3 IV 4.6.8" "partial"]
theorem effectiveDescentDataSheafified_toDescentData_iff [J.Subcanonical]
    [HasWeakSheafify (J.over S) (Type max u v)] (hf : Sieve.ofArrows X f ∈ J S)
    (G : Sheaf (J.over S) (Type max u v)) :
    effectiveDescentDataSheafified J f
        (((J.pseudofunctorOver (Type max u v)).toDescentData f).obj G) ↔
      G.obj.IsRepresentable :=
  have := isEquivalence_toDescentData_pseudofunctorOver J (Type max u v) f hf
  ((Functor.FullyFaithful.ofFullyFaithful
      ((J.pseudofunctorOver (Type max u v)).toDescentData f)).essImage_comp_iff _ G).trans
    (Sheaf.essImage_sheafifiedYoneda_iff (J.over S) G)

end GrothendieckTopology

end CategoryTheory

end
