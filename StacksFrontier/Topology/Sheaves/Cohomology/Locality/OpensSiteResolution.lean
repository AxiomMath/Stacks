module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf

/-!
# Cohomology of an abelian sheaf on a space, read on an injective resolution

Let `X` be a topological space, let `F` be a sheaf of abelian groups on `X` and let `I` be an
injective resolution of `F`. The complex of presheaves of sections of `I` computes the
cohomology of `F` over every open, compatibly with restriction: this file is the instantiation,
at the site of opens of a space, of the two comparisons of Section 21.7 which carry that
compatibility,

* `Stacks.Cohomology.cohomologyPresheafIsoResolution`, an isomorphism of *presheaves* between
  the homology presheaves of the section complex and Mathlib's cohomology presheaves, and
* `Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality`, which commutes homology
  past evaluation at an open compatibly with restriction,

both of which are stated for an arbitrary small site. What is derived from them here is the
statement a vanishing argument on a space actually consumes: if restriction to an open `V ⊆ W`
is surjective on the degree-`n` cohomology presheaf of `F`, then it is epimorphic on the
degree-`n` homology of the complex of sections of `I`.

## Main definitions

* `Stacks.Cohomology.OpensSite.cohomologyPresheafIsoResolution`: the homology presheaves of the
  section complex of an injective resolution are the cohomology presheaves, at the site of
  opens.
* `Stacks.Cohomology.OpensSite.sectionsHomologyIsoCohomologyPresheaf`: the homology of the
  complex of sections over one open `W` of an injective resolution of `F` is the value at `W`
  of the degree-`n` cohomology presheaf of `F`.

## Main results

* `Stacks.Cohomology.OpensSite.cohomologyPresheafIsoResolution_hom_naturality` and
  `Stacks.Cohomology.OpensSite.mapHomologyIso_evaluation_naturality`: the two comparisons are
  compatible with restriction along an inclusion of opens.
* `Stacks.Cohomology.OpensSite.epi_homologyMap_sections_of_epi_cohomologyPresheaf_map`:
  surjectivity of a restriction map on the cohomology presheaf, transported onto an injective
  resolution.

## Implementation notes

Each statement below is a restatement, with the site taken to be `Opens.grothendieckTopology X`,
of a result proved for a general small site. The restatements exist because instantiating a
`[SmallCategory C]` result at `C = Opens X` makes instance search reconcile the category
instance of `Opens X` with the one inside `Opens.grothendieckTopology X`; the resulting
unification problem is cheap at a declaration's *signature*, where the elaborator has the
instance in hand, and expensive inside a proof term that mentions the general result. Paying it
once here keeps it out of the proofs of the consumers.

Restriction of sections is spelled `(sheafSections (Opens.grothendieckTopology X) _).map f.op`
rather than `Functor.whiskerLeft (sheafToPresheaf _ _) ((evaluation _ _).map f.op)`, which is
the form the general lemma uses: the two are definitionally equal, and the former is the form in
which consumers — for instance
`Stacks.Cohomology.SupportedComplexes.restrictionToSupportComplement` — present a restriction
map.

## References

* [Stacks Project, Lemma 21.7.2 (Tag 03AY)](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Locality

universe u

namespace Stacks.Cohomology.OpensSite

variable {X : Type u} [TopologicalSpace X]

/-! ### Two lemmas on epimorphisms and isomorphisms -/

/-- An isomorphism followed by an epimorphism is an epimorphism. -/
private lemma epi_isoHom_comp {C : Type*} [Category* C] {A B D : C} (e : A ≅ B) (g : B ⟶ D)
    (h : Epi g) : Epi (e.hom ≫ g) :=
  inferInstance

/-- A morphism which becomes epimorphic after composing with an isomorphism is epimorphic. -/
private lemma epi_of_epi_comp_iso {C : Type*} [Category* C] {A B B' : C} (g : A ⟶ B) (e : B ≅ B')
    (h : Epi (g ≫ e.hom)) : Epi g := by
  simpa using (inferInstance : Epi ((g ≫ e.hom) ≫ e.inv))

/-! ### The comparisons of Section 21.7 at the site of opens -/

/-- **[Stacks, Tag 03AY] at the site of opens of a space.** The homology presheaves of the
complex of sections of an injective resolution `I` of an abelian sheaf `F` on a topological space
are the cohomology presheaves of `F`.

This is `Stacks.Cohomology.cohomologyPresheafIsoResolution` for
`Opens.grothendieckTopology X`. -/
def cohomologyPresheafIsoResolution
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (I : InjectiveResolution F)
    (n : ℕ) :
    (HomologicalComplex.homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
        (ComplexShape.up ℕ) n).obj (sectionComplex F I) ≅ F.cohomologyPresheaf n :=
  _root_.Stacks.Cohomology.cohomologyPresheafIsoResolution
    (Opens.grothendieckTopology X) F I n

/-- The comparison `Stacks.Cohomology.OpensSite.cohomologyPresheafIsoResolution` is compatible
with restriction along an inclusion of opens: it is an isomorphism of presheaves, and this is its
naturality square. -/
lemma cohomologyPresheafIsoResolution_hom_naturality
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (I : InjectiveResolution F)
    (n : ℕ) {V W : Opens X} (f : V ⟶ W) :
    ((HomologicalComplex.homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℕ) n).obj (sectionComplex F I)).map f.op ≫
        (cohomologyPresheafIsoResolution F I n).hom.app (op V) =
      (cohomologyPresheafIsoResolution F I n).hom.app (op W) ≫
        (F.cohomologyPresheaf n).map f.op :=
  (cohomologyPresheafIsoResolution F I n).hom.naturality f.op

/-- **Homology commutes with sections over an open, compatibly with restriction.** For the
section complex of an injective resolution of `F`, the isomorphism exchanging homology and
evaluation at an open is natural as the open varies.

This is `Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality` for
`Opens.grothendieckTopology X`, with restriction of sections spelled through `sheafSections`. -/
theorem mapHomologyIso_evaluation_naturality
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (I : InjectiveResolution F)
    (n : ℕ) {V W : Opens X} (f : V ⟶ W) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f.op)
            (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (ShortComplex.mapHomologyIso ((sectionComplex F I).sc n)
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom =
      (ShortComplex.mapHomologyIso ((sectionComplex F I).sc n)
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))).hom ≫
        ((sectionComplex F I).homology n).map f.op :=
  _root_.Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality F I n f

/-- The homology of the complex of sections over an open `W` of an injective resolution of `F`
is the value at `W` of the degree-`n` cohomology presheaf of `F`.

Both factors are instantiations of Section 21.7: homology commutes with evaluation at `W`
because evaluation is exact, and the homology presheaves of the section complex are the
cohomology presheaves by [Stacks, Tag 03AY]. -/
def sectionsHomologyIsoCohomologyPresheaf (W : Opens X)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op W)).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (F.cohomologyPresheaf n).obj (op W) :=
  (ShortComplex.mapHomologyIso ((sectionComplex F I).sc n)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))) ≪≫
    (cohomologyPresheafIsoResolution F I n).app (op W)

/-- **Surjectivity of a restriction map on the cohomology presheaf, read on an injective
resolution.** If restriction to an open `V ⊆ W` is surjective on the degree-`n` cohomology
presheaf of `F`, then it is epimorphic on the degree-`n` homology of the complex of sections
of an injective resolution `I` of `F`.

This is the form in which a vanishing argument consumes surjectivity of a restriction map, and
it is why the comparisons used are the two above: both are compatible with restriction, whereas
an identification of `Ext`-theoretic cohomology with right-derived sections made separately at
each open carries no such compatibility. -/
lemma epi_homologyMap_sections_of_epi_cohomologyPresheaf_map {V W : Opens X} (f : V ⟶ W)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) (hf : Epi ((F.cohomologyPresheaf n).map f.op)) :
    Epi (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f.op)
        (ComplexShape.up ℕ)).app I.cocomplex) n) := by
  -- `P` is the degree-`n` homology presheaf of the section complex of `I`.
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (HomologicalComplex.homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (ComplexShape.up ℕ) n).obj (sectionComplex F I)
  let c := cohomologyPresheafIsoResolution F I n
  -- Restriction is epimorphic on `P`, by the naturality square of `c`.
  have h₁ : Epi (P.map f.op ≫ c.hom.app (op V)) := by
    rw [cohomologyPresheafIsoResolution_hom_naturality F I n f]
    infer_instance
  have hP : Epi (P.map f.op) := epi_of_epi_comp_iso _ (c.app (op V)) h₁
  -- Transport that along the comparison exchanging homology with sections over an open.
  let eV := ShortComplex.mapHomologyIso ((sectionComplex F I).sc n)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  have h₂ : Epi ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
          (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f.op)
          (ComplexShape.up ℕ)).app I.cocomplex) ≫ eV.hom) := by
    rw [mapHomologyIso_evaluation_naturality F I n f]
    exact epi_isoHom_comp _ _ hP
  exact epi_of_epi_comp_iso _ eV h₂

end Stacks.Cohomology.OpensSite

end
