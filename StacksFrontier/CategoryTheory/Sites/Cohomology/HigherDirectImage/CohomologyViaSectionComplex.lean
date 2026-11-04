module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero

/-!
# Sheaf cohomology computed on an injective resolution

Let `J` be a Grothendieck topology on a small category `C` and let `F` be a sheaf of abelian
groups for `J` with an injective resolution `I`. The complex of presheaves of sections
`Stacks.Cohomology.Locality.sectionComplex F I` computes the cohomology of `F` over every
object: the value of its `n`-th homology presheaf at `U` is `H^n(U, F)`, compatibly with
restriction along morphisms of `C`.

This file isolates that identification, together with the two facts about sheafification which
make it useful: a section of a sheaf which dies on a covering is zero, and a presheaf all of
whose sections die locally has zero sheafification.

## Main definitions

* `Stacks.Cohomology.Locality.sectionHomologyIso`: the identification of
  `Stacks.sheafCohomology J F U n` with the value at `U` of the `n`-th homology presheaf of
  `sectionComplex F I`.

## Main results

* `Stacks.Cohomology.Locality.sectionHomologyIso_naturality` and
  `Stacks.Cohomology.Locality.sectionHomologyIso_restrict`: the identification is compatible
  with restriction, as an equality of morphisms and read on elements.
* `Stacks.Cohomology.Locality.section_eq_zero_of_cover`: a section of a sheaf of abelian groups
  which restricts to zero on the members of a covering is zero.
* `Stacks.Cohomology.Locality.isZero_presheafToSheaf_of_locally_zero`: a presheaf of abelian
  groups each of whose sections dies on some covering of its domain has zero sheafification.

## Implementation notes

Cohomology is `Stacks.sheafCohomology`, the right derived functors of the sections over an
object, and the identification is the composite of Mathlib's
`InjectiveResolution.isoRightDerivedObj`, which computes those derived functors on the chosen
resolution, with `ShortComplex.mapHomologyIso` for the (exact) evaluation functor, which commutes
homology past evaluation at the object. Naturality in the object is the corresponding naturality
of those two isomorphisms, the second being
`Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality`.

The vanishing criterion for a sheafification is proved from local surjectivity of the unit
`toSheafify` and local injectivity of the same: a section of the sheafification is locally the
image of a section of the presheaf, each of which dies on a further covering, so the sieve of
morphisms along which the section restricts to zero is covering by transitivity, and a sheaf is
separated.

## References

* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Locality

variable {C : Type u} [Category.{v} C]

/-- Cohomology over an object of a site is the homology of the complex of sections of an
injective resolution, evaluated at that object. This is the description of cohomology on which
Stacks 01FW and Stacks 072W both rest. -/
def sectionHomologyIso (J : GrothendieckTopology C) [HasSheafify J Ab.{max u v}]
    (F : Sheaf J Ab.{max u v}) (I : InjectiveResolution F) (n : ℕ) (V : C) :
    Stacks.sheafCohomology J F V n ≅ ((sectionComplex F I).homology n).obj (op V) :=
  (I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op V)) n).trans
    (((sectionComplex F I).sc n).mapHomologyIso ((evaluation Cᵒᵖ Ab.{max u v}).obj (op V)))

/-- The identification of cohomology with the homology of the section complex is compatible
with restriction along a morphism of the site. -/
lemma sectionHomologyIso_naturality (J : GrothendieckTopology C) [HasSheafify J Ab.{max u v}]
    (F : Sheaf J Ab.{max u v}) (I : InjectiveResolution F) (n : ℕ) {U V : C} (f : U ⟶ V) :
    Stacks.sheafCohomologyRestriction J f n F ≫ (sectionHomologyIso J F I n U).hom =
      (sectionHomologyIso J F I n V).hom ≫ ((sectionComplex F I).homology n).map f.op := by
  let K := sectionComplex F I
  let e₀U := I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op U)) n
  let e₀V := I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op V)) n
  let e₁U : (HomologicalComplex.homologyFunctor Ab.{max u v} (ComplexShape.up ℕ) n).obj
      ((((evaluation Cᵒᵖ Ab.{max u v}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) ≅ (K.homology n).obj (op U) :=
    (K.sc n).mapHomologyIso ((evaluation Cᵒᵖ Ab.{max u v}).obj (op U))
  let e₁V : (HomologicalComplex.homologyFunctor Ab.{max u v} (ComplexShape.up ℕ) n).obj
      ((((evaluation Cᵒᵖ Ab.{max u v}).obj (op V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) ≅ (K.homology n).obj (op V) :=
    (K.sc n).mapHomologyIso ((evaluation Cᵒᵖ Ab.{max u v}).obj (op V))
  let m := (HomologicalComplex.homologyFunctor Ab.{max u v} (ComplexShape.up ℕ) n).map
    ((NatTrans.mapHomologicalComplex ((sheafSections J Ab.{max u v}).map f.op)
      (ComplexShape.up ℕ)).app I.cocomplex)
  show (NatTrans.rightDerived ((sheafSections J Ab.{max u v}).map f.op) n).app F ≫
    (e₀U ≪≫ e₁U).hom = (e₀V ≪≫ e₁V).hom ≫ (K.homology n).map f.op
  calc
    _ = e₀V.hom ≫ m ≫ e₀U.inv ≫ (e₀U ≪≫ e₁U).hom := by
      rw [InjectiveResolution.rightDerived_app_eq
        (α := (sheafSections J Ab.{max u v}).map f.op) (P := I) n]
      rfl
    _ = e₀V.hom ≫ m ≫ e₁U.hom := by simp [m]
    _ = e₀V.hom ≫ e₁V.hom ≫ (K.homology n).map f.op :=
      congrArg (e₀V.hom ≫ ·) (mapHomologyIso_evaluation_naturality F I n f)

/-- The identification of cohomology with the homology of the section complex, read on
elements. -/
lemma sectionHomologyIso_restrict (J : GrothendieckTopology C) [HasSheafify J Ab.{max u v}]
    (F : Sheaf J Ab.{max u v}) (I : InjectiveResolution F) (n : ℕ) {U V : C} (f : U ⟶ V)
    (x : Stacks.sheafCohomology J F V n) :
    (sectionHomologyIso J F I n U).hom (Stacks.sheafCohomologyRestriction J f n F x) =
      ((sectionComplex F I).homology n).map f.op ((sectionHomologyIso J F I n V).hom x) :=
  congrArg (fun k => k x) (sectionHomologyIso_naturality J F I n f)

/-- A section of a sheaf of abelian groups which restricts to zero on the members of a covering
is zero. -/
lemma section_eq_zero_of_cover (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Ab.{max u v})
    (hG : Presheaf.IsSheaf J G) {U : C} (R : J.Cover U) (x : G.obj (op U))
    (hx : ∀ g : R.Arrow, G.map g.f.op x = 0) : x = 0 := by
  have h := (Presheaf.isSheaf_iff_isSheaf_forget J G (forget Ab.{max u v})).mp hG
  exact ((isSheaf_iff_isSheaf_of_type J _).mp h R.1 R.2).isSeparatedFor.ext fun V g hg => by
    simpa using hx ⟨V, g, hg⟩

/-- A sheaf of abelian groups all of whose groups of sections are zero is a zero object. -/
lemma isZero_of_forall_isZero_sections (J : GrothendieckTopology C) (G : Sheaf J Ab.{max u v})
    (hG : ∀ U : Cᵒᵖ, IsZero (G.obj.obj U)) : IsZero G :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf J Ab.{max u v}) G
    (CategoryTheory.Functor.isZero _ hG)

/-- **The vanishing criterion for a sheafification.** A presheaf of abelian groups each of whose
sections dies after restriction to the members of some covering of its domain has zero
sheafification. Together with the description of a higher direct image as a sheafification
(Stacks 072W) this is what makes local vanishing of cohomology classes (Stacks 01FW) into
vanishing of a higher direct image. -/
lemma isZero_presheafToSheaf_of_locally_zero (J : GrothendieckTopology C)
    [HasSheafify J Ab.{max u v}]
    (P : Cᵒᵖ ⥤ Ab.{max u v})
    (hP : ∀ (U : C) (x : P.obj (op U)), ∃ R : J.Cover U, ∀ g : R.Arrow, P.map g.f.op x = 0) :
    IsZero ((presheafToSheaf J Ab.{max u v}).obj P) := by
  have key : ∀ (U : C) (y : (sheafify J P).obj (op U)), y = 0 := by
    intro U y
    have hmem : Presheaf.equalizerSieve (F := sheafify J P) (X := op U) y 0 ∈ J U := by
      refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J P) y) _ ?_
      rintro W g ⟨t, ht⟩
      obtain ⟨R, hR⟩ := hP W t
      refine J.superset_covering ?_ R.2
      intro Z k hk
      have hzero : (sheafify J P).map (k ≫ g).op y = 0 := by
        rw [op_comp, (sheafify J P).map_comp, ConcreteCategory.comp_apply, ← ht,
          ← NatTrans.naturality_apply (toSheafify J P) k.op t, hR ⟨Z, k, hk⟩, map_zero]
      simpa [Presheaf.equalizerSieve] using hzero
    exact section_eq_zero_of_cover J _ ((presheafToSheaf J Ab.{max u v}).obj P).property ⟨_, hmem⟩ y
      fun g => by simpa [Presheaf.equalizerSieve] using g.hf
  refine isZero_of_forall_isZero_sections J _ fun U => ?_
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun a b => by rw [key U.unop a, key U.unop b]⟩

end Stacks.Cohomology.Locality

end
