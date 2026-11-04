module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import StacksCore.Algebra.Homology.SpectralSequence.EdgeStep
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transporting a spectral sequence along an exact functor

Let `F : C ⥤ D` be an additive functor between abelian categories which preserves homology (for
instance an exact functor). Applying `F` degreewise to every page of a spectral sequence of `C`
produces a spectral sequence of `D`: the identification of the homology of a page with the next
page is transported by the canonical isomorphism `ShortComplex.mapHomologyIso`, which is
available exactly because `F` preserves homology. The construction is functorial in the spectral
sequence, and the resulting functor therefore carries isomorphisms of spectral sequences to
isomorphisms.

The motivating special case is `F = AddCommGrpCat.uliftFunctor`, which changes the universe of a
spectral sequence of abelian groups without changing any of its pages, differentials or
page-to-page identifications. This is what lets a spectral sequence whose terms are Hom groups of
a category be compared with one whose terms are Hom groups of its derived category, the two
living in unrelated universes: both are lifted to their common upper bound.

Also recorded here is the converse direction of `SpectralSequence.isIso_hom_of_GE`: a morphism of
spectral sequences which is an isomorphism on the *first* page is an isomorphism, the inverse
being assembled page by page from the inverses supplied by that lemma.

## Main definitions

* `CategoryTheory.SpectralSequence.map`: the spectral sequence `F(E)` obtained by applying `F` to
  every page of `E`.
* `CategoryTheory.SpectralSequence.mapFunctor`: the same construction as a functor
  `SpectralSequence C c r₀ ⥤ SpectralSequence D c r₀`.
* `CategoryTheory.SpectralSequence.ulift`, `CategoryTheory.SpectralSequence.uliftFunctor`: the
  specialization to `AddCommGrpCat.uliftFunctor`, changing the universe of a spectral sequence of
  abelian groups.

## Main results

* `CategoryTheory.SpectralSequence.isIso_of_isIso_hom`: a morphism of spectral sequences which is
  an isomorphism on the page `r₀` is an isomorphism.

## Implementation notes

No `set_option` is used. The naturality square for `mapFunctor.map` is not accessible to `rw` in
the shape in which it arises: the first factor of the goal is
`HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) pq`, whose `HasHomology`
instance is the one of `(F.mapHomologicalComplex _).obj (E.page r)` rather than the one of the
short complex `((E.page r).sc pq).map F` that `ShortComplex.mapHomologyIso_hom_naturality` speaks
about. The two are definitionally equal but not type-correct for each other under the `implicit`
transparency level, so a bare `rw [← Functor.map_comp]` or even `rw [Category.assoc]` fails to
build its motive. A single `change` puts the goal in the short-complex spelling, after which every
remaining step is either a rewrite by a fully explicit equation (`hsplit`, `hjoin`, and the
`show … from f.comm`) or a term-mode `congrArg`/`Category.assoc`.
-/

@[expose] public noncomputable section

namespace CategoryTheory

namespace SpectralSequence

open Limits

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Map

variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- **A homology-preserving additive functor transports spectral sequences.** The `r`-th page of
`E.map F` is the image of the `r`-th page of `E` under `F`, and the identification of the homology
of a page with the next page is the one of `E`, transported by the canonical isomorphism
`ShortComplex.mapHomologyIso` between the homology of an image and the image of the homology. -/
def map (E : SpectralSequence C c r₀) : SpectralSequence D c r₀ where
  page r hr := (F.mapHomologicalComplex _).obj (E.page r hr)
  iso r r' pq hrr' hr :=
    ((E.page r hr).sc pq).mapHomologyIso F ≪≫ F.mapIso (E.iso r r' pq hrr' hr)

/-- The `r`-th page of `E.map F` is the image of the `r`-th page of `E` under `F`. -/
@[simp]
lemma map_page (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) :
    (E.map F).page r hr = (F.mapHomologicalComplex _).obj (E.page r hr) :=
  rfl

/-- **The transport of spectral sequences along `F` is a functor.** A morphism of spectral
sequences is sent to the morphism obtained by applying `F` to it on every page. -/
def mapFunctor : SpectralSequence C c r₀ ⥤ SpectralSequence D c r₀ where
  obj E := E.map F
  map {E E'} f :=
    { hom r hr := (F.mapHomologicalComplex _).map (f.hom r hr)
      comm r r' pq hrr' hr := by
        change ShortComplex.homologyMap (F.mapShortComplex.map
            ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr))) ≫
            (((E'.page r hr).sc pq).mapHomologyIso F).hom ≫
              F.map (E'.iso r r' pq hrr' hr).hom =
          ((((E.page r hr).sc pq).mapHomologyIso F).hom ≫
            F.map (E.iso r r' pq hrr' hr).hom) ≫ F.map ((f.hom r').f pq)
        have hsplit : F.map (ShortComplex.homologyMap
              ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr))) ≫
            F.map (E'.iso r r' pq hrr' hr).hom =
              F.map (ShortComplex.homologyMap
                ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)) ≫
                  (E'.iso r r' pq hrr' hr).hom) := (F.map_comp _ _).symm
        have hjoin : F.map ((E.iso r r' pq hrr' hr).hom ≫ (f.hom r').f pq) =
            F.map (E.iso r r' pq hrr' hr).hom ≫ F.map ((f.hom r').f pq) := F.map_comp _ _
        rw [← Category.assoc, ShortComplex.mapHomologyIso_hom_naturality
            ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)) F,
          Category.assoc, hsplit,
          show ShortComplex.homologyMap
                ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)) ≫
              (E'.iso r r' pq hrr' hr).hom =
            (E.iso r r' pq hrr' hr).hom ≫ (f.hom r').f pq from f.comm r r' pq hrr' hr]
        exact (congrArg (fun x => (((E.page r hr).sc pq).mapHomologyIso F).hom ≫ x) hjoin).trans
          (Category.assoc _ _ _).symm }
  map_id E := hom_ext fun _ _ => (F.mapHomologicalComplex _).map_id _
  map_comp f g := hom_ext fun _ _ => (F.mapHomologicalComplex _).map_comp _ _

/-- The functor `mapFunctor F` sends a spectral sequence `E` to `E.map F`. -/
@[simp]
lemma mapFunctor_obj (E : SpectralSequence C c r₀) : (mapFunctor F).obj E = E.map F :=
  rfl

/-- On the `r`-th page, the image of a morphism `f` under `mapFunctor F` is the image of the
`r`-th component of `f` under `F`. -/
@[simp]
lemma mapFunctor_map_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    ((mapFunctor F).map f).hom r hr = (F.mapHomologicalComplex _).map (f.hom r hr) :=
  rfl

end Map

/-- **A morphism of spectral sequences which is an isomorphism on the first page is an
isomorphism.** By `SpectralSequence.isIso_hom_of_GE` it is then an isomorphism on every page, and
the inverses on the pages are compatible with the identifications of the homology of a page with
the next page, so they assemble into an inverse morphism of spectral sequences. -/
@[ega "0 11.1.2" "more general"]
lemma isIso_of_isIso_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (hf : IsIso (f.hom r₀ le_rfl)) : IsIso f := by
  have h (r : ℤ) (hr : r₀ ≤ r) : IsIso (f.hom r hr) :=
    SpectralSequence.isIso_hom_of_GE f r₀ r hr hf
  let g : E' ⟶ E :=
    { hom r hr := inv (f.hom r hr)
      comm r r' pq hrr' hr := by
        apply (cancel_mono ((f.hom r').f pq)).1
        rw [Category.assoc, ← f.comm r r' pq hrr' hr, ← Category.assoc,
          ← HomologicalComplex.homologyMap_comp, IsIso.inv_hom_id,
          HomologicalComplex.homologyMap_id, Category.id_comp]
        simp only [Category.assoc, ← HomologicalComplex.comp_f, IsIso.inv_hom_id,
          HomologicalComplex.id_f, Category.comp_id] }
  exact ⟨⟨g, hom_ext fun r hr => IsIso.hom_inv_id (f.hom r hr),
    hom_ext fun r hr => IsIso.inv_hom_id (f.hom r hr)⟩⟩

section Ulift

universe w v

/-- **Changing the universe of a spectral sequence of abelian groups.** The pages, the
differentials and the identifications of the homology of a page with the next page are retained;
only the universe of the underlying types changes, by `ULift`. -/
abbrev ulift (E : SpectralSequence AddCommGrpCat.{v} c r₀) :
    SpectralSequence AddCommGrpCat.{max w v} c r₀ :=
  E.map AddCommGrpCat.uliftFunctor.{w, v}

/-- **The universe change of a spectral sequence of abelian groups is a functor.** In particular
it carries an isomorphism of spectral sequences to an isomorphism. -/
abbrev uliftFunctor :
    SpectralSequence AddCommGrpCat.{v} c r₀ ⥤ SpectralSequence AddCommGrpCat.{max w v} c r₀ :=
  mapFunctor AddCommGrpCat.uliftFunctor.{w, v}

end Ulift

end SpectralSequence

end CategoryTheory

end
