module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Homology.HomologyColimit

/-!
# A filtered colimit of quasi-isomorphisms is a quasi-isomorphism

Let `F` be a filtered diagram of homological complexes in an abelian category whose colimits of
that shape are exact. If every transition map of `F` is a quasi-isomorphism, then every leg of a
colimit cocone on `F` is a quasi-isomorphism; and if every complex of `F` is acyclic, then so is
the vertex of a colimit cocone on `F`. For complexes of modules the exactness hypothesis is
automatic, being Grothendieck's axiom AB5.

## Main results

* `StacksDraft.isZero_homology_of_isColimit`: a colimit of complexes with vanishing degree-`n`
  homology has vanishing degree-`n` homology, for a shape whose colimits are exact.
* `StacksDraft.quasiIso_ι_of_isColimit`: for a filtered diagram of complexes whose transition
  maps are quasi-isomorphisms, every leg of a colimit cocone is a quasi-isomorphism.
* `StacksDraft.isZero_homology_isColimit` and `StacksDraft.quasiIso_isColimit_ι`: the same two
  statements for complexes of modules, where the exactness of filtered colimits is automatic.
* `StacksDraft.isZero_homology_colimit` and `StacksDraft.quasiIso_colimit_ι`: the chosen-colimit
  form for cochain complexes of modules indexed by `ℤ`.

## Implementation notes

Both proofs go through `Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor`: the
degree-`n` homology functor preserves colimits of a shape whose colimits are exact, so the image
of a colimit cocone of complexes under it is a colimit cocone in the ambient abelian category.
That reduces each statement to one about a plain colimit cocone.

For the vanishing statement what remains is that the vertex of a colimit cocone on a diagram of
zero objects is zero, which is `StacksDraft.isZero_of_isColimit`: a map out of the vertex is
determined by its restrictions along the legs, and those all start at a zero object.

For the quasi-isomorphism statement what remains is that the legs of a filtered colimit cocone on
a diagram of isomorphisms are isomorphisms. That is exactly Mathlib's
`CategoryTheory.Functor.IsEventuallyConstantFrom.isIso_ι_of_isColimit`, since
`Functor.IsEventuallyConstantFrom G j` asks precisely that `G.map φ` be an isomorphism for every
`φ` out of `j`; no filteredness is needed on the diagram of complexes itself, only on the index
category, which is where it is used.

The statements are given for an arbitrary `ComplexShape` and for an arbitrary colimit cocone
rather than the chosen `CategoryTheory.Limits.colimit`, both of which the argument is indifferent
to; the `colimit` forms are immediate corollaries via
`CategoryTheory.Limits.colimit.isColimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace StacksDraft

section General

variable {C : Type v} [Category.{w} C]

/-- **The vertex of a colimit cocone on a diagram of zero objects is a zero object.** A morphism
out of the vertex is determined by its composites with the legs of the cocone, and each of those
has a zero object as its source. -/
lemma isZero_of_isColimit [HasZeroMorphisms C] {J : Type*} [Category J] (G : J ⥤ C)
    (hG : ∀ j, IsZero (G.obj j)) (s : Cocone G) (hs : IsColimit s) : IsZero s.pt := by
  rw [IsZero.iff_id_eq_zero]
  refine hs.hom_ext fun j => ?_
  rw [Category.comp_id, comp_zero]
  exact (hG j).eq_zero_of_src _

variable [Abelian C]

/-- The degree-`n` homology functor sends a colimit cocone of complexes to a colimit cocone, for a
shape whose colimits are exact. -/
private def isColimit_mapCocone_homologyFunctor {J : Type*} [Category J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {ι : Type*} {c : ComplexShape ι} {F : J ⥤ HomologicalComplex C c}
    {s : Cocone F} (hs : IsColimit s) (n : ι) :
    IsColimit ((HomologicalComplex.homologyFunctor C c n).mapCocone s) :=
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := C) (J := J) c n
  isColimitOfPreserves (HomologicalComplex.homologyFunctor C c n) hs

/-- **A colimit of complexes with vanishing homology in a degree has vanishing homology in that
degree**, for a shape whose colimits are exact. The degree-`n` homology functor preserves such
colimits, so the homology of the vertex is a colimit of zero objects. -/
theorem isZero_homology_of_isColimit {J : Type*} [Category J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {ι : Type*} {c : ComplexShape ι}
    (F : J ⥤ HomologicalComplex C c)
    (hF : ∀ (j : J) (n : ι), IsZero ((F.obj j).homology n))
    (s : Cocone F) (hs : IsColimit s) (n : ι) :
    IsZero (s.pt.homology n) :=
  isZero_of_isColimit (F ⋙ HomologicalComplex.homologyFunctor C c n) (fun j => hF j n) _
    (isColimit_mapCocone_homologyFunctor hs n)

/-- **Every leg of a filtered colimit cocone on a diagram of quasi-isomorphisms is a
quasi-isomorphism**, for a shape whose colimits are exact. In each degree the homology functor
turns the cocone into a colimit cocone on a filtered diagram of isomorphisms, whose legs are
isomorphisms. -/
theorem quasiIso_ι_of_isColimit {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {ι : Type*} {c : ComplexShape ι}
    (F : J ⥤ HomologicalComplex C c)
    (hF : ∀ ⦃i j : J⦄ (φ : i ⟶ j), QuasiIso (F.map φ))
    (s : Cocone F) (hs : IsColimit s) (j : J) :
    QuasiIso (s.ι.app j) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hev : (F ⋙ HomologicalComplex.homologyFunctor C c n).IsEventuallyConstantFrom j := by
    intro k φ
    have : QuasiIso (F.map φ) := hF φ
    exact (quasiIsoAt_iff_isIso_homologyMap (F.map φ) n).mp inferInstance
  exact hev.isIso_ι_of_isColimit (isColimit_mapCocone_homologyFunctor hs n)

end General

section Modules

variable {J : Type u} [Category.{u} J] [IsFiltered J] {A : Type u} [CommRing A]

/-- **A filtered colimit of complexes of modules with vanishing homology in a degree has
vanishing homology in that degree.** The exactness of filtered colimits of modules is
Grothendieck's axiom AB5, available as `CategoryTheory.AB5 (ModuleCat.{u} A)`. -/
theorem isZero_homology_isColimit {ι : Type*} {c : ComplexShape ι}
    (F : J ⥤ HomologicalComplex (ModuleCat.{u} A) c)
    (hF : ∀ (j : J) (n : ι), IsZero ((F.obj j).homology n))
    (s : Cocone F) (hs : IsColimit s) (n : ι) :
    IsZero (s.pt.homology n) :=
  isZero_homology_of_isColimit F hF s hs n

/-- **A filtered colimit of quasi-isomorphisms of complexes of modules is a quasi-isomorphism**,
in the form of the legs of a colimit cocone on a filtered diagram whose transition maps are
quasi-isomorphisms. -/
theorem quasiIso_isColimit_ι {ι : Type*} {c : ComplexShape ι}
    (F : J ⥤ HomologicalComplex (ModuleCat.{u} A) c)
    (hF : ∀ ⦃i j : J⦄ (φ : i ⟶ j), QuasiIso (F.map φ))
    (s : Cocone F) (hs : IsColimit s) (j : J) :
    QuasiIso (s.ι.app j) :=
  quasiIso_ι_of_isColimit F hF s hs j

/-- A filtered colimit of acyclic complexes of modules is acyclic. -/
theorem isZero_homology_colimit (F : J ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (hF : ∀ (j : J) (n : ℤ), IsZero ((F.obj j).homology n)) (n : ℤ) :
    IsZero ((colimit F).homology n) :=
  isZero_homology_isColimit F hF (colimit.cocone F) (colimit.isColimit F) n

/-- If every transition map of a filtered diagram of complexes of modules is a
quasi-isomorphism, then so is every map into the colimit. -/
theorem quasiIso_colimit_ι (F : J ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (hF : ∀ ⦃i j : J⦄ (φ : i ⟶ j), QuasiIso (F.map φ)) (j : J) :
    QuasiIso (colimit.ι F j) :=
  quasiIso_isColimit_ι F hF (colimit.cocone F) (colimit.isColimit F) j

end Modules

end StacksDraft

end
