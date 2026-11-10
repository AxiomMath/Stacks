module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Prespectral
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# Sections over a quasi-compact open commute with filtered colimits

Let `X` be a topological space with a basis of quasi-compact opens whose binary intersections
are again quasi-compact — hypotheses (H1) and (H2) of Stacks 0069 — and let `R` be a sheaf of
rings on `X`. For a quasi-compact open `U ⊆ X` and a filtered system of sheaves of `R`-modules
the canonical map `colimᵢ Fᵢ(U) ⟶ (colimᵢ Fᵢ)(U)` is an isomorphism. This is Stacks 009F for
sheaves of modules; it is the degree-zero case of Stacks 01FF, and it is also what identifies
the Čech complex of a colimit with the colimit of the Čech complexes, since under (H1) and (H2)
all the intersections occurring in a finite Čech complex of quasi-compact opens are themselves
quasi-compact.

## Main results

* `Stacks.Cohomology.CompactSections.preservesColimitsOfShape_sheafCompose_forget`: forgetting
  the group structure of an abelian sheaf preserves filtered colimits.
* `Stacks.Cohomology.CompactSections.preservesColimitsOfShape_sheafSections_addCommGrp`:
  sections of abelian sheaves over such a `U` preserve filtered colimits.
* `Stacks.Cohomology.CompactSections.preservesColimitsOfShape_toSheaf`: the abelian sheaf
  underlying a sheaf of modules preserves all colimits.
* `Stacks.Cohomology.CompactSections.preservesColimitsOfShape_secF`: sections of sheaves of
  `R`-modules over such a `U` preserve filtered colimits.

## Implementation notes

The statement is in `PreservesColimitsOfShape` form rather than as an assertion about a named
comparison map: that carries the canonical map, its naturality, and the independence of the
chosen colimit cocone all at once, and it is the form `Limits.colimit.post` results are derived
from (`Limits.preservesColimit_of_isIso_post` in one direction,
`CategoryTheory.isIso_iff_bijective` in the other).

The proof is a chain of three reductions onto the sheaf-of-sets statement, part (4) of
Stacks 0738 (`CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections`):

1. Its hypothesis is produced by
   `Stacks.Cohomology.Sections.exists_finite_quasiCompact_refinement`: the finite covering
   family is extracted from quasi-compactness of `U` applied to the quasi-compact opens lying
   in the given covering sieve, which cover `U` because the quasi-compact opens form a basis
   (H1), and the fibre product of two opens over a third is their intersection, which is
   quasi-compact by (H2).
2. From sheaves of sets to abelian sheaves: `CategoryTheory.sheafCompose` along
   `forget AddCommGrpCat` preserves filtered colimits. This is not immediate, because
   `sheafToPresheaf` does not preserve them; the argument instead rewrites the diagram as
   `(D ⋙ sheafToPresheaf) ⋙ presheafToSheaf` using that the counit of the sheafification
   adjunction is an isomorphism, so that only the left adjoint `presheafToSheaf` and the
   composite `presheafToSheaf ⋙ sheafCompose` — which is `CategoryTheory.sheafComposeNatIso` for
   the whiskering by the forgetful functor, hence colimit-preserving pointwise — have to
   preserve colimits. `forget AddCommGrpCat` reflects isomorphisms, so the abelian statement
   follows from the underlying statement of sets.
3. From abelian sheaves to sheaves of modules: `SheafOfModules.toSheaf` preserves *all*
   colimits, by the same counit rewriting with `PresheafOfModules.sheafification` as the left
   adjoint and `PresheafOfModules.sheafificationCompToSheaf` as the identification of the
   composite. Filteredness is not used there.

Everything is at coefficient universe `u`, the universe of the space: part (4) of Stacks 0738 is
stated for sheaves valued in `Type max u v`, which for the site of opens of a `Type u` space is
`Type u`, and that is the target of `forget AddCommGrpCat.{u}`.

## References

* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Stacks.Cohomology.CompactSections

/-- If `L ⊣ G` has an isomorphism as counit and `L ⋙ F` preserves colimits of shape `J`, then so
does `F`: every diagram in the target of `L` is isomorphic to one in the image of `L`. -/
private theorem preservesColimitsOfShape_of_isIso_counit {J C D E : Type*} [Category J] [Category C]
    [Category D] [Category E] [HasColimitsOfShape J C] {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    [IsIso adj.counit] (F : D ⥤ E) [PreservesColimitsOfShape J (L ⋙ F)] :
    PreservesColimitsOfShape J F := by
  have : PreservesColimitsOfShape J L := adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  constructor
  intro K
  have e : (K ⋙ G) ⋙ L ≅ K :=
    NatIso.ofComponents (fun j => (asIso adj.counit).app (K.obj j))
      (fun f => (asIso adj.counit).hom.naturality (K.map f))
  have : PreservesColimit ((K ⋙ G) ⋙ L) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (K ⋙ G)))
      (isColimitOfPreserves (L ⋙ F) (colimit.isColimit (K ⋙ G)))
  exact preservesColimit_of_iso_diagram F e

variable {X : Type u} [TopologicalSpace X]

section Sections

/-! ### From sheaves of sets to sheaves of modules -/

variable {Idx : Type u} [SmallCategory Idx] [IsFiltered Idx]

/-- **Forgetting the group structure of an abelian sheaf commutes with filtered colimits.**
A colimit of abelian sheaves is the sheafification of the colimit of the underlying presheaves,
and sheafification commutes with the forgetful functor (`CategoryTheory.sheafComposeNatIso`,
available because the forgetful functor preserves the limits and filtered colimits the plus
construction is built from). -/
theorem preservesColimitsOfShape_sheafCompose_forget :
    PreservesColimitsOfShape Idx
      (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat.{u})) := by
  let J := Opens.grothendieckTopology X
  have hWR : PreservesColimitsOfShape Idx
      ((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u})) := by
    refine preservesColimitsOfShape_of_evaluation _ Idx fun k => ?_
    exact inferInstanceAs (PreservesColimitsOfShape Idx
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj k ⋙
        forget AddCommGrpCat.{u}))
  have hLT : PreservesColimitsOfShape Idx
      (presheafToSheaf J AddCommGrpCat.{u} ⋙ sheafCompose J (forget AddCommGrpCat.{u})) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J (forget AddCommGrpCat.{u})
        (sheafificationAdjunction J AddCommGrpCat.{u})
        (sheafificationAdjunction J (Type u)))
  exact preservesColimitsOfShape_of_isIso_counit (sheafificationAdjunction J AddCommGrpCat.{u}) _

/-- **Sections of abelian sheaves over a quasi-compact open commute with filtered colimits.**
The underlying map of sets is the comparison for sheaves of sets, which is bijective, and the
forgetful functor to sets reflects isomorphisms. -/
theorem preservesColimitsOfShape_sheafSections_addCommGrp
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape Idx
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) := by
  let J := Opens.grothendieckTopology X
  let T := sheafCompose J (forget AddCommGrpCat.{u})
  let SAb := (sheafSections J AddCommGrpCat.{u}).obj (op U)
  let STy := (sheafSections J (Type u)).obj (op U)
  have hT : PreservesColimitsOfShape Idx T :=
    preservesColimitsOfShape_sheafCompose_forget (Idx := Idx) (X := X)
  have hS : PreservesColimitsOfShape Idx STy :=
    Sections.preservesColimitsOfShape_sheafSections_type_of_isCompact (I := Idx) h1 h2 U hU
  have hiso : SAb ⋙ forget AddCommGrpCat.{u} ≅ T ⋙ STy :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have hfg : PreservesColimitsOfShape Idx (SAb ⋙ forget AddCommGrpCat.{u}) :=
    preservesColimitsOfShape_of_natIso hiso.symm
  have : ReflectsColimitsOfShape Idx (forget AddCommGrpCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms (J := Idx)
  exact preservesColimitsOfShape_of_reflects_of_preserves SAb (forget AddCommGrpCat.{u})

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [IsFiltered Idx] in
/-- **The abelian sheaf underlying a sheaf of modules preserves all colimits.** No filteredness
and no hypothesis on the space is involved: a colimit of sheaves of modules is the
sheafification of the colimit of the underlying presheaves of modules, and sheafification of
presheaves of modules is compatible with the passage to abelian sheaves
(`PresheafOfModules.sheafificationCompToSheaf`). -/
theorem preservesColimitsOfShape_toSheaf :
    PreservesColimitsOfShape Idx (SheafOfModules.toSheaf.{u} R) := by
  have hLT : PreservesColimitsOfShape Idx
      (PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  exact preservesColimitsOfShape_of_isIso_counit
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) _

/-- **Stacks 009F for sheaves of modules.** On a space with a basis of quasi-compact opens
whose binary intersections are quasi-compact, taking sections over a quasi-compact open commutes
with filtered colimits of sheaves of modules. Equivalently, the canonical map
`colimᵢ Fᵢ(U) ⟶ (colimᵢ Fᵢ)(U)` is an isomorphism.

This is the degree-zero case of Stacks 01FF. -/
theorem preservesColimitsOfShape_secF
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape Idx (secF.{u, v, u} R U) := by
  have hA : PreservesColimitsOfShape Idx (SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfShape_toSheaf (Idx := Idx) R
  have hB : PreservesColimitsOfShape Idx
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) :=
    preservesColimitsOfShape_sheafSections_addCommGrp (Idx := Idx) h1 h2 U hU
  change PreservesColimitsOfShape Idx (SheafOfModules.toSheaf.{u} R ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))
  infer_instance

end Sections

end Stacks.Cohomology.CompactSections

end
