module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksFrontier.Algebra.Module.Adequate.FiniteTypeSubalgebras

/-!
# Exactness of adequate module-valued functors is detected on the finite-type algebras

The proof of [Stacks, Tag 06ZR] reads a condition on complexes of quasi-coherent `𝒪_U`-modules
off their sections over the `A`-algebras *of a chosen big site*, while the condition it is to be
compared with quantifies over all schemes over `U = Spec A`. The affine half of that comparison
of quantifiers is purely algebraic, and is what this module proves: a condition which is
exactness of a sequence of **adequate** module-valued functors needs only to be checked on the
`A`-algebras of **finite type**, because

* every `A`-algebra is the filtered colimit of its finitely generated subalgebras —
  `Stacks.Adequate.isColimit_fgSubalgebraCoconeOpOp`, with
  `Stacks.Adequate.finiteType_fgSubalgebraDiagram_obj` identifying the terms as finite-type
  algebras; and
* an adequate module-valued functor turns that filtered colimit of algebras into a colimit of
  abelian groups — [Stacks, Tag 06UU], `AdequateFunctor.isColimit_mapCocone_of_isAdequate`.

The two together say that a section of an adequate functor over an `A`-algebra already lives
over a finitely generated subalgebra, and that a section which dies over the algebra already
dies over a finitely generated subalgebra. Chasing a cycle through those two statements is the
joining argument, and it is `Stacks.Adequate.exists_preimage_of_finiteType`.

## Main definitions

* `Stacks.Adequate.fgSubalgebraDiagramOpOp` and `Stacks.Adequate.fgSubalgebraCoconeOpOp` — the
  diagram and the cocone of `Stacks.Adequate.isColimit_fgSubalgebraCoconeOpOp`, named, so that
  the stage statements below can mention their legs.

## Main results

* `Stacks.Adequate.exists_fgSubalgebra_stage` — **a section of an adequate module-valued functor
  over an `A`-algebra is restricted from a finitely generated subalgebra.**
* `Stacks.Adequate.eq_zero_of_finiteType` — **an adequate module-valued functor which vanishes
  on the finite-type algebras vanishes.**
* `Stacks.Adequate.exists_fgSubalgebra_stage_eq_zero` — **a section over a finitely generated
  subalgebra which restricts to zero over the algebra restricts to zero over a larger finitely
  generated subalgebra.**
* `Stacks.Adequate.exists_preimage_of_finiteType` — **the joining argument.** For `α : F ⟶ G`
  and `β : G ⟶ H` with `G` and `H` adequate, if over every finite-type `A`-algebra every section
  of `G` killed by `β` is in the image of `α`, then the same holds over *every* `A`-algebra.

## Implementation notes

Everything is at `.{u, u}`: [Stacks, Tag 06UU] is stated for a value universe `w` and an algebra
universe `v` independent of the base ring's universe `u`, but the index category here is the
poset of finitely generated subalgebras of an algebra in `CommAlgCat.{u} A`, which is a
`Type u` with `Category.{u}`, and the `UnivLE` hypotheses of [Stacks, Tag 06UU] then force
`max u v = u`.

The two stage statements are read off the colimit of abelian groups through
`CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
`CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`; the forgetful functor of
`AddCommGrpCat.{u}` preserves filtered colimits indexed by a `Type u`, so no universe shrinking
is needed, unlike inside the proof of [Stacks, Tag 06UU] itself.

They are stated in the `PresheafOfModules.map` spelling rather than the
`PresheafOfModules.presheaf` one, because that is the spelling
`CategoryTheory.PresheafOfModules.naturality_apply` — the only other input of the joining
argument — speaks.

## References

* [Stacks Project, Tag 06UU](https://stacks.math.columbia.edu/tag/06UU)
* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {A : Type u} [CommRing A] (R : CommAlgCat.{u} A)

/-- `Stacks.Adequate.fgSubalgebraDiagram` of the carrier of `R`, placed in
`((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ`: the category the module-valued functors
`AdequateFunctor.ModuleValuedFunctor` are indexed by. -/
public abbrev fgSubalgebraDiagramOpOp :
    FgSubalgebras A ↥R ⥤ ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ :=
  fgSubalgebraDiagram A ↥R ⋙ (opOpEquivalence (CommAlgCat.{u} A)).inverse

/-- The cocone with apex `R` on `Stacks.Adequate.fgSubalgebraDiagramOpOp`, which is the cocone
`Stacks.Adequate.isColimit_fgSubalgebraCoconeOpOp` exhibits as a colimit. -/
public abbrev fgSubalgebraCoconeOpOp : Cocone (fgSubalgebraDiagramOpOp R) :=
  (opOpEquivalence (CommAlgCat.{u} A)).inverse.mapCocone (fgSubalgebraCocone A ↥R)

/-- The forgetful functor of abelian groups preserves colimits indexed by the finitely generated
subalgebras: the index category is filtered and lives in the same universe as the groups. -/
public instance preservesColimitsOfShape_fgSubalgebras_forget :
    PreservesColimitsOfShape (FgSubalgebras A ↥R) (forget AddCommGrpCat.{u}) :=
  PreservesFilteredColimitsOfSize.preserves_filtered_colimits _

/-- An adequate module-valued functor carries the colimit of finitely generated subalgebras to a
colimit of abelian groups. -/
private noncomputable def isColimit_presheaf_mapCocone
    (G : AdequateFunctor.ModuleValuedFunctor.{u, u} A)
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G) :
    IsColimit (G.presheaf.mapCocone (fgSubalgebraCoconeOpOp R)) :=
  (AdequateFunctor.isColimit_mapCocone_of_isAdequate G hG
    (isColimit_fgSubalgebraCoconeOpOp A ↥R)).some

/-- **A section of an adequate module-valued functor over an `A`-algebra is restricted from a
finitely generated subalgebra.** The algebra is the filtered colimit of its finitely generated
subalgebras, `Stacks.Adequate.isColimit_fgSubalgebraCoconeOpOp`, and an adequate functor carries
that colimit to a colimit of abelian groups, [Stacks, Tag 06UU]; the legs of a filtered colimit
of abelian groups are jointly surjective. -/
public theorem exists_fgSubalgebra_stage
    (G : AdequateFunctor.ModuleValuedFunctor.{u, u} A)
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G) (y : G.obj (op (op R))) :
    ∃ (T : FgSubalgebras A ↥R) (z : G.obj ((fgSubalgebraDiagramOpOp R).obj T)),
      G.map ((fgSubalgebraCoconeOpOp R).ι.app T) z = y := by
  exact Concrete.isColimit_exists_rep (fgSubalgebraDiagramOpOp R ⋙ G.presheaf)
    (isColimit_presheaf_mapCocone R G hG) y

/-- **An adequate module-valued functor which vanishes on the finite-type algebras vanishes.**
Every section comes from a finitely generated subalgebra by
`Stacks.Adequate.exists_fgSubalgebra_stage`, and a finitely generated subalgebra is of finite
type over `A`, `Stacks.Adequate.finiteType_fgSubalgebraDiagram_obj`.

With `Stacks.Adequate.exists_preimage_of_finiteType` this is the second half of what it takes
for restriction to a domain of algebras containing the finite-type ones to reflect vanishing and
exactness, hence acyclicity, of complexes of adequate module-valued functors. -/
public theorem eq_zero_of_finiteType
    (G : AdequateFunctor.ModuleValuedFunctor.{u, u} A)
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G)
    (hft : ∀ (C : CommAlgCat.{u} A), Algebra.FiniteType A ↥C →
      ∀ w : G.obj (op (op C)), w = 0)
    (y : G.obj (op (op R))) : y = 0 := by
  obtain ⟨T, z, hz⟩ := exists_fgSubalgebra_stage R G hG y
  refine hz.symm.trans ?_
  rw [hft ((fgSubalgebraDiagram A ↥R).obj T) (finiteType_fgSubalgebraDiagram_obj A ↥R T) z]
  exact map_zero (G.map ((fgSubalgebraCoconeOpOp R).ι.app T)).hom

/-- **A section over a finitely generated subalgebra which restricts to zero over the whole
algebra already restricts to zero over a larger finitely generated subalgebra.** Two sections of
a filtered colimit of abelian groups with the same image agree at some later stage; here the
second section is the zero section. -/
public theorem exists_fgSubalgebra_stage_eq_zero
    (H : AdequateFunctor.ModuleValuedFunctor.{u, u} A)
    (hH : AdequateFunctor.IsAdequate (𝟭 _) H) {T : FgSubalgebras A ↥R}
    (z : H.obj ((fgSubalgebraDiagramOpOp R).obj T))
    (hz : H.map ((fgSubalgebraCoconeOpOp R).ι.app T) z = 0) :
    ∃ (T' : FgSubalgebras A ↥R) (a : T ⟶ T'),
      H.map ((fgSubalgebraDiagramOpOp R).map a) z = 0 := by
  have hrep : (H.presheaf.mapCocone (fgSubalgebraCoconeOpOp R)).ι.app T z =
      (H.presheaf.mapCocone (fgSubalgebraCoconeOpOp R)).ι.app T
        (0 : H.obj ((fgSubalgebraDiagramOpOp R).obj T)) := by
    change H.map ((fgSubalgebraCoconeOpOp R).ι.app T) z =
      H.map ((fgSubalgebraCoconeOpOp R).ι.app T) 0
    rw [hz, map_zero (H.map ((fgSubalgebraCoconeOpOp R).ι.app T)).hom]
  obtain ⟨T', a, b, hab⟩ :=
    Concrete.isColimit_exists_of_rep_eq (fgSubalgebraDiagramOpOp R ⋙ H.presheaf)
      (isColimit_presheaf_mapCocone R H hH) _ _ hrep
  refine ⟨T', a, ?_⟩
  show H.map ((fgSubalgebraDiagramOpOp R).map a) z = 0
  refine hab.trans ?_
  change H.map ((fgSubalgebraDiagramOpOp R).map b) 0 = 0
  exact map_zero (H.map ((fgSubalgebraDiagramOpOp R).map b)).hom

/-- **The joining argument of [Stacks, Tag 06ZR]: exactness of a sequence of adequate
module-valued functors is detected on the finite-type algebras.** Let `α : F ⟶ G` and
`β : G ⟶ H` be morphisms of module-valued functors on the `A`-algebras, with `G` and `H`
adequate. If over every finite-type `A`-algebra every section of `G` killed by `β` lies in the
image of `α`, then the same holds over every `A`-algebra.

A section `y` of `G` over `R` comes from a section `z` over a finitely generated subalgebra `T`
by `Stacks.Adequate.exists_fgSubalgebra_stage`; its image `β z` restricts to `β y = 0`, so it
already dies over a larger finitely generated subalgebra `T'` by
`Stacks.Adequate.exists_fgSubalgebra_stage_eq_zero`. The restriction of `z` to `T'` is therefore
a cycle over a finite-type algebra — `Stacks.Adequate.finiteType_fgSubalgebraDiagram_obj` — so
the hypothesis produces a preimage there, and restricting it to `R` gives one over `R`. -/
public theorem exists_preimage_of_finiteType
    {F G H : AdequateFunctor.ModuleValuedFunctor.{u, u} A}
    (hG : AdequateFunctor.IsAdequate (𝟭 _) G)
    (hH : AdequateFunctor.IsAdequate (𝟭 _) H) (α : F ⟶ G) (β : G ⟶ H)
    (hft : ∀ (C : CommAlgCat.{u} A), Algebra.FiniteType A ↥C →
      ∀ w : G.obj (op (op C)), β.app (op (op C)) w = 0 →
        ∃ v : F.obj (op (op C)), α.app (op (op C)) v = w)
    (y : G.obj (op (op R))) (hy : β.app (op (op R)) y = 0) :
    ∃ x : F.obj (op (op R)), α.app (op (op R)) x = y := by
  obtain ⟨T, z, hz⟩ := exists_fgSubalgebra_stage R G hG y
  have hbz : H.map ((fgSubalgebraCoconeOpOp R).ι.app T)
      (β.app ((fgSubalgebraDiagramOpOp R).obj T) z) = 0 := by
    rw [← PresheafOfModules.naturality_apply β ((fgSubalgebraCoconeOpOp R).ι.app T) z, hz]
    exact hy
  obtain ⟨T', a, ha⟩ := exists_fgSubalgebra_stage_eq_zero R H hH _ hbz
  have hcycle : β.app (op (op ((fgSubalgebraDiagram A ↥R).obj T')))
      (G.map ((fgSubalgebraDiagramOpOp R).map a) z) = 0 :=
    (PresheafOfModules.naturality_apply β ((fgSubalgebraDiagramOpOp R).map a) z).trans ha
  obtain ⟨v, hv⟩ := hft ((fgSubalgebraDiagram A ↥R).obj T')
    (finiteType_fgSubalgebraDiagram_obj A ↥R T') _ hcycle
  refine ⟨F.map ((fgSubalgebraCoconeOpOp R).ι.app T') v, ?_⟩
  have h1 : α.app (op (op R)) (F.map ((fgSubalgebraCoconeOpOp R).ι.app T') v) =
      G.map ((fgSubalgebraCoconeOpOp R).ι.app T')
        (α.app (op (op ((fgSubalgebraDiagram A ↥R).obj T'))) v) :=
    PresheafOfModules.naturality_apply α ((fgSubalgebraCoconeOpOp R).ι.app T') v
  have h2 : G.map ((fgSubalgebraCoconeOpOp R).ι.app T')
        (α.app (op (op ((fgSubalgebraDiagram A ↥R).obj T'))) v) =
      G.map ((fgSubalgebraCoconeOpOp R).ι.app T')
        (G.map ((fgSubalgebraDiagramOpOp R).map a) z) := by rw [hv]
  have h3 : G.map ((fgSubalgebraCoconeOpOp R).ι.app T')
        (G.map ((fgSubalgebraDiagramOpOp R).map a) z) = y :=
    (G.map_comp_apply ((fgSubalgebraDiagramOpOp R).map a)
        ((fgSubalgebraCoconeOpOp R).ι.app T') z).symm.trans
      ((G.congr_map_apply ((fgSubalgebraCoconeOpOp R).w a) z).trans hz)
  exact h1.trans (h2.trans h3)

end Stacks.Adequate

end
