module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreSheaf

/-!
# The double complex of the simplicial site instance of Stacks 08RX

`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteMooreSheaf.lean` attaches
to a presheaf of modules `F` on the simplicial site `Δ × C` over a presheaf of commutative rings `O`
the complex of abelian sheaves `s(F_•)` (`Stacks.SimplicialModules.mooreSheafCochain`) and the
base-change unit

`s(F_•) ⟶ s(F_• ⊗_O O')`

along a homomorphism `θ : O ⟶ O'` of structure rings
(`Stacks.SimplicialModules.mooreSheafBaseChange`). This module carries out, for those coefficients,
the assembly that
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeAssembly.lean` carries out
for simplicial modules over a simplicial commutative ring: it forms the double complex obtained by
applying the two Moore-complex functors to a resolution and compares the two total complexes
through the column and the row filtration.

## The shape of the argument

Let `L^•` be a complex of presheaves of modules on `Δ × C`, bounded above by `0`, and form the two
double complexes

`Z^{p,q} = s(L^p)^q` and `Z'^{p,q} = s(L^p ⊗_O O')^q`

of abelian sheaves on `C`, together with the morphism `Z ⟶ Z'` which in each column is the
base-change unit at `L^p`. Both lie in the third quadrant — `L^•` is bounded above by `0` and the
Moore complex is concentrated in cohomological degrees `≤ 0`
(`Stacks.SimplicialModules.isZero_mooreSheafCochain_X`) — so both have total complexes, and
[Stacks, Tag 0133] for double complexes bounded above
(`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound`) turns the column step into

`Tot(Z) ⟶ Tot(Z')` a quasi-isomorphism

(`Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap`). The column step
itself is carried here as a hypothesis: it is the statement of the simplicial site instance of
[Stacks, Tag 08RX] at the terms of the resolution, and is not proved in this module.

The *row* filtration compares `Tot(Z)` with `s(M)`. On the unchanged side it is proved here: the
row `q = -n` of the double complex is the resolution read in simplicial degree `n`, on underlying
abelian presheaves and then sheafified, and every one of those operations is exact, so no homology
is computed (`Stacks.SimplicialModules.preservesHomology_mooreSheafCochain_comp_eval` and
`Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`). On the base-changed side the
rows are not exact functors, and that is where flatness would be consumed; it is carried here as a
hypothesis, and discharged in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteFlatBaseChange.lean` by
`Stacks.SimplicialModules.quasiIso_total_map_baseChangedMooreSheafBicomplex`.

Passing between `Tot` of the double complex of `M[0]` and `s(M)` itself needs no new work:
`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit` identifies the total complex of a double
complex concentrated in the column `0` with that column, and Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` identifies the double complex of `M[0]` with the
column `s(M)`. This is
`Stacks.SimplicialModules.quasiIso_totalSingleColumn_mooreSheafCochain`.

## Main definitions

* `Stacks.SimplicialModules.mooreSheafBicomplex` and
  `Stacks.SimplicialModules.baseChangedMooreSheafBicomplex`: the two double complexes of abelian
  sheaves.
* `Stacks.SimplicialModules.mooreSheafBicomplexBaseChangeMap`: the morphism between them, in each
  column the base-change unit.

## Main results

* `Stacks.SimplicialModules.isZero_moorePresheafCochain_X` and
  `Stacks.SimplicialModules.isZero_mooreSheafCochain_X`: the Moore complex of a simplicial module
  on `Δ × C` vanishes in positive cohomological degrees, before and after sheafification.
* `Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap`: **the column
  filtration** — the base-change unit is a quasi-isomorphism on total complexes as soon as it is
  one in every column.
* `Stacks.SimplicialModules.preservesHomology_mooreSheafCochain_comp_eval`: the rows of the double
  complex are exact functors of the simplicial module.
* `Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`: **the row filtration on the
  unchanged side** — a quasi-isomorphism of resolutions stays one on total complexes.
* `Stacks.SimplicialModules.quasiIso_totalSingleColumn_mooreSheafCochain` and
  `Stacks.SimplicialModules.quasiIso_totalSingleColumn_baseChangedMooreSheafCochain`: the
  identification `Tot(Z) ≃ s(M)` which makes the row filtration usable, on the two sides.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso

universe u

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-! ### Additivity of the currying functor -/


/-! ### Vanishing in positive degrees -/

/-- The Moore complex of a simplicial module on `Δ × C` vanishes in positive cohomological
degrees: the simplicial degree `n` sits in cohomological degree `-n`. -/
lemma isZero_moorePresheafCochain_X (M : PresheafOfModules.{u} (ringPresheaf O)) (q : ℤ)
    (hq : 0 < q) :
    IsZero (((moorePresheafCochain O).obj M).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- **The complex `s(F_•)` vanishes in positive cohomological degrees**: it is the degreewise
sheafification of a complex which does, and sheafification takes the zero object to the zero
object. -/
lemma isZero_mooreSheafCochain_X (M : PresheafOfModules.{u} (ringPresheaf O)) (q : ℤ)
    (hq : 0 < q) :
    IsZero (((mooreSheafCochain J O).obj M).X q) :=
  Functor.map_isZero (presheafToSheaf J AddCommGrpCat.{u})
    (isZero_moorePresheafCochain_X M q hq)

/-! ### The double complex and its column filtration -/

/-- **The double complex `Z^{p,q} = s(L^p)^q`** of a complex of presheaves of modules on
`Δ × C`. -/
abbrev mooreSheafBicomplex (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) :
    HomologicalComplex₂ (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

/-- **The base-changed double complex `Z'^{p,q} = s(L^p ⊗_O O')^q`.** -/
abbrev baseChangedMooreSheafBicomplex
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) :
    HomologicalComplex₂ (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex (ComplexShape.up ℤ)).obj L

/-- **The base-change unit between the two double complexes**, in each column the unit at
`L^p`. -/
abbrev mooreSheafBicomplexBaseChangeMap
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) :
    mooreSheafBicomplex J L ⟶ baseChangedMooreSheafBicomplex J θ L :=
  (NatTrans.mapHomologicalComplex (mooreSheafBaseChange J θ) (ComplexShape.up ℤ)).app L

/-- Every term of the double complex vanishes in positive second degree. -/
lemma isZero_mooreSheafBicomplex_X_X
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) (p q : ℤ) (hq : 0 < q) :
    IsZero (((mooreSheafBicomplex J L).X p).X q) :=
  isZero_mooreSheafCochain_X J (L.X p) q hq

/-- Every term of the base-changed double complex vanishes in positive second degree. -/
lemma isZero_baseChangedMooreSheafBicomplex_X_X
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) (p q : ℤ) (hq : 0 < q) :
    IsZero (((baseChangedMooreSheafBicomplex J θ L).X p).X q) :=
  isZero_mooreSheafCochain_X J ((changeOfRings θ).obj (L.X p)) q hq

/-- A column of the double complex over a vanishing term of the resolution vanishes. -/
lemma isZero_mooreSheafBicomplex_X
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) (p : ℤ)
    (hp : IsZero (L.X p)) :
    IsZero ((mooreSheafBicomplex J L).X p) :=
  Functor.map_isZero (mooreSheafCochain J O) hp

/-- A column of the base-changed double complex over a vanishing term of the resolution
vanishes. -/
lemma isZero_baseChangedMooreSheafBicomplex_X
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) (p : ℤ)
    (hp : IsZero (L.X p)) :
    IsZero ((baseChangedMooreSheafBicomplex J θ L).X p) :=
  Functor.map_isZero (changeOfRings θ ⋙ mooreSheafCochain J O') hp

/-- The double complex of a resolution bounded above by `0` is bounded above, hence has a total
complex. -/
instance hasTotal_mooreSheafBicomplex
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0] :
    (mooreSheafBicomplex J L).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_mooreSheafBicomplex_X J L p
      (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (fun p q hq => isZero_mooreSheafBicomplex_X_X J L p q hq)

/-- The base-changed double complex of a resolution bounded above by `0` is bounded above, hence
has a total complex. -/
instance hasTotal_baseChangedMooreSheafBicomplex
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0] :
    (baseChangedMooreSheafBicomplex J θ L).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_baseChangedMooreSheafBicomplex_X J θ L p
      (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (fun p q hq => isZero_baseChangedMooreSheafBicomplex_X_X J θ L p q hq)

/-- **The column filtration of the double complex of the simplicial site instance of
[Stacks, Tag 08RX]**: the base-change unit is a quasi-isomorphism on total complexes as soon as it
is one in every column, which is the hypothesis `hcol`.

This is [Stacks, Tag 0133] for double complexes bounded above
(`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound`); the two double complexes
are bounded above because the resolution is and because the Moore complex is concentrated in
cohomological degrees `≤ 0`. -/
theorem quasiIso_total_mooreSheafBicomplexBaseChangeMap
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0]
    (hcol : ∀ p, QuasiIso ((mooreSheafBaseChange J θ).app (L.X p))) :
    QuasiIso (HomologicalComplex₂.total.map (mooreSheafBicomplexBaseChangeMap J θ L)
      (ComplexShape.up ℤ)) :=
  have h0 (p : ℤ) (hp : 0 < p) := CochainComplex.isZero_of_isStrictlyLE L 0 p hp
  quasiIso_total_map_of_upperBound (mooreSheafBicomplexBaseChangeMap J θ L) 0 0
    (fun p hp => isZero_mooreSheafBicomplex_X J L p (h0 p hp))
    (isZero_mooreSheafBicomplex_X_X J L)
    (fun p hp => isZero_baseChangedMooreSheafBicomplex_X J θ L p (h0 p hp))
    (isZero_baseChangedMooreSheafBicomplex_X_X J θ L) hcol

/-! ### The row filtration on the unchanged side -/

/-- **Evaluating the complex `s(F_•)` in a fixed cohomological degree is an exact functor of the
simplicial module.** For `q = -n ≤ 0` it is the composite of four exact functors: the underlying
abelian presheaf on `Δ × C`, the currying which reads it as a simplicial abelian presheaf on `C`
(an equivalence), evaluation at `⦋n⦌` on a functor category, and sheafification — the
identification of the Moore complex in that degree with the evaluation is
`AlgebraicTopology.alternatingFaceMapCochainComplexCompEvalIso`. For `q > 0` the functor is zero
by `Stacks.SimplicialModules.isZero_mooreSheafCochain_X`. This is what makes the rows of the
double complex compute no homology of their own. -/
instance preservesHomology_mooreSheafCochain_comp_eval (q : ℤ) :
    (mooreSheafCochain J O ⋙ HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u})
      (ComplexShape.up ℤ) q).PreservesHomology := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    have eAb : mooreAbPresheafCochain (C := C) ⋙
          HomologicalComplex.eval (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)
            ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
        simplicialCurry AddCommGrpCat.{u} ⋙
          (evaluation SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
            (op (SimplexCategory.mk n)) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (simplicialCurry AddCommGrpCat.{u})
          (alternatingFaceMapCochainComplexCompEvalIso (Cᵒᵖ ⥤ AddCommGrpCat.{u}) n)
    have e : mooreSheafCochain J O ⋙ HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u})
          (ComplexShape.up ℤ) ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
        PresheafOfModules.toPresheaf (ringPresheaf O) ⋙
          (simplicialCurry AddCommGrpCat.{u} ⋙
            (evaluation SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
              (op (SimplexCategory.mk n))) ⋙ presheafToSheaf J AddCommGrpCat.{u} :=
      Functor.isoWhiskerLeft (PresheafOfModules.toPresheaf (ringPresheaf O))
        (Functor.isoWhiskerRight eAb (presheafToSheaf J AddCommGrpCat.{u}))
    have := preservesFiniteLimits_of_natIso e.symm
    have := preservesFiniteColimits_of_natIso e.symm
    infer_instance
  · exact Functor.preservesHomology_of_map_exact _ fun S _ =>
      ShortComplex.exact_of_isZero_X₂ _ (isZero_mooreSheafCochain_X J S.X₂ q hq)

/-- **The row filtration of the double complex, on the unchanged side**: a quasi-isomorphism of
complexes of presheaves of modules on `Δ × C`, both bounded above by `0`, stays one on the total
complexes of the associated double complexes. The rows are exact functors of the simplicial module
(`Stacks.SimplicialModules.preservesHomology_mooreSheafCochain_comp_eval`), so no homology is
computed; this is [Stacks, Tag 0133] for double complexes bounded above with the hypothesis on the
rows. -/
theorem quasiIso_total_map_mooreSheafBicomplex
    {L L' : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ} (π : L ⟶ L')
    [L.IsStrictlyLE 0] [L'.IsStrictlyLE 0] [QuasiIso π] :
    QuasiIso (HomologicalComplex₂.total.map
      (((mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
      (ComplexShape.up ℤ)) := by
  have hZ (K : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [K.IsStrictlyLE 0]
      (p q : ℤ) (hpq : 0 < p ∨ 0 < q) : IsZero (((mooreSheafBicomplex J K).X p).X q) := by
    refine hpq.elim (fun hp => Functor.map_isZero
      (HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) q)
      (isZero_mooreSheafBicomplex_X J K p (CochainComplex.isZero_of_isStrictlyLE K 0 p hp)))
      (isZero_mooreSheafBicomplex_X_X J K p q)
  refine quasiIso_total_map_of_upperBound_flip _ 0 0 (hZ L) (hZ L') fun q => ?_
  · have h : (flipHom (((mooreSheafCochain J O).mapHomologicalComplex
          (ComplexShape.up ℤ)).map π)).f q =
        ((mooreSheafCochain J O ⋙ HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u})
          (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℤ)).map π := rfl
    rw [h]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology π _

/-! ### The bottom edge of the square of filtrations -/

/-- The total complex of a double complex of abelian sheaves concentrated in one column exists;
this is `StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn` registered as an instance for the
coefficient category at hand. -/
instance hasTotal_singleColumn_sheaf (W : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (a : ℤ) :
    (singleColumn W a).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_singleColumn W a

/-- The double complex of `M[0]` has a total complex, written in the composite form
`single ⋙ (mooreSheafCochain J O).mapHomologicalComplex` in which Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` presents it. This is
`Stacks.SimplicialModules.hasTotal_mooreSheafBicomplex` at the complex concentrated in degree
`0`; instance search does not see through the composition on its own. -/
instance hasTotal_single_comp_mooreSheafBicomplex (M : PresheafOfModules.{u} (ringPresheaf O)) :
    HomologicalComplex₂.HasTotal
      ((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O)) (ComplexShape.up ℤ) 0 ⋙
        (mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
      (ComplexShape.up ℤ) :=
  hasTotal_mooreSheafBicomplex J
    ((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
      (ComplexShape.up ℤ) 0).obj M)

/-- The base-changed double complex of `M[0]` has a total complex, in the same composite form.
This is `Stacks.SimplicialModules.hasTotal_baseChangedMooreSheafBicomplex` at the complex
concentrated in degree `0`. -/
instance hasTotal_single_comp_baseChangedMooreSheafBicomplex
    (M : PresheafOfModules.{u} (ringPresheaf O)) :
    HomologicalComplex₂.HasTotal
      ((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O)) (ComplexShape.up ℤ) 0 ⋙
        (changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) (ComplexShape.up ℤ) :=
  hasTotal_baseChangedMooreSheafBicomplex J θ
    ((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
      (ComplexShape.up ℤ) 0).obj M)

/-- The double complex concentrated in the column `0` with the column `s(M)` has a total complex,
written in the composite form `mooreSheafCochain J O ⋙ single` in which Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` presents it. This is
`Stacks.SimplicialModules.hasTotal_singleColumn_sheaf`, which instance search does not reach
through the composition. -/
instance hasTotal_mooreSheafCochain_comp_single (M : PresheafOfModules.{u} (ringPresheaf O)) :
    HomologicalComplex₂.HasTotal
      ((mooreSheafCochain J O ⋙ HomologicalComplex.single
        (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (ComplexShape.up ℤ) 0).obj M)
      (ComplexShape.up ℤ) :=
  hasTotal_singleColumn ((mooreSheafCochain J O).obj M) 0

/-- The same for the column `s(M ⊗_O O')`, again in the composite form. -/
instance hasTotal_baseChangedMooreSheafCochain_comp_single
    (M : PresheafOfModules.{u} (ringPresheaf O)) :
    HomologicalComplex₂.HasTotal
      (((changeOfRings θ ⋙ mooreSheafCochain J O') ⋙ HomologicalComplex.single
        (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (ComplexShape.up ℤ) 0).obj M)
      (ComplexShape.up ℤ) :=
  hasTotal_singleColumn ((changeOfRings θ ⋙ mooreSheafCochain J O').obj M) 0

/-- **The row filtration identifies `Tot(Z)` with `s(M)`.** Let `π : L^• ⟶ M[0]` be a
quasi-isomorphism with `L^•` bounded above by `0`. Composing the row filtration
(`Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`) with Mathlib's identification
of the double complex of `M[0]` with the column `s(M)`
(`HomologicalComplex.singleMapHomologicalComplex`) and with the identification of the total
complex of a double complex concentrated in the column `0` with that column
(`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit`, in the form
`Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso`) gives a quasi-isomorphism

`Tot(Z) ⟶ s(M)`.

The last two legs are isomorphisms, so only the first carries any content. -/
theorem quasiIso_totalSingleColumn_mooreSheafCochain
    (M : PresheafOfModules.{u} (ringPresheaf O))
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0]
    (π : L ⟶ (HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
      (ComplexShape.up ℤ) 0).obj M) [QuasiIso π] :
    QuasiIso (HomologicalComplex₂.total.map
          (((mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          ((HomologicalComplex.singleMapHomologicalComplex (mooreSheafCochain J O)
            (ComplexShape.up ℤ) 0).hom.app M) (ComplexShape.up ℤ) ≫
        (Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
          ((mooreSheafCochain J O).obj M)).inv) := by
  have := quasiIso_total_map_mooreSheafBicomplex J π
  have h₂ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreSheafCochain J O)
        (ComplexShape.up ℤ) 0).hom.app M) (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  infer_instance

/-- **The same identification on the base-changed side.** The rows of the base-changed double
complex are not exact functors of the simplicial module — that is where the flatness hypothesis of
[Stacks, Tag 08RX] is consumed — so the row filtration is carried here as the hypothesis `hrow`;
granted it, the two remaining legs are isomorphisms exactly as on the unchanged side, and the
composite is a quasi-isomorphism

`Tot(Z') ⟶ s(M ⊗_O O')`. -/
theorem quasiIso_totalSingleColumn_baseChangedMooreSheafCochain
    (M : PresheafOfModules.{u} (ringPresheaf O))
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0]
    (π : L ⟶ (HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
      (ComplexShape.up ℤ) 0).obj M)
    (hrow : QuasiIso (HomologicalComplex₂.total.map
      (((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
        (ComplexShape.up ℤ)).map π) (ComplexShape.up ℤ))) :
    QuasiIso (HomologicalComplex₂.total.map
          (((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
            (ComplexShape.up ℤ)).map π) (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (changeOfRings θ ⋙ mooreSheafCochain J O') (ComplexShape.up ℤ) 0).hom.app M)
          (ComplexShape.up ℤ) ≫
        (Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
          ((changeOfRings θ ⋙ mooreSheafCochain J O').obj M)).inv) := by
  have h₂ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (changeOfRings θ ⋙ mooreSheafCochain J O') (ComplexShape.up ℤ) 0).hom.app M)
      (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  infer_instance

end Stacks.SimplicialModules

end
