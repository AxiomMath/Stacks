module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StdCoverResolution

/-!
# The double complex of the Δ-instance of Stacks 08RX

`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeOfSimplicialModules.lean`
sets up the Δ-instance of [Stacks, Tag 08RX] — for a homomorphism `φ : O ⟶ O'` of simplicial
commutative rings and a degreewise flat simplicial `O`-module `M`, the base-change unit

`s(M) ⟶ s(M ⊗_O O')`

is a quasi-isomorphism as soon as `s(O) ⟶ s(O')` is one — and proves its **column step**: the
unit is a quasi-isomorphism at `PresheafOfModules.stdCover' N`
(`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover'`). This module carries out
the first half of the assembly that turns the column step into the statement: a resolution of `M`
by objects of the shape `stdCover'`, the double complex obtained by applying the two Moore-complex
functors to it, and the comparison of the two total complexes through the column filtration.

## The shape of the argument

Resolve `M` by a bounded above complex `L^•` of simplicial modules each of which is zero or
isomorphic to a `stdCover'` — `Stacks.SimplicialModules.exists_isStdCover_resolution`, which is
[Stacks, Tag 05T7] for the object property `Stacks.SimplicialModules.IsStdCover` — and form the
two double complexes

`Z^{p,q} = s(L^p)^q` and `Z'^{p,q} = s(L^p ⊗_O O')^q`,

together with the morphism `Z ⟶ Z'` given in each column by the base-change unit. Both lie in the
third quadrant, because `L^•` is bounded above by `0` and the Moore complex is concentrated in
cohomological degrees `≤ 0`, so both have total complexes. The column `p` of the morphism is the
base-change unit at `L^p`, a quasi-isomorphism by the column step, so
[Stacks, Tag 0133] for double complexes bounded above
(`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound`) gives

`Tot(Z) ⟶ Tot(Z')` a quasi-isomorphism.

The *row* filtration compares `Tot(Z)` with `s(M)` and `Tot(Z')` with `s(M ⊗_O O')`. On the
unchanged side it is proved here: the row `q` of the double complex is the resolution evaluated
at the object `⦋n⦌` of `Δ` with `q = -n`, and evaluation is exact, so no homology is computed
(`Stacks.SimplicialModules.quasiIso_total_map_mooreBicomplex`). On the base-changed side the rows
are the resolution evaluated at `⦋n⦌` and then tensored with `B` over `O_n`, and *that* is where
the flatness of `M` is consumed; it is carried here as the hypothesis `hrow` of
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_row`, and is the
only thing between this module and the Δ-instance of Tag 08RX. The route to it is
`CochainComplex.KFlat.kFlat_of_flat` — a bounded above complex of flat modules is K-flat, and the
terms of the resolution are sectionwise flat by
`Stacks.SimplicialModules.flat_stdCover_obj` — together with
`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`.

Passing between `Tot` of the double complex of `M[0]` and `s(M)` itself needs no new work:
`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit` identifies the total complex of a double
complex concentrated in the column `0` with that column, Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` identifies the double complex of `M[0]` with the
column `s(M)`, and the second of these is natural in the functor
(`HomologicalComplex.singleMapHomologicalComplex_hom_naturality`), which is what makes the
bottom edge of the square of filtrations the base-change unit at `M`.

## Main definitions

* `Stacks.SimplicialModules.IsStdCover`: the object property "zero, or isomorphic to a
  `PresheafOfModules.stdCover'`", the class of objects the resolution is built from.
* `Stacks.SimplicialModules.mooreBicomplex` and
  `Stacks.SimplicialModules.baseChangedMooreBicomplex`: the two double complexes.
* `Stacks.SimplicialModules.mooreBicomplexBaseChangeMap`: the morphism between them, in each
  column the base-change unit.

## Main results

* `Stacks.SimplicialModules.exists_isStdCover_resolution`: every simplicial module receives a
  degreewise epimorphic quasi-isomorphism from a complex, bounded above by `0`, of objects which
  are zero or `stdCover'`s.
* `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_of_isStdCover`: the column step
  at any such object.
* `Stacks.SimplicialModules.quasiIso_total_mooreBicomplexBaseChangeMap`: **the column
  filtration** — `Tot(Z) ⟶ Tot(Z')` is a quasi-isomorphism.
* `Stacks.SimplicialModules.preservesHomology_mooreCochain_comp_eval`: the rows of the double
  complex are exact functors of the simplicial module.
* `Stacks.SimplicialModules.quasiIso_total_map_mooreBicomplex`: **the row filtration on the
  unchanged side** — `Tot(Z) ≃ s(M)`.
* `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_row`: **the
  Δ-instance of [Stacks, Tag 08RX] from the row filtration on the base-changed side** — the
  base-change unit is a quasi-isomorphism at `M`.
* `Stacks.SimplicialModules.flat_stdCover_obj`: **the sections of a standard cover are a flat
  module** — the flatness the base-changed rows consume on the terms of the resolution.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso

universe u

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {O O' : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}} (φ : O ⟶ O')

/-! ### Resolutions by standard covers -/

/-- **The objects the resolution of [Stacks, Tag 08RX] is built from**: a simplicial module is
either zero or isomorphic to the canonical cover `PresheafOfModules.stdCover' N` of some simplicial
module `N` by free simplicial modules on standard simplices. This is
`PresheafOfModules.IsStdCover` at `C = Δ`; the zero object is included there so that the property
contains zero, which is what [Stacks, Tag 05T7] asks for. -/
abbrev IsStdCover : ObjectProperty (SMod O) :=
  PresheafOfModules.IsStdCover

/-- Every simplicial module is a quotient of an object with the property
`Stacks.SimplicialModules.IsStdCover`, namely of its own standard cover. -/
theorem exists_isStdCover_epi (N : SMod O) :
    ∃ (N' : SMod O) (_ : IsStdCover N') (p : N' ⟶ N), Epi p :=
  PresheafOfModules.exists_isStdCover_epi N

/-- **A resolution of a simplicial module by standard covers**, [Stacks, Tag 05T7] for the object
property `Stacks.SimplicialModules.IsStdCover`: every simplicial module `M` receives a degreewise
epimorphic quasi-isomorphism from a cochain complex concentrated in degrees `≤ 0` each of whose
terms is zero or a `PresheafOfModules.stdCover'`. -/
theorem exists_isStdCover_resolution (M : SMod O) :
    ∃ (L : CochainComplex (SMod O) ℤ)
      (π : L ⟶ (HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M)
      (_ : QuasiIso π) (_ : ∀ n, IsStdCover (L.X n)), L.IsStrictlyLE 0 :=
  PresheafOfModules.exists_isStdCover_resolution M

/-! ### The column step at an arbitrary standard cover -/

/-- **The column step of the Δ-instance of [Stacks, Tag 08RX] at any object of the resolution.**
The base-change unit is a quasi-isomorphism at every object which is zero or isomorphic to a
`PresheafOfModules.stdCover'`; on a zero object both sides vanish, and on a `stdCover'` this is
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover'`. -/
theorem quasiIso_mooreCochainBaseChange_app_of_isStdCover {N : SMod O} (hN : IsStdCover N)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app N) := by
  obtain hz | ⟨N', ⟨e⟩⟩ := hN
  · have h₁ : IsZero ((mooreCochain O).obj N) := Functor.map_isZero _ hz
    have h₂ : IsZero ((changeOfRings φ ⋙ mooreCochain O').obj N) := Functor.map_isZero _ hz
    have : IsIso ((mooreCochainBaseChange' φ).app N) :=
      ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
    infer_instance
  · have key : (mooreCochainBaseChange' φ).app N =
        (mooreCochain O).map e.hom ≫ (mooreCochainBaseChange' φ).app N'.stdCover' ≫
          (changeOfRings φ ⋙ mooreCochain O').map e.inv := by
      rw [← Category.assoc, (mooreCochainBaseChange' φ).naturality e.hom, Category.assoc,
        ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [key]
    have := quasiIso_mooreCochainBaseChange_app_stdCover' φ N' hφ
    infer_instance

/-! ### The double complex and its column filtration -/

/-- The Moore complex vanishes in positive cohomological degrees: the simplicial degree `n` sits
in cohomological degree `-n`. -/
lemma isZero_mooreCochain_X (M : SMod O) (q : ℤ) (hq : 0 < q) :
    IsZero (((mooreCochain O).obj M).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- **The double complex `Z^{p,q} = s(L^p)^q`** of a complex of simplicial modules. -/
abbrev mooreBicomplex (L : CochainComplex (SMod O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((mooreCochain O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

/-- **The base-changed double complex `Z'^{p,q} = s(L^p ⊗_O O')^q`.** -/
abbrev baseChangedMooreBicomplex (L : CochainComplex (SMod O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((changeOfRings φ ⋙ mooreCochain O').mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

/-- **The base-change unit between the two double complexes**, in each column the unit at `L^p`. -/
abbrev mooreBicomplexBaseChangeMap (L : CochainComplex (SMod O) ℤ) :
    mooreBicomplex L ⟶ baseChangedMooreBicomplex φ L :=
  (NatTrans.mapHomologicalComplex (mooreCochainBaseChange' φ) (ComplexShape.up ℤ)).app L

/-- The double complex `mooreBicomplex L` vanishes in positive row degrees `q`. -/
lemma isZero_mooreBicomplex_X_X (L : CochainComplex (SMod O) ℤ) (p q : ℤ) (hq : 0 < q) :
    IsZero (((mooreBicomplex L).X p).X q) :=
  isZero_mooreCochain_X (L.X p) q hq

/-- The double complex `baseChangedMooreBicomplex φ L` vanishes in positive row degrees `q`. -/
lemma isZero_baseChangedMooreBicomplex_X_X (L : CochainComplex (SMod O) ℤ) (p q : ℤ)
    (hq : 0 < q) :
    IsZero (((baseChangedMooreBicomplex φ L).X p).X q) :=
  isZero_mooreCochain_X ((changeOfRings φ).obj (L.X p)) q hq

/-- The column of `mooreBicomplex L` in degree `p` is zero when `L.X p` is zero. -/
lemma isZero_mooreBicomplex_X (L : CochainComplex (SMod O) ℤ) (p : ℤ) (hp : IsZero (L.X p)) :
    IsZero ((mooreBicomplex L).X p) :=
  Functor.map_isZero (mooreCochain O) hp

/-- The column of `baseChangedMooreBicomplex φ L` in degree `p` is zero when `L.X p` is zero. -/
lemma isZero_baseChangedMooreBicomplex_X (L : CochainComplex (SMod O) ℤ) (p : ℤ)
    (hp : IsZero (L.X p)) :
    IsZero ((baseChangedMooreBicomplex φ L).X p) :=
  Functor.map_isZero (changeOfRings φ ⋙ mooreCochain O') hp

/-- For `L` concentrated in degrees `≤ 0`, the double complex `mooreBicomplex L` has a total
complex. -/
instance hasTotal_mooreBicomplex (L : CochainComplex (SMod O) ℤ) [L.IsStrictlyLE 0] :
    (mooreBicomplex L).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_mooreBicomplex_X L p (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (isZero_mooreBicomplex_X_X L)

/-- For `L` concentrated in degrees `≤ 0`, the double complex `baseChangedMooreBicomplex φ L` has a
total complex. -/
instance hasTotal_baseChangedMooreBicomplex (L : CochainComplex (SMod O) ℤ) [L.IsStrictlyLE 0] :
    (baseChangedMooreBicomplex φ L).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_baseChangedMooreBicomplex_X φ L p
      (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (isZero_baseChangedMooreBicomplex_X_X φ L)

/-- **The column filtration of the double complex of the Δ-instance of [Stacks, Tag 08RX]**: the
base-change unit is a quasi-isomorphism on total complexes, because it is one in every column.

This is [Stacks, Tag 0133] for double complexes bounded above
(`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound`) applied to the column step
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_of_isStdCover`. -/
theorem quasiIso_total_mooreBicomplexBaseChangeMap (L : CochainComplex (SMod O) ℤ)
    [L.IsStrictlyLE 0] (hL : ∀ p, IsStdCover (L.X p))
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexBaseChangeMap φ L)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_upperBound (mooreBicomplexBaseChangeMap φ L) 0 0
    (fun p hp => isZero_mooreBicomplex_X L p (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (isZero_mooreBicomplex_X_X L)
    (fun p hp => isZero_baseChangedMooreBicomplex_X φ L p
      (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    (isZero_baseChangedMooreBicomplex_X_X φ L)
    (fun p => quasiIso_mooreCochainBaseChange_app_of_isStdCover φ (hL p) hφ)

/-! ### The row filtration on the unchanged side -/

/-- **Evaluating the Moore complex of a simplicial module in a fixed cohomological degree is an
exact functor of the module.** For `q = -n ≤ 0` it is evaluation at `⦋n⦌`, read on underlying
abelian groups — `AlgebraicTopology.alternatingFaceMapCochainComplexCompEvalIso` is the
identification — and for `q > 0` it is zero. This is what makes the rows of the double complex
compute no homology of their own. -/
instance preservesHomology_mooreCochain_comp_eval (q : ℤ) :
    (mooreCochain O ⋙
      HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q).PreservesHomology := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    subst hn
    have e : mooreCochain O ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
        PresheafOfModules.toPresheaf (ringPresheaf O) ⋙
          (evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj (op (SimplexCategory.mk n)) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (PresheafOfModules.toPresheaf (ringPresheaf O))
          (alternatingFaceMapCochainComplexCompEvalIso AddCommGrpCat.{u} n)
    have := preservesFiniteLimits_of_natIso e.symm
    have := preservesFiniteColimits_of_natIso e.symm
    infer_instance
  · exact Functor.preservesHomology_of_map_exact _
      fun S _ => ShortComplex.exact_of_isZero_X₂ _ (isZero_mooreCochain_X S.X₂ q hq)

/-- **The row filtration of the double complex, on the unchanged side**: a quasi-isomorphism of
complexes of simplicial modules, both bounded above by `0`, stays one on the total complexes of
the associated double complexes. The rows are exact functors of the simplicial module
(`Stacks.SimplicialModules.preservesHomology_mooreCochain_comp_eval`), so no homology is
computed; this is [Stacks, Tag 0133] for double complexes bounded above with the hypothesis on
the rows. -/
theorem quasiIso_total_map_mooreBicomplex {L L' : CochainComplex (SMod O) ℤ} (π : L ⟶ L')
    [L.IsStrictlyLE 0] [L'.IsStrictlyLE 0] [QuasiIso π] :
    QuasiIso (HomologicalComplex₂.total.map
      (((mooreCochain O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
      (ComplexShape.up ℤ)) := by
  have hz : ∀ (K : CochainComplex (SMod O) ℤ) [K.IsStrictlyLE 0] (p q : ℤ), 0 < p ∨ 0 < q →
      IsZero (((mooreBicomplex K).flip.X q).X p) := by
    intro K _ p q hpq
    rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q)
        (isZero_mooreBicomplex_X K p (CochainComplex.isZero_of_isStrictlyLE K 0 p hp))
    · exact isZero_mooreBicomplex_X_X K p q hq
  refine quasiIso_total_map_of_upperBound_flip _ 0 0 (fun p q hpq => hz L p q hpq)
    (fun p q hpq => hz L' p q hpq) (fun q => ?_)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology π
    (mooreCochain O ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q)

/-! ### The Δ-instance of Tag 08RX, reduced to the flat row step -/

/-- Two out of three on total complexes for a commuting square of double complexes. -/
private theorem quasiIso_total_map_of_comp_eq
    {K₁ K₂ K₃ K₄ : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K₁.HasTotal (ComplexShape.up ℤ)] [K₂.HasTotal (ComplexShape.up ℤ)]
    [K₃.HasTotal (ComplexShape.up ℤ)] [K₄.HasTotal (ComplexShape.up ℤ)]
    (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₄) (c : K₁ ⟶ K₃) (d : K₃ ⟶ K₄) (h : a ≫ b = c ≫ d)
    [QuasiIso (HomologicalComplex₂.total.map a (ComplexShape.up ℤ))]
    [QuasiIso (HomologicalComplex₂.total.map c (ComplexShape.up ℤ))]
    [QuasiIso (HomologicalComplex₂.total.map d (ComplexShape.up ℤ))] :
    QuasiIso (HomologicalComplex₂.total.map b (ComplexShape.up ℤ)) := by
  have : QuasiIso (HomologicalComplex₂.total.map a (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map b (ComplexShape.up ℤ)) := by
    rw [← HomologicalComplex₂.total.map_comp, h, HomologicalComplex₂.total.map_comp]
    infer_instance
  exact quasiIso_of_comp_left (HomologicalComplex₂.total.map a (ComplexShape.up ℤ)) _

/-- The base-change unit is a quasi-isomorphism at `M` once it is one on the total complexes of
the double complexes of `M[0]`. -/
private theorem quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_single (M : SMod O)
    (hbot : QuasiIso (HomologicalComplex₂.total.map
      ((NatTrans.mapHomologicalComplex (mooreCochainBaseChange' φ) (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M))
      (ComplexShape.up ℤ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app M) := by
  let := hasTotal_singleColumn ((mooreCochain O).obj M) (0 : ℤ)
  let := hasTotal_singleColumn ((changeOfRings φ ⋙ mooreCochain O').obj M) (0 : ℤ)
  have hiso₂ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (changeOfRings φ ⋙ mooreCochain O')
        (ComplexShape.up ℤ) 0).hom.app M) (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  have hiso₁ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochain O)
        (ComplexShape.up ℤ) 0).hom.app M) (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  have hsingle : QuasiIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.single (CochainComplex AddCommGrpCat.{u} ℤ)
        (ComplexShape.up ℤ) 0).map ((mooreCochainBaseChange' φ).app M)) (ComplexShape.up ℤ)) :=
    quasiIso_total_map_of_comp_eq _ _ _ _
      (HomologicalComplex.singleMapHomologicalComplex_hom_naturality (ComplexShape.up ℤ) 0
        (mooreCochainBaseChange' φ) M).symm
  have hcomp : QuasiIso ((mooreCochainBaseChange' φ).app M ≫
      (Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
        ((changeOfRings φ ⋙ mooreCochain O').obj M)).hom) := by
    rw [Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso_hom_naturality]
    infer_instance
  exact quasiIso_of_comp_right ((mooreCochainBaseChange' φ).app M)
    (Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
      ((changeOfRings φ ⋙ mooreCochain O').obj M)).hom

/-- **The Δ-instance of [Stacks, Tag 08RX] from the row filtration on the base-changed side.**
Let `L^• ⟶ M[0]` be a resolution of a simplicial `O`-module by standard covers. If the
base-change unit is a quasi-isomorphism at the structure module — the hypothesis `hφ`, which is
`s(O) ⟶ s(O')` — and if base change takes the resolution to a quasi-isomorphism on total
complexes — the hypothesis `hrow`, which is where the flatness of `M` is consumed — then the
base-change unit is a quasi-isomorphism at `M`.

The proof is three applications of two out of three. The square

`Tot(Z) ⟶ Tot(Z')`, `Tot(Z) ⟶ Tot(W)`, `Tot(Z') ⟶ Tot(W')`

commutes by naturality of the unit, its top edge is the column filtration
(`Stacks.SimplicialModules.quasiIso_total_mooreBicomplexBaseChangeMap`) and its left edge the row
filtration (`Stacks.SimplicialModules.quasiIso_total_map_mooreBicomplex`), so its bottom edge is
a quasi-isomorphism; and the bottom edge is the unit at `M`, read through the identification of
the total complex of a double complex concentrated in column zero with that column
(`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit`) and Mathlib's comparison
`single ⋙ F.mapHomologicalComplex ≅ F ⋙ single`, which is natural in `F`
(`HomologicalComplex.singleMapHomologicalComplex_hom_naturality`). -/
theorem quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_row (M : SMod O)
    (L : CochainComplex (SMod O) ℤ) [L.IsStrictlyLE 0] (hL : ∀ p, IsStdCover (L.X p))
    (π : L ⟶ (HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M) [QuasiIso π]
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ)))
    (hrow : QuasiIso (HomologicalComplex₂.total.map
      (((changeOfRings φ ⋙ mooreCochain O').mapHomologicalComplex
          (ComplexShape.up ℤ)).map π) (ComplexShape.up ℤ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app M) := by
  have hcol : QuasiIso (HomologicalComplex₂.total.map
      (mooreBicomplexBaseChangeMap φ L) (ComplexShape.up ℤ)) :=
    quasiIso_total_mooreBicomplexBaseChangeMap φ L hL hφ
  have hrowL : QuasiIso (HomologicalComplex₂.total.map
      (((mooreCochain O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
      (ComplexShape.up ℤ)) := quasiIso_total_map_mooreBicomplex π
  have hbot : QuasiIso (HomologicalComplex₂.total.map
      ((NatTrans.mapHomologicalComplex (mooreCochainBaseChange' φ) (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M))
      (ComplexShape.up ℤ)) :=
    quasiIso_total_map_of_comp_eq _ _ _ _
      ((NatTrans.mapHomologicalComplex (mooreCochainBaseChange' φ)
        (ComplexShape.up ℤ)).naturality π)
  exact quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_single φ M hbot

/-! ### Standard covers are sectionwise free -/

/-- The commutative ring structure on a section ring of the presheaf of rings underlying a
presheaf of *commutative* rings, which instance search does not see through
`Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf`. -/
instance commRing_ringPresheaf_obj (n : SimplexCategoryᵒᵖ) :
    CommRing ↥((ringPresheaf O).obj n) :=
  inferInstanceAs (CommRing ↥(O.obj n))

/-- **A coproduct of flat modules is flat**: it is the direct sum of the family. -/
lemma flat_sigma {R : Type u} [CommRing R] {I : Type u} (F : I → ModuleCat.{u} R)
    (h : ∀ i, Module.Flat R (F i)) : Module.Flat R ↥(∐ F) := by
  classical
  have : Module.Flat R (DirectSum I fun i => ↥(F i)) := Module.Flat.directSum
  exact Module.Flat.of_linearEquiv (ModuleCat.coprodIsoDirectSum F).toLinearEquiv

/-- **The sections of a free presheaf of modules are a free module**, hence flat. -/
lemma flat_free_obj (F : SimplexCategoryᵒᵖ ⥤ Type u) (n : SimplexCategoryᵒᵖ) :
    Module.Flat ↥((ringPresheaf O).obj n)
      ↥(((PresheafOfModules.free (ringPresheaf O)).obj F).obj n) :=
  inferInstanceAs (Module.Flat ↥((ringPresheaf O).obj n) (F.obj n →₀ ↥((ringPresheaf O).obj n)))

/-- **The sections of a standard cover are a flat module.** The cover is a coproduct of free
presheaves of modules on universe-lifted representables, evaluation at an object of `Δ` preserves
that coproduct, and the sections of a free presheaf of modules are a free module. This is the
flatness that the row direction of the Δ-instance of [Stacks, Tag 08RX] consumes on the terms of
the resolution. -/
lemma flat_stdCover_obj (N : SMod O) (n : SimplexCategoryᵒᵖ) :
    Module.Flat ↥((ringPresheaf O).obj n) ↥((N.stdCover').obj n) := by
  classical
  have e := Limits.PreservesCoproduct.iso (PresheafOfModules.evaluation (ringPresheaf O) n)
    (fun m : N.Elements => (PresheafOfModules.free (ringPresheaf O)).obj
      (uliftYoneda.{u}.obj m.1.unop))
  have : Module.Flat ↥((ringPresheaf O).obj n)
      ↥(∐ fun m : N.Elements => (PresheafOfModules.evaluation (ringPresheaf O) n).obj
        ((PresheafOfModules.free (ringPresheaf O)).obj (uliftYoneda.{u}.obj m.1.unop))) :=
    flat_sigma _ (fun m => flat_free_obj (uliftYoneda.{u}.obj m.1.unop) n)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Stacks.SimplicialModules

end
