module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualOfStrictlyPerfectComplex

/-!
# The two hypotheses of the derived dual of a strictly perfect complex

`AlgebraicGeometry.RingedSite.derivedDualIsoQDualComplex` identifies the derived dual of a
complex `ℱ^•` of `𝒪`-modules with the dual complex `𝒢^• = 𝑆heafHom^•(ℱ^•, 𝒪)` of
[Stacks, Tag 0FPR]. It asks for two things which a *globally* strictly perfect complex — the
Koszul complex, for instance — does not supply in the shape it wants:

* `hterm`, that each term of `ℱ^•` be **locally** a direct summand of a finite free
  `𝒪`-module, whereas [Stacks, Tag 08FL] gives that globally;
* `hG`, that the dual complex `𝒢^•` be K-flat.

This file supplies both from global strict perfectness.

## Main results

* `AlgebraicGeometry.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isDirectSummandOfFiniteFree`:
  **a direct summand of a finite free `𝒪`-module is locally one.** The covering sieve is the
  whole sieve and the retract is the restriction of the global one.
* `AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_dualSheaf` and
  `AlgebraicGeometry.RingedSite.isZero_dualSheaf`: the dual sheaf of [Stacks, Tag 0FNY] of a
  direct summand of a finite free `𝒪`-module is again one, and the dual sheaf of a zero module
  is zero.
* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_dualComplex`: **the dual complex of a strictly
  perfect complex is strictly perfect.**
* `AlgebraicGeometry.RingedSite.kFlatComplexes_dualComplex`: hence **the dual complex of a
  strictly perfect complex is K-flat**, in the form the derived tensor product of
  [Stacks, Tag 0FPT] reads K-flatness in.

## Implementation notes

**The global-to-local bridge.** `Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` asks,
for every object `U`, for a covering sieve on each member of which the restriction of the module
is a retract of a finite free module. Starting from a global retract `𝟙 = i ≫ r` with
`i : M ⟶ 𝒪^{⊕n}` the sieve can be taken to be `⊤`, and the retract over an arbitrary `V` is the
image of the global one under restriction to the slice,
`SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V`, read through the
comparison `Stacks.SheafOfModules.SliceFinite.freeOverIso` between the free module on the slice and
the restriction of the free module. That comparison is the one built from additivity rather than
from an adjunction, so no products on the site are needed; a finite index type is all it asks for,
and `ULift (Fin n)` is one. The global retract is taken in the plain form
`isDirectSummandOfFiniteFree_iff_free`, which is what the predicate of [Stacks, Tag 08FM] amounts
to at a module universe equal to the universe of the sections of the structure sheaf.

**Why the dual sheaf needs no new construction.** The terms of the dual complex are
`Stacks.SheafOfModules.dualSheaf 𝒪 h 𝓕 = Stacks.SheafOfModules.sheafHom 𝒪 h 𝓕 (unit …)`, whose
underlying presheaf of modules is the internal hom presheaf of [Stacks, Tag 03EM] with the sheaf
condition of that tag, and that is also what
`AlgebraicGeometry.RingedSite.internalHomSheaf X 𝓕 (unit …)` is: the two are the same term, the
sheaf condition being a `Prop` and the two spellings of the sheaf of rings being definitionally
equal. So the dual-sheaf statements below are the `internalHomSheaf` ones —
`AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_internalHomSheaf_unit` and
`AlgebraicGeometry.RingedSite.internalHomSheaf_isZero_of_isZero` — applied as terms, with no
transport inserted. An earlier note said that nothing related the two spellings; nothing needs
to.

**Why strict perfectness and not flatness directly.** Stacks 06YQ wants flatness of the terms
and boundedness above, and both are consequences of strict perfectness of the dual complex,
which is the stronger and shorter statement: the terms are duals of direct summands of finite
free modules, hence again such, and the set of degrees where the dual complex is nonzero is
contained in the negation of the one for `ℱ^•`, because the dual sheaf of a zero module is zero.
The passage to the K-flatness of [Stacks, Tag 0FPT] is then
`AlgebraicGeometry.RingedSite.kFlatComplexes_of_isStrictlyPerfect`.

**No tag is registered.** All four statements are infrastructure: the global-to-local passage
for the hypothesis of [Stacks, Tag 0FNY], and the composite of [Stacks, Tag 08FM] /
[Stacks, Tag 08JJ] (the dual of a direct summand of a finite free module) with [Stacks, Tag
0FPR] (the terms of the dual complex) and [Stacks, Tag 06YQ].

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The global-to-local bridge -/

section Local

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A retract of a finite free `𝒪`-module restricts to a retract of a finite free
`𝒪|_V`-module.** The two morphisms are the restrictions of the global ones, composed with the
comparison `Stacks.SheafOfModules.SliceFinite.freeOverIso` between the free `𝒪|_V`-module on the
index type and the restriction of the free `𝒪`-module on it. -/
theorem nonempty_retract_free_over_of_retract_free (V : X.C) (n : ℕ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (i : M ⟶ SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ULift.{u} (Fin n)))
    (r : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ULift.{u} (Fin n)) ⟶ M)
    (hir : i ≫ r = 𝟙 M) :
    Nonempty (Retract
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj M)
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (ULift.{u} (Fin n)))) :=
  ⟨{ i := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map i ≫
        (Stacks.SheafOfModules.SliceFinite.freeOverIso V (ULift.{u} (Fin n))).inv
     r := (Stacks.SheafOfModules.SliceFinite.freeOverIso V (ULift.{u} (Fin n))).hom ≫
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map r
     retract := by
       rw [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir,
         CategoryTheory.Functor.map_id] }⟩

/-- **A direct summand of a finite free `𝒪`-module is locally a direct summand of a finite free
`𝒪`-module** — the hypothesis of [Stacks, Tag 0FNY] from the global condition of
[Stacks, Tag 08FM]. The covering sieve of an object is the whole sieve, and over each of its
members the retract is the restriction of the global retract. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isDirectSummandOfFiniteFree
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :
    Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) M := by
  obtain ⟨n, i, r, hir⟩ :=
    (_root_.isDirectSummandOfFiniteFree_iff_free
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M).1 hM
  exact fun U => ⟨⊤, X.J.top_mem U, fun V _ _ => ⟨ULift.{u} (Fin n), inferInstance,
    nonempty_retract_free_over_of_retract_free X V n i r hir⟩⟩

end Local

/-! ### The dual sheaf of a direct summand of a finite free module -/

/-- **The dual sheaf of [Stacks, Tag 0FNY] of a direct summand of a finite free `𝒪`-module is
again one.** The dual sheaf `𝑆heafHom(M, 𝒪)` is the internal Hom sheaf of [Stacks, Tag 03EM]
into the structure sheaf, so this is
`AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_internalHomSheaf_unit`. -/
theorem isDirectSummandOfFiniteFree_dualSheaf
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :
    _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (Stacks.SheafOfModules.dualSheaf X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) M) :=
  isDirectSummandOfFiniteFree_internalHomSheaf_unit X M hM

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The dual sheaf of a zero module is zero.** A local section of it is a morphism out of a
zero module on the slice site; the dual sheaf is the internal Hom sheaf of [Stacks, Tag 03EM]
into the structure sheaf, so this is
`AlgebraicGeometry.RingedSite.internalHomSheaf_isZero_of_isZero`. -/
theorem isZero_dualSheaf {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsZero M) :
    IsZero (Stacks.SheafOfModules.dualSheaf X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) M) :=
  internalHomSheaf_isZero_of_isZero X hM

/-! ### The dual complex of a strictly perfect complex -/

section DualComplex

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual complex of [Stacks, Tag 0FPR] of a strictly perfect complex is strictly
perfect.** Its degree-`j` term is the dual sheaf of the degree-`(-j)` term of `ℱ^•`, so it is a
direct summand of a finite free `𝒪`-module by `isDirectSummandOfFiniteFree_dualSheaf`, and it
vanishes whenever the degree-`(-j)` term of `ℱ^•` does, by `isZero_dualSheaf`; the degrees where
the dual complex is nonzero therefore form a subset of the negation of a finite set. -/
theorem isStrictlyPerfect_dualComplex
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hterm : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) (F.X n))
    (hF : _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F) :
    _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm) where
  bounded := by
    refine (hF.bounded.image fun i : ℤ => -i).subset fun j hj => ?_
    simp only [Set.mem_ofPred_eq] at hj
    exact ⟨-j, fun h => hj (isZero_dualSheaf X h), neg_neg j⟩
  termDirectSummand j :=
    isDirectSummandOfFiniteFree_dualSheaf X (F.X (-j)) (hF.termDirectSummand (-j))

/-- **The dual complex of [Stacks, Tag 0FPR] of a strictly perfect complex is K-flat**, in the
form the subcategory of K-flat complexes that the derived tensor product of [Stacks, Tag 0FPT]
is built from reads K-flatness in. This is the hypothesis `hG` of
`AlgebraicGeometry.RingedSite.derivedDualIsoQDualComplex`. -/
theorem kFlatComplexes_dualComplex
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hterm : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) (F.X n))
    (hF : _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F) :
    Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O
      (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm) :=
  kFlatComplexes_of_isStrictlyPerfect X _ (isStrictlyPerfect_dualComplex X F hterm hF)

end DualComplex

end AlgebraicGeometry.RingedSite

end
