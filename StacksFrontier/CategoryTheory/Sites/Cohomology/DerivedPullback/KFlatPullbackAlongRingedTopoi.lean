module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of K-flat complexes along a morphism of ringed topoi

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi and let `K` be a K-flat
complex of `O`-modules with flat terms.  Then `f^*K` is a K-flat complex of `O'`-modules.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_isColimit`: **the
  engine.** The pullback of a
  sequential colimit of bounded above complexes of flat modules is K-flat.  This is the one
  thing about `f^*` that the source's argument really uses, and the reason the argument is
  shaped the way it is: K-flatness itself does not transport along `f^*`, while each clause of
  "colimit of bounded above complexes with flat terms" does.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_isFlat_cycles`: the
  pullback of a complex with flat
  terms and flat cycles is K-flat — the acyclic case of the source's argument, read through the
  canonical truncations.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X`: **the flat-terms
  assertion of Tag 0G7E**, from
  `PullbackPreservesIsFlat` (Tag 05VD) alone and with nothing about K-flatness in it.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kernelSequence_resolution_facts` and
  `kFlat_pullbackComplex_of_shortExact`: the two steps of the main argument, split off so that
  the expensive `ShortComplex.kernelSequence` elaboration happens once per declaration.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex`: **the K-flatness assertion
  of Tag 0G7E**, from the
  three inputs `PullbackPreservesIsFlat` (Tag 05VD), `PullbackPreservesShortExact` (Tag 0G6R)
  and `CyclesIsFlat` (Tag 0G7C), each of which is written out below as a named predicate so
  that the contract is auditable.

## Implementation notes

The three hypotheses of `kFlat_pullbackComplex` are exactly the three results of the source's
proof that are about something other than K-flatness.  **One of the three is now proved in the
tree, and the other two are not:**

* `PullbackPreservesIsFlat f` is Stacks Tag 05VD, the SGA 4 statement that pullback along a
  morphism of ringed topoi preserves flatness of a module.  No declaration in either tree
  concludes it.
* `PullbackPreservesShortExact f` is Stacks Tag 0G6R, that pullback keeps a short exact
  sequence of modules short exact when its third term is flat.  In the source it is deduced
  from 05VD and 03EX; `StacksPullbackFactorization` builds the
  factorization that deduction runs through.  No declaration in either tree concludes it.
* `CyclesIsFlat O` is Stacks Tag 0G7C, that the cycles of an acyclic K-flat complex with flat
  terms are flat.  This one **is** discharged, unconditionally and for every
  `RingedTopos.{v₁, u₁, w₁}` with the three universes independent, by
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`.
  That same development restates
  `kFlat_pullbackComplex` on the two remaining hypotheses, and gives the acyclic case of
  Tag 0G7E on `PullbackPreservesIsFlat` alone.

**The morphism-of-sites hypothesis.**  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor `f.u` be *continuous*; left exactness of `f⁻¹` is not a field of it, and
`AlgebraicGeometry.RingedToposSiteHom.toToposHom` takes `f.u.IsMorphismOfSites Y.J X.J` as a
separate argument precisely for that reason.  Both 05VD and 0G6R are statements about a
morphism of *ringed topoi*, whose definition in the source includes that exactness, and both
are **false** for a merely continuous `f.u`: taking the one-point site over the source
`WalkingParallelPair`, both sides carrying the topology `⊥`, makes `f^*` a cokernel functor,
under which a flat module of ranks `1` and `3` on the two objects pulls back to `ℤ/2`.
So `PullbackPreservesIsFlat` and `PullbackPreservesShortExact` each carry
`f.u.IsMorphismOfSites Y.J X.J` as a hypothesis, and the results that consume them carry it
too.  `CyclesIsFlat` mentions no morphism and needs no such hypothesis.

`Functor.isMorphismOfSites_iff_preservesFiniteLimits` identifies that hypothesis with left
exactness of `f⁻¹` on sheaves of sets, and
`Functor.isMorphismOfSites_of_isFiltered_op` (Stacks 00X5) and
`Functor.isMorphismOfSites_of_isTerminal` (Stacks 00X6) are the two standard ways to supply
it.

Everything else in the source's proof is discharged here.  The shape of the argument:

1. Resolve `K` by `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit`: a termwise
  surjective
   quasi-isomorphism `α : colim D ⟶ K` out of the colimit of a sequence of bounded above
   complexes of flat modules.  That presentation — rather than K-flatness of `colim D` — is
   what survives `f^*`, which is why 06YS is used in that form.
2. `Λ := colim D` is K-flat with flat terms, by 06YQ/06YR and 03EU.
3. `M := ker α` sits in a short exact sequence `0 ⟶ M ⟶ Λ ⟶ K ⟶ 0` of complexes.  Its terms
   are flat by Tag 03EY, it is K-flat by Tag 0G7B, and it is acyclic because `α` is a
   quasi-isomorphism.
4. `f^*M` is K-flat by `kFlat_pullbackComplex_of_isFlat_cycles`, using 0G7C for the cycles;
   `f^*Λ` is K-flat by the engine.
5. Pulling the sequence back stays short exact (0G6R, degreewise), and Tag 0G7B then gives
   K-flatness of `f^*K`.

The acyclic case is read through `CochainComplex.truncLE` rather than through a second
application of the resolution ladder: a complex is the sequential colimit of its canonical
truncations (`Stacks.SheafOfModules.truncLECocone_isColimit`), the `n`-th of which is
bounded above by `n` and has terms `K^i` for `i < n`, the cycles in degree `n`, and zero
above — so flat terms and flat cycles are exactly what the engine needs.  Acyclicity of `M`
enters only through 0G7C.

**Tagging.**  Stacks 0G7E has three clauses.  Exactly one of them is covered here, and the
covering set is deliberately partial:

* "degreewise pullback" is the clause asserting the `PreservesZeroMorphisms` instance of the
  module pullback — the thing that makes the degreewise pullback functor on complexes exist.
  `pullbackTopos_preservesZeroMorphisms` below *is* that statement, carries no hypothesis the
  source lacks, and is proved; it carries the tag.
* "K-flatness" is the clause asserting K-flatness of `f^*K`, which is `kFlat_pullbackComplex`
  below.  **Untagged**, because it carries `PullbackPreservesIsFlat` and
  `PullbackPreservesShortExact`, two `Prop` hypotheses the source does not have and which no
  declaration in either tree concludes.
* "flat terms" is the clause asserting flatness of the pulled-back terms, which *is*
  Stacks 05VD, i.e. `PullbackPreservesIsFlat` itself.  **Untagged**, for the same reason.

**Universes.** Both ringed topoi are taken at `RingedTopos.{u, u, u}`: the object, morphism
and section universes agree. This narrowing is **inherited, not chosen here**, and it is forced
**three** independent ways:

* `SheafOfModules.pullback`, which requires both sites to be small in the universe of the
  sections of the structure sheaves;
* Tag 03EX, through the extension-by-zero resolutions its proof runs through;
* `CategoryTheory.Functor.IsMorphismOfSites`, the hypothesis `hmos` below is stated with: it is
  declared for `{C D : Type u}` with `SmallCategory` on both, so it collapses the object and
  morphism universes of the two sites as well.  This third forcing is the one that bites on the
  *hypothesis* rather than on the conclusion, and it is also recorded in the implementation
  notes of `StacksPullbackFactorization`.

The same narrowing is carried by the already-tagged chain this file sits on (`06YS`, `03EX`,
`03EY`, `0G7B`), which take their tags under collapsed universes while the Stacks statements
have independent ones.

## References

* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.Sheaves.DerivedPullback.KFlatPullback

/-- Weak sheafification of abelian presheaves, from the global instance
`Stacks.SheafOfModules.coefficientSheafification`. It is made a local instance of high priority
so that the declarations below find it rather than the section variable
`[HasSheafify X.J AddCommGrpCat.{u}]`, and so do not depend on that variable. -/
private abbrev hasWeakSheafifyAddCommGrpCatKFlat (X : AlgebraicGeometry.RingedTopos.{u, u, u}) :
    HasWeakSheafify X.J AddCommGrpCat.{u} :=
  inferInstance

/-- Sheafification of abelian presheaves, from the global instance
`Stacks.SheafOfModules.coefficientSheafification`, made a local instance of high priority for the
same reason. -/
private abbrev hasSheafifyAddCommGrpCatKFlat (X : AlgebraicGeometry.RingedTopos.{u, u, u}) :
    HasSheafify X.J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCatKFlat hasSheafifyAddCommGrpCatKFlat

/- Since Mathlib v4.35.0 instance search would reach the section variable
`HasSheafify X.J AddCommGrpCat` through `instHasWeakSheafifyOfHasSheafify`, making it a
hypothesis of the declarations below; erasing the bridge restores the pre-bump behaviour. -/
attribute [-instance] instHasWeakSheafifyOfHasSheafify

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pullback of sheaves of modules preserves zero morphisms, being additive.  This is what
makes the degreewise pullback functor on complexes available. -/
@[stacks 0G7E "degreewise pullback"]
instance pullbackTopos_preservesZeroMorphisms
    (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) from
        f.pullbackTopos).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive f.pullbackTopos

/-- The degreewise pullback of complexes of modules along a morphism of ringed topoi. -/
abbrev pullbackComplex (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) from
      f.pullbackTopos).mapHomologicalComplex (ComplexShape.up ℤ)

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The degreewise pullback of a complex bounded above by `b` is bounded above by `b`, since
`f^*` carries a zero module to a zero module. -/
lemma isStrictlyLE_pullbackComplex (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b] : ((pullbackComplex f).obj L).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero
    (C := SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (D := SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    f.pullbackTopos (L.isZero_of_isStrictlyLE b i hi)

/-! ### The three inputs the source's proof takes from elsewhere -/

/-- **Stacks Tag 05VD** for the pullback of modules along a morphism of ringed topoi:
*if* the underlying continuous functor is a morphism of sites — so that `f` really is a
morphism of ringed topoi and `f⁻¹` is exact — then pullback preserves flatness.

The morphism-of-sites hypothesis is part of the statement of the source, and it cannot be
dropped: `AlgebraicGeometry.RingedToposSiteHom` asks only for continuity of `f.u`, and for a
merely continuous functor `f^*` need not be exact and the conclusion is false.  See the
implementation notes. -/
def PullbackPreservesIsFlat (f : AlgebraicGeometry.RingedToposSiteHom X Y) : Prop :=
  f.u.IsMorphismOfSites Y.J X.J →
    ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) M →
        AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
          (f.pullbackTopos.obj M)

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- **The flat-terms assertion of Tag 0G7E**, on `PullbackPreservesIsFlat` (Stacks 05VD) alone.
The source's statement of 0G7E concludes that `f^*K` is K-flat *and has flat terms*; this is the
second half, and it needs nothing about K-flatness.  The term of the degreewise pullback in
degree `i` is `f^*(K^i)` on the nose, so the content is exactly one application of 05VD per
degree.

This is the clause recorded under the string "flat terms", which the source delegates to
Stacks 05VD.  No tag is placed here: the hypothesis `hpf` is a `Prop` the source does not
carry and which no declaration in either tree concludes, so a tag would read as progress on a
clause that is still open. -/
theorem isFlat_pullbackComplex_X (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (((pullbackComplex f).obj K).X i) :=
  hpf hmos _ (hflatK i)

/-- **Stacks Tag 0G6R**: for a morphism of ringed topoi — the underlying continuous functor
being a morphism of sites — pullback keeps a short exact sequence of modules short exact when
its third term is flat.

As for `PullbackPreservesIsFlat`, the morphism-of-sites hypothesis is part of the statement of
the source and cannot be dropped. -/
def PullbackPreservesShortExact (f : AlgebraicGeometry.RingedToposSiteHom X Y) : Prop :=
  f.u.IsMorphismOfSites Y.J X.J →
    ∀ T : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)),
      T.ShortExact → AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) T.X₃ →
        (@ShortComplex.map
          (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          inferInstance inferInstance inferInstance inferInstance T f.pullbackTopos
          (Functor.preservesZeroMorphisms_of_additive f.pullbackTopos)).ShortExact

section Cycles

-- `CyclesIsFlat` is stated at arbitrary universes, where only the section bridge applies.
attribute [local instance] instHasWeakSheafifyOfHasSheafify

universe v₁ u₁ w₁

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]

/-- **Stacks Tag 0G7C**: the cycles of an acyclic K-flat complex with flat terms are flat.

This one is a statement about a single ringed topos and mentions no morphism, so — unlike
`PullbackPreservesIsFlat` and `PullbackPreservesShortExact` — it carries no
morphism-of-sites hypothesis.

Its three universes are independent of one another and of the `RingedTopos.{u, u, u}` the rest
of this file is written over, so the predicate can be read at an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`; setting all three to `u` gives the form
`kFlat_pullbackComplex` below consumes. -/
def CyclesIsFlat (O : AlgebraicGeometry.RingedTopos.{v₁, u₁, w₁})
    [O.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
    [HasSheafify O.J AddCommGrpCat.{w₁}]
    [O.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} O.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} O.O).obj M).Additive]
    [∀ (K₁ K₂ :
        CochainComplex (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf O.O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w₁, w₁, w₁} O.O)
        (ComplexShape.up ℤ)] : Prop :=
  ∀ M : CochainComplex (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf O.O)) ℤ,
    M.Acyclic → Stacks.SheafOfModules.KFlat.KFlat O.O M →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v₁, u₁, w₁, w₁} (O := O.O) (M.X i)) →
      ∀ n : ℤ,
        AlgebraicGeometry.SheafOfModules.IsFlat.{v₁, u₁, w₁, w₁} (O := O.O) (M.cycles n)

end Cycles

/-! ### Flatness of the terms of a canonical truncation -/

section Trunc

variable {Z : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify Z.J AddCommGrpCat.{u}] in
/-- The terms of the canonical truncation `τ_{≤ n}M` of a complex with flat terms and flat
cycles are flat: in degree `i < n` the term is `M^i`, in degree `n` it is the cycles in
degree `n`, and above `n` it is zero. -/
theorem isFlat_truncLE_X
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O)
      (M.X i))
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O)
      (M.cycles n))
    (n i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O)
      ((M.truncLE n).X i) := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Z.O (M.truncLEXIso n i hi).symm
      (hflat i)
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Z.O (M.truncLEXIsoCycles i).symm
      (hcyc i)
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero Z.O
      ((M.truncLE n).isZero_of_isStrictlyLE n i hi)

end Trunc

/-! ### The engine: what the pullback does to a colimit of bounded above flat complexes -/

section Engine

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)] in
/-- The total complex of a double complex of `O_X`-modules exists: in each total degree it is
the coproduct of the terms along the antidiagonal `p + r = n`, which `Mod(O_X)` has. The
K-flatness criteria of `CochainComplex.KFlatBifunctor` take this as a hypothesis quantified
over the double complex, and instance search does not solve that goal here even though it
solves it for each fixed double complex, so it is supplied by hand below. -/
lemma hasTotal_sheafOfModules :
    ∀ K : HomologicalComplex₂ (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ), K.HasTotal (ComplexShape.up ℤ) :=
  fun _ ↦ inferInstance

omit [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- The pullback of a bounded above complex of flat modules is K-flat: its terms are flat by
Tag 05VD and it is still bounded above, so Tag 06YQ applies on the source. -/
theorem kFlat_pullbackComplex_of_isStrictlyLE (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (L.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj L) := by
  have : ((pullbackComplex f).obj L).IsStrictlyLE b := isStrictlyLE_pullbackComplex f L b
  have := hasTotal_sheafOfModules (X := X)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ _ b
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor X.O)
      (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules X.O) fun q ↦ ?_
  exact Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.O _ (hpf hmos _ (hflat q)) q

omit [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- **The engine.** The pullback of a sequential colimit of bounded above complexes of flat
modules is K-flat: `f^*` is a left adjoint, so it commutes with the colimit degreewise, and
each stage pulls back to a bounded above complex of flat modules. -/
theorem kFlat_pullbackComplex_of_isColimit (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) ((D.obj n).X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj c.pt) := by
  have hp : PreservesColimit D (pullbackComplex f) :=
    @CochainComplex.KFlat.preservesColimit_mapHomologicalComplex
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      inferInstance inferInstance inferInstance inferInstance
      ℤ (ComplexShape.up ℤ) ℕ inferInstance inferInstance D f.pullbackTopos
      (Functor.preservesZeroMorphisms_of_additive f.pullbackTopos) inferInstance
  have := hasTotal_sheafOfModules (X := X)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _
    ((pullbackComplex f).mapCocone c) (isColimitOfPreserves (pullbackComplex f) hc)
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor X.O)
      (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules X.O) fun n ↦ ?_
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact kFlat_pullbackComplex_of_isStrictlyLE f hmos hpf (D.obj n) b (hflat n)

omit [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- The engine read at the colimit cocone: the pullback of `colim D`, for `D` a sequence of
bounded above complexes of flat modules, is K-flat.  This is the shape in which
`Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit` hands the resolution back. -/
theorem kFlat_pullbackComplex_colimit (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) ((D.obj n).X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj (colimit D)) :=
  kFlat_pullbackComplex_of_isColimit f hmos hpf D (colimit.cocone D) (colimit.isColimit D)
    hLE hflat

end Engine

/-! ### The K-flatness assertion of Tag 0G7E -/

section Main

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]

omit [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)] in
/-- The pullback of a complex with flat terms and flat cycles is K-flat: such a complex is
the sequential colimit of its canonical truncations, each of which is bounded above with flat
terms, so the engine applies.  This is the acyclic case of the source's argument; acyclicity
itself is used only to know the cycles are flat (Tag 0G7C). -/
theorem kFlat_pullbackComplex_of_isFlat_cycles (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (M.X i))
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (M.cycles n)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj M) :=
  kFlat_pullbackComplex_of_isColimit f hmos hpf
    (Stacks.SheafOfModules.truncLESequence M) (Stacks.SheafOfModules.truncLECocone M)
    (Stacks.SheafOfModules.truncLECocone_isColimit M)
    (fun n ↦ ⟨(n : ℤ), inferInstanceAs ((M.truncLE (n : ℤ)).IsStrictlyLE (n : ℤ))⟩)
    (fun n i ↦ isFlat_truncLE_X M hflat hcyc (n : ℤ) i)

/-- **The acyclic case of Tag 0G7E**, on `CyclesIsFlat` (Tag 0G7C) as a hypothesis: the pullback
of an acyclic K-flat complex with flat terms is K-flat.  0G7C turns the hypotheses into flatness
of the cycles, and `kFlat_pullbackComplex_of_isFlat_cycles` finishes; acyclicity and K-flatness
of `M` are used for nothing else.
  `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_acyclic`
is this statement with that hypothesis discharged. -/
theorem kFlat_pullbackComplex_of_acyclic_of_cyclesIsFlat
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (hcyc : CyclesIsFlat Y)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hacyc : M.Acyclic) (hM : Stacks.SheafOfModules.KFlat.KFlat Y.O M)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (M.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj M) :=
  kFlat_pullbackComplex_of_isFlat_cycles f hmos hpf M hflat (hcyc M hacyc hM hflat)

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)] in
/-- Pullback of a short exact sequence of complexes whose third complex has flat terms is
short exact, degree by degree, by Tag 0G6R. -/
theorem shortExact_map_pullbackComplex (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hex : PullbackPreservesShortExact f)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      Y.O)) ℤ))
    (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (S.X₃.X i)) :
    (S.map (pullbackComplex f)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  exact hex hmos (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
    (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)) (hflat i)

/-- **The kernel of a resolution.**  Let `α : L ⟶ K` be a termwise surjective
quasi-isomorphism onto a K-flat complex `K` with flat terms, out of a K-flat `L` with flat
terms.  Then the kernel sequence `0 ⟶ ker α ⟶ L ⟶ K ⟶ 0` is short exact and `ker α` has flat
terms (Tag 03EY), is K-flat (Tag 0G7B) and is acyclic.

This is the `O`-side half of Tag 0G7E and mentions no morphism of ringed topoi.  It is a
separate declaration, as are the two that follow, because elaborating
`ShortComplex.kernelSequence α` over complexes of sheaves of modules costs a few tens of
thousands of heartbeats *per occurrence*, so the dozen occurrences of the whole argument
exceed the elaboration budget of any single declaration. -/
theorem kernelSequence_resolution_facts :
    letI : Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
      Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u} Y.J
    ∀ {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (_hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (_hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (_hΛflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
    (_hΛkflat : Stacks.SheafOfModules.KFlat.KFlat Y.O L)
    (α : L ⟶ K) (_hqis : QuasiIso α) (_hαepi : Epi α),
    (ShortComplex.kernelSequence α).ShortExact ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
        ((ShortComplex.kernelSequence α).X₁.X i)) ∧
      Stacks.SheafOfModules.KFlat.KFlat Y.O (ShortComplex.kernelSequence α).X₁ ∧
      (ShortComplex.kernelSequence α).X₁.Acyclic := by
  let : Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
    Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u} Y.J
  intro K L hK hflatK hΛflat hΛkflat α hqis hαepi
  have hS : (ShortComplex.kernelSequence α).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact α) inferInstance hαepi
  refine ⟨hS, fun i ↦ ?_, ?_, hS.acyclic_X₁ hqis⟩
  · exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact Y.O
      ((ShortComplex.kernelSequence α).map (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)) (hΛflat i) (hflatK i)
  · exact Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_left_of_shortExact Y.O
      (ShortComplex.kernelSequence α) hS hflatK hΛkflat hK

omit [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)] in
/-- **The engine at the middle term of a kernel sequence.**  The middle term of the kernel short
complex of `α` is the source of `α`, so for `α` out of a colimit cocone the engine applies to
`(ShortComplex.kernelSequence α).X₂` directly.  Recorded at an abstract cocone `c`, where the
two spellings agree by projection. -/
theorem kFlat_pullbackComplex_kernelSequence_X₂
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) ((D.obj n).X i))
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (α : c.pt ⟶ K) :
    Stacks.SheafOfModules.KFlat.KFlat X.O
      ((pullbackComplex f).obj (ShortComplex.kernelSequence α).X₂) :=
  kFlat_pullbackComplex_of_isColimit f hmos hpf D c hc hLE hflat

omit [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)] in
/-- **Tag 0G7E, the two-out-of-three step.**  For a short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0`
of complexes of `O`-modules with `S₃` of flat terms, `f^*S₃` is K-flat as soon as `f^*S₁` and
`f^*S₂` are:  the pulled-back sequence is still short exact (Tag 0G6R) and Tag 0G7B gives the
third term.  Stated at an abstract short complex. -/
theorem kFlat_pullbackComplex_of_shortExact (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (hex : PullbackPreservesShortExact f)
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ))
    (hS : S.ShortExact)
    (hflat₃ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (S.X₃.X i))
    (h₁ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₁))
    (h₂ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₂)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₃) :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact X.O
    (S.map (pullbackComplex f))
    (shortExact_map_pullbackComplex f hmos hex S hS hflat₃)
    (fun i ↦ hpf hmos _ (hflat₃ i)) h₁ h₂

/-- **The K-flatness assertion of Stacks Tag 0G7E**, from Tags 05VD, 0G6R and 0G7C.

The pullback of a K-flat complex of `O`-modules with flat terms along a morphism of ringed
topoi is a K-flat complex of `O'`-modules. -/
theorem kFlat_pullbackComplex (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (hex : PullbackPreservesShortExact f)
    (hcyc : CyclesIsFlat Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj K) := by
  obtain ⟨D, α, hLE, hDflat, hqis, hepi⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit Y.O K
  obtain ⟨hS, hMflat, hMkflat, hMacyc⟩ :=
    kernelSequence_resolution_facts hK hflatK
      (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X Y.O D hDflat)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat Y.O D
        hLE hDflat) α hqis (HomologicalComplex.epi_of_epi_f α hepi)
  exact kFlat_pullbackComplex_of_shortExact f hmos hpf hex
    (ShortComplex.kernelSequence α) hS hflatK
    (kFlat_pullbackComplex_of_acyclic_of_cyclesIsFlat f hmos hpf hcyc _ hMacyc hMkflat hMflat)
    (kFlat_pullbackComplex_kernelSequence_X₂ f hmos hpf D (colimit.cocone D)
      (colimit.isColimit D) hLE hDflat α)

end Main

end Stacks.Sheaves.DerivedPullback.KFlatPullback

end

end
