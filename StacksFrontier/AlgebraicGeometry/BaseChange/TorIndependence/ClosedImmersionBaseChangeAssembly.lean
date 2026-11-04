module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeCounitChase

/-!
# The assembly of the open equality of Stacks 0E23

`Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQKFlat` is the one statement
Stacks 0E23 waits on, and this file carries out the diagram chase that reduces it, at one point
and one complex, to an identity between the four local rings of the square alone.

## The chase

Both sides of `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQAt` factor
through one and the same leading morphism, the stalk formula for `f` at `i' w` taken at `Ri_* K`.
On the left that factorization takes nine rungs, in `lhsKeyChase` and `lhsChase`:

1. `AlgebraicGeometry.derivedStalk_transpose_comp_derivedStalkPushforward` at the transpose read
   off `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq`, with the signature
   permutation `g' := g`, `f' := i'`, `f := i`, `g := f`;
2. the transposed morphism split into its four factors;
3. `AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` for `g` at `w`;
4. the naturality of that stalk formula at the derived counit of `Li^* ⊣ Ri_*`;
5. `AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes` for `i`
   at `g w`, which replaces the derived counit by the counit of the germ adjunction;
6. `AlgebraicGeometry.derivedStalk_compIso_inv_comp_derivedPullbackStalkIso` for `g` and `i`;
7. `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_derivedStalk_compIso` for `i'` and `f`;
8. `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp` along the diagonal;
9. the naturality of the unit of the germ adjunction for `i'` at the stalk formula for `f`.

On the right it takes two, in `rhsChase`: the naturality of the stalk formula for `f` at the
comparison of `Ri_*` with the degreewise pushforward, and
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` for `f` at `i' w`.  `combine` joins
the two normalizations.

What is left is `LocalBaseChangeIdentityAt`: no derived base change map, no adjoint transpose, no
coherence of Tag 0D5S, no derived counit — only the unit and counit of the two germ adjunctions,
the two merges of extensions of scalars, the transport along the diagonal, the comparisons of
derived against degreewise extension of scalars, and `DerivedCategory.Q` of three degreewise
maps.  It is the shape that
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_eq_unit_comp_counit` is stated to
meet.

## Implementation notes

*What is and is not proved here.*  The nine rungs and the two, as chases at free objects of
arbitrary categories, are proved, and so are the geometric normalizations of rungs 2 to 8
(`Stacks.Cohomology.ClosedImmersionBaseChange.lhsKeyChaseGeom`) and of the right-hand side
(`Stacks.Cohomology.ClosedImmersionBaseChange.rhsChaseGeom`).  `LocalBaseChangeIdentityAt` is
stated, not proved: it is the one thing Stacks 0E23 still waits on.  Rung 1 and rung 9 are joined
to those two in the module `ClosedImmersionBaseChangeLocalReduction`, which is where
`DerivedStalkBaseChangeEqQAt` is reduced to `LocalBaseChangeIdentityAt`.

*The kernel wall, and how rung 2 and rung 8 are made to meet.*
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is a reducible `abbrev`, so a
defeq the elaborator discharges with its transparency heuristics is re-derived by the kernel by
unfolding, and `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` underneath it
is `derivedPullbackCompIso` at a dozen large arguments.  Three consequences:

* `(derivedPullbackCompIsoLeft …).hom.app N = … ≫ …` cannot be proved by `rfl`; it has to be
  descended one level at a time, which is what `derivedPullbackCompIsoLeft_eq_trans`,
  `derivedPullbackCompIsoLeft_hom_eq` and `derivedPullbackCompIsoLeft_hom_app` do, and in that
  form it costs seconds instead of exhausting the kernel.
* `congrArg (fun q => derivedPullback q) h` cannot be elaborated against a written-out expected
  type either; `derivedPullback_diagonal_eq` therefore supplies the equation once, so that every
  consumer presents the same term instead of a second proof.
* The two spellings `derivedPullback (i' ≫ f).toLRSHom.toShHom` and
  `derivedPullback (i'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom)` — the first is what
  `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp` is read at, the second what
  `derivedPullbackCompIsoLeft` produces — are interchangeable at the level of the *equation*
  (`derivedPullback_diagonal_eq_scheme`, seconds) and at the level of the two *objects*
  (`derivedPullback_diagonal_obj_eq`), but **not** under `CategoryTheory.eqToIso _ |>.hom.app N`,
  where the kernel runs out of fuel.  So neither rung carries the transport as a transport of
  functors: both carry it as `CategoryTheory.eqToHom` of a free equation of the two *objects*,
  rung 8 by its own statement and rung 2 by
  `derivedPullbackCompIsoLeft_hom_app_eqToHom`, and a consumer hands both the same
  `derivedPullback_diagonal_obj_eq`.  The two then meet on one and the same term and
  `lhsKeyChase` needs no hypothesis between them.  The `CategoryTheory.eqToIso`-to-
  `CategoryTheory.eqToHom` step itself has to be assembled by `Eq.trans` and `congrArg`: done by
  `rw`, the motive it builds exhausts the kernel even with no spelling to convert.

*What the geometric instances of the rungs are.*  Write `K` for `DerivedCategory.Q.obj P`, `N`
for `(derivedPushforward i.toLRSHom.toShHom).obj K` and `M` for
`(derivedPullback f.toLRSHom.toShHom).obj N`.  Then `lhsChase` is fed
`R := (ModuleCat.restrictScalars (i'.stalkMap w).hom).mapDerivedCategory`, and the eleven
hypotheses are: `h1`,
`AlgebraicGeometry.derivedStalk_transposeSplit_comp_derivedStalkPushforward` for `i'` at `w`, with
the transpose supplied by
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_split` and the further morphism by
`AlgebraicGeometry.pullbackComparisonOnComplex` for `g`; `h2`, `splitHead` of
`CategoryTheory.Functor.map_comp` for the derived stalk at `w`; `h3`,
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` for `g` at `w` read backwards; `h4`,
the naturality of `(AlgebraicGeometry.derivedPullbackStalkIso g w).hom` at the derived counit of
`Li^* ⊣ Ri_*`; `h5`, `map_comp₂_symm` along `cancelHead` of
`AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes` for `i` at
`g w`; `h6` and `h7`, the two coherences of the module `ClosedImmersionBaseChangeCounitChase`
at `(g, i)` and at `(i', f)`; `h8`, rung 8 at `sq.w` with
`derivedPullback_diagonal_obj_eq sq N`; `h9`, `CategoryTheory.Adjunction.unit_naturality` of
`AlgebraicGeometry.derivedStalkGermAdjunction` for `i'` at `w`, taken at the common leading
factor `(AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app N`.  `rhsChase` is fed the
naturality of that same leading factor at the comparison of `Ri_*` with the degreewise
pushforward, and `derivedPullbackStalkIso_comp_comparison` for `f` at `i' w` read backwards.
Each of those eleven, and each of the two, is checked by the kernel on its own in seconds.

*How the rungs are made to meet.*  The rungs spell the *implicit* objects of
`CategoryTheory.Functor.map` and of `CategoryStruct.comp` differently — rung 1 declares the
adjoint with source `(derivedPullback i'.toLRSHom.toShHom).obj M`, the component of
`derivedPullbackCompIsoLeft` that rung 2 splits has source
`(derivedPullback f.toLRSHom.toShHom ⋙ derivedPullback i'.toLRSHom.toShHom).obj N` — and those
conversions are all cheap: the bare equation of objects, even under
`(totalDerivedExtensionScalars _).functor.obj` and even as the type ascribed to a
`CategoryTheory.Functor.map`, is checked in under a second.  Two things make the joints free
rather than merely cheap, and both were found by bisecting with probe declarations that take the
rungs as hypotheses and conclude `True`:

* `AlgebraicGeometry.derivedStalk_transposeSplit_comp_derivedStalkPushforward` takes the factors
  the transpose splits into rather than their composite, so the consumer never writes a copy of
  the adjoint and `lhsKeyChaseGeom` abstracts over the one morphism whose spelling it does not
  own, instantiating it by unification;
* the transpose is read off
  `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_split` rather than off
  `derivedBaseChangeMap_eq`.  This is the one that mattered.  The kernel cannot convert
  `derivedBaseChangeMap_eq`'s `derivedPullbackCompIsoLeft` factor — as the module that owns the
  definition elaborated it — into the same text elaborated anywhere else: a declaration whose
  statement is that composite equated to *itself*, at abstract ringed spaces and an abstract
  complex, is free when proved by `rfl` and over the budget when proved by
  `(derivedBaseChangeMap_adjoint …).symm.trans (derivedBaseChangeMap_adjoint …)`, while the
  composite's other two factors convert in seconds.  The split form carries that factor already
  descended, and does convert.

`lhsChaseMid`, `lhsChaseEm` and `lhsChaseUnit` split the accumulation of the remaining
conversions into three declarations, each with its own heartbeats.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace StacksDraft.DerivedStalkAssemblyChase

variable {A B : Type*} [Category A] [Category B] {C D : Type*} [Category C] [Category D]

/-- A functor carried over a five-fold composite, with the first four bracketed. -/
theorem map_comp₅ (F : C ⥤ D) {x₀ x₁ x₂ x₃ x₄ x₅ : C} (a₁ : x₀ ⟶ x₁) (a₂ : x₁ ⟶ x₂)
    (b : x₂ ⟶ x₃) (c : x₃ ⟶ x₄) (e : x₄ ⟶ x₅) :
    F.map ((a₁ ≫ a₂ ≫ b ≫ c) ≫ e) =
      F.map a₁ ≫ F.map a₂ ≫ F.map b ≫ F.map c ≫ F.map e := by
  simp

/-- A functor carried over a composite, read backwards. -/
theorem map_comp₂_symm (F : C ⥤ D) {x₀ x₁ x₂ : C} (a : x₀ ⟶ x₁) (b : x₁ ⟶ x₂) {c : x₀ ⟶ x₂}
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp, h]

/-- A leading factor split in two, in front of a tail. -/
theorem splitHead {m x y z : C} {a : x ⟶ y} {a₁ : x ⟶ m} {a₂ : m ⟶ y} (ha : a = a₁ ≫ a₂)
    (b : y ⟶ z) : a ≫ b = a₁ ≫ a₂ ≫ b := by
  rw [ha, Category.assoc]

/-- Cancelling an inverse pair in front of a factorization. -/
theorem cancelHead {c₀ c₁ c₂ : C} (hm : c₀ ⟶ c₁) (iv : c₁ ⟶ c₀) (cf : c₁ ⟶ c₂) (t : c₀ ⟶ c₂)
    (hc : cf = iv ≫ t) (hi : hm ≫ iv = CategoryStruct.id c₀) : hm ≫ cf = t := by
  rw [hc, ← Category.assoc, hi, Category.id_comp]

/-- **The two normalizations, joined.**  The left-hand side of the open equality and the first
four factors of its right-hand side both factor through the stalk formula for `f` at `Ri_* K`;
the remaining equality `h` is between the two tails. -/
theorem combine {x y z₀ z₁ z₂ z₃ z₄ z₅ z₆ : A}
    (R1 : x ⟶ z₀) (R2 : z₀ ⟶ z₁) (R3a : z₁ ⟶ z₂) (R3b : z₂ ⟶ z₃)
    (R4 : z₃ ⟶ z₄) (R5 : z₄ ⟶ z₅) (R6 : z₅ ⟶ z₆)
    (α : x ⟶ y) (b₁ : y ⟶ z₆) (b₂ : y ⟶ z₃) (Lg : x ⟶ z₆)
    (hL : Lg = α ≫ b₁)
    (hR : R1 ≫ R2 ≫ R3a ≫ R3b = α ≫ b₂)
    (h : b₁ = b₂ ≫ R4 ≫ R5 ≫ R6) :
    Lg = (R1 ≫ R2 ≫ (R3a ≫ R3b) ≫ R4 ≫ R5) ≫ R6 := by
  rw [hL, h, ← Category.assoc α, ← hR]
  simp

/-- **The middle of the normalization of the left-hand side.**  The seven rungs that run from
the inverse of the stalk formula for `i'` to the comparison of derived against degreewise
extension of scalars along the germ map of `g`, with the derived base change map not mentioned.

`h2` splits the transposed map into its four factors; `h3` computes the tail against the stalk
formula for `g`; `h4` moves the derived counit of `Li^* ⊣ Ri_*` past that formula; `h5` replaces
it by the counit of the germ adjunction; `h6` merges the extensions of scalars for `g` and `i`;
`h7` merges those for `i'` and `f`; `h8` transports along the diagonal of the square. -/
theorem lhsKeyChase {t₀ s₀ s₁ s₂ s₃ s₄ s₅ q₀ r₀ r₁ r₂ r₃ r₄ v₀ u₀ : B}
    (D₀ : s₅ ⟶ q₀) (ι : t₀ ⟶ s₀) (SVPC : s₀ ⟶ s₅)
    (s1 : s₀ ⟶ s₁) (s2 : s₁ ⟶ s₂) (s3 : s₂ ⟶ s₃) (s4 : s₃ ⟶ s₄) (spc : s₄ ⟶ s₅)
    (pgh : s₄ ⟶ r₀) (Tgfac : r₀ ⟶ r₁) (Tgcmp : r₁ ⟶ q₀)
    (pgh' : s₃ ⟶ u₀) (Tgsε : u₀ ⟶ r₀) (Tgpsi : u₀ ⟶ r₂) (Tgcf : r₂ ⟶ r₀)
    (pghgi : s₂ ⟶ r₃) (dsExt2inv : r₃ ⟶ r₂)
    (Tα : t₀ ⟶ r₄) (dsExt1hom : r₄ ⟶ v₀) (psIsoIFinv : v₀ ⟶ s₁) (eqh : v₀ ⟶ r₃)
    (h2 : SVPC = s1 ≫ s2 ≫ s3 ≫ s4 ≫ spc)
    (h3 : spc ≫ D₀ = pgh ≫ Tgfac ≫ Tgcmp)
    (h4 : s4 ≫ pgh = pgh' ≫ Tgsε)
    (h5 : Tgpsi ≫ Tgcf = Tgsε)
    (h6 : s3 ≫ pgh' ≫ Tgpsi = pghgi ≫ dsExt2inv)
    (h7 : ι ≫ s1 = (Tα ≫ dsExt1hom) ≫ psIsoIFinv)
    (h8 : psIsoIFinv ≫ s2 ≫ pghgi = eqh) :
    ι ≫ SVPC ≫ D₀ =
      Tα ≫ dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp := by
  rw [h2]
  simp only [Category.assoc]
  slice_lhs 6 7 => rw [h3]
  slice_lhs 5 6 => rw [h4]
  slice_lhs 6 6 => rw [← h5]
  slice_lhs 4 6 => rw [h6]
  slice_lhs 1 2 => rw [h7]
  slice_lhs 3 5 => rw [h8]
  simp

/-- **The left-hand side of the open equality of Stacks 0E23, normalized.**  Read `BC` as the
derived stalk of the derived base change map, `PCm` as the derived stalk of `Ri'_*` of the
comparison to the degreewise pullback, `Φ` as the derived stalk of `Ri'_*` on the image, `D₀` as
the tail of the target chain and `Em` as the factorization of restriction of scalars.

`h1` moves the adjoint transpose out of the way, `key` is `lhsKeyChase`, and `h9` moves the unit
of the germ adjunction for `i'` past the stalk formula for `f`. -/
theorem lhsChase (R : B ⥤ A)
    {a₀ a₁ a₂ aT aE : A} {t₀ s₀ s₅ q₀ r₀ r₁ r₄ v₀ r₂ r₃ : B}
    (BC : a₀ ⟶ a₁) (PCm : a₁ ⟶ a₂) (Φ : a₂ ⟶ R.obj s₅) (D₀ : s₅ ⟶ q₀) (Em : R.obj q₀ ⟶ aE)
    (U : a₀ ⟶ R.obj t₀) (ι : t₀ ⟶ s₀) (SVPC : s₀ ⟶ s₅)
    (Tgfac : r₀ ⟶ r₁) (Tgcmp : r₁ ⟶ q₀) (Tgcf : r₂ ⟶ r₀) (dsExt2inv : r₃ ⟶ r₂)
    (α : a₀ ⟶ aT) (U' : aT ⟶ R.obj r₄) (Tα : t₀ ⟶ r₄)
    (dsExt1hom : r₄ ⟶ v₀) (eqh : v₀ ⟶ r₃)
    (h1 : BC ≫ PCm ≫ Φ = U ≫ R.map (ι ≫ SVPC))
    (key : ι ≫ SVPC ≫ D₀ =
      Tα ≫ dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp)
    (h9 : α ≫ U' = U ≫ R.map Tα) :
    BC ≫ (PCm ≫ Φ ≫ R.map D₀) ≫ Em =
      α ≫ U' ≫ R.map (dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp) ≫ Em := by
  calc BC ≫ (PCm ≫ Φ ≫ R.map D₀) ≫ Em
      = (BC ≫ PCm ≫ Φ) ≫ R.map D₀ ≫ Em := by simp
    _ = (U ≫ R.map (ι ≫ SVPC)) ≫ R.map D₀ ≫ Em := by rw [h1]
    _ = U ≫ R.map (ι ≫ SVPC ≫ D₀) ≫ Em := by simp
    _ = U ≫ R.map (Tα ≫ dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp) ≫ Em := by
        rw [key]
    _ = (U ≫ R.map Tα) ≫
          R.map (dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp) ≫ Em := by simp
    _ = α ≫ U' ≫ R.map (dsExt1hom ≫ eqh ≫ dsExt2inv ≫ Tgcf ≫ Tgfac ≫ Tgcmp) ≫ Em := by
        rw [← h9]
        simp

/-- **The right-hand side of the open equality of Stacks 0E23, normalized.**  Read `R1` as the
derived pullback along `f` and the derived stalk at `i' w` of the comparison of `Ri_*` with the
degreewise pushforward, `R2 ≫ R3a ≫ R3b` as the comparison tail that the stalk formula for `f`
is characterized against, and `R4 ≫ R5 ≫ R6` as `DerivedCategory.Q` of the three degreewise
maps. -/
theorem rhsChase {a₀ aT c₀ c₁ c₂ c₃ c₇ c₈ : A}
    (R1 : a₀ ⟶ c₀) (R2 : c₀ ⟶ c₁) (R3a : c₁ ⟶ c₂) (R3b : c₂ ⟶ c₃)
    (α : a₀ ⟶ aT) (αQ : c₀ ⟶ c₇) (Tfmap : aT ⟶ c₇) (TfXfac : c₇ ⟶ c₈) (Tfcmp : c₈ ⟶ c₃)
    (g1 : R1 ≫ αQ = α ≫ Tfmap)
    (g2 : R2 ≫ R3a ≫ R3b = αQ ≫ TfXfac ≫ Tfcmp) :
    R1 ≫ R2 ≫ R3a ≫ R3b = α ≫ Tfmap ≫ TfXfac ≫ Tfcmp := by
  rw [g2, ← Category.assoc, g1]
  simp

/-- **The left-hand side of the open equality, normalized through the unit — the middle step.**
The first five rungs of `lhsChase`, with the factorization of restriction of scalars not yet
composed on: `h1` moves the adjoint transpose out of the way and `key` is `lhsKeyChase`.

Split off from `lhsChase` so that the kernel checks the conversions of this step against those of
`lhsChaseEm` and `lhsChaseUnit` in three separate declarations; see the implementation note on the
kernel wall. -/
theorem lhsChaseMid (R : B ⥤ A) {a₀ a₁ a₂ : A} {t₀ s₀ s₅ q₀ r₄ : B}
    (BC : a₀ ⟶ a₁) (PCm : a₁ ⟶ a₂) (Φ : a₂ ⟶ R.obj s₅) (D₀ : s₅ ⟶ q₀)
    (U : a₀ ⟶ R.obj t₀) (ι : t₀ ⟶ s₀) (SVPC : s₀ ⟶ s₅) (Tα : t₀ ⟶ r₄) (tail : r₄ ⟶ q₀)
    (h1 : BC ≫ PCm ≫ Φ = U ≫ R.map (ι ≫ SVPC))
    (key : ι ≫ SVPC ≫ D₀ = Tα ≫ tail) :
    BC ≫ PCm ≫ Φ ≫ R.map D₀ = U ≫ R.map Tα ≫ R.map tail := by
  rw [← Functor.map_comp, ← key]
  simp [reassoc_of% h1]

/-- **`lhsChaseMid` with the factorization of restriction of scalars composed on.**  Nothing but
associativity; it is a separate step because the conversion between the two spellings of the
target complex — the composite functor against the two functors applied in turn — is what the
kernel pays for here, and it is paid for nowhere else. -/
theorem lhsChaseEm (R : B ⥤ A) {a₀ a₁ a₂ aE : A} {t₀ s₅ q₀ r₄ : B}
    (BC : a₀ ⟶ a₁) (PCm : a₁ ⟶ a₂) (Φ : a₂ ⟶ R.obj s₅) (D₀ : s₅ ⟶ q₀) (Em : R.obj q₀ ⟶ aE)
    (U : a₀ ⟶ R.obj t₀) (Tα : t₀ ⟶ r₄) (tail : r₄ ⟶ q₀)
    (h : BC ≫ PCm ≫ Φ ≫ R.map D₀ = U ≫ R.map Tα ≫ R.map tail) :
    BC ≫ (PCm ≫ Φ ≫ R.map D₀) ≫ Em = (U ≫ R.map Tα) ≫ R.map tail ≫ Em := by
  simpa using h =≫ Em

/-- **The last rung of `lhsChase`.**  The unit of the germ adjunction for `i'` moved past the
stalk formula for `f`, which is rung 9. -/
theorem lhsChaseUnit (R : B ⥤ A) {a₀ aT aE : A} {t₀ q₀ r₄ : B}
    (Em : R.obj q₀ ⟶ aE) (U : a₀ ⟶ R.obj t₀) (Tα : t₀ ⟶ r₄) (tail : r₄ ⟶ q₀)
    (α : a₀ ⟶ aT) (U' : aT ⟶ R.obj r₄) (L : a₀ ⟶ aE)
    (hA : L = (U ≫ R.map Tα) ≫ R.map tail ≫ Em)
    (h9 : α ≫ U' = U ≫ R.map Tα) :
    L = α ≫ U' ≫ R.map tail ≫ Em := by
  rw [hA, ← h9]
  simp

end StacksDraft.DerivedStalkAssemblyChase

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

attribute [local instance] isLeftDerived_alphaG isLeftDerived_alphaH

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition in
/-- `derivedPullback_diagonal_eq` for the square, spelled with the composite scheme morphisms —
the spelling `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp` produces.  Using
one and the same term on both sides of the chase is what keeps the kernel from re-deriving
`(i' ≫ f).toLRSHom.toShHom = i'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom` under the reducible
`derivedPullback` at every unification. -/
theorem derivedPullback_diagonal_eq_scheme (sq : IsPullback i' g f i) :
    derivedPullback (i' ≫ f).toLRSHom.toShHom =
      derivedPullback (g ≫ i).toLRSHom.toShHom :=
  derivedPullback_diagonal_eq g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
    f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)

open Stacks.Cohomology.DerivedBaseChange in
/-- `derivedPullback_diagonal_eq` read at an object of `D(𝒪_X)`.  This is the comparison the
kernel can afford; see `StacksDraft.DerivedBaseChangeSplit.eqToIso_hom_app_eq`. -/
theorem derivedPullback_diagonal_obj_eq (sq : IsPullback i' g f i)
    (N : DerivedCategory X.Modules) :
    (derivedPullback (i'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom)).obj N =
      (derivedPullback (g.toLRSHom.toShHom ≫ i.toLRSHom.toShHom)).obj N :=
  congrArg (fun F : DerivedCategory X.Modules ⥤ DerivedCategory Z'.Modules => F.obj N)
    (derivedPullback_diagonal_eq g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq))

open Stacks.Cohomology.DerivedBaseChange in
/-- **The one local identity that Stacks 0E23 now waits on.**  Every ingredient of the open
equality that mentions the geometry of the square away from the point `w` has been eliminated:
the derived base change map of Stacks 08HY, its adjoint transpose, the two coherences of Tag
0D5S, the transport along the diagonal of the square and the derived counit of `Li^* ⊣ Ri_*` are
all gone.  What is left speaks only of the four local rings.

On the left: the unit of the germ adjunction for `i'` at `w`, then restriction of scalars along
the germ map of `i'` of — the merge of the extensions of scalars for `i'` and `f`, the transport
of the point and the ring, the merge for `g` and `i` read backwards, the counit of the germ
adjunction for `i` at `g w`, and the two factorizations that bring the derived stalk at `g w`
down to `DerivedCategory.Q` of the stalk complex — and finally the factorization of restriction
of scalars.

On the right: the derived stalk at `f (i' w)` of the comparison of `Ri_*` with the degreewise
pushforward, extended along the germ map of `f`, then the comparison of derived against
degreewise extension of scalars, and then `DerivedCategory.Q` of three degreewise maps: the
transport of the point, the bridge of
`StacksDraft.DerivedRingIso.extendScalarsRestrictIso`, and the underived comparison of Stacks
065Z.

This is the shape that
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_eq_unit_comp_counit` — and its
uniform-universe corollary in `RingTheory.TorIndependence`,
`derivedBaseChangeComparison_fst_app_eq_unit_comp_counit_extendScalarsComp` — is stated to
meet: the underived comparison of Stacks 065Z is a unit, a merge and a counit, which is exactly
what the left-hand side here is, read degreewise at each `P.X n`. -/
abbrev LocalBaseChangeIdentityAt (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (P : CochainComplex Z.Modules ℤ) : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  (AlgebraicGeometry.derivedStalkGermAdjunction i' w).unit.app
        ((AlgebraicGeometry.derivedStalkFunctor (f (i' w)) ⋙
            (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
      (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
              ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
            eqToHom (congrArg (fun ψ : Z' ⟶ X =>
                (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
                  ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
                    ((derivedPushforward i.toLRSHom.toShHom).obj
                      (DerivedCategory.Q.obj P)))) sq.w) ≫
              (AlgebraicGeometry.derivedStalkExtensionCompIso g i w).inv.app
                  ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
                    ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
                (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                    ((totalDerivedExtensionScalars.{u, u, u} (i.stalkMap (g w)).hom).functor.map
                        ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                          i (g w)).hom.app (DerivedCategory.Q.obj P)) ≫
                      (AlgebraicGeometry.derivedStalkGermAdjunction i (g w)).counit.app
                        ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj
                          (DerivedCategory.Q.obj P))) ≫
                  (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison.app
                      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
    ((AlgebraicGeometry.derivedStalkFunctor (f (i' w)) ⋙
            (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
              (f (i' w))).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
              (f (i' w))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))) ≫
      DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} (f.stalkMap (i' w)).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex (modulesStalkFunctorCongr (ptEq sq w).symm)
                  (ComplexShape.up ℤ)).inv.app
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P) ≫
              ((ModuleCat.restrictScalars.{u, u, u}
                (X.presheaf.stalkCongr
                  (Inseparable.of_eq (ptEq sq w).symm)).hom.hom).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                ((NatTrans.mapHomologicalComplex
                  (Stacks.ModuleSkyscraper.pushStalkMap i (g w))
                    (ComplexShape.up ℤ)).app P))) ≫
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
                (StacksDraft.DerivedRingIso.extendScalarsRestrictIso
                  (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w))).hom.hom
                  (X.presheaf.stalkCongr (Inseparable.of_eq (ptEq sq w).symm)).hom.hom
                  (stalkCongr_symm_hom_hom_apply (ptEq sq w))
                  (stalkCongr_hom_symm_hom_apply (ptEq sq w))
                  (f.stalkMap (i' w)).hom).hom (ComplexShape.up ℤ)).app
              (((ModuleCat.restrictScalars.{u, u, u}
                  (i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                  (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
                (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom
                  (ringRR' w (ptEq sq w)) (g.stalkMap w).hom (i'.stalkMap w).hom
                  (stalkMap_ringHom_square sq w (ptEq sq w))
                  (Lg w (ptEq sq w)) (Lh w) (alphaG w (ptEq sq w)) (alphaH w)).1
                  (ComplexShape.up ℤ)).app
              (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g w)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
  StacksDraft.DerivedStalkAssemblyChase in
/-- **The middle of the normalization of the left-hand side, at the geometry of the square.**
`StacksDraft.DerivedStalkAssemblyChase.lhsKeyChase` at the seven rungs of the implementation
notes: `h2` splits the transposed map into its four factors, `h3` is the stalk formula for `g` at
`w` read backwards, `h4` carries it past the derived counit of `Li^* ⊣ Ri_*`, `h5` replaces that
counit by the counit of the germ adjunction for `i`, `h6` and `h7` are the two coherences of Tag
0D5S, and `h8` transports along the diagonal of the square.

The adjoint of the base change map is written with its source ascribed to
`(derivedPullback i'.toLRSHom.toShHom).obj M`, the spelling rung 1 declares it at. -/
theorem lhsKeyChaseGeom (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (P : CochainComplex Z.Modules ℤ)
    {V : (AlgebraicGeometry.derivedStalkFunctor w).obj
          ((derivedPullback i'.toLRSHom.toShHom).obj
            ((derivedPullback f.toLRSHom.toShHom).obj
              ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))) ⟶
        (AlgebraicGeometry.derivedStalkFunctor w).obj
          (DerivedCategory.Q.obj (((Scheme.Modules.pullback g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))}
    (h2 : V =
      (AlgebraicGeometry.derivedStalkFunctor w).map
          ((derivedPullbackCompIsoCanonical i'.toLRSHom.toShHom f.toLRSHom.toShHom).hom.app
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
        (AlgebraicGeometry.derivedStalkFunctor w).map
            (eqToHom (derivedPullback_diagonal_obj_eq sq
              ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))) ≫
          (AlgebraicGeometry.derivedStalkFunctor w).map
              ((derivedPullbackCompIsoCanonical g.toLRSHom.toShHom i.toLRSHom.toShHom).inv.app
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
            (AlgebraicGeometry.derivedStalkFunctor w).map
                ((derivedPullback g.toLRSHom.toShHom).map
                  ((derivedAdjunction i.toLRSHom.toShHom).counit.app
                    (DerivedCategory.Q.obj P))) ≫
              (AlgebraicGeometry.derivedStalkFunctor w).map
                (AlgebraicGeometry.pullbackComparisonOnComplex g P)) :
    (AlgebraicGeometry.derivedPullbackStalkIso i' w).inv.app
          ((derivedPullback f.toLRSHom.toShHom).obj
            ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
        V ≫ (Stacks.ModuleSkyscraper.modulesStalkFunctor Z'
                w).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback g).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso g w).symm
              (ComplexShape.up ℤ)).hom.app P) =
      (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor.map
              ((AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
                  (AlgebraicGeometry.derivedStalkExtensionCompIso i' f w).hom.app
              ((AlgebraicGeometry.derivedStalkFunctor (f (i' w))).obj
                ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
            eqToHom (congrArg (fun ψ : Z' ⟶ X =>
                (totalDerivedExtensionScalars.{u, u, u} (ψ.stalkMap w).hom).functor.obj
                  ((AlgebraicGeometry.derivedStalkFunctor (ψ w)).obj
                    ((derivedPushforward i.toLRSHom.toShHom).obj
                      (DerivedCategory.Q.obj P)))) sq.w) ≫
              (AlgebraicGeometry.derivedStalkExtensionCompIso g i w).inv.app
                  ((AlgebraicGeometry.derivedStalkFunctor (i (g w))).obj
                    ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))) ≫
                (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                    ((totalDerivedExtensionScalars.{u, u, u} (i.stalkMap (g w)).hom).functor.map
                        ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
                          i (g w)).hom.app (DerivedCategory.Q.obj P)) ≫
                      (AlgebraicGeometry.derivedStalkGermAdjunction i (g w)).counit.app
                        ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj
                          (DerivedCategory.Q.obj P))) ≫
                  (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor.map
                      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapDerivedCategoryFactors.hom.app P) ≫
                    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison.app
                      (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                        (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have h3 := (AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison g w P).symm
  have h4 := (AlgebraicGeometry.derivedPullbackStalkIso g w).hom.naturality
    ((derivedAdjunction i.toLRSHom.toShHom).counit.app (DerivedCategory.Q.obj P))
  have h5 := map_comp₂_symm
    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor _ _
    (cancelHead _ _ _ _
      (AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes
        i (g w) (DerivedCategory.Q.obj P))
      ((AlgebraicGeometry.derivedPullbackStalkIso i (g w)).hom_inv_id_app
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))))
  have h6 := AlgebraicGeometry.derivedStalk_compIso_inv_comp_derivedPullbackStalkIso g i w
    ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))
  have h7 := AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_derivedStalk_compIso i' f w
    ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))
  have h8 := AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp sq.w w
    ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))
    (derivedPullback_diagonal_obj_eq sq
      ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)))
  exact lhsKeyChase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 h3 h4 h5 h6 h7 h8

open Stacks.Cohomology.DerivedBaseChange StacksDraft.DerivedStalkAssemblyChase in
/-- **The right-hand side of the open equality of Stacks 0E23, normalized.**
`StacksDraft.DerivedStalkAssemblyChase.rhsChase` at the naturality of the stalk formula for `f` at
`i' w` along the comparison of `Ri_*` with the degreewise pushforward, and at that stalk formula's
characterizing equation read backwards.  The leading morphism is the one `lhsChaseGeom`
produces. -/
theorem rhsChaseGeom (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (P : CochainComplex Z.Modules ℤ) :
        (derivedPullback f.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (AlgebraicGeometry.pullbackComparisonOnComplex f
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
                (i' w)).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                  (Stacks.ModuleSkyscraper.pullbackStalkIso f (i' w)).symm
                  (ComplexShape.up ℤ)).hom.app
                (((Scheme.Modules.pushforward i).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) =
    (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app
        ((derivedPushforward i.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
          ((AlgebraicGeometry.derivedStalkFunctor (f (i' w)) ⋙
            (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
                i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
            (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
              (f (i' w))).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
              (f (i' w))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((Scheme.Modules.pushforward i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))) := by
  have g1 := (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.naturality
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
          i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P) ≫
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app P)
  have g2 := (AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison f (i' w)
    (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm
  exact rhsChase _ _ _ _ _ _ _ _ _ g1 g2

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
