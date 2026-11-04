module

public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Locality
public import StacksFrontier.AlgebraicGeometry.SubalgebraTrimLocalization.Basic

/-!
# The affine cut-down to finite type, for the sections of a quasi-coherent algebra sheaf

Let `X` be a scheme, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras, `U ⊆ X` an affine
open, and `f i : Γ(X, U)` finitely many sections whose basic opens `D(f i) ⊆ U` are the opens over
which `A` is already known to be of finite type. Then **one finite subset `G` of `A(U)` generates a
`Γ(X, U)`-subalgebra that has not shrunk over any `D(f i)`**: every section of `A` over `D(f i)` is
a fraction `t / (f i)^n` with numerator `t` in `Algebra.adjoin Γ(X, U) G`.

This is the geometric half of the "affine cut-down to finite type" that
`StacksFrontier/AlgebraicGeometry/SubalgebraSectionsResidue/Basic.lean` records as one of the
absent pieces of the symmetric-algebra-free route to the colimit assertion of [Stacks, Tag 05JT]
and to [Stacks, Tag 0817]. It is a **composition of two proved results and introduces no new
mathematics**:

* the ring-level trim `Stacks.SubalgebraTrimLocalization.exists_finset_hasNumeratorIn_family`
  (`SubalgebraTrimLocalization/Basic.lean`), which asks that each `A(D(f i))` be a localization
  of `A(U)` away from the image of `f i` and of finite type over `Γ(X, U)`; and
* `Stacks.FPAlgebraSheaf.isLocalization_away_sections` (`FPAlgebraSheaf/Locality.lean`), which
  supplies exactly that localization statement for a quasi-coherent algebra sheaf.

The hypothesis is read over the *localized* base `Γ(X, D(f i))`, which is the form a geometric
caller holds — finite type of `A` over `D(f i)` is finite type of `A(D(f i))` over
`Γ(X, D(f i))`, not over `Γ(X, U)` — and
`Stacks.SubalgebraTrimLocalization.exists_finset_hasNumeratorIn_family_of_localizedBase` performs
the conversion.

## Main results

* `exists_finset_hasNumeratorIn_sections`: the statement above, in the
  `Stacks.SubalgebraTrimLocalization.HasNumeratorIn` vocabulary.
* `exists_finset_restrict_eq_restrict_mul_pow`: the same conclusion written out with the sheaf's
  own restriction maps and no `Algebra` instance in the statement except the one
  `Algebra.adjoin Γ(X, U)` needs. This is the form in which a caller holds it, and it differs from
  the previous one by the naturality square
  `Stacks.RelativeSpec.AlgebraSheaf.presheaf_map_comp_app`: `HasNumeratorIn` uses the denominator
  `algebraMap Γ(X, U) (A(D(f i))) (f i)`, i.e. `f i` restricted in `𝒪_X` and *then* pushed into
  `A`, while a caller has the image of `f i` in `A(U)` restricted to `D(f i)`.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** Neither assertion of
[Stacks, Tag 05JT] nor any assertion of [Stacks, Tag 0817] is proved here, and nothing here is a
statement of either: both labels of Tag 05JT are registered on
`StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraFiltered/Basic.lean`, and what
`StacksFrontier/AlgebraicGeometry/SubalgebraSectionsResidue/Basic.lean` records as the residue of the
symmetric-algebra-free route is a finite type quasi-coherent algebra sheaf on the whole of `X`
mapping to `A` and hitting a given section over an affine open. What is below is one input
to that, and it carries hypotheses the tags do not grant (an affine open, a chosen finite family of
sections, and finite type over each of their basic opens).

Specifically, this file does **not** construct a subalgebra *sheaf*: its output is a finite subset
of `A(U)` together with the statement that the subalgebra it generates is undiminished over each
`D(f i)`. Turning that into a quasi-coherent subalgebra of `A` on `X` needs the extension across an
open immersion (`AlgebraOpenExtension/Basic.lean`, whose two inputs are
proved in `OpenImmersionAlgebraBridges/`) and the gluing of quasi-coherent subalgebras along a
two-member open cover, which is not in this library.

## Implementation notes

The instances the conclusion needs are introduced with `letI` in the statement, in the same style
as `Stacks.FPAlgebraSheaf.isLocalization_away_sections` and
`Stacks.RelativeSpec.AlgebraSheaf.isPushout_sections`, and the ones indexed by `i` are introduced
as functions of `i`, which the local instance set uses as `Pi`-type instances.

`Stacks.FPAlgebraSheaf.isLocalization_away_sections` states its denominator as
`(A.hom.hom.app (op U)).hom (f i)` while the ring-level trim asks for
`algebraMap Γ(X, U) (A(U)) (f i)`; these are the same term, because
`Stacks.RelativeSpec.AlgebraSheaf.algebraSections` is that ring map's `RingHom.toAlgebra`, so the
`letI` is accepted with no bridging. The analogous pair for the *denominator inside the
localization* is **not** definitional — see `exists_finset_restrict_eq_restrict_mul_pow`, where the
naturality square has to be applied.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.SubalgebraTrimLocalization
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u w

namespace Stacks.AlgebraicGeometry.SubalgebraTrimAffine

variable {X : Scheme.{u}}

/-- **The affine cut-down to finite type, for the sections of a quasi-coherent algebra sheaf.**
Let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras, `U` an affine open of `X`, and
`f : ι → Γ(X, U)` a finite family of sections such that the sections of `A` over each basic open
`D(f i)` are of finite type over `Γ(X, D(f i))`. Then a single finite subset `G` of `A(U)`
generates a `Γ(X, U)`-subalgebra of `A(U)` which has not shrunk over any `D(f i)`: every section of
`A` over `D(f i)` is a fraction with numerator in `Algebra.adjoin Γ(X, U) G` and denominator a
power of `f i`.

Nothing is assumed about `X` beyond `U` being affine, and the family need not cover anything. -/
theorem exists_finset_hasNumeratorIn_sections (A : AlgebraSheaf X) [A.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type w} [Finite ι] (f : ι → Γ(X, U))
    (hft : ∀ i, RingHom.FiniteType (A.hom.hom.app (op (X.basicOpen (f i)))).hom) :
    letI := AlgebraSheaf.algebraSections A U
    letI := fun i : ι => AlgebraSheaf.algebraRestrict A (X.basicOpen_le (f i))
    letI := fun i : ι => AlgebraSheaf.algebraSectionsOfLE A (X.basicOpen_le (f i))
    ∃ G : Finset (AlgebraSheaf.sections A U),
      ∀ (i : ι) (x : AlgebraSheaf.sections A (X.basicOpen (f i))),
        HasNumeratorIn (Algebra.adjoin Γ(X, U) (G : Set (AlgebraSheaf.sections A U))) (f i) x := by
  let _ := AlgebraSheaf.algebraSections A U
  let _ : ∀ i : ι, Algebra (AlgebraSheaf.sections A U)
      (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => AlgebraSheaf.algebraRestrict A (X.basicOpen_le (f i))
  let _ : ∀ i : ι, Algebra Γ(X, U) (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => AlgebraSheaf.algebraSectionsOfLE A (X.basicOpen_le (f i))
  let _ : ∀ i : ι, Algebra Γ(X, U) Γ(X, X.basicOpen (f i)) :=
    fun i => algebraOfLE X (X.basicOpen_le (f i))
  let _ : ∀ i : ι, Algebra Γ(X, X.basicOpen (f i))
      (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => AlgebraSheaf.algebraSections A (X.basicOpen (f i))
  let _ : ∀ i : ι, IsScalarTower Γ(X, U) (AlgebraSheaf.sections A U)
      (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => AlgebraSheaf.isScalarTower_restrict A (X.basicOpen_le (f i))
  let _ : ∀ i : ι, IsScalarTower Γ(X, U) Γ(X, X.basicOpen (f i))
      (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => AlgebraSheaf.isScalarTower_sections A (X.basicOpen_le (f i))
  let _ : ∀ i : ι, IsLocalization.Away (f i) Γ(X, X.basicOpen (f i)) :=
    fun i => hU.isLocalization_basicOpen (f i)
  let _ : ∀ i : ι, IsLocalization.Away
      (algebraMap Γ(X, U) (AlgebraSheaf.sections A U) (f i))
      (AlgebraSheaf.sections A (X.basicOpen (f i))) :=
    fun i => Stacks.FPAlgebraSheaf.isLocalization_away_sections A hU (f i)
  exact exists_finset_hasNumeratorIn_family_of_localizedBase f
    (fun i => Γ(X, X.basicOpen (f i)))
    (fun i => AlgebraSheaf.sections A (X.basicOpen (f i))) hft

/-- **The same conclusion with the sheaf's own restriction maps.** The denominator is the image of
`f i` in `A(U)` restricted to `D(f i)`, which is how a geometric caller holds it; `HasNumeratorIn`
uses instead the image of the restriction of `f i` in `𝒪_X`, and the two agree by the naturality of
the structure morphism of `A`
(`Stacks.RelativeSpec.AlgebraSheaf.presheaf_map_comp_app`). -/
theorem exists_finset_restrict_eq_restrict_mul_pow (A : AlgebraSheaf X) [A.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type w} [Finite ι] (f : ι → Γ(X, U))
    (hft : ∀ i, RingHom.FiniteType (A.hom.hom.app (op (X.basicOpen (f i)))).hom) :
    letI := AlgebraSheaf.algebraSections A U
    ∃ G : Finset (AlgebraSheaf.sections A U),
      ∀ (i : ι) (x : AlgebraSheaf.sections A (X.basicOpen (f i))),
        ∃ (t : AlgebraSheaf.sections A U) (n : ℕ),
          t ∈ Algebra.adjoin Γ(X, U) (G : Set (AlgebraSheaf.sections A U)) ∧
            x * (A.right.obj.map (homOfLE (X.basicOpen_le (f i))).op).hom
                  ((A.hom.hom.app (op U)).hom (f i)) ^ n =
              (A.right.obj.map (homOfLE (X.basicOpen_le (f i))).op).hom t := by
  let _ := AlgebraSheaf.algebraSections A U
  obtain ⟨G, hG⟩ := exists_finset_hasNumeratorIn_sections A hU f hft
  refine ⟨G, fun i x => ?_⟩
  obtain ⟨t, n, htG, ht⟩ := hG i x
  refine ⟨t, n, htG, ?_⟩
  -- `HasNumeratorIn`'s denominator is `𝒪`-restrict-then-push; the goal's is push-then-restrict.
  have hnat : (A.right.obj.map (homOfLE (X.basicOpen_le (f i))).op).hom
      ((A.hom.hom.app (op U)).hom (f i)) =
      (A.hom.hom.app (op (X.basicOpen (f i)))).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le (f i))).op).hom (f i)) :=
    (congr($(AlgebraSheaf.presheaf_map_comp_app A (X.basicOpen_le (f i))).hom (f i))).symm
  rwa [hnat]

end Stacks.AlgebraicGeometry.SubalgebraTrimAffine

end
