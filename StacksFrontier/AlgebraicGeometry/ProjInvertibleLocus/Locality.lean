module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.DualBasis
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.InvertibleSheaves
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Trivialization
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sets.OpenCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local triviality implies invertibility

Tag 01MU's goodness condition asks that the `d`-divisible twists on an open of `Proj S` be
invertible, and the trivializations of
`StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Trivialization.lean` are local: one on each
standard open `D₊(pq)`. Invertibility is defined, following Tag 01CS, as "the tensor functor is
an equivalence", a property with no visible locality, so passing from those trivializations to
invertibility of a module on a union is a separate local-to-global step.

The route is **not** descent of the inverse object: it is the dual sheaf of Tag 0FNV. Given
trivializations on a family covering the terminal object,
`Stacks.InvertibleLocallyFree.dualBasisOneOfIso` turns each into a rank-one dual basis and
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne` inverts the evaluation pairing
`L^∨ ⊗ L ⟶ 𝒪` after sheafification. The inverse is the globally constructed `L^∨`, so no object
is glued.

## Main results

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_of_coversTop_iso_unit`: on any
  site, a sheaf of modules trivialized on a family covering the terminal object is invertible.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_of_coversTop_nonempty_iso_unit`:
  the same with the trivializations given only up to `Nonempty`, which is the form local data
  usually takes.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_of_iSup_eq_top`: the version on the
  site of opens of a topological space, with the covering hypothesis as `⨆ i, U i = ⊤`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_of_onSpace`: invertibility in the
  sense of Tag 02AD implies invertibility in the sense of Tag 01CS.
  `AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible` is *defined* as local triviality, and
  this compares it with the tensor-equivalence predicate.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.overIsoUnitOfLE` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_pullback_of_iSup_eq`: the same for an
  arbitrary open `W` of a scheme, trivialized on a family of opens with supremum `W`. This is
  `isInvertible_pullback_of_iso_unit` generalized from one trivializing open to a covering family
  of them, and `overIsoUnitOfLE` is the change of site it needs.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_pullback_twistingSheaf_ratioLocus`:
  the invertibility clause of Tag 01MU's condition (1) for the locus `W_d` itself, with no
  hypothesis. This strengthens `isInvertible_pullback_twistingSheaf_basicOpen_mul` from one
  standard open `D₊(pq)` to their whole union.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isGoodOpen_ratioLocus_of_isIso_mul` and
  `ratioLocus_le_whereInvertible_of_isIso_mul_ratioLocus` in the same namespace:
  Tag 01MU's inclusion `⋃ D₊(fg) ⊆ W_d`, reduced to the multiplication clause on the single open
  `W_d`. These strengthen `isGoodOpen_basicOpen_mul_of_isIso_mul` and
  `ratioLocus_le_whereInvertible_of_isIso_mul`, whose hypotheses are that condition on every
  standard open separately.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top`:
  the `d`-divisible twists are invertible on all of `Proj 𝒮` when Tag 01MU's locus `W_d` is
  everything.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_adjoin_degree_one`:
  every `𝒪(n)` is invertible on `Proj 𝒮` when `𝒮` is generated in degree one.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioCover` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.coversTop_ratioCover_iff`: Tag 01MU's second
  open subset as a family of opens, and the fact that it covers exactly when `W_d = Proj 𝒮`.

## Implementation notes

**Scope.** These lemmas give closure of invertibility under *assembling explicit local
trivializations*. They do **not** give closure of invertibility under suprema of opens on which
the module is merely known to be invertible: that needs the converse direction, local
triviality from `AlgebraicGeometry.SheafOfModules.IsInvertible`, which is clause 2 of Tag 0B8M.

**Universes.** The module universe is `max u v` for a site `C : Type u` with `Category.{v} C`.
This is inherited from `Stacks.InvertibleLocallyFree.dualBasisOneOfIso`, which is stated there
because a section of the internal hom of Tag 03EM over `U` is a morphism of presheaves of
modules on `C/U`. On the site of opens of a space the hom universe is `0`, so the constraint is
vacuous, which is why `isInvertible_of_iSup_eq_top` has an unconstrained statement.

**Why the propositional form of the trivializations has its own lemma.** `Classical.choice` on
them has to happen before `dualBasisOneOfIso` is applied, because that definition takes the
isomorphism as a `def`-level argument. A caller holding a constructed isomorphism wants the
data form, a caller who produced the trivializations pointwise has only the propositional one.
Assuming only the propositional form is a *weaker* hypothesis, so that lemma is the stronger of
the two.

**Which `IsInvertible`.** The conclusions are spelled `_root_.AlgebraicGeometry.SheafOfModules`
`.IsInvertible` and not `SheafOfModules.IsInvertible`. There are two classes of that name with
identical bodies, and inside the `Stacks.*` namespace the unqualified spelling resolves to
`Stacks.SheafOfModules.IsInvertible`, the one that Tag 01MU's `IsGoodOpen` is *not* stated
over. Writing it unqualified here produces a statement which compiles, and which is about the
other class, so it cannot discharge `IsGoodOpen`.

**Non-vacuity.** `IsGoodOpen` is satisfied by `⊥`, so a statement about it is worth only as much
as its witnesses. The hypothesis of `isInvertible_twistingSheaf_of_adjoin_degree_one` is
discharged for a polynomial ring, and hence for projective space, by
`AlgebraicGeometry.ProjectiveSpace.adjoin_range_X_homogeneousSubmodule_zero` together with
`MvPolynomial.gradedAlgebra`. `isInvertible_pullback_twistingSheaf_ratioLocus` has no hypothesis
at all, and its open `W_d` is `⊥` only when no product `fg` with `deg f = deg g + d` is outside
every relevant prime.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02AD](https://stacks.math.columbia.edu/tag/02AD)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe v u

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

variable (𝒪 h𝒪)

/-- A sheaf of modules trivialized on a covering family is invertible. No descent of the
inverse object occurs: the inverse is the dual sheaf `L^∨`, built globally, and the only
local-to-global step is that the evaluation pairing, being locally bijective, is inverted by
sheafification. -/
theorem isInvertible_of_coversTop_iso_unit
    {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (φ : ∀ i, L.over (Y i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (Y
        i))) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  (Stacks.InvertibleLocallyFree.stacksIsInvertible_iff_isInvertible 𝒪 h𝒪 L).mp
    (Stacks.SheafOfModules.isInvertible_of_dualBasisOne 𝒪 h𝒪 hY fun i =>
      Stacks.InvertibleLocallyFree.dualBasisOneOfIso 𝒪 h𝒪 (φ i))

/-- `isInvertible_of_coversTop_iso_unit` with the trivializations given up to `Nonempty`, which
is the form in which local data is usually produced. -/
theorem isInvertible_of_coversTop_nonempty_iso_unit
    {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (φ : ∀ i, Nonempty (L.over (Y i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (Y
        i)))) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  isInvertible_of_coversTop_iso_unit 𝒪 h𝒪 hY fun i => (φ i).some

end Site

section Space

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}}
  {h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable (𝒪 h𝒪)

/-- A sheaf of modules on a space, trivialized on a family of opens that covers, is
invertible: `isInvertible_of_coversTop_nonempty_iso_unit` with the covering hypothesis in its
elementary form. -/
theorem isInvertible_of_iSup_eq_top
    {L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    {I : Type*} {U : I → Opens X} (hU : (⨆ i, U i) = ⊤)
    (φ : ∀ i, Nonempty (L.over (U i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over (U
        i)))) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  isInvertible_of_coversTop_nonempty_iso_unit 𝒪 h𝒪 ((Opens.coversTop_iff _ U).mpr hU) φ

/-- Invertibility in the sense of Tag 02AD implies invertibility in the sense of Tag 01CS:
`AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible` is *defined* as local triviality, and
`AlgebraicGeometry.SheafOfModules.IsInvertible` is the tensor-equivalence form.

The converse is clause 2 of Tag 0B8M; see the implementation notes. -/
theorem isInvertible_of_onSpace
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [h : _root_.AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L] :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L := by
  choose U hmem hiso using h.locally_iso
  refine isInvertible_of_iSup_eq_top 𝒪 h𝒪 (U := U) (eq_top_iff.mpr fun x _ => ?_) hiso
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

end Space

section Scheme

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}} {W : X.Opens} {M : X.Modules}

/-- A trivialization of `M` on the restricted site of `V ≤ W`, transported to a trivialization
of the restriction of `M` to the open subscheme `W` on the restricted site of the corresponding
open `W.ι ⁻¹ᵁ V` of `W.toScheme`.

This is the change of site that a local-to-global argument on a *proper* open `W` needs and
that `isInvertible_pullback_of_iso_unit` does not perform: the trivializations of Tag 01MU are
produced on the site of opens of the ambient scheme, while invertibility on `W` is a statement
about the site of opens of `W.toScheme`. Both restriction composition lemmas go through
`Scheme.Opens.isoOfLE`, which identifies `(W.ι ⁻¹ᵁ V).toScheme` with `V.toScheme`. -/
noncomputable def overIsoUnitOfLE {V : X.Opens} (hVW : V ≤ W) (M : X.Modules)
    (e : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    ((Scheme.Modules.pullback W.ι).obj M).over (W.ι ⁻¹ᵁ V) ≅
      SheafOfModules.unit (W.toScheme.ringCatSheaf.over (W.ι ⁻¹ᵁ V)) :=
  have hι : (W.ι ⁻¹ᵁ V).ι ≫ W.ι = (Scheme.Opens.isoOfLE hVW).hom ≫ V.ι :=
    (Scheme.Opens.isoOfLE_hom_ι hVW).symm
  (Scheme.Modules.overEquiv (W.ι ⁻¹ᵁ V)).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (W.ι ⁻¹ᵁ V)).app _ ≪≫
      ((restrictFunctor (W.ι ⁻¹ᵁ V).ι).mapIso
          ((restrictFunctorIsoPullback W.ι).app M).symm ≪≫
        ((restrictFunctorComp (W.ι ⁻¹ᵁ V).ι W.ι).app M).symm ≪≫
        (restrictFunctorCongr hι).app M ≪≫
        (restrictFunctorComp (Scheme.Opens.isoOfLE hVW).hom V.ι).app M ≪≫
        (restrictFunctor (Scheme.Opens.isoOfLE hVW).hom).mapIso
          (restrictIsoUnitOfOverIsoUnit V M e) ≪≫
        restrictUnitIso (Scheme.Opens.isoOfLE hVW).hom) ≪≫
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit (W.ι ⁻¹ᵁ V)
        W.toScheme.ringCatSheaf).symm)

/-- A module trivialized on a family of opens whose supremum is `W` has invertible
restriction to `W`.

This is the local-to-global step of Tag 01MU's condition (1) for an arbitrary open, and it is
the generalization of `isInvertible_pullback_of_iso_unit` from a single trivializing open to a
covering family of them. The invertibility predicate and its spelling are exactly those of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.IsGoodOpen`'s first clause. -/
theorem isInvertible_pullback_of_iSup_eq
    {I : Type*} {V : I → X.Opens} (hV : (⨆ i, V i) = W)
    (φ : ∀ i, M.over (V i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (V i))) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible W.toScheme.presheaf
      W.toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback W.ι).obj M) := by
  have hle : ∀ i, V i ≤ W := fun i => hV ▸ le_iSup V i
  refine isInvertible_of_iSup_eq_top W.toScheme.presheaf W.toScheme.ringCatSheaf.2
    (U := fun i => (W.ι ⁻¹ᵁ V i : W.toScheme.Opens)) (eq_top_iff.mpr fun x _ => ?_)
    fun i => ⟨overIsoUnitOfLE (hle i) M (φ i)⟩
  have hx : (x.1 : X) ∈ (⨆ i, V i) := hV ▸ x.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

end Scheme

section Proj

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The standard opens `D₊(fg)` with `deg f = deg g + d`, indexed by the triples that define
them. This is Tag 01MU's second open subset, presented as a family rather than as a supremum. -/
def ratioCover (d : ℕ) : (Σ e : ℕ, 𝒮 (e + d) × 𝒮 e) → Opens (ProjectiveSpectrum.top 𝒮) :=
  fun i => ProjectiveSpectrum.basicOpen 𝒮 ((i.2.1 : S) * (i.2.2 : S))

/-- The family `ratioCover` has `ProjShared.ratioLocus` for its supremum: Tag 01MU's second
open subset, with the three nested suprema of its definition flattened into one. -/
theorem iSup_ratioCover (d : ℕ) :
    (⨆ i, ratioCover 𝒮 d i) = ProjShared.ratioLocus 𝒮 d := by
  rw [ProjShared.ratioLocus, iSup_sigma]
  exact iSup_congr fun _ => iSup_prod

/-- Tag 01MU's standard opens cover `Proj 𝒮` exactly when `W_d` is everything. -/
theorem coversTop_ratioCover_iff (d : ℕ) :
    (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)).CoversTop (ratioCover 𝒮 d) ↔
      ProjShared.ratioLocus 𝒮 d = ⊤ := by
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, iSup_ratioCover]
  exact Iff.rfl

/-- The `d`-divisible twists are invertible on the whole of Tag 01MU's locus `W_d`.

This is the invertibility clause of Tag 01MU's condition (1) for the open `W_d` itself, in
exactly the spelling `IsGoodOpen` asks for, and it has no hypothesis. It strengthens
`isInvertible_pullback_twistingSheaf_basicOpen_mul` from a single standard open `D₊(pq)` to
their whole union: the trivializations `(p/q)^n` are assembled by
`isInvertible_pullback_of_iSup_eq`, whose local-to-global step is the dual sheaf and not
descent. No hypothesis on `d` is needed, and no homogeneous element of degree `d` need exist. -/
theorem isInvertible_pullback_twistingSheaf_ratioLocus (d : ℕ) (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
      (ProjShared.ratioLocus 𝒮 d).toScheme.presheaf
      (ProjShared.ratioLocus 𝒮 d).toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (ProjShared.ratioLocus 𝒮 d).ι).obj
        (twistingSheaf 𝒮 ((d : ℤ) * n))) :=
  isInvertible_pullback_of_iSup_eq (V := ratioCover 𝒮 d) (iSup_ratioCover 𝒮 d)
    fun i => ratioOverIsoUnit 𝒮 i.2.1.2 i.2.2.2 (mul_comm (n : ℤ) (d : ℤ))

/-- The `d`-divisible twists are invertible on all of `Proj 𝒮` as soon as Tag 01MU's locus
`W_d` is everything.

This is the local-to-global half of Tag 01MU's condition (1), in the one case where it needs no
change of site: the trivializations `ratioOverIsoUnit` of the standard opens `D₊(fg)` live on
the site of opens of `Proj 𝒮` already, and when those opens cover, `W_d = Proj 𝒮` and
`isInvertible_of_coversTop_iso_unit` assembles them. Note that no homogeneous element of degree
`d` need exist: the trivializing sections are *ratios* `(p/q)^n` with `deg p = deg q + d`, which
is the whole point of Tag 01MU.

This is only the invertibility clause of `IsGoodOpen`. Its multiplication clause, that
`𝒪(dn) ⊗ 𝒪(dm) → 𝒪(dn + dm)` is an isomorphism, is independent of this argument. -/
@[ega "II 2.5.8" "Case U_d = Proj S", ega "II 3.2.5" "Second assertion"]
theorem isInvertible_twistingSheaf_of_ratioLocus_eq_top {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.2 (twistingSheaf 𝒮 ((d : ℤ) * n)) :=
  isInvertible_of_coversTop_iso_unit _ _ ((coversTop_ratioCover_iff 𝒮 d).mpr hd)
    fun i => ratioOverIsoUnit 𝒮 i.2.1.2 i.2.2.2 (mul_comm (n : ℤ) (d : ℤ))

/-- Every twist `𝒪(n)` is invertible on `Proj 𝒮` when `𝒮` is generated in degree one.

This is the classical case of Tag 01MU: a graded ring generated over `𝒮 0` by `𝒮 1` has
`W_d = Proj 𝒮` for every `d` (`ProjShared.ratioLocus_eq_top_of_adjoin_degree_one`), so taking
`d = 1` makes every `𝒪(n)` invertible. -/
@[ega "II 8.6.4" "partial"]
theorem isInvertible_twistingSheaf_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒮 0) (Set.range fun f : 𝒮 1 => (f : S)) = ⊤) (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.2 (twistingSheaf 𝒮 n) := by
  have h := isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒮
    (ProjShared.ratioLocus_eq_top_of_adjoin_degree_one 𝒮 hgen 1) n
  rwa [Nat.cast_one, one_mul] at h

/-! ### Tag 01MU's first inclusion, reduced to one hypothesis on one open -/

/-- Tag 01MU's locus `W_d` is a good open as soon as the multiplication maps are isomorphisms
on it. Its invertibility clause is `isInvertible_pullback_twistingSheaf_ratioLocus`, which has
no hypothesis.

This strengthens `isGoodOpen_basicOpen_mul_of_isIso_mul`, whose hypothesis is the same condition
on *every* standard open `D₊(pq)` separately. -/
theorem isGoodOpen_ratioLocus_of_isIso_mul (d : ℕ)
    (hmul : ∀ n m : ℤ, IsIso ((twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m)).over
      (ProjShared.ratioLocus 𝒮 d))) :
    IsGoodOpen 𝒮 d (ProjShared.ratioLocus 𝒮 d) :=
  ⟨isInvertible_pullback_twistingSheaf_ratioLocus 𝒮 d,
    fun n m => isIso_restrictFunctor_map_of_isIso_over _ _ (hmul n m)⟩

/-- Tag 01MU's inclusion `⋃ D₊(fg) ⊆ W_d`, reduced to one hypothesis on one open.

This strengthens `ratioLocus_le_whereInvertible_of_isIso_mul`: that lemma assumes the
multiplication maps become isomorphisms on every standard open `D₊(fg)` separately, whereas the
invertibility half holds on the union itself, so the hypothesis is needed only there. -/
theorem ratioLocus_le_whereInvertible_of_isIso_mul_ratioLocus (d : ℕ)
    (hmul : ∀ n m : ℤ, IsIso ((twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m)).over
      (ProjShared.ratioLocus 𝒮 d))) :
    ProjShared.ratioLocus 𝒮 d ≤ whereInvertible 𝒮 d :=
  le_whereInvertible_of_isGoodOpen 𝒮 (isGoodOpen_ratioLocus_of_isIso_mul 𝒮 d hmul)

end Proj

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

end
