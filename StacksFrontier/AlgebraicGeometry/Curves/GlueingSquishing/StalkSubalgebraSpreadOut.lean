module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.LowerProperSubalgebra
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.MinimalStep
public import StacksFrontier.AlgebraicGeometry.SubalgebraGlueCover.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Spreading an arbitrary stalk subalgebra out, and the minimality of [Stacks, Tag 0C1L]

The splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` has two branches. The branch that
*splits* needs a finite quasi-coherent subalgebra `𝒪_X ⊊ 𝒜 ⊊ f_*𝒪_{X'}`; the branch that does
*not* split must produce an elementary modification, and the only producers of one from the
geometry — `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`
and `Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal` — demand stalk
*minimality*

`hmin : ∀ E : Subalgebra 𝒪_{X,x} (f_*𝒪_{X'})_x, E = ⊥ ∨ E = ⊤`.

**This file closes the gap between the two.** `hmin` is now *derived* from the failure of the
splitting branch: `Stacks.GlueSquishFactor.forall_eq_bot_or_eq_top_of_forall_isFinite_subalg`
says that if no finite quasi-coherent subalgebra of `f_*𝒪_{X'}` is proper at both ends over an
affine open `U ∋ x`, then the stalk extension has no subalgebra strictly in between. So the
dichotomy of `hsplit` can be taken on the *sheaf* and still hand `hmin` to the one-step
classification.

## Why the subalgebra `𝒪_X + ℐ_x · f_*𝒪_{X'}` is not enough, and what replaces it

`Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` spreads the one stalk subalgebra
`𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` out, as `𝒪_X + ℐ_x · f_*𝒪_{X'}`. That subalgebra is proper at the
upper end always (Nakayama) but strictly above `𝒪_X` only in the branch
`m_x·(f_*𝒪_{X'})_x ⊄ 𝒪_{X,x}` of
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra`; in the other branch
it degenerates to `𝒪_X`, and minimality of the stalk extension does **not** follow — with
`𝒪_{X,x} = k` and `(f_*𝒪_{X'})_x = k³` the dichotomy lands in that branch, yet `{(a, a, b)}` is a
proper intermediate subalgebra and the fibre `k³` is neither `k × k` nor `k[ε]`, so a splitting
is genuinely required there and no ideal-times-algebra construction can produce one.

What produces it is not an ideal-times-algebra construction at all:
`Stacks.RelativeSpec.AlgebraSheaf.germPreimage`, the sections of `A` whose **germ at `x` lies in
`E`**, for an arbitrary subalgebra `E` of the stalk. Properness at both ends is then immediate
from `⊥ < E < ⊤`, and the content moves to quasi-coherence and finiteness.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.stalk`, `...germ` and `...stalkAlgebra`: **the stalk API
  `Stacks.RelativeSpec.AlgebraSheaf.Subalg` did not have** — the stalk of an algebra sheaf, the
  germ of a section, and the algebra structure of the stalk over the stalk of `𝒪_X`, together
  with the two compatibilities `germ_res` and `germ_app` that any germ computation needs.
* `Stacks.RelativeSpec.AlgebraSheaf.germPreimage`: **the concrete subalgebra cut out by a
  subalgebra `E` of one stalk.**

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_germPreimage`: **it is quasi-coherent**, as
  soon as `E` absorbs `m_x · A_x`. See below for why that hypothesis is both needed and free.
* `Stacks.RelativeSpec.AlgebraSheaf.isFinite_subalg`: **every** concrete subalgebra of a finite
  algebra sheaf on a locally Noetherian scheme is finite. This is cheaper than the route of
  `Stacks.GlueSquishFactor.isFinite_genSubalg` through
  `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFinite_of_isFiniteType`: no finite type
  hypothesis on the subalgebra and no coherence of the ambient algebra sheaf, because
  Noetherianity of `Γ(X, U)` makes any submodule of the finite module `Γ(A, U)` finite.
* `Stacks.GlueSquishFactor.exists_germ_eq_mul_unit`: every element of `(f_*𝒪_{X'})_x` is the
  germ of a section over an affine `U ∋ x` divided by a unit of `𝒪_{X,x}`. Both ends of
  properness turn on this, and it is the only place the localisation
  `AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk` is used.
* `Stacks.GlueSquishFactor.ne_top_obj_germPreimage` and
  `Stacks.GlueSquishFactor.exists_mem_obj_germPreimage_notMem_range`: **properness at both
  ends**, from `E ≠ ⊤` and `E ≠ ⊥` respectively.
* `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top_of_subalgebra_lt`: **the
  spreading-out.** From a subalgebra `𝒪_{X,x} ⊊ E ⊊ (f_*𝒪_{X'})_x` of the stalk, a finite
  quasi-coherent subalgebra of `f_*𝒪_{X'}` proper at both ends over `U`.
* `Stacks.GlueSquishFactor.forall_eq_bot_or_eq_top_of_forall_isFinite_subalg`: **`hmin`**, as
  above.
* `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg`: the glueing half
  of the one-step classification with `hmin` discharged — the check that the derived minimality
  is the one the geometric producers ask for, and the statement in which the two hypotheses that
  remain, `hne` and `hiso`, are visible.

## Why quasi-coherence needs `m_x · A_x ⊆ E`, and why that costs nothing

Quasi-coherence is checked by
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`:
over the basic opens `X.basicOpen a` of an affine open `U` the sections must localize. For
`x ∈ X.basicOpen a` this is free — the numerator of a section of the subalgebra has germ
`a_x ^ n` times the germ of that section, and `E` is a subalgebra containing the image of
`𝒪_{X,x}`. For `x ∈ U` **outside** `X.basicOpen a` the subalgebra is all of `A` over
`X.basicOpen a` while it is a proper subring over `U`, and the numerator has to be corrected:
multiplying a section over `U` by `a`, whose germ at `x` lies in `m_x`, carries it into the
subalgebra precisely when `E` absorbs `m_x · A_x`.

That is not a restriction on the consumer. The branch of
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra` in which
`m_x·(f_*𝒪_{X'})_x` lies in the image of `𝒪_{X,x}` makes *every* subalgebra absorb it; and in the
other branch `𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` is a subalgebra which absorbs it and which
`Stacks.GlueSquishFactor.addMapMaximalIdeal_ne_top` and
`Stacks.GlueSquishFactor.bot_lt_addMapMaximalIdeal` show to be proper at both ends. So
`exists_isFinite_subalg_ne_top_of_subalgebra_lt` spreads out `E` in the first case and
`𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` in the second, and needs no hypothesis on `E` beyond
`⊥ < E < ⊤`.

## What is still missing for [Stacks, Tag 0C1L], and no stacks attribute

**No `@[stacks]` attribute is attached.** `hmin` is one of three inputs `hsplit` needs, and
the other two are not provided here.

* *The measure of each half of a splitting.* The measure
  `Stacks.GlueSquishFactor.measureOver` and both of its strict drops are proved
  (`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSum`), and the point of the
  support that the drops ask for is produced from the two properness clauses above by
  `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both`. What is not proved is
  the identification of the two halves' measures with those drops:
  `Stacks.GlueSquishFactor.sumSheafMultiplicity_eq_of_iso` against
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` for the lower half, and `q_*` of the
  upper quotient against `f_*𝒪_{X'}/𝒜` through
  `Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero` composed
  with `Stacks.GlueSquishFactor.sum_sheafMultiplicity_le_sheafMultiplicity_pushforward` for the
  upper half.
* *One bad point.* The glueing half of the one-step classification,
  `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`,
  also asks for `hiso`, an isomorphism over the complement of the *single* point `x`, which
  `Stacks.GlueSquishFactor.IsAlmostIso` does not give: it gives an isomorphism away from some
  finite set. That is the source's "we may assume that `f` is not an isomorphism in exactly one
  point", and it is a statement about the whole bad set. Note that the subalgebra built here
  does not settle it either, but it narrows what would: with two bad points `x ≠ y` the
  subalgebra `𝒪_X + ℐ_y·f_*𝒪_{X'}` of
  `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra` is proper at the
  upper end at `y` and, by `Stacks.GlueSquishFactor.obj_idealSmulSubalg_eq_top`, agrees with
  `f_*𝒪_{X'}` near `x`, hence is proper at the lower end there — so a splitting exists whenever
  the bad set has more than one point. That argument is not formalized here.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1I](https://stacks.math.columbia.edu/tag/0C1I)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01OU](https://stacks.math.columbia.edu/tag/01OU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-! ### The stalk of an algebra sheaf -/

/-- The stalk at `x` of the sheaf of rings underlying an algebra sheaf. -/
noncomputable abbrev stalk (A : AlgebraSheaf X) (x : X) : CommRingCat.{u} :=
  TopCat.Presheaf.stalk (X := X.toPresheafedSpace.carrier) A.right.obj x

/-- The germ at `x` of a section of an algebra sheaf over an open containing `x`. -/
noncomputable abbrev germ (A : AlgebraSheaf X) (U : X.Opens) (x : X) (hx : x ∈ U) :
    sections A U ⟶ stalk A x :=
  TopCat.Presheaf.germ (X := X.toPresheafedSpace.carrier) A.right.obj U x hx

/-- The stalk of an algebra sheaf is an algebra over the stalk of the structure sheaf. -/
@[instance_reducible]
noncomputable def stalkAlgebra (A : AlgebraSheaf X) (x : X) :
    Algebra (X.presheaf.stalk x) (stalk A x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map A.hom.hom).hom.toAlgebra

/-- The germ of a restricted section is the germ of the section. -/
theorem germ_res (A : AlgebraSheaf X) {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V)
    (s : sections A U) :
    (germ A V x hx).hom ((A.right.obj.map (homOfLE h).op).hom s) = (germ A U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

/-- The germ of the image of a section of the structure sheaf is the image of its germ. -/
theorem germ_app (A : AlgebraSheaf X) {U : X.Opens} {x : X} (hx : x ∈ U) (r : Γ(X, U)) :
    letI := stalkAlgebra A x
    (germ A U x hx).hom ((A.hom.hom.app (op U)).hom r) =
      algebraMap (X.presheaf.stalk x) (stalk A x) (X.presheaf.germ U x hx r) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx A.hom.hom r).symm

/-! ### Sections of the underlying module, read as sections of the algebra sheaf

The sections of `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule A` over an open and the
sections of `A` there are the same type, but not the same *expression*: the first is an
`AddCommGrp`, the second a `CommRingCat`. `mval` and `mofval` name the two readings, and the
lemmas below compute the module operations in the ring of sections. -/

/-- A section of the underlying module of an algebra sheaf, read as a section of the algebra
sheaf. -/
def mval (A : AlgebraSheaf X) {U : X.Opens} (z : Γ(underlyingModule A, U)) : sections A U := z

/-- A section of an algebra sheaf, read as a section of its underlying module. -/
def mofval (A : AlgebraSheaf X) {U : X.Opens} (s : sections A U) : Γ(underlyingModule A, U) := s

/-- Reading a section of an algebra sheaf as a module section and back recovers it. -/
@[simp] theorem mval_mofval (A : AlgebraSheaf X) {U : X.Opens} (s : sections A U) :
    mval A (mofval A s) = s := rfl

/-- The zero section of the underlying module reads as the zero section of the algebra sheaf. -/
@[simp] theorem mval_zero (A : AlgebraSheaf X) {U : X.Opens} :
    mval A (0 : Γ(underlyingModule A, U)) = 0 := rfl

/-- Sections of the underlying module are determined by their reading in the sections. -/
theorem mval_inj (A : AlgebraSheaf X) {U : X.Opens} {z₁ z₂ : Γ(underlyingModule A, U)}
    (h : mval A z₁ = mval A z₂) : z₁ = z₂ := h

/-- The restriction map of the underlying module of an algebra sheaf, read in the sections. -/
theorem mval_restrictₗ (A : AlgebraSheaf X) {U V : X.Opens} (h : V ≤ U)
    (z : Γ(underlyingModule A, U)) :
    letI := moduleOfLE (underlyingModule A) h
    mval A (restrictₗ (underlyingModule A) h z) =
      (A.right.obj.map (homOfLE h).op).hom (mval A z) := rfl

/-- The scalar action on the sections of the underlying module of an algebra sheaf, read in the
sections. -/
theorem mval_smul (A : AlgebraSheaf X) {U : X.Opens} (r : Γ(X, U))
    (z : Γ(underlyingModule A, U)) :
    mval A (r • z) = (A.hom.hom.app (op U)).hom r * mval A z := rfl

/-- `mval_smul` for the scalars restricted from a larger open. -/
theorem mval_smul_ofLE (A : AlgebraSheaf X) {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (z : Γ(underlyingModule A, V)) :
    letI := moduleOfLE (underlyingModule A) h
    mval A (r • z) =
      (A.hom.hom.app (op V)).hom (X.presheaf.map (homOfLE h).op r) * mval A z := rfl

/-- The restriction map of the underlying module of a concrete subalgebra, on underlying
sections. -/
theorem val_restrictₗ_subalg {A : AlgebraSheaf X} (C : Subalg A) {U V : X.Opens} (h : V ≤ U)
    (z : Γ(underlyingModule (Subalg.toAlgebraSheaf C), U)) :
    letI := moduleOfLE (underlyingModule (Subalg.toAlgebraSheaf C)) h
    (restrictₗ (underlyingModule (Subalg.toAlgebraSheaf C)) h z).1 =
      (A.right.obj.map (homOfLE h).op).hom z.1 := rfl

/-- The scalar action on the sections of the underlying module of a concrete subalgebra, on
underlying sections. -/
theorem val_smul_subalg {A : AlgebraSheaf X} (C : Subalg A) {U : X.Opens} (r : Γ(X, U))
    (z : Γ(underlyingModule (Subalg.toAlgebraSheaf C), U)) :
    ((r • z : Γ(underlyingModule (Subalg.toAlgebraSheaf C), U))).1 =
      (A.hom.hom.app (op U)).hom r * z.1 := rfl

/-- `val_smul_subalg` for the scalars restricted from a larger open. -/
theorem val_smul_subalg_ofLE {A : AlgebraSheaf X} (C : Subalg A) {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) (z : Γ(underlyingModule (Subalg.toAlgebraSheaf C), V)) :
    letI := moduleOfLE (underlyingModule (Subalg.toAlgebraSheaf C)) h
    ((r • z : Γ(underlyingModule (Subalg.toAlgebraSheaf C), V))).1 =
      (A.hom.hom.app (op V)).hom (X.presheaf.map (homOfLE h).op r) * z.1 := rfl

/-! ### The subalgebra cut out by a subalgebra of one stalk -/

variable (A : AlgebraSheaf X) (x : X)

/-- The sections over `U` whose germ at `x` lies in `E`, as a subring: over an open missing `x`
there is no condition. -/
def germPreimageSubring (E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x))
    (U : X.Opens) : Subring (sections A U) where
  carrier := {s | ∀ hx : x ∈ U, (germ A U x hx).hom s ∈ E}
  one_mem' hx := by rw [map_one]; exact one_mem E
  mul_mem' ha hb hx := by rw [map_mul]; exact mul_mem (ha hx) (hb hx)
  zero_mem' hx := by rw [map_zero]; exact zero_mem E
  add_mem' ha hb hx := by rw [map_add]; exact add_mem (ha hx) (hb hx)
  neg_mem' ha hx := by rw [map_neg]; exact neg_mem (ha hx)

/-- **The subalgebra of an algebra sheaf cut out by a subalgebra `E` of one stalk**: its
sections over `U` are the sections of `A` whose germ at `x` lies in `E`, with no condition over
the opens missing `x`.

This is a concrete subalgebra because `E` is a subalgebra: it contains the germs of the
structure sheaf, it is stable under restriction because the germ of a restricted section is the
germ of the section, and membership is local because the germ is computed on any neighbourhood
of `x`. -/
def germPreimage (E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x)) :
    Subalg A where
  obj U := germPreimageSubring A x E U
  algebraMap_mem U a hx := by
    let := stalkAlgebra A x
    rw [germ_app A hx a]
    exact E.algebraMap_mem _
  map_mem {U V} h {s} hs hx := by rw [germ_res A h hx s]; exact hs (h hx)
  isSheaf {U} s hs hx := by
    obtain ⟨V, hVU, hxV, hmem⟩ := hs x hx
    rw [← germ_res A hVU hxV s]
    exact hmem hxV

variable {A x}

/-- Membership in the subalgebra cut out by a stalk subalgebra. -/
theorem mem_germPreimage_iff
    {E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x)} {U : X.Opens}
    (s : sections A U) :
    s ∈ (germPreimage A x E).obj U ↔ ∀ hx : x ∈ U, (germ A U x hx).hom s ∈ E := Iff.rfl

/-- The germ at `x` of a section of the subalgebra cut out by `E` lies in `E`. -/
theorem germ_mem_of_mem_germPreimage
    {E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x)} {U : X.Opens}
    (hx : x ∈ U) {s : sections A U} (hs : s ∈ (germPreimage A x E).obj U) :
    (germ A U x hx).hom s ∈ E := hs hx

/-- A section whose germ at `x` lies in `E` is a section of the subalgebra cut out by `E`. -/
theorem mem_germPreimage_of_germ_mem
    {E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x)} {U : X.Opens}
    (hx : x ∈ U) {s : sections A U} (hs : (germ A U x hx).hom s ∈ E) :
    s ∈ (germPreimage A x E).obj U := fun _ => hs

/-! ### Quasi-coherence -/

/-- **The sections of the subalgebra cut out by a stalk subalgebra localize.** Over the basic
opens of an affine open they are the localization of the sections over that open, which is the
criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`
asks for.

The hypothesis `hmE` — that `E` absorbs `m_x · A_x` — is what makes the statement true over a
basic open **missing** `x`: there the subalgebra is all of `A`, and a section over `U` is
carried into it by multiplying by `a`, whose germ at `x` then lies in `m_x`. Over a basic open
*containing* `x` no hypothesis is needed: the numerator of a section of the subalgebra has germ
`a_x ^ n` times the germ of that section, which `E` contains already. -/
theorem isLocalizedModule_germPreimage (A : AlgebraSheaf X) [A.IsQuasicoherent] (x : X)
    (E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x))
    (hmE : letI := stalkAlgebra A x
      ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), ∀ b : stalk A x,
        algebraMap (X.presheaf.stalk x) (stalk A x) r * b ∈ E)
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE (underlyingModule (Subalg.toAlgebraSheaf (germPreimage A x E)))
      (X.basicOpen_le a)
    IsLocalizedModule.Away a
      (restrictₗ (underlyingModule (Subalg.toAlgebraSheaf (germPreimage A x E)))
        (X.basicOpen_le a)) := by
  let := stalkAlgebra A x
  set C := germPreimage A x E with hC
  set M := underlyingModule (Subalg.toAlgebraSheaf C) with hM
  set F := underlyingModule A with hF
  set hle : X.basicOpen a ≤ U := X.basicOpen_le a with hhle
  let := moduleOfLE M hle
  let := moduleOfLE F hle
  have hFloc : IsLocalizedModule.Away a (restrictₗ F hle) :=
    isLocalizedModule_restrictₗ F hU a rfl hle
  have hunit : IsUnit (X.presheaf.map (homOfLE hle).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · refine (Module.End.isUnit_iff _).mpr ⟨fun z₁ z₂ h ↦ ?_, fun z ↦ ?_⟩
    · simp only [Module.algebraMap_end_apply] at h
      exact hunit.smul_left_cancel.mp h
    · obtain ⟨v, hv⟩ := hunit.exists_left_inv
      refine ⟨v • z, ?_⟩
      rw [Module.algebraMap_end_apply]
      show (X.presheaf.map (homOfLE hle).op a) • v • z = z
      rw [smul_smul, mul_comm, hv, one_smul]
  · intro z
    obtain ⟨n, s, hs⟩ := IsLocalizedModule.Away.surj (restrictₗ F hle) a (mofval A z.1)
    -- the numerator over `U`, multiplied by `a`
    have hsval : (A.right.obj.map (homOfLE hle).op).hom (mval A s) =
        (A.hom.hom.app (op (X.basicOpen a))).hom
            (X.presheaf.map (homOfLE hle).op (a ^ n)) * z.1 := by
      have h1 := congrArg (mval A) hs.symm
      rw [mval_restrictₗ A hle s, mval_smul_ofLE A hle (a ^ n) (mofval A z.1),
        mval_mofval] at h1
      exact h1
    refine ⟨n + 1, ⟨(A.hom.hom.app (op U)).hom a * mval A s, ?_⟩, ?_⟩
    · -- the germ of the numerator lies in `E`
      intro hxU
      rw [map_mul, germ_app A hxU a]
      by_cases hxa : x ∈ X.basicOpen a
      · -- over a basic open containing `x` the germ of `s` is already in `E`
        have hgs : (germ A U x hxU).hom (mval A s) =
            algebraMap (X.presheaf.stalk x) (stalk A x)
              (X.presheaf.germ U x hxU (a ^ n)) * (germ A (X.basicOpen a) x hxa).hom z.1 := by
          rw [← germ_res A hle hxa (mval A s), hsval, map_mul,
            germ_app A hxa (X.presheaf.map (homOfLE hle).op (a ^ n)),
            TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) x hxa (a ^ n)]
        rw [hgs]
        exact mul_mem (E.algebraMap_mem _)
          (mul_mem (E.algebraMap_mem _) (germ_mem_of_mem_germPreimage hxa z.2))
      · -- over a basic open missing `x` the germ of `a` lies in the maximal ideal
        exact hmE _ ((IsLocalRing.mem_maximalIdeal _).mpr
          fun hu => hxa ((Scheme.mem_basicOpen X a x hxU).mpr hu)) _
    · refine Subtype.ext ?_
      show (A.hom.hom.app (op (X.basicOpen a))).hom
            (X.presheaf.map (homOfLE hle).op (a ^ (n + 1))) * z.1 =
          (A.right.obj.map (homOfLE hle).op).hom
            ((A.hom.hom.app (op U)).hom a * mval A s)
      have hmul : ∀ p q : Γ(X, X.basicOpen a),
          (A.hom.hom.app (op (X.basicOpen a))).hom (p * q) =
            (A.hom.hom.app (op (X.basicOpen a))).hom p *
              (A.hom.hom.app (op (X.basicOpen a))).hom q := fun p q => map_mul _ p q
      rw [map_mul, res_app hle a, hsval, pow_succ', map_mul, hmul, mul_assoc]
  · intro z hz
    have h1 : (A.right.obj.map (homOfLE hle).op).hom z.1 = 0 := by
      have h0 := congrArg Subtype.val hz
      rw [val_restrictₗ_subalg C hle z] at h0
      exact h0
    have hz' : restrictₗ F hle (mofval A z.1) = restrictₗ F hle (0 : Γ(F, U)) :=
      mval_inj A (by
        rw [mval_restrictₗ A hle, mval_restrictₗ A hle, mval_mofval, mval_zero, map_zero, h1])
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := restrictₗ F hle) a hz'
    refine ⟨n, Subtype.ext ?_⟩
    have h2 := congrArg (mval A) hn
    rw [mval_smul A (a ^ n) (mofval A z.1), mval_smul A (a ^ n) (0 : Γ(F, U)), mval_mofval,
      mval_zero, mul_zero] at h2
    rw [val_smul_subalg C (a ^ n) z]
    exact h2

/-- **The subalgebra cut out by a stalk subalgebra is quasi-coherent**, as soon as `E` absorbs
`m_x · A_x`. -/
theorem isQuasicoherent_germPreimage (A : AlgebraSheaf X) [A.IsQuasicoherent] (x : X)
    (E : letI := stalkAlgebra A x; Subalgebra (X.presheaf.stalk x) (stalk A x))
    (hmE : letI := stalkAlgebra A x
      ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), ∀ b : stalk A x,
        algebraMap (X.presheaf.stalk x) (stalk A x) r * b ∈ E) :
    (Subalg.toAlgebraSheaf (germPreimage A x E)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ _
    fun _ hU a => isLocalizedModule_germPreimage A x E hmE hU a

/-! ### Finiteness -/

/-- **A concrete subalgebra of a finite algebra sheaf on a locally Noetherian scheme is
finite.** Over an affine open the sections of `A` are a finite module over the Noetherian ring
`Γ(X, U)`, hence a Noetherian module, and the sections of the subalgebra are a submodule of it.

This is the finiteness `Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` asks of
the intermediate subalgebra, and unlike the route through
`Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFinite_of_isFiniteType` it needs no finite type
hypothesis on the subalgebra and no coherence of `A`: Noetherianity of the base does that work.
-/
theorem isFinite_subalg [IsLocallyNoetherian X] {A : AlgebraSheaf X} (C : Subalg A)
    (hA : A.IsFinite) : (Subalg.toAlgebraSheaf C).IsFinite := by
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := algebraSections A U
  have : Module.Finite Γ(X, U) (sections A U) := hA U hU
  have : IsNoetherian Γ(X, U) (sections A U) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let := algebraSections (Subalg.toAlgebraSheaf C) U
  show Module.Finite Γ(X, U) (sections (Subalg.toAlgebraSheaf C) U)
  exact Module.Finite.of_injective
    ({ toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      sections (Subalg.toAlgebraSheaf C) U →ₗ[Γ(X, U)] sections A U) Subtype.val_injective

end Stacks.RelativeSpec.AlgebraSheaf

namespace Stacks.GlueSquishFactor

open Stacks.RelativeSpec.AlgebraSheaf

/-! ### Every element of the stalk is a germ over an affine open, divided by a unit -/

/-- **Every element of `(f_*𝒪_{X'})_x` is the germ of a section over an affine open `U ∋ x`
divided by a unit of `𝒪_{X,x}`.** The stalk is the localization of `Γ(X', f⁻¹U)` at the image of
the prime cut out by `x` (`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`), and
the denominators come from `Γ(X, U)`, so their germs do not lie in `m_x`.

This is the step both ends of the properness of a spread-out subalgebra turn on, isolated: the
upper end needs it to see that the germs of the sections over `U` generate the whole stalk over
`𝒪_{X,x}`, and the lower end needs it to realise a prescribed stalk element as such a germ. -/
theorem exists_germ_eq_mul_unit {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (b' : (f.base _* X'.presheaf).stalk x) :
    letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
      (stalkPushforwardMap f x).hom.toAlgebra
    ∃ (b : Γ(X', f ⁻¹ᵁ U)) (v : (X.presheaf.stalk x)ˣ),
      b' * algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)
          (v : X.presheaf.stalk x) =
        ((f.base _* X'.presheaf).germ U x hx).hom b := by
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) :=
    ((f.base _* X'.presheaf).germ U x hx).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(X', f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ((f.base _* X'.presheaf).stalk x) :=
    IsAffineOpen.isLocalization_pushforwardStalk f hU hx
  obtain ⟨⟨b, sden⟩, hbs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid Γ(X', f ⁻¹ᵁ U)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) b'
  obtain ⟨r, hr, hrs⟩ := sden.2
  have hunit : IsUnit (X.presheaf.germ U x hx r) :=
    IsLocalRing.notMem_maximalIdeal.mp fun hcon =>
      hr (IsAffineOpen.comap_maximalIdeal_germ hU (⟨x, hx⟩ : U) ▸ Ideal.mem_comap.mpr hcon)
  obtain ⟨v, hv⟩ := hunit
  have hsden : algebraMap Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x)
        (sden : Γ(X', f ⁻¹ᵁ U)) =
      algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)
        (X.presheaf.germ U x hx r) := by
    rw [← hrs, show algebraMap Γ(X, U) Γ(X', f ⁻¹ᵁ U) r = (f.app U).hom r from rfl]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.c r).symm
  exact ⟨b, v, by rw [hv, ← hsden]; exact hbs⟩

/-! ### Both ends of the properness of the spread-out subalgebra -/

/-- If `b * v = c` for a unit `v` of the base, then `b = c * v⁻¹`, in the algebra. -/
private theorem eq_mul_algebraMap_inv_of_mul_algebraMap_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {b c : S} {v : Rˣ} (h : b * algebraMap R S v = c) :
    b = c * algebraMap R S ↑v⁻¹ := by
  rw [← h, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

/-- **Upper properness.** If `E` is a proper subalgebra of the stalk then the sections over an
affine open `U ∋ x` of the subalgebra it cuts out are not all the sections of `f_*𝒪_{X'}`.

Were they, every germ at `x` of a section over `U` would lie in `E`, and
`Stacks.GlueSquishFactor.exists_germ_eq_mul_unit` turns those germs, divided by units of
`𝒪_{X,x}`, into the whole stalk. -/
theorem ne_top_obj_germPreimage {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (E : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x))
    (hE : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      E ≠ ⊤) :
    (germPreimage (pushforwardAlgebra f) x E).obj U ≠ ⊤ := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  intro htop
  refine hE (top_unique fun b' _ => ?_)
  obtain ⟨b, v, hbv⟩ := exists_germ_eq_mul_unit f hU hx b'
  have hbE : ((f.base _* X'.presheaf).germ U x hx).hom b ∈ E :=
    germ_mem_of_mem_germPreimage (A := pushforwardAlgebra f) hx (htop ▸ Subring.mem_top b)
  rw [eq_mul_algebraMap_inv_of_mul_algebraMap_eq hbv]
  exact mul_mem hbE (Subalgebra.algebraMap_mem _ _)

/-- **Lower properness.** If `E` is strictly larger than the image of `𝒪_{X,x}` then the
subalgebra it cuts out has, over an affine open `U ∋ x`, a section which is not a section of
`𝒪_X`: an element of `E` outside the image is a germ over `U` divided by a unit, and that germ
is the section wanted. -/
theorem exists_mem_obj_germPreimage_notMem_range {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (E : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x))
    (hE : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      E ≠ ⊥) :
    ∃ s ∈ (germPreimage (pushforwardAlgebra f) x E).obj U,
      s ∉ Set.range (f.app U).hom := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  obtain ⟨e, heE, heb⟩ : ∃ e ∈ E, e ∉ (⊥ : Subalgebra (X.presheaf.stalk x)
      ((f.base _* X'.presheaf).stalk x)) := by
    by_contra hcon
    refine hE (le_antisymm (fun e heE => ?_) bot_le)
    by_contra hb
    exact hcon ⟨e, heE, hb⟩
  obtain ⟨b, v, hbv⟩ := exists_germ_eq_mul_unit f hU hx e
  have hgerm : ((f.base _* X'.presheaf).germ U x hx).hom b ∈ E := by
    rw [← hbv]
    exact mul_mem heE (Subalgebra.algebraMap_mem _ _)
  refine ⟨b, mem_germPreimage_of_germ_mem (A := pushforwardAlgebra f) hx hgerm, ?_⟩
  rintro ⟨a, ha⟩
  refine heb ?_
  have hb : ((f.base _* X'.presheaf).germ U x hx).hom b =
      algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)
        (X.presheaf.germ U x hx a) := by
    rw [← ha]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.c a).symm
  rw [eq_mul_algebraMap_inv_of_mul_algebraMap_eq (hbv.trans hb), ← map_mul]
  exact Subalgebra.algebraMap_mem _ _

/-! ### The spreading-out -/

/-- **The spreading-out of an arbitrary stalk subalgebra.** Let `f : X' ⟶ X` be a finite
morphism to a locally Noetherian scheme whose pushforward algebra is quasi-coherent, let `U` be
an affine open and `x ∈ U`, and suppose there is an `𝒪_{X,x}`-subalgebra `E` of `(f_*𝒪_{X'})_x`
with `𝒪_{X,x} ⊊ E ⊊ (f_*𝒪_{X'})_x`. Then there is a **finite quasi-coherent subalgebra of
`f_*𝒪_{X'}` which is proper at both ends over `U`**: its sections over `U` are not all of
`Γ(X', f⁻¹U)`, and they are not all sections of `𝒪_X` either.

This is the passage that `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` makes only for
the one subalgebra `𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x`, which is not enough: by
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra` that subalgebra is
strictly above `𝒪_{X,x}` only when `m_x·(f_*𝒪_{X'})_x ⊄ 𝒪_{X,x}`, and in the remaining case —
where an arbitrary `E` is all one has — the spread-out subalgebra `𝒪_X + ℐ_x·f_*𝒪_{X'}` degenerates
to `𝒪_X`.

The subalgebra used here is not an ideal-times-algebra construction at all: it is
`Stacks.RelativeSpec.AlgebraSheaf.germPreimage`, the sections whose germ at `x` lies in `E`.
Both ends of its properness are then immediate, and the two facts that need proof are its
quasi-coherence (`Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_germPreimage`, which needs
`m_x · (f_*𝒪_{X'})_x ⊆ E`) and its finiteness
(`Stacks.RelativeSpec.AlgebraSheaf.isFinite_subalg`, from Noetherianity of the base). The
hypothesis on `m_x · (f_*𝒪_{X'})_x` is supplied by the dichotomy, in both of its branches: in the
branch `m_x·(f_*𝒪_{X'})_x ⊆ 𝒪_{X,x}` every subalgebra absorbs it, and in the other branch
`𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` is itself a subalgebra that does, and is proper at both ends.

Compared with `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` the hypotheses are weaker:
neither coherence of the underlying module nor closedness of `{x}` is used. -/
theorem exists_isFinite_subalg_ne_top_of_subalgebra_lt {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X]
    [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (E : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x))
    (hE : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)) < E)
    (hE' : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      E < ⊤) :
    ∃ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent ∧
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite ∧ C.obj U ≠ ⊤ ∧
          ∃ s ∈ C.obj U, s ∉ Set.range (f.app U).hom := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  have : Module.Finite (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    module_finite_stalk_pushforward f x
  have hne : (⊥ : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)) ≠ ⊤ :=
    fun h => hE'.ne (le_antisymm le_top (h ▸ bot_le))
  -- the subalgebra to spread out: `E` itself, or `𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x`
  obtain ⟨D, hDtop, hDbot, hmD⟩ :
      ∃ D : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x),
        D ≠ ⊤ ∧ D ≠ ⊥ ∧ ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
          ∀ b : (f.base _* X'.presheaf).stalk x,
            algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) r * b ∈ D := by
    by_cases hall : ∀ b ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
        (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)),
        ∃ a : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) a = b
    · refine ⟨E, hE'.ne, hE.ne', fun r hr b => ?_⟩
      obtain ⟨a, ha⟩ := hall _ (Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem _ hr))
      exact ha ▸ Subalgebra.algebraMap_mem E a
    · obtain ⟨b, hb, hnb⟩ := by simpa only [not_forall, not_exists] using hall
      refine ⟨addMapMaximalIdeal (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x),
        addMapMaximalIdeal_ne_top _ _ hne,
        (bot_lt_addMapMaximalIdeal _ _ hb (by simpa using hnb)).ne', fun r hr c => ?_⟩
      exact ⟨0, by simpa using Ideal.mul_mem_right c _ (Ideal.mem_map_of_mem _ hr)⟩
  exact ⟨germPreimage (pushforwardAlgebra f) x D,
    isQuasicoherent_germPreimage (pushforwardAlgebra f) x D hmD,
    isFinite_subalg _ (AlgebraicGeometry.isFinite_pushforwardAlgebra f),
    ne_top_obj_germPreimage f hU hx D hDtop,
    exists_mem_obj_germPreimage_notMem_range f hU hx D hDbot⟩

/-- **Minimality of the stalk extension, from the absence of a proper intermediate
quasi-coherent subalgebra.** If every finite quasi-coherent subalgebra of `f_*𝒪_{X'}` which is
proper over an affine open `U ∋ x` has all its sections over `U` coming from `𝒪_X`, then the
stalk extension `𝒪_{X,x} ⊂ (f_*𝒪_{X'})_x` has **no** subalgebra strictly in between.

This is the hypothesis `hmin` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` and of
`Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal`, derived from the branch of the
splitting dichotomy of [Stacks, Tag 0C1L] in which no splitting is available — which is where
the proof of the lemma needs it. It is the contrapositive of
`Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top_of_subalgebra_lt`. -/
theorem forall_eq_bot_or_eq_top_of_forall_isFinite_subalg {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X]
    [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (hno : ∀ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent →
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite → C.obj U ≠ ⊤ →
          ∀ s ∈ C.obj U, s ∈ Set.range (f.app U).hom) :
    letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
      (stalkPushforwardMap f x).hom.toAlgebra
    ∀ E : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x), E = ⊥ ∨ E = ⊤ := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  intro E
  by_cases hbot : E = ⊥
  · exact Or.inl hbot
  by_cases htop : E = ⊤
  · exact Or.inr htop
  obtain ⟨C, hqc, hfinC, hCtop, s, hsC, hsnot⟩ :=
    exists_isFinite_subalg_ne_top_of_subalgebra_lt f hU hx E
      (lt_of_le_of_ne bot_le (Ne.symm hbot)) (lt_of_le_of_ne le_top htop)
  exact absurd (hno C hqc hfinC hCtop s hsC) hsnot

/-- **The glueing half of the one-step classification of [Stacks, Tag 0C1L], with `hmin`
discharged.** `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`
with its minimality hypothesis replaced by the absence of a proper intermediate finite
quasi-coherent subalgebra over an affine open around the point — which is the branch of the
splitting dichotomy of `hsplit` in which an elementary modification has to be produced.

This is the drop-in check that
`Stacks.GlueSquishFactor.forall_eq_bot_or_eq_top_of_forall_isFinite_subalg` really is the `hmin`
the geometric producers ask for, and the two remaining hypotheses are visible in it: `hne`, that
`f` is not an isomorphism at the point, and `hiso`, that it is an isomorphism over the complement
of *that one* point.

No `@[stacks]` attribute: `hiso`, `hno` and the fibre identification are hypotheses the source
does not grant. -/
theorem exists_isGlueingTwoPoints_of_forall_isFinite_subalg {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X]
    [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X) (hx : x.IsOver (Spec (.of k)))
    (hX'ft : LocallyOfFiniteType (X' ↘ Spec (.of k)))
    (hX'qc : QuasiCompact (X' ↘ Spec (.of k)))
    (hXft : LocallyOfFiniteType (X ↘ Spec (.of k)))
    (hXqc : QuasiCompact (X ↘ Spec (.of k)))
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom)
    (hiso : ∃ U : X.Opens, (U : Set X) = {basePoint x}ᶜ ∧ IsIso (f ∣_ U))
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (hno : ∀ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent →
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite → C.obj U ≠ ⊤ →
          ∀ s ∈ C.obj U, s ∈ Set.range (f.app U).hom) :
    letI : Algebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
      (stalkConstMap X (basePoint x)).hom.toAlgebra
    letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
      ((stalkPushforwardMap f (basePoint x)).hom.comp
        (stalkConstMap X (basePoint x)).hom).toAlgebra
    (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
        ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
      (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
          stalkFibreIdeal f (basePoint x)) ≃ₐ[k] k × k) →
      ∃ a b : Spec (.of k) ⟶ X', IsGlueingTwoPoints f a b := by
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  intro hne e
  exact exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod f hf x hx hX'ft hX'qc hXft hXqc
    hmono hiso hne (forall_eq_bot_or_eq_top_of_forall_isFinite_subalg f hU hxU hno) e

end Stacks.GlueSquishFactor

end
