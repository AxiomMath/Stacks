module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Inputs
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.UnderImages
public import StacksFrontier.AlgebraicGeometry.SubalgebraAffineSections.Basic

/-!
# The affine sections statement of Tag 05JT is local, and follows from an affine cover

Let `X` be a scheme and `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The colimit
assertion of [Stacks, Tag 05JT] is reduced by
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.nonempty_isColimit_of_affineSections`
to the statement that every section of `A` over every affine open comes from a finite type
quasi-coherent subalgebra of `A` on the whole of `X`.

This file proves that that statement is **local**: if a section of `A` over an open `U` comes
from a finite type quasi-coherent subalgebra over each member of a finite cover of `U`, then it
comes from one over `U` itself. Combined with
`Stacks.AlgebraicGeometry.SubalgebraAffineSections.exists_finiteTypeSubalgebra_section_of_le`,
which transports the statement from an affine open down to the affine opens inside it, this
reduces the whole affine sections statement to the members of **one** affine open covering of
`X`, of any cardinality.

## Main results

* `comesFromFiniteTypeSubalgebra_of_finite_cover`: **locality.** The finite cover is where the
  filteredness of the finite type quasi-coherent subalgebras is used: finitely many local
  solutions are dominated by a single subalgebra, and its local sections then glue, because a
  subalgebra is a subsheaf and its inclusion is injective on sections over every open.
* `comesFromFiniteTypeSubalgebra_of_affineCover`: **the affine sections statement from an affine
  covering.** If `X` is covered by affine opens `V i` and every section of `A` over every `V i`
  comes from a finite type quasi-coherent subalgebra of `A`, then so does every section over
  every affine open of `X`.
* `nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover`: hence the colimit assertion of
  [Stacks, Tag 05JT].
* `comesFromFiniteTypeSubalgebra_of_hom`: a section which is the image of a section of **any**
  quasi-coherent algebra sheaf of finite type mapping to `A` comes from a finite type
  quasi-coherent subalgebra of `A`. This is the general form of the step
  `Stacks.AlgebraicGeometry.Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top`
  performs for the polynomial algebra sheaf.

## What this does and does not do, and no stacks attribute

No stacks attribute is attached. The covering hypothesis of
`comesFromFiniteTypeSubalgebra_of_affineCover` and the sections hypothesis of
`nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover` are hypotheses [Stacks, Tag 05JT]
does not grant, so the covering set of the colimit label is not complete. The directedness label
of that tag is already attached, at
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.isFiltered_finiteTypeSubalgebra`.

What remains for the colimit label is the extension step, the algebra analogue of
[Stacks, Tag 01PF]: for `V` an affine open of a quasi-compact quasi-separated `X` and `x` a
section of `A` over `V`, a finite type quasi-coherent subalgebra of `A` **on the whole of `X`**
having `x` among its sections over `V`. What this file changes is which affine opens that is
needed for: with the two reductions composed, the members of one chosen affine covering suffice,
rather than every affine open of `X`.

The remark in the module documentation of
`StacksFrontier/AlgebraicGeometry/SubalgebraAffineSections/Basic.lean` — that the general case is
not reducible to a finite affine covering, because an arbitrary affine open of a general scheme
need not be contained in a member of a chosen covering — is correct about the span argument that
proves `exists_finiteTypeSubalgebra_section_of_le`, and is not an obstruction to the reduction
proved here: an arbitrary affine open `U` is *covered* by basic opens of `U` that do sit inside
members of the covering, and the locality result then assembles the solution over `U` from those.

## Implementation notes

The gluing is done with `TopCat.Sheaf.existsUnique_gluing'` and
`TopCat.Sheaf.eq_of_locally_eq'`, which need the space and the target category given explicitly:
`TopCat.Sheaf` is a `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`, so a term
whose type is written in the latter form is not unified with the former unless `(X := TopCat.of
↥X)` and `(C := CommRingCat.{u})` are supplied. This is the same measurement recorded in the
implementation notes of `StacksFrontier/Topology/Sheaves/Cohomology/CechElementChase/Basic.lean`.

`TopCat.Presheaf.IsCompatible` is phrased with `TopologicalSpace.Opens.infLELeft` and
`infLERight`, while the restriction maps below are written `homOfLE inf_le_left` and
`homOfLE inf_le_right`; in `Opens X` those are the same morphism, so no rewrite is needed.

Dominating finitely many subalgebras by one is `CategoryTheory.IsFiltered.sup_objs_exists` over
the `Finset` of the chosen subalgebras, which needs decidable equality on the objects and is
therefore inside `classical`. Moving a section along a morphism of subalgebras is
`Stacks.AlgebraicGeometry.SubalgebraAffineSections.exists_section_of_hom`.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.SubalgebraSectionsLocal

open Stacks.AlgebraicGeometry.FiniteTypeSubalgebras

variable {X : Scheme.{u}}

/-- **A section of `A` over `U` comes from a finite type quasi-coherent subalgebra of `A`.** This
is the predicate the affine sections statement of [Stacks, Tag 05JT] quantifies over, and it is
written out verbatim in the hypothesis of
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.nonempty_isColimit_of_affineSections`.
-/
abbrev ComesFromFiniteTypeSubalgebra (A : AlgebraSheaf X) (U : X.Opens)
    (x : A.right.obj.obj (op U)) : Prop :=
  ∃ (B : FiniteTypeSubalgebra A) (y : (B.obj : AlgebraSheaf X).right.obj.obj (op U)),
    B.obj.arrow.right.hom.app (op U) y = x

/-- **Two successive restriction maps of a presheaf on the opens of a space compose to one.** The
first restriction is taken along an arbitrary morphism of the opposite category rather than along
a `CategoryTheory.homOfLE`, so that the statement applies to the `TopologicalSpace.Opens.infLELeft`
and `infLERight` spellings that `TopCat.Presheaf.IsCompatible` uses; the two composites agree
because the opens of a space form a thin category. -/
theorem map_restrict_apply (F : (X.Opens)ᵒᵖ ⥤ CommRingCat.{u}) {V W U : X.Opens}
    (g : (op W : (X.Opens)ᵒᵖ) ⟶ op V) (h : W ≤ U) (hVU : V ≤ U) (x : F.obj (op U)) :
    F.map g (F.map (homOfLE h).op x) = F.map (homOfLE hVU).op x := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp,
    Subsingleton.elim ((homOfLE h).op ≫ g) (homOfLE hVU).op]

/-! ### A section coming from any quasi-coherent algebra sheaf of finite type -/

/-- **A section of `A` which is the image of a section of a quasi-coherent algebra sheaf of
finite type comes from a finite type quasi-coherent subalgebra of `A`.** The subalgebra is the
image of the morphism, which is quasi-coherent by
`Stacks.AlgebraImageSurjective.imageIsQuasicoherent` and of finite type because the
corestriction to it is locally surjective.

Neither `U` nor `X` carries any hypothesis. This is the general form of the construction
`Stacks.AlgebraicGeometry.Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top` performs
for the polynomial algebra sheaf in one variable. -/
theorem comesFromFiniteTypeSubalgebra_of_hom {A C : AlgebraSheaf X} (φ : C ⟶ A)
    (hC : AlgebraSheaf.IsQuasicoherent C) (hA : AlgebraSheaf.IsQuasicoherent A)
    (hCft : AlgebraSheaf.IsFiniteType C) (U : X.Opens) (c : C.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U (φ.right.hom.app (op U) c) := by
  refine exists_finiteTypeSubalgebra_section_of_factorisation (image.ι φ) (factorThruImage φ)
    (Stacks.AlgebraImageSurjective.imageIsQuasicoherent X C A φ hC hA) hC hCft
    (Stacks.AlgebraImageSurjective.imageIsLocallySurjective X C A φ) U _ c ?_
  rw [image.fac]

/-! ### Locality -/

/-- **A section coming from a finite type quasi-coherent subalgebra over `U` comes from the same
one over any smaller open.** The witness is the restriction of the witness, and the identity it
satisfies is the naturality of the inclusion. -/
theorem comesFromFiniteTypeSubalgebra_restrict {A : AlgebraSheaf X} {U W : X.Opens} (hWU : W ≤ U)
    {x : A.right.obj.obj (op U)} (h : ComesFromFiniteTypeSubalgebra A U x) :
    ComesFromFiniteTypeSubalgebra A W (A.right.obj.map (homOfLE hWU).op x) := by
  obtain ⟨B, y, hy⟩ := h
  refine ⟨B, (B.obj : AlgebraSheaf X).right.obj.map (homOfLE hWU).op y, ?_⟩
  rw [NatTrans.naturality_apply, hy]

/-- **The inclusion of a finite type quasi-coherent subalgebra is injective on sections over
every open.** A subobject arrow is a monomorphism, a monomorphism of algebra sheaves has
monomorphic underlying morphism of sheaves of commutative rings, and a monomorphism of sheaves
of commutative rings is injective on sections. -/
theorem injective_arrow_app {A : AlgebraSheaf X} (B : FiniteTypeSubalgebra A)
    (U : (X.Opens)ᵒᵖ) : Function.Injective (B.obj.arrow.right.hom.app U) :=
  Stacks.AlgebraImageSurjective.injective_app_of_mono_sheaf
    (_root_.Opens.grothendieckTopology ↥X) B.obj.arrow.right
    (Under.mono_right_of_mono B.obj.arrow) U

/-- **Locality of the affine sections statement of [Stacks, Tag 05JT].** If a section `x` of a
quasi-coherent algebra sheaf `A` over an open `U` comes from a finite type quasi-coherent
subalgebra of `A` over each member of a finite cover of `U`, then it comes from one over `U`.

The finitely many subalgebras are dominated by a single one `S`, because the finite type
quasi-coherent subalgebras of `A` form a filtered category by
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.isFiltered_finiteTypeSubalgebra`, which
is unconditional. The local sections of `S` obtained that way agree on the overlaps, because the
inclusion of `S` is injective on sections and they all restrict to restrictions of `x`; so they
glue, and the glued section maps to `x` because it does so locally.

No hypothesis on `X` or on `U` is used beyond the quasi-coherence of `A`. -/
theorem comesFromFiniteTypeSubalgebra_of_finite_cover {A : AlgebraSheaf X}
    (hA : AlgebraSheaf.IsQuasicoherent A) {ι : Type*} [Finite ι] {U : X.Opens}
    (W : ι → X.Opens) (hWU : ∀ i, W i ≤ U) (hcov : U ≤ ⨆ i, W i)
    (x : A.right.obj.obj (op U))
    (h : ∀ i, ComesFromFiniteTypeSubalgebra A (W i) (A.right.obj.map (homOfLE (hWU i)).op x)) :
    ComesFromFiniteTypeSubalgebra A U x := by
  classical
  cases nonempty_fintype ι
  have := FiniteTypeSubalgebraFiltered.isFiltered_finiteTypeSubalgebra A hA
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists
    (Finset.image (fun i => (h i).choose) (Finset.univ : Finset ι))
  have hz : ∀ i, ∃ z : (S.obj : AlgebraSheaf X).right.obj.obj (op (W i)),
      S.obj.arrow.right.hom.app (op (W i)) z = A.right.obj.map (homOfLE (hWU i)).op x := by
    intro i
    obtain ⟨g⟩ := hS (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact SubalgebraAffineSections.exists_section_of_hom g (W i) (h i).choose_spec
  choose z hzspec using hz
  have hcompat : TopCat.Presheaf.IsCompatible (X := TopCat.of ↥X)
      (S.obj : AlgebraSheaf X).right.obj W z := by
    intro i j
    refine injective_arrow_app S (op (W i ⊓ W j)) ?_
    have hij : W i ⊓ W j ≤ U := le_trans inf_le_left (hWU i)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hzspec, hzspec,
      map_restrict_apply _ _ (hWU i) hij, map_restrict_apply _ _ (hWU j) hij]
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := TopCat.of ↥X)
    (C := CommRingCat.{u})
    ⟨(S.obj : AlgebraSheaf X).right.obj, (S.obj : AlgebraSheaf X).right.2⟩
    W U (fun i => homOfLE (hWU i)) hcov z hcompat
  refine ⟨S, y, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (X := TopCat.of ↥X) (C := CommRingCat.{u})
    ⟨A.right.obj, A.right.2⟩ W U (fun i => homOfLE (hWU i)) hcov _ x fun i => ?_
  rw [← NatTrans.naturality_apply, hy i, hzspec i]

/-! ### The affine sections statement from an affine covering -/

/-- **The affine sections statement of [Stacks, Tag 05JT] from an affine open covering.** Let `A`
be a quasi-coherent sheaf of commutative `𝒪_X`-algebras and let `V` be a family of affine opens
covering `X`. If every section of `A` over every `V i` comes from a finite type quasi-coherent
subalgebra of `A`, then so does every section of `A` over every affine open of `X`.

The covering need not be finite, and `X` carries no hypothesis: the quasi-compactness used is
that of the affine open `U` the conclusion is about. Every point of `U` has a basic open
neighbourhood in `U` contained in a member of the covering, by
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`; those basic opens are affine, so
`Stacks.AlgebraicGeometry.SubalgebraAffineSections.exists_finiteTypeSubalgebra_section_of_le`
solves the problem over each of them; finitely many cover `U`; and
`comesFromFiniteTypeSubalgebra_of_finite_cover` assembles the solution over `U`. -/
theorem comesFromFiniteTypeSubalgebra_of_affineCover (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hVcov : ∀ p : ↥X, ∃ i, p ∈ V i)
    (hsec : ∀ (i : ι) (m : A.right.obj.obj (op (V i))),
      ComesFromFiniteTypeSubalgebra A (V i) m)
    {U : X.Opens} (hU : IsAffineOpen U) (x : A.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U x := by
  classical
  have key : ∀ p : ↥U, ∃ (f : Γ(X, U)) (i : ι),
      X.basicOpen f ≤ V i ∧ (p : ↥X) ∈ X.basicOpen f := by
    intro p
    obtain ⟨i, hi⟩ := hVcov (p : ↥X)
    obtain ⟨f, hfV, hpf⟩ := hU.exists_basicOpen_le (⟨(p : ↥X), hi⟩ : ↥(V i)) p.2
    exact ⟨f, i, hfV, hpf⟩
  choose f idx hfV hpf using key
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover
    (fun p : ↥U => (X.basicOpen (f p) : Set ↥X)) (fun p => (X.basicOpen (f p)).isOpen)
    (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hpf ⟨q, hq⟩⟩)
  refine comesFromFiniteTypeSubalgebra_of_finite_cover hA
    (ι := {p : ↥U // p ∈ t}) (fun p => X.basicOpen (f p.1))
    (fun p => X.basicOpen_le (f p.1)) ?_ x fun p => ?_
  · intro q hq
    obtain ⟨p, hpt, hqp⟩ := by simpa only [Set.mem_iUnion, exists_prop] using ht hq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hpt⟩, hqp⟩
  · exact SubalgebraAffineSections.exists_finiteTypeSubalgebra_section_of_le A hA
      (hU.basicOpen (f p.1)) (hV (idx p.1)) (hfV p.1) (hsec (idx p.1)) _

/-- **The colimit assertion of [Stacks, Tag 05JT] from an affine open covering.** A
quasi-coherent sheaf of commutative `𝒪_X`-algebras is the colimit of its finite type
quasi-coherent subalgebras, with the canonical inclusions, as soon as `X` has an affine open
covering over whose members every section of `A` comes from a finite type quasi-coherent
subalgebra of `A`.

No stacks attribute is attached: the covering hypothesis is not one [Stacks, Tag 05JT] grants. -/
theorem nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hVcov : ∀ p : ↥X, ∃ i, p ∈ V i)
    (hsec : ∀ (i : ι) (m : A.right.obj.obj (op (V i))),
      ComesFromFiniteTypeSubalgebra A (V i) m) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone A)) :=
  FiniteTypeSubalgebraFiltered.nonempty_isColimit_of_affineSections A hA fun _ hU x =>
    comesFromFiniteTypeSubalgebra_of_affineCover A hA V hV hVcov hsec hU x

/-- **The affine case, recovered.** On an affine scheme the one-member covering by `⊤` satisfies
the hypothesis of `comesFromFiniteTypeSubalgebra_of_affineCover`, because
`Stacks.AlgebraicGeometry.Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top` solves
the problem for a global section unconditionally. This reproves
`Stacks.AlgebraicGeometry.SubalgebraAffineSections.exists_finiteTypeSubalgebra_section_of_isAffine`
and so records that the covering reduction is a generalization of it rather than a different
statement. -/
theorem comesFromFiniteTypeSubalgebra_of_isAffine [IsAffine X] (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) {U : X.Opens} (hU : IsAffineOpen U)
    (x : A.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U x :=
  comesFromFiniteTypeSubalgebra_of_affineCover A hA (fun _ : Unit => ⊤)
    (fun _ => isAffineOpen_top X) (fun _ => ⟨(), trivial⟩)
    (fun _ m => Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top A hA m) hU x

end Stacks.AlgebraicGeometry.SubalgebraSectionsLocal

end
