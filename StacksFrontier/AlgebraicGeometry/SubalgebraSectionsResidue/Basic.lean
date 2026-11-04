module

public import StacksFrontier.AlgebraicGeometry.SubalgebraSectionsLocal.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.Basic

/-!
# The residue of Tag 05JT and Tag 0817, with every subobject condition removed

Let `X` be a scheme and `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The colimit
assertions of [Stacks, Tag 05JT] and [Stacks, Tag 0817] are, at this pin, reduced to a single
statement about sections: over every affine open `U`, every `x ∈ A(U)` comes from a finite type
quasi-coherent *subalgebra* of `A` (the predicate
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.ComesFromFiniteTypeSubalgebra`).

This file replaces that statement by one which asks for **no subobject, no monomorphism and no
subalgebra at all**: a quasi-coherent algebra sheaf `C` of finite type, *any* morphism
`φ : C ⟶ A`, and a section of `C` over `U` whose image is `x`. The two are **equivalent** for
quasi-coherent `A` — nothing is weakened and nothing is given away — and the second is the form
in which the remaining mathematics should be attacked, since producing a map into `A` out of a
finite type algebra sheaf is a construction, while producing a subobject of `A` carries a mono
condition that
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.comesFromFiniteTypeSubalgebra_of_hom`
discharges once and for all through the image.

It then combines that with the locality already proved in
`StacksFrontier/AlgebraicGeometry/SubalgebraSectionsLocal/Basic.lean`, so that the hypothesis is
needed **only around each point of `X`, at one affine open of the asker's choosing**, and
delivers the colimit assertions of both tags from it.

## Main definitions

* `HitByFiniteTypeAlgebra A U x`: there are a quasi-coherent algebra sheaf `C` of finite type, a
  morphism `C ⟶ A`, and a section of `C` over `U` mapping to `x`.

## Main results

* `comesFromFiniteTypeSubalgebra_iff_hitByFiniteTypeAlgebra`: **the two forms of the residue
  agree**, for quasi-coherent `A`, at every open and with no hypothesis on `X`.
* `hitByFiniteTypeAlgebra_top`: the hypothesis holds at `⊤` for every scheme, so it is not
  vacuous; this is `Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top` read through the
  equivalence.
* `comesFromFiniteTypeSubalgebra_of_affineCover_hit` and
  `comesFromFiniteTypeSubalgebra_of_forall_exists_affine`: the affine sections statement at
  **every** affine open, from the hypothesis at the members of an affine covering, respectively at
  one affine open around each point.
* `nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover_hit`: the colimit assertion of
  [Stacks, Tag 05JT] from that hypothesis.
* `nonempty_isColimit_finiteSubalgebraCocone_of_affineCover_hit`: the colimit assertion of
  [Stacks, Tag 0817] from that hypothesis, for integral `A`.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached.** Every statement below carries a
hypothesis the tags do not grant, and that hypothesis is the whole residue of the
`finite_subalgebras` label of [Stacks, Tag 0817] and of the `the colimit` label of
[Stacks, Tag 05JT]. The directedness halves of both labels are proved and unconditional
(`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.isFiltered_finiteTypeSubalgebra` and
`Stacks.AlgebraicGeometry.FiniteSubalgebras.isFiltered_finiteSubalgebra`), so one assertion of
each label is proved and the other is not; the covering set is therefore incomplete and the tag
is withheld.

What the residue needs:

* **The source's own route to it is through [Stacks, Tag 05JS]**, not through
  [Stacks, Tag 01PF]: Tag 05JT's proof writes `A` as a directed colimit of *finitely presented*
  quasi-coherent algebras and takes the images. Tag 05JS's proof in turn needs
  `Sym_{𝒪_X}(F)` for `F` a finitely presented quasi-coherent module, as does the proof of part
  (2) of Tag 0817.
* **That symmetric algebra does not exist in this repository as a sheaf of algebras.** For
  `E : X.Modules` the repository has `Sym E` as *graded data* —
  `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SymmetricAlgebraConstruction/Scheme.lean`) with
  values in `SheafOfModules.GradedAlgebra X.ringCatSheaf`, and `schemeSheafGradedAlgebra`
  (`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Scheme.lean`) with values in
  `SheafGradedAlgebra X` — together with quasi-coherence of the pieces, degree-one generation, the
  affine universal property and base change. It has **no** construction landing in
  `Stacks.RelativeSpec.AlgebraSheaf X = CategoryTheory.Under X.sheaf`. The ungraded realization
  stops at a *presheaf* of `RingCat` (`Stacks.GradedAlgebra.totalPresheaf`, in
  `Algebra/Category/ModuleCat/Sheaf/UngradedAlgebras.lean`), whose own documentation records that
  the sheafification, the associativity of the extended multiplication and the identification of the
  underlying module sheaf are not proved. The one functor between the two categories is the
  **forgetful** one, `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor`.
* **The alternative route through [Stacks, Tag 01PF] is blocked at the same distance.** That
  module-level statement — on a quasi-compact quasi-separated scheme every section of a
  quasi-coherent module over an affine open lies in a finite type quasi-coherent submodule — is
  not proved here either. It exists only as the named hypothesis
  `Stacks.AlgebraicGeometry.Tag01PGColimit.AffineSections`, a `Prop`-valued definition that is
  consumed and never discharged; its affine case is proved with `[IsAffine X]`
  (`Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on`), its glueing step and its
  spelling primitives are proved, and the induction over a finite affine cover is not. Moreover
  that induction needs the affine case in a form prescribing the submodule over the overlap,
  which `StacksFrontier/AlgebraicGeometry/SubmoduleAgree/Basic.lean` records as strictly stronger
  than the proved one. Even granted it, the passage from a submodule to a subalgebra is the
  missing symmetric algebra again.
* **There is no route through global sections, and the obstruction is not an artifact.**
  `hitByFiniteTypeAlgebra_top` is unconditional, and
  `Stacks.AlgebraicGeometry.SubalgebraAffineSections.exists_finiteTypeSubalgebra_section_of_le`
  propagates the statement from a larger affine open *downward* only, which is why an affine `X`
  is a complete case and a general `X` is not reducible to a finite affine cover. On `ℙ¹` the
  algebra `Sym(𝒪(-1))` has only constants as global sections while being a finite type
  quasi-coherent subalgebra of itself, as recorded in
  `StacksFrontier/AlgebraicGeometry/ColimitGlobal/Basic.lean`.

A fourth route, mirroring Tag 01PF at the level of algebras and so using no symmetric algebra at
all, is visible but not taken here: the fibre product `A ×_{j_*(A|_U)} j_*G` is a quasi-coherent
subalgebra of `A` restricting to `G` on `U`, which is the algebra analogue of
[Stacks, Tag 01PE]; what that route then needs is the glueing of quasi-coherent subalgebras along
a two-member open cover and the affine cut-down to finite type. None of the three is in this
repository.

## Implementation notes

`HitByFiniteTypeAlgebra` bundles the quasi-coherence and finite typeness of `C` into the
existential rather than taking them as instance arguments, so that it is a `Prop` depending only
on `A`, `U` and `x` and can be used as the hypothesis of the covering statements below.

The forward direction of the equivalence is immediate — a finite type quasi-coherent subalgebra
*is* such a `C`, its two properties being the two components of `ObjectProperty.FullSubcategory`'s
`property` field — and the backward direction is
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.comesFromFiniteTypeSubalgebra_of_hom`, which
builds the subobject as the image of `φ` using
`Stacks.AlgebraImageSurjective.imageIsQuasicoherent` and
`Stacks.AlgebraImageSurjective.imageIsLocallySurjective`. Both of those are proved and
unconditional on `X`, and the identification of the underlying module of the image is
`Stacks.AlgebraImageSurjective.underlyingModuleImageIso`.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.SubalgebraSectionsResidue

open Stacks.AlgebraicGeometry.FiniteTypeSubalgebras
open Stacks.AlgebraicGeometry.SubalgebraSectionsLocal

variable {X : Scheme.{u}}

/-- **A section of `A` over `U` is in the image of a quasi-coherent algebra sheaf of finite
type.** No subobject and no monomorphism occurs: the morphism `φ` is arbitrary. This is the
residue of the colimit assertions of [Stacks, Tag 05JT] and [Stacks, Tag 0817] in the form in
which they should be attacked, and it is equivalent to
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.ComesFromFiniteTypeSubalgebra` by
`comesFromFiniteTypeSubalgebra_iff_hitByFiniteTypeAlgebra`. -/
abbrev HitByFiniteTypeAlgebra (A : AlgebraSheaf X) (U : X.Opens)
    (x : A.right.obj.obj (op U)) : Prop :=
  ∃ (C : AlgebraSheaf X) (φ : C ⟶ A) (c : C.right.obj.obj (op U)),
    AlgebraSheaf.IsQuasicoherent C ∧ AlgebraSheaf.IsFiniteType C ∧
      φ.right.hom.app (op U) c = x

/-- **A section coming from a finite type quasi-coherent subalgebra is hit by a finite type
quasi-coherent algebra sheaf.** The algebra sheaf is the subalgebra itself and the morphism is
its inclusion; the two properties asked for are the two components of the object's membership in
the defining property of `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.FiniteTypeSubalgebra`.
Neither `X`, nor `U`, nor `A` carries any hypothesis. -/
theorem hitByFiniteTypeAlgebra_of_comesFrom {A : AlgebraSheaf X} {U : X.Opens}
    {x : A.right.obj.obj (op U)} (h : ComesFromFiniteTypeSubalgebra A U x) :
    HitByFiniteTypeAlgebra A U x := by
  obtain ⟨B, y, hy⟩ := h
  exact ⟨(B.obj : AlgebraSheaf X), B.obj.arrow, y, B.property.1, B.property.2, hy⟩

/-- **A section hit by a finite type quasi-coherent algebra sheaf comes from a finite type
quasi-coherent subalgebra.** The subalgebra is the image of the morphism, by
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.comesFromFiniteTypeSubalgebra_of_hom`; the
quasi-coherence of `A` is what that image construction needs, and `U` and `X` carry no
hypothesis. -/
theorem comesFromFiniteTypeSubalgebra_of_hitByFiniteTypeAlgebra {A : AlgebraSheaf X}
    (hA : AlgebraSheaf.IsQuasicoherent A) {U : X.Opens} {x : A.right.obj.obj (op U)}
    (h : HitByFiniteTypeAlgebra A U x) : ComesFromFiniteTypeSubalgebra A U x := by
  obtain ⟨C, φ, c, hCqc, hCft, hc⟩ := h
  exact hc ▸ comesFromFiniteTypeSubalgebra_of_hom φ hCqc hA hCft U c

/-- **The two forms of the residue of [Stacks, Tag 05JT] agree.** For a quasi-coherent algebra
sheaf, a section over any open comes from a finite type quasi-coherent *subalgebra* exactly when
it is in the image of *some* morphism out of a finite type quasi-coherent algebra sheaf. So
dropping the subobject condition from the residue gives nothing away. -/
theorem comesFromFiniteTypeSubalgebra_iff_hitByFiniteTypeAlgebra {A : AlgebraSheaf X}
    (hA : AlgebraSheaf.IsQuasicoherent A) {U : X.Opens} (x : A.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U x ↔ HitByFiniteTypeAlgebra A U x :=
  ⟨hitByFiniteTypeAlgebra_of_comesFrom,
    comesFromFiniteTypeSubalgebra_of_hitByFiniteTypeAlgebra hA⟩

/-- **The hypothesis holds at `⊤`, for every scheme.** A global section of a quasi-coherent
algebra sheaf is hit by the polynomial algebra sheaf in one variable, which is quasi-coherent of
finite type; this is
`Stacks.AlgebraicGeometry.Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top` read
through `hitByFiniteTypeAlgebra_of_comesFrom`. Recorded so that the hypothesis of the statements
below is known to be satisfiable, and so that the exact gap is visible: it is the passage from
`⊤` to an arbitrary affine open, which no shrinking argument supplies. -/
theorem hitByFiniteTypeAlgebra_top (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) (x : A.right.obj.obj (op ⊤)) :
    HitByFiniteTypeAlgebra A ⊤ x :=
  hitByFiniteTypeAlgebra_of_comesFrom
    (Tag05JTColimitGlobal.exists_finiteTypeSubalgebra_section_top A hA x)

/-- **The affine sections statement of [Stacks, Tag 05JT] from an affine covering, in the hom
form.** If `X` has a covering by affine opens over each of which every section of `A` is hit by a
finite type quasi-coherent algebra sheaf mapping to `A`, then every section of `A` over *every*
affine open comes from a finite type quasi-coherent subalgebra of `A`.

The covering need not be finite and `X` carries no hypothesis; the content is
`Stacks.AlgebraicGeometry.SubalgebraSectionsLocal.comesFromFiniteTypeSubalgebra_of_affineCover`,
whose hypothesis is converted by
`comesFromFiniteTypeSubalgebra_of_hitByFiniteTypeAlgebra`. -/
theorem comesFromFiniteTypeSubalgebra_of_affineCover_hit (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hVcov : ∀ p : ↥X, ∃ i, p ∈ V i)
    (hhit : ∀ (i : ι) (m : A.right.obj.obj (op (V i))), HitByFiniteTypeAlgebra A (V i) m)
    {U : X.Opens} (hU : IsAffineOpen U) (x : A.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U x :=
  comesFromFiniteTypeSubalgebra_of_affineCover A hA V hV hVcov
    (fun i m => comesFromFiniteTypeSubalgebra_of_hitByFiniteTypeAlgebra hA (hhit i m)) hU x

/-- **One affine open around each point suffices.** If every point of `X` has *some* affine open
neighbourhood over which every section of `A` is hit by a finite type quasi-coherent algebra
sheaf mapping to `A`, then every section of `A` over every affine open comes from a finite type
quasi-coherent subalgebra of `A`.

This is `comesFromFiniteTypeSubalgebra_of_affineCover_hit` at the covering indexed by the points
of `X`, and it is the weakest form of the residue the locality supports: the open may be
chosen freely at each point, and nothing is asked at any other open. -/
theorem comesFromFiniteTypeSubalgebra_of_forall_exists_affine (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (hloc : ∀ p : ↥X, ∃ V : X.Opens, IsAffineOpen V ∧ p ∈ V ∧
      ∀ m : A.right.obj.obj (op V), HitByFiniteTypeAlgebra A V m)
    {U : X.Opens} (hU : IsAffineOpen U) (x : A.right.obj.obj (op U)) :
    ComesFromFiniteTypeSubalgebra A U x := by
  choose V hVaff hpV hVhit using hloc
  exact comesFromFiniteTypeSubalgebra_of_affineCover_hit A hA V hVaff
    (fun p => ⟨p, hpV p⟩) hVhit hU x

/-- **The colimit assertion of [Stacks, Tag 05JT] from the hom form of the residue.** A
quasi-coherent sheaf of commutative `𝒪_X`-algebras is the colimit of its finite type
quasi-coherent subalgebras, with the canonical inclusions, as soon as `X` has an affine open
covering over whose members every section of `A` is hit by a finite type quasi-coherent algebra
sheaf mapping to `A`.

**No stacks attribute is attached**: the covering hypothesis is not one the tag grants. -/
theorem nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover_hit (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hVcov : ∀ p : ↥X, ∃ i, p ∈ V i)
    (hhit : ∀ (i : ι) (m : A.right.obj.obj (op (V i))), HitByFiniteTypeAlgebra A (V i) m) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone A)) :=
  FiniteTypeSubalgebraFiltered.nonempty_isColimit_of_affineSections A hA fun _ hU x =>
    comesFromFiniteTypeSubalgebra_of_affineCover_hit A hA V hV hVcov hhit hU x

/-- **The colimit assertion of [Stacks, Tag 0817] from the hom form of the residue.** An integral
quasi-coherent sheaf of commutative `𝒪_X`-algebras is the colimit of its **finite**
quasi-coherent subalgebras, with the canonical inclusions, as soon as `X` has an affine open
covering over whose members every section of `A` is hit by a finite type quasi-coherent algebra
sheaf mapping to `A`.

Integrality is used exactly twice, and only to identify the two indexing categories:
`Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_finiteSubalgebra_section_iff` reads the
sections statement in tag 0817's vocabulary, and
`Stacks.AlgebraicGeometry.FiniteSubalgebras`'s
`nonempty_isColimit_finiteSubalgebraCocone_of_affineSections` transports the colimit.
Neither quasi-compactness nor quasi-separatedness of `X` appears: both are consumed entirely
by `hhit`.

**No stacks attribute for the `finite_subalgebras` label of [Stacks, Tag 0817] is attached.**
That label covers two assertions; the directedness one is proved and
unconditional as
`Stacks.AlgebraicGeometry.FiniteSubalgebras.isFiltered_finiteSubalgebra`, and this one carries a
hypothesis the tag does not grant, so the covering set is incomplete. -/
theorem nonempty_isColimit_finiteSubalgebraCocone_of_affineCover_hit (A : AlgebraSheaf X)
    (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hVcov : ∀ p : ↥X, ∃ i, p ∈ V i)
    (hhit : ∀ (i : ι) (m : A.right.obj.obj (op (V i))), HitByFiniteTypeAlgebra A (V i) m) :
    Nonempty (IsColimit (FiniteSubalgebras.finiteSubalgebraCocone A)) :=
  FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone_of_affineSections A hAqc hAint
    fun _ hU x => (FiniteSubalgebras.exists_finiteSubalgebra_section_iff hAint x).mpr
      (comesFromFiniteTypeSubalgebra_of_affineCover_hit A hAqc V hV hVcov hhit hU x)

end Stacks.AlgebraicGeometry.SubalgebraSectionsResidue

end
