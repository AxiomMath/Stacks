module

public import StacksFrontier.AlgebraicGeometry.AlgebraFibreProductQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.SubalgebraSectionsResidue.Basic

/-!
# The extension half of the algebra analogue of Tag 01PF: a quasi-coherent algebra hitting a
section over an affine open

Let `X` be a quasi-separated scheme, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras,
`U ⊆ X` an affine open and `x` a section of `A` over `U`. This file produces

* a sheaf of commutative `𝒪_U`-algebras `G` which is quasi-coherent **and of finite type**,
  together with a morphism `φ : G ⟶ A|_U`, and
* a **quasi-coherent** sheaf of commutative `𝒪_X`-algebras — the extension algebra
  `A ×_{j_*(A|_U)} j_* G` of
  `StacksFrontier/AlgebraicGeometry/AlgebraOpenExtension/Basic.lean` — with a morphism to `A`
  (its projection) and a section over `U` mapping to `x`.

That is the *extension* half of the extension-and-trim induction which is the algebra analogue
of [Stacks, Tag 01PF], and which the module documentation of
`StacksFrontier/AlgebraicGeometry/SubalgebraSectionsResidue/Basic.lean` records as the residue
of the `the colimit` label of [Stacks, Tag 05JT] and of the `finite_subalgebras` label of
[Stacks, Tag 0817]. What is **not** here is the trim: the extension agrees with `A` away from
`U`, so it is not of finite type, and
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.HitByFiniteTypeAlgebra` is not proved at an
arbitrary affine open. See "What is not done" below for the exact remaining statement.

## Main results

* `isQuasicoherent_algebraPullback_obj`: the restriction of a quasi-coherent algebra sheaf along
  an **arbitrary** morphism of schemes is quasi-coherent, as an instance.
* `isQuasicoherent_extension`: **the extension algebra is quasi-coherent with no hypothesis on
  the restriction** —
  `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_extensionAlgebra` with its third
  hypothesis discharged.
* `exists_fst_eq_of_isPullback`: elements of a cartesian square of commutative rings — given
  sections of the two corners agreeing in the third, a section of the fibre product restricting
  to both.
* `exists_hom_section_of_eq_top`:
  `Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.hitByFiniteTypeAlgebra_top` at an open
  which is merely *equal* to `⊤`, which is the form the preimage of an open under its own
  inclusion arrives in.
* `exists_extensionAlgebra_section`: **the statement described above.**

## The hypothesis the records called absent, and which of them was needed

`AlgebraFibreProductQcoh/Basic.lean` carries quasi-coherence of the restriction
`(algebraPullback j).obj A` as an instance hypothesis of `isQuasicoherent_extensionAlgebra`, and
calls it in its own module documentation "a real gap … recorded as such", the identification of
the underlying module of the inverse image with `AlgebraicGeometry.Scheme.Modules.pullback`
being "a third bridge … not built here".

**No bridge is needed, because the statement is already proved.**
`Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`
(`StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/Invertible.lean`) is exactly
`AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A)` for an **arbitrary** morphism of
schemes `g : T ⟶ S` and an arbitrary quasi-coherent `A`; it is the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA], proved there by checking the
comparison `g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` invertible on stalks. So the only hypotheses
`isQuasicoherent_extension` keeps are quasi-compactness of the immersion, which is what
[Stacks, Tag 01LC] asks of the two direct images in the cospan, and quasi-coherence of `A` and
of `G`.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.**
`exists_extensionAlgebra_section` carries `QuasiSeparatedSpace ↥X` (which [Stacks, Tag 05JT]
does grant) **and** `IsAffineOpen U` (which it does not: the tag quantifies over nothing but
`X` and `A`), and — decisively — its conclusion is about a quasi-coherent extension, not about
a quasi-coherent extension **of finite type**. The colimit assertion of [Stacks, Tag 05JT]
needs `nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover_hit` of
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue`, whose `hhit` hypothesis is
`HitByFiniteTypeAlgebra`, and nothing below proves that. So the
covering set of the `the colimit` label is still incomplete and the label stays untagged; the
`directedness` label of that tag is live and untouched, at
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.isFiltered_finiteTypeSubalgebra`.

The one statement that remains, written out:

* **the trim.** For `X` quasi-compact and quasi-separated, `E` a quasi-coherent algebra sheaf
  with a morphism to `A`, and `U` an affine open over which the restriction of `E` is of finite
  type, a quasi-coherent algebra sheaf of finite type on the whole of `X` with a morphism to `A`
  whose sections over `U` still reach everything `E`'s do. The pieces of it are available:
  `Stacks.AlgebraicGeometry.SubalgebraTrimAffine.exists_finset_hasNumeratorIn_sections` cuts
  down over one affine open, `Stacks.RelativeSpec.AlgebraSheaf.isFiniteType_glue_of_pieces` and
  `Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_glue` assemble the pieces of a covering
  family, and `Stacks.RelativeSpec.AlgebraSheaf.isFiniteType_of_iSup_eq_top` says finite type of
  a quasi-coherent algebra sheaf is local on the base. What is **absent** is the induction that
  runs them along a chain of opens, together with the two relativizations it needs:
  quasi-coherence and finite type of a concrete subalgebra *over an open of `X`* rather than
  over `X`, since the glueing results above require the covering family to admit an affine
  refinement of the whole of `X`, which the intermediate stages of the induction do not.

## Implementation notes

Three measurements.

* **The transport across `U.ι ⁻¹ᵁ U = ⊤` must be done by `subst`, not by `eqToHom`.** The
  section of the restriction `A|_U` that the extension is built from is
  `(extensionUnit U.ι A)` applied to `x`, which lands in the sections over
  `U.ι ⁻¹ᵁ U`, while `hitByFiniteTypeAlgebra_top` speaks about the sections over `⊤`. Carrying
  the element across by `AlgebraSheaf.right.obj.map (eqToHom …)` in both directions and
  cancelling the two does work, but the cancellation needs `CategoryTheory.comp_apply` in the
  `←` direction and **`rw` cannot find its pattern**: the middle object of the composite is the
  sections of `j_*(A|_U)` over `U` on one side and the sections of `A|_U` over `U.ι ⁻¹ᵁ U` on
  the other, which are definitionally equal and not syntactically equal, so the instantiation
  of `comp_apply`'s implicit object cannot match both at the transparency `rw` uses.
  `exists_hom_section_of_eq_top` moves the equation into the *statement* instead, where `subst`
  discharges it and no transport survives — §8.219's idiom (write the thing out so the raw
  spelling never appears) at the level of an open.
* **Sections of a cartesian square of rings come from `CommRingCat.pullbackCone`.** The square
  `Stacks.AlgebraicGeometry.AlgebraOpenExtension.isPullback_extensionAlgebra_sections` is an
  `IsPullback` in `CommRingCat`, and the element is produced by lifting *out of* Mathlib's
  constructed cone — whose point is the `RingHom.eqLocus` of the two maps `A × B ⟶ C`, so a
  pair agreeing in `C` is literally an element of it — rather than by finding a ring whose
  points are elements. The two facs are then `CategoryTheory.ConcreteCategory.congr_hom` of
  `CategoryTheory.IsPullback.lift_fst` and `lift_snd`.
* `((algebraPushforward j).map φ).right.hom.app (op V)` and
  `φ.right.hom.app (op (j ⁻¹ᵁ V))` are definitionally equal — `algebraPushforward` is
  `CategoryTheory.Under.post` of the direct image of sheaves of rings followed by
  `CategoryTheory.Under.map`, neither of which touches the sections — so the proof obligation of
  `exists_fst_eq_of_isPullback` is discharged by a term stated in the second spelling with no
  bridging. They are *not* syntactically equal, which is what the first note is about.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec
open Stacks.AlgebraicGeometry.AlgebraOpenExtension

universe u

namespace Stacks.AlgebraicGeometry.AlgebraExtensionSection

/-- **The restriction of a quasi-coherent algebra sheaf along an arbitrary morphism of schemes
is quasi-coherent**, as an instance. This is
`Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`, the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA]; it is recorded here in instance
form because the quasi-coherence of the extension algebra needs it of
`(algebraPullback j).obj A` and carried it as a hypothesis for want of it. -/
instance isQuasicoherent_algebraPullback_obj {T S : Scheme.{u}} (g : T ⟶ S)
    (A : AlgebraSheaf S) [A.IsQuasicoherent] :
    ((algebraPullback g).obj A).IsQuasicoherent :=
  Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent g A ‹_›

/-- **The extension algebra `A ×_{j_*(A|_U)} j_* G` is quasi-coherent**, with no hypothesis on
the restriction of `A` to `U`: the three hypotheses are quasi-compactness of the open immersion,
which [Stacks, Tag 01LC] needs of the two direct images in the cospan, and quasi-coherence of
`A` and of `G`.

This is `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_extensionAlgebra` with its
third hypothesis discharged by `isQuasicoherent_algebraPullback_obj`. -/
theorem isQuasicoherent_extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (A : AlgebraSheaf X) [A.IsQuasicoherent] (G : AlgebraSheaf U)
    [G.IsQuasicoherent] (φ : G ⟶ (algebraPullback j).obj A) :
    (extensionAlgebra j A G φ).IsQuasicoherent :=
  AlgebraFibreProduct.isQuasicoherent_extensionAlgebra j A G φ

/-- Faithfulness check for `isQuasicoherent_extension`, with every hypothesis an explicit
argument: quasi-coherence of the two given algebra sheaves and quasi-compactness of the
immersion, and **nothing about the restriction `(algebraPullback j).obj A`**, which is the one
hypothesis `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_extensionAlgebra`
carries and this does not. -/
example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (A : AlgebraSheaf X) (G : AlgebraSheaf U) (φ : G ⟶ (algebraPullback j).obj A)
    (_hA : AlgebraSheaf.IsQuasicoherent A) (_hG : AlgebraSheaf.IsQuasicoherent G) :
    AlgebraSheaf.IsQuasicoherent
      (pullback (extensionUnit j A) ((algebraPushforward j).map φ)) :=
  isQuasicoherent_extension j A G φ

/-- **Sections of a cartesian square of commutative rings.** If a section of `A` and a section
of `B` have the same image in `C`, there is a section of the fibre product restricting to both.

The witness is produced by lifting out of `CommRingCat.pullbackCone`, whose point is the
`RingHom.eqLocus` of the two maps `A × B ⟶ C` and therefore contains the given pair by
hypothesis; no ring whose points are elements has to be found. -/
theorem exists_fst_eq_of_isPullback {P A B C : CommRingCat.{u}} {p : P ⟶ A} {q : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback p q f g) (a : A) (b : B)
    (hab : f.hom a = g.hom b) :
    ∃ e : P, p.hom e = a ∧ q.hom e = b := by
  refine ⟨(h.lift (CommRingCat.pullbackCone f g).fst (CommRingCat.pullbackCone f g).snd
      (CommRingCat.pullbackCone f g).condition).hom
      (⟨(a, b), hab⟩ : (CommRingCat.pullbackCone f g).pt), ?_, ?_⟩
  · exact ConcreteCategory.congr_hom (h.lift_fst _ _ _) _
  · exact ConcreteCategory.congr_hom (h.lift_snd _ _ _) _

/-- **A section of a quasi-coherent algebra sheaf over an open equal to `⊤` is the image of a
section of a quasi-coherent algebra sheaf of finite type.** This is
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.hitByFiniteTypeAlgebra_top` with the equality
moved into the statement, so that `subst` discharges it and no transport of the section along an
`eqToHom` survives; see the implementation notes for why the transport is worth avoiding.

The open the caller has is `j ⁻¹ᵁ U` for `j` the inclusion of `U`, which *equals* `⊤` and is not
it. -/
theorem exists_hom_section_of_eq_top {U : Scheme.{u}} (B : AlgebraSheaf U) [B.IsQuasicoherent]
    {V : U.Opens} (hV : V = ⊤) (y : B.right.obj.obj (op V)) :
    ∃ (G : AlgebraSheaf U) (φ : G ⟶ B) (g : G.right.obj.obj (op V)),
      AlgebraSheaf.IsQuasicoherent G ∧ AlgebraSheaf.IsFiniteType G ∧
        φ.right.hom.app (op V) g = y := by
  subst hV
  exact SubalgebraSectionsResidue.hitByFiniteTypeAlgebra_top B ‹_› y

variable {X : Scheme.{u}}

/-- **The extension half of the algebra analogue of [Stacks, Tag 01PF].** Let `X` be a
quasi-separated scheme, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras, `U` an affine
open of `X` and `x` a section of `A` over `U`. Then there are a quasi-coherent sheaf of
commutative `𝒪_U`-algebras `G` **of finite type** and a morphism `φ : G ⟶ A|_U` whose extension
algebra `A ×_{j_*(A|_U)} j_* G` is quasi-coherent and has a section over `U` mapping to `x`
under the projection to `A`.

Quasi-separatedness of `X` is used once, to make the inclusion of the affine — hence
quasi-compact — open `U` a quasi-compact morphism, which is what [Stacks, Tag 01LC] asks of the
two direct images in the cospan. Affineness of `U` is used only for that quasi-compactness and
could be weakened to it.

**No `@[stacks]` attribute is attached and none is earned**: the extension is quasi-coherent and
is *not* of finite type — it agrees with `A` away from `U` — so this is not
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue.HitByFiniteTypeAlgebra` and does not feed
`nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineCover_hit`. The remaining statement is
the trim, written out in this file's module documentation.

The finite type `G` comes from `hitByFiniteTypeAlgebra_top` of
`Stacks.AlgebraicGeometry.SubalgebraSectionsResidue` on the scheme `U`, applied to the image of
`x` under the unit `A ⟶ j_*(A|_U)`, which is a *global* section of the restriction `A|_U`
because `j ⁻¹ᵁ U = ⊤`; the section of the extension is
then the pair `(x, g)`, which agrees in `j_*(A|_U)` by construction. -/
theorem exists_extensionAlgebra_section [QuasiSeparatedSpace ↥X] (A : AlgebraSheaf X)
    [A.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (x : A.right.obj.obj (op U)) :
    ∃ (G : AlgebraSheaf U.toScheme) (φ : G ⟶ (algebraPullback U.ι).obj A)
      (e : (extensionAlgebra U.ι A G φ).right.obj.obj (op U)),
      AlgebraSheaf.IsQuasicoherent G ∧ AlgebraSheaf.IsFiniteType G ∧
        (extensionAlgebra U.ι A G φ).IsQuasicoherent ∧
        (extensionProjection U.ι A G φ).right.hom.app (op U) e = x := by
  have : IsAffine U.toScheme := hU
  have : QuasiCompact U.ι := inferInstance
  obtain ⟨G, φ, g, hGqc, hGft, hg⟩ :=
    exists_hom_section_of_eq_top ((algebraPullback U.ι).obj A) U.ι_preimage_self
      ((extensionUnit U.ι A).right.hom.app (op U) x)
  have := hGqc
  obtain ⟨e, he, -⟩ := exists_fst_eq_of_isPullback
    (isPullback_extensionAlgebra_sections U.ι A G φ U) x g hg.symm
  exact ⟨G, φ, e, hGqc, hGft, isQuasicoherent_extension U.ι A G φ, he⟩

/-- Faithfulness check for `exists_extensionAlgebra_section`, with every hypothesis an explicit
argument and the conclusion written out: quasi-separatedness of `X`, quasi-coherence of `A` and
affineness of `U`, and nothing else — no quasi-compactness of `X`, no Noetherian hypothesis, no
finite type hypothesis on `A`. The extension is the literal fibre product
`pullback (extensionUnit U.ι A) ((algebraPushforward U.ι).map φ)`. -/
example (_hX : QuasiSeparatedSpace ↥X) (A : AlgebraSheaf X)
    (_hA : AlgebraSheaf.IsQuasicoherent A) {U : X.Opens} (hU : IsAffineOpen U)
    (x : A.right.obj.obj (op U)) :
    ∃ (G : AlgebraSheaf U.toScheme) (φ : G ⟶ (algebraPullback U.ι).obj A)
      (e : (pullback (extensionUnit U.ι A) ((algebraPushforward U.ι).map φ)).right.obj.obj
        (op U)),
      AlgebraSheaf.IsQuasicoherent G ∧ AlgebraSheaf.IsFiniteType G ∧
        AlgebraSheaf.IsQuasicoherent
          (pullback (extensionUnit U.ι A) ((algebraPushforward U.ι).map φ)) ∧
        (pullback.fst (extensionUnit U.ι A)
          ((algebraPushforward U.ι).map φ)).right.hom.app (op U) e = x :=
  exists_extensionAlgebra_section A hU x

end Stacks.AlgebraicGeometry.AlgebraExtensionSection

end
