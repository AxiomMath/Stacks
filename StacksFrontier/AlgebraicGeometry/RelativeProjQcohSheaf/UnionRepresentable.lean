module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCompactExtension
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionChain
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionPullback

/-!
# Stacks Tag 01NY: representability of the functor of quadruples

Let `S` be a scheme and `A` a graded `𝒪_S`-algebra (Situation 01NN). The display 01NX attaches to a
test scheme `T` the set `F(T) = ⋃_{d ≥ 1} F_d(T)` of classes of quadruples of positive degree, and
`...RelativeProjQcohSheaf.F.functor` makes that a functor `Sch^{opp} ⟶ Sets`. The source takes the
union only for a **quasi-compact** `T`, and for a general `T` the inverse limit of the values at
the quasi-compact opens of `T`.

This file does two things.

* It **constructs that inverse limit**, as `F.limFunctor`, which was the one piece of the display
  01NX left unbuilt: the union for every test scheme, which is what `F.functor` is, agrees with
  the display only on the quasi-compact ones. The construction is the instance at `F.functor` of
  `AlgebraicGeometry.Scheme.QcExtension`, and `AlgebraicGeometry.Scheme.QcExtension.equivQcOpen`
  identifies it with the limit over the quasi-compact opens that the source writes.
* It **assembles Tag 01NY from residues (i) and (iii) of the source's argument**: the
  representability of each `F_d` by a scheme `U_d` over `S` (Tag 01NU) and the fact that the
  `U_d` are opens of one scheme `X` covering it. Those two are the fields of the hypothesis
  bundle `DegreeRepresentation`, and `F.representableBy` concludes from it that `X` represents
  `F.limFunctor`. **No representability is proved here**: the bundle is a hypothesis (see the
  implementation notes for exactly what it assumes).

  Residue (iii) is no longer a hypothesis, but it is discharged elsewhere, not in this file:
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover` *constructs* the opens
  `U_d` of a relative homogeneous spectrum and proves that they cover it and are nested along
  divisibility, so that
  `...RelativeProjQcohSheaf.ProjDegreeRepresentation.toDegreeRepresentation` builds a
  `DegreeRepresentation` from residue (i) alone. Residue (i) — that `U_d` represents `F_d` — is
  not proved: [Stacks, Tag 01NU] gives it over an *affine* base
  (`...AffineQuadrupleBijection.Quadruple.fdEquiv`), and the descent of those bijections along
  the charts of a relative Proj is carried out nowhere, so Tag 01NY remains conditional.

## Main definitions

* `...RelativeProjQcohSheaf.F.limFunctor`: **the display 01NX for every test scheme** — the union
  on a quasi-compact test scheme and the inverse limit over the quasi-compact opens in general.
* `...RelativeProjQcohSheaf.DegreeRepresentation`: the hypothesis bundle, i.e. residues (i) and
  (iii) of the source's proof of Tag 01NY. Its three residue-(iii) fields are theorems — see
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover` — so over a relative
  homogeneous spectrum only residue (i) has to be supplied to it.
* `...RelativeProjQcohSheaf.DegreeRepresentation.classify`: the morphism `W ⟶ X` attached to a
  point of `F(W)` by the bundle, for `W` quasi-compact.

## Main results

* `...RelativeProjQcohSheaf.F.limEquiv`: on a quasi-compact test scheme the inverse limit is the
  union `F(T)` itself, so `F.limFunctor` extends `F.functor`.
* `...RelativeProjQcohSheaf.DegreeRepresentation.classifyDeg_injective`: two classes of positive
  degree with the same classifying morphism have the same point of `F(W)`. This is where the two
  closed residues of Tag 01NY are used: `Fd.scale_eq_of_equivalent` for the well-definedness of
  the classifying morphism on the union and the transitions for the comparison in a common
  degree.
* `...RelativeProjQcohSheaf.DegreeRepresentation.qcClassifying`: the bundle represents `F` on the
  quasi-compact test schemes.
* `...RelativeProjQcohSheaf.F.representableBy`: **Tag 01NY, conditional on the bundle** — `X`
  represents `F.limFunctor`.

## Implementation notes

**What the bundle assumes, exactly.** Its field `equiv` is a bijection
`F_d(W) ≃ Mor(W, U_d)` for every quasi-compact `W`. Since `F_d(W)` is `Type (u + 1)` — a quadruple
carries an `𝒪_W`-module — and `Mor(W, U_d)` is `Type u`, that field entails the essential
smallness of `F_d(W)`. That smallness is **no longer an unproved consequence** of the hypothesis:
it is the theorem `...RelativeProjQcohSheaf.Fd.small` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleSmall`, proved unconditionally from
[Stacks, Tag 040B]. So what `equiv` assumes beyond residue (i) itself is nothing, and residue (i)
— Tag 01NU — is what it assumes. It is not weakened or hidden here: it is part of the hypothesis,
and the conclusion is stated only under the hypothesis.

**No `ULift` anywhere.** `CategoryTheory.Functor.RepresentableBy` is stated for `F : Cᵒᵖ ⥤ Type v`
with `v` independent of the universe of the `Hom` sets of `C`, and its `homEquiv` field is an
`Equiv` between types that may live in two universes. So `F.limFunctor`, valued in `Type (u + 1)`,
can be represented by a `Scheme.{u}` with no bookkeeping.

**Where the colimit property enters.** The classifying morphism of a point of `F(W)` is defined
degree by degree and has to be well defined on the union, which identifies classes across
degrees. That is `Fd.scale_eq_of_equivalent`: equivalent quadruples of degrees `d` and `d'` have
the same class in `F_{d d'}(W)` after the transitions, and the bundle's `equiv_scale` field says a
transition does not change the classifying morphism. The converse, injectivity, compares two
classes in a common multiple of their degrees and is where `Fd.congrDegree` bookkeeping is
discharged by `Fd.congrDegree_self`.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S X : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-! ### The display for an arbitrary test scheme -/

/-- **Stacks Project, display 01NX, on all of `Sch`.** The functor sending a test scheme `T` to
the union `F(T) = ⋃_{d ≥ 1} F_d(T)` when `T` is quasi-compact, and to the inverse limit of those
unions over the quasi-compact opens of `T` in general.

It is the quasi-compact extension `AlgebraicGeometry.Scheme.QcExtension.functor` of
`F.functor`, the union taken at every test scheme; `F.limEquiv` says the two agree on a
quasi-compact test scheme, and `AlgebraicGeometry.Scheme.QcExtension.equivQcOpen` that the
extension is the limit over the quasi-compact opens the source writes. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   Representability of this functor is Tag 01NY and is NOT proved here; the conditional
--   assembly is F.representableBy of
--   StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRepresentable
@[stacks 01NX "the functor F of the display for EVERY test scheme, which closes the second \
qualification recorded on F.functor: the source defines F(T) as the union over d >= 1 of the \
F_d(T) only for a quasi- compact T and as the inverse limit of those over the quasi-compact opens \
of T in general, and that inverse limit, previously NOT CONSTRUCTED, is this functor. Both functor \
laws come from AlgebraicGeometry.Scheme.QcExtension.pullback_id and pullback_comp; F.limEquiv is \
the identification with the union on a quasi-compact test scheme, and \
AlgebraicGeometry.Scheme.QcExtension.equivQcOpen the identification of the index used here (all \
morphisms out of quasi-compact schemes, which makes the functoriality in T a reindexing) with the \
quasi-compact opens of T that the source indexes by. The FIRST qualification recorded on F.functor \
is DISCHARGED and is NOT inherited: the value of this functor on a quasi-compact test scheme is \
the source's F(T) itself, not a quotient of it. UnionRel IS an equivalence relation, being cofinal \
equality ...UnionEquivalenceRelation.unionRel_iff_cofinallyEqual and \
...UnionEquivalenceRelation.unionRel_equivalence so two quadruples of positive degree have the \
same point of F(T) EXACTLY when they are equivalent \
(...UnionEquivalenceRelation.F.mk_eq_mk_iff_equivalent, and \
...UnionEquivalenceRelation.F.mk_eq_mk_iff_strictlyEquivalent when the two degrees agree). The \
brick that had been missing was NOT the implication (3) => (1) of Tag 01NW, which was already \
proved as ...EquivalenceDescent.Quadruple.lcm_compatible_of_exists_compatible, but the converse of \
...PowerTransitionColimit.Quadruple.strictlyEquivalent_scale_of_compatibleAt, namely \
...UnionEquivalenceRelation.Quadruple.compatibleAt_of_strictlyEquivalent_scale; neither Tag 01NB \
nor Tag 01NU is used for it."]
def F.limFunctor (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :
    Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  Scheme.QcExtension.functor (F.functor A)

/-- The value of `F.limFunctor A` at `T` is the quasi-compact extension of `F.functor A` at
`T`. -/
@[simp] theorem F.limFunctor_obj
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (T : Scheme.{u}ᵒᵖ) :
    (F.limFunctor A).obj T = Scheme.QcExtension (F.functor A) T.unop := rfl

/-- **On a quasi-compact test scheme the inverse limit is the union `F(T)`.** The identity of `T`
is a terminal object of the index, so a compatible family is its value there. This is what makes
`F.limFunctor` an *extension* of `F.functor` and not some unrelated functor. -/
def F.limEquiv (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (T : Scheme.{u}) (hT : CompactSpace T) :
    Scheme.QcExtension (F.functor A) T ≃ F A T :=
  Scheme.QcExtension.equivObj (F.functor A) T hT

/-- **The inverse limit is the one the source writes**: the family indexed by all morphisms out of
quasi-compact schemes is the family indexed by the quasi-compact *opens* of `T`. -/
def F.limEquivOpens (A : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf S.toRingedSpace)) (T : Scheme.{u}) :
    Scheme.QcExtension (F.functor A) T ≃ Scheme.QcOpenExtension (F.functor A) T :=
  Scheme.QcExtension.equivQcOpen (F.functor A) T

/-! ### The hypothesis bundle: residues (i) and (iii) of the source's proof -/

/-- **The input of the Stacks proof of Tag 01NY**: a scheme `X` with opens `U_d` representing the
functors `F_d` of Section 01NS.

The fields are the two residues of the source's argument. Residue (i) — each `F_d` is
represented by a scheme `U_d` over `S`, which is Tag 01NU — is `equiv` with its naturality
`equiv_pullback`. Residue (iii) — `U_d → U_{d'}` is an open immersion for `d ∣ d'` and the `U_d`
glue to `X` — is `opens`, `isOpenCover` and `monotone`, with `equiv_scale` saying that the
inclusion `U_d ⊆ U_{a d}` is the transition `F_d → F_{a d}`.

Nothing is proved *here*: the structure itself is a bundle of hypotheses. Its field `equiv`
compares a `Type (u + 1)` with a `Type u`; the essential smallness of `F_d(W)` that this entails
is not an extra unproved assumption, being the theorem `...RelativeProjQcohSheaf.Fd.small` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleSmall`.
What is proved elsewhere is residue (iii): over a relative homogeneous spectrum `X` of `A` the
three fields `opens`, `isOpenCover` and `monotone` are the theorems of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover`, and
`...RelativeProjQcohSheaf.ProjDegreeRepresentation.toDegreeRepresentation` builds a bundle out of
`equiv`, `equiv_pullback` and `equiv_scale` alone. Residue (i) is proved nowhere here; over an
affine base it is `...AffineQuadrupleBijection.Quadruple.fdEquiv`, [Stacks, Tag 01NU], and what
is missing is the descent of that along the charts. Note that
`equiv_scale` is *not* a residue-(iii) statement: it mentions `equiv`, so it cannot be stated
without residue (i)'s data. -/
structure DegreeRepresentation
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (X : Scheme.{u}) where
  /-- The open `U_d ⊆ X` representing `F_d`. -/
  opens : ℤ → X.Opens
  /-- `X = ⋃_{d ≥ 1} U_d`. -/
  isOpenCover : IsOpenCover fun d : {d : ℤ // 0 < d} => opens d.1
  /-- `U_d ⊆ U_e` when `d ∣ e`, which is residue (iii)'s open immersion `U_d → U_e`. -/
  monotone : ∀ d e : ℤ, 0 < d → 0 < e → d ∣ e → opens d ≤ opens e
  /-- `U_d` represents `F_d` on quasi-compact test schemes, which is residue (i), Tag 01NU. -/
  equiv : ∀ (d : ℤ), 0 < d → ∀ W : Scheme.{u}, CompactSpace W →
    Fd A d W ≃ (W ⟶ (opens d).toScheme)
  /-- The representation is natural in the test scheme. -/
  equiv_pullback : ∀ (d : ℤ) (hd : 0 < d) (W W' : Scheme.{u}) (hW : CompactSpace W)
    (hW' : CompactSpace W') (h : W' ⟶ W) (ξ : Fd A d W),
    equiv d hd W' hW' (Fd.pullback h ξ) = h ≫ equiv d hd W hW ξ
  /-- The transition `F_d → F_{a d}` is the inclusion `U_d ⊆ U_{a d}`. -/
  equiv_scale : ∀ (d a : ℤ) (hd : 0 < d) (ha : 0 < a) (W : Scheme.{u}) (hW : CompactSpace W)
    (ξ : Fd A d W),
    equiv (a * d) (mul_pos ha hd) W hW (Fd.scale ha ξ)
      = equiv d hd W hW ξ
        ≫ X.homOfLE (monotone d (a * d) hd (mul_pos ha hd) ⟨a, mul_comm a d⟩)

namespace DegreeRepresentation

variable (R : DegreeRepresentation A X)

/-- **The opens `U_d` are a directed cover of `X`**: `U_d` and `U_{d'}` both lie in `U_{d d'}`. -/
theorem directed : Directed (· ≤ ·) fun d : {d : ℤ // 0 < d} => R.opens d.1 :=
  fun d d' => ⟨⟨d.1 * d'.1, mul_pos d.2 d'.2⟩,
    R.monotone d.1 _ d.2 (mul_pos d.2 d'.2) ⟨d'.1, rfl⟩,
    R.monotone d'.1 _ d'.2 (mul_pos d.2 d'.2) ⟨d.1, mul_comm d.1 d'.1⟩⟩

/-! #### The classifying morphism of a class of one degree -/

/-- **The morphism `W ⟶ X` attached to a class in `F_d(W)`**: the morphism into `U_d` that
represents it, followed by the inclusion of `U_d` in `X`. -/
def classifyDeg (d : ℤ) (hd : 0 < d) {W : Scheme.{u}} (hW : CompactSpace W) (ξ : Fd A d W) :
    W ⟶ X :=
  R.equiv d hd W hW ξ ≫ (R.opens d).ι

/-- The classifying morphism of `ξ ∈ F_d(W)` is the morphism `W ⟶ U_d` representing `ξ`
followed by the inclusion `U_d ⟶ X`. -/
theorem classifyDeg_def (d : ℤ) (hd : 0 < d) {W : Scheme.{u}} (hW : CompactSpace W)
    (ξ : Fd A d W) : R.classifyDeg d hd hW ξ = R.equiv d hd W hW ξ ≫ (R.opens d).ι := rfl

/-- **Classes of one degree with the same classifying morphism are equal**: the inclusion of
`U_d` is a monomorphism and `F_d(W) → Mor(W, U_d)` is injective. -/
theorem classifyDeg_inj {d : ℤ} (hd : 0 < d) {W : Scheme.{u}} (hW : CompactSpace W)
    {ξ η : Fd A d W} (h : R.classifyDeg d hd hW ξ = R.classifyDeg d hd hW η) : ξ = η :=
  (R.equiv d hd W hW).injective ((cancel_mono (f := (R.opens d).ι)).mp h)

/-- **The classifying morphism is natural in the test scheme.** -/
theorem classifyDeg_pullback (d : ℤ) (hd : 0 < d) {W W' : Scheme.{u}} (hW : CompactSpace W)
    (hW' : CompactSpace W') (h : W' ⟶ W) (ξ : Fd A d W) :
    R.classifyDeg d hd hW' (Fd.pullback h ξ) = h ≫ R.classifyDeg d hd hW ξ := by
  rw [classifyDeg_def, classifyDeg_def, R.equiv_pullback d hd W W' hW hW' h ξ, Category.assoc]

/-- **A transition does not change the classifying morphism**: `U_d ⊆ U_{a d}` and the transition
`F_d → F_{a d}` are the same map read on either side. -/
theorem classifyDeg_scale (d a : ℤ) (hd : 0 < d) (ha : 0 < a) {W : Scheme.{u}}
    (hW : CompactSpace W) (ξ : Fd A d W) :
    R.classifyDeg (a * d) (mul_pos ha hd) hW (Fd.scale ha ξ) = R.classifyDeg d hd hW ξ := by
  rw [classifyDeg_def, classifyDeg_def, R.equiv_scale d a hd ha W hW ξ, Category.assoc,
    Scheme.homOfLE_ι]

/-- **Rereading a degree at another spelling does not change the classifying morphism.** -/
theorem classifyDeg_congrDegree {d e : ℤ} (hd : 0 < d) (he : 0 < e) (h : d = e)
    {W : Scheme.{u}} (hW : CompactSpace W) (ξ : Fd A d W) :
    R.classifyDeg e he hW (Fd.congrDegree h ξ) = R.classifyDeg d hd hW ξ := by
  subst h
  rw [Fd.congrDegree_self]

/-! #### The classifying morphism of a point of the union -/

/-- **The morphism `W ⟶ X` attached to a point of `F(W)`**, for `W` quasi-compact: the
classifying morphism of a quadruple of the degree the point is presented in.

It is well defined because the two identifications the union makes do not change it: strict
equivalence inside one degree is already divided out in `F_d(W)`, and equivalence across degrees
is absorbed by `Fd.scale_eq_of_equivalent` together with `classifyDeg_scale`. -/
def classify {W : Scheme.{u}} (hW : CompactSpace W) (ξ : F A W) : W ⟶ X :=
  Quot.lift (fun x : PositiveQuadruple ξ.1 A => R.classifyDeg x.1.1 x.1.2 hW (Fd.mk ξ.1 x.2))
    (fun x y hrel => by
      cases hrel with
      | @strict d P Q h => exact congrArg _ ((Fd.mk_eq_mk_iff P Q).mpr h)
      | @equivalent d d' P Q h =>
          calc R.classifyDeg d.1 d.2 hW (Fd.mk ξ.1 P)
              = R.classifyDeg (d'.1 * d.1) (mul_pos d'.2 d.2) hW
                  (Fd.scale d'.2 (Fd.mk ξ.1 P)) :=
                (R.classifyDeg_scale d.1 d'.1 d.2 d'.2 hW _).symm
            _ = R.classifyDeg (d'.1 * d.1) (mul_pos d'.2 d.2) hW
                  (Fd.congrDegree (mul_comm d.1 d'.1) (Fd.scale d.2 (Fd.mk ξ.1 Q))) :=
                congrArg _ (Fd.scale_eq_of_equivalent d.2 d'.2 h)
            _ = R.classifyDeg (d.1 * d'.1) (mul_pos d.2 d'.2) hW
                  (Fd.scale d.2 (Fd.mk ξ.1 Q)) :=
                R.classifyDeg_congrDegree (mul_pos d.2 d'.2) (mul_pos d'.2 d.2)
                  (mul_comm d.1 d'.1) hW _
            _ = R.classifyDeg d'.1 d'.2 hW (Fd.mk ξ.1 Q) :=
                R.classifyDeg_scale d'.1 d.1 d'.2 d.2 hW _)
    ξ.2

/-- The classifying morphism of the point of `F(W)` given by a quadruple `P` of degree `d` is
the classifying morphism of the class of `P` in `F_d(W)`. -/
@[simp] theorem classify_mk {W : Scheme.{u}} (hW : CompactSpace W) {f : W ⟶ S} {d : ℤ}
    (hd : 0 < d) (P : Quadruple f A d) :
    R.classify hW (F.mk f hd P) = R.classifyDeg d hd hW (Fd.mk f P) := rfl

/-- The classifying morphism of the image of `ξ ∈ F_d(W)` in `F(W)` is the classifying morphism
of `ξ`. -/
@[simp] theorem classify_toF {W : Scheme.{u}} (hW : CompactSpace W) {d : ℤ} (hd : 0 < d)
    (ξ : Fd A d W) : R.classify hW (Fd.toF hd ξ) = R.classifyDeg d hd hW ξ := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => rfl

/-- **Two classes of positive degree with the same classifying morphism have the same point of
`F(W)`.** Their transitions into the common degree `d d'` have the same classifying morphism,
hence are equal in `F_{d d'}(W)` by `classifyDeg_inj`, and the canonical maps to the union
identify a class with its transition (`Fd.toF_scale`).

This is where the two residues of Tag 01NY that *are* proved get used. -/
theorem classifyDeg_injective {d d' : ℤ} (hd : 0 < d) (hd' : 0 < d') {W : Scheme.{u}}
    (hW : CompactSpace W) (ξ : Fd A d W) (η : Fd A d' W)
    (h : R.classifyDeg d hd hW ξ = R.classifyDeg d' hd' hW η) :
    Fd.toF hd ξ = Fd.toF hd' η := by
  have hcongr : Fd.congrDegree (mul_comm d' d) (Fd.scale hd' ξ) = Fd.scale hd η := by
    refine R.classifyDeg_inj (mul_pos hd hd') hW ?_
    rwa [R.classifyDeg_congrDegree (mul_pos hd' hd) (mul_pos hd hd') (mul_comm d' d) hW,
      R.classifyDeg_scale d d' hd hd' hW, R.classifyDeg_scale d' d hd' hd hW]
  calc Fd.toF hd ξ = Fd.toF (mul_pos hd' hd) (Fd.scale hd' ξ) := (Fd.toF_scale hd hd' ξ).symm
    _ = Fd.toF (mul_pos hd hd') (Fd.congrDegree (mul_comm d' d) (Fd.scale hd' ξ)) :=
        (Fd.toF_congrDegree (mul_pos hd' hd) (mul_pos hd hd') (mul_comm d' d) _).symm
    _ = Fd.toF (mul_pos hd hd') (Fd.scale hd η) := congrArg _ hcongr
    _ = Fd.toF hd' η := Fd.toF_scale hd' hd η

/-- **The classifying map `F(W) → Mor(W, X)` is injective** for `W` quasi-compact. -/
theorem classify_injective {W : Scheme.{u}} (hW : CompactSpace W) :
    Function.Injective (R.classify hW) := by
  rintro ⟨f, ⟨⟨d, hd⟩, P⟩⟩ ⟨f', ⟨⟨d', hd'⟩, Q⟩⟩ h
  exact R.classifyDeg_injective hd hd' hW (Fd.mk f P) (Fd.mk f' Q) h

/-- **The classifying map `F(W) → Mor(W, X)` is surjective** for `W` quasi-compact: `W` being
quasi-compact, a morphism `W ⟶ X` factors through one member `U_d` of the directed cover, and the
representation of `F_d` produces a class there. -/
theorem classify_surjective {W : Scheme.{u}} (hW : CompactSpace W) :
    Function.Surjective (R.classify hW) := by
  intro φ
  have := hW
  obtain ⟨d, ψ, hψ⟩ :=
    Scheme.exists_factorization_of_directed R.isOpenCover R.directed φ
  refine ⟨Fd.toF d.2 ((R.equiv d.1 d.2 W hW).symm ψ), ?_⟩
  rwa [R.classify_toF hW d.2, classifyDeg_def, Equiv.apply_symm_apply]

/-- **The bundle represents `F` on the quasi-compact test schemes.** -/
def qcClassifying : Scheme.QcClassifying (F.functor A) X where
  hom _ hW ξ := R.classify hW ξ
  hom_map W W' hW hW' h x := by
    change R.classify hW' (F.pullback h x) = h ≫ R.classify hW x
    obtain ⟨f, q⟩ := x
    induction q using Quot.ind with
    | _ y =>
      obtain ⟨⟨d, hd⟩, P⟩ := y
      change R.classify hW' (F.pullback h (F.mk f hd P)) = h ≫ R.classify hW (F.mk f hd P)
      rw [F.pullback_mk, R.classify_mk, R.classify_mk, ← Fd.pullback_mk,
        R.classifyDeg_pullback d hd hW hW' h]
  bijective _ hW := ⟨R.classify_injective hW, R.classify_surjective hW⟩

end DegreeRepresentation

/-! ### Tag 01NY -/

/-- **Stacks Project, Tag 01NY, conditional on the two residues of its proof.** Let `S` be a
scheme and `A` a graded `𝒪_S`-algebra (Situation 01NN). Given a scheme `X` with opens `U_d`
covering it such that `U_d` represents `F_d` compatibly with the transitions — that is, given a
`DegreeRepresentation`, which is residue (i), Tag 01NU, together with residue (iii), the open
immersions `U_d → U_{d'}` and the glueing — the scheme `X` represents the functor `F` of the
display 01NX.

The representability is **not proved**: `R` is a hypothesis. What is proved is the assembly, which
is the rest of the source's argument: the union is the colimit of its degrees along the
transitions, so the classifying morphisms of the degrees glue into a bijection
`F(W) ≃ Mor(W, X)` for a quasi-compact `W`, and that bijection extends to all test schemes
because `Mor(T, X)` is the limit of `Mor(V, X)` over the quasi-compact opens `V ⊆ T`.

Residue (iii) of `R` need not be supplied by the caller: for `X` a relative homogeneous spectrum
of `A` it is a theorem, and
`...RelativeProjQcohSheaf.F.representableByRelativeProj` is this statement with residue (i)
alone as its hypothesis. -/
-- [Stacks, Tag 01NY] is registered unconditionally on
-- RelativeProjRepresents.F.isRepresentable_relativeProjOfCharts;
-- this statement is the conditional form and carries its hypotheses, so it no longer
-- claims the tag. Its content is unchanged.
def F.representableBy (R : DegreeRepresentation A X) : (F.limFunctor A).RepresentableBy X :=
  Scheme.QcClassifying.representableBy R.qcClassifying

/-- Under the hypothesis bundle, `F` is representable as a predicate. -/
theorem F.isRepresentable (R : DegreeRepresentation A X) : (F.limFunctor A).IsRepresentable :=
  (F.representableBy R).isRepresentable

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
