module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Theta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegMultiplicative

/-!
# The twists on the relative Proj of an algebraic space, over the scheme points of the base

In Situation 0849 let `X` be an algebraic space over a scheme `S`, let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra and let `π : P = Proj_X(𝒜) ⟶ X` be its relative homogeneous spectrum of
Stacks 084C.  Stacks 084D asserts three things:

1. `P` carries a quasi-coherent sheaf of `ℤ`-graded `𝒪_P`-algebras `⨁_{n ∈ ℤ} 𝒪_P(n)` — pieces,
   multiplication and unit;
2. there is a canonical homomorphism of graded algebras `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)`;
3. the base change of (1) and (2) to any scheme over `X` agrees with Constructions, Stacks 01NR.

**This file delivers the third assertion, and with it (1) and (2) after base change, with no
hypothesis whatsoever.**  The relative Proj of an algebraic space is presented here through its
base changes to the scheme points of the base, by
`AlgebraicGeometry.Space.RelativeProjPoints` — Stacks 084B's second assertion as data, and the
substrate on which Stacks 085D, 085F and 085G are formalized.  That structure supplies, at every
object `T` of the site and every `T`-point `f` of `X`, a quasi-coherent graded algebra
`d.algebra T f` on the scheme of `T` — the restriction `f^*𝒜` — and an object `d.fibre T f` of the
site whose scheme is `Proj_T(f^*𝒜)` and which the cartesian square `d.isPullback T f` identifies
with `T ×_X P`.  So the base change of `P` to the scheme point `f` *is* a scheme-level relative
Proj, and Stacks 01NR applies to it on the nose.

The point of the file is that this costs nothing: Stacks 01NR is available in this library in its
unconditional form, `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, which
produces the whole twist datum of a quasi-coherent graded algebra on an arbitrary scheme with no
hypothesis beyond the algebra itself.  Applying it to `d.algebra T f` gives the graded algebra
with its multiplication and unit, the quasi-coherence of every homogeneous piece, and the
homogeneous-section map `ψ` with its unit and product laws — all three clauses of Stacks 084D,
read after base change to the scheme point.  No module data has to be added to
`AlgebraicGeometry.Space.RelativeProjPoints` to obtain them.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.pointTwistData` is Stacks 01NR at a scheme point of
  the base: the twist datum of the relative Proj of `f^*𝒜`.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointTwistAlgebra` is
  `⨁_{n ∈ ℤ} 𝒪_{Proj_T(f^*𝒜)}(n)` as a sheaf of `ℤ`-graded algebras, whose `n`-th homogeneous
  piece is the twist `AlgebraicGeometry.Space.RelativeProjPoints.pointTwist` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjFunctoriality.lean`
  (`…pointTwistAlgebra_piece`); `…pointTwistMul` and `…pointTwistOne` are its multiplication and
  its unit.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointPsi` is `ψ` at a scheme point of the base, in
  the adjoint form `𝒜_n|_T ⟶ (π_T)_*𝒪_{Proj_T(f^*𝒜)}(n)` that Stacks 01NR produces it in.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointPsiHom` is the same `ψ` as a homomorphism of
  sheaves of `ℤ`-graded algebras `π_T^*(f^*𝒜) ⟶ ⨁_{n ∈ ℤ} 𝒪_{Proj_T(f^*𝒜)}(n)`, the form in
  which the source states it.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointTwistTheta` is Stacks 01O3's `θ` at a scheme
  point: the identification of the inverse image of the twists along a further base change
  `g : Z ⟶ T` with the twists of `Proj_Z(g^*f^*𝒜)`, as `ℤ`-graded algebras.
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreTwistAlgebra` is the same graded algebra read
  on the scheme of the object
  `d.fibre T f` of the site, that is on `T ×_X P` itself, through the identification
  `d.fibreIso T f` of Stacks 084B.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.isQuasicoherent_pointTwist`: every homogeneous
  twist is quasi-coherent.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointPsi_one` and
  `AlgebraicGeometry.Space.RelativeProjPoints.pointPsi_mul`: `ψ` carries the unit of `f^*𝒜` to
  the unit of the twists and is multiplicative, that is, it is a homomorphism of graded algebras.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointTwistMul_comm`: the multiplication of the
  twists is commutative.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointPsi_chart`: under the chart identifications of
  Stacks 01NR, `ψ` is the absolute homogeneous-section map of Stacks 01MP.  This is what pins
  `ψ` down to the canonical one rather than an arbitrary graded-algebra map.
* `AlgebraicGeometry.Space.RelativeProjPoints.basePsi_pointTwistTheta`: `θ` is compatible with
  `ψ` — the base change of `ψ` along a further `g : Z ⟶ T`, followed by `θ`, is the `ψ` of
  Stacks 01NR for `Proj_Z(g^*f^*𝒜)`.  So the whole datum of Stacks 084D at a scheme point is
  carried to the datum of Stacks 01NR by further base change.
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreTwistAlgebra_piece`: its pieces are the twists
  `…fibreTwist` on `T ×_X P`, the inverse images of the twists on `Proj_T(f^*𝒜)` along
  `d.fibreIso T f`.

## Implementation notes

**Nothing here is conditional.**
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` is total, so
`pointTwistData` is a function of the presentation alone, and every declaration below is proved
with no hypothesis beyond the presentation.

**Why the twists are stated on `Proj_T(f^*𝒜)` and not on `d.fibre T f`.**  The two schemes are
isomorphic by the field `d.fibreIso T f`, and the graded algebra transports along that
isomorphism by inverse image — that is `fibreTwistAlgebra`, and it is cheap.  What does not
transport as cheaply is `ψ`: its target is a direct image along the structure morphism of the
relative Proj, and `d.fibreHom_comp T f` factors the structure morphism of the fibre through
`d.fibreIso T f`, so transporting `ψ` means composing the pseudofunctoriality of direct images
with the counit of the inverse-image adjunction at an isomorphism.  Since the whole content is
invariant under the isomorphism, `ψ` is stated where Stacks 01NR produces it and `fibreIso` is
named in the statements that need the fibre; the transported `ψ` is not provided.

**What is *not* delivered: `𝒪_P(n)` and `ψ` as sheaves on the algebraic space `P`.**  The twists
exist here at every scheme point of the base, not as modules on the small étale site of `P`
itself.  This is not a missing proof that could be supplied on the present substrate: on it the
space-level statement is false, and what is missing is Stacks 084B.

* *Why it is false on the available substrates.*  `AlgebraicGeometry.Space.RelativeProjPoints`
  records an algebra `d.algebra T f` at each scheme point as an independent field, with no
  comparison `g^*(f^*𝒜) ≅ (f ∘ g)^*𝒜` between points and no compatibility of the squares
  `d.isPullback` with further base change.  Take `X = Spec ℝ`, `P` a conic without real points,
  `d.algebra` its anticanonical ring at the point `Spec ℝ` and `ℂ[x, y]` at the point
  `Spec ℂ` (both have the right Proj).  A module on `P` restricting to the twists at both points
  would restrict on `P_ℂ ≅ ℙ¹_ℂ` both to `𝒪(1)` and to `𝒪(2)`.  The chart substrates
  (`AlgebraicGeometry.Space.RelativeProjSheafGlueingData`,
  `AlgebraicGeometry.Space.RelativeProjSituationChart`) fail in the same way: the identification
  `P ×_X U ≅ Proj_U(𝒜|_U)` is an arbitrary isomorphism, so with `𝒜 = ℝ[x, y]` and
  `U = Spec ℂ` the conic is admissible as `P`, and it has no line bundle of degree one.
* *What is missing: Stacks 084B.*  The relative Proj `Proj_X(𝒜)` is not constructed from `𝒜` in
  this library.  Constructing it, with the canonical isomorphisms
  `Proj_Z(g^*𝒜) = Z ×_X Proj_X(𝒜)` compatible with further base change, is exactly what pins
  `P` to `𝒜`.  Given that, the source's descent goes through with what is here:
  `pointTwistTheta` for the two projections `P_R ⇉ P_U` gives the descent isomorphism; the
  uniqueness clause of Stacks 01NR
  (`Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueAlgIso`) together with
  `basePsi_pointTwistTheta` gives the cocycle condition; and Stacks 03M3
  (`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`) descends each piece.  The
  graded restriction of `𝒜` to a chart is `AlgebraicGeometry.Space.chartSheafAlgebra`.

**Relation to Stacks 085C.**  Stacks 085C is the space-level Stacks 01O3: for `g : X' ⟶ X` a
morphism of algebraic spaces, `r : Proj_{X'}(g^*𝒜) ≅ X' ×_X Proj_X(𝒜)` together with an
isomorphism `θ` of the `ℤ`-graded algebras `⨁_d 𝒪(d)` across `r`.  Its `θ` needs exactly the
graded algebra of the present file, and at the level of scheme points its `θ` *is*
`pointTwistTheta`, which is Stacks 01O3 (`…RelativeProjBaseChangeTwist.pulledTwistIso`).

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry.ProjTwistSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
  (d : RelativeProjPoints B S hS π) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)

/-! ### Stacks 01NR at a scheme point of the base -/

/-- **Stacks 01NR at a scheme point of the base.**  The twist datum of the relative Proj of the
quasi-coherent graded algebra `f^*𝒜` that the presentation supplies at the `T`-point `f` of `X`:
the `ℤ`-graded algebra `⨁_{n ∈ ℤ} 𝒪(n)`, the identifications of its pieces with the absolute
twists on the projective-spectrum charts, and the homogeneous-section map `ψ`.

It is produced with no hypothesis beyond the algebra: `twistDataOfGradedAlgebra` is total. -/
noncomputable def pointTwistData : TwistData (d.algebra T f) :=
  twistDataOfGradedAlgebra (d.algebra T f)

/-- **Stacks 084D, clause (1), after base change to a scheme point of the base.**  The
quasi-coherent sheaf of `ℤ`-graded algebras `⨁_{n ∈ ℤ} 𝒪_{Proj_T(f^*𝒜)}(n)` on the base change
`T ×_X Proj_X(𝒜)` of the relative Proj along the `T`-point `f` of `X`, with its multiplication
and its unit. -/
@[stacks 084D "the base-change clause: for every scheme point f : T -> X of the base, the sheaf \
of Z-graded algebras (+)_{n in Z} O(n) -- homogeneous pieces, multiplication and unit, which are \
the three fields of the type -- on the base change Proj_T(f^*A) of the relative Proj, which \
d.fibreIso identifies with the scheme of T x_X Proj_X(A). It is Tag 01NR's graded algebra there, \
which is what the tag asks the base change to agree with. Quasi-coherence of the pieces is NOT \
part of this type; it is isQuasicoherent_pointTwist below. The sheaf on Proj_X(A) itself is NOT \
produced here"]
noncomputable def pointTwistAlgebra :
    SchemeGradedAlgebra (relativeProj (d.algebra T f)).scheme :=
  (d.pointTwistData T f).algebra

/-- The `n`-th homogeneous piece of `pointTwistAlgebra` is the twist
`AlgebraicGeometry.Space.RelativeProjPoints.pointTwist` at the scheme point. -/
theorem pointTwistAlgebra_piece (n : ℤ) : (d.pointTwistAlgebra T f).piece n = d.pointTwist T f n :=
  rfl

/-- **Stacks 084D, quasi-coherence of the twists after base change to a scheme point.** -/
@[stacks 084D "the base-change clause, quasi-coherence half: every homogeneous twist O(n) on the \
base change Proj_T(f^*A) of the relative Proj along a scheme point f : T -> X of the base is a \
quasi-coherent module"]
theorem isQuasicoherent_pointTwist (n : ℤ) : (d.pointTwist T f n).IsQuasicoherent :=
  (d.pointTwistData T f).isQuasicoherent n

/-- The multiplication `𝒪(i) × 𝒪(j) ⟶ 𝒪(i + j)` of the twists at a scheme point of the base. -/
noncomputable def pointTwistMul (i j : ℤ) :
    (d.pointTwist T f i).BilinearMap (d.pointTwist T f j) (d.pointTwist T f (i + j)) :=
  (d.pointTwistAlgebra T f).mul i j

/-- The unit of the twists at a scheme point of the base, a global section of `𝒪(0)`. -/
noncomputable def pointTwistOne : (d.pointTwist T f 0).sections :=
  (d.pointTwistAlgebra T f).one

/-- The multiplication of the twists is commutative. -/
theorem pointTwistMul_comm (i j : ℤ) (V : (relativeProj (d.algebra T f)).scheme.Opensᵒᵖ)
    (a : (d.pointTwist T f i).val.obj V) (b : (d.pointTwist T f j).val.obj V) :
    HEq ((d.pointTwistMul T f i j).app V a b) ((d.pointTwistMul T f j i).app V b a) :=
  (d.pointTwistData T f).mul_comm i j V a b

/-! ### `ψ` at a scheme point of the base -/

/-- **Stacks 084D, clause (2), after base change to a scheme point of the base.**  The canonical
homomorphism of graded algebras `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪(n)`, read at the `T`-point `f` of `X` in
the adjoint form that Stacks 01NR produces: in each degree `n ≥ 0` a map
`(f^*𝒜)_n ⟶ (π_T)_*𝒪_{Proj_T(f^*𝒜)}(n)`.

That it is a homomorphism of graded algebras is `…pointPsi_one` and `…pointPsi_mul`, and
`…pointPsi_chart` identifies it on the projective-spectrum charts with the absolute
homogeneous-section map of Stacks 01MP, which is what makes it the canonical one. -/
@[stacks 084D "the base-change clause for psi: the degreewise maps of the canonical \
homomorphism psi : pi^*A -> (+)_{n >= 0} O(n) on the base change Proj_T(f^*A) of the relative \
Proj along a scheme point f : T -> X of the base, in the adjoint form (f^*A)_n -> (pi_T)_* O(n) \
that Tag 01NR produces psi in. This declaration is the family of maps and nothing more; that it \
preserves the unit, is multiplicative, and is Tag 01MP's homogeneous-section map on the charts \
are the three companion theorems pointPsi_one, pointPsi_mul and pointPsi_chart below. psi on \
Proj_X(A) itself is NOT produced here"]
noncomputable def pointPsi (n : ℕ) :
    (d.algebra T f).piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj (d.algebra T f)).toBase).obj
        (d.pointTwist T f (n : ℤ)) :=
  (d.pointTwistData T f).ψ n

/-- **`ψ` preserves the unit.** -/
theorem pointPsi_one (U : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    ((d.pointTwistData T f).ψ 0).val.app (op U) ((d.algebra T f).one U) =
      (d.pointTwistData T f).algebra.one.eval
        (op ((relativeProj (d.algebra T f)).toBase ⁻¹ᵁ U)) :=
  (d.pointTwistData T f).ψ_one U

/-- The degree-`n + m` product of two homogeneous local sections of `f^*𝒜`, read in the degree
`((n + m : ℕ) : ℤ)` that indexes the degree-`n + m` component of `ψ`. -/
noncomputable def algebraMulNat (U : ((BigFppfOver.toScheme B S hS).obj T).Opens) (n m : ℕ)
    (a : (d.algebra T f).sectionPieces U n) (b : (d.algebra T f).sectionPieces U m) :
    Γ((d.algebra T f).piece ((n + m : ℕ) : ℤ), U) :=
  (Int.natCast_add n m).symm ▸ ((d.algebra T f).mul (n : ℤ) (m : ℤ)).app U a b

/-- **`ψ` is multiplicative.** -/
theorem pointPsi_mul (U : ((BigFppfOver.toScheme B S hS).obj T).Opens) (n m : ℕ)
    (a : (d.algebra T f).sectionPieces U n) (b : (d.algebra T f).sectionPieces U m) :
    HEq
      (((d.pointTwistData T f).ψ (n + m)).val.app (op U) (d.algebraMulNat T f U n m a b))
      (((d.pointTwistData T f).algebra.mul (n : ℤ) (m : ℤ)).app
        (op ((relativeProj (d.algebra T f)).toBase ⁻¹ᵁ U))
          (((d.pointTwistData T f).ψ n).val.app (op U) a)
          (((d.pointTwistData T f).ψ m).val.app (op U) b)) :=
  (d.pointTwistData T f).ψ_mul U n m a b

/-- **`ψ` is the absolute homogeneous-section map of Stacks 01MP on the charts.**  Under the chart
identification of Stacks 01NR over an affine open `U` of the scheme of `T`, the degree-`n`
component of `ψ` is the map `Stacks.AlgebraicGeometry.RelativeProjTwists.degreeSection` of the
graded ring of sections. -/
theorem pointPsi_chart (U : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hU : IsAffineOpen U) (n : ℕ) (a : (d.algebra T f).sectionPieces U n) :
    letI := (d.pointTwistData T f).chartData.chart_isOpenImmersion U hU
    (d.pointTwistData T f).chartData.mapSection U hU (n : ℤ) ⊤
      (degreeSection ((d.algebra T f).grading U) n
        ⟨DirectSum.of ((d.algebra T f).sectionPieces U) n a,
          (d.algebra T f).of_mem_grading U a⟩) =
      ((d.pointTwistData T f).chartData.chart_range U hU).symm ▸
        (((d.pointTwistData T f).ψ n).val.app (op U) a) :=
  (d.pointTwistData T f).ψ_chart U hU n a

/-- **Stacks 084D, clause (2), after base change to a scheme point of the base, as a
homomorphism of graded algebras.**  The canonical homomorphism

`ψ : π_T^*(f^*𝒜) ⟶ ⨁_{n ∈ ℤ} 𝒪_{Proj_T(f^*𝒜)}(n)`

of sheaves of `ℤ`-graded algebras on `Proj_T(f^*𝒜)`, where `π_T : Proj_T(f^*𝒜) ⟶ T` is the
structure morphism: the transpose across `π_T^* ⊣ (π_T)_*` of the homogeneous-section map
`AlgebraicGeometry.Space.RelativeProjPoints.pointPsi`, assembled with its multiplicativity
(`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposeHom`).  The source writes the
target as `⨁_{n ≥ 0} 𝒪(n)`; since `π_T^*(f^*𝒜)` vanishes in negative degrees the two targets
receive the same homomorphisms, and the components in degrees `n ≥ 0` are the transposes of
`pointPsi` (`…pointPsiHom_app_natCast`). -/
@[stacks 084D "the base-change clause for psi as a homomorphism of graded algebras: on the base \
change Proj_T(f^*A) of the relative Proj along a scheme point f : T -> X of the base, the \
canonical homomorphism psi : pi_T^*(f^*A) -> (+)_n O(n) of sheaves of Z-graded algebras \
(multiplicative by construction), whose degree-n components for n >= 0 are the adjoint transposes \
of pointPsi. psi on Proj_X(A) itself is NOT produced here"]
noncomputable def pointPsiHom :
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
          (relativeProj (d.algebra T f)).toBase)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra (d.algebra T f))
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct _) ⟶
      d.pointTwistAlgebra T f :=
  (d.pointTwistData T f).psiTransposeHom

/-- In a degree `n ≥ 0` the component of `ψ` is the transpose of `pointPsi` across the
adjunction `π_T^* ⊣ (π_T)_*`. -/
theorem pointPsiHom_app_natCast (n : ℕ) :
    (d.pointPsiHom T f).app (n : ℤ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (relativeProj (d.algebra T f)).toBase).homEquiv _ _).symm (d.pointPsi T f n) :=
  rfl

/-! ### Stacks 01O3 at a scheme point of the base -/

/-- **Stacks 01O3 at a scheme point of the base: the base-change isomorphism `θ`.**  For a further
morphism of schemes `g : Z ⟶ T`, the inverse image along the base-change morphism
`Proj_Z(g^*f^*𝒜) ⟶ Proj_T(f^*𝒜)` of the twists at the point `f` is the graded algebra of twists
of `Proj_Z(g^*f^*𝒜)`, as `ℤ`-graded algebras.

This is what makes the base-change clause of Stacks 084D a *compatible* family rather than a
statement at one point at a time, and it is the scheme-point case of the `θ` of Stacks 085C. -/
@[stacks 084D "the base-change clause is compatible with further base change: for g : Z -> T the \
inverse image of (+)_d O_{Proj_T(f^*A)}(d) along the base-change morphism is \
(+)_d O_{Proj_Z(g^*f^*A)}(d) as Z-graded algebras. This is Tag 01O3's theta, and it is the \
scheme-point case of the theta of Tag 085C"]
noncomputable def pointTwistTheta {Z : Scheme.{u}}
    (g : Z ⟶ (BigFppfOver.toScheme B S hS).obj T) :
    pbAlgS (baseChangeHom (d.algebra T f) g) (d.pointTwistAlgebra T f) ≅
      Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra ((d.algebra T f).pullback g) :=
  pulledTwistIso (d.algebra T f) g

/-- **The base-change clause of Stacks 084D for `ψ`, at a scheme point of the base.**  For a
further morphism of schemes `g : Z ⟶ T`, the base change along `g` of the homogeneous-section
map `ψ` of the twists at the point `f` — the morphism
`g^*(f^*𝒜)_k ⟶ (π_Z)_* h^*𝒪_{Proj_T(f^*𝒜)}(k)` adjoint to
`(f^*𝒜)_k ⟶ (π_T)_*𝒪(k) ⟶ (π_T)_* h_* h^*𝒪(k)`, where `h : Proj_Z(g^*f^*𝒜) ⟶ Proj_T(f^*𝒜)` is the
base-change morphism (`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.basePsi`) — followed
by the isomorphism `θ` of `AlgebraicGeometry.Space.RelativeProjPoints.pointTwistTheta` is the
homogeneous-section map of Stacks 01NR for `Proj_Z(g^*f^*𝒜)`.

So the isomorphism `θ` of the graded algebras of twists is compatible with `ψ`: base change
carries the whole of Stacks 084D's datum at `f` — graded algebra and `ψ` — to Stacks 01NR's datum
on `Proj_Z(g^*f^*𝒜)`.  The proof is the gluing statement
`Stacks.AlgebraicGeometry.TwistExistenceBasis.glueIso_psi` behind `θ`. -/
@[stacks 084D "the base-change clause for psi, compatible with further base change: for \
g : Z -> T the base change along g of psi at the scheme point f, followed by Tag 01O3's theta \
(pointTwistTheta), is Tag 01NR's psi for Proj_Z(g^*f^*A), degree by degree"]
theorem basePsi_pointTwistTheta {Z : Scheme.{u}} (g : Z ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (k : ℕ) :
    basePsi (relativeProj (d.algebra T f)).toBase
        (relativeProj ((d.algebra T f).pullback g)).toBase g
        (baseChangeHom (d.algebra T f) g) (baseChangeHom_comp_toBase (d.algebra T f) g)
        (d.pointPsi T f k) ≫
      (Scheme.Modules.pushforward (relativeProj ((d.algebra T f).pullback g)).toBase).map
        ((d.pointTwistTheta T f g).hom.app (k : ℤ)) =
      (twistDataOfGradedAlgebra ((d.algebra T f).pullback g)).ψ k :=
  Stacks.AlgebraicGeometry.TwistExistenceBasis.glueIso_psi (isBasis_baseChangeBasis g)
    (isAffineOpen_of_mem_baseChangeBasis g) (pulledBasisData (d.algebra T f) g)
    (Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData.ofTwistData
      (twistDataOfGradedAlgebra ((d.algebra T f).pullback g))) k

/-! ### The twists read on `T ×_X P` -/

/-- **The twists read on the base change `T ×_X P` itself.**  The object `d.fibre T f` of the site
is `T ×_X Proj_X(𝒜)` by the cartesian square `d.isPullback T f`, and `d.fibreIso T f` identifies
its scheme with `Proj_T(f^*𝒜)`; this is the graded algebra of twists transported along that
identification. -/
noncomputable def fibreTwistAlgebra :
    SchemeGradedAlgebra ((BigFppfOver.toScheme B S hS).obj (d.fibre T f)) :=
  pbAlgS (d.fibreIso T f).hom (d.pointTwistAlgebra T f)

/-- The homogeneous pieces of the twists read on `T ×_X P` are the twists
`AlgebraicGeometry.Space.RelativeProjPoints.fibreTwist` there, the inverse images of the twists on
`Proj_T(f^*𝒜)` along the identification `d.fibreIso T f` of Stacks 084B. -/
theorem fibreTwistAlgebra_piece (n : ℤ) :
    (d.fibreTwistAlgebra T f).piece n = d.fibreTwist T f n :=
  rfl

end RelativeProjPoints

end AlgebraicGeometry.Space

end
