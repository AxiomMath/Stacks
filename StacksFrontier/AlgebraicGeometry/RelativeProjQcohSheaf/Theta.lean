module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ThetaUnique
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# The comparison `θ` of a quadruple exists, and its triangle commutes

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), `d` a positive integer and
`(f : T → S, d, ℒ, ψ)` a quadruple of degree `d`. Lemma 01O1 attaches to it the `S`-morphism
`r = r_{d, ℒ, ψ}` and asserts that there is an isomorphism of `ℤ`-graded `𝒪_T`-algebras

`θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

for which `ψ` is `θ` composed with the pullback of `ψ_univ` along `r`, and that the commutativity
of that triangle determines `θ`. The last assertion is
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta`; this file proves the **existence** of `θ`
and the **commutativity** of the triangle.

## The argument

The source's own: `θ` is the comparison of the quadruple with the pullback of the universal
quadruple. Write it out.

A scheme `Y` representing the functor `F_d` of Section 01NS carries a universal element
`ξ_univ ∈ F_d(Y)`, that is, the strict equivalence class of a quadruple `(p, d, ℒ_univ, ψ_univ)`
over the structure morphism `p : Y ⟶ S` — this is `Fd.exists_universalQuadruple`, the morphism
recorded by the universal element being `p` because the representation is a representation over
`S`. For a morphism `r : T ⟶ Y` the representation turns `r` into the class of the pullback of
that quadruple, `Fd.homEquiv_eq_mk_pullback`, since the restriction maps of `F_d` *are* the
pullback of a quadruple (`...RelativeProjQcohSheaf.UnionPullback.Fd.pullback`, with its two
functor laws in `...RelativeProjQcohSheaf.UnionFunctor`). So if `r` is the morphism attached to
the class of `(f, d, ℒ, ψ)`, the two quadruples `(p, d, ℒ_univ, ψ_univ)` pulled back along `r` and
`(f, d, ℒ, ψ)` have the *same class* in `F_d(T)`, hence are strictly equivalent; and a strict
equivalence is exactly an isomorphism of the Laurent algebras carrying one `ψ` to the other
(`Quadruple.strictlyEquivalent_iff_exists_hom`). That isomorphism is `θ`, and the clause carrying
`ψ` to `ψ` is the commutativity of the triangle.

Two quadruples are compared only over a common morphism to `S`, and the two morphisms here are
`r ≫ p` and `f`; they agree, because the representation is a representation over `S`, and
`Fd.exists_laurentIso_of_mk_eq` reads the strict equivalence off the equality of classes together
with that agreement.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.universalLeg`: **the second leg of
  Lemma 01O1's triangle**, the pullback along `r` of the `ψ` of the universal quadruple, read as a
  degreewise family `f^*𝒜_{nd} ⟶ (r^*ℒ_univ)^{⊗ n}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentingProjData.InclNatural`: the
  compatibility of the carried functor `F`'s restriction maps with the pullback of quadruples.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentingProjData.degreeInclusion`: the
  morphism `Y ⟶ Proj_S(𝒜)` induced by the inclusion `F_d ⊆ F`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.exists_theta`: **`θ` exists and the
  triangle commutes.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_theta_universal`: the
  same, together with the uniqueness of `θ` among homomorphisms of graded algebras solving the
  triangle.
* `...RelativeProjQcohSheaf.RepresentingProjData.associatedMorphism_eq_comp`: the morphism
  `r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` of Lemma 01O1 factors through `Y` as the morphism attached to the
  class in `F_d(T)` followed by `degreeInclusion`.
* `...RelativeProjQcohSheaf.RepresentingProjData.exists_theta_associatedMorphism`: **Lemma 01O1
  for the associated morphism**: that factorisation, the existence of `θ`, the commutativity of
  the triangle and the uniqueness of `θ`, in one statement.

## What is carried, and what the source of `θ` is

The representation of `F_d` by a scheme over `S` is **Tag 01NV**, proved here only conditionally.
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts` has exactly the conclusion
`∃ Y, ∃ p : Y ⟶ S, ∃ e, ∀ T ξ, e.homEquiv.symm ξ ≫ p = ξ.1` that the statements below take as a
hypothesis, and is the sharpest form available: the smallness of the sets `F_d(T)` is discharged
there by `Fd.small`, so what it still carries is the Zariski sheaf property of `F_d` together with
the family of affine-local charts `c`, `hc`, `hcover` — the descent of the charts along the base,
not the affine-base representability. (`Fd.exists_representableBy_functor_over_base` is the same
conclusion with smallness also carried.) Nothing else about `Y` is assumed; in particular `Y` is
not assumed to be an open of the relative homogeneous spectrum, which is what it is in the
source.

Consequently the source of `θ` is the Laurent algebra `⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n}` of the
pullback of the universal invertible module, and the second leg of the triangle is the pullback of
the universal quadruple's own `ψ`. Identifying these with `r^*(⨁_n 𝒪_{Proj_S(𝒜)}(nd))` and with
the pullback of `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` — that is, `ℒ_univ`
with `𝒪(d)` on the degree-`d` locus, and `(r^*𝒪(d))^{⊗ n}` with `r^*𝒪(nd)` — is **not** done
here, and needs the comparison of the carried representation with the glued twists.

What that comparison would take, and what of it the repository already has, is worth stating
precisely, because the second of the two identifications is **not** missing. For a morphism
`φ : Y ⟶ U_d` into the degree-`d` open of the **absolute** `Proj` of a graded ring together with
an isomorphism `α : φ^*𝒪(d) ≅ L`,

* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` is the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)`
  in every **integer** degree, and
* `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistPowIso` is `φ^*𝒪(dn) ≅ L^{⊗ n}` in
  every integer degree, with
  `...PullbackTwistPower.tensorPowerModule_eq_laurent_piece` identifying its target with the
  degree-`n` piece of the Laurent algebra of `L` by `rfl` — the very spelling the statements
  below are graded by.

So the degreewise half of the identification exists, and so does the **multiplicativity** of
`thetaInt` in an arbitrary integer bidegree, without which the degreewise family would not be a
morphism of graded algebras: that is
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerBidegree`, extending
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerMul`, which has only the bidegrees
`(n, 0)` for an integer `n` and `(n, m)` for natural `n`, `m`.

The relative statement — the glued twists of Tag 01NR on `Proj_S(𝒜)` in place of the twists on an
absolute `Proj` — is available too. A twist datum of Tag 01NR exists on
`Proj_S(𝒜)` for every quasi-coherent graded algebra, by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`; its `d`-divisible regrading
`⨁_{n ∈ ℤ} 𝒪(nd)` and the pullback `r^*(⨁_{n ∈ ℤ} 𝒪(nd))` that is the tag's own source for `θ` are
`Stacks.AlgebraicGeometry.RelativeVeroneseTwists.twistVeronese` and `pullbackTwistVeronese` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeVeroneseTwists`, whose degree-`n` pieces are
`𝒪(nd)` and `r^*𝒪(nd)` by `rfl`; and the two facts that make the comparison a formality —
invertibility of each `𝒪(nd)` and invertibility of each multiplication
`𝒪(nd) ⊗ 𝒪(md) ⟶ 𝒪((n + m)d)` — are `...RelativeVeroneseTwists.isInvertible_twistVeronese_piece`
and `isIso_mulSheaf_twistVeronese`, both from
`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf` and
`twistData_stacksIsInvertible`, on the hypothesis that `𝒜` is generated in degree one over every
affine open of the base. An earlier note here said no form of either was available restricted to
the degree-`d` locus `...RelativeProj.RelativeProjData.degreeOpen`, which the general case needs;
both are now available there, for an arbitrary quasi-coherent graded algebra, in
`StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison`
(`...RelativeVeroneseTwists.isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen` and
`isInvertible_pullbackTwistVeronese_piece_zero`), and
`...RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` is the `θ`-assertion at the tag's own
source with no generation hypothesis.

The step one further in — the recognition statement that a sheaf of `ℤ`-graded algebras with
invertible multiplications and invertible degree-zero piece *is* the Laurent algebra of its
degree-one piece — is **proved**. Degreewise it is
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentRecognition`; multiplicativity in an
arbitrary integer bidegree is `...GradedLaurentRecognition.pieceIso_mul` and the isomorphism of
graded algebras is `...GradedLaurentRecognition.gradedIso`, both of
`StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul`. Applied to the tag's own source it
gives the comparison, as `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.laurentComparison` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison`, on the degree-one datum
`α : r^*𝒪(d) ≅ ℒ` — not removable, being `θ`'s own degree-one component — and on degree-one
generation of `𝒜`.

The step that consumes such a comparison is
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_sourceIso`: it carries both the
existence of `θ` with its triangle and the uniqueness of `θ` from the source below to any other
presentation of the source, and
`...RelativeVeroneseTwists.existsUnique_theta_of_degreeOneIso` is that step run with the
comparison above.

The compatibility `RepresentingProjData.InclNatural` of the carried functor `F` with the pullback
of quadruples is a hypothesis of the two statements about `Proj_S(𝒜)` rather than a field of
`RepresentingProjData`: adding a field would strengthen the hypothesis of the statements already
proved from that structure, and so weaken them. It is satisfiable for the same reason as the
structure's other fields — the source's `F` has the pullback of a quadruple for its restriction
maps, which is what `...RelativeProjQcohSheaf.UnionPullback.F.pullback` builds.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T T' S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### Reading a quadruple off a class in `F_d(T)` -/

/-- A class in `F_d(T)` whose recorded morphism is `f` is the class of a quadruple over `f`. -/
theorem Fd.exists_mk {f : T ⟶ S} (ξ : Fd A d T) (h : ξ.1 = f) :
    ∃ P : Quadruple f A d, ξ = Fd.mk f P := by
  obtain ⟨f₀, q⟩ := ξ
  subst h
  induction q using Quotient.ind with
  | _ P => exact ⟨P, rfl⟩

/-- Two quadruples with the same class in `F_d(T)` are over the same morphism to `S` and are
strictly equivalent, the strict equivalence being presented as an isomorphism of their Laurent
algebras carrying one `ψ` to the other.

The two maps `ψ` have the pullbacks of `𝒜_{nd}` along the two morphisms for their sources, so the
clause relating them is stated through the identification of those two pullbacks that the equality
of the morphisms gives. -/
theorem Fd.exists_laurentIso_of_mk_eq {f f' : T ⟶ S}
    (P : Quadruple f A d) (Q : Quadruple f' A d) (h : Fd.mk f P = Fd.mk f' Q) :
    ∃ hf : f = f', ∃ γ : laurent P.L ≅ laurent Q.L, ∀ n : ℤ,
      P.twisting.app n ≫ γ.hom.app n =
        eqToHom (congrArg (fun k : T ⟶ S =>
          (pullbackFunctor (ringedSpaceHom k)).obj (A.piece (n * d))) hf) ≫ Q.twisting.app n := by
  have hf : f = f' := congrArg (fun x : Fd A d T => x.1) h
  subst hf
  obtain ⟨γ, hγ⟩ :=
    (Quadruple.strictlyEquivalent_iff_exists_hom P Q).mp ((Fd.mk_eq_mk_iff P Q).mp h)
  exact ⟨rfl, γ, fun n => by simpa using hγ n⟩

/-- The canonical map `F_d(T) → F(T)` commutes with the pullback of quadruples: both sides send
the class of a quadruple to the point of its pullback. -/
theorem Fd.toF_pullback (hd : 0 < d) (g : T' ⟶ T) (ξ : Fd A d T) :
    F.pullback g (Fd.toF hd ξ) = Fd.toF hd (Fd.pullback g ξ) := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => rfl

/-! ### The universal quadruple of a representation of `F_d`, and `θ` -/

section Universal

variable {Y : Scheme.{u}} {p : Y ⟶ S} {f : T ⟶ S}

/-- A representation of `F_d` sends `r : T ⟶ Y` to the pullback along `r` of its universal
element. -/
private theorem Fd.homEquiv_eq_pullback (e : (Fd.functor A d).RepresentableBy Y) (r : T ⟶ Y) :
    e.homEquiv r = Fd.pullback r (e.homEquiv (𝟙 Y)) := by
  rw [← Category.comp_id r]
  exact e.homEquiv_comp r (𝟙 Y)

/-- **A representation of `F_d` turns a morphism `r : T ⟶ Y` into the pullback along `r` of the
universal quadruple.** This is the universal property read through the restriction maps of `F_d`,
which are the pullback of a quadruple. -/
theorem Fd.homEquiv_eq_mk_pullback (e : (Fd.functor A d).RepresentableBy Y)
    {Qu : Quadruple p A d} (hQu : e.homEquiv (𝟙 Y) = Fd.mk p Qu) (r : T ⟶ Y) :
    e.homEquiv r = Fd.mk (r ≫ p) (Qu.pullback r) := by
  rw [Fd.homEquiv_eq_pullback, hQu]
  rfl

/-- **The universal quadruple of a representation of `F_d` over `S`.** The universal element of
`F_d(Y)` is the class of a quadruple of degree `d` over the structure morphism `p : Y ⟶ S`: the
morphism it records is `p`, because the representation is a representation over `S`. -/
theorem Fd.exists_universalQuadruple (e : (Fd.functor A d).RepresentableBy Y)
    (hp : ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1) :
    ∃ Qu : Quadruple p A d, e.homEquiv (𝟙 Y) = Fd.mk p Qu := by
  refine Fd.exists_mk (e.homEquiv (𝟙 Y)) ?_
  have h := hp Y (e.homEquiv (𝟙 Y))
  rw [Equiv.symm_apply_apply, Category.id_comp] at h
  exact h.symm

namespace Quadruple

/-- **The second leg of Lemma 01O1's triangle**: the pullback along `r : T ⟶ Y` of the map `ψ` of
the universal quadruple, as a degreewise family `f^*𝒜_{nd} ⟶ (r^*ℒ_univ)^{⊗ n}`.

The pullback of the universal quadruple is a quadruple over `r ≫ p`, so the source of its `ψ` is
`(r ≫ p)^*𝒜_{nd}`; the family below is that `ψ` read on `f^*𝒜_{nd}` through the identification of
the two pullbacks that `r ≫ p = f` gives. -/
def universalLeg (Qu : Quadruple p A d) {r : T ⟶ Y} {f : T ⟶ S} (hf : r ≫ p = f) (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)) ⟶
      (laurent (Qu.pullback r).L).piece n :=
  eqToHom (congrArg (fun k : T ⟶ S =>
      (pullbackFunctor (ringedSpaceHom k)).obj (A.piece (n * d))) hf.symm) ≫
    (Qu.pullback r).twisting.app n

/-- **The comparison `θ` of Lemma 01O1 exists, and the characterising triangle commutes.** Let
`(f, d, ℒ, ψ)` be a quadruple of degree `d`, let `Y` represent `F_d` over `S`, and let
`r : T ⟶ Y` be the morphism attached to the class of the quadruple. Then there is an isomorphism

`θ : ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n} ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras with `u_n ≫ θ_n = ψ_n` in every degree, where `u` is the
pullback along `r` of the `ψ` of the universal quadruple `(p, d, ℒ_univ, ψ_univ)`.

It is the comparison of a strict equivalence: the pullback along `r` of the universal quadruple
and `(f, d, ℒ, ψ)` have the same class in `F_d(T)`, because `r` is the morphism attached to that
class and the restriction maps of `F_d` are the pullback of a quadruple. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   no RepresentingProjData is carried and no relative Proj appears, which makes this the sharpest
--   form of those two clauses in this repository. The clause that r_{d, L, psi} : T → Proj_S(A) is
--   an S-MORPHISM is `...RepresentingProjData.associatedMorphism_comp_toBase`, the factorisation
--   of r through Y is `...RepresentingProjData.associatedMorphism_eq_comp`, and the three clauses
--   in one statement about Proj_S(A) are
--   `...RepresentingProjData.exists_theta_associatedMorphism`. The uniqueness of theta is
--   `Quadruple.existsUnique_theta`. CARRIED: the representation of F_d by a scheme over S, which
--   is Tag 01NV; the hypotheses e and hp are verbatim the conclusion of
--   `Fd.exists_representableBy_functor_of_charts`, the sharpest form available, which still
--   carries the Zariski sheaf property of F_d and the affine-local charts of Tag 01NU.
--   QUALIFICATION on the source of theta: it is the Laurent algebra of the pullback along r of the
--   universal invertible module of the representation, not r^*(⨁_n O_{Proj}(nd)) for the glued
--   twists of Tag 01NR, and the second leg is the universal quadruple's own psi rather than
--   TwistData.psi; moving theta to the tag's source is
--   `Quadruple.existsUnique_theta_of_sourceIso`, which reduces that move to one comparison of
--   graded algebras, and the clause string on
--   `...RepresentingProjData.exists_theta_associatedMorphism` says which parts of that comparison
--   the repository already has.
theorem exists_theta (Q : Quadruple f A d) (e : (Fd.functor A d).RepresentableBy Y)
    (hp : ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1)
    {r : T ⟶ Y} (hr : e.homEquiv r = Fd.mk f Q) :
    ∃ (Qu : Quadruple p A d) (hf : r ≫ p = f)
      (θ : laurent (Qu.pullback r).L ≅ laurent Q.L),
      ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n := by
  obtain ⟨Qu, hQu⟩ := Fd.exists_universalQuadruple e hp
  obtain ⟨hf, γ, hγ⟩ := Fd.exists_laurentIso_of_mk_eq (Qu.pullback r) Q
    ((Fd.homEquiv_eq_mk_pullback e hQu r).symm.trans hr)
  refine ⟨Qu, hf, γ, fun n => ?_⟩
  rw [universalLeg, Category.assoc, hγ n]
  simp

/-- **Lemma 01O1's `θ` exists and is the unique solution of its triangle.** The existence and the
commutativity are `Quadruple.exists_theta`; the uniqueness among homomorphisms of graded algebras
is `Quadruple.existsUnique_theta`, applied to the source of `θ` and to the second leg of the
triangle. -/
theorem existsUnique_theta_universal (Q : Quadruple f A d)
    (e : (Fd.functor A d).RepresentableBy Y)
    (hp : ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1)
    {r : T ⟶ Y} (hr : e.homEquiv r = Fd.mk f Q) :
    ∃ (Qu : Quadruple p A d) (hf : r ≫ p = f),
      (∃ θ : laurent (Qu.pullback r).L ≅ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n) ∧
        ∃! Θ : laurent (Qu.pullback r).L ⟶ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ Θ.app n = Q.twisting.app n := by
  obtain ⟨Qu, hf, θ, hθ⟩ := Q.exists_theta e hp hr
  exact ⟨Qu, hf, ⟨θ, hθ⟩, Quadruple.existsUnique_theta Q _ (Qu.universalLeg hf) hθ⟩

end Quadruple

end Universal

/-! ### The morphism `r_{d, ℒ, ψ}` of Lemma 01O1 -/

section Representing

variable {A : SheafGradedAlgebra S}

/-- The carried functor `F` of the display 01NX has the pullback of quadruples for its restriction
maps: restricting the point of a quadruple along a morphism of test schemes gives the point of the
pullback of that quadruple.

This is a property of the carried datum `incl`, not a further datum, and it is what the source's
`F` satisfies by construction. -/
def RepresentingProjData.InclNatural (R : RepresentingProjData A) : Prop :=
  ∀ (T T' : Scheme.{u}) (g : T' ⟶ T) (ξ : F (situationAlgebra A) T),
    R.functor.map g.op (R.incl T ξ) = R.incl T' (F.pullback g ξ)

namespace RepresentingProjData

variable (R : RepresentingProjData A) {Y : Scheme.{u}}

/-- **The morphism `Y ⟶ Proj_S(𝒜)` induced by the inclusion `F_d ⊆ F`**, from a scheme `Y`
representing `F_d`: the morphism representing the point of `F(Y)` of the universal element of
`F_d(Y)`. In the source it is the open immersion of the locus of degree `d` into the relative
homogeneous spectrum. -/
def degreeInclusion (hd : 0 < d)
    (e : (Fd.functor (situationAlgebra A) d).RepresentableBy Y) : Y ⟶ (relativeProj A).scheme :=
  R.relativeProjRepresentableBy.homEquiv.symm (R.incl Y (Fd.toF hd (e.homEquiv (𝟙 Y))))

/-- **The morphism `r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` attached to a quadruple of degree `d` factors
through a scheme representing `F_d`**: it is the morphism attached to the class of the quadruple in
`F_d(T)`, followed by `degreeInclusion`.

Both morphisms represent the same point of `F(T)`: the inclusion `F_d ⊆ F` commutes with the
pullback of quadruples (`Fd.toF_pullback`), and so does the identification of `F(T)` with the
points of the carried functor (`InclNatural`). -/
theorem associatedMorphism_eq_comp (hnat : R.InclNatural) (hd : 0 < d)
    (e : (Fd.functor (situationAlgebra A) d).RepresentableBy Y)
    {f : T ⟶ S} (Q : Quadruple f (situationAlgebra A) d) {r : T ⟶ Y}
    (hr : e.homEquiv r = Fd.mk f Q) :
    R.associatedMorphism hd Q = r ≫ R.degreeInclusion hd e := by
  have h0 : Fd.pullback r (e.homEquiv (𝟙 Y)) = Fd.mk f Q :=
    (Fd.homEquiv_eq_pullback e r).symm.trans hr
  have hξ : F.pullback r (Fd.toF hd (e.homEquiv (𝟙 Y))) = F.mk f hd Q :=
    ((Fd.toF_pullback hd r (e.homEquiv (𝟙 Y))).trans
      (congrArg (Fd.toF hd) h0)).trans (Fd.toF_mk hd Q)
  have h1 : R.relativeProjRepresentableBy.homEquiv (r ≫ R.degreeInclusion hd e) =
      R.incl T (F.mk f hd Q) :=
    (R.relativeProjRepresentableBy.homEquiv_comp r (R.degreeInclusion hd e)).trans
      ((congrArg (fun z => R.functor.map r.op z)
          (Equiv.apply_symm_apply R.relativeProjRepresentableBy.homEquiv
            (R.incl Y (Fd.toF hd (e.homEquiv (𝟙 Y)))))).trans
        ((hnat Y T r (Fd.toF hd (e.homEquiv (𝟙 Y)))).trans (congrArg (R.incl T) hξ)))
  exact ((Equiv.eq_symm_apply _).mpr h1).symm

/-- **Stacks Project, Tag 01O1.** *The comparison `θ` exists and the characterising triangle
commutes.*

Let `(f : T → S, d, ℒ, ψ)` be a quadruple of positive degree and let `Y` represent the functor
`F_d` of Section 01NS over `S` — Tag 01NV, available in this repository as
`Fd.exists_representableBy_functor_over_base`. Then, with `r : T ⟶ Y` the morphism attached to the
class of the quadruple in `F_d(T)`:

* the morphism `r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` of
  `RepresentingProjData.associatedMorphism` is `r` followed by `degreeInclusion`;
* there is an isomorphism `θ : ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n} ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` of sheaves of
  `ℤ`-graded `𝒪_T`-algebras with `u_n ≫ θ_n = ψ_n` in every degree, `u` being the pullback along
  `r` of the `ψ` of the universal quadruple;
* and `θ` is the only homomorphism of graded algebras with that property.

The source of `θ` is the Laurent algebra of the pullback of the universal invertible module; see
the module docstring for what identifying it with `r^*(⨁_n 𝒪_{Proj_S(𝒜)}(nd))` would need. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   CARRIED: (i) the representation of F_d by a scheme over S, which is Tag 01NV, proved only
--   conditionally here, the sharpest form being Fd.exists_representableBy_functor_of_charts, whose
--   conclusion is verbatim the hypothesis here and which still carries the Zariski sheaf property
--   of F_d and the affine-local charts c/hc/hcover, i.e. the descent of the charts along the base;
--   its smallness hypothesis is discharged by the instance Fd.small; (ii) `RepresentingProjData`,
--   as for the tag's S-morphism clause see the clause string on
--   `existsUnique_isoOver_representing`; (iii) `InclNatural`, that the carried functor F's
--   restriction maps are the pullback of a quadruple. QUALIFICATION on the source of theta: it is
--   the Laurent algebra of the pullback along r of the universal invertible module of the carried
--   representation, not r^*(⨁_n O_{Proj}(nd)) for the glued twists of Tag 01NR, and the second leg
--   is likewise the universal quadruple's own psi and is not identified with
--   RelativeProjTwists.TwistData.psi. Moving theta to the tag's source is
--   `Quadruple.existsUnique_theta_of_sourceIso`, which reduces that move to a single comparison of
--   graded algebras between r^*(⨁_n O(nd)) and the Laurent algebra of r^*L_univ carrying the one
--   second leg to the other. Its degreewise half, for a morphism into the absolute Proj of a
--   graded ring: `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` is O_{U_d}(d)^{⊗ n} ≅ O_{U_d}(dn) in
--   every INTEGER degree (StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaInteger) and
--   `Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackTwistPowIso` is phi^*O(dn) ≅ L^{⊗ n} in
--   every integer degree for phi : Y → U_d and an isomorphism alpha : phi^*O(d) ≅ L, whose target
--   is the degree-n piece of the Laurent algebra of L on the nose
--   (`PullbackTwistPower.tensorPowerModule_eq_laurent_piece`, by rfl). The MULTIPLICATIVITY of
--   thetaInt in an arbitrary INTEGER bidegree, without which that degreewise family would not be a
--   morphism of graded algebras, is `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul`
--   (StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerBidegree).
--   The RELATIVE statement, the
--   twists of Tag 01NR on Proj_S(A) in place of the twists on the absolute Proj of a graded ring:
--   a twist datum exists for every quasi-coherent graded algebra
--   (GluedTwistAlgebra.twistDataOfGradedAlgebra), the tag's own source r^*(⨁_n O(nd)) is
--   `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese` with its pieces
--   r^*O(nd) by rfl, and each O(nd) and each multiplication O(nd) ⊗ O(md) ⟶ O((n+m)d) is
--   invertible by `...RelativeVeroneseTwists.isInvertible_twistVeronese_piece` and
--   `isIso_mulSheaf_twistVeronese`, on the hypothesis that A is generated in degree one over every
--   affine open; both hold on the degree-d locus with NO such hypothesis, as
--   `RelativeVeroneseTwists.isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen` and
--   `isInvertible_pullbackTwistVeronese_piece_zero`
--   (StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison), and the
--   theta-assertion at the tag's source with no generation hypothesis is
--   `RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` there. Multiplicativity in an
--   arbitrary integer bidegree of the comparison R_n ≅ L^{⊗n} for a graded algebra with invertible
--   multiplications is `GradedLaurentRecognition.pieceIso_mul`, the resulting isomorphism of
--   graded algebras is `GradedLaurentRecognition.gradedIso`
--   (StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul), and a comparison of the tag's
--   source with the Laurent algebra is `RelativeVeroneseTwists.laurentComparison`
--   (StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison). What it is NOT built
--   from is the degree-one datum alpha : r^*O(d) ≅ L, which remains a hypothesis there and here,
--   being theta's own degree-one component. The clause that r_{d, L, psi} is an S-morphism is
--   `RepresentingProjData.associatedMorphism_comp_toBase`.
theorem exists_theta_associatedMorphism (hnat : R.InclNatural) (hd : 0 < d) {p : Y ⟶ S}
    (e : (Fd.functor (situationAlgebra A) d).RepresentableBy Y)
    (hp : ∀ (T : Scheme.{u}) (ξ : Fd (situationAlgebra A) d T), e.homEquiv.symm ξ ≫ p = ξ.1)
    {f : T ⟶ S} (Q : Quadruple f (situationAlgebra A) d) :
    ∃ (r : T ⟶ Y) (Qu : Quadruple p (situationAlgebra A) d) (hf : r ≫ p = f),
      R.associatedMorphism hd Q = r ≫ R.degreeInclusion hd e ∧
        (∃ θ : laurent (Qu.pullback r).L ≅ laurent Q.L,
            ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n) ∧
          ∃! Θ : laurent (Qu.pullback r).L ⟶ laurent Q.L,
            ∀ n : ℤ, Qu.universalLeg hf n ≫ Θ.app n = Q.twisting.app n := by
  have hr : e.homEquiv (e.homEquiv.symm (Fd.mk f Q)) = Fd.mk f Q := Equiv.apply_symm_apply _ _
  obtain ⟨Qu, hf, hθ, huniq⟩ := Q.existsUnique_theta_universal e hp hr
  exact ⟨_, Qu, hf, R.associatedMorphism_eq_comp hnat hd e Q hr, hθ, huniq⟩

end RepresentingProjData

end Representing

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
