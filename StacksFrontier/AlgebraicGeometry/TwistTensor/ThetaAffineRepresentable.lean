module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineBaseHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineFdRepresentable
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Theta

/-!
# Lemma 01O1's `θ`-assertion with nothing carried, over an affine base

`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Theta` proves the `θ`-assertion of
[Stacks, Tag 01O1] — existence, the commutativity of the characterising triangle, and uniqueness
— for a scheme `Y` representing the functor `F_d` of Section 01NS, with two things carried: the
representation `e` itself, which is Tag 01NV, and a hypothesis `hp` saying that `e` is a
representation *over* `S`.

**`hp` is removable, and over an affine base so is `e`.**

`hp` is removable because the morphism `p : Y ⟶ S` it constrains need not be prescribed: the
universal element of `F_d(Y)` is a pair, a morphism `Y ⟶ S` and a strict equivalence class over
it, and taking `p` to be *that* morphism makes the one thing `hp` was for — that the universal
element's recorded morphism is `p` — true by `rfl`. The identity `r ≫ p = f`, which `hp`
underwrote, then comes out as part of the conclusion rather than going in as an assumption.

`e` is available unconditionally over an affine base: it is
`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`, Tag 01NU for an affine base, whose
bijections `...RelativeProjQcohSheaf.Quadruple.fdEquiv` have the computable
`...RelativeProjQcohSheaf.AffineTripleSections.fdOfHom` for their inverse. Its over-`S` clause is
`...RelativeProjQcohSheaf.Quadruple.toProj_classifyingHomOfClass_comp_toSpecZero` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineBaseHom`, reassociated below.

So over an affine base the whole `θ`-assertion holds with no hypothesis beyond `IsAffine S` and
`0 < d`.

**The affineness is removable, and is removed elsewhere.** A representation `e` is in fact
available over an arbitrary base: residue (i) of [Stacks, Tag 01NY] — that the relative
degree-`d` open represents `F_d` — is proved for an arbitrary relative homogeneous spectrum in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv`, and
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaRelativeRepresentable` packages that bijection as
a `CategoryTheory.Functor.RepresentableBy` and reruns the argument below on it, giving
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_relativeProjData` on `0 < d` alone. The
statements below are kept because they are the affine-chart forms, stated at the absolute
`U_d ⊆ Proj Γ(S, 𝒜)` rather than at the degree-`d` open of a relative `Proj`; neither form
implies the other verbatim.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.exists_universalQuadruple_of_representableBy`:
  the universal element of a representation of `F_d` is the class of a quadruple over the morphism
  it records — no over-`S` hypothesis.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_representableBy`:
  **the `θ`-assertion for a representation of the bare functor `F_d`**, with the morphism to `S`
  and the identity `r ≫ p = f` produced rather than assumed.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.representableByDegreeOpen_comp_structureHom`:
  the affine representation is a representation over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_isAffine`:
  **the `θ`-assertion over an affine base, with nothing carried.**

## What this does not do

It does not present `θ` on the tag's own source `r^*(⨁_{n ∈ ℤ} 𝒪(nd))`. The source here is the
Laurent algebra of the pullback along `r` of the universal invertible module of the
representation, and the triangle's second leg is the pullback of the universal quadruple's own
`ψ`. Moving to the tag's source is one comparison of graded algebras
(`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_sourceIso`), and what that comparison
would have to carry is the pullback of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` to the pullback of the universal
quadruple's `ψ`.

The first half of that is available: the adjoint-transposed and base-changed form of
`TwistData.ψ` **does** exist, as
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTranspose`, `psiLeg` and
`psiLegVeronese` of `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiPullbackLeg`, and it is
multiplicative both before base change (`TwistData.psiTranspose_mulSheaf`,
`...TwistTensor.PsiLegMultiplicative`) and after it
(`TwistData.psiLegVeronese_mulSheaf`, `...TwistTensor.PsiLegVeroneseMultiplicative`).

What *is* still owed is the second half — no `...RelativeProjQcohSheaf.Twisting`, and so no
`Quadruple`, is built from a `TwistData` anywhere in this repository — and behind it the
statement the source's own proof of [Stacks, Tag 01O1] turns on: that the quadruple
`(U_d → S, d, 𝒪_{U_d}(d), ψ_univ|_{𝒜^{(d)}})` assembled from [Stacks, Tag 01NR] **is** the
universal element of `F_d(U_d)`. It has three ingredients.

* The epimorphy of `π^*𝒜_d ⟶ 𝒪(d)` over the degree-`d` locus is still owed (recorded in
  `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers`). Its absolute shadow is available
  and unconditional — `...MorphismsIntoProj.generatesStalks_psiPullbackVeroneseHom_one` for any
  morphism into the absolute `U_d`, and
  `iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top` in
  `...ProjDegreeOpenUniversalTriple` as a covering of nonvanishing opens — and
  `...AffineTwisting.epi_app_one` turns such a covering into `Epi` with no hypothesis on the base.
  What is missing is the descent along the charts.
* The unit normalisation splits in two, and **one half is now proved**. On the comparison's side,
  `...GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero` of
  `StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentUnit` says the recognition isomorphism
  preserves the graded-algebra unit — the clause `...GradedVeronese.isoOfPiecesOfHoms` does not
  carry, since the homomorphisms of that category preserve products only. On the leg's side,
  `...TwistData.psiTransposeNat_zero_unit` of
  `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegUnit` is the unit law for the transpose on
  sections over the inverse image of an open of the base — the first consumer of the `ψ_one` field
  anywhere. `TwistData.psiTransposeHom` is still a `SheafOfModules.GradedAlgebra.Hom` and not a
  `UnitalHom`: what remains is to descend that sectionwise equation to a morphism equation along
  the cover of the relative `Proj` by the inverse images of an affine cover of the base, and to
  carry it through the base change of `TwistData.psiLeg`.
* The join of `TwistData.ψ_chart` with `TwistData.psi_val_app` is **done**:
  `...TwistData.psiTransposeNat_chart` of
  `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegChart` states the chart description of the
  homogeneous-section map for the adjoint transpose, and `...TwistData.psiTranspose_chart` reads it
  in an integer degree. What remains of the chart-wise comparison is the descent of
  `...ProjClassifyingPullback.classifyingHom_universalVeroneseSections` along the charts: that
  sectionwise chart description has to be pushed through the restriction to the degree-`d` locus
  and the comparison `...ProjTwistTensorPowDegreeOpen.thetaNat` of the twists with their tensor
  powers, and assembled into a `...RelativeProjQcohSheaf.Twisting` on each chart. Note that the
  framework gap the comparison was once thought to need **does not exist**:
  the sheaf-level `Quadruple`/`Twisting` machinery is defined *on top of* the section-level
  `VeroneseSections`/`classifyingHom` machinery — `Quadruple.classifyingHom` of
  `...RelativeProjQcohSheaf.AffineQuadrupleRoundTrip` is literally
  `ProjTripleClassifying.classifyingHom` of `veroneseSections P.twisting` — so the chart-wise
  comparison is a statement about *sections*, at the level `ψ_chart` is already stated at, and not
  a transport of `ψ_chart` into sheaf morphisms.

So that comparison is not available here and nothing below pretends otherwise.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T S Y : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### The universal quadruple of a representation of `F_d`, with no over-`S` hypothesis -/

/-- **The universal element of a representation of `F_d` is the class of a quadruple**, over the
morphism it records. -/
theorem Fd.exists_universalQuadruple_of_representableBy
    (e : (Fd.functor A d).RepresentableBy Y) :
    ∃ (p : Y ⟶ S) (Qu : Quadruple p A d), e.homEquiv (𝟙 Y) = Fd.mk p Qu := by
  obtain ⟨Qu, hQu⟩ := Fd.exists_mk (e.homEquiv (𝟙 Y)) (f := (e.homEquiv (𝟙 Y)).1) rfl
  exact ⟨_, Qu, hQu⟩

/-- **Stacks Project, Tag 01O1.** *The comparison `θ` exists, its characterising triangle
commutes, and the triangle determines it* — for a scheme `Y` representing the functor `F_d` of
Section 01NS. -/
theorem Quadruple.existsUnique_theta_of_representableBy (Q : Quadruple f A d)
    (e : (Fd.functor A d).RepresentableBy Y) {r : T ⟶ Y}
    (hr : e.homEquiv r = Fd.mk f Q) :
    ∃ (p : Y ⟶ S) (Qu : Quadruple p A d) (hf : r ≫ p = f),
      (∃ θ : laurent (Qu.pullback r).L ≅ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n) ∧
        ∃! Θ : laurent (Qu.pullback r).L ⟶ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ Θ.app n = Q.twisting.app n := by
  obtain ⟨p, Qu, hQu⟩ := Fd.exists_universalQuadruple_of_representableBy e
  obtain ⟨hf, γ, hγ⟩ := Fd.exists_laurentIso_of_mk_eq (Qu.pullback r) Q
    ((Fd.homEquiv_eq_mk_pullback e hQu r).symm.trans hr)
  have hθ : ∀ n : ℤ, Qu.universalLeg hf n ≫ γ.hom.app n = Q.twisting.app n := by
    intro n
    rw [Quadruple.universalLeg, Category.assoc, hγ n]
    simp
  exact ⟨p, Qu, hf, ⟨γ, hθ⟩, Quadruple.existsUnique_theta Q _ (Qu.universalLeg hf) hθ⟩

/-! ### The affine representation is a representation over the base -/

variable {B : SheafGradedAlgebra.{u} S} {k : ℕ}

/-- The structure morphism `U_d ⟶ Proj Γ(S, 𝒜) ⟶ Spec A_0 ⟶ S` of the open of
Equation 27.12.0.1 inside the `Proj` of the graded ring of global sections. -/
abbrev Fd.degreeOpenStructureHom [IsAffine S] (B : SheafGradedAlgebra.{u} S) (k : ℕ) :
    (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme ⟶ S :=
  (degreeOpen (B.grading (⊤ : S.Opens)) k).ι ≫
    AlgebraicGeometry.Proj.toSpecZero (B.grading (⊤ : S.Opens)) ≫
      Spec.map (AffineTripleSections.structureRingHom B) ≫ S.isoSpec.inv

/-- **The representation of `F_d` by `U_d` over an affine base is a representation over `S`**:
the morphism `T ⟶ U_d` attached to a class in `F_d(T)`, followed by the structure morphism of
`U_d`, is the morphism the class records. -/
theorem Fd.representableByDegreeOpen_comp_structureHom [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (T' : Scheme.{u}) (ξ : Fd (situationAlgebra B) (k : ℤ) T') :
    (Fd.representableByDegreeOpen hk hqc).homEquiv.symm ξ ≫ Fd.degreeOpenStructureHom B k
      = ξ.1 := by
  refine Eq.trans ?_ (Quadruple.toProj_classifyingHomOfClass_comp_toSpecZero hk hqc ξ)
  exact (Category.assoc _ _ _).symm

/-! ### Lemma 01O1's `θ`-assertion over an affine base -/

/-- **Stacks Project, Tag 01O1 over an affine base, with nothing carried.** Let `S` be affine,
`𝒜` a graded `𝒪_S`-algebra of Situation 01NN, `d ≥ 1`, and `(f : T → S, d, ℒ, ψ)` a quadruple of
Section 01NS. Then there are a morphism `r : T ⟶ U_d ⊆ Proj Γ(S, 𝒜)` with
`r ≫ (structure morphism of U_d) = f`, a universal quadruple `(U_d → S, d, ℒ_univ, ψ_univ)`, and
an isomorphism

`θ : ⨁_{n ∈ ℤ} (r^*ℒ_univ)^{⊗ n} ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras with `u_n ≫ θ_n = ψ_n` in every integer degree, `u` being
the pullback of `ψ_univ` along `r`; and `θ` is the only homomorphism of graded algebras with that
property.

Nothing is assumed beyond `IsAffine S` and `0 < d`: the representation of `F_d` is
`Fd.representableByDegreeOpen`, its over-`S` clause is
`Fd.representableByDegreeOpen_comp_structureHom`, and the quasi-coherence those two want is the
field `isQuasicoherent` of the graded algebra. See the module docstring for why the source of `θ`
is not the tag's own `r^*(⨁_n 𝒪(nd))`. -/
theorem Quadruple.existsUnique_theta_of_isAffine [IsAffine S] (hk : 0 < k)
    (Q : Quadruple f (situationAlgebra B) (k : ℤ)) :
    ∃ (r : T ⟶ (degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme)
      (Qu : Quadruple (Fd.degreeOpenStructureHom B k) (situationAlgebra B) (k : ℤ))
      (hf : r ≫ Fd.degreeOpenStructureHom B k = f),
      (∃ θ : laurent (Qu.pullback r).L ≅ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ θ.hom.app n = Q.twisting.app n) ∧
        ∃! Θ : laurent (Qu.pullback r).L ⟶ laurent Q.L,
          ∀ n : ℤ, Qu.universalLeg hf n ≫ Θ.app n = Q.twisting.app n := by
  obtain ⟨Qu, hf, hθ, huniq⟩ :=
    Q.existsUnique_theta_universal
      (Fd.representableByDegreeOpen hk fun n => B.isQuasicoherent n)
      (Fd.representableByDegreeOpen_comp_structureHom hk fun n => B.isQuasicoherent n)
      (r := (Fd.representableByDegreeOpen hk fun n => B.isQuasicoherent n).homEquiv.symm
        (Fd.mk f Q))
      (Equiv.apply_symm_apply _ _)
  exact ⟨_, Qu, hf, hθ, huniq⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
