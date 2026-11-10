module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleUnique

/-!
# The comparison `θ` of a quadruple is determined by its characterising triangle

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), `d` an integer and
`(f : T → S, d, ℒ, ψ)` a quadruple. Lemma 01O1 attaches to it the `S`-morphism
`r = r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` and asserts that there is an isomorphism of `ℤ`-graded
`𝒪_T`-algebras

`θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

for which the triangle
`𝒜^{(d)} --ψ--> f_*(⨁_n ℒ^{⊗ n})`, `𝒜^{(d)} --ψ_univ--> π_*(⨁_{n ≥ 0} 𝒪(nd))`,
`π_*(⨁_{n ≥ 0} 𝒪(nd)) --θ--> f_*(⨁_n ℒ^{⊗ n})` commutes, and that **the commutativity of that
triangle determines `θ`**.

This file proves the last assertion. The source of `θ` enters only as a sheaf of `ℤ`-graded
`𝒪_T`-algebras `ℛ` together with the degreewise family

`u_n : f^*𝒜_{nd} ⟶ ℛ_n`

that the triangle's second leg provides — for Lemma 01O1 these are
`ℛ_n = r^*𝒪_{Proj_S(𝒜)}(nd)` and `u_n` the adjoint transpose of `ψ_univ` in degree `nd` pulled
back along `r`, using `r ≫ π = f`. Neither the identity of `ℛ` nor that of `u` is used: the
conclusion holds for every such pair, hence in particular for Lemma 01O1's.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.epi_of_comm`: the second leg of the
  triangle is an epimorphism in degree one, as soon as some isomorphism solves the triangle.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.theta_eq_of_comm`: **a homomorphism
  of graded algebras solving the triangle equals any isomorphism solving it.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_theta`: **once one
  isomorphism solves the triangle, it is the unique homomorphism solving it** — the uniqueness
  assertion of Lemma 01O1.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_sourceIso`:
  **both halves of the tag's `θ`-assertion transport along a comparison of the source.** An
  isomorphism solving the triangle on `ℛ`, together with an isomorphism `c : ℛ' ≅ ℛ` of graded
  algebras carrying a second degreewise family `v` to `u`, gives an isomorphism solving the
  triangle on `ℛ'` and the uniqueness of that solution.

## Where the existence of `θ` is proved

The **existence** of `θ`, and the commutativity of the triangle for that `θ`, are
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.exists_theta` and
`...RelativeProjQcohSheaf.RepresentingProjData.exists_theta_associatedMorphism` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Theta`, which carry the Tag 01O1 attribute
for those clauses. There `θ` is the comparison of a strict equivalence of quadruples: the given
quadruple and the pullback, along the morphism attached to its class, of the universal quadruple
of a representation of the functor `F_d` of Section 01NS. That representation is Tag 01NV and is
carried, and the source of `θ` is accordingly the Laurent algebra of the pullback of the
universal invertible module, which is not identified with `r^*(⨁_n 𝒪_{Proj_S(𝒜)}(nd))` for the
glued twists of Tag 01NR. The `ψ` of the triangle is `Quadruple.twisting`.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- The homogeneous components of an isomorphism of sheaves of graded algebras are inverse to
each other, in the order `hom ≫ inv`. -/
private theorem hom_app_comp_inv_app
    {X Y : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    (θ : X ≅ Y) (n : ℤ) : θ.hom.app n ≫ θ.inv.app n = 𝟙 _ :=
  congrArg (fun φ : X ⟶ X => φ.app n) θ.hom_inv_id

/-- The homogeneous components of an isomorphism of sheaves of graded algebras are inverse to
each other, in the order `inv ≫ hom`. -/
private theorem inv_app_comp_hom_app
    {X Y : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    (θ : X ≅ Y) (n : ℤ) : θ.inv.app n ≫ θ.hom.app n = 𝟙 _ :=
  hom_app_comp_inv_app θ.symm n

namespace Quadruple

variable (P : Quadruple f A d)
  (R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
  (u : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)) ⟶ R.piece n)

/-- **The second leg of Lemma 01O1's triangle is an epimorphism in degree one**, as soon as some
isomorphism `θ` solves the triangle. -/
theorem epi_of_comm {θ : R ≅ laurent P.L}
    (hθ : ∀ n : ℤ, u n ≫ θ.hom.app n = P.twisting.app n) : Epi (u 1) := by
  have := P.epi_app_one
  have : IsIso (θ.inv.app 1) :=
    ⟨θ.hom.app 1, inv_app_comp_hom_app θ 1, hom_app_comp_inv_app θ 1⟩
  have heq : P.twisting.app 1 ≫ θ.inv.app 1 = u 1 := by
    rw [← hθ 1, Category.assoc, hom_app_comp_inv_app θ 1, Category.comp_id]
  rw [← heq]
  exact epi_comp _ _

/-- **Stacks Project, Tag 01O1.** *The commutativity of the characterising triangle determines
`θ`.*

Let `(f : T → S, d, ℒ, ψ)` be a quadruple, let `ℛ` be a sheaf of `ℤ`-graded `𝒪_T`-algebras and
let `u_n : f^*𝒜_{nd} ⟶ ℛ_n` be a degreewise family — for the tag, `ℛ_n = r^*𝒪(nd)` and `u` the
pullback along `r_{d, ℒ, ψ}` of the adjoint transpose of `ψ_univ`. If an isomorphism
`θ : ℛ ≅ ⨁_n ℒ^{⊗ n}` of graded algebras satisfies `u_n ≫ θ_n = ψ_n` in every degree, then it is
the only homomorphism of graded algebras that does: any `Θ` with `u_n ≫ Θ_n = ψ_n` equals `θ`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   The clause that r_{d, L, psi} is an S-morphism is carried by
--   `RepresentingProjData.associatedMorphism_comp_toBase`
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   The EXISTENCE of theta and the commutativity of the triangle are proved elsewhere and carry
--   the attribute there: `Quadruple.exists_theta` and
--   `RepresentingProjData.exists_theta_associatedMorphism` of
--   StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Theta, where theta is the comparison of
--   a strict equivalence with the pullback of the universal quadruple of a representation of F_d
--   (Tag 01NV, carried), and its source is the Laurent algebra of the pullback of the universal
--   invertible module rather than r^*(⨁_n O_{Proj}(nd)) for the glued twists of Tag 01NR.
theorem theta_eq_of_comm {θ : R ≅ laurent P.L} {Θ : R ⟶ laurent P.L}
    (hθ : ∀ n : ℤ, u n ≫ θ.hom.app n = P.twisting.app n)
    (hΘ : ∀ n : ℤ, u n ≫ Θ.app n = P.twisting.app n) :
    Θ = θ.hom := by
  have := epi_of_comm P R u hθ
  have h1 : Θ.app 1 = θ.hom.app 1 := (cancel_epi (u 1)).mp ((hΘ 1).trans (hθ 1).symm)
  have hγ : θ.inv ≫ Θ = 𝟙 (laurent P.L) := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    refine laurent_app_eq_of_app_one (γ := θ.inv ≫ Θ) (γ' := 𝟙 (laurent P.L))
      (e := Iso.refl P.L) ?_ ?_ n
    · change (θ.inv.app 1 ≫ Θ.app 1) ≫ (oneIsoL P.L).hom = (oneIsoL P.L).hom ≫ 𝟙 _
      rw [h1, inv_app_comp_hom_app θ 1, Category.id_comp, Category.comp_id]
    · simp
  simpa using congrArg (θ.hom ≫ ·) hγ

/-- **Stacks Project, Tag 01O1.** *The characterising triangle has at most one solution.*

Packaged as a `∃!`: once one isomorphism of graded algebras `θ : ℛ ≅ ⨁_n ℒ^{⊗ n}` makes Lemma
01O1's triangle commute, it is the unique homomorphism of graded algebras doing so. -/
theorem existsUnique_theta {θ : R ≅ laurent P.L}
    (hθ : ∀ n : ℤ, u n ≫ θ.hom.app n = P.twisting.app n) :
    ∃! Θ : R ⟶ laurent P.L, ∀ n : ℤ, u n ≫ Θ.app n = P.twisting.app n :=
  ⟨θ.hom, hθ, fun _ hΘ => theta_eq_of_comm P R u hθ hΘ⟩

/-- **Stacks Project, Tag 01O1.** *Both halves of the tag's `θ`-assertion transport along a
comparison of the source.*

Let `ℛ'` be a second sheaf of `ℤ`-graded `𝒪_T`-algebras with a degreewise family
`v_n : f^*𝒜_{nd} ⟶ ℛ'_n`, and let `c : ℛ' ≅ ℛ` be an isomorphism of graded algebras with
`v_n ≫ c_n = u_n` in every degree — that is, a presentation of the triangle's second leg on `ℛ'`.
Then an isomorphism `θ` solving the triangle on `ℛ` produces one solving it on `ℛ'`, namely
`c ≫ θ`, and that solution is again the unique homomorphism of graded algebras solving it. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   The existence half is `Quadruple.exists_theta` (Tag 01NV carried there), which produces theta
--   on the Laurent algebra of the pullback of a universal invertible module rather than on
--   r^*(⨁_n O_{Proj}(nd)), and the uniqueness half is `theta_eq_of_comm` applied to R'. What this
--   adds is that the tag's own source needs no separate argument: given a comparison c with
--   v_n ≫ c_n = u_n, the tag's theta is c followed by theta, and is unique. The tag's source is
--   `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese`, the pullback along r
--   of the d-th Veronese regrading of the glued twists of Tag 01NR, with degree-n piece r^*O(nd)
--   by rfl, and this statement instantiated at it is
--   `...RelativeVeroneseTwists.existsUnique_theta_pullbackTwistVeronese`. A comparison c for it is
--   `...RelativeVeroneseTwists.laurentComparison`, which needs degree-one generation of A and a
--   degree-one isomorphism alpha : r^*O(d) ≅ L; with it this statement is
--   `...RelativeVeroneseTwists.existsUnique_theta_of_degreeOneIso`
theorem existsUnique_theta_of_sourceIso
    {R' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)) ⟶ R'.piece n)
    (c : R' ≅ R) (hc : ∀ n : ℤ, v n ≫ c.hom.app n = u n)
    {θ : R ≅ laurent P.L} (hθ : ∀ n : ℤ, u n ≫ θ.hom.app n = P.twisting.app n) :
    ∃ θ' : R' ≅ laurent P.L, (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
      ∃! Θ : R' ⟶ laurent P.L, ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n := by
  have h' (n : ℤ) : v n ≫ (c ≪≫ θ).hom.app n = P.twisting.app n := by
    simp [reassoc_of% (hc n), hθ n]
  exact ⟨c ≪≫ θ, h', existsUnique_theta P R' v h'⟩

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
