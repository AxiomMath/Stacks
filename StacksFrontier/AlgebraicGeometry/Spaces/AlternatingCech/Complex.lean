module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulComplex

/-!
# The alternating Čech complex of an abelian sheaf on an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `U` be an algebraic space étale over `X`
and let `F` be an abelian sheaf on the spaces-étale site of `X`.  The alternating Čech complex
of `F` and `U` is the complex
`Hom(K^0, F) → Hom(K^1, F) → Hom(K^2, F) → …`
of abelian groups, with `K^p = ∧^{p+1} j_{U!} ℤ` the terms of the Koszul complex and the
differentials given by precomposition with those of `K^•`.  This is Stacks 0724.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechComplex` is **Stacks 0724**, the
  alternating Čech complex `Č^•_alt(f, F)`.
* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechDiff` is its differential,
  precomposition with the differential of `K^•`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechComplex_X` and
  `AlgebraicGeometry.Space.SpacesEtale.alternatingCechComplex_d` compute the terms and the
  differentials of the complex.

## Implementation notes

The homomorphism groups are taken in the category of abelian sheaves on the spaces-étale site
of `X`, which is where Stacks 0724 computes them; they are abelian groups because that
category is preadditive, and the differentials are additive because composition is bilinear.

Stacks 0724 states the definition for a surjective étale morphism `U ⟶ X`.  Being étale is
membership in the site, and surjectivity is not used by the definition: it is what makes the
complex compute the cohomology of `F`, which is the content of Stacks 0725.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The differential `Hom(K^p, F) ⟶ Hom(K^{p+1}, F)` of the alternating Čech complex:
precomposition with the differential `K^{p+1} ⟶ K^p` of the Koszul complex. -/
def alternatingCechDiff (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    AddCommGrpCat.of ((koszulComplex B S hS X U).X p ⟶ F) ⟶
      AddCommGrpCat.of ((koszulComplex B S hS X U).X (p + 1) ⟶ F) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun g => (koszulComplex B S hS X U).d (p + 1) p ≫ g)
      fun _ _ => Preadditive.comp_add _ _ _ _ _ _)

/-- **Stacks 0724.** The alternating Čech complex `Č^•_alt(f, F)` associated to an abelian
sheaf `F` on the spaces-étale site of `X` and an object `U` of that site: the complex
`Hom(K^0, F) → Hom(K^1, F) → Hom(K^2, F) → …` with Hom groups computed in `Ab(X_étale)` and
`K^p = ∧^{p+1} j_{U!} ℤ`. -/
@[stacks 0724]
def alternatingCechComplex (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  CochainComplex.of (fun p => AddCommGrpCat.of ((koszulComplex B S hS X U).X p ⟶ F))
    (alternatingCechDiff B S hS X U F) fun p => by
      refine AddCommGrpCat.ext fun g => ?_
      change (koszulComplex B S hS X U).d (p + 1 + 1) (p + 1) ≫
        ((koszulComplex B S hS X U).d (p + 1) p ≫ g) = 0
      rw [← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp]

/-- The term of the alternating Čech complex in degree `p` is `Hom(K^p, F)`. -/
theorem alternatingCechComplex_X (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (alternatingCechComplex B S hS X U F).X p =
      AddCommGrpCat.of ((koszulComplex B S hS X U).X p ⟶ F) :=
  rfl

/-- The differential of the alternating Čech complex is precomposition with the differential
of the Koszul complex. -/
theorem alternatingCechComplex_d (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (alternatingCechComplex B S hS X U F).d p (p + 1) = alternatingCechDiff B S hS X U F p :=
  CochainComplex.of_d (fun q => AddCommGrpCat.of ((koszulComplex B S hS X U).X q ⟶ F))
    (alternatingCechDiff B S hS X U F) p

/-- The differential of the alternating Čech complex, evaluated at a map `K^p ⟶ F`. -/
theorem alternatingCechComplex_d_apply (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (g : (koszulComplex B S hS X U).X p ⟶ F) :
    ((alternatingCechComplex B S hS X U F).d p (p + 1)).hom g =
      (koszulComplex B S hS X U).d (p + 1) p ≫ g :=
  congrArg (fun k => AddCommGrpCat.Hom.hom k g) (alternatingCechComplex_d B S hS X U F p)

end AlgebraicGeometry.Space.SpacesEtale

end
