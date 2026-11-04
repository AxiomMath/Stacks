module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

/-!
# From a quadruple to a triple: the graded map on sections

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and fix `d`. Section 01NS
attaches to a test scheme `T` the quadruples `(d, f : T → S, L, ψ)`, where
`ψ : f^*𝒜^{(d)} ⟶ ⨁_{n} L^{⊗ n}` is a homomorphism of sheaves of graded algebras, and Tag 01NU
says that for `S` affine the functor `F_d` of their strict equivalence classes is representable
by the open `U_d ⊆ Proj Γ(S, 𝒜)`. The source proves this by *identifying `F_d` with the functor
of triples of Section 01N4*, and the first half of that identification is the passage

`ψ : f^*𝒜^{(d)} ⟶ ⨁_n L^{⊗ n}`  ⟼  `A^{(d)} ⟶ Γ_*(T, L)`,   `A = Γ(S, 𝒜)`,

obtained by transposing `ψ` across the adjunction `f^* ⊣ f_*` and taking sections. **This file
carries out that passage**, and proves that the resulting degreewise family of maps on sections
is multiplicative and unit-preserving — that is, that it is a homomorphism of graded rings from
the `d`-th Veronese regrading of the sections of `𝒜` into the sections of the tensor powers of
`L`, which is exactly the `ψ` of a triple.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.sectionHom`: the degree-`k` component
  `Γ(U, 𝒜_{kd}) ⟶ Γ(f⁻¹U, L^{⊗ k})` of the transposed map, for an arbitrary open `U ⊆ S`. It is
  the composite of the unit `𝒜_{kd} ⟶ f_*f^*𝒜_{kd}` of the adjunction with `ψ_k`, read on
  sections.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom`: the same in the
  case `U = S`, so with `Γ(S, 𝒜_{kd}) ⟶ Γ(T, L^{⊗ k})`, which is the degree-`k` component of the
  map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.sectionHom_mul` and
  `Twisting.sectionHom_one`: **the family is multiplicative and carries the unit of `𝒜` to the
  unit of the Laurent algebra.** Together with additivity, which is how `sectionHom` is built,
  this says that the transposed map is a homomorphism of graded rings on sections.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom_mul` and
  `Twisting.globalSectionHom_one`: the same over `U = S`, that is, for the map
  `A^{(d)} ⟶ Γ_*(T, L)`.

## Scope

This is the direction *quadruples `→` triples* of the source's proof of Tag 01NU, on sections.
It is **unconditional**: no affineness of `S` and no quasi-coherence of `𝒜` is used, because none
is needed to transpose `ψ` and take sections. What the affine hypothesis and quasi-coherence are
for in the source is the **converse** direction — recovering `ψ`, and the morphism `f : T → S`
itself, from a graded ring map `A^{(d)} → Γ_*(T, L)`.

The maps below land in the sections of the tensor powers over `⊤`, while the `ψ` of
`Stacks.AlgebraicGeometry.ProjTriple.Triple` lands in
`Stacks.AlgebraicGeometry.ProjTriple.gammaStar`, whose degree-`k` summand is the sections of the
same tensor power over the *terminal* open `⊤_ (Opens T)` (the comparison is
`Stacks.AlgebraicGeometry.ProjTriple.toTopSection`) and whose multiplication is
`Stacks.SheafOfModules.sectionRingMul` rather than the Laurent multiplication. On the source
side, by `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparisonSectionRing`, the
domain is on the nose the degree-`kd` piece of the graded ring `A = Γ(S, 𝒜)` of Situation 01NN.

## Implementation notes

`sectionHom` is stated for an arbitrary open `U` of `S` rather than only for `U = S`: the
transposed map is a morphism of sheaves, so its degreewise components exist over every open, and
the multiplicativity below is proved at that generality and then specialized. The target is the
sections over the inverse image `f⁻¹U`, which is where the pullback-unit of Tag 01CD lands; for
`U = S` this is `T` itself, by `Twisting.preimage_top`, and `globalSectionHom` restricts along
that identification.

The multiplicativity is the section formula of the comparison of Tag 01CD,
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_pullbackUnit`, combined with the
multiplicativity axiom `Twisting.app_mul`; the degree bookkeeping `kd + ld = (k + l)d` is the
`eqToHom` that `app_mul` already carries. Unit preservation is `Twisting.app_one` combined with
`Stacks.PullbackStrictUnit.pullbackOne_eq`, the formula identifying the global unit of `f^*𝒜`
with the pullback-unit image of the global unit of `𝒜`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower RingedSpaceModuleAdjunction

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Twisting

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The inverse image of `S` itself under `f` is `T`. -/
theorem preimage_top (f : T ⟶ S) :
    (opensMap (ringedSpaceHom f)).obj (⊤ : Opens S.toRingedSpace.carrier) = ⊤ :=
  Opens.map_top _

/-- **The degree-`k` component of the transposed map `𝒜^{(d)} ⟶ f_*(⨁_n L^{⊗ n})`, on
sections.** A section of `𝒜_{kd}` over an open `U ⊆ S` is carried into `f^*𝒜_{kd}` by the unit
of `f^* ⊣ f_*` and then pushed through the degree-`k` component of `ψ`, giving a section of
`L^{⊗ k}` over `f⁻¹U`.

This is the first half of the identification of Tag 01NU: the source views `ψ` as a map of
`𝒪_S`-modules `𝒜^{(d)} → ⨁_n f_*L^{⊗ n}` and then takes sections. -/
def sectionHom (ψ : Twisting f A d L) (k : ℤ) (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) :
    (A.piece (k * d)).val.obj U →+
      ((laurent L).piece k).val.obj ((opensMap (ringedSpaceHom f)).op.obj U) :=
  AddMonoidHom.mk'
    (fun a => (ψ.app k).val.app ((opensMap (ringedSpaceHom f)).op.obj U)
      (pullbackUnit (ringedSpaceHom f) (A.piece (k * d)) U a))
    (fun a b => by
      rw [pullbackUnit_add]
      exact map_add _ _ _)

/-- The value of `sectionHom ψ k U` on a section `a` of `𝒜_{kd}` over `U` is the degree-`k`
component of `ψ` applied to the pullback-unit image of `a`. -/
theorem sectionHom_apply (ψ : Twisting f A d L) (k : ℤ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (k * d)).val.obj U) :
    ψ.sectionHom k U a =
      (ψ.app k).val.app ((opensMap (ringedSpaceHom f)).op.obj U)
        (pullbackUnit (ringedSpaceHom f) (A.piece (k * d)) U a) :=
  rfl

/-- **The transposed map is multiplicative.** For sections `a` of `𝒜_{kd}` and `b` of `𝒜_{ld}`
over an open `U ⊆ S`, the product in the Laurent algebra of their images is the image of their
product `ab`, a section of `𝒜_{(k+l)d}` after the degree identification `kd + ld = (k + l)d`.

This is the multiplicativity axiom of `ψ` read on the pullback-unit images of local sections,
which the comparison of Tag 01CD computes. -/
theorem sectionHom_mul (ψ : Twisting f A d L) (k l : ℤ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (k * d)).val.obj U)
    (b : (A.piece (l * d)).val.obj U) :
    ((laurent L).mul k l).app ((opensMap (ringedSpaceHom f)).op.obj U)
        (ψ.sectionHom k U a) (ψ.sectionHom l U b) =
      ψ.sectionHom (k + l) U
        ((eqToHom (congrArg A.piece (by ring : k * d + l * d = (k + l) * d))).val.app U
          ((A.mul (k * d) (l * d)).app U a b)) := by
  have hmul : (ψ.app k ⊗ₘ ψ.app l) ≫ mulHom (laurent L) k l =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (k * d)) (A.piece (l * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (mulHom A (k * d) (l * d) ≫
              eqToHom (congrArg A.piece (by ring : k * d + l * d = (k + l) * d))) ≫
          ψ.app (k + l) :=
    ψ.app_mul k l
  have hcomp := congrArg
    (fun θ : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (k * d)) ⊗
          (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (l * d)) ⟶
        (laurent L).piece (k + l) =>
      θ.val.app ((opensMap (ringedSpaceHom f)).op.obj U)
        (tmul T.toRingedSpace ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (k * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (l * d)))
          ((opensMap (ringedSpaceHom f)).op.obj U)
          (pullbackUnit (ringedSpaceHom f) (A.piece (k * d)) U a)
          (pullbackUnit (ringedSpaceHom f) (A.piece (l * d)) U b)))
    hmul
  rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    SheafOfModules.comp_val_app_apply, tensorHom_tmul, mulHom_tmul,
    ← pullbackTensorComparison_pullbackUnit (ringedSpaceHom f) (A.piece (k * d))
      (A.piece (l * d)) U a b,
    inv_val_app_apply, pullbackUnit_naturality, SheafOfModules.comp_val_app_apply,
    mulHom_tmul] at hcomp
  exact hcomp

/-- **The transposed map carries the unit of `𝒜` to the unit of the Laurent algebra.** The
global unit of `𝒜` lives in degree `0`, which is degree `0` of the Veronese regrading as well,
and its image is the global unit of `⨁_n L^{⊗ n}`.

This is the unit axiom of `ψ`, read on the pullback-unit image of the global unit of `𝒜`. -/
theorem sectionHom_one (ψ : Twisting f A d L) (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) :
    ψ.sectionHom 0 U
        ((eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))).val.app U (A.one.eval U)) =
      (laurent L).one.eval ((opensMap (ringedSpaceHom f)).op.obj U) := by
  have hcomp := congrArg
    (fun θ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ⟶
        (laurent L).piece 0 =>
      θ.val.app ((opensMap (ringedSpaceHom f)).op.obj U)
        (oneSec T.toRingedSpace ((opensMap (ringedSpaceHom f)).op.obj U)))
    ψ.app_one
  rw [show Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A =
      Stacks.PullbackExteriorAlgebra.comparisonOne (ringedSpaceHom f) A from
    (Stacks.PullbackStrictUnit.pullbackOne_eq (ringedSpaceHom f) A).trans
      (Stacks.PullbackExteriorAlgebra.comparisonOne_eq (ringedSpaceHom f) A).symm,
    SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    Stacks.PullbackExteriorAlgebra.comparisonOne_val_app_oneSec, pullbackUnit_naturality,
    show SheafOfModules.GradedAlgebra.oneHom (laurent L) = oneMorphism (laurent L) from rfl,
    oneMorphism_val_app_oneSec] at hcomp
  exact hcomp

/-- **The degree-`k` component of the map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4**, for
`A = Γ(S, 𝒜)`: `sectionHom` over `U = S`, with its target read on `T` through
`Twisting.preimage_top`. -/
def globalSectionHom (ψ : Twisting f A d L) (k : ℤ) :
    (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier)) →+
      ((laurent L).piece k).val.obj (op (⊤ : Opens T.toRingedSpace.carrier)) :=
  (((laurent L).piece k).val.restrictₛₗ
      (eqToHom (congrArg op (preimage_top f)) :
        (opensMap (ringedSpaceHom f)).op.obj (op (⊤ : Opens S.toRingedSpace.carrier)) ⟶
          op (⊤ : Opens T.toRingedSpace.carrier))).toAddMonoidHom.comp
    (ψ.sectionHom k (op (⊤ : Opens S.toRingedSpace.carrier)))

/-- The value of `globalSectionHom ψ k` on a global section `a` of `𝒜_{kd}` is the restriction of
`sectionHom ψ k ⊤ a` along the identification `f⁻¹(S) = T` of `Twisting.preimage_top`. -/
theorem globalSectionHom_apply (ψ : Twisting f A d L) (k : ℤ)
    (a : (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    ψ.globalSectionHom k a =
      ((laurent L).piece k).val.map
        (eqToHom (congrArg op (preimage_top f)) :
          (opensMap (ringedSpaceHom f)).op.obj (op (⊤ : Opens S.toRingedSpace.carrier)) ⟶
            op (⊤ : Opens T.toRingedSpace.carrier))
        (ψ.sectionHom k (op (⊤ : Opens S.toRingedSpace.carrier)) a) :=
  rfl

/-- **The map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4 is multiplicative**, `A = Γ(S, 𝒜)`: this is
`Twisting.sectionHom_mul` over `U = S`, the multiplications being those of the sheaves of graded
algebras `𝒜` and `⨁_n L^{⊗ n}` on global sections. -/
theorem globalSectionHom_mul (ψ : Twisting f A d L) (k l : ℤ)
    (a : (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier)))
    (b : (A.piece (l * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    ((laurent L).mul k l).app (op (⊤ : Opens T.toRingedSpace.carrier))
        (ψ.globalSectionHom k a) (ψ.globalSectionHom l b) =
      ψ.globalSectionHom (k + l)
        ((eqToHom (congrArg A.piece (by ring : k * d + l * d = (k + l) * d))).val.app
          (op (⊤ : Opens S.toRingedSpace.carrier)) ((A.mul (k * d) (l * d)).app _ a b)) := by
  rw [globalSectionHom_apply, globalSectionHom_apply, globalSectionHom_apply,
    ← ((laurent L).mul k l).naturality
      (eqToHom (congrArg op (preimage_top f)) :
        (opensMap (ringedSpaceHom f)).op.obj (op (⊤ : Opens S.toRingedSpace.carrier)) ⟶
          op (⊤ : Opens T.toRingedSpace.carrier)),
    ψ.sectionHom_mul k l]

/-- **The map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4 carries `1` to `1`**, `A = Γ(S, 𝒜)`: this is
`Twisting.sectionHom_one` over `U = S`. -/
theorem globalSectionHom_one (ψ : Twisting f A d L) :
    ψ.globalSectionHom 0
        ((eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))).val.app
          (op (⊤ : Opens S.toRingedSpace.carrier)) (A.one.eval _)) =
      (laurent L).one.eval (op (⊤ : Opens T.toRingedSpace.carrier)) := by
  rw [globalSectionHom_apply, ψ.sectionHom_one]
  exact PresheafOfModules.sections_property (laurent L).one _

/-- **The global sections `ψ(a)` of `L` that the generation condition of a triple is about.**
Section 01N4 requires of a triple `(d, L, ψ)` that `L` be generated by the global sections
`ψ(a)`, `a ∈ A_d`; those sections are the degree-one values of the map `A^{(d)} ⟶ Γ_*(T, L)`,
read through the identification `L^{⊗ 1} ≅ L` of Tag 01CU.

The argument is a global section of `𝒜_d`, carried into degree `1 · d` of the Veronese
regrading by the degree identification `d = 1 · d`. -/
def degreeOneSectionHom (ψ : Twisting f A d L) :
    (A.piece d).val.obj (op (⊤ : Opens S.toRingedSpace.carrier)) →+
      L.val.obj (op (⊤ : Opens T.toRingedSpace.carrier)) :=
  letI := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry T.toRingedSpace.presheaf
    (isSheafStruct T) L inferInstance
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    T.toRingedSpace.presheaf (isSheafStruct T) L
  ((tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L).hom.val.app
        (op (⊤ : Opens T.toRingedSpace.carrier))).hom.toAddMonoidHom.comp
    ((ψ.globalSectionHom 1).comp
      ((eqToHom (congrArg A.piece (one_mul d).symm) :
            A.piece d ⟶ A.piece (1 * d)).val.app
          (op (⊤ : Opens S.toRingedSpace.carrier))).hom.toAddMonoidHom)

end Twisting

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
