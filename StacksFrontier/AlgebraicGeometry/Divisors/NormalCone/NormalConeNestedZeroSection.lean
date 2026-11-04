module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NestedConormalVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSectionAffineCriterion

/-!
# The normal cone of a nested pair of divisors lands in the zero section

Let `Z ⊆ Y ⊆ X` be closed subschemes with `Y ⊆ X` an effective Cartier divisor, so that the
normal cone `C_YX` is a line bundle over `Y` with zero section `o : Y ⟶ C_YX`. This file proves
that the composite

    `C_ZY ⟶ C_ZX ⟶ C_YX`

factors through `o`, which is the hypothesis `hzero` that
`Stacks.Chow.normalConeToZeroFibre` would otherwise need for [Stacks, Tag 0FEB].

## Main results

* `Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection`: **the composite
  `C_ZY ⟶ C_ZX ⟶ C_YX` is the projection `C_ZY ⟶ Z ⟶ Y` followed by the zero section.**

## How the proof goes

`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens` turns the
factorization into one vanishing: the algebra datum of the relative-spectrum pair that the functor
of points of the total space of the conormal line bundle attaches to the composite has to kill the
degree-one homogeneous sections over the affine opens of `Y`. What is left — and what this file
does — is to compute that datum.

The morphism whose pair is wanted is a composite of three morphisms of relative spectra over three
different bases,

    `C_ZY --m₁--> C_ZX --m₂--> C_YX --ν--> N_YX`,

followed by the comparison `N_YX ⟶ Tot(𝒞_{Y/X})` whose pair is
`Stacks.LineBundle.Situation.vectorBundlePair`. Each factor is a
`Stacks.RelativeSpec.pairToHom`: `m₁` and `m₂` by `Stacks.Conormal.normalConeMap_eq_pairToHom`,
and `ν` by `Stacks.Conormal.normalConeToNormalBundle_eq_pairToHom`. So
`Stacks.RelativeSpec.comp_pairToHom` presents the whole composite, and the pair is peeled one
factor at a time by `Stacks.RelativeSpec.pullback_comp_pairToHom_algebraHomPair`: pulling an
`Stacks.RelativeSpec.algebraHomPair` back along a `pairToHom` composes the two algebra maps and
leaves the inner pair alone.

What the peeling produces, read on an affine open `U ⊆ Y` and a degree-one section `x`, is the
chain

    `Sym(𝒞_{Y/X})(U) ⟶ 𝒞_{Y/X,*}(U) ⟶ 𝒞_{Z/X,*}(f⁻¹U) ⟶ 𝒞_{Z/Y,*}(f⁻¹U) ⟶ Γ(C_ZY, ...)`,

whose first step is `Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl` followed
by `Stacks.Conormal.conormalSymmetricAlgebraSheafHom_ungradedIncl`, whose two middle steps are
`Stacks.Conormal.conormalAlgebraSheafPushforwardHom_ungradedIncl` (that is
`Stacks.Conormal.normalConeMapPair_snd_right_app_ungradedIncl` here), and whose last step is a
ring map. The two middle steps compose to the canonical map
`𝒞_{Y/X,1} ⟶ 𝒞_{Z/X,1} ⟶ 𝒞_{Z/Y,1}`, which is zero by
`AlgebraicGeometry.conormalAlgebraHom_comp_map_eq_zero`, and a ring map kills `0`.

## Implementation notes

**The pair of a composite is read with no dependent-type transport.** The round-trip identity
`Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom` is an equation between terms of
a `Σ`-type, so its second components do not share a type; but every use of it below is through the
map `p ↦ ⟨p.1, φ ≫ p.2⟩`, which is a *total* function on pairs, so `congrArg` applies to it
directly. That is `Stacks.RelativeSpec.pullback_pairToHom_algebraHomPair`.

**The peeling steps are stated as `Iff`s between two vanishing statements, and applied with
`refine`, not `rw`.** The goal mentions the pair both through `Sigma.snd` and through the `0` of
the module that `Sigma.fst` names, so rewriting the pair needs both occurrences abstracted at
once. That is what `rw` does, and it is how
`Stacks.LineBundle.Situation.totalSpaceHomEquiv_snd_eq_zero_iff` is proved. Here, however, the
*concrete* goal — whose algebra sheaf is `(Stacks.Conormal.conormalSituation DY).algebraSheaf`,
reached from the situation's base only by unfolding `Situation.relativeSpecSituation` — is not
type-correct at `implicit` transparency, which is the transparency at which `rw` checks its
motive. So the pair-level rewrites are performed once and for all in
`Stacks.RelativeSpec.pullback_comp_pairToHom_algebraHomPair_app_eq_zero_iff` and
`Stacks.RelativeSpec.pullback_pairToHom_universalRelativeSpecPair_app_eq_zero_iff`, where
everything is abstract and the question does not arise, and the main proof applies those with
`refine`, which unifies at default transparency. The same consideration is why the value of the
first two algebra maps on the section is fed in as the hypothesis of
`Stacks.RelativeSpec.pullback_comp_pairToHom_algebraHomPair_app_eq_zero_of_eq` rather than
rewritten into the goal.

**No composition law for `Stacks.Conormal.normalConeMap` is used or proved.** A composite of two
morphisms of normal cones over different bases is presented as a single `pairToHom` of the
pulled-back pair, which is what `Stacks.RelativeSpec.comp_pairToHom` gives; comparing it with a
third `normalConeMap` would mean comparing two pairs whose first components are equal only
propositionally, and that comparison never occurs below.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B) {T : Scheme.{u}}

/-- **Pulling `Stacks.RelativeSpec.algebraHomPair` back is pulling the universal pair back and
then composing with the algebra map.** Both sides are the same pair reassociated, so this holds by
`rfl`; it is stated because the right-hand side is the shape to which
`Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom` applies. -/
theorem pullback_algebraHomPair (b : T ⟶ (gluedSpectrum (s.withAlgebra B hB)).scheme) :
    RelativeSpecPair.pullback b (algebraHomPair s B hB ψ) =
      ⟨(RelativeSpecPair.pullback b (universalRelativeSpecPair (s.withAlgebra B hB))).1,
        algebraHomAsUnder ψ ≫
          (RelativeSpecPair.pullback b (universalRelativeSpecPair (s.withAlgebra B hB))).2⟩ :=
  rfl

/-- **The pair of `Stacks.RelativeSpec.algebraHomPair` pulled back along the morphism of a pair
`q` is `q` with the algebra map precomposed.** This is the round-trip identity of
[Stacks, Tag 01LV] carried through the total function `p ↦ ⟨p.1, ψ ≫ p.2⟩` on pairs, so no
transport along the equality of first components is needed. -/
theorem pullback_pairToHom_algebraHomPair (q : RelativeSpecPair (s.withAlgebra B hB) T) :
    RelativeSpecPair.pullback (pairToHom q) (algebraHomPair s B hB ψ) =
      ⟨q.1, algebraHomAsUnder ψ ≫ q.2⟩ :=
  (pullback_algebraHomPair s B hB ψ (pairToHom q)).trans
    (congrArg (fun P : RelativeSpecPair (s.withAlgebra B hB) T =>
        (⟨P.1, algebraHomAsUnder ψ ≫ P.2⟩ : RelativeSpecPair s T))
      (pullback_universalRelativeSpecPair_pairToHom q))

/-- **One peeling step for the pair of a composite of morphisms of relative spectra**: pulling
`Stacks.RelativeSpec.algebraHomPair` back along `b ≫ pairToHom q` is pulling `q` back along `b`,
with the algebra map precomposed. -/
theorem pullback_comp_pairToHom_algebraHomPair (q : RelativeSpecPair (s.withAlgebra B hB) T)
    {T' : Scheme.{u}} (b : T' ⟶ T) :
    RelativeSpecPair.pullback (b ≫ pairToHom q) (algebraHomPair s B hB ψ) =
      ⟨(RelativeSpecPair.pullback b q).1,
        algebraHomAsUnder ψ ≫ (RelativeSpecPair.pullback b q).2⟩ :=
  (RelativeSpecPair.pullback_comp b (pairToHom q) (algebraHomPair s B hB ψ)).trans
    (congrArg (RelativeSpecPair.pullback b) (pullback_pairToHom_algebraHomPair s B hB ψ q))

/-- **The peeling step, read as an equivalence of two vanishing statements.** This is
`Stacks.RelativeSpec.pullback_comp_pairToHom_algebraHomPair` applied to a local section; stating it
here, where every object is abstract, is what lets a concrete consumer invoke it with `refine`
instead of rewriting a goal whose motive is not type-correct at `implicit` transparency. -/
theorem pullback_comp_pairToHom_algebraHomPair_app_eq_zero_iff
    (q : RelativeSpecPair (s.withAlgebra B hB) T) {T' : Scheme.{u}} (b : T' ⟶ T)
    (U : s.base.Opens) (ξ : AlgebraSheaf.sections s.algebra U) :
    (((RelativeSpecPair.pullback (b ≫ pairToHom q)
          (algebraHomPair s B hB ψ)).2.right.app (op U)).hom ξ = 0) ↔
      (((RelativeSpecPair.pullback b q).2.right.app (op U)).hom
        ((ψ.right.hom.app (op U)).hom ξ) = 0) := by
  rw [pullback_comp_pairToHom_algebraHomPair]
  exact Iff.rfl

/-- The peeling step with the value of the algebra map on the section supplied as a hypothesis,
which is how a consumer that has computed that value uses it. -/
theorem pullback_comp_pairToHom_algebraHomPair_app_eq_zero_of_eq
    (q : RelativeSpecPair (s.withAlgebra B hB) T) {T' : Scheme.{u}} (b : T' ⟶ T)
    (U : s.base.Opens) (ξ : AlgebraSheaf.sections s.algebra U)
    (η : AlgebraSheaf.sections B U) (hη : (ψ.right.hom.app (op U)).hom ξ = η)
    (h : ((RelativeSpecPair.pullback b q).2.right.app (op U)).hom η = 0) :
    ((RelativeSpecPair.pullback (b ≫ pairToHom q)
        (algebraHomPair s B hB ψ)).2.right.app (op U)).hom ξ = 0 :=
  (pullback_comp_pairToHom_algebraHomPair_app_eq_zero_iff s B hB ψ q b U ξ).mpr (hη ▸ h)

/-- **The last peeling step, read as an equivalence of two vanishing statements**: the universal
pair pulled back along the morphism of a pair `q` is `q`, by [Stacks, Tag 01LV]. -/
theorem pullback_pairToHom_universalRelativeSpecPair_app_eq_zero_iff
    (q : RelativeSpecPair s T) (U : s.base.Opens) (ζ : AlgebraSheaf.sections s.algebra U) :
    (((RelativeSpecPair.pullback (pairToHom q)
          (universalRelativeSpecPair s)).2.right.app (op U)).hom ζ = 0) ↔
      ((q.2.right.app (op U)).hom ζ = 0) := by
  rw [pullback_universalRelativeSpecPair_pairToHom]

end Stacks.RelativeSpec

namespace Stacks.Conormal

open Stacks.AffineAlgebraEquivalence

/-! ### The relative-spectrum pair of a morphism of normal cones -/

section Functorial

variable {Z X Y X' : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X') (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i'] (H : AlgebraicGeometry.ConormalAlgebraHom i i' f)
  [(conormalAlgebraSheaf i).IsQuasicoherent] [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- **The relative-spectrum pair of the morphism of normal cones `C_ZX ⟶ C_YX'`**: the projection
`C_ZX ⟶ Z` followed by `f`, together with `Stacks.Conormal.normalConePushforwardHom`. This is the
pair `Stacks.Conormal.normalConeMap` is defined by, named so that
`Stacks.RelativeSpec.comp_pairToHom` can be applied to a composite ending in it. -/
def normalConeMapPair : RelativeSpecPair (normalConeSituation i') (normalCone i) :=
  ⟨normalConeToBase i ≫ f,
    (conormalAlgebraSheaf i').pairHomEquiv (normalConeToBase i ≫ f)
      (normalConePushforwardHom i i' f H)⟩

/-- **The morphism of normal cones is the morphism attached to
`Stacks.Conormal.normalConeMapPair`.** This is its definition read through
`Stacks.RelativeSpec.pairToHom`. -/
theorem normalConeMap_eq_pairToHom :
    normalConeMap i i' f H = pairToHom (normalConeMapPair i i' f H) := rfl

/-- **The algebra datum of a morphism of normal cones, on a homogeneous local section**: it is the
homogeneous section of the same degree given by the sectionwise datum of `H`, viewed in the
structure sheaf of `C_ZX` through the universal algebra map. This is
`Stacks.Conormal.conormalAlgebraSheafPushforwardHom_ungradedIncl` with the remaining factor of
`Stacks.Conormal.normalConePushforwardHom` left in place. -/
theorem normalConeMapPair_snd_right_app_ungradedIncl (n : ℤ) (V : Y.Opens)
    (y : ((conormalAlgebra i').algebra.piece n).val.obj (op V)) :
    (((normalConeMapPair i i' f H).2.right.app (op V)).hom
        ((conormalAlgebra i').algebra.ungradedIncl n y)) =
      (((universalRelativeSpecPair (normalConeSituation i)).2.right.app (op (f ⁻¹ᵁ V))).hom
        ((conormalAlgebra i).algebra.ungradedIncl n (H.map n (f ⁻¹ᵁ V) V le_rfl y))) :=
  congrArg
    (fun t => ((universalAlgebraMap (normalConeSituation i)).right.app (op (f ⁻¹ᵁ V))).hom t)
    (conormalAlgebraSheafPushforwardHom_ungradedIncl i i' f H n V y)

/-- `Stacks.Conormal.normalConeMapPair_snd_right_app_ungradedIncl` after a further pullback along
a morphism `b` into the normal cone: `b` contributes its comorphism to both sides. -/
theorem pullback_normalConeMapPair_snd_right_app_ungradedIncl {T : Scheme.{u}}
    (b : T ⟶ normalCone i) (n : ℤ) (V : Y.Opens)
    (y : ((conormalAlgebra i').algebra.piece n).val.obj (op V)) :
    (((RelativeSpecPair.pullback b (normalConeMapPair i i' f H)).2.right.app (op V)).hom
        ((conormalAlgebra i').algebra.ungradedIncl n y)) =
      (((RelativeSpecPair.pullback b
          (universalRelativeSpecPair (normalConeSituation i))).2.right.app (op (f ⁻¹ᵁ V))).hom
        ((conormalAlgebra i).algebra.ungradedIncl n (H.map n (f ⁻¹ᵁ V) V le_rfl y))) :=
  congrArg (fun t => (b.c.app (op (normalConeToBase i ⁻¹ᵁ (f ⁻¹ᵁ V)))).hom t)
    (normalConeMapPair_snd_right_app_ungradedIncl i i' f H n V y)

omit [(conormalAlgebraSheaf i).IsQuasicoherent] in
/-- **The Tag 0637 morphism `C_ZX ⟶ N_ZX` is the morphism attached to
`Stacks.RelativeSpec.algebraHomPair` of the canonical map `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}.`** This is
its definition read through `Stacks.RelativeSpec.pairToHom`. -/
theorem normalConeToNormalBundle_eq_pairToHom
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra i)]
    [hci : (conormalAlgebraSheaf i).IsQuasicoherent] :
    normalConeToNormalBundle i =
      pairToHom (algebraHomPair (normalBundleSituation i) (conormalAlgebraSheaf i) hci
        (conormalSymmetricAlgebraSheafHom i)) := rfl

end Functorial

section Square

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (p : Z ⟶ Z') (g : X ⟶ X')
  [IsImmersion i] [IsImmersion i']
  [(conormalAlgebraSheaf i).IsQuasicoherent] [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- The canonical morphism of normal cones over a commutative square is the morphism attached to
`Stacks.Conormal.normalConeMapPair` of the canonical map of conormal graded algebras. -/
theorem normalConeMapOfSquare_eq_pairToHom (comm : p ≫ i' = i ≫ g) :
    normalConeMapOfSquare i i' p g comm =
      pairToHom (normalConeMapPair i i' p
        (AlgebraicGeometry.conormalAlgebraHom i i' p g comm).hom) := rfl

end Square

section Factorization

variable {Z Y X : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X) (p : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i']
  [(conormalAlgebraSheaf i).IsQuasicoherent] [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- The canonical morphism `C_ZX ⟶ C_YX` of a nested pair is the morphism attached to
`Stacks.Conormal.normalConeMapPair` of the canonical map of conormal graded algebras. -/
theorem normalConeMapOfFactorization_eq_pairToHom (hp : p ≫ i' = i) :
    normalConeMapOfFactorization i i' p hp =
      pairToHom (normalConeMapPair i i' p
        (AlgebraicGeometry.conormalAlgebraHom i i' p (𝟙 X)
          (hp.trans (Category.comp_id i).symm)).hom) := rfl

end Factorization

/-! ### The factorization through the zero section -/

section Nested

variable {X : Scheme.{u}} (DY : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra DY.subschemeι)]
  [(conormalAlgebraSheaf DY.subschemeι).IsQuasicoherent]
  {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  [(conormalAlgebraSheaf iZ).IsQuasicoherent]
  (f : Z ⟶ DY.subscheme) [IsClosedImmersion f]
  [(conormalAlgebraSheaf f).IsQuasicoherent] (hf : f ≫ DY.subschemeι = iZ)

/-- **The composite `C_ZY ⟶ C_ZX ⟶ C_YX` factors through the zero section `o : Y ⟶ C_YX`**, for
closed subschemes `Z ⊆ Y ⊆ X` with `Y ⊆ X` an effective Cartier divisor: it is the projection
`C_ZY ⟶ Z ⟶ Y` followed by `o`.

This is the hypothesis `hzero` that [Stacks, Tag 0FEB] needs in order to view `C_ZY` as a closed
subscheme of `Y ×_{o, C_YX} C_ZX`, and it is no longer a hypothesis. By
`Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens` it is equivalent
to the vanishing, over the affine opens of `Y` and in degree one, of the algebra datum of the
relative-spectrum pair of the composite; that datum is the canonical composite
`𝒞_{Y/X,1} ⟶ 𝒞_{Z/X,1} ⟶ 𝒞_{Z/Y,1}` of [Stacks, Tag 0634] read into the structure sheaf of
`C_ZY`, and the canonical composite is zero by
`AlgebraicGeometry.conormalAlgebraHom_comp_map_eq_zero`. The implementation notes of this file
describe the computation. -/
theorem normalConeNested_eq_comp_normalConeZeroSection :
    normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι ((Category.id_comp iZ).trans hf.symm) ≫
        normalConeMapOfFactorization iZ DY.subschemeι f hf =
      normalConeToBase f ≫ f ≫ normalConeZeroSection DY := by
  rw [normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens]
  intro U x
  -- The value of the two comparison maps `Sym(𝒞_{Y/X}) ⟶ 𝒞_{Y/X,*}` on a degree-one section.
  have hval :
      (((conormalSymmetricAlgebraSheafHom DY.subschemeι).right.hom.app (op U.1)).hom
          ((((conormalSituation DY).algebraSheafIsoSymmetricAlgebraSheaf.hom.right.hom).app
              (op U.1)).hom
            ((conormalSituation DY).algebraSheafIncl 1 U.1
              ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x)))) =
        (conormalAlgebra DY.subschemeι).algebra.ungradedIncl 1
          (((conormalSymmetricHom DY.subschemeι).app 1).val.app (op U.1)
            ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x)) :=
    (congrArg (((conormalSymmetricAlgebraSheafHom DY.subschemeι).right.hom.app (op U.1)).hom)
        (Stacks.RelativeSpec.ungradedToGradedRight_ungradedAlgebraSheafIncl DY.subscheme
          (conormalSituation DY).symmetricAlgebra
          (conormalSituation DY).symmetricAlgebra_mul_comm 1 U.1
          ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x))).trans
      (conormalSymmetricAlgebraSheafHom_ungradedIncl DY.subschemeι 1 U.1
        ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x))
  -- The canonical composite `𝒞_{Y/X,1} ⟶ 𝒞_{Z/X,1} ⟶ 𝒞_{Z/Y,1}` kills that section.
  have hv : (AlgebraicGeometry.conormalAlgebraHom f iZ (𝟙 Z) DY.subschemeι
          ((Category.id_comp iZ).trans hf.symm)).hom.map (1 : ℤ)
          ((𝟙 Z) ⁻¹ᵁ (f ⁻¹ᵁ U.1)) (f ⁻¹ᵁ U.1) le_rfl
        ((AlgebraicGeometry.conormalAlgebraHom iZ DY.subschemeι f (𝟙 X)
            (hf.trans (Category.comp_id iZ).symm)).hom.map (1 : ℤ) (f ⁻¹ᵁ U.1) U.1 le_rfl
          (((conormalSymmetricHom DY.subschemeι).app 1).val.app (op U.1)
            ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x))) = 0 :=
    AlgebraicGeometry.conormalAlgebraHom_comp_map_eq_zero DY.subschemeι f hf 1 one_ne_zero U.1
      le_rfl _
  -- Present each of the three factors as the morphism of a relative-spectrum pair.
  rw [normalConeMapOfSquare_eq_pairToHom, normalConeMapOfFactorization_eq_pairToHom,
    normalConeToNormalBundle_eq_pairToHom]
  -- Peel the pairs off one factor at a time.
  refine (pullback_comp_pairToHom_algebraHomPair_app_eq_zero_iff ..).mpr ?_
  refine pullback_comp_pairToHom_algebraHomPair_app_eq_zero_of_eq _ _ _ _ _ _ _ _ _ hval ?_
  refine Eq.trans (pullback_normalConeMapPair_snd_right_app_ungradedIncl ..) ?_
  refine (pullback_pairToHom_universalRelativeSpecPair_app_eq_zero_iff ..).mpr ?_
  refine Eq.trans (normalConeMapPair_snd_right_app_ungradedIncl ..) ?_
  -- What is left is the vanishing, carried through the inclusion of a homogeneous section and a
  -- ring map.
  refine Eq.trans (congrArg (((universalRelativeSpecPair (normalConeSituation f)).2.right.app
      (op ((𝟙 Z) ⁻¹ᵁ (f ⁻¹ᵁ U.1)))).hom)
    (Eq.trans (congrArg ((conormalAlgebra f).algebra.ungradedIncl 1) hv)
      ((conormalAlgebra f).algebra.toPresheafGradedAlgebra.inclSheaf_zero _ 1))) (map_zero _)

end Nested

end Stacks.Conormal

end
