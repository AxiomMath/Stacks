module

public import StacksFrontier.AlgebraicGeometry.SymmetricDehomogenize.UnitScaling

/-!
# The dehomogenization of the symmetric algebra is compatible with shrinking the test scheme

`Stacks.SymmetricDehomogenize.dehomogenize g F κ U φ` is a ring homomorphism
`Γ(U, Sym F) ⟶ B` built from a morphism `κ : F ⟶ g_*𝒪_X` and a ring homomorphism `φ` out of
`Γ(X, g⁻¹U)`. **This file compares two such dehomogenizations along a morphism of test schemes.**

Let `h : X' ⟶ X` and `g' = h ≫ g`. Restricting functions along `h` is a morphism
`g_*𝒪_X ⟶ g'_*𝒪_{X'}` of `𝒪_T`-modules, the same morphism in every degree of
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitGradedAlgebra`, and therefore a
unital homomorphism of graded algebras. Composing the graded map of `κ` with it is a unital
homomorphism out of `Sym F` whose degree-one part is `κ` followed by restriction; so if `κ'` is
that composite then, by the uniqueness of `desc`, the graded map of `κ'` **is** the graded map of
`κ` followed by restriction — in every degree at once, which is the only way to get it, since
`desc` has no formula per degree.

The dehomogenizations then differ only by the bookkeeping of the two `φ`s, and
`Stacks.SymmetricDehomogenize.dehomogenize_comp_resRingHom` reduces their comparison to a single
hypothesis about those: that the given ring homomorphism `ψ : B ⟶ B'` carries `φ` to `φ'`
composed with `AlgebraicGeometry.Scheme.Hom.appLE` of `h`.

## Why this is the shape of the statement

The consumer is the gluing of the local sections of a projective bundle, where `g` and `g'` are
the inclusions of two affine opens `W ⊆ V` of the base, `U = V`, `U' = W` and `ψ` is the
restriction of global functions from `V` to `W`. There the hypothesis on the `φ`s is a pure
structure-sheaf identity between two factorizations of one `appLE`, and the hypothesis on `κ` is
the statement that the trivialized quotient over `V` restricts to the one over `W`. Both halves
are separated out here so that neither has to be done inside a `Proj` computation.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitRes`: **restriction of
  functions along `h`**, as a morphism `g_*𝒪_X ⟶ g'_*𝒪_{X'}` of `𝒪_T`-modules.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.resAppLE`: the ring homomorphism
  `Γ(X, g⁻¹S) ⟶ Γ(X', g'⁻¹S)` it is on sections over `S`, namely `appLE` of `h`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitResScale`: that morphism read
  as a unital homomorphism of graded algebras, the same map in every degree.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.ofPushforwardUnit_pushforwardUnitRes_app`:
  **on sections, the morphism is `appLE` of `h`.** Everything in its construction is
  definitional on sections except the unit law of the structure sheaf, so this is one `congrArg`.
* `Stacks.SymmetricDehomogenize.gradedHom_comp_pushforwardUnitRes`: **the graded map of a
  restricted trivialization is the graded map followed by restriction**, in every degree at
  once, by the uniqueness of `desc`.
* `Stacks.SymmetricDehomogenize.ofPushforwardUnit_gradedHom_app_res`: the degree-`n` coefficient
  of the restricted dehomogenization, on a restricted homogeneous section.
* `Stacks.SymmetricDehomogenize.dehomogenize_comp_resRingHom`: **the comparison of the two
  dehomogenizations**, given the hypothesis on `κ` and the hypothesis on the `φ`s.

## Implementation notes

The morphism `𝒪_X ⟶ h_*𝒪_{X'}` out of which `pushforwardUnitRes` is built is written as
`SheafOfModules.unitHomEquiv.symm` of the unit section rather than as the existing
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`. The two are the same morphism, but the
`unitHomEquiv` spelling is the one whose value on a section `x` is `x • 1`, which is exactly what
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.ofPushforwardUnit_smul_of_eq_one` computes; with
the other spelling the section formula is no longer one `congrArg`. No second name is introduced
for it: the morphism appears only inside `pushforwardUnitRes`.

The composite `h ≫ g` is related to `g'` by a hypothesis rather than being used directly,
because the consumer has `h ≫ V.ι = W.ι` as a theorem (`AlgebraicGeometry.Scheme.homOfLE_ι`) and
not as a definition; `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` localizes the transport
into the definition, where its component is a presheaf restriction along an equality of opens and
therefore invisible in the section formula.

`rw` is unusable on several of these goals: `AlgebraicGeometry.Scheme.Modules` is a `def`
carrying its own `Category` instance, and the pieces of a graded algebra are definitionally but
not syntactically the direct image, so the rewrite motive is reported as not type-correct at
`implicit` transparency. The proofs are therefore term-style — `Eq.trans` of `congrArg`s, with
`show` where a type has to be chosen — and the lemmas stated with the arguments explicit, so that
elaboration performs the coercion that unification would refuse.

No `@[stacks]` attribute is attached. This is a naturality property of a construction that feeds
the classifying morphism of [Stacks, Tag 01NA]; it asserts no part of that tag, and Tag 0B3V's
bijection is not reached here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

variable {X X' T : Scheme.{u}} (g : X ⟶ T) (h : X' ⟶ X)

/-- **Restriction of functions along `h`, as a morphism `g_*𝒪_X ⟶ g'_*𝒪_{X'}`** of
`𝒪_T`-modules, for `g' = h ≫ g`. It is the direct image along `g` of the structure map of `h`,
followed by the identification of the iterated direct image with the direct image of the
composite. -/
public def pushforwardUnitRes {g' : X' ⟶ T} (hg : h ≫ g = g') :
    pushforwardUnit g ⟶ pushforwardUnit g' :=
  (Scheme.Modules.pushforward g).map
      ((pushforwardUnit h).unitHomEquiv.symm (pushforwardUnitOne h)) ≫
    (Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr hg).hom.app (SheafOfModules.unit X'.ringCatSheaf)

/-- The inverse image of an open of `T` under `g' = h ≫ g` is the inverse image under `h` of its
inverse image under `g`. -/
public theorem preimage_eq_of_comp {g' : X' ⟶ T} (hg : h ≫ g = g') (S : T.Opens) :
    g' ⁻¹ᵁ S = h ⁻¹ᵁ (g ⁻¹ᵁ S) :=
  hg ▸ rfl

/-- Monotonicity of the previous identity: the inverse image under `g'` of a smaller open of `T`
lies inside the inverse image under `h` of the inverse image under `g` of a larger one. -/
public theorem preimage_le_preimage_of_comp {g' : X' ⟶ T} (hg : h ≫ g = g') {U U' : T.Opens}
    (hU : U' ≤ U) : g' ⁻¹ᵁ U' ≤ h ⁻¹ᵁ (g ⁻¹ᵁ U) :=
  (preimage_eq_of_comp g h hg U').le.trans fun _ hx => hU hx

/-- **The ring homomorphism `pushforwardUnitRes` is on sections over `S`**: the structure map of
`h` from the inverse image of `S` under `g` to its inverse image under `g'`. -/
public def resAppLE {g' : X' ⟶ T} (hg : h ≫ g = g') (S : T.Opens) :
    Γ(X, g ⁻¹ᵁ S) ⟶ Γ(X', g' ⁻¹ᵁ S) :=
  h.appLE (g ⁻¹ᵁ S) (g' ⁻¹ᵁ S) (preimage_eq_of_comp g h hg S).le

/-- **On sections, `pushforwardUnitRes` is `AlgebraicGeometry.Scheme.Hom.appLE` of `h`.** The
identification of the iterated direct image is the identity on sections and the transport along
`h ≫ g = g'` is a restriction between equal opens, so the only content is that the structure map
of `h` applied to `x` is `x` times the unit. -/
public theorem ofPushforwardUnit_pushforwardUnitRes_app {g' : X' ⟶ T} (hg : h ≫ g = g')
    (S : T.Opensᵒᵖ) (x : (pushforwardUnit g).val.obj S) :
    ofPushforwardUnit g' ((pushforwardUnitRes g h hg).val.app S x) =
      (resAppLE g h hg S.unop).hom (ofPushforwardUnit g x) := by
  subst hg
  exact congrArg (X'.presheaf.map (homOfLE (le_refl ((h ≫ g) ⁻¹ᵁ S.unop))).op).hom
    (ofPushforwardUnit_smul_of_eq_one h (g ⁻¹ᵁ S.unop) x _ rfl)

/-- Restriction is multiplicative, the multiplications being those of the two structure
sheaves. -/
public theorem ofPushforwardUnit_pushforwardUnitRes_mul {g' : X' ⟶ T} (hg : h ≫ g = g')
    (S : T.Opensᵒᵖ) (x y : (pushforwardUnit g).val.obj S) :
    ofPushforwardUnit g'
        ((pushforwardUnitRes g h hg).val.app S ((pushforwardUnitMul g).app S x y)) =
      ofPushforwardUnit g' ((pushforwardUnitMul g').app S
        ((pushforwardUnitRes g h hg).val.app S x)
        ((pushforwardUnitRes g h hg).val.app S y)) := by
  rw [ofPushforwardUnit_pushforwardUnitRes_app, ofPushforwardUnit_pushforwardUnitMul_app,
    ofPushforwardUnit_pushforwardUnitMul_app, ofPushforwardUnit_pushforwardUnitRes_app,
    ofPushforwardUnit_pushforwardUnitRes_app]
  exact map_mul _ _ _

/-- Restriction carries the unit section to the unit section. -/
public theorem ofPushforwardUnit_pushforwardUnitRes_one {g' : X' ⟶ T} (hg : h ≫ g = g')
    (S : T.Opensᵒᵖ) :
    ofPushforwardUnit g'
        ((pushforwardUnitRes g h hg).val.app S ((pushforwardUnitOne g).eval S)) =
      ofPushforwardUnit g' ((pushforwardUnitOne g').eval S) := by
  rw [ofPushforwardUnit_pushforwardUnitRes_app, ofPushforwardUnit_pushforwardUnitOne_eval,
    ofPushforwardUnit_pushforwardUnitOne_eval]
  exact map_one _

/-- **Restriction along `h`, as a unital homomorphism of graded algebras of the two direct
images**: the same morphism in every degree. Both laws are the two previous lemmas, every piece
of either graded algebra being the direct image itself. -/
public def pushforwardUnitResScale {g' : X' ⟶ T} (hg : h ≫ g = g') :
    SheafOfModules.GradedAlgebra.UnitalHom (pushforwardUnitGradedAlgebra g)
      (pushforwardUnitGradedAlgebra g') where
  app _ := pushforwardUnitRes g h hg
  map_mul _ _ S x y :=
    ofPushforwardUnit_injective g' (ofPushforwardUnit_pushforwardUnitRes_mul g h hg S x y)
  map_one S :=
    ofPushforwardUnit_injective g' (ofPushforwardUnit_pushforwardUnitRes_one g h hg S)

/-- In every degree `n`, the component of `pushforwardUnitResScale g h hg` is the restriction
`pushforwardUnitRes g h hg`. -/
@[simp]
public theorem pushforwardUnitResScale_app {g' : X' ⟶ T} (hg : h ≫ g = g') (n : ℤ) :
    (pushforwardUnitResScale g h hg).app n = pushforwardUnitRes g h hg :=
  rfl

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

namespace Stacks.SymmetricDehomogenize

open Stacks.AlgebraicGeometry.ProjF1Dehomogenization

variable {X X' T : Scheme.{u}} (g : X ⟶ T) (h : X' ⟶ X)

/-- **The graded map of a restricted trivialization is the graded map followed by restriction.**
Both sides are unital homomorphisms out of the symmetric algebra extending `κ` followed by
restriction in degree one, and `desc` is unique; there is no formula for the degree-`n`
component of either side, and the equality holds in every degree at once. -/
public theorem gradedHom_comp_pushforwardUnitRes {g' : X' ⟶ T} (hg : h ≫ g = g')
    (F : T.Modules) (κ : F ⟶ pushforwardUnit g) (κ' : F ⟶ pushforwardUnit g')
    (hκ : κ ≫ pushforwardUnitRes g h hg = κ') :
    gradedHom g' F κ' = (gradedHom g F κ).comp (pushforwardUnitResScale g h hg) :=
  ((isSymmetricAlgebra_symmetricAlgebra T F).isUniversal.desc_unique
    (pushforwardUnitGradedAlgebra g') _ (pairwiseCommutes_pushforwardUnit g' F _)
    (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ pushforwardUnitRes g h hg) (gradedHom_degree_one g F κ))).trans hκ)).symm

/-- **The degree-`n` coefficient of the restricted dehomogenization, on a restricted homogeneous
section.** The previous lemma replaces the graded map of `κ'` by the graded map of `κ` followed
by restriction, naturality of the latter moves the restriction of the homogeneous section past
it, and the two restrictions compose into one `appLE` by
`AlgebraicGeometry.Scheme.Hom.map_appLE`. -/
public theorem ofPushforwardUnit_gradedHom_app_res {g' : X' ⟶ T} (hg : h ≫ g = g')
    (F : T.Modules) (κ : F ⟶ pushforwardUnit g) (κ' : F ⟶ pushforwardUnit g')
    (hκ : κ ≫ pushforwardUnitRes g h hg = κ')
    {U U' : T.Opens} (hU : U' ≤ U) (n : ℤ)
    (y : ((Scheme.Modules.symmetricAlgebra T F).piece n).val.obj (op U)) :
    ofPushforwardUnit g' (((gradedHom g' F κ').app n).val.app (op U')
        (((Scheme.Modules.symmetricAlgebra T F).piece n).val.map (homOfLE hU).op y)) =
      (h.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ U') (preimage_le_preimage_of_comp g h hg hU)).hom
        (ofPushforwardUnit g (((gradedHom g F κ).app n).val.app (op U) y)) := by
  refine Eq.trans (congrArg (fun Θ : SheafOfModules.GradedAlgebra.UnitalHom
      (Scheme.Modules.symmetricAlgebra T F) (pushforwardUnitGradedAlgebra g') =>
      ofPushforwardUnit g' ((Θ.app n).val.app (op U')
        (((Scheme.Modules.symmetricAlgebra T F).piece n).val.map (homOfLE hU).op y)))
      (gradedHom_comp_pushforwardUnitRes g h hg F κ κ' hκ)) ?_
  refine Eq.trans (ofPushforwardUnit_pushforwardUnitRes_app g h hg (op U')
    (((gradedHom g F κ).app n).val.app (op U')
      (((Scheme.Modules.symmetricAlgebra T F).piece n).val.map (homOfLE hU).op y))) ?_
  refine Eq.trans (congrArg (fun z => (resAppLE g h hg U').hom (ofPushforwardUnit g z))
    (PresheafOfModules.naturality_apply ((gradedHom g F κ).app n).val (homOfLE hU).op y)) ?_
  exact congrArg (fun φ : Γ(X, g ⁻¹ᵁ U) ⟶ Γ(X', g' ⁻¹ᵁ U') =>
      φ.hom (ofPushforwardUnit g (((gradedHom g F κ).app n).val.app (op U) y)))
    (Scheme.Hom.map_appLE h (preimage_eq_of_comp g h hg U').le
      (homOfLE (fun _ hx => hU hx) : (g ⁻¹ᵁ U') ⟶ (g ⁻¹ᵁ U)).op)

/-- **The dehomogenization of `Sym F` is compatible with shrinking the test scheme and the
open.** Given that the trivialization over `X` restricts to the one over `X'`, and that `ψ`
carries `φ` to `φ'` composed with the structure map of `h`, the dehomogenization over `U`
followed by `ψ` is restriction of homogeneous sections followed by the dehomogenization over
`U'`.

Both sides are ring homomorphisms out of a direct sum, so it is enough to compare them on a
homogeneous summand, where the comparison is the previous lemma. -/
public theorem dehomogenize_comp_resRingHom {g' : X' ⟶ T} (hg : h ≫ g = g')
    (F : T.Modules) (hqc : IsQuasicoherentPieces F)
    (κ : F ⟶ pushforwardUnit g) (κ' : F ⟶ pushforwardUnit g')
    (hκ : κ ≫ pushforwardUnitRes g h hg = κ')
    {U U' : T.Opens} (hU : U' ≤ U) {B B' : Type u} [CommRing B] [CommRing B']
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) →+* B)
    (φ' : X'.ringCatSheaf.obj.obj (op (g' ⁻¹ᵁ U')) →+* B') (ψ : B →+* B')
    (hψ : ∀ z, ψ (φ z) =
      φ' ((h.appLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ U')
        (preimage_le_preimage_of_comp g h hg hU)).hom z)) :
    ψ.comp (dehomogenize g F κ U φ hqc) =
      (dehomogenize g' F κ' U' φ' hqc).comp
        ((schemeSheafGradedAlgebra F hqc).resRingHom hU) := by
  refine DFunLike.ext _ _ fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | of n y =>
    rw [RingHom.comp_apply, RingHom.comp_apply, dehomogenize_of,
      (schemeSheafGradedAlgebra F hqc).resRingHom_of hU, dehomogenize_of]
    exact (hψ _).trans
      (congrArg φ' (ofPushforwardUnit_gradedHom_app_res g h hg F κ κ' hκ hU (n : ℤ) y).symm)

end Stacks.SymmetricDehomogenize

end
