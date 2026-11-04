module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Functorial
public import StacksCore.Tactic.StacksAttribute

/-!
# The tangent space is the dual of the stalk of relative differentials

Let `f : X ⟶ S` be a morphism of schemes and let `x` be a point of `X`. The relative tangent
space at `x` — the vector space of dual-number arrows into `X` over `S` extending the
residue-field point `x` — is canonically the `𝒪_{X,x}`-linear dual of the stalk at `x` of the
sheaf of relative differentials, with values in the residue field `κ(x)`:
`T_{X/S,x} = Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))`, an isomorphism of `κ(x)`-vector spaces.

## Main definitions

* `AlgebraicGeometry.CotangentSpace`: the dual `Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))`.
* `AlgebraicGeometry.pullbackInfinitesimalCoefficient`: the coefficient of `ε` in the pullback
  of a local section of `𝒪_X` along a dual-number arrow.

## Main results

* `AlgebraicGeometry.tangentSpaceEquivCotangentSpace`: the canonical `κ(x)`-linear equivalence
  between the relative tangent space and that dual.
* `AlgebraicGeometry.tangentSpaceEquivCotangentSpace_apply_germ`: the equivalence evaluated on
  the germ of a universal relative differential `d a` returns the coefficient of `ε` in the
  pullback of `a`, which is what makes it canonical.

## Implementation notes

A dual-number arrow is the same data as a derivation of `𝒪_{X,x}` into `κ(x)` annihilating the
image of `𝒪_{S,f x}` — this is `AlgebraicGeometry.dottedDerivationEquiv` — and such a derivation
is the same data as an `𝒪_{S,f x}`-derivation of `𝒪_{X,x}`, because the two annihilation
conditions coincide: `AlgebraicGeometry.tangentDerivationsEquiv`. On the other side the stalk of
relative differentials is `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` by
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, so its dual is the
derivations, by `KaehlerDifferential.linearMapEquivDerivation`. The equivalence is the composite
of these three, and the germ formula is read off by tracing a universal differential through it.

None of the module structures involved is found by instance search: the local ring at `x` acts on
`κ(x)` through the residue map, the local ring of `S` at `f x` acts on both through the stalk map
of `f`, and `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is a definition that synthesis
does not unfold. They are therefore named and declared as instances local to this file, so that
the statements below carry no instance preamble; the actions are the ones that
`AlgebraicGeometry.tangentDerivations` is stated over.

## References

* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
* [Stacks Project, Tag 0B2B](https://stacks.math.columbia.edu/tag/0B2B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules
open IsLocalRing
open Stacks.RelativeDifferentialStalkMap
open Stacks.SmoothAtJacobian (relativeDifferentialStalk relativeDifferentialStalkModule)

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-! ### The actions on the residue field and on the stalk of differentials -/

/-- The local ring at `x` acts on the residue field `κ(x)` through the residue map. This is the
action that `AlgebraicGeometry.tangentDerivations` is stated over. -/
noncomputable abbrev residueModule :
    Module (X.presheaf.stalk x) (X.residueField x) :=
  Module.compHom _ (X.residue x).hom

attribute [local instance] residueModule

/-- Scalars from `κ(x)` and from the local ring at `x` commute on `κ(x)`. -/
noncomputable abbrev residueSMulComm :
    SMulCommClass (X.residueField x) (X.presheaf.stalk x) (X.residueField x) :=
  ⟨by
    intro r a v
    change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
    ring⟩

/-- Scalars from the local ring at `x` and from `κ(x)` commute on `κ(x)`. -/
noncomputable abbrev residueSMulComm' :
    SMulCommClass (X.presheaf.stalk x) (X.residueField x) (X.residueField x) :=
  ⟨by
    intro a r v
    change (X.residue x a) * (r * v) = r * ((X.residue x a) * v)
    ring⟩

attribute [local instance] residueSMulComm residueSMulComm'

/-- `𝒪_{X,x}` as an algebra over `𝒪_{S,f x}`, through the stalk map of `f`. This is
`Stacks.RelativeDifferentialStalkMap.algebraStalkMap`, named again at the spelling
`X.presheaf.stalk x` of the stalk of the structure sheaf that the tangent-space material uses. -/
noncomputable abbrev stalkMapAlgebra :
    Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
  algebraStalkMap f x

attribute [local instance] stalkMapAlgebra

/-- The local ring of `S` at `f x` acts on `κ(x)` through the stalk map of `f` followed by the
residue map. -/
noncomputable abbrev baseResidueModule :
    Module (S.presheaf.stalk (f.base x)) (X.residueField x) :=
  Module.compHom _ ((X.residue x).hom.comp (f.stalkMap x).hom)

attribute [local instance] baseResidueModule

/-- Scalars from the local ring of `S` at `f x` and from `κ(x)` commute on `κ(x)`. -/
noncomputable abbrev baseResidueSMulComm :
    SMulCommClass (S.presheaf.stalk (f.base x)) (X.residueField x) (X.residueField x) :=
  ⟨by
    intro s r v
    change (X.residue x ((f.stalkMap x) s)) * (r * v) =
      r * ((X.residue x ((f.stalkMap x) s)) * v)
    ring⟩

/-- `κ(x)` is a scalar tower over the stalk map of `f`: the action of the local ring of `S` at
`f x` on `κ(x)` is the one obtained through the local ring of `X` at `x`. -/
noncomputable abbrev residueIsScalarTower :
    IsScalarTower (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Decidable equality of the indices of the neighbourhood filter at `x`, needed to compute the
stalk of the sheaf of relative differentials as a colimit. There is no constructive instance, so
it is supplied classically. -/
noncomputable abbrev openNhdsDecidableEq :
    DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) :=
  Classical.decEq _

attribute [local instance] baseResidueSMulComm residueIsScalarTower openNhdsDecidableEq
attribute [local instance] relativeDifferentialStalkModule

/-! ### Tangent derivations are relative derivations of the local ring -/

/-- **A tangent derivation at `x` is the same data as an `𝒪_{S,f x}`-derivation of `𝒪_{X,x}` with
values in `κ(x)`.** The two conditions coincide: annihilating the image of the stalk map of `f`
is annihilating the structural map of the algebra `𝒪_{S,f x} → 𝒪_{X,x}`. -/
noncomputable def tangentDerivationsEquiv :
    tangentDerivations f x ≃ₗ[X.residueField x]
      Derivation (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x) where
  toFun D :=
    { toLinearMap :=
        { toFun := D.val
          map_add' := D.val.map_add
          map_smul' := by
            intro s a
            have hz : D.val (algebraMap (ToType (S.presheaf.stalk (f.base x)))
                (ToType (X.presheaf.stalk x)) s) = 0 := D.property s
            calc D.val (s • a)
                = D.val (algebraMap (ToType (S.presheaf.stalk (f.base x)))
                    (ToType (X.presheaf.stalk x)) s * a) := by rw [Algebra.smul_def]
              _ = _ • D.val a + a • D.val (algebraMap _ _ s) := D.val.leibniz _ _
              _ = _ := by
                  rw [hz, smul_zero, add_zero, RingHom.id_apply,
                    IsScalarTower.algebraMap_smul] }
      map_one_eq_zero' := D.val.map_one_eq_zero
      leibniz' := D.val.leibniz }
  invFun D := ⟨D.restrictScalars ℤ, D.map_algebraMap⟩
  left_inv _ := Subtype.ext <| Derivation.ext fun _ => rfl
  right_inv _ := Derivation.ext fun _ => rfl
  map_add' _ _ := Derivation.ext fun _ => rfl
  map_smul' _ _ := Derivation.ext fun _ => rfl

/-- `AlgebraicGeometry.tangentDerivationsEquiv` does not change the underlying function. -/
theorem tangentDerivationsEquiv_apply (D : tangentDerivations f x)
    (a : X.presheaf.stalk x) :
    tangentDerivationsEquiv f x D a = D.val a :=
  rfl

/-- **The dual-number arrows at `x` are the same data as the tangent derivations at `x`**,
linearly over the residue field: the vector space structure of Tag 0B2B is transported along
`AlgebraicGeometry.dottedDerivationEquiv`. -/
noncomputable def dottedDerivationLinearEquiv :
    DottedTangentArrow f x ≃ₗ[X.residueField x] tangentDerivations f x where
  toEquiv := dottedDerivationEquiv f x
  map_add' := dottedToDerivation_add f x
  map_smul' := dottedToDerivation_smul f x

/-! ### The cotangent space -/

/-- **The cotangent space of `f` at `x`**: the `𝒪_{X,x}`-linear dual
`Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))` of the stalk of the sheaf of relative differentials, with
values in the residue field. -/
noncomputable abbrev CotangentSpace : Type u :=
  relativeDifferentialStalk f x →ₗ[X.presheaf.stalk x] X.residueField x

/-- **The cotangent space is the module of `𝒪_{S,f x}`-derivations of `𝒪_{X,x}` into `κ(x)`.**
The stalk of the relative differentials is `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` by Tag 01V0 at a point, and
the `𝒪_{X,x}`-linear dual of the Kähler differentials is the derivations. -/
noncomputable def cotangentSpaceEquivDerivation :
    CotangentSpace f x ≃ₗ[X.residueField x]
      Derivation (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x) :=
  let E : relativeDifferentialStalk f x ≃ₗ[X.presheaf.stalk x]
      KaehlerDifferential (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) :=
    relativeDifferentialsStalkKaehlerEquiv f x
  let dualκ : CotangentSpace f x ≃ₗ[X.residueField x]
      (KaehlerDifferential (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) →ₗ[X.presheaf.stalk x] X.residueField x) :=
    { toEquiv := (LinearEquiv.arrowCongr E (LinearEquiv.refl _ _)).toEquiv
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let derivκ :
      (KaehlerDifferential (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) →ₗ[X.presheaf.stalk x] X.residueField x)
        ≃ₗ[X.residueField x]
      Derivation (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x) :=
    { toEquiv := (KaehlerDifferential.linearMapEquivDerivation
        (ToType (S.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x))
        (M := ToType (X.residueField x))).toEquiv
      map_add' := fun _ _ => Derivation.ext fun _ => rfl
      map_smul' := fun _ _ => Derivation.ext fun _ => rfl }
  dualκ.trans derivκ

/-- The inverse of `AlgebraicGeometry.cotangentSpaceEquivDerivation` lifts a derivation through
the identification of the stalk of relative differentials with the Kähler differentials of the
stalk map. -/
theorem cotangentSpaceEquivDerivation_symm_apply
    (D : Derivation (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x))
    (ω : relativeDifferentialStalk f x) :
    (cotangentSpaceEquivDerivation f x).symm D ω =
      D.liftKaehlerDifferential (relativeDifferentialsStalkKaehlerEquiv f x ω) :=
  rfl

/-! ### The identification of Tag 0B2D -/

/-- The coefficient of `ε` in a local section of `𝒪_X` pulled back along a dual-number arrow.
The hypothesis `hU` says that the arrow factors through the open set on which the section is
defined. -/
noncomputable def pullbackInfinitesimalCoefficient {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (θ : DottedTangentArrow f x) (U : X.Opens) (hU : ⊤ ≤ θ.val ⁻¹ᵁ U)
    (a : X.presheaf.obj (op U)) : X.residueField x :=
  TrivSqZeroExt.snd
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (X.residueField x)))).hom.hom
      ((θ.val.appLE U ⊤ hU).hom a))

/-- The map on local rings determined by a dual-number arrow sends the germ at `x` of a local
section to the pullback of that section along the arrow. -/
theorem dottedStalkHom_germ (θ : DottedTangentArrow f x)
    (U : X.Opens) (hx : x ∈ U) (hU : ⊤ ≤ θ.val ⁻¹ᵁ U) (a : X.presheaf.obj (op U)) :
    (dottedStalkHom f x θ).hom ((X.presheaf.germ U x hx).hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (X.residueField x)))).hom.hom
        ((θ.val.appLE U ⊤ hU).hom a) := by
  have hy : θ.val (closedPoint (CommRingCat.of (DualNumber (X.residueField x)))) = x :=
    dotted_closedPoint f x θ
  have hyU : θ.val (closedPoint (CommRingCat.of (DualNumber (X.residueField x)))) ∈ U := by
    rwa [hy]
  have hcongr : X.presheaf.germ U x hx ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom =
      X.presheaf.germ U _ hyU := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact X.presheaf.germ_stalkSpecializes hx _
  have hinc : (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem θ.val hyU).symm).op =
      (homOfLE hU).op := Subsingleton.elim _ _
  change ((X.presheaf.germ U x hx ≫
    (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫
      Scheme.stalkClosedPointTo θ.val).hom a) = _
  rw [← Category.assoc, hcongr, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  rw [Scheme.Hom.appLE, hinc]
  simp

/-- The tangent derivation attached to a dual-number arrow is the coefficient of `ε` in the
image under the arrow's map on local rings. -/
theorem dottedToDerivation_apply (θ : DottedTangentArrow f x) (t : X.presheaf.stalk x) :
    (dottedToDerivation f x θ).val t = TrivSqZeroExt.snd ((dottedStalkHom f x θ).hom t) :=
  rfl

/-- **Stacks Project, Tag 0B2D.** The relative tangent space at a point is canonically the
`𝒪_{X,x}`-linear dual of the stalk of relative differentials, as a vector space over the residue
field: `T_{X/S,x} = Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))`. -/
@[stacks 0B2D, ega "IV 16.5.13" "(16.5.13.1)"]
noncomputable def tangentSpaceEquivCotangentSpace :
    DottedTangentArrow f x ≃ₗ[X.residueField x] CotangentSpace f x :=
  (dottedDerivationLinearEquiv f x).trans
    ((tangentDerivationsEquiv f x).trans (cotangentSpaceEquivDerivation f x).symm)

/-- `AlgebraicGeometry.tangentSpaceEquivCotangentSpace` sends a dual-number arrow to the
functional which lifts its tangent derivation through the identification of the stalk of
relative differentials with the Kähler differentials of the stalk map. -/
theorem tangentSpaceEquivCotangentSpace_apply (θ : DottedTangentArrow f x)
    (ω : relativeDifferentialStalk f x) :
    tangentSpaceEquivCotangentSpace f x θ ω =
      (tangentDerivationsEquiv f x (dottedToDerivation f x θ)).liftKaehlerDifferential
        (relativeDifferentialsStalkKaehlerEquiv f x ω) :=
  rfl

/-- **Stacks Project, Tag 0B2D.** The canonical equivalence sends a dual-number arrow to the
functional which, on the germ `d a` of a universal relative differential, returns the
coefficient of `ε` in the pullback of `a` along the arrow. This is what makes it canonical. -/
@[stacks 0B2D "characterization"]
theorem tangentSpaceEquivCotangentSpace_apply_germ (θ : DottedTangentArrow f x)
    (U : X.Opens) (hx : x ∈ U) (hU : ⊤ ≤ θ.val ⁻¹ᵁ U) (a : X.presheaf.obj (op U)) :
    tangentSpaceEquivCotangentSpace f x θ
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf U x hx
          ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      pullbackInfinitesimalCoefficient θ U hU a := by
  have hE : relativeDifferentialsStalkKaehlerEquiv f x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf U x hx
        ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) ((X.presheaf.germ U x hx).hom a) :=
    relativeDifferentialsStalkKaehlerEquiv_germ_d f x
      (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) a
  refine (tangentSpaceEquivCotangentSpace_apply f x θ _).trans ?_
  rw [hE, Derivation.liftKaehlerDifferential_comp_D, tangentDerivationsEquiv_apply,
    dottedToDerivation_apply, dottedStalkHom_germ f x θ U hx hU]
  rfl

end AlgebraicGeometry

end
