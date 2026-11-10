module

public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.MaximalIdealCotangent
public import StacksCore.Tactic.StacksAttribute

/-!
# The tangent map is dual to the map on differentials

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with structure morphisms `p : X ⟶ S`
and `q : Y ⟶ S` satisfying `f ≫ q = p`, let `x` be a point of `X` and set `y = f x`. The
morphism `f` induces a natural map `Ω_{Y/S,y} → Ω_{X/S,x}` on stalks of relative differentials,
semilinear over the stalk map `𝒪_{Y,y} → 𝒪_{X,x}`, hence a map
`κ(y) ⊗ Ω_{Y/S,y} → κ(x) ⊗ Ω_{X/S,x}` on residue-field fibres, semilinear over the residue
field extension `κ(y) → κ(x)`. When `κ(y) = κ(x)`, the tangent map
`d f : T_{X/S,x} → T_{Y/S,y}` of Tag 0B2F is the dual of this map, under the identifications
`T_{X/S,x} = Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x)) = Hom_{κ(x)}(κ(x) ⊗ Ω_{X/S,x}, κ(x))` of Tag 0B2D.

## Main definitions

* `AlgebraicGeometry.relativeDifferentialStalkMap`: the map `Ω_{Y/S,y} → Ω_{X/S,x}`.
* `AlgebraicGeometry.differentialFiberMap`: the map `κ(y) ⊗ Ω_{Y/S,y} → κ(x) ⊗ Ω_{X/S,x}`.
* `AlgebraicGeometry.tangentSpaceEquivDualDifferentialFiber`: the identification of Tag 0B2D
  in the form `T_{X/S,x} = Hom_{κ(x)}(κ(x) ⊗ Ω_{X/S,x}, κ(x))`.
* `AlgebraicGeometry.differentialFiberMapDual`: the dual of `differentialFiberMap` when the
  residue field extension is an isomorphism.

## Main results

* `AlgebraicGeometry.relativeDifferentialStalkMap_germ_d` and
  `AlgebraicGeometry.differentialFiberMap_one_tmul_germ_d`: the map on differentials sends the
  germ of `d a` at `y` to the germ of `d (f^* a)` at `x`, which is what makes it natural.
* `AlgebraicGeometry.tangentSpaceEquivCotangentSpace_tangentMap`: the tangent map is the dual
  of `relativeDifferentialStalkMap` under the identification of Tag 0B2D.
* `AlgebraicGeometry.tangentSpaceEquivDualDifferentialFiber_tangentMap`: the tangent map is the
  dual of `differentialFiberMap` under the identification of Tag 0B2D, which is the second
  assertion of Tag 0B2F.

## Implementation notes

The stalk of the relative differentials is identified with the Kähler differentials of the stalk
map by `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, and the map
on stalks is `KaehlerDifferential.map` for the square formed by the stalk maps of `q`, `f` and
`f ≫ q`. The base point of `S` is `q (f x)` on one side and `p x` on the other, which agree only
once `p` is replaced by `f ≫ q`; the constructions substitute the equation `f ≫ q = p`.

The scalar structures are those of `AlgebraicGeometry.relativeCotangentSpaceEquivDifferentialFiber`
(Tag 0B2E): the residue field is an algebra over the local ring through Mathlib's
`IsLocalRing.ResidueField.algebra`, so the fibre `κ(x) ⊗ Ω_{X/S,x}` is the one of Tag 0B2E, and
the passage from `Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))` to `Hom_{κ(x)}(κ(x) ⊗ Ω_{X/S,x}, κ(x))` is
`LinearMap.liftBaseChangeEquiv`. The tangent-derivation side of Tag 0B2D lets the local ring act
on `κ(x)` through `AlgebraicGeometry.residueModule` instead; the two actions agree definitionally,
but instance search sees two different terms, so the statements about the stalk map are made in a
section where the instances of `AlgebraicGeometry.tangentSpaceEquivCotangentSpace` are local, and
the statements about fibres in a separate section where those of Tag 0B2E are.

Equality of the residue fields is expressed, as in `AlgebraicGeometry.tangentMap`, by the
assertion that `f.residueFieldMap x : κ(y) ⟶ κ(x)` is an isomorphism; the dual of a map which
is semilinear over it is semilinear over its inverse, as the tangent map is.

## References

* [Stacks Project, Tag 0B2F](https://stacks.math.columbia.edu/tag/0B2F)
* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules
open Stacks.RelativeDifferentialStalkMap
open Stacks.SmoothAtJacobian (relativeDifferentialStalk relativeDifferentialStalkModule)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] stalkMapAlgebra openNhdsDecidableEq relativeDifferentialStalkModule

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)

/-- The inverse of an isomorphism of residue fields undoes it. -/
lemma inv_residueFieldMap_apply (x : X) [IsIso (f.residueFieldMap x)]
    (c : Y.residueField (f x)) :
    (inv (f.residueFieldMap x)).hom ((f.residueFieldMap x).hom c) = c :=
  congrArg (fun g : Y.residueField (f x) ⟶ Y.residueField (f x) ↦ g.hom c)
    (IsIso.hom_inv_id (f.residueFieldMap x))

/-! ### The map on stalks of relative differentials -/

/-- The stalk maps of `q` at `f x`, of `f` at `x` and of `f ≫ q` at `x` form a scalar tower
`𝒪_{S,q(f x)} → 𝒪_{Y,f x} → 𝒪_{X,x}`. -/
theorem isScalarTower_stalkMap_comp (x : X) :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
        (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
    IsScalarTower (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (Y.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x)) := by
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
  refine IsScalarTower.of_algebraMap_eq' ?_
  change ((f ≫ q).stalkMap x).hom = (f.stalkMap x).hom.comp (q.stalkMap (f.base x)).hom
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **The map `Ω_{Y/S,f x} → Ω_{X/S,x}` induced by `f` on stalks of relative differentials**,
semilinear over the stalk map of `f`. Under the identifications of the stalks with Kähler
differentials of the stalk maps it is `KaehlerDifferential.map`. -/
noncomputable def relativeDifferentialStalkMap (h : f ≫ q = p) (x : X) :
    relativeDifferentialStalk q (f.base x) →ₛₗ[(f.stalkMap x).hom]
      relativeDifferentialStalk p x := by
  subst h
  letI : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
  haveI := isScalarTower_stalkMap_comp f q x
  let EX : relativeDifferentialStalk (f ≫ q) x ≃ₗ[X.presheaf.stalk x]
      Ω[ToType (X.presheaf.stalk x)⁄ToType (S.presheaf.stalk (q.base (f.base x)))] :=
    relativeDifferentialsStalkKaehlerEquiv (f ≫ q) x
  let EY : relativeDifferentialStalk q (f.base x) ≃ₗ[Y.presheaf.stalk (f.base x)]
      Ω[ToType (Y.presheaf.stalk (f.base x))⁄ToType (S.presheaf.stalk (q.base (f.base x)))] :=
    relativeDifferentialsStalkKaehlerEquiv q (f.base x)
  let M := KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base x))))
    (ToType (S.presheaf.stalk (q.base (f.base x))))
    (ToType (Y.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x))
  let M' : Ω[ToType (Y.presheaf.stalk (f.base x))⁄ToType (S.presheaf.stalk (q.base (f.base x)))]
      →ₛₗ[(f.stalkMap x).hom]
      Ω[ToType (X.presheaf.stalk x)⁄ToType (S.presheaf.stalk (q.base (f.base x)))] :=
    { toFun := M
      map_add' := M.map_add
      map_smul' := fun b w ↦ (M.map_smul b w).trans
        (algebraMap_smul (ToType (X.presheaf.stalk x)) b _).symm }
  exact EX.symm.toLinearMap ∘ₛₗ M' ∘ₛₗ EY.toLinearMap

/-- Read through the identifications of the stalks with Kähler differentials,
`AlgebraicGeometry.relativeDifferentialStalkMap` is `KaehlerDifferential.map`. -/
theorem relativeDifferentialStalkMap_apply (x : X)
    (ω : relativeDifferentialStalk q (f.base x)) :
    letI : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
        (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
    haveI := isScalarTower_stalkMap_comp f q x
    relativeDifferentialStalkMap f (f ≫ q) q rfl x ω =
      (relativeDifferentialsStalkKaehlerEquiv (f ≫ q) x).symm
        (KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base (f.base x))))
          (ToType (S.presheaf.stalk (q.base (f.base x))))
          (ToType (Y.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x))
          (relativeDifferentialsStalkKaehlerEquiv q (f.base x) ω)) :=
  rfl

/-- **The map on stalks of relative differentials is natural**: it sends the germ at `f x` of the
universal relative differential `d a` of a local section `a` of `𝒪_Y` to the germ at `x` of
`d (f^* a)`. -/
theorem relativeDifferentialStalkMap_germ_d (h : f ≫ q = p) (x : X) (U : Y.Opens)
    (hx : f.base x ∈ U) (a : Y.presheaf.obj (op U)) :
    relativeDifferentialStalkMap f p q h x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials q).val.presheaf U (f.base x) hx
          ((Scheme.Hom.universalRelativeDerivation q).d a)) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials p).val.presheaf (f ⁻¹ᵁ U) x hx
        ((Scheme.Hom.universalRelativeDerivation p).d (f.app U a)) := by
  subst h
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
  have := isScalarTower_stalkMap_comp f q x
  have hq := relativeDifferentialsStalkKaehlerEquiv_germ_d q (f.base x)
    (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds (f.base x))) a
  have hp := relativeDifferentialsStalkKaehlerEquiv_germ_d (f ≫ q) x
    (OrderDual.toDual (⟨f ⁻¹ᵁ U, hx⟩ : TopologicalSpace.OpenNhds x)) (f.app U a)
  refine (relativeDifferentialStalkMap_apply f q x _).trans
    ((LinearEquiv.symm_apply_eq _).mpr ?_)
  refine (congrArg _ hq).trans ((KaehlerDifferential.map_D _ _ _ _ _).trans
    (Eq.trans ?_ hp.symm))
  exact congrArg (KaehlerDifferential.D _ _) (Scheme.Hom.germ_stalkMap_apply f U x hx a)

/-- On universal differentials of the local ring of `Y` at `f x`, the map on stalks of relative
differentials is the stalk map of `f`: `d a ↦ d (f^♯ a)`. -/
theorem relativeDifferentialStalkMap_symm_D (h : f ≫ q = p) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    relativeDifferentialStalkMap f p q h x
        ((relativeDifferentialsStalkKaehlerEquiv q (f.base x)).symm
          (KaehlerDifferential.D (ToType (S.presheaf.stalk (q.base (f.base x))))
            (ToType (Y.presheaf.stalk (f.base x))) a)) =
      (relativeDifferentialsStalkKaehlerEquiv p x).symm
        (KaehlerDifferential.D (ToType (S.presheaf.stalk (p.base x)))
          (ToType (X.presheaf.stalk x)) ((f.stalkMap x).hom a)) := by
  subst h
  let : Algebra (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (X.presheaf.stalk x)) := stalkMapAlgebra (f ≫ q) x
  have := isScalarTower_stalkMap_comp f q x
  exact (relativeDifferentialStalkMap_apply f q x _).trans (congrArg _
    ((congrArg _ (LinearEquiv.apply_symm_apply _ _)).trans (KaehlerDifferential.map_D _ _ _ _ a)))

/-! ### The tangent map is dual to the map on differentials -/

section Cotangent

attribute [local instance] residueModule residueSMulComm residueSMulComm' baseResidueModule
  baseResidueSMulComm residueIsScalarTower

/-- The Kähler lift of a tangent derivation sends `d a` to the value of the derivation at `a`. -/
private theorem lift_tangentDerivationsEquiv_D {Z : Scheme.{u}} (g : Z ⟶ S) (z : Z)
    (D : tangentDerivations g z) (a : Z.presheaf.stalk z) :
    (tangentDerivationsEquiv g z D).liftKaehlerDifferential
        (KaehlerDifferential.D (ToType (S.presheaf.stalk (g.base z)))
          (ToType (Z.presheaf.stalk z)) a) = D.val a :=
  (Derivation.liftKaehlerDifferential_comp_D _ a).trans (tangentDerivationsEquiv_apply g z D a)

/-- **The tangent map is dual to the map on stalks of relative differentials**, under the
identification `T_{X/S,x} = Hom_{𝒪_{X,x}}(Ω_{X/S,x}, κ(x))` of Tag 0B2D: the functional of
`d f (θ)` is the functional of `θ` precomposed with `Ω_{Y/S,f x} → Ω_{X/S,x}`, read back in
`κ(f x)` through the residue-field identification. -/
@[sga "1 II 4.7" "(x), special case"]
theorem tangentSpaceEquivCotangentSpace_tangentMap (h : f ≫ q = p) (x : X)
    [IsIso (f.residueFieldMap x)] (θ : DottedTangentArrow p x)
    (ω : relativeDifferentialStalk q (f.base x)) :
    tangentSpaceEquivCotangentSpace q (f.base x) (tangentMap f p q h x θ) ω =
      (inv (f.residueFieldMap x)).hom
        (tangentSpaceEquivCotangentSpace p x θ (relativeDifferentialStalkMap f p q h x ω)) := by
  obtain ⟨ξ, rfl⟩ := (relativeDifferentialsStalkKaehlerEquiv q (f.base x)).symm.surjective ω
  have hd : dottedToDerivation q (f.base x) (tangentMap f p q h x θ) =
      tangentDerivationMap f p q x h (dottedToDerivation p x θ) :=
    dottedToDerivation_derivationToDotted q (f.base x) _
  let EX : relativeDifferentialStalk p x ≃ₗ[X.presheaf.stalk x]
      Ω[ToType (X.presheaf.stalk x)⁄ToType (S.presheaf.stalk (p.base x))] :=
    relativeDifferentialsStalkKaehlerEquiv p x
  let EY : relativeDifferentialStalk q (f.base x) ≃ₗ[Y.presheaf.stalk (f.base x)]
      Ω[ToType (Y.presheaf.stalk (f.base x))⁄ToType (S.presheaf.stalk (q.base (f.base x)))] :=
    relativeDifferentialsStalkKaehlerEquiv q (f.base x)
  let g := EX.toLinearMap ∘ₛₗ relativeDifferentialStalkMap f p q h x ∘ₛₗ EY.symm.toLinearMap
  have g_D : ∀ a, g (KaehlerDifferential.D (ToType (S.presheaf.stalk (q.base (f.base x))))
      (ToType (Y.presheaf.stalk (f.base x))) a) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (p.base x)))
        (ToType (X.presheaf.stalk x)) ((f.stalkMap x).hom a) := fun a ↦
    (congrArg EX (relativeDifferentialStalkMap_symm_D f p q h x a)).trans
      (EX.apply_symm_apply _)
  let L := (tangentDerivationsEquiv q (f.base x)
    (tangentDerivationMap f p q x h (dottedToDerivation p x θ))).liftKaehlerDifferential
  let K := (tangentDerivationsEquiv p x (dottedToDerivation p x θ)).liftKaehlerDifferential
  suffices H : ∀ ξ', L ξ' = (inv (f.residueFieldMap x)).hom (K (g ξ')) by
    refine (tangentSpaceEquivCotangentSpace_apply q (f.base x) _ _).trans (Eq.trans ?_
      (congrArg _ (tangentSpaceEquivCotangentSpace_apply p x θ _).symm))
    refine (congrArg _ (LinearEquiv.apply_symm_apply _ ξ)).trans ?_
    rw [hd]
    exact H ξ
  intro ξ'
  have hξ : ξ' ∈ Submodule.span (ToType (Y.presheaf.stalk (f.base x)))
      (Set.range (KaehlerDifferential.D (ToType (S.presheaf.stalk (q.base (f.base x))))
        (ToType (Y.presheaf.stalk (f.base x))))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hξ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    rw [g_D]
    exact (lift_tangentDerivationsEquiv_D _ _ _ a).trans
      ((tangentDerivationMap_val_apply f p q x h (dottedToDerivation p x θ) a).trans
        (congrArg _ (lift_tangentDerivationsEquiv_D _ _ _ _).symm))
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul c z _ hz =>
    rw [map_smul, LinearMap.map_smulₛₗ, map_smul, hz]
    change Y.residue (f.base x) c * _ =
      (inv (f.residueFieldMap x)).hom (X.residue x ((f.stalkMap x).hom c) * _)
    rw [map_mul, inv_residueFieldMap_residue]

end Cotangent

/-! ### Residue-field fibres -/

section Fiber

attribute [local instance] stalkResidueAlgebra residueAlgebraTower

/-- The residue-field extension of `f` at `x` is compatible with the residue maps of the two
local rings, written as structural maps of algebras. -/
lemma residueFieldMap_algebraMap (x : X) (b : Y.presheaf.stalk (f.base x)) :
    (f.residueFieldMap x).hom
        (algebraMap (Y.presheaf.stalk (f.base x)) (Y.residueField (f.base x)) b) =
      algebraMap (X.presheaf.stalk x) (X.residueField x) ((f.stalkMap x).hom b) :=
  congrArg (fun g : Y.presheaf.stalk (f.base x) ⟶ X.residueField x ↦ g.hom b)
    (Scheme.residue_residueFieldMap f x)

/-- **The map `κ(y) ⊗ Ω_{Y/S,y} → κ(x) ⊗ Ω_{X/S,x}` induced by `f` on residue-field fibres of
the stalks of relative differentials**, where `y = f x`: it is `c ⊗ ω ↦ c ⊗ f^*ω`, semilinear
over the residue field extension `κ(y) → κ(x)` of `f` at `x`. -/
noncomputable def differentialFiberMap (h : f ≫ q = p) (x : X) :
    Y.residueField (f.base x) ⊗[Y.presheaf.stalk (f.base x)] relativeDifferentialStalk q (f.base x)
      →ₛₗ[(f.residueFieldMap x).hom]
      X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk p x where
  toFun := TensorProduct.liftAddHom
    { toFun := fun c ↦
        { toFun := fun ω ↦
            (f.residueFieldMap x).hom c ⊗ₜ relativeDifferentialStalkMap f p q h x ω
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun ω ω' ↦ by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext ω
        exact (congrArg (· ⊗ₜ[X.presheaf.stalk x] relativeDifferentialStalkMap f p q h x ω)
          (map_zero _)).trans (TensorProduct.zero_tmul _ _)
      map_add' := fun c c' ↦ by
        ext ω
        exact (congrArg (· ⊗ₜ[X.presheaf.stalk x] relativeDifferentialStalkMap f p q h x ω)
          (map_add _ c c')).trans (TensorProduct.add_tmul _ _ _) }
    (fun r c ω ↦ by
      change (f.residueFieldMap x).hom (r • c) ⊗ₜ relativeDifferentialStalkMap f p q h x ω =
        (f.residueFieldMap x).hom c ⊗ₜ relativeDifferentialStalkMap f p q h x (r • ω)
      rw [Algebra.smul_def, map_mul, residueFieldMap_algebraMap, ← Algebra.smul_def,
        TensorProduct.smul_tmul, LinearMap.map_smulₛₗ])
  map_add' := map_add _
  map_smul' := fun c t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul c' ω =>
      rw [TensorProduct.smul_tmul']
      change (f.residueFieldMap x).hom (c • c') ⊗ₜ relativeDifferentialStalkMap f p q h x ω =
        (f.residueFieldMap x).hom c •
          ((f.residueFieldMap x).hom c' ⊗ₜ relativeDifferentialStalkMap f p q h x ω)
      rw [smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The map on residue-field fibres sends `c ⊗ ω` to `c ⊗ f^*ω`. -/
theorem differentialFiberMap_tmul (h : f ≫ q = p) (x : X) (c : Y.residueField (f.base x))
    (ω : relativeDifferentialStalk q (f.base x)) :
    differentialFiberMap f p q h x (c ⊗ₜ ω) =
      (f.residueFieldMap x).hom c ⊗ₜ relativeDifferentialStalkMap f p q h x ω :=
  rfl

/-- **The map on residue-field fibres is natural**: it sends `1 ⊗ d a`, for the germ at `f x` of
the universal relative differential of a local section `a` of `𝒪_Y`, to `1 ⊗ d (f^* a)`. -/
theorem differentialFiberMap_one_tmul_germ_d (h : f ≫ q = p) (x : X) (U : Y.Opens)
    (hx : f.base x ∈ U) (a : Y.presheaf.obj (op U)) :
    differentialFiberMap f p q h x ((1 : Y.residueField (f.base x)) ⊗ₜ
        (show relativeDifferentialStalk q (f.base x) from
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials q).val.presheaf U (f.base x) hx
            ((Scheme.Hom.universalRelativeDerivation q).d a))) =
      (1 : X.residueField x) ⊗ₜ
        (show relativeDifferentialStalk p x from
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials p).val.presheaf (f ⁻¹ᵁ U) x hx
            ((Scheme.Hom.universalRelativeDerivation p).d (f.app U a))) := by
  rw [differentialFiberMap_tmul, map_one, relativeDifferentialStalkMap_germ_d]

/-- The identification of Tag 0B2D in the form used by Tag 0B2F: the relative tangent space at `x`
is the `κ(x)`-linear dual `Hom_{κ(x)}(κ(x) ⊗ Ω_{X/S,x}, κ(x))` of the residue-field fibre of the
stalk of relative differentials. It is `AlgebraicGeometry.tangentSpaceEquivCotangentSpace`
followed by the identification of `𝒪_{X,x}`-linear functionals on `Ω_{X/S,x}` with `κ(x)`-linear
functionals on its fibre. -/
@[sga "1 II 4.7" "(x)", sga "3 XI 1.9" "special case"]
noncomputable def tangentSpaceEquivDualDifferentialFiber (x : X) :
    DottedTangentArrow p x ≃ₗ[X.residueField x]
      (X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk p x →ₗ[X.residueField x]
        X.residueField x) :=
  (show DottedTangentArrow p x ≃ₗ[X.residueField x]
      (relativeDifferentialStalk p x →ₗ[X.presheaf.stalk x] X.residueField x) from
    tangentSpaceEquivCotangentSpace p x).trans
    (LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x))

/-- The identification of the tangent space with the dual of the fibre evaluates a tangent
vector on `c ⊗ ω` as `c` times its functional of Tag 0B2D evaluated on `ω`. -/
theorem tangentSpaceEquivDualDifferentialFiber_tmul (x : X) (θ : DottedTangentArrow p x)
    (c : X.residueField x) (ω : relativeDifferentialStalk p x) :
    tangentSpaceEquivDualDifferentialFiber p x θ (c ⊗ₜ ω) =
      c * tangentSpaceEquivCotangentSpace p x θ ω :=
  rfl

/-- **The dual of the map on residue-field fibres**, when the residue field extension of `f` at
`x` is an isomorphism: a `κ(x)`-linear functional `ψ` on `κ(x) ⊗ Ω_{X/S,x}` goes to the
`κ(y)`-linear functional `t ↦ ψ (f^* t)` on `κ(y) ⊗ Ω_{Y/S,y}`, read in `κ(y)` through the
inverse of the residue-field identification. It is semilinear over that inverse. -/
noncomputable def differentialFiberMapDual (h : f ≫ q = p) (x : X)
    [IsIso (f.residueFieldMap x)] :
    (X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk p x →ₗ[X.residueField x]
        X.residueField x) →ₛₗ[(inv (f.residueFieldMap x)).hom]
      (Y.residueField (f.base x) ⊗[Y.presheaf.stalk (f.base x)]
          relativeDifferentialStalk q (f.base x) →ₗ[Y.residueField (f.base x)]
        Y.residueField (f.base x)) where
  toFun ψ :=
    { toFun := fun t ↦ (inv (f.residueFieldMap x)).hom (ψ (differentialFiberMap f p q h x t))
      map_add' := fun t t' ↦ by rw [map_add, map_add, map_add]
      map_smul' := fun c t ↦ by
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, smul_eq_mul, map_mul,
          inv_residueFieldMap_apply, RingHom.id_apply, smul_eq_mul] }
  map_add' ψ ψ' := LinearMap.ext fun _ ↦ map_add (inv (f.residueFieldMap x)).hom _ _
  map_smul' c ψ := LinearMap.ext fun _ ↦ map_mul (inv (f.residueFieldMap x)).hom c _

/-- The dual of the map on residue-field fibres evaluates a functional `ψ` on `t` as
`ψ (f^* t)`, read in `κ(y)`. -/
theorem differentialFiberMapDual_apply (h : f ≫ q = p) (x : X) [IsIso (f.residueFieldMap x)]
    (ψ : X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk p x
      →ₗ[X.residueField x] X.residueField x)
    (t : Y.residueField (f.base x) ⊗[Y.presheaf.stalk (f.base x)]
      relativeDifferentialStalk q (f.base x)) :
    differentialFiberMapDual f p q h x ψ t =
      (inv (f.residueFieldMap x)).hom (ψ (differentialFiberMap f p q h x t)) :=
  rfl

/-- **The tangent map is dual to the map on residue-field fibres.** Let `f : X ⟶ Y` be a morphism
of schemes over `S`, let `x` be a point of `X` with `κ(f x) = κ(x)`. Under the identifications
`T_{X/S,x} = Hom_{κ(x)}(κ(x) ⊗ Ω_{X/S,x}, κ(x))` and
`T_{Y/S,f x} = Hom_{κ(f x)}(κ(f x) ⊗ Ω_{Y/S,f x}, κ(f x))` of Tag 0B2D, the tangent map
`d f : T_{X/S,x} → T_{Y/S,f x}` is the dual of the natural map
`κ(f x) ⊗ Ω_{Y/S,f x} → κ(x) ⊗ Ω_{X/S,x}`. -/
@[stacks 0B2F "dual to the map Ω_{Y/S,y} ⊗ κ(y) → Ω_{X/S,x} ⊗ κ(x) via the identifications of \
  Tag 0B2D", ega "IV 16.5.13" "partial, special case"]
theorem tangentSpaceEquivDualDifferentialFiber_tangentMap (h : f ≫ q = p) (x : X)
    [IsIso (f.residueFieldMap x)] (θ : DottedTangentArrow p x) :
    tangentSpaceEquivDualDifferentialFiber q (f.base x) (tangentMap f p q h x θ) =
      differentialFiberMapDual f p q h x (tangentSpaceEquivDualDifferentialFiber p x θ) := by
  refine LinearMap.ext fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul c ω =>
    rw [differentialFiberMapDual_apply, differentialFiberMap_tmul,
      tangentSpaceEquivDualDifferentialFiber_tmul, tangentSpaceEquivDualDifferentialFiber_tmul,
      tangentSpaceEquivCotangentSpace_tangentMap, map_mul, inv_residueFieldMap_apply]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

end Fiber

end AlgebraicGeometry

end
