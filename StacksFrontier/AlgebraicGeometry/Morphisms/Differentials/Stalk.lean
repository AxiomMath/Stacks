module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

/-!
# The stalk criterion for the canonical map of relative differentials

For a commutative square of schemes

```
X <--r-- W
|        |
p        s
v        v
S <--g-- Y
```

the canonical map `r^* Ω_{X/S} ⟶ Ω_{W/Y}` of Stacks Project, Tag 01UV is an isomorphism as soon
as it is one at every point. At a point `x` of `W` the three stalks involved are the Kähler
differentials of the local rings and a tensor product of them, so being an isomorphism at `x` is
the existence of a linear equivalence

```
𝒪_{W,x} ⊗_{𝒪_{X,r x}} Ω[𝒪_{X,r x}⁄𝒪_{S,p(r x)}] ≃ Ω[𝒪_{W,x}⁄𝒪_{Y,s x}]
```

carrying `1 ⊗ d a` to `d` of the image of `a`. That is what this file's criterion asks for, so a
consumer only has to produce such an equivalence out of commutative algebra.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_stalk`: the criterion above.

## Implementation notes

Isomorphy of a morphism of sheaves of modules is stalkwise, by
`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`. The three stalks at `x` are
identified by `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` for the
two sheaves of differentials and by
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` for the pullback, and the
stalk of the canonical map is identified with the given equivalence by comparing the two on the
universal differentials of germs — which is exactly the defining compatibility
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`.

The comparison is propagated from those generators by two inductions rather than by an equality
of linear maps, exactly as in
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmooth`:
`Submodule.span_induction` against `KaehlerDifferential.span_range_derivation`, with the scalar
quantified inside the induction hypothesis so that the scalar-multiplication step is
`TensorProduct.smul_tmul`, and then `TensorProduct.induction_on`.

The stalk of the pullback is named through a presheaf of modules whose ring presheaf is *written
out* as `𝒪_W ⋙ forget₂ CommRingCat RingCat`: the module structure on a stalk is found by instance
search only when the ring presheaf is visible in that shape, and the structure sheaf of a scheme
presents it through `AlgebraicGeometry.Scheme.ringCatSheaf`, which search does not unfold.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 08TE](https://stacks.math.columbia.edu/tag/08TE)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeDifferentialStalk Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The canonical map of relative differentials of a commutative square of schemes is an
isomorphism as soon as it is one on local rings.** The hypothesis at a point `x` of the upper-left
corner is a linear equivalence
`𝒪_{W,x} ⊗_{𝒪_{X,r x}} Ω[𝒪_{X,r x}⁄𝒪_{S,p(r x)}] ≃ Ω[𝒪_{W,x}⁄𝒪_{Y,s x}]` carrying the universal
differential `1 ⊗ d a` to the universal differential of the image of `a`; no compatibility with
the canonical map itself has to be checked, because that compatibility is forced on the
generators `d a`.

This is the stalk form of Stacks Project, Tag 01UV, obtained from Tag 08TE for the stalks of the
sheaves of differentials and Tag 0098 for the stalk of the pullback. -/
theorem isIso_relativeDifferentialsMap_of_stalk {W X Y S : Scheme.{u}}
    (r : W ⟶ X) (p : X ⟶ S) (s : W ⟶ Y) (g : Y ⟶ S) (hcomm : r ≫ p = s ≫ g)
    (H : ∀ x : W,
      let R : Type u := ToType (S.presheaf.stalk (p.base (r.base x)))
      let A : Type u := ToType (X.presheaf.stalk (r.base x))
      let B : Type u := ToType (Y.presheaf.stalk (s.base x))
      let C : Type u := ToType (W.presheaf.stalk x)
      letI : Algebra R A := (p.stalkMap (r.base x)).hom.toAlgebra
      letI : Algebra A C := (r.stalkMap x).hom.toAlgebra
      letI : Algebra B C := (s.stalkMap x).hom.toAlgebra
      ∃ E : C ⊗[A] Ω[A⁄R] ≃ₗ[C] Ω[C⁄B],
        ∀ a : A, E ((1 : C) ⊗ₜ[A] KaehlerDifferential.D R A a) =
          KaehlerDifferential.D B C (algebraMap A C a)) :
    IsIso (relativeDifferentialsMap r p s g hcomm) := by
  classical
  set c := relativeDifferentialsMap r p s g hcomm with hc
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap c).2 fun x => ?_
  let ΩXS : X.Modules := relativeDifferentials p
  let ΩWY : W.Modules := relativeDifferentials s
  -- the underlying presheaf of modules of the pullback, named so its stalk is a module
  let P' : _root_.PresheafOfModules (W.sheaf.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((Scheme.Modules.pullback r).obj ΩXS).val
  -- the four local rings at `x` and its images
  let R : Type u := ToType (S.presheaf.stalk (p.base (r.base x)))
  let A : Type u := ToType (X.sheaf.presheaf.stalk (r.base x))
  let B : Type u := ToType (Y.presheaf.stalk (s.base x))
  let C : Type u := ToType (W.sheaf.presheaf.stalk x)
  let : Algebra R A := algebraStalkMap p (r.base x)
  let : Algebra A C := (r.stalkMap x).hom.toAlgebra
  let : Algebra B C := algebraStalkMap s x
  -- the three stalks and their identifications
  let M : Type u :=
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ΩXS.val.presheaf (r.base x))
  let P : Type u := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P'.presheaf x)
  let N : Type u := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ΩWY.val.presheaf x)
  let eA : M ≃ₗ[A] Ω[A⁄R] := relativeDifferentialsStalkKaehlerEquiv p (r.base x)
  let eC : N ≃ₗ[C] Ω[C⁄B] := relativeDifferentialsStalkKaehlerEquiv s x
  obtain ⟨ePull, hPullGerm⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv r.toLRSHom.toShHom ΩXS x
  let ePull' : P ≃ₗ[C] C ⊗[A] M := ePull
  let stalkC : P →ₗ[C] N :=
    Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom W.sheaf.presheaf x c.val
  let eT : C ⊗[A] M ≃ₗ[A] C ⊗[A] Ω[A⁄R] := TensorProduct.congr (LinearEquiv.refl A C) eA
  obtain ⟨E₀, hE₀⟩ := H x
  -- re-ascribe the given equivalence at the local names, so that its scalars are the fvars
  -- `A`, `B`, `C` rather than the stalks written out
  let E : C ⊗[A] Ω[A⁄R] ≃ₗ[C] Ω[C⁄B] := E₀
  have hE : ∀ a : A, E ((1 : C) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      KaehlerDifferential.D B C (algebraMap A C a) := hE₀
  have hb (L : Type u) [AddCommGroup L] [Module A L] (b : C) (z : L) :
      b ⊗ₜ[A] z = b • ((1 : C) ⊗ₜ[A] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  -- the stalk of `c` agrees with the given equivalence on the universal differential of a germ
  have hgen : ∀ (b : C) (a : A),
      E (eT (b ⊗ₜ[A] eA.symm (KaehlerDifferential.D R A a)))
        = eC (stalkC (ePull'.symm (b ⊗ₜ[A] eA.symm (KaehlerDifferential.D R A a)))) := by
    intro b a
    obtain ⟨U, hxU, v, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.presheaf a
    set dX := (universalRelativeDerivation p).d v with hdX
    set mX := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩXS.val.presheaf U (r.base x) hxU dX
      with hmX
    set dW := (universalRelativeDerivation s).d ((r.app U).hom v) with hdW
    set mW := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩWY.val.presheaf (r ⁻¹ᵁ U) x hxU dW
      with hmW
    have heA : eA mX = KaehlerDifferential.D R A (X.sheaf.presheaf.germ U (r.base x) hxU v) :=
      relativeDifferentialsStalkKaehlerEquiv_germ_d p (r.base x) (OrderDual.toDual ⟨U, hxU⟩) v
    have heC : eC mW = KaehlerDifferential.D B C
        (W.sheaf.presheaf.germ (r ⁻¹ᵁ U) x hxU ((r.app U).hom v)) :=
      relativeDifferentialsStalkKaehlerEquiv_germ_d s x
        (OrderDual.toDual ⟨r ⁻¹ᵁ U, hxU⟩) ((r.app U).hom v)
    -- the germ of the adjunction unit is the pure tensor `1 ⊗ germ`
    have hunit : ePull'.symm ((1 : C) ⊗ₜ[A] mX) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P'.presheaf (r ⁻¹ᵁ U) x hxU
          (((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app ΩXS).val.app (op U) dX) :=
      ePull'.symm_apply_eq.2 (hPullGerm U hxU dX).symm
    have hd : ((Scheme.Modules.pushforward r).map c).val.app (op U)
        (((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app ΩXS).val.app (op U) dX)
          = dW := by
      have h := relativeDifferentialsMap_app_d (f := r) (p := p) (p' := s) g hcomm U v
      rwa [Adjunction.homEquiv_unit] at h
    have hstalkC : stalkC (ePull'.symm ((1 : C) ⊗ₜ[A] mX)) = mW := by
      rw [hunit]
      refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply (r ⁻¹ᵁ U) x hxU
        ((PresheafOfModules.toPresheaf W.ringCatSheaf.obj).map c.val) _) ?_
      exact congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩWY.val.presheaf
        (r ⁻¹ᵁ U) x hxU) hd
    have hgerm : (algebraMap A C) (X.sheaf.presheaf.germ U (r.base x) hxU v) =
        W.sheaf.presheaf.germ (r ⁻¹ᵁ U) x hxU ((r.app U).hom v) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (r.germ_stalkMap U x hxU)) v
    rw [← heA, LinearEquiv.symm_apply_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      heA, hb, map_smul, hE, hgerm, hb, map_smul, map_smul, map_smul, hstalkC, heC]
  -- propagate to all of `Ω[A⁄R]`, then to the whole tensor product
  have hspan : ∀ (ω : Ω[A⁄R]) (b : C),
      E (eT (b ⊗ₜ[A] eA.symm ω)) = eC (stalkC (ePull'.symm (b ⊗ₜ[A] eA.symm ω))) := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact fun b => hgen b a
    | zero => intro b; simp
    | add y z _ _ ihy ihz =>
      intro b
      simp only [map_add, TensorProduct.tmul_add, ihy b, ihz b]
    | smul a y _ ihy =>
      intro b
      rw [map_smul, ← TensorProduct.smul_tmul]
      exact ihy (a • b)
  have hBridge : ∀ w : C ⊗[A] M, E (eT w) = eC (stalkC (ePull'.symm w)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul b m =>
      have h := hspan (eA m) b
      rwa [LinearEquiv.symm_apply_apply] at h
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  -- the stalk of `c` is bijective because it is the given equivalence up to three others
  change Function.Bijective stalkC
  have hEq : ⇑eC ∘ ⇑stalkC = ⇑E ∘ ⇑eT ∘ ⇑ePull' := funext fun z => by
    have h := hBridge (ePull' z)
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm
  rw [← eC.bijective.of_comp_iff' stalkC, hEq]
  exact E.bijective.comp (eT.bijective.comp ePull'.bijective)

end AlgebraicGeometry.Scheme.Hom

end
