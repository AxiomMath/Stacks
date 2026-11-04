module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Pieces

/-!
# The pullback of the Rees algebra, chart by chart

Let `ℐ` be a quasi-coherent ideal sheaf on a scheme `X` and let `g : Z ⟶ X` be a morphism of
schemes. The pullback `g^*(⨁ₙ ℐⁿ)` of the Rees algebra of `ℐ` is a sheaf of graded algebras on
`Z` by `Stacks.Conormal.gradedPullback`. This file describes it over an affine chart `U` of `X`:
an element of `ℐ(U)ⁿ` gives a degree-`n` section over `g⁻¹U`, and that assignment is additive,
linear over `Γ(X, U)` acting through `g`, compatible with restriction between charts, and turns
multiplication of ideal elements into the graded multiplication and `1` into the graded unit.

On a chart with affine preimage on which the functions surject, the assignment is surjective,
and if moreover the kernel of the map on functions is `ℐ(U)` its kernel is exactly `ℐ(U)ⁿ⁺¹`.

## Main definitions

* `Stacks.Conormal.reesSection`: an element of `ℐ(U)ⁿ`, as a degree-`n` section of the Rees
  algebra over an affine open `U`.
* `Stacks.Conormal.pullbackSectionAddHom`: pulling a section of a sheaf of modules back along
  `g`, as an additive map.
* `Stacks.Conormal.reesPullbackMap`: the pullback of `reesSection`, a degree-`n` section of
  `g^*(⨁ₙ ℐⁿ)` over `g⁻¹U`.

## Main results

* `Stacks.Conormal.pullbackSection_restrict` and `Stacks.Conormal.pullbackSection_smul`: pulling
  a section back commutes with restriction and carries the `Γ(X, U)`-action to the
  `Γ(Z, g⁻¹U)`-action along `g`.
* `Stacks.Conormal.reesSection_smul`, `reesSection_restrict`, `reesSection_mul` and
  `reesSection_one`: the corresponding compatibilities of `reesSection`.
* `Stacks.Conormal.reesPullbackMap_surjective` and `reesPullbackMap_eq_zero_iff`: on a chart
  with affine preimage on which the functions surject, `reesPullbackMap` is surjective, and its
  kernel is `ℐ(U)ⁿ⁺¹` when the kernel of the map on functions is `ℐ(U)`.
* `Stacks.Conormal.reesPullbackMap_naturality`, `reesPullbackMap_smul`,
  `reesPullbackMap_mul` and `reesPullbackMap_one`: the four compatibilities of
  `reesPullbackMap`.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

/-! ### Pulling a section back commutes with restriction and with scalars -/

section Sections

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (M : X.Modules)

/-- **Pulling a section back commutes with restriction.** -/
lemma pullbackSection_restrict {U V : X.Opens} (h : V ≤ U) (hZ : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullback g).obj M).val.map (homOfLE hZ).op
        (Scheme.Modules.pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a) =
      Scheme.Modules.pullbackSection g M V (g ⁻¹ᵁ V) le_rfl
        (M.val.map (homOfLE h).op a) := by
  rw [pullbackSection_self g M U a, pullbackSection_self g M V (M.val.map (homOfLE h).op a)]
  exact (PresheafOfModules.congr_map_apply ((Scheme.Modules.pullback g).obj M).val
    (Subsingleton.elim (homOfLE hZ).op
      ((RingedSpaceModuleAdjunction.opensMap g.toLRSHom.toShHom).op.map
        (homOfLE h).op)) _).trans
    (Stacks.RingedSpace.pullbackUnit_restrict g.toLRSHom.toShHom M (homOfLE h).op a)

/-- **Pulling a section back is linear over the map on functions.** -/
lemma pullbackSection_smul (U : X.Opens) (r : Γ(X, U)) (a : M.val.obj (op U)) :
    Scheme.Modules.pullbackSection g M U (g ⁻¹ᵁ U) le_rfl
        ((show X.ringCatSheaf.obj.obj (op U) from r) • a) =
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) from (g.app U).hom r) •
        Scheme.Modules.pullbackSection g M U (g ⁻¹ᵁ U) le_rfl a := by
  rw [pullbackSection_self g M U _, pullbackSection_self g M U a]
  exact Stacks.RingedSpace.pullbackUnit_smul g.toLRSHom.toShHom M (op U) r a

end Sections

/-! ### Local sections of the Rees algebra -/

section Rees

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- An element of `ℐ(U)ⁿ`, as a degree-`n` section of the Rees algebra over the affine open
`U`. -/
noncomputable def reesSection (n : ℕ) (U : X.affineOpens) :
    ↥(I.ideal U ^ n) →+ Γ(reesModule I (n : ℤ), U.1) :=
  AddMonoidHom.mk' (fun a => (reesAffineLinearEquiv I n U).symm a) (map_add _)

/-- `Stacks.Conormal.reesAffineLinearEquiv` sends `reesSection I n U a` back to `a`. -/
@[simp] lemma reesAffineLinearEquiv_reesSection (n : ℕ) (U : X.affineOpens)
    (a : ↥(I.ideal U ^ n)) : reesAffineLinearEquiv I n U (reesSection I n U a) = a :=
  (reesAffineLinearEquiv I n U).apply_symm_apply a

/-- The function on `U` underlying `reesSection I n U a` is `a`. -/
lemma reesSection_coe (n : ℕ) (U : X.affineOpens) (a : ↥(I.ideal U ^ n)) :
    (Stacks.Blowup.reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U
      (reesSection I n U a) : Γ(X, U)) = (a : Γ(X, U)) :=
  congrArg (fun b : ↥(I.ideal U ^ n) => (b : Γ(X, U)))
    (reesAffineLinearEquiv_reesSection I n U a)

/-- The degree-`n` sections of the Rees algebra are `Γ(X, U)`-linear in the ideal element. -/
lemma reesSection_smul (n : ℕ) (U : X.affineOpens) (r : Γ(X, U)) (a : ↥(I.ideal U ^ n)) :
    reesSection I n U (r • a) =
      r • reesSection I n U a :=
  (reesAffineLinearEquiv I n U).symm.map_smul r a

/-- A degree-`n` section of the Rees algebra is `reesSection I n U c` once its function on `U`
is `c`. -/
private theorem eq_reesSection_of_coe_eq (n : ℕ) (U : X.affineOpens)
    (x : Γ(reesModule I (n : ℤ), U.1)) (c : ↥(I.ideal U ^ n))
    (h : (Stacks.Blowup.reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U x : Γ(X, U)) =
      (c : Γ(X, U))) :
    x = reesSection I n U c :=
  (Stacks.Blowup.reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U).injective
    (Subtype.ext (h.trans (reesSection_coe I n U c).symm))

/-- The degree-`n` sections of the Rees algebra are compatible with restriction between affine
charts. -/
lemma reesSection_restrict (n : ℕ) (U V : X.affineOpens) (h : U.1 ≤ V.1)
    (a : ↥(I.ideal V ^ n)) (b : ↥(I.ideal U ^ n))
    (hb : (b : Γ(X, U)) = X.presheaf.map (homOfLE h).op (a : Γ(X, V))) :
    (reesModule I (n : ℤ)).val.map (homOfLE h).op (reesSection I n V a) =
      reesSection I n U b :=
  eq_reesSection_of_coe_eq I n U _ b
    ((Stacks.Blowup.reesPieceAffineEquiv_restrict I (n : ℤ) (Int.natCast_nonneg n) U V h _).trans
      ((congrArg _ (reesSection_coe I n V a)).trans hb.symm))

/-- The degree-`n` sections of the Rees algebra turn multiplication of ideal elements into the
graded multiplication. -/
lemma reesSection_mul (n m : ℕ) (U : X.affineOpens) (a : ↥(I.ideal U ^ n))
    (b : ↥(I.ideal U ^ m)) (c : ↥(I.ideal U ^ (n + m))) (hc : (c : Γ(X, U)) = a * b) :
    reesSection I (n + m) U c =
      ((Stacks.Blowup.reesGradedAlgebra I).mul (n : ℤ) (m : ℤ)).app (op U.1)
        (reesSection I n U a) (reesSection I m U b) :=
  (eq_reesSection_of_coe_eq I (n + m) U _ c
    ((Stacks.Blowup.reesPieceAffineEquiv_mul I (n : ℤ) (m : ℤ) (Int.natCast_nonneg n)
      (Int.natCast_nonneg m) U _ _).trans
      (by rw [reesSection_coe, reesSection_coe, hc]))).symm

/-- The degree-zero section coming from `1` is the graded unit. -/
lemma reesSection_one (U : X.affineOpens) (a : ↥(I.ideal U ^ 0)) (ha : (a : Γ(X, U)) = 1) :
    reesSection I 0 U a = (Stacks.Blowup.reesGradedAlgebra I).one.eval (op U.1) :=
  (eq_reesSection_of_coe_eq I 0 U _ a
    ((Stacks.Blowup.reesPieceAffineEquiv_one I U).trans ha.symm)).symm

end Rees

/-! ### Local sections of the pulled-back Rees algebra -/

section ReesPullback

variable {Z X : Scheme.{u}} (I : X.IdealSheafData) (g : Z ⟶ X)

/-- Pulling a section back, as an additive map. -/
noncomputable def pullbackSectionAddHom (M : X.Modules) (U : X.Opens) :
    M.val.obj (op U) →+ ((Scheme.Modules.pullback g).obj M).val.obj (op (g ⁻¹ᵁ U)) :=
  (((Scheme.Modules.pullback g).obj M).val.map
      (homOfLE (le_refl (g ⁻¹ᵁ U))).op).hom.toAddMonoidHom.comp
    ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app
      (op U)).hom.toAddMonoidHom)

/-- An element of `ℐ(U)ⁿ`, as a degree-`n` section of the pullback `g^*(⨁ₙ ℐⁿ)` of the Rees
algebra over the preimage of the affine open `U`. -/
noncomputable def reesPullbackMap (n : ℕ) (U : X.affineOpens) :
    ↥(I.ideal U ^ n) →+
      ((gradedPullback g (Stacks.Blowup.reesGradedAlgebra I)).piece (n : ℤ)).val.obj
        (op (g ⁻¹ᵁ U.1)) :=
  (pullbackSectionAddHom g (reesModule I (n : ℤ)) U.1).comp (reesSection I n U)

/-- `reesPullbackMap I g n U a` is the pullback along `g` of the section `reesSection I n U a`. -/
lemma reesPullbackMap_apply (n : ℕ) (U : X.affineOpens) (a : ↥(I.ideal U ^ n)) :
    reesPullbackMap I g n U a =
      Scheme.Modules.pullbackSection g (reesModule I (n : ℤ)) U.1 (g ⁻¹ᵁ U.1) le_rfl
        (reesSection I n U a) := rfl

/-- **Exactly `ℐ(U)ⁿ⁺¹` dies in degree `n`**, on a chart with affine preimage on which the
functions surject and the kernel ideal is `ℐ(U)`. -/
lemma reesPullbackMap_eq_zero_iff (n : ℕ) (U : X.affineOpens)
    (hV : IsAffineOpen (g ⁻¹ᵁ U.1)) (hker : RingHom.ker (g.app U.1).hom = I.ideal U)
    (hsurj : Function.Surjective (g.app U.1).hom) (a : ↥(I.ideal U ^ n)) :
    reesPullbackMap I g n U a = 0 ↔ (a : Γ(X, U)) ∈ I.ideal U ^ (n + 1) :=
  reesPullbackSection_eq_zero_iff I n U g hV hker hsurj a

/-- **Every degree-`n` section over such a chart comes from `ℐ(U)ⁿ`.** -/
lemma reesPullbackMap_surjective (n : ℕ) (U : X.affineOpens)
    (hV : IsAffineOpen (g ⁻¹ᵁ U.1)) (hsurj : Function.Surjective (g.app U.1).hom) :
    Function.Surjective (reesPullbackMap I g n U) :=
  reesPullbackSection_surjective I n U g hV hsurj

/-- The local description commutes with restriction between affine charts. -/
lemma reesPullbackMap_naturality (n : ℕ) (U V : X.affineOpens) (h : U.1 ≤ V.1)
    (hZ : g ⁻¹ᵁ U.1 ≤ g ⁻¹ᵁ V.1) (a : ↥(I.ideal V ^ n)) (b : ↥(I.ideal U ^ n))
    (hb : (b : Γ(X, U)) = X.presheaf.map (homOfLE h).op (a : Γ(X, V))) :
    ((gradedPullback g (Stacks.Blowup.reesGradedAlgebra I)).piece (n : ℤ)).val.map
        (homOfLE hZ).op (reesPullbackMap I g n V a) =
      reesPullbackMap I g n U b :=
  (pullbackSection_restrict g (reesModule I (n : ℤ)) h hZ (reesSection I n V a)).trans
    (congrArg (Scheme.Modules.pullbackSection g (reesModule I (n : ℤ)) U.1 (g ⁻¹ᵁ U.1) le_rfl)
      (reesSection_restrict I n U V h a b hb))

/-- The local description is linear over the map on functions. -/
lemma reesPullbackMap_smul (n : ℕ) (U : X.affineOpens) (r : Γ(X, U))
    (a : ↥(I.ideal U ^ n)) :
    reesPullbackMap I g n U (r • a) =
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U.1)) from (g.app U.1).hom r) •
        reesPullbackMap I g n U a :=
  (congrArg (Scheme.Modules.pullbackSection g (reesModule I (n : ℤ)) U.1 (g ⁻¹ᵁ U.1) le_rfl)
      (reesSection_smul I n U r a)).trans
    (pullbackSection_smul g (reesModule I (n : ℤ)) U.1 r (reesSection I n U a))

/-- The local description turns multiplication of ideal elements into the graded
multiplication. -/
lemma reesPullbackMap_mul (n m : ℕ) (U : X.affineOpens) (a : ↥(I.ideal U ^ n))
    (b : ↥(I.ideal U ^ m)) (c : ↥(I.ideal U ^ (n + m))) (hc : (c : Γ(X, U)) = a * b) :
    reesPullbackMap I g (n + m) U c =
      ((gradedPullback g (Stacks.Blowup.reesGradedAlgebra I)).mul (n : ℤ) (m : ℤ)).app
          (op (g ⁻¹ᵁ U.1)) (reesPullbackMap I g n U a) (reesPullbackMap I g m U b) :=
  (congrArg
      (Scheme.Modules.pullbackSection g (reesModule I ((n : ℤ) + (m : ℤ))) U.1 (g ⁻¹ᵁ U.1) le_rfl)
      (reesSection_mul I n m U a b c hc)).trans
    (gradedPullback_mul_pullbackSection g (Stacks.Blowup.reesGradedAlgebra I) (n : ℤ) (m : ℤ)
      U.1 (reesSection I n U a) (reesSection I m U b)).symm

/-- The local description sends `1` to the graded unit. -/
lemma reesPullbackMap_one (U : X.affineOpens) (a : ↥(I.ideal U ^ 0))
    (ha : (a : Γ(X, U)) = 1) :
    reesPullbackMap I g 0 U a =
      (gradedPullback g (Stacks.Blowup.reesGradedAlgebra I)).one.eval (op (g ⁻¹ᵁ U.1)) :=
  (congrArg (Scheme.Modules.pullbackSection g (reesModule I (0 : ℤ)) U.1 (g ⁻¹ᵁ U.1) le_rfl)
      (reesSection_one I U a ha)).trans
    (gradedPullback_one_eval g (Stacks.Blowup.reesGradedAlgebra I) U.1).symm

end ReesPullback

end Stacks.Conormal

end
