module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleEquivariantSheaf

/-!
# Combinations of canonical pullback sections

Let `F` be a quasi-coherent module on a scheme `Z` and let `p : W ⟶ Z`.  A finitely supported
family `(mᵢ)` of global sections of `F` together with a family `(rᵢ)` of global functions on `W`
gives the global section `∑ rᵢ · (mᵢ ⊗ 1)` of the pullback `p^* F`, where `mᵢ ⊗ 1` is the
canonical pullback section.  This file develops that combination map, the transport of sections
of a pullback along a further morphism, and the two facts about them that a morphism of affine
schemes supplies: the base-change identification of
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso` carries `r · (m ⊗ 1)` to the pure
tensor `r ⊗ m`, and a base change along a ring map free on a prescribed family writes every
element uniquely as a combination of that family.

This is the apparatus a `𝐆ₘ`-equivariant module needs in order to read its descent morphism in
coefficients: for `W = 𝐆ₘ × Z` the coefficients are the Laurent monomials `xⁿ` and the ring of
`W` is free over the ring of `Z` on them, so a section of the pullback has *unique*
coefficients.

## Main definitions

* `AlgebraicGeometry.GmEquivariant.pullbackSectionHom` is the canonical pullback section as an
  additive homomorphism.
* `AlgebraicGeometry.GmEquivariant.pullbackTransport` reads a global section of a pullback along
  `p` as a global section of the pullback along `f ≫ p`.
* `AlgebraicGeometry.GmEquivariant.sectionsCombination` is the combination map above.

## Main results

* `AlgebraicGeometry.GmEquivariant.pullbackTransport_pullbackSection`,
  `AlgebraicGeometry.GmEquivariant.pullbackTransport_smul` and
  `AlgebraicGeometry.GmEquivariant.pullbackTransport_sectionsCombination` compute the transport
  on canonical pullback sections, on rescalings and on combinations, and
  `AlgebraicGeometry.GmEquivariant.bijective_pullbackTransport` shows it is bijective along an
  isomorphism of schemes.
* `AlgebraicGeometry.GmEquivariant.bijective_finsuppSumTmul`: a base change along a ring map
  which is free on a prescribed family writes every element uniquely as a finitely supported
  combination of that family.
* `AlgebraicGeometry.GmEquivariant.sectionsPullbackIso_smul_pullbackSection`: over a morphism of
  affine schemes the base-change identification carries `r · (m ⊗ 1)` to `r ⊗ m`.
* `AlgebraicGeometry.GmEquivariant.bijective_sectionsCombination_specMap`: over a morphism of
  affine schemes whose ring map is free on a prescribed family, every global section of the
  pullback is uniquely such a combination.

## Implementation notes

The value of the base-change identification on an unrescaled canonical pullback section is
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.sectionsPullbackIso_hom_unit`; only the
rescaled form is proved here, and the canonical pullback section is the unit of the
pullback--pushforward adjunction on global sections, so the two match by `rfl`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0EKL](https://stacks.math.columbia.edu/tag/0EKL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u v w

namespace AlgebraicGeometry.GmEquivariant

/-! ### Transport of sections of a pullback along a further morphism -/

/-- The canonical pullback section, as an additive homomorphism. -/
noncomputable def pullbackSectionHom {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules) :
    Γ(F, ⊤) →+ Γ((Scheme.Modules.pullback p).obj F, ⊤) where
  toFun := pullbackSection p F
  map_zero' := pullbackSection_zero p F
  map_add' := pullbackSection_add p F

/-- Reading a global section of a pullback through a further morphism: the canonical map from
the sections of the pullback along `p` to the sections of the pullback along `f ≫ p`. -/
noncomputable def pullbackTransport {W' W Z : Scheme.{u}} (f : W' ⟶ W) (p : W ⟶ Z)
    (F : Z.Modules) :
    Γ((Scheme.Modules.pullback p).obj F, ⊤) →+
      Γ((Scheme.Modules.pullback (f ≫ p)).obj F, ⊤) where
  toFun w := ((Scheme.Modules.pullbackComp f p).hom.app F).app ⊤
    (pullbackSection f ((Scheme.Modules.pullback p).obj F) w)
  map_zero' := by
    rw [pullbackSection_zero]
    exact map_zero _
  map_add' a b := by
    rw [pullbackSection_add]
    exact map_add _ _ _

/-- The transport of `w` is the image under the composition isomorphism of the canonical pullback
section of `w` along `f`. -/
theorem pullbackTransport_apply {W' W Z : Scheme.{u}} (f : W' ⟶ W) (p : W ⟶ Z)
    (F : Z.Modules) (w : Γ((Scheme.Modules.pullback p).obj F, ⊤)) :
    pullbackTransport f p F w =
      ((Scheme.Modules.pullbackComp f p).hom.app F).app ⊤
        (pullbackSection f ((Scheme.Modules.pullback p).obj F) w) :=
  rfl

/-- Transport carries the canonical pullback section of a global section to the canonical
pullback section along the composite. -/
theorem pullbackTransport_pullbackSection {W' W Z : Scheme.{u}} (f : W' ⟶ W) (p : W ⟶ Z)
    (F : Z.Modules) (s : Γ(F, ⊤)) :
    pullbackTransport f p F (pullbackSection p F s) = pullbackSection (f ≫ p) F s :=
  pullbackSection_comp_hom f p F s

/-- Transport is semilinear: a global function on the target is pulled back along `f`. -/
theorem pullbackTransport_smul {W' W Z : Scheme.{u}} (f : W' ⟶ W) (p : W ⟶ Z)
    (F : Z.Modules) (r : Γ(W, ⊤)) (w : Γ((Scheme.Modules.pullback p).obj F, ⊤)) :
    pullbackTransport f p F (r • w) = f.appTop r • pullbackTransport f p F w := by
  rw [pullbackTransport_apply, pullbackTransport_apply, pullbackSection_smul,
    Scheme.Modules.Hom.app_smul]

/-- Transport along an isomorphism of schemes is bijective. -/
theorem bijective_pullbackTransport {W' W Z : Scheme.{u}} (f : W' ⟶ W) [IsIso f] (p : W ⟶ Z)
    (F : Z.Modules) : Function.Bijective (pullbackTransport f p F) := by
  have := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isEquivalence_pullback f
  have h₁ : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback p).obj F)).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  have h₂ : Function.Bijective
      ((((Scheme.Modules.pullbackComp f p).hom.app F)).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  exact h₂.comp h₁

/-! ### Combinations of canonical pullback sections -/

/-- The additive map sending a finitely supported family `(mᵢ)` of global sections of `F` to
`∑ rᵢ · (mᵢ ⊗ 1)`, the combination of the canonical pullback sections along `p` with
prescribed coefficients `rᵢ`. -/
noncomputable def sectionsCombination {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx : Type*} (r : Idx → Γ(W, ⊤)) :
    (Idx →₀ Γ(F, ⊤)) →+ Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
  Finsupp.liftAddHom fun i =>
    AddMonoidHom.comp (DistribSMul.toAddMonoidHom _ (r i)) (pullbackSectionHom p F)

/-- The combination of a single section `m` at index `i` is `r i • (m ⊗ 1)`. -/
@[simp]
theorem sectionsCombination_single {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx : Type*} (r : Idx → Γ(W, ⊤)) (i : Idx) (m : Γ(F, ⊤)) :
    sectionsCombination p F r (Finsupp.single i m) = r i • pullbackSection p F m := by
  classical
  rw [sectionsCombination, Finsupp.liftAddHom_apply_single]
  rfl

/-- The combination of a family `(mᵢ)` is the sum `∑ rᵢ • (mᵢ ⊗ 1)`. -/
theorem sectionsCombination_apply {W Z : Scheme.{u}} (p : W ⟶ Z) (F : Z.Modules)
    {Idx : Type*} (r : Idx → Γ(W, ⊤)) (f : Idx →₀ Γ(F, ⊤)) :
    sectionsCombination p F r f = f.sum fun i m => r i • pullbackSection p F m := by
  classical
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun i _ => sectionsCombination_single p F r i _

/-- Transport carries a combination of canonical pullback sections to the combination with the
pulled-back coefficients. -/
theorem pullbackTransport_sectionsCombination {W' W Z : Scheme.{u}} (f : W' ⟶ W) (p : W ⟶ Z)
    (F : Z.Modules) {Idx : Type*} (r : Idx → Γ(W, ⊤)) :
    (pullbackTransport f p F).comp (sectionsCombination p F r) =
      sectionsCombination (f ≫ p) F fun i => f.appTop (r i) := by
  refine Finsupp.addHom_ext fun i m => ?_
  rw [AddMonoidHom.comp_apply, sectionsCombination_single, sectionsCombination_single,
    pullbackTransport_smul, pullbackTransport_pullbackSection]

/-! ### Free base change of a tensor product -/

/-- Coordinatizing a free base change sends the pure tensor of a basis vector to a single. -/
private theorem rTensor_finsuppScalarLeft_tmul {R T M : Type*} [CommRing R] [AddCommMonoid T]
    [Module R T] [AddCommGroup M] [Module R M] {Idx : Type*} [DecidableEq Idx]
    (eta : T ≃ₗ[R] (Idx →₀ R)) (t : T) (i : Idx) (ht : eta t = Finsupp.single i 1) (m : M) :
    ((eta.rTensor M).trans (TensorProduct.finsuppScalarLeft R M Idx)) (t ⊗ₜ[R] m) =
      Finsupp.single i m := by
  rw [LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul, ht,
    TensorProduct.finsuppScalarLeft_apply_tmul]
  simp

/-- A base change along a ring map which is free on a prescribed family writes every element
uniquely as a finitely supported combination of that family. -/
theorem bijective_finsuppSumTmul {R T : Type u} [CommRing R] [CommRing T] [Module R T]
    {M : Type u} [AddCommGroup M] [Module R M] {Idx : Type w}
    (eta : T ≃ₗ[R] (Idx →₀ R)) (t : Idx → T) (ht : ∀ i, eta (t i) = Finsupp.single i 1) :
    Function.Bijective (fun f : Idx →₀ M => f.sum fun i m => (t i) ⊗ₜ[R] m) := by
  classical
  set Φ : TensorProduct R T M ≃ₗ[R] (Idx →₀ M) :=
    (eta.rTensor M).trans (TensorProduct.finsuppScalarLeft R M Idx) with hΦ
  have hΦt (i : Idx) (m : M) : Φ ((t i) ⊗ₜ[R] m) = Finsupp.single i m :=
    rTensor_finsuppScalarLeft_tmul eta (t i) i (ht i) m
  have hcomp (f : Idx →₀ M) : Φ (f.sum fun i m => (t i) ⊗ₜ[R] m) = f := by
    induction f using Finsupp.induction_linear with
    | zero => rw [Finsupp.sum_zero_index, map_zero]
    | add p q hp hq =>
      rw [Finsupp.sum_add_index' (fun i => TensorProduct.tmul_zero _ _)
        (fun i m₁ m₂ => TensorProduct.tmul_add _ _ _), map_add, hp, hq]
    | single i m =>
      rw [show (Finsupp.single i m).sum (fun i m => (t i) ⊗ₜ[R] m) = (t i) ⊗ₜ[R] m from
        Finsupp.sum_single_index (TensorProduct.tmul_zero _ (t i)), hΦt]
  have heq (f : Idx →₀ M) : (f.sum fun i m => (t i) ⊗ₜ[R] m) = Φ.symm f :=
    Φ.injective (by rw [hcomp, LinearEquiv.apply_symm_apply])
  rw [funext heq]
  exact Φ.symm.bijective

/-! ### Sections of a pullback along a morphism of affine schemes -/

open Stacks.AlgebraicGeometry.SectionsColimit in
/-- The base-change identification is semilinear for the global functions on `Spec T`. -/
theorem sectionsPullbackIso_smul {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (F : (Spec R).Modules) [F.IsQuasicoherent] (t : T)
    (z : Γ((Scheme.Modules.pullback (Spec.map φ)).obj F, ⊤)) :
    ((sectionsPullbackIso φ F).hom).hom ((Scheme.ΓSpecIso T).inv t • z) =
      t • ((sectionsPullbackIso φ F).hom).hom z :=
  map_smul ((sectionsPullbackIso φ F).hom).hom t z

open Stacks.AlgebraicGeometry.SectionsColimit in
/-- The base-change identification carries a rescaled canonical pullback section to the
corresponding pure tensor. -/
theorem sectionsPullbackIso_smul_pullbackSection {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (F : (Spec R).Modules) [F.IsQuasicoherent] (s : T) (m : Γ(F, ⊤)) :
    ((sectionsPullbackIso φ F).hom).hom
        ((Scheme.ΓSpecIso T).inv s • pullbackSection (Spec.map φ) F m) =
      s ⊗ₜ[R, φ.hom] m :=
  ((sectionsPullbackIso_smul φ F s (pullbackSection (Spec.map φ) F m)).trans
    (congrArg (fun z => s • z)
      (Stacks.AlgebraicGeometry.AffineBaseChangeLocality.sectionsPullbackIso_hom_unit φ F m
        (pullbackSection (Spec.map φ) F m) rfl))).trans
      ((ModuleCat.ExtendScalars.smul_tmul (M := moduleSpecΓFunctor.obj F) φ.hom s 1 m).trans
        (congrArg (fun a : T => a ⊗ₜ[R, φ.hom] m) (mul_one s)))

/-! ### Unique coefficients over a free base change -/

/-- The identification of a free base change with finitely supported families, on the pure
tensor of a basis vector. -/
theorem finsuppScalarLeft_single_one_tmul {R : Type u} [CommRing R] {N : Type v}
    [AddCommGroup N] [Module R N] {Idx : Type w} [DecidableEq Idx] (i : Idx) (n : N) :
    TensorProduct.finsuppScalarLeft R N Idx ((Finsupp.single i (1 : R)) ⊗ₜ[R] n) =
      Finsupp.single i n := by
  rw [TensorProduct.finsuppScalarLeft_apply_tmul]
  simp

open Stacks.AlgebraicGeometry.SectionsColimit in
/-- Over a morphism of affine schemes whose ring map is free on a prescribed family, every
global section of the pullback of a quasi-coherent module is uniquely a combination of the
canonical pullback sections with those coefficients. -/
theorem bijective_sectionsCombination_specMap {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (F : (Spec R).Modules) [F.IsQuasicoherent] {Idx : Type w}
    (eta : T ≃+ (Idx →₀ R)) (heta : ∀ (r : R) (x : T), eta (φ r * x) = r • eta x)
    (t : Idx → T) (ht : ∀ i, eta (t i) = Finsupp.single i 1) :
    Function.Bijective
      (sectionsCombination (Spec.map φ) F fun i => (Scheme.ΓSpecIso T).inv (t i)) := by
  classical
  let etaL : ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of T T)) ≃ₗ[R] (Idx →₀ R) :=
    @AddEquiv.toLinearEquiv R T (Idx →₀ R) _ _ _
      (((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of T T)).isModule) _ eta heta
  let E : ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F)) ≃+
      (Idx →₀ Γ(F, ⊤)) :=
    ((etaL.rTensor (moduleSpecΓFunctor.obj F)).trans
      (TensorProduct.finsuppScalarLeft R (moduleSpecΓFunctor.obj F) Idx)).toAddEquiv
  have hE : ∀ (i : Idx) (m : Γ(F, ⊤)), E (t i ⊗ₜ[R, φ.hom] m) = Finsupp.single i m :=
    fun i m => rTensor_finsuppScalarLeft_tmul etaL (t i) i (ht i) m
  set g : Γ((Scheme.Modules.pullback (Spec.map φ)).obj F, ⊤) →+ (Idx →₀ Γ(F, ⊤)) :=
    E.toAddMonoidHom.comp ((sectionsPullbackIso φ F).hom).hom.toAddMonoidHom
  have hgbij : Function.Bijective g :=
    E.bijective.comp (ConcreteCategory.bijective_of_isIso (sectionsPullbackIso φ F).hom)
  have hid : g.comp (sectionsCombination (Spec.map φ) F fun i =>
      (Scheme.ΓSpecIso T).inv (t i)) = AddMonoidHom.id _ := by
    refine Finsupp.addHom_ext fun i m => ?_
    exact (congrArg (fun z => E (((sectionsPullbackIso φ F).hom).hom z))
        (sectionsCombination_single (Spec.map φ) F
          (fun i => (Scheme.ΓSpecIso T).inv (t i)) i m)).trans
      ((congrArg E (sectionsPullbackIso_smul_pullbackSection φ F (t i) m)).trans (hE i m))
  refine (hgbij.of_comp_iff' _).mp ?_
  rw [← AddMonoidHom.coe_comp, hid]
  exact Function.bijective_id

end AlgebraicGeometry.GmEquivariant

end
