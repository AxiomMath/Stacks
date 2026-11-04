module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.Module.Free.OfAdicQuotients

/-!
# The stalk of an ideal-power quotient, and freeness across a change of base ring

Let `X` be a locally Noetherian scheme, `ℐ` a sheaf of ideals and `𝒢` a module of finite
presentation. If every adic quotient `𝒢 / ℐ ^ (n + 1) 𝒢` is the direct image of a finite locally
free module on the infinitesimal neighbourhood `Yₙ`, then `𝒢` is free at every point of the
support of `ℐ`.

## Main definitions

* `Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`: the stalk of `ℳ / ℐ ^ n ℳ` at a
  point `x` is `ℳ_x / ℐ_x ^ n ℳ_x`, for `ℳ` quasi-coherent.
* `Stacks.Algebraization.stalkPushforwardModuleLinearEquiv`: the stalk of `i_* ℳ` at `i z` is the
  stalk of `ℳ` at `z`, for `i` with inducing underlying map.

## Main results

* `Stacks.Algebraization.free_of_ringEquiv_of_addEquiv`: freeness transported along a ring
  isomorphism `R ≃+* S` and an additive isomorphism of an `R`-module with an `S`-module which is
  semilinear over it.
* `Stacks.Algebraization.free_quotient_stalk_of_pushforward_iso`: `𝒢_y / ℐ_y ^ t 𝒢_y` is free over
  `𝒪_{X,y} / ℐ_y ^ t` when `𝒢 / ℐ ^ t 𝒢` is the direct image of a finite locally free module.
* `Stacks.Algebraization.free_stalk_of_forall_pushforward_iso`: the stalk `𝒢_y` is free.

## References

* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-! ### The stalk of an ideal-power quotient -/

variable {X : Scheme.{u}}

/-- The stalk of `ℳ / ℐ ^ n ℳ` is `ℳ_x / ℐ_x ^ n ℳ_x`, for a quasi-coherent `ℳ`. -/
def idealPowerQuotientStalkLinearEquiv (J : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (x : X) :
    ((modulesStalkFunctor X x).obj M ⧸
        (IdealSheafData.stalk J x ^ n •
          (⊤ : Submodule (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M))))
      ≃ₗ[X.presheaf.stalk x] (modulesStalkFunctor X x).obj (idealPowerQuotient J n M) :=
  (Submodule.quotEquivOfEq _ _
      ((stalk_idealPowerMultiple J n M x).symm.trans
        (range_stalk_submodule_ι_eq_ker_stalk_cokernel_π (idealPowerMultiple J n M) x))).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_stalk_cokernel_π _ x))

/-! ### Freeness across a change of base ring -/

/-- If `e : R ≃+* S`, `N` is a free `S`-module and `f : M ≃+ N` is an additive isomorphism from
an `R`-module `M` satisfying `f (r • m) = e r • f m`, then `M` is a free `R`-module. -/
theorem free_of_ringEquiv_of_addEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M ≃+ N) (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m)
    [Module.Free S N] : Module.Free R M := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := S) (M := N)
  let g : M ≃+ (ι →₀ R) :=
    f.trans (b.repr.toAddEquiv.trans (Finsupp.mapRange.addEquiv e.toAddEquiv).symm)
  refine Module.Free.of_basis (ι := ι) (Module.Basis.ofRepr
    { toFun := g, invFun := g.symm, map_add' := g.map_add,
      left_inv := g.left_inv, right_inv := g.right_inv, map_smul' := fun r m => ?_ })
  ext j
  simp only [g, AddEquiv.trans_apply, hf, LinearEquiv.coe_toAddEquiv,
    Finsupp.mapRange.addEquiv_symm, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply,
    Finsupp.smul_apply, smul_eq_mul, RingEquiv.toAddEquiv_eq_coe]
  simp

/-! ### The stalk of a direct image along a closed immersion -/

/-- The stalk of `i_* ℳ` at `i z`, for `i` with inducing underlying map, is the stalk of `ℳ` at
`z`, as a module over `𝒪_{X, i z}` by restriction of scalars along the stalk map of `i`. -/
def stalkPushforwardModuleLinearEquiv {Z : Scheme.{u}} (i : Z ⟶ X) (M : Z.Modules) (z : Z)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) :
    letI : Module (X.presheaf.stalk (i z)) (M.presheaf.stalk z) :=
      Module.compHom _ (i.stalkMap z).hom
    ((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z)
      ≃ₗ[X.presheaf.stalk (i z)] M.presheaf.stalk z :=
  letI : Module (X.presheaf.stalk (i z)) (M.presheaf.stalk z) :=
    Module.compHom _ (i.stalkMap z).hom
  { toFun := Stacks.Chow.stalkPushforwardComparison i M z
    map_add' := Stacks.Chow.stalkPushforwardComparison_add i M z
    map_smul' := Stacks.Chow.stalkPushforwardComparison_smul i M z
    invFun := Function.surjInv (Stacks.Chow.bijective_stalkPushforwardComparison i M z hi).2
    left_inv :=
      Function.leftInverse_surjInv (Stacks.Chow.bijective_stalkPushforwardComparison i M z hi)
    right_inv :=
      Function.rightInverse_surjInv
        (Stacks.Chow.bijective_stalkPushforwardComparison i M z hi).2 }

/-- The stalk of a finite locally free module, in the sense of
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, is free. -/
theorem free_stalk_of_isFiniteLocallyFree {Z : Scheme.{u}} (M : Z.Modules)
    (hM : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree M) (z : Z) :
    Module.Free (Z.presheaf.stalk z) (M.presheaf.stalk z) :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators M).mp hM
  (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree M z).1

/-! ### Freeness of the adic quotients of a stalk -/

/-- If the `t`-th adic quotient `𝒢 / ℐ ^ t 𝒢` of a quasi-coherent module is the direct image of
a finite locally free module on the closed subscheme cut out by `ℐ ^ t`, then at a point `y` of
the support of `ℐ` the module `𝒢_y / ℐ_y ^ t 𝒢_y` is free over `𝒪_{X,y} / ℐ_y ^ t`. -/
theorem free_quotient_stalk_of_pushforward_iso (J : X.IdealSheafData) (G : X.Modules)
    [G.IsQuasicoherent] {t : ℕ} (ht : t ≠ 0) {y : X} (hy : y ∈ J.support)
    (N : (J ^ t).subscheme.Modules)
    (hN : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree N)
    (e : idealPowerQuotient J t G ≅ (Scheme.Modules.pushforward (J ^ t).subschemeι).obj N) :
    Module.Free (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t)
      ((modulesStalkFunctor X y).obj G ⧸
        (IdealSheafData.stalk J y ^ t •
          (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj G)))) := by
  classical
  have hind : Topology.IsInducing (ConcreteCategory.hom ((J ^ t).subschemeι).base) :=
    (IsClosedImmersion.isClosedEmbedding ((J ^ t).subschemeι)).isInducing
  let z : (J ^ t).subscheme := idealPowSubschemePoint J ht y hy
  let _ : Module (X.presheaf.stalk y) (N.presheaf.stalk z) :=
    Module.compHom _ (((J ^ t).subschemeι).stalkMap z).hom
  have : Module.Free ((J ^ t).subscheme.presheaf.stalk z) (N.presheaf.stalk z) :=
    free_stalk_of_isFiniteLocallyFree N hN z
  let eRing : (X.presheaf.stalk y ⧸ IdealSheafData.stalk J y ^ t) ≃+*
      ((J ^ t).subscheme.presheaf.stalk z) :=
    (Ideal.quotEquivOfEq (IdealSheafData.stalk_pow J t y).symm).trans
      (IdealSheafData.subschemeStalkQuotEquiv (J ^ t) z)
  have f₃ : ((Scheme.Modules.pushforward ((J ^ t).subschemeι)).obj N).presheaf.stalk y
      ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
    stalkPushforwardModuleLinearEquiv ((J ^ t).subschemeι) N z hind
  have fL : ((modulesStalkFunctor X y).obj G ⧸
        (IdealSheafData.stalk J y ^ t •
          (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj G))))
      ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk z :=
    ((idealPowerQuotientStalkLinearEquiv J t G y).trans
      ((modulesStalkFunctor X y).mapIso e).toLinearEquiv).trans f₃
  refine free_of_ringEquiv_of_addEquiv eRing fL.toAddEquiv fun c m => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hsmul : (Ideal.Quotient.mk (IdealSheafData.stalk J y ^ t) r) • m = r • m :=
    algebraMap_smul _ r m
  have heR : eRing (Ideal.Quotient.mk (IdealSheafData.stalk J y ^ t) r) =
      ((J ^ t).subschemeι).stalkMap z r :=
    IdealSheafData.subschemeStalkQuotEquiv_mk (J ^ t) z r
  change fL _ = _
  rw [hsmul, heR, fL.map_smul]
  rfl

/-- Let `X` be locally Noetherian, `ℐ` a sheaf of ideals, `𝒢` a module of finite presentation and
`y` a point of the support of `ℐ`. If every adic quotient `𝒢 / ℐ ^ (n + 1) 𝒢` is the direct image
of a finite locally free module on the infinitesimal neighbourhood `Yₙ`, then the stalk `𝒢_y` is
a free `𝒪_{X,y}`-module. -/
theorem free_stalk_of_forall_pushforward_iso (J : X.IdealSheafData) [IsLocallyNoetherian X]
    (G : X.Modules) [G.IsFinitePresentation] [G.IsQuasicoherent] {y : X} (hy : y ∈ J.support)
    (h : ∀ n : ℕ, ∃ N : (J ^ (n + 1)).subscheme.Modules,
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree N ∧
        Nonempty (idealPowerQuotient J (n + 1) G ≅
          (Scheme.Modules.pushforward (J ^ (n + 1)).subschemeι).obj N)) :
    Module.Free (ToType (X.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) := by
  have : Module.FinitePresentation (ToType (X.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) :=
    Stacks.StalkFiniteType.finitePresentation_stalk G y
  have hI : IdealSheafData.stalk J y ≠ ⊤ := fun hc =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support J y).mp hc hy
  refine Stacks.FreeOfAdicQuotients.free_of_forall_free_quotient_pow_smul_top hI fun n => ?_
  obtain ⟨N, hN, ⟨e⟩⟩ := h n
  exact free_quotient_stalk_of_pushforward_iso J G (Nat.succ_ne_zero n) hy N hN e

end Stacks.Algebraization

end
