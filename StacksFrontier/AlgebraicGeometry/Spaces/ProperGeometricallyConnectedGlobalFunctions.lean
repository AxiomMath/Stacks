module

public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Global functions of a proper, geometrically reduced and connected algebraic space

Let `X` be a proper algebraic space over a field `k` which is geometrically reduced and
geometrically connected. Then `k = H⁰(X, 𝒪_X)`: the canonical map from `k` to the ring of global
regular functions of `X` is bijective. This is the case of [Stacks, Tag 0DMY] used in the proof
of [Stacks, Tag 0E0S], and it is proved here without the finiteness of cohomology of proper
algebraic spaces ([Stacks, Tag 08AS]).

Over an algebraically closed field `K`, Chow's lemma ([Stacks, Tag 089J]) gives a proper
surjection `X' ⟶ X_K` from a scheme proper over `K`. Pullback of global functions along it is
injective because `X_K` is reduced, so `Γ(X_K)` embeds into the finite dimensional `Γ(X')`
([Stacks, Tag 0BUG] (1)); being reduced, finite dimensional and without nontrivial idempotents
(as `|X_K|` is connected), it is `K`. To descend to `k` one base changes to an algebraic closure
`K` of `k` and reads a global function on an affine étale chart `W` of `X` and on its base change
`W_K = W ×_k K`: an element of `Γ(W)` which becomes a constant of `K` in `Γ(W) ⊗_k K` is a
constant of `k`.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsChangeOfBase`: pullback of global functions along the
  base change `X_S ⟶ X` of an algebraic space along a morphism of base schemes `S ⟶ S'`.

## Main results

* `AlgebraicGeometry.Space.isProper_toBase_relocalizeRestrict`: properness over the base is
  preserved by base change along a morphism of base schemes.
* `AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper_of_isReduced`: the global
  functions of a reduced proper algebraic space over a field are finite dimensional.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_isAlgClosed`: over an
  algebraically closed field, a proper, reduced, connected algebraic space has only constant
  global functions.
* `AlgebraicGeometry.Space.exists_algebraMap_eq_of_globalFunctionsChangeOfBase`: constants
  descend along a field extension.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_isProper` and
  `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_isGeometricallyReduced`:
  `k = H⁰(X, 𝒪_X)` for `X` proper over `k`, with geometric reducedness and connectedness read on
  the base changes to algebraically closed fields, respectively given by Stacks 0DMQ and 0A0Z.

## Implementation notes

Base change to a field `K` is restriction along the localization functor, so the fields quantified
over are those whose spectrum lies in the chosen big fppf site; the algebraic closure of `k` does
(`AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure`). No declaration here carries a
Stacks attribute: Tag 0DMY asserts more (finite dimensionality and the componentwise splitting for
every proper `X`), and Tag 0E0S is the relative statement this feeds.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- On an algebraic space whose point space is connected, every idempotent global function is
`0` or `1`: its support is clopen, hence empty or everything, and an idempotent function on a
scheme with empty, respectively full, basic open is `0`, respectively `1`. -/
theorem isIdempotentElem_eq_zero_or_one_of_connectedPoints (hconn : ConnectedPoints B S hS F)
    (s : globalFunctions B S hS F) (hs : IsIdempotentElem s) : s = 0 ∨ s = 1 := by
  let := pointTopology B S hS F
  have hcl := isClopen_sectionSupport B S hS F hF s hs
  have hval (U : (SmallEtale B S hS F)ᵒᵖ) : IsIdempotentElem (s.val U) :=
    congrArg (fun t : globalFunctions B S hS F => t.val U) hs.eq
  rcases isClopen_iff.mp hcl with h | h
  · left
    apply Subtype.ext
    funext U
    refine (Scheme.isIdempotentElem_eq_of_basicOpen _ _ (hval U)).2 fun x hx => ?_
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS U.unop.obj.left x
    have := (mem_sectionSupport_iff B S hS F s U.unop p).mpr hx
    rw [h] at this
    exact this
  · right
    apply Subtype.ext
    funext U
    refine (Scheme.isIdempotentElem_eq_of_basicOpen _ _ (hval U)).1 fun x => ?_
    obtain ⟨p, rfl⟩ := surjective_pointsToScheme B S hS U.unop.obj.left x
    exact (mem_sectionSupport_iff B S hS F s U.unop p).mp (h ▸ Set.mem_univ _)

include hF in
/-- The ring of global functions of an algebraic space with a point is nontrivial: the point
lies on an étale chart, whose scheme is then nonempty. -/
theorem nontrivial_globalFunctions_of_nonempty (x : points B S hS F) :
    Nontrivial (globalFunctions B S hS F) := by
  let := pointTopology B S hS F
  obtain ⟨U, p, -⟩ := exists_chart_point B S hS F hF x
  refine nontrivial_of_ne 0 1 fun h => ?_
  have h' : (0 : Γ((BigFppfOver.toScheme B S hS).obj U.obj.left, ⊤)) = 1 :=
    congrArg (fun t : globalFunctions B S hS F => t.val (op U)) h
  have hg := congrArg (((BigFppfOver.toScheme B S hS).obj U.obj.left).presheaf.germ ⊤
    (pointsToScheme B S hS U.obj.left p) trivial).hom h'
  rw [map_zero, map_one] at hg
  exact zero_ne_one hg

end Chart

/-- The ring of global functions of an algebraic space with connected point space is
nontrivial. -/
private theorem nontrivial_globalFunctions_of_connectedPoints (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hconn : ConnectedPoints B S hS F) :
    Nontrivial (globalFunctions B S hS F) := by
  let := pointTopology B S hS F
  exact nontrivial_globalFunctions_of_nonempty B S hS F hF hconn.toNonempty.some

section Base

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- Pullback of global functions to a scheme over the base is a homomorphism of `A`-algebras,
for the `A`-algebra structure on the scheme's functions given by its structure morphism. -/
theorem globalFunctionsToChart_algebraMap {T : BigFppfOver B (Spec (.of A)) hA}
    (p : yoneda.obj T ⟶ X) (a : A) :
    globalFunctionsToChart B (Spec (.of A)) hA ⟨X, hX⟩ p
        (algebraMap A (globalFunctions B (Spec (.of A)) hA X) a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T.hom).appTop).hom a := by
  change ((globalFunctionsChartEquiv B (Spec (.of A)) hA ⟨X, hX⟩).val _).val _ = _
  rw [globalFunctionsChartEquiv_algebraMap B A hA ⟨X, hX⟩]
  rfl

end Base

/-! ### Properness of a base change -/

section BaseChange

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') (X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)

/-- **Base change along a morphism of base schemes preserves properness over the base.**
Viewed again over `S'`, the base change of `X` along `g : S ⟶ S'` is the fibre product
`S ×_{S'} X`, so its projection to `S` is a base change of the structure morphism of `X`, and
properness of a morphism does not depend on the base scheme it is read over. -/
theorem isProper_toBase_relocalizeRestrict (hX : IsAlgebraicSpace B S' hS' X)
    (z : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS')) : BigFppfOver B S' hS'))
    (hz : IsProper B S' hS' z) :
    IsProper B S hS
      ((isTerminal_yoneda_obj_base B S hS).from ((OverShriek.relocalizeRestrict g).obj X)) := by
  set XS := (OverShriek.relocalizeRestrict g).obj X with hXS
  have hXS' : IsAlgebraicSpace B S hS XS :=
    isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g X hX
  set π : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))) := OverShriek.toYonedaMkId X with hπ
  set τ : yoneda.obj (Over.mk g) ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))) :=
    OverShriek.toYonedaMkId (yoneda.obj (Over.mk g)) with hτ
  have hsq : IsPullback (OverShriek.relocalizeRestrictCounit g X)
      (OverShriek.relocalizeToYoneda g XS) π τ :=
    OverShriek.isPullback_relocalizeRestrictCounit g X
      (fun W ↦ OverShriek.subsingleton_yoneda_obj_mkId W) π τ
  have hπz : π = z := (isTerminal_yoneda_obj_base B S' hS').hom_ext _ _
  have hP : IsAlgebraicSpace B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj XS) :=
    isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hS') g XS hXS'
  have hrel : IsProper B S' hS' (OverShriek.relocalizeToYoneda g XS) :=
    (isProper_isStableUnderBaseChange B S' hS').of_isPullback
      (isPullback_homMk B S' hS' hX (isAlgebraicSpace_yoneda B S' hS' _)
        (isAlgebraicSpace_yoneda B S' hS' _) hP hsq) (hπz ▸ hz)
  have h := (isProper_relocalizeToYoneda_iff B S S' hS hS' g XS hXS').mp hrel
  have he : toYonedaId B S hS XS = (isTerminal_yoneda_obj_base B S hS).from XS :=
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  rwa [he] at h

end BaseChange

/-! ### A tensor product computation -/

/-- In a pushout `P = R ⊗_k A` of algebras over a field `k`, with `A` nonzero, an element of `R`
whose image in `P` comes from `A` is a scalar: apply `id ⊗ φ` for a `k`-linear form `φ` on `A`
with `φ 1 = 1`. -/
theorem exists_algebraMap_eq_of_isPushout {k R A P : Type*} [Field k] [CommRing R] [CommRing A]
    [Nontrivial A] [CommRing P] [Algebra k R] [Algebra k A] [Algebra R P] [Algebra A P]
    [Algebra k P] [IsScalarTower k R P] [IsScalarTower k A P] [Algebra.IsPushout k R A P]
    {r : R} {a : A} (h : algebraMap R P r = algebraMap A P a) :
    ∃ c : k, algebraMap k R c = r := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.toSpanSingleton k A 1)
    (LinearMap.ker_eq_bot.mpr (smul_left_injective k one_ne_zero))
  have hφ1 : φ 1 = 1 := by
    simpa using LinearMap.congr_fun hφ 1
  have heq : (r ⊗ₜ[k] (1 : A)) = (1 : R) ⊗ₜ[k] a := by
    apply (Algebra.IsPushout.equiv k R A P).injective
    rw [Algebra.IsPushout.equiv_tmul, Algebra.IsPushout.equiv_tmul, map_one, map_one, mul_one,
      one_mul, h]
  have h2 := congrArg ((TensorProduct.rid k R).toLinearMap ∘ₗ LinearMap.lTensor R φ) heq
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, hφ1, one_smul] at h2
  exact ⟨φ a, by rw [h2, Algebra.algebraMap_eq_smul_one]⟩

/-- **Functions on a base change of an affine scheme along a field extension.** Let `U` be an
affine scheme over a field `k`, `K/k` a field extension and `P = U ×_k K`. A function on `U`
whose pullback to `P` is the pullback of a constant of `K` is a constant of `k`. -/
theorem exists_eq_of_isPullback_spec {k K : Type u} [Field k] [Field K] [Algebra k K]
    {U P : Scheme.{u}} [IsAffine U] {f : U ⟶ Spec (.of k)} {fst : P ⟶ U}
    {snd : P ⟶ Spec (.of K)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (r : Γ(U, ⊤)) (a : K)
    (hr : fst.appTop r = snd.appTop ((Scheme.ΓSpecIso (.of K)).inv a)) :
    ∃ c : k, ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) c = r := by
  have hpo := isPushout_appTop_of_isPullback h
  have hpo' : IsPushout ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)
      (CommRingCat.ofHom (algebraMap k K)) fst.appTop
      ((Scheme.ΓSpecIso (.of K)).inv ≫ snd.appTop) :=
    hpo.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of K)) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  let : Algebra k Γ(U, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra Γ(U, ⊤) Γ(P, ⊤) := fst.appTop.hom.toAlgebra
  let : Algebra K Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ snd.appTop).hom.toAlgebra
  let : Algebra k Γ(P, ⊤) := (CommRingCat.ofHom (algebraMap k K) ≫
    (Scheme.ΓSpecIso (.of K)).inv ≫ snd.appTop).hom.toAlgebra
  have : IsScalarTower k K Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k Γ(U, ⊤) Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom hpo'.w).symm
  have : Algebra.IsPushout k Γ(U, ⊤) K Γ(P, ⊤) := CommRingCat.isPushout_iff_isPushout.mp hpo'
  exact exists_algebraMap_eq_of_isPushout (A := K) (P := Γ(P, ⊤)) hr

/-! ### Pullback of global functions along a change of base scheme -/

section ChangeOfBase


variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  (g : B.obj hS ⟶ B.obj hS') (X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)

/-- `CategoryTheory.OverShriek.restrictYonedaEquiv` is natural in the representing object. -/
theorem restrictYonedaEquiv_yoneda_map_comp {A A' : Over (B.obj hS)} (j : A' ⟶ A)
    (t : yoneda.obj A ⟶ (OverShriek.relocalizeRestrict g).obj X) :
    OverShriek.restrictYonedaEquiv g A' X (yoneda.map j ≫ t) =
      yoneda.map ((Over.map g).map j) ≫ OverShriek.restrictYonedaEquiv g A X t := by
  apply yonedaEquiv.injective
  simp only [OverShriek.restrictYonedaEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have := yonedaEquiv_naturality t j
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at this
  exact this.symm

/-- A scheme chart of the base change `X_S` of `X` along `g : S ⟶ S'` is a scheme chart of `X`
on the same scheme, viewed over `S'`. -/
noncomputable def chartChangeOfBase :
    CostructuredArrow yoneda ((OverShriek.relocalizeRestrict g).obj X) ⥤
      CostructuredArrow yoneda X where
  obj j := CostructuredArrow.mk (OverShriek.restrictYonedaEquiv g j.left X j.hom)
  map {j j'} h := CostructuredArrow.homMk ((Over.map g).map h.left) (by
    change _ ≫ OverShriek.restrictYonedaEquiv g j'.left X j'.hom =
      OverShriek.restrictYonedaEquiv g j.left X j.hom
    rw [← restrictYonedaEquiv_yoneda_map_comp, CostructuredArrow.w])
  map_id j := CostructuredArrow.hom_ext _ _ (by simp)
  map_comp f f' := CostructuredArrow.hom_ext _ _ (by simp)

/-- Pullback of all-chart families of functions along the change of base `g`: precomposition with
`AlgebraicGeometry.Space.chartChangeOfBase`, which does not change the scheme of a chart. -/
noncomputable def chartFunctionsChangeOfBase :
    chartFunctions B S' hS' X →+*
      chartFunctions B S hS ((OverShriek.relocalizeRestrict g).obj X) where
  toFun s := ⟨fun j => s.val (op ((chartChangeOfBase g X).obj j.unop)),
    fun {_ _} h => s.property ((chartChangeOfBase g X).map h.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (hX : IsAlgebraicSpace B S' hS' X)
  (hXS : IsAlgebraicSpace B S hS ((OverShriek.relocalizeRestrict g).obj X))

/-- **Pullback of global functions along the base change `X_S ⟶ X`** of an algebraic space along a
morphism of base schemes `g : S ⟶ S'`: a function is extended to all scheme charts of `X`, and
read on the charts of `X_S`, which are scheme charts of `X` on the same schemes. -/
noncomputable def globalFunctionsChangeOfBase :
    globalFunctions B S' hS' X →+*
      globalFunctions B S hS ((OverShriek.relocalizeRestrict g).obj X) :=
  (chartFunctionsToSmall B S hS _).comp ((chartFunctionsChangeOfBase g X).comp
    (globalFunctionsChartEquiv B S' hS' ⟨X, hX⟩).val.toRingHom)

/-- The pullback of a global function to the base change, read on a scheme chart `p` of the base
change, is the function read on `p` viewed as a chart of `X`. -/
theorem globalFunctionsToChart_globalFunctionsChangeOfBase {T : BigFppfOver B S hS}
    (p : yoneda.obj T ⟶ (OverShriek.relocalizeRestrict g).obj X) (s : globalFunctions B S' hS' X) :
    globalFunctionsToChart B S hS ⟨_, hXS⟩ p (globalFunctionsChangeOfBase g X hX s) =
      globalFunctionsToChart B S' hS' ⟨X, hX⟩ (OverShriek.restrictYonedaEquiv g T X p) s := by
  have h : (globalFunctionsChartEquiv B S hS ⟨_, hXS⟩).val (globalFunctionsChangeOfBase g X hX s) =
      chartFunctionsChangeOfBase g X ((globalFunctionsChartEquiv B S' hS' ⟨X, hX⟩).val s) := by
    apply chartFunctionsToSmall_injective B S hS _ hXS
    rw [(globalFunctionsChartEquiv B S hS ⟨_, hXS⟩).property]
    rfl
  change ((globalFunctionsChartEquiv B S hS ⟨_, hXS⟩).val _).val _ = _
  rw [h]
  rfl

end ChangeOfBase

section ChartMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Pullback of global functions to a scheme chart is compatible with morphisms of charts. -/
theorem globalFunctionsToChart_yoneda_map_comp {T T' : BigFppfOver B S hS} (q : T' ⟶ T)
    (p : yoneda.obj T ⟶ F) (s : globalFunctions B S hS F) :
    globalFunctionsToChart B S hS ⟨F, hF⟩ (yoneda.map q ≫ p) s =
      ((BigFppfOver.toScheme B S hS).map q).appTop (globalFunctionsToChart B S hS ⟨F, hF⟩ p s) :=
  (((globalFunctionsChartEquiv B S hS ⟨F, hF⟩).val s).property
    (CostructuredArrow.homMk q rfl : CostructuredArrow.mk (yoneda.map q ≫ p) ⟶
      CostructuredArrow.mk p).op).symm

/-- On an étale chart, pullback of global functions is the value of the function there. -/
theorem globalFunctionsToChart_etale (U : SmallEtale B S hS F) (s : globalFunctions B S hS F) :
    globalFunctionsToChart B S hS ⟨F, hF⟩ U.obj.hom s = s.val (op U) :=
  globalFunctionsChartEquiv_val_etale B S hS ⟨F, hF⟩ s U

end ChartMap

/-! ### Descent of constants along a field extension -/

section FieldDescent

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K)))

/-- The chart of a base change obtained by base changing a chart `c : W ⟶ X`, viewed as a chart
of `X`, factors through `c` along the projection `W ×_k K ⟶ W`. -/
theorem restrictYonedaEquiv_restrictYonedaIso {S S' : Scheme.{u}} {hS : B.Contains S}
    {hS' : B.Contains S'} (g : B.obj hS ⟶ B.obj hS') {Y : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (W : BigFppfOver B S' hS') (c : yoneda.obj W ⟶ Y) :
    OverShriek.restrictYonedaEquiv g ((Over.pullback g).obj W) Y
        ((OverShriek.restrictYonedaIso g W).hom ≫ (OverShriek.relocalizeRestrict g).map c) =
      yoneda.map (Over.homMk (pullback.fst W.hom g) (by simp [pullback.condition]) :
        (Over.map g).obj ((Over.pullback g).obj W) ⟶ W) ≫ c := by
  apply yonedaEquiv.injective
  simp only [OverShriek.restrictYonedaEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  change c.app _ ((OverShriek.restrictYonedaIso g W).hom.app _ (𝟙 _)) = c.app _ _
  congr 1

include hX in
/-- **Constants descend along a field extension.** Let `X` be a quasi-compact algebraic space
over a field `k` and `K/k` a field extension. A global function of `X` whose pullback to `X_K` is
a constant of `K` is a constant of `k`. Read on an affine surjective étale chart `W` of `X` and on
its base change `W_K = W ×_k K`, this is the statement that an element `a` of `A = Γ(W)` with
`a ⊗ 1 ∈ 1 ⊗ K` inside `A ⊗_k K` lies in `k`. -/
theorem exists_algebraMap_eq_of_globalFunctionsChangeOfBase
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (hf : IsQuasiCompact B (Spec (.of k)) hk f)
    (hXK : IsAlgebraicSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK))
    (s : globalFunctions B (Spec (.of k)) hk X) (a : K)
    (hs : globalFunctionsChangeOfBase (specMapOfExtension B k hk K hK) X hX s =
      algebraMap K (globalFunctions B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)) a) :
    ∃ c : k, algebraMap k (globalFunctions B (Spec (.of k)) hk X) c = s := by
  set g := specMapOfExtension B k hk K hK with hg
  obtain ⟨W, c, hWaff, hcs, hce⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec (.of k)) hk hX f hf
  let V : SmallEtale B (Spec (.of k)) hk X :=
    ⟨CostructuredArrow.mk c, presheaf_etale_of_isEtale B (Spec (.of k)) hk hce⟩
  have hinj := injective_globalFunctions_val_of_isSurjective B (Spec (.of k)) hk X hX V
    (isSurjective_of_presheafSurjective B (Spec (.of k)) hk c hcs)
  let q : yoneda.obj ((Over.pullback g).obj W) ⟶ fieldBaseChange B k hk X K hK :=
    (OverShriek.restrictYonedaIso g W).hom ≫ (OverShriek.relocalizeRestrict g).map c
  have h1 := congrArg (globalFunctionsToChart B (Spec (.of K)) hK ⟨_, hXK⟩ q) hs
  rw [globalFunctionsToChart_globalFunctionsChangeOfBase g X hX hXK q s,
    globalFunctionsToChart_algebraMap K B hK _ hXK q a,
    restrictYonedaEquiv_restrictYonedaIso B g W c,
    globalFunctionsToChart_yoneda_map_comp B (Spec (.of k)) hk X hX _ c s] at h1
  have hV : globalFunctionsToChart B (Spec (.of k)) hk ⟨X, hX⟩ c s = s.val (op V) :=
    globalFunctionsToChart_etale B (Spec (.of k)) hk X hX V s
  rw [hV] at h1
  have hpb : IsPullback (B.inclusion.map (pullback.fst W.hom g))
      (B.inclusion.map (pullback.snd W.hom g)) (B.inclusion.map W.hom) (B.inclusion.map g) :=
    (IsPullback.of_hasPullback W.hom g).map B.inclusion
  have : IsAffine (B.inclusion.obj W.left) := hWaff
  obtain ⟨c₀, hc₀⟩ := exists_eq_of_isPullback_spec (k := k) (K := K) hpb (s.val (op V)) a h1
  exact ⟨c₀, hinj (hc₀.trans rfl)⟩

end FieldDescent

/-! ### Over an algebraically closed field -/

section AlgClosed

variable (B : BigFppfSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of K)) hK X)

/-- A morphism of the site whose Yoneda image is a proper morphism of algebraic spaces is a
proper morphism of schemes: read properness on the base change along the identity. -/
theorem isProper_of_isProper_yoneda_map {S : Scheme.{u}} {hS : B.Contains S}
    {U V : BigFppfOver B S hS} (f : U ⟶ V) (hf : IsProper B S hS (yoneda.map f)) :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map f) := by
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).mp
    ((presheaf_isProper_iff B S hS (yoneda.map f)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (Functor.relativelyRepresentable.map yoneda f)).mp hf)

include hX in
/-- The ring of global functions of a proper algebraic space over a field is finite
dimensional once the space is reduced: by Chow's lemma (Stacks 089J) it receives a proper
surjection from a scheme proper over the field, whose ring of global functions is finite
dimensional (Stacks 0BUG (1)), and pullback along a surjection is injective on a reduced
space. -/
theorem moduleFinite_globalFunctions_of_isProper_of_isReduced
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)))) (hf : IsProper B (Spec (.of K)) hK f)
    (hred : HasEtaleLocalProperty B (Spec (.of K)) hK X
      (fun Y : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Y)) :
    Module.Finite K (globalFunctions B (Spec (.of K)) hK X) := by
  obtain ⟨X', p, hpp, hps, -⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B (CommRingCat.of K) hK X hX f hf.1 hf.2.1
  let φ : X' ⟶ Over.mk (𝟙 (B.obj hK)) := Over.homMk X'.hom (by simp)
  have hcomp : p ≫ f = yoneda.map φ := (isTerminal_yoneda_obj_base B _ hK).hom_ext _ _
  have hφ : IsProper B (Spec (.of K)) hK (yoneda.map φ) :=
    hcomp ▸ isProper_comp' B _ hK p f hX (isAlgebraicSpace_yoneda B _ hK _) hpp hf
  have hφs := isProper_of_isProper_yoneda_map B φ hφ
  let : Algebra K Γ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj X', ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).map φ).appTop).hom.toAlgebra
  have hfin : Module.Finite K Γ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj X', ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper K
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).map φ)
  let ψ : globalFunctions B (Spec (.of K)) hK X →ₐ[K]
      Γ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj X', ⊤) :=
    { globalFunctionsToChart B (Spec (.of K)) hK ⟨X, hX⟩ p with
      commutes' := globalFunctionsToChart_algebraMap K B hK X hX p }
  exact Module.Finite.of_injective ψ.toLinearMap
    (injective_globalFunctionsToChart_of_isSurjective B (Spec (.of K)) hK ⟨X, hX⟩ hred p hps)

include hX in
/-- **The global functions of a proper, reduced, connected algebraic space over an
algebraically closed field are the constants.** The ring is finite dimensional
(`moduleFinite_globalFunctions_of_isProper_of_isReduced`), reduced (Stacks 0BGS) and has only
the trivial idempotents because the space is connected, so it is a finite field extension of
`K`, hence `K` itself. -/
theorem bijective_algebraMap_globalFunctions_of_isAlgClosed [IsAlgClosed K]
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)))) (hf : IsProper B (Spec (.of K)) hK f)
    (hred : HasEtaleLocalProperty B (Spec (.of K)) hK X
      (fun Y : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Y))
    (hconn : ConnectedPoints B (Spec (.of K)) hK X) :
    Function.Bijective (algebraMap K (globalFunctions B (Spec (.of K)) hK X)) := by
  set R := globalFunctions B (Spec (.of K)) hK X
  have hfin : Module.Finite K R :=
    moduleFinite_globalFunctions_of_isProper_of_isReduced B K hK X hX f hf hred
  have : Nontrivial R := nontrivial_globalFunctions_of_connectedPoints B _ hK X hX hconn
  have : _root_.IsReduced R := isReduced_globalFunctions B _ hK X hX hred
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 :=
    isIdempotentElem_eq_zero_or_one_of_connectedPoints B _ hK X hX hconn
  have : IsLocalRing R := IsLocalRing.of_isArtinianRing_of_forall_isIdempotentElem R hidem
  have : IsDomain R := (IsArtinianRing.isField_of_isReduced_of_isLocalRing R).isDomain
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end AlgClosed

/-! ### Over an arbitrary field -/

section Field

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)

include hX in
/-- **The global functions of a proper algebraic space over a field `k` which is geometrically
reduced and geometrically connected are the constants**, `k = H⁰(X, 𝒪_X)`. Geometric reducedness
and connectedness enter only through the base changes `X_K` to algebraically closed fields `K`
(whose spectrum lies in the site), where they say that `X_K` is reduced with connected space of
points.

Over an algebraic closure `K` of `k` the space `X_K` is proper, reduced and connected, so its
global functions are `K` by Chow's lemma
(`bijective_algebraMap_globalFunctions_of_isAlgClosed`); and a global function of `X` which
becomes a constant of `K` on `X_K` is a constant of `k`, read on an affine étale chart of `X`
(`exists_algebraMap_eq_of_globalFunctionsChangeOfBase`). No finiteness theorem for the
cohomology of `X` itself is used. -/
theorem bijective_algebraMap_globalFunctions_of_isProper
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (hf : IsProper B (Spec (.of k)) hk f)
    (hred : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
      (hK : B.Contains (Spec (.of K))),
      HasEtaleLocalProperty B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hconn : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
      (hK : B.Contains (Spec (.of K))),
      ConnectedPoints B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)) :
    Function.Bijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X)) := by
  set K := AlgebraicClosure k
  have hK : B.Contains (Spec (.of K)) := B.contains_spec_algebraicClosure k hk
  set g := specMapOfExtension B k hk K hK with hg
  have hXK : IsAlgebraicSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK) :=
    isAlgebraicSpace_fieldBaseChange B k hk X hX K hK
  have hfK : IsProper B (Spec (.of K)) hK
      ((isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from (fieldBaseChange B k hk X K hK)) :=
    isProper_toBase_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk g X hX f hf
  have hbij := bijective_algebraMap_globalFunctions_of_isAlgClosed B K hK _ hXK _ hfK
    (hred K hK) (hconn K hK)
  have : Nontrivial (globalFunctions B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)) :=
    nontrivial_globalFunctions_of_connectedPoints B _ hK _ hXK (hconn K hK)
  have : Nontrivial (globalFunctions B (Spec (.of k)) hk X) :=
    (globalFunctionsChangeOfBase g X hX).domain_nontrivial
  refine ⟨(algebraMap k _).injective, fun s => ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 (globalFunctionsChangeOfBase g X hX s)
  exact exists_algebraMap_eq_of_globalFunctionsChangeOfBase B k hk X hX K hK f hf.2.1.2 hXK s a
    ha.symm

/-- **`k = H⁰(X, 𝒪_X)` for a proper, geometrically reduced (Stacks 0DMQ) and geometrically
connected (Stacks 0A0Z) algebraic space over a field `k`.** This is
`bijective_algebraMap_globalFunctions_of_isProper`, the base change `X_K` to an algebraically
closed field being reduced by Stacks 0E04 and connected by definition. -/
theorem bijective_algebraMap_globalFunctions_of_isGeometricallyReduced
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (hf : IsProper B (Spec (.of k)) hk f)
    (hgr : IsGeometricallyReduced k B hk X hX) (hgc : IsGeometricallyConnected B k hk X) :
    Function.Bijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X)) := by
  refine bijective_algebraMap_globalFunctions_of_isProper B k hk X hX f hf
    (fun K _ _ _ hK => ?_) (fun K _ _ _ hK => ?_)
  · exact hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced K B hK _
      (isAlgebraicSpace_fieldBaseChange B k hk X hX K hK)
      ((isGeometricallyReduced_fieldBaseChange_iff B k hk X K hK hX).mp hgr)
  · have h := hgc K hK
    rw [← specMapOfExtension_eq_fieldExtensionMap B k hk K hK] at h
    exact h

end Field

end AlgebraicGeometry.Space

end
