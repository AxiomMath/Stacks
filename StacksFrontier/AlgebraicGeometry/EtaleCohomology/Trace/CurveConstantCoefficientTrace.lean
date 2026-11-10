module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyDegreeZeroSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInput
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurveMapDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The traces of `φ^*` on the étale cohomology `H^i(C, ℤ/ℓ^m)` of a curve

Let `C` be a smooth proper curve over an algebraically closed field `k`, let `φ : C ⟶ C` be an
endomorphism over `k` (constant or not), and let `ℓ` be a prime invertible in `k`. The étale
cohomology `H^i(C, ℤ/ℓ^m) = Sheaf.H (ℤ/ℓ^m)_C i` of the constant sheaf is a `ℤ/ℓ^m`-module, free of
finite rank, and `φ^*` acts on it by restriction along `φ` followed by the canonical identification
`φ^{-1}(ℤ/ℓ^m)_C ≅ (ℤ/ℓ^m)_C` of constant sheaves. This file computes its traces degree by degree,
as in the proof of [Stacks, Tag 03U3]:

* `H⁰(C, ℤ/n) = ℤ/n`, spanned by the constant classes, which every pullback fixes, so the trace
  is `1`;
* a primitive `n`-th root of unity `ζ ∈ k` identifies `H^i(C, ℤ/n)` with `H^i(C, μ_n)` through
  `m ↦ ζ^m`, compatibly with pullback along any morphism over `k`
  (`sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo`); the Kummer sequence identifies
  `H¹(C, μ_{ℓ^m})` with `Pic(C)[ℓ^m]`, naturally, so the trace in degree one is
  `Tr(φ^* | Pic(C)[ℓ^m])`;
* `H²(C, μ_n) = Pic(C)/n ≅ ℤ/n` through the degree, with `φ^*` acting as multiplication by
  `deg φ`, so the trace in degree two is `deg φ`.

## Main definitions

* `Stacks.EtaleCohomology.etaleConstantCohomologyPullback` — the pullback
  `π^* : H^q(Y, M) ⟶ H^q(X, M)` along a morphism of schemes `π : X ⟶ Y`.
* `Stacks.EtaleCohomology.moduleZModSheafHEtaleConstantSheaf` — the `ℤ/n`-module structure of
  `H^q(X, ℤ/n)`.
* `Stacks.EtaleCohomology.etaleConstantClass` — the constant classes `M → H⁰(X, M)`.

## Main results

* `Stacks.EtaleCohomology.trace_etaleConstantCohomologyPullback_zero`,
  `Stacks.EtaleCohomology.trace_etaleConstantCohomologyPullback_one`,
  `Stacks.EtaleCohomology.trace_etaleConstantCohomologyPullback_two` — the three traces.
* `Stacks.EtaleCohomology.module_free_finite_sheafH_etaleConstantSheaf` — each `H^i(C, ℤ/ℓ^m)` is
  free of finite rank over `ℤ/ℓ^m`.
* `Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback` and
  `Stacks.EtaleCohomology.sum_trace_etaleConstantCohomologyPullback_eq_toZModPow` — the
  alternating sum is `1 - Tr(φ^* | Pic(C)[ℓ^m]) + deg φ`, that is `1 - Tr_J(φ^*) + deg φ` modulo
  `ℓ^m`, with `Tr_J(φ^*)` the trace of `φ^*` on the `ℓ`-adic Tate module of the jacobian.

None of the declarations here is registered: they are the degreewise computations in the proof of
[Stacks, Tag 03U3], which is registered once combined with Weil's formula [Stacks, Tag 03U1].

## References

* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

section RootsOfUnity

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) (π : X ⟶ Y) (hπ : π ≫ gY = gX) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

include hπ in
/-- The image of `ζ` on an étale `Y`-scheme `V`, pulled back along the projection
`V ×_Y X ⟶ V`, is the image of `ζ` on `V ×_Y X`, for `π : X ⟶ Y` a morphism over `k`. -/
theorem map_rootOn_pullbackFst_of_comp (V : Y.Etale) :
    Units.map (pullback.fst V.hom π).appTop.hom.toMonoidHom (Stacks.Kummer.rootOn gY hζ hn V) =
      Stacks.Kummer.rootOn gX hζ hn ((smallEtaleBaseChange π).obj V) := by
  have hs : (pullback.fst V.hom π).appTop.hom.comp (Stacks.Kummer.structMap gY V) =
      Stacks.Kummer.structMap gX ((smallEtaleBaseChange π).obj V) := by
    rw [Stacks.Kummer.structMap, Stacks.Kummer.structMap, ← CommRingCat.hom_comp]
    congr 1
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop]
    change _ ≫ gY.appTop ≫ (pullback.fst V.hom π ≫ V.hom).appTop =
      _ ≫ gX.appTop ≫ (pullback.snd V.hom π).appTop
    rw [pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc gY.appTop,
      ← Scheme.Hom.comp_appTop, hπ]
  rw [Stacks.Kummer.rootOn, Stacks.Kummer.rootOn, ← hs]
  rfl

include hπ in
/-- **The constant-sheaf comparison is the comparison on `μ_n`.** For a morphism `π : X ⟶ Y` of
schemes over a field `k` containing a primitive `n`-th root of unity `ζ`, the canonical
comparison `π^{-1} ℤ/n ≅ ℤ/n` of constant sheaves corresponds, under `m ↦ ζ^m`, to the comparison
`π^{-1} μ_n ⟶ μ_n`. -/
theorem inverseImage_rootsOfUnityConstantHom_comp_comparison :
    (etaleAbelianInverseImage.{u, 0} π).map (Stacks.Kummer.rootsOfUnityConstantHom gY hζ hn) ≫
        Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} π n =
      (etaleAbelianInverseImageConstantIso.{u, 0} π).hom.app _ ≫
        Stacks.Kummer.rootsOfUnityConstantHom gX hζ hn := by
  rw [← cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} X n), Category.assoc, Category.assoc,
    Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, ← Functor.map_comp_assoc,
    Stacks.Kummer.rootsOfUnityConstantHom_comp_ι, Stacks.Kummer.rootsOfUnityConstantHom_comp_ι]
  apply (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal Y)).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} π)).homEquiv _ _).injective
  rw [constantSheaf_comp_homEquiv_apply.{u, 0}, constantSheaf_comp_homEquiv_apply.{u, 0},
    Adjunction.homEquiv_naturality_left,
    Stacks.Kummer.multiplicativeInverseImageComparison_transpose,
    Adjunction.homEquiv_naturality_right]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ← Category.assoc,
    ← Category.assoc, constantSheafSection_comp_homEquiv_constantIso.{u, 0} π]
  change (toSheafify Y.smallEtaleTopology _ ≫ (Stacks.Kummer.rootSheafHom gY hζ hn).hom).app _ ≫
      _ = (toSheafify X.smallEtaleTopology _ ≫ (Stacks.Kummer.rootSheafHom gX hζ hn).hom).app _
  rw [Stacks.Kummer.toSheafify_rootSheafHom, Stacks.Kummer.toSheafify_rootSheafHom]
  ext ⟨m⟩
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
  change (multiplicativeDirectImageComparison.{u, 0} π).hom.app (op (etaleSiteTerminal Y))
      (Stacks.Kummer.rootHom gY hζ hn _ (z : ZMod n)) =
    Stacks.Kummer.rootHom gX hζ hn _ (z : ZMod n)
  rw [Stacks.Kummer.rootHom_intCast, Stacks.Kummer.rootHom_intCast, map_zsmul,
    multiplicativeDirectImageComparison_app_ofUnit, map_rootOn_pullbackFst_of_comp gX gY π hπ hζ hn]
  rfl

end RootsOfUnity

section Cohomology

open Abelian

variable {X : Scheme.{u}} [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- `n` kills the étale cohomology `H^q(X, ℤ/n)` of the constant sheaf `ℤ/n`. -/
theorem nsmul_sheafH_etaleConstantSheaf_eq_zero (n q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) q) : n • x = 0 := by
  have h1 : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1, 0} (ZMod n))) = 0 := by
    ext ⟨m⟩
    simp
  have h2 : n • 𝟙 (etaleConstantSheaf.{u, 0} X (ZMod n)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h1, Functor.map_zero]
  have h3 : n • Ext.mk₀ (𝟙 (etaleConstantSheaf.{u, 0} X (ZMod n))) = 0 := by
    rw [← Ext.addEquiv₀_symm_apply, ← map_nsmul, h2, map_zero]
  rw [← Ext.comp_mk₀_id x]
  change n • x.precomp _ (add_zero q) (Ext.mk₀ (𝟙 _)) = 0
  rw [← map_nsmul, h3, map_zero]

/-- The étale cohomology `H^q(X, ℤ/n)` of the constant sheaf `ℤ/n` is a `ℤ/n`-module: it is
killed by `n`. -/
instance moduleZModSheafHEtaleConstantSheaf (n q : ℕ) :
    Module (ZMod n) (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) q) :=
  AddCommGroup.zmodModule (nsmul_sheafH_etaleConstantSheaf_eq_zero n q)

end Cohomology

section Pullback

variable {X Y : Scheme.{u}} [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The pullback `π^* : H^q(Y, M) ⟶ H^q(X, M)` on étale cohomology with constant coefficients**
along a morphism of schemes `π : X ⟶ Y`: restriction along `π` followed by the canonical
identification `π^{-1} M_Y ≅ M_X` of constant sheaves. -/
def etaleConstantCohomologyPullback (π : X ⟶ Y) (M : Type) [AddCommGroup M] (q : ℕ) :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y M) q →+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X M) q :=
  etaleCohomologyMapTo π ((etaleAbelianInverseImageConstantIso.{u, 0} π).hom.app _) q

end Pullback

section Bridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) (π : X ⟶ Y) (hπ : π ≫ gY = gX) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

include hπ in
/-- **Pullback on `H^q(-, ℤ/n)` is pullback on `H^q(-, μ_n)`.** For a morphism `π : X ⟶ Y` over a
field `k` with a primitive `n`-th root of unity `ζ`, the map on cohomology induced by
`m ↦ ζ^m` carries restriction along `π` followed by the constant-sheaf comparison to the
pullback `π^* : H^q(Y, μ_n) ⟶ H^q(X, μ_n)`. -/
theorem sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo (q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod n)) q) :
    Sheaf.H.map (Stacks.Kummer.rootsOfUnityConstantHom gX hζ hn) q
        (etaleConstantCohomologyPullback π (ZMod n) q x) =
      rootsOfUnityPullbackMap.{u, 0, u + 1} π n q
        (Sheaf.H.map (Stacks.Kummer.rootsOfUnityConstantHom gY hζ hn) q x) := by
  rw [rootsOfUnityPullbackMap_apply, Stacks.Kummer.etaleCohomologyRestrictionMap_sheafHMap]
  change Sheaf.H.map _ q (Sheaf.H.map _ q (etaleCohomologyRestrictionMap.{u, 0, u + 1} π _ q x)) = _
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    inverseImage_rootsOfUnityConstantHom_comp_comparison gX gY π hπ hζ hn]

end Bridge

section DegreeZero

/-- A section `h` of the projection `pullback (𝟙 Y) π ⟶ X` composes with the other projection to
`π`. -/
theorem comp_pullbackFst_id_eq_of_comp_pullbackSnd {X Y : Scheme.{u}} (π : X ⟶ Y)
    (h : X ⟶ pullback (𝟙 Y) π) (h1 : h ≫ pullback.snd (𝟙 Y) π = 𝟙 X) :
    h ≫ pullback.fst (𝟙 Y) π = π := by
  have hc : pullback.fst (𝟙 Y) π = pullback.snd (𝟙 Y) π ≫ π :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [hc, ← Category.assoc, h1, Category.id_comp]

variable {X Y : Scheme.{u}} (π : X ⟶ Y)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Pullback on `H⁰(-, 𝐆_m)` is pullback of invertible global functions.** Through
`CategoryTheory.Sheaf.H.equiv₀` at the terminal objects, restriction along `π : X ⟶ Y` followed by
the comparison `π^{-1} 𝐆_m ⟶ 𝐆_m` sends the class of an invertible global function `a` on `Y` to
the class of `π^♯ a`. -/
theorem equiv₀_etaleCohomologyMapTo_multiplicativeInverseImageComparison
    (x : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} Y) 0) (a : (Γ(Y, ⊤))ˣ)
    (ha : Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal Y) x =
      Stacks.Kummer.ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 Y)) a) :
    Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal X)
        (etaleCohomologyMapTo π (Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} π) 0 x) =
      Stacks.Kummer.ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 X))
        (Units.map π.appTop.hom.toMonoidHom a) := by
  rw [equiv₀_etaleCohomologyMapTo, ha, etaleSectionsRestriction]
  set h := (isTerminalSmallEtaleBaseChangeEtaleMkId π).from (Scheme.Etale.mk (𝟙 X))
  rw [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply _
    ((Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} π).hom.app _),
    (Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} π).hom.naturality h.op,
    ConcreteCategory.comp_apply]
  change (Stacks.Kummer.multiplicativeSheaf.{u, 0} X).obj.map h.op
      ((Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} π).hom.app
        (op ((smallEtaleBaseChange π).obj (Scheme.Etale.mk (𝟙 Y))))
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
          (Stacks.Kummer.multiplicativeSheaf.{u, 0} Y)).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
          (Stacks.Kummer.ofUnit a))) = _
  rw [Stacks.Kummer.multiplicativeInverseImageComparison_app_ofUnit.{u, 0} π
    (Scheme.Etale.mk (𝟙 Y)) a]
  refine (Stacks.Kummer.map_ofUnit.{u, 0} h _).trans ?_
  congr 1
  apply Units.ext
  have hh : h.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π = π :=
    comp_pullbackFst_id_eq_of_comp_pullbackSnd π h.left (MorphismProperty.Over.w h)
  change (h.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π).appTop.hom (a : Γ(Y, ⊤)) =
    π.appTop.hom (a : Γ(Y, ⊤))
  rw [hh]
  rfl

end DegreeZero

section Trace

/-- **Traces of conjugate endomorphisms agree.** If an additive isomorphism `e : M ≃+ N` of
`ℤ/n`-modules carries `f` to `g`, the traces of `f` and `g` over `ℤ/n` agree. -/
theorem trace_toZModLinearMap_eq_of_addEquiv {n : ℕ} {M N : Type*} [AddCommGroup M]
    [Module (ZMod n) M] [AddCommGroup N] [Module (ZMod n) N] (e : M ≃+ N) (f : M →+ M)
    (g : N →+ N) (h : ∀ x, e (f x) = g (e x)) :
    LinearMap.trace (ZMod n) M (f.toZModLinearMap n) =
      LinearMap.trace (ZMod n) N (g.toZModLinearMap n) := by
  let E : M ≃ₗ[ZMod n] N := e.toLinearEquiv (ZMod.map_smul e)
  have hE : g.toZModLinearMap n = E.conj (f.toZModLinearMap n) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change g (e y) = e (f (E.symm (e y)))
    rw [show E.symm (e y) = y from E.symm_apply_apply y, h]
  rw [hE, LinearMap.trace_conj']

/-- The trace over `ℤ/n` of multiplication by an integer `c` on `ℤ/n` is `c`. -/
theorem trace_zsmul_id_zmod (n : ℕ) (c : ℤ) :
    LinearMap.trace (ZMod n) (ZMod n) ((c • AddMonoidHom.id (ZMod n)).toZModLinearMap n) = c := by
  rcases subsingleton_or_nontrivial (ZMod n) with h | h
  · exact Subsingleton.elim _ _
  · have hc : (c • AddMonoidHom.id (ZMod n)).toZModLinearMap n = (c : ZMod n) • LinearMap.id := by
      ext
      simp
    rw [hc, map_smul, LinearMap.trace_id, Module.finrank_self]
    simp

/-- A `ℤ/n`-module additively isomorphic to a free `ℤ/n`-module of finite rank is free of finite
rank. -/
theorem module_free_finite_of_addEquiv {n : ℕ} {M N : Type*} [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup N] [Module (ZMod n) N] [Module.Free (ZMod n) N] [Module.Finite (ZMod n) N]
    (e : M ≃+ N) : Module.Free (ZMod n) M ∧ Module.Finite (ZMod n) M := by
  let E : N ≃ₗ[ZMod n] M := (e.toLinearEquiv (ZMod.map_smul e)).symm
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E⟩

end Trace

section DegreeZeroRoots

open Stacks.Kummer

variable (X : Scheme.{u}) [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- `H⁰(X, μ_n) ⟶ H⁰(X, 𝐆_m)` is injective. -/
theorem injective_sheafH_map_rootsOfUnityι_zero (n : ℕ) :
    Function.Injective (Sheaf.H.map.{u + 1} (rootsOfUnityι.{u, 0} X n) 0) := by
  intro a b hab
  apply (Abelian.Ext.addEquiv₀).injective
  have h := congrArg Abelian.Ext.addEquiv₀ hab
  rw [Sheaf.H.addEquiv₀_map, Sheaf.H.addEquiv₀_map] at h
  exact (cancel_mono _).1 h

/-- `H⁰(X, 𝐆_m) ≃+ Γ(X, 𝒪_X)ˣ`, written additively. -/
def h0MultiplicativeAddEquiv :
    Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
  (Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal X)).trans AddEquiv.ulift

/-- The inverse of `h0MultiplicativeAddEquiv` sends a unit `a` of `Γ(X, 𝒪_X)` to the class whose
global section is `a`. -/
theorem h0MultiplicativeAddEquiv_symm_apply (a : (Γ(X, ⊤))ˣ) :
    Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal X)
        ((h0MultiplicativeAddEquiv X).symm (Additive.ofMul a)) =
      ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 X)) a :=
  (Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal X)).apply_symm_apply _

/-- The class in `H⁰(X, M)` of the map of constant sheaves `ℤ_X ⟶ M_X` sending `1` to `m`. -/
def etaleConstantClass (M : Type) [AddCommGroup M] :
    M →+ Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X M) 0 where
  toFun m := Ext.mk₀ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := M)).symm.toAddMonoidHom.comp
      ((zmultiplesHom M m).comp (AddEquiv.ulift.{0, u + 1} (α := ℤ)).toAddMonoidHom))))
  map_zero' := by
    rw [← Ext.mk₀_zero, ← Functor.map_zero]
    congr 2
    ext ⟨z⟩
    simp
  map_add' a b := by
    rw [← Ext.mk₀_add, ← Functor.map_add]
    congr 2
    ext ⟨z⟩
    simp [smul_add]

variable {X} in
/-- **Pullback fixes the constant classes**: for every morphism `π : X ⟶ Y`, `π^*` carries the
class in `H⁰(Y, M)` of the constant section `m` to the class in `H⁰(X, M)` of `m`. -/
theorem etaleConstantCohomologyPullback_etaleConstantClass {Y : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] (π : X ⟶ Y)
    (M : Type) [AddCommGroup M] (m : M) :
    etaleConstantCohomologyPullback π M 0 (etaleConstantClass Y M m) =
      etaleConstantClass X M m := by
  change ((Ext.mk₀ _).comp ((Ext.mk₀ _).mapExactFunctor (etaleAbelianInverseImage.{u, 0} π))
    (zero_add 0)).comp (Ext.mk₀ _) (add_zero 0) = Ext.mk₀ _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  congr 1
  have h := (etaleAbelianInverseImageConstantIso.{u, 0} π).hom.naturality
    (AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := M)).symm.toAddMonoidHom.comp
      ((zmultiplesHom M m).comp (AddEquiv.ulift.{0, u + 1} (α := ℤ)).toAddMonoidHom)))
  simp only [Functor.comp_map] at h
  rw [Category.assoc, h, Iso.app_inv]
  exact Iso.inv_hom_id_app_assoc (etaleAbelianInverseImageConstantIso.{u, 0} π) _ _

/-- `CategoryTheory.Sheaf.H.equiv₀` of the class of a map `θ : ℤ_X ⟶ F` is the value of `θ` on the
canonical section `1` over the terminal object. -/
theorem equiv₀_mk₀ {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (θ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    Sheaf.H.equiv₀ F (etaleMkIdIsTerminal X) (Ext.mk₀ θ) =
      ((constantSheafAdj _ _ (etaleMkIdIsTerminal X)).homEquiv _ _ θ) (ULift.up 1) := by
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Ext.addEquiv₀, AddEquiv.coe_mk,
    Adjunction.homAddEquiv_apply]
  have h : Ext.homEquiv₀ (Ext.mk₀ θ) = θ := Ext.homEquiv₀.apply_symm_apply θ
  rw [h]
  rfl

end DegreeZeroRoots

section DegreeZeroCount

open Stacks.Kummer

variable {k : Type u} [Field k] {X : Scheme.{u}} (gX : X ⟶ Spec (.of k)) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

include gX hζ hn in
/-- **The constant classes are distinct** on a nonempty scheme over a field with a primitive
`n`-th root of unity: under `m ↦ ζ^m` the class of `m` is the global function `ζ^m`. -/
theorem etaleConstantClass_injective [Nonempty X] :
    Function.Injective (etaleConstantClass X (ZMod n)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h1 := congrArg (fun y => Sheaf.H.equiv₀ _ (etaleMkIdIsTerminal X)
    (Sheaf.H.map (rootsOfUnityConstantHom gX hζ hn ≫ rootsOfUnityι.{u, 0} X n) 0 y)) hm
  simp only [map_zero] at h1
  change Sheaf.H.equiv₀ _ _ ((Ext.mk₀ _).comp (Ext.mk₀ _) (add_zero 0)) = 0 at h1
  rw [Ext.mk₀_comp_mk₀, equiv₀_mk₀, Adjunction.homEquiv_naturality_left,
    rootsOfUnityConstantHom_comp_ι,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq] at h1
  rw [ConcreteCategory.comp_apply] at h1
  change (toSheafify X.smallEtaleTopology _ ≫ (rootSheafHom gX hζ hn).hom).app _
    (ULift.up ((1 : ℤ) • m)) = 0 at h1
  rw [toSheafify_rootSheafHom] at h1
  change rootHom gX hζ hn (Scheme.Etale.mk (𝟙 X)) ((1 : ℤ) • m) = 0 at h1
  have : Nonempty (Scheme.Etale.mk (𝟙 X)).left := ‹Nonempty X›
  rwa [one_zsmul, rootHom_eq_zero_iff] at h1

/-- `ℤ/n ≅ μ_n` through `m ↦ ζ^m`, on étale cohomology. -/
def sheafHRootsOfUnityConstantAddEquiv (q : ℕ) :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) q ≃+
      Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) q :=
  { toFun := Sheaf.H.map (rootsOfUnityConstantIso gX hζ hn).hom q
    invFun := Sheaf.H.map (rootsOfUnityConstantIso gX hζ hn).inv q
    left_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
    right_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
    map_add' := map_add _ }

/-- `sheafHRootsOfUnityConstantAddEquiv` is the map on cohomology induced by
`rootsOfUnityConstantHom`. -/
theorem sheafHRootsOfUnityConstantAddEquiv_apply (q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) q) :
    sheafHRootsOfUnityConstantAddEquiv gX hζ hn q x =
      Sheaf.H.map (rootsOfUnityConstantHom gX hζ hn) q x :=
  rfl

/-- The global root of unity attached to a class of `H⁰(X, ℤ/n)`: through `m ↦ ζ^m`, the class
is an `n`-th root of unity in `Γ(X, 𝒪_X)`. -/
def h0EtaleConstantToRootsOfUnity :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) 0 → rootsOfUnity n (Γ(X, ⊤)) :=
  fun x => ⟨Additive.toMul (h0MultiplicativeAddEquiv X
      (Sheaf.H.map (rootsOfUnityι.{u, 0} X n) 0
        (sheafHRootsOfUnityConstantAddEquiv gX hζ hn 0 x))), by
    rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul (h0MultiplicativeAddEquiv X),
      ← sheafH_map_powMap.{u + 1, u, 0} X n 0, ← Sheaf.H.map_comp_apply,
      rootsOfUnityι_comp_powMap,
      Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero, map_zero]
    rfl⟩

/-- The map `h0EtaleConstantToRootsOfUnity` from `H⁰(X, ℤ/n)` to the `n`-th roots of unity in
`Γ(X, 𝒪_X)` is injective. -/
theorem h0EtaleConstantToRootsOfUnity_injective :
    Function.Injective (h0EtaleConstantToRootsOfUnity gX hζ hn) := by
  intro a b hab
  have h := congrArg (fun z : rootsOfUnity n (Γ(X, ⊤)) => Additive.ofMul (z : (Γ(X, ⊤))ˣ)) hab
  simp only [h0EtaleConstantToRootsOfUnity, ofMul_toMul] at h
  exact (sheafHRootsOfUnityConstantAddEquiv gX hζ hn 0).injective
    (injective_sheafH_map_rootsOfUnityι_zero X n ((h0MultiplicativeAddEquiv X).injective h))

include gX hζ hn in
/-- `H⁰(X, ℤ/n)` is finite, of order at most `n`, on an integral scheme over a field with a
primitive `n`-th root of unity. -/
theorem finite_sheafH_zero_etaleConstantSheaf [IsIntegral X] :
    Finite (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) 0) := by
  have : NeZero n := ⟨hn⟩
  exact Finite.of_injective _ (h0EtaleConstantToRootsOfUnity_injective gX hζ hn)

include gX hζ hn in
/-- `H⁰(X, ℤ/n)` has at most `n` elements on an integral scheme over a field with a primitive
`n`-th root of unity. -/
theorem natCard_sheafH_zero_etaleConstantSheaf_le [IsIntegral X] :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod n)) 0) ≤ n := by
  have : NeZero n := ⟨hn⟩
  exact (Nat.card_le_card_of_injective _ (h0EtaleConstantToRootsOfUnity_injective gX hζ hn)).trans
    (card_rootsOfUnity (Γ(X, ⊤)) n)

include gX hζ hn in
/-- **`H⁰(X, ℤ/n) = ℤ/n`** on an integral scheme over a field with a primitive `n`-th root of
unity: every class is a constant class. -/
theorem etaleConstantClass_bijective [IsIntegral X] :
    Function.Bijective (etaleConstantClass X (ZMod n)) := by
  have : NeZero n := ⟨hn⟩
  have := finite_sheafH_zero_etaleConstantSheaf gX hζ hn
  refine (etaleConstantClass_injective gX hζ hn).bijective_of_nat_card_le ?_
  rw [Nat.card_zmod]
  exact natCard_sheafH_zero_etaleConstantSheaf_le gX hζ hn

/-- The identification `ℤ/n ≅ μ_n` on cohomology is compatible with pullback along `φ`. -/
private theorem sheafHRootsOfUnityConstantAddEquiv_etaleConstantCohomologyPullback
    {C : Scheme.{u}} [HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (f : C ⟶ Spec (.of k)) (φ : C ⟶ C) (w : φ ≫ f = f) (q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) q) :
    sheafHRootsOfUnityConstantAddEquiv f hζ hn q (etaleConstantCohomologyPullback φ (ZMod n) q x) =
      rootsOfUnityPullbackMap.{u, 0, u + 1} φ n q
        (sheafHRootsOfUnityConstantAddEquiv f hζ hn q x) :=
  sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo f f φ w hζ hn q x

end DegreeZeroCount

section Curve

open Stacks.Kummer
open scoped CategoryTheory.MonObj

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  (φ : C ⟶ C) (w : φ ≫ f = f)

omit [IsAlgClosed k] in
/-- An algebraically closed field contains a primitive `n`-th root of unity whenever `n` is a unit
in it. -/
theorem exists_isPrimitiveRoot_of_isUnit [IsAlgClosed k] {n : ℕ} (hn : IsUnit (n : k)) :
    ∃ ζ : k, IsPrimitiveRoot ζ n := by
  have : NeZero (n : k) := ⟨hn.ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n

/-- The cast of `ℓ ^ m` is a unit in a ring in which `ℓ` is. -/
private theorem isUnit_natCast_pow {R : Type*} [Semiring R] (ℓ m : ℕ) (hℓ : IsUnit (ℓ : R)) :
    IsUnit (((ℓ ^ m : ℕ)) : R) := by
  rw [Nat.cast_pow]
  exact hℓ.pow m

include f in
/-- **The trace of `φ^*` on `H⁰(C, ℤ/n)` is `1`**: `H⁰(C, ℤ/n) = ℤ/n` is spanned by the constant
classes, which every pullback fixes. -/
theorem trace_etaleConstantCohomologyPullback_zero [IsIntegral C] {n : ℕ} (hn : IsUnit (n : k)) :
    LinearMap.trace (ZMod n) _ ((etaleConstantCohomologyPullback φ (ZMod n) 0).toZModLinearMap n) =
      1 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  let e := AddEquiv.ofBijective (etaleConstantClass C (ZMod n))
    (etaleConstantClass_bijective f hζ hn0)
  rw [trace_toZModLinearMap_eq_of_addEquiv e.symm _ ((1 : ℤ) • AddMonoidHom.id (ZMod n)) ?_,
    trace_zsmul_id_zmod, Int.cast_one]
  intro x
  obtain ⟨m, rfl⟩ := e.surjective x
  rw [one_zsmul, AddMonoidHom.id_apply]
  change e.symm (etaleConstantCohomologyPullback φ (ZMod n) 0 (etaleConstantClass C (ZMod n) m)) =
    e.symm (e m)
  rw [etaleConstantCohomologyPullback_etaleConstantClass]
  rfl

variable [IsCurve k f] [IsProper f]

include w in
/-- **The trace of `φ^*` on `H¹(C, ℤ/ℓ^m)` is the trace of `φ^*` on `Pic(C)[ℓ^m]`**: the choice of
a primitive `ℓ^m`-th root of unity identifies `H¹(C, ℤ/ℓ^m)` with `H¹(C, μ_{ℓ^m})`, and the Kummer
sequence with `H¹(C, μ_{ℓ^m}) = Pic(C)[ℓ^m]`, both compatibly with pullback along `φ`. -/
theorem trace_etaleConstantCohomologyPullback_one (ℓ m : ℕ) [NeZero ℓ]
    (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod (ℓ ^ m)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) 1).toZModLinearMap (ℓ ^ m)) =
      picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ m := by
  have hn := isUnit_natCast_pow ℓ m hℓ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  have hX := isUnit_natCast_globalSections C (ℓ ^ m) f hn
  have hsurj := surjective_sheafH_map_powMap_zero.{u + 1, u, 0} C (n := ℓ ^ m)
    (exists_pow_eq_globalUnit C (ℓ ^ m) f (Nat.pos_of_ne_zero hn0))
  let E := (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 1).trans
    ((h1RootsOfUnityAddEquivPicardTorsion.{u + 1, 0, u} C (ℓ ^ m) hn0 hX hsurj).trans
      (Stacks.AbelianGroup.torsionByNatCastPowEquiv _ ℓ m))
  rw [picardTorsionTrace]
  refine trace_toZModLinearMap_eq_of_addEquiv E _ _ fun x => Subtype.ext ?_
  rw [Stacks.Picard.torsionByRestrict_apply]
  change ((h1RootsOfUnityAddEquivPicardTorsion.{u + 1, 0, u} C (ℓ ^ m) hn0 hX hsurj
      (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 1
        (etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) 1 x)) : Stacks.Picard.ofScheme C)) =
    Stacks.Picard.schemePullbackClassHom φ
      (h1RootsOfUnityAddEquivPicardTorsion.{u + 1, 0, u} C (ℓ ^ m) hn0 hX hsurj
        (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 1 x))
  rw [sheafHRootsOfUnityConstantAddEquiv_etaleConstantCohomologyPullback hζ hn0 f φ w]
  exact h1RootsOfUnityAddEquivPicardTorsion_naturality.{u + 1, 0, u} φ (ℓ ^ m) hn0 hX hX
    hsurj hsurj _

variable [Smooth f]

include w in
/-- **The trace of `φ^*` on `H²(C, ℤ/n)` is `deg φ`**: the choice of a primitive `n`-th root of
unity identifies `H²(C, ℤ/n)` with `H²(C, μ_n) = Pic(C)/n Pic(C) ≅ ℤ/n`, on which `φ^*` is
multiplication by `deg φ`, compatibly with pullback along `φ`. -/
theorem trace_etaleConstantCohomologyPullback_two {n : ℕ} (hn : IsUnit (n : k)) :
    LinearMap.trace (ZMod n) _ ((etaleConstantCohomologyPullback φ (ZMod n) 2).toZModLinearMap n) =
      (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ZMod n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  have hdim : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  let E := (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 2).trans (smoothProperCurveTrace f hn)
  rw [trace_toZModLinearMap_eq_of_addEquiv E _
    ((AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ℤ) • AddMonoidHom.id (ZMod n)) ?_,
    trace_zsmul_id_zmod, Int.cast_natCast]
  intro x
  change smoothProperCurveTrace f hn (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 2
      (etaleConstantCohomologyPullback φ (ZMod n) 2 x)) =
    (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ℤ) •
      smoothProperCurveTrace f hn (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 2 x)
  rw [sheafHRootsOfUnityConstantAddEquiv_etaleConstantCohomologyPullback hζ hn0 f φ w]
  refine smoothProperCurveTrace_rootsOfUnityPullbackMap f f hn hn φ _ (fun L => ?_) _
  rw [← Stacks.Picard.picardDegree_picardModelAddEquiv f hdim,
    ← Stacks.Picard.picardDegree_picardModelAddEquiv f hdim]
  exact AlgebraicGeometry.CurveGraph.picardDegree_schemePullbackClass f hdim φ w L

include w in
/-- **The alternating sum of the traces of `φ^*` on `H^i(C, ℤ/ℓ^m)`**, degree by degree: it is
`1 - Tr(φ^* | Pic(C)[ℓ^m]) + deg φ` in `ℤ/ℓ^m`. -/
theorem sum_trace_etaleConstantCohomologyPullback (ℓ m : ℕ) [NeZero ℓ] (hℓ : IsUnit (ℓ : k)) :
    ∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ m)) ^ i * LinearMap.trace (ZMod (ℓ ^ m)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) i).toZModLinearMap (ℓ ^ m)) =
      1 - picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ m +
        (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ZMod (ℓ ^ m)) := by
  have hn := isUnit_natCast_pow ℓ m hℓ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    trace_etaleConstantCohomologyPullback_zero f φ hn,
    trace_etaleConstantCohomologyPullback_one f φ w ℓ m hℓ,
    trace_etaleConstantCohomologyPullback_two f φ w hn]
  ring

include w in
/-- **`∑_i (-1)^i Tr(φ^* | H^i(C, ℤ/ℓ^m)) = 1 - Tr_J(φ^*) + deg φ mod ℓ^m`**, with `Tr_J(φ^*)` the
trace of `φ^*` on the `ℓ`-adic Tate module of the jacobian `Pic⁰(C)`. -/
theorem sum_trace_etaleConstantCohomologyPullback_eq_toZModPow (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∑ i ∈ Finset.range 3, (-1 : ZMod (ℓ ^ m)) ^ i * LinearMap.trace (ZMod (ℓ ^ m)) _
        ((etaleConstantCohomologyPullback φ (ZMod (ℓ ^ m)) i).toZModLinearMap (ℓ ^ m)) =
      PadicInt.toZModPow m (1 - AlgebraicGeometry.CurveGraph.jacobianTateTrace f
        (IsCurve.topologicalKrullDim_eq_one (f := f)).le φ w ℓ +
          (AlgebraicGeometry.CurveGraph.curveMapDegree f φ w : ℤ_[ℓ])) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [sum_trace_etaleConstantCohomologyPullback f φ w ℓ m hℓ, map_add, map_sub, map_one,
    map_natCast, AlgebraicGeometry.CurveGraph.toZModPow_jacobianTateTrace f _ φ w ℓ hℓ m]

include f in
/-- **Every `H^i(C, ℤ/ℓ^m)` is a free `ℤ/ℓ^m`-module of finite rank**: `H⁰` and `H²` are free of
rank one, `H¹ = Pic(C)[ℓ^m] = Pic⁰(C)[ℓ^m]` is free of rank `2g` (it is the `ℓ^m`-torsion of the
jacobian), and `H^i = 0` for `i ≥ 3`. -/
@[sga "4½ Arcata 3.3.5" "Freeness of H^q(X"]
theorem module_free_finite_sheafH_etaleConstantSheaf (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) (i : ℕ) :
    Module.Free (ZMod (ℓ ^ m)) (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ m))) i) ∧
      Module.Finite (ZMod (ℓ ^ m))
        (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ m))) i) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hn := isUnit_natCast_pow ℓ m hℓ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  have hn0 := ne_zero_of_isUnit_natCast hn
  have hdim : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  match i with
  | 0 =>
    exact module_free_finite_of_addEquiv (AddEquiv.ofBijective (etaleConstantClass C _)
      (etaleConstantClass_bijective f hζ hn0)).symm
  | 1 =>
    have hX := isUnit_natCast_globalSections C (ℓ ^ m) f hn
    have hsurj := surjective_sheafH_map_powMap_zero.{u + 1, u, 0} C (n := ℓ ^ m)
      (exists_pow_eq_globalUnit C (ℓ ^ m) f (Nat.pos_of_ne_zero hn0))
    obtain ⟨J, _, _, E, -⟩ := exists_jacobian_data f k hdim
    let e := (Stacks.Groupoids.nonempty_torsionBy_pow_addEquiv J ℓ hℓ m).some
    exact module_free_finite_of_addEquiv ((sheafHRootsOfUnityConstantAddEquiv f hζ hn0 1).trans
      ((h1RootsOfUnityAddEquivPicardTorsion.{u + 1, 0, u} C (ℓ ^ m) hn0 hX hsurj).trans
        ((Stacks.AbelianGroup.torsionByNatCastPowEquiv _ ℓ m).trans
          ((AlgebraicGeometry.CurveGraph.picardDegreeZeroTorsionEquiv f hdim ℓ m).symm.trans
            ((Stacks.AbelianGroup.torsionAddEquiv E _).symm.trans e)))))
  | 2 =>
    exact module_free_finite_of_addEquiv
      ((sheafHRootsOfUnityConstantAddEquiv f hζ hn0 2).trans (smoothProperCurveTrace f hn))
  | q + 3 =>
    have hs : Subsingleton (Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} C (ℓ ^ m)) (q + 3)) :=
      subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve f hn (q + 3) (by lia)
    have : Subsingleton (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod (ℓ ^ m))) (q + 3)) :=
      (sheafHRootsOfUnityConstantAddEquiv f hζ hn0 (q + 3)).injective.subsingleton
    exact ⟨Module.Free.of_subsingleton _ _, Module.Finite.of_finite⟩

end Curve

end Stacks.EtaleCohomology
