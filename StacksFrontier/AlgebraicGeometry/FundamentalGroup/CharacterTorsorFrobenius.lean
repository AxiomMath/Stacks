module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsorClassRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree

/-!
# Pullback of the `μ_n`-torsor of a character along a Frobenius twist

Let `σ : S ⟶ S` be an endomorphism over `Y` of the base `S` of the `μ_n`-torsor `P` of a character
torsor (`AlgebraicGeometry.CharacterTorsorData.baseTorsor`), pulling the root of unity `ζ` back to
`ζ ^ q`. The torsor scheme `T ×_Y S` is its own base change along `σ`, and for `q m ≡ 1 (mod n)`
a root of unity `u` acts on the base change of a section `s` as `u ^ m` acts on `s`: on the piece
where `u = ζ ^ a`, the pulled back `u` is `ζ ^ (q a)` for the structure of the source. By
`Stacks.EtaleCohomology.sheafHMap_etaleCohomologyRestrictionMap_torsorClass`, the pullback of the
class of `P` along `σ` is `q` times the class of `P`.

## Main results

* `Stacks.Kummer.nsmul_sheafH_rootsOfUnity_eq_zero`: `H^i(S, μ_n)` is killed by `n`.
* `Stacks.Kummer.rootsOfUnitySection_transpose`: the transpose of the comparison
  `π^{-1} μ_n ⟶ μ_n` pulls roots of unity back.
* `AlgebraicGeometry.CharacterTorsorData.rootsOfUnityPullbackMap_baseTorsor`: the pullback along
  `σ` of the class of the torsor of a character is `q` times that class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Stacks.Cohomology.Torsors Stacks.EtaleCohomology

universe w u

namespace Stacks.Kummer

/-- `n` times the identity of `μ_n` is zero. -/
theorem nsmul_id_rootsOfUnitySheaf (S : Scheme.{u}) (n : ℕ) :
    n • 𝟙 (rootsOfUnitySheaf.{u, 0} S n) = 0 := by
  rw [← cancel_mono (rootsOfUnityι.{u, 0} S n), zero_comp, Preadditive.nsmul_comp,
    Category.id_comp, ← Category.comp_id (rootsOfUnityι.{u, 0} S n), ← Preadditive.comp_nsmul]
  exact rootsOfUnityι_comp_powMap S n

/-- The map on `H^i` induced by `m • g` is `m` times the map induced by `g`. -/
theorem sheafH_map_nsmul_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (g : F ⟶ G) (m i : ℕ) (x : Sheaf.H.{w} F i) :
    Sheaf.H.map (m • g) i x = m • Sheaf.H.map g i x := by
  induction m with
  | zero =>
    rw [zero_nsmul, zero_nsmul, Sheaf.H.map_apply, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, succ_nsmul]

/-- `H^i(S, μ_n)` is killed by `n`. -/
theorem nsmul_sheafH_rootsOfUnity_eq_zero (S : Scheme.{u}) (n : ℕ)
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : ℕ)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, 0} S n) i) : n • x = 0 := by
  have h := sheafH_map_nsmul_apply (𝟙 (rootsOfUnitySheaf.{u, 0} S n)) n i x
  rw [nsmul_id_rootsOfUnitySheaf, Sheaf.H.map_id_apply, Sheaf.H.map_apply,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] at h
  exact h.symm

/-- **The transpose of the comparison `π^{-1} μ_n ⟶ μ_n` pulls roots of unity back** along the
projection `U ×_Y X ⟶ U`. -/
theorem rootsOfUnitySection_transpose {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ) (U : Y.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, 0} Y n).obj.obj (op U))) :
    (rootsOfUnitySection.{u, 0} X n (op ((smallEtaleBaseChange π).obj U))
      ((((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).homEquiv _ _
        (rootsOfUnityInverseImageComparison.{u, 0} π n)).hom.app (op U)) s)).1 =
      Units.map (pullback.fst U.hom π).appTop.hom.toMonoidHom
        (rootsOfUnitySection.{u, 0} Y n (op U) s).1 := by
  set adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} π
  have h1 : adj.homEquiv _ _ (rootsOfUnityInverseImageComparison.{u, 0} π n) ≫
      (etaleAbelianDirectImage.{u, 0} π).map (rootsOfUnityι.{u, 0} X n) =
      rootsOfUnityι.{u, 0} Y n ≫ multiplicativeDirectImageComparison.{u, 0} π := by
    rw [← Adjunction.homEquiv_naturality_right,
      rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, Adjunction.homEquiv_naturality_left,
      multiplicativeInverseImageComparison_transpose]
  have h2 := congrArg (fun φ => φ.hom.app (op U) s) h1
  have h3 : (multiplicativeDirectImageComparison.{u, 0} π).hom.app (op U)
      ((rootsOfUnityι.{u, 0} Y n).hom.app (op U) s) =
      ofUnit.{u, 0} (U := (smallEtaleBaseChange π).obj U)
        (Units.map (pullback.fst U.hom π).appTop.hom.toMonoidHom
          (rootsOfUnitySection.{u, 0} Y n (op U) s).1) := by
    rw [rootsOfUnityι_app_eq_ofUnit]
    exact multiplicativeDirectImageComparison_app_ofUnit π U _
  exact ofUnit_injective.{u, 0} (h2.trans h3)

/-- On sections over `U`, the morphism of sheaves `m • g` sends `t` to `m • g t`. -/
theorem sheaf_nsmul_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (g : F ⟶ G) (m : ℕ) (U : Cᵒᵖ)
    (t : ToType (F.obj.obj U)) : (m • g).hom.app U t = m • g.hom.app U t := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, ← ih]
    rfl

/-- The root of unity of the section `m • t` of `μ_n` is the `m`-th power of that of `t`. -/
theorem rootsOfUnitySection_nsmul (S : Scheme.{u}) (n m : ℕ) (U : S.Etale)
    (t : ToType ((rootsOfUnitySheaf.{u, 0} S n).obj.obj (op U))) :
    (rootsOfUnitySection.{u, 0} S n (op U) (m • t)).1 =
      (rootsOfUnitySection.{u, 0} S n (op U) t).1 ^ m := by
  refine ofUnit_injective.{u, 0} ?_
  rw [← rootsOfUnityι_app_eq_ofUnit, map_nsmul, rootsOfUnityι_app_eq_ofUnit, ← natCast_zsmul,
    zsmul_ofUnit, zpow_natCast]

/-- The transpose of `π^{-1} μ_n ⟶ μ_n ⟶ μ_n`, the comparison followed by the `m`-th power,
sends a root of unity `u` to `(pr₁^* u) ^ m` along the projection `U ×_Y X ⟶ U`. -/
theorem rootsOfUnitySection_transpose_comp_nsmul {X Y : Scheme.{u}} (π : X ⟶ Y) (n m : ℕ)
    (U : Y.Etale) (s : ToType ((rootsOfUnitySheaf.{u, 0} Y n).obj.obj (op U))) :
    (rootsOfUnitySection.{u, 0} X n (op ((smallEtaleBaseChange π).obj U))
      ((((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).homEquiv _ _
        (rootsOfUnityInverseImageComparison.{u, 0} π n ≫
          (m • 𝟙 (rootsOfUnitySheaf.{u, 0} X n)))).hom.app (op U)) s)).1 =
      Units.map (pullback.fst U.hom π).appTop.hom.toMonoidHom
        (rootsOfUnitySection.{u, 0} Y n (op U) s).1 ^ m := by
  have hv : ((((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).homEquiv _ _
      (rootsOfUnityInverseImageComparison.{u, 0} π n ≫
        (m • 𝟙 (rootsOfUnitySheaf.{u, 0} X n)))).hom.app (op U)) s) =
      m • ((((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).homEquiv _ _
        (rootsOfUnityInverseImageComparison.{u, 0} π n)).hom.app (op U)) s) := by
    rw [Adjunction.homEquiv_naturality_right]
    exact sheaf_nsmul_app_apply _ m _ _
  refine (congrArg (fun t => (rootsOfUnitySection.{u, 0} X n
    (op ((smallEtaleBaseChange π).obj U)) t).1) hv).trans
    ((rootsOfUnitySection_nsmul X n m _ _).trans ?_)
  rw [rootsOfUnitySection_transpose]
  rfl

end Stacks.Kummer

namespace AlgebraicGeometry

open Stacks.Kummer

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {n : ℕ} [NeZero n]
  {V : Subgroup (EtaleFundamentalGroup X x)} {Y : FiniteEtaleOver X}
  {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}
  {χ : V → ZMod n} {hadd : ∀ a b, χ (a * b) = χ a + χ b}

namespace CharacterTorsorData

variable (D : CharacterTorsorData x χ hadd Y eY) {K : Type u} [Field K] [DecidableEq K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ n) {S : Scheme.{u}} (fS : S ⟶ Spec (.of K)) (π : S ⟶ Y.left)
  [ConnectedSpace Y.left] (σ : S ⟶ S) (hσπ : σ ≫ π = π)

omit [NeZero n] [ConnectedSpace Y.left] in
include hσπ in
/-- For a section `s` of the torsor scheme over `U`, the composite
`U ×_S S ⟶ U ⟶ T ×_Y S ⟶ T ⟶ Y` agrees with `U ×_S S ⟶ S ⟶ Y`, where the fibre product is
taken along `σ`. -/
theorem frobSection_condition (U : S.Etale) (s : U.left ⟶ pullback D.q.left π)
    (hs : s ≫ pullback.snd D.q.left π = U.hom) :
    (pullback.fst U.hom σ ≫ s ≫ pullback.fst D.q.left π) ≫ D.q.left =
      pullback.snd U.hom σ ≫ π := by
  rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hs, pullback.condition_assoc,
    hσπ]

include hσπ in
/-- The base change along `σ` of a section of the torsor scheme. -/
def frobSection (U : S.Etale) (s : U ⟶ Scheme.Etale.mk (pullback.snd D.q.left π)) :
    (Stacks.EtaleCohomology.smallEtaleBaseChange σ).obj U ⟶
      Scheme.Etale.mk (pullback.snd D.q.left π) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst U.hom σ ≫ s.left ≫ pullback.fst D.q.left π)
      (pullback.snd U.hom σ) (D.frobSection_condition π σ hσπ U s.left (MorphismProperty.Over.w s)))
    (pullback.lift_snd _ _ _)

omit [NeZero n] [ConnectedSpace Y.left] in
/-- The base change along `σ` of sections of the torsor scheme commutes with restriction along
a morphism `g : W ⟶ U`. -/
theorem frobSection_comp {U W : S.Etale} (g : W ⟶ U)
    (s : U ⟶ Scheme.Etale.mk (pullback.snd D.q.left π)) :
    D.frobSection π σ hσπ W (g ≫ s) =
      (Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g ≫ D.frobSection π σ hσπ U s := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift _ _ _ = ((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g).left ≫
    pullback.lift _ _ _
  have e1 : ((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g).left ≫
      pullback.fst U.hom σ = pullback.fst W.hom σ ≫ g.left :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst σ g
  have e2 : ((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g).left ≫
      pullback.snd U.hom σ = pullback.snd W.hom σ :=
    MorphismProperty.Over.w ((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g)
  apply pullback.hom_ext
  · refine (pullback.lift_fst _ _ _).trans (Eq.trans ?_
      (congrArg (((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g).left ≫ ·)
        (pullback.lift_fst _ _ _)).symm)
    have e3 : pullback.fst W.hom σ ≫ (g ≫ s).left ≫ pullback.fst D.q.left π =
        (pullback.fst W.hom σ ≫ g.left) ≫ s.left ≫ pullback.fst D.q.left π := by
      rw [Category.assoc]
      exact congrArg (pullback.fst W.hom σ ≫ ·) (Category.assoc g.left s.left _)
    exact e3.trans ((congrArg (· ≫ s.left ≫ pullback.fst D.q.left π) e1.symm).trans
      (Category.assoc _ _ _))
  · exact (pullback.lift_snd _ _ _).trans (e2.symm.trans
      (congrArg (((Stacks.EtaleCohomology.smallEtaleBaseChange σ).map g).left ≫ ·)
        (pullback.lift_snd _ _ _)).symm)

/-- **The base change along `σ`, on sections of the torsor.** -/
def frobAlpha : (D.baseTorsor hζ fS π).1.presheaf ⟶
    (Stacks.EtaleCohomology.smallEtaleBaseChange σ).op ⋙ (D.baseTorsor hζ fS π).1.presheaf where
  app U := ↾ fun s => ULift.up (D.frobSection π σ hσπ U.unop s.down)
  naturality U W g := by
    ext s
    exact ULift.ext (D.frobSection_comp π σ hσπ g.unop s.down)

omit [ConnectedSpace Y.left] in
include hζ hσπ in
/-- **The base change of a translated section, on a piece where the root of unity is constant.**
If `u = ζ ^ a` on the image of `h`, then `h ≫ σ^*(u • s) = h ≫ σ^*(s) ≫ τ_a`. -/
theorem comp_frobSection_rootSMul (U : S.Etale) (xu : Γ(U.left, ⊤)) (hxu : xu ^ n = 1)
    (s : U.left ⟶ pullback D.q.left π) (hs : s ≫ pullback.snd D.q.left π = U.hom)
    {Z : Scheme.{u}} (h : Z ⟶ pullback U.hom σ) (a : ZMod n)
    (ha : (h ≫ pullback.fst U.hom σ).appTop.hom xu =
      baseRingMap fS ((h ≫ pullback.fst U.hom σ) ≫ U.hom) (ζ ^ a.val)) :
    h ≫ pullback.lift (pullback.fst U.hom σ ≫ rootSMul fS hζ (D.τZ π) U.hom xu hxu s ≫
        pullback.fst D.q.left π) (pullback.snd U.hom σ)
        (D.frobSection_condition π σ hσπ U _ (rootSMul_comp fS hζ _ _ _ _
          (fun a => baseChangeTranslation_snd _ _ _ _ a) s hs)) =
      h ≫ pullback.lift (pullback.fst U.hom σ ≫ s ≫ pullback.fst D.q.left π)
        (pullback.snd U.hom σ) (D.frobSection_condition π σ hσπ U s hs) ≫ D.τZ π a := by
  have h1 := comp_rootSMul_of_eq fS hζ (D.τZ π) U.hom xu hxu s (h ≫ pullback.fst U.hom σ) a ha
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, baseChangeTranslation_fst,
      pullback.lift_fst_assoc]
    have h2 := congrArg (· ≫ pullback.fst D.q.left π) h1
    simp only [Category.assoc, baseChangeTranslation_fst] at h2
    exact h2
  · simp only [Category.assoc, pullback.lift_snd, baseChangeTranslation_snd]

/-- Evaluating the global sections map of a composite is evaluating the two maps in turn. -/
private theorem appTop_comp_hom_apply {Z W W' : Scheme.{u}} (h : Z ⟶ W) (g : W ⟶ W')
    (y : Γ(W', ⊤)) : (h ≫ g).appTop.hom y = h.appTop.hom (g.appTop.hom y) := by
  rw [Scheme.Hom.comp_appTop]; rfl

omit [NeZero n] [DecidableEq K] [ConnectedSpace Y.left] in
/-- **The transposed root of unity on a piece.** If `σ` pulls `ζ` back to `ζ ^ q` and
`ζ ^ (q m) = ζ`, then on the piece where `u = ζ ^ a` the root `(pr₁^* u) ^ m` of the base change is
`ζ ^ a` for the structure of the base change. -/
theorem appTop_fst_pow_eq (U : S.Etale) (xu : Γ(U.left, ⊤)) {Z : Scheme.{u}}
    (h : Z ⟶ pullback U.hom σ) (a : ZMod n)
    (ha : (h ≫ pullback.fst U.hom σ).appTop.hom xu =
      baseRingMap fS ((h ≫ pullback.fst U.hom σ) ≫ U.hom) (ζ ^ a.val)) (q m : ℕ)
    (hσζ : σ.appTop.hom (baseRingMap fS (𝟙 S) ζ) = baseRingMap fS (𝟙 S) ζ ^ q)
    (hqm : ζ ^ (q * m) = ζ) :
    h.appTop.hom ((pullback.fst U.hom σ).appTop.hom xu ^ m) =
      baseRingMap fS (h ≫ pullback.snd U.hom σ) (ζ ^ a.val) := by
  have e1 : (h ≫ pullback.fst U.hom σ) ≫ U.hom = (h ≫ pullback.snd U.hom σ) ≫ σ := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have e2 : baseRingMap fS σ ζ = baseRingMap fS (𝟙 S) ζ ^ q := by
    rw [← hσζ, baseRingMap_comp_apply, Category.comp_id]
  rw [map_pow, ← appTop_comp_hom_apply, ha, e1,
    ← baseRingMap_comp_apply, map_pow, e2, ← pow_mul, map_pow, baseRingMap_comp_apply,
    Category.comp_id]
  simp only [← map_pow, ← pow_mul]
  have hz : ζ ^ (q * a.val * m) = ζ ^ a.val := by
    rw [show q * a.val * m = (q * m) * a.val by ring, pow_mul, hqm]
  rw [hz]

omit [ConnectedSpace Y.left] in
include hσπ in
/-- **The base change of a translated section.** If `σ` pulls `ζ` back to `ζ ^ q`,
`ζ ^ (q m) = ζ` and `v = (pr₁^* u) ^ m`, then `σ^*(u • s) = v • σ^* s`. -/
theorem frobSection_rootSMul_eq (q m : ℕ)
    (hσζ : σ.appTop.hom (baseRingMap fS (𝟙 S) ζ) = baseRingMap fS (𝟙 S) ζ ^ q)
    (hqm : ζ ^ (q * m) = ζ) (U : S.Etale) (xu : Γ(U.left, ⊤)) (hxu : xu ^ n = 1)
    (s : U.left ⟶ pullback D.q.left π) (hs : s ≫ pullback.snd D.q.left π = U.hom)
    (xv : Γ(pullback U.hom σ, ⊤)) (hxv : xv ^ n = 1)
    (hv : xv = (pullback.fst U.hom σ).appTop.hom xu ^ m) :
    pullback.lift (pullback.fst U.hom σ ≫ rootSMul fS hζ (D.τZ π) U.hom xu hxu s ≫
        pullback.fst D.q.left π) (pullback.snd U.hom σ)
        (D.frobSection_condition π σ hσπ U _ (rootSMul_comp fS hζ _ _ _ _
          (fun a => baseChangeTranslation_snd _ _ _ _ a) s hs)) =
      rootSMul fS hζ (D.τZ π) (pullback.snd U.hom σ) xv hxv
        (pullback.lift (pullback.fst U.hom σ ≫ s ≫ pullback.fst D.q.left π)
          (pullback.snd U.hom σ) (D.frobSection_condition π σ hσπ U s hs)) := by
  have hx' : ((pullback.fst U.hom σ).appTop.hom xu) ^ n = 1 := by
    rw [← map_pow, hxu, map_one]
  refine piece_hom_ext fS hζ (pullback.fst U.hom σ ≫ U.hom)
    ((pullback.fst U.hom σ).appTop.hom xu) _ _ fun a => ?_
  have h0 := appTop_ι_piece fS hζ (pullback.fst U.hom σ ≫ U.hom)
    ((pullback.fst U.hom σ).appTop.hom xu) hx' a
  have ha := (appTop_comp_hom_apply _ (pullback.fst U.hom σ) xu).trans (h0.trans
    (congrArg (fun t => baseRingMap fS t (ζ ^ a.val)) (Category.assoc _ _ _).symm))
  refine (D.comp_frobSection_rootSMul hζ fS π σ hσπ U xu hxu s hs _ a ha).trans ?_
  symm
  refine comp_rootSMul_of_eq fS hζ (D.τZ π) (pullback.snd U.hom σ) _ _ _ _ a ?_
  rw [hv]
  exact appTop_fst_pow_eq fS σ U xu _ a ha q m hσζ hqm

include hσπ in
/-- **The base change along `σ` is equivariant along the twisted comparison.** If `σ` pulls `ζ`
back to `ζ ^ q` and `ζ ^ (q m) = ζ`, the base change of `u • s` is `(σ^* u) ^ m • σ^* s`: the
transpose of `π^{-1} μ_n ⟶ μ_n ⟶ μ_n` (comparison, then `m`-th power) is `u ↦ (pr₁^* u) ^ m`, and
on the piece where `pr₁^* u = ζ ^ a` both sides are `σ^* s` translated by `a`. -/
theorem frobAlpha_app_act (q m : ℕ)
    (hσζ : σ.appTop.hom (baseRingMap fS (𝟙 S) ζ) = baseRingMap fS (𝟙 S) ζ ^ q)
    (hqm : ζ ^ (q * m) = ζ) (U : (S.Etale)ᵒᵖ) (h : (rootsOfUnitySheaf.{u, 0} S n).obj.obj U)
    (s : (D.baseTorsor hζ fS π).1.presheaf.obj U) :
    (D.frobAlpha hζ fS π σ hσπ).app U
        ((D.baseTorsor hζ fS π).1.act U (Multiplicative.ofAdd h) s) =
      (D.baseTorsor hζ fS π).1.act ((Stacks.EtaleCohomology.smallEtaleBaseChange σ).op.obj U)
        (Multiplicative.ofAdd
          (((etaleAbelianInverseImageDirectImageAdj.{u, 0} σ).homEquiv _ _
            (rootsOfUnityInverseImageComparison.{u, 0} σ n ≫
              (m • 𝟙 (rootsOfUnitySheaf.{u, 0} S n)))).hom.app U h))
        ((D.frobAlpha hζ fS π σ hσπ).app U s) := by
  refine ULift.ext (MorphismProperty.Over.Hom.ext ?_)
  refine D.frobSection_rootSMul_eq hζ fS π σ hσπ q m hσζ hqm U.unop _ (sectionRootVal_pow _ _)
    s.down.left (MorphismProperty.Over.w s.down) _ (sectionRootVal_pow _ _) ?_
  exact (congrArg Units.val
    (rootsOfUnitySection_transpose_comp_nsmul σ n m U.unop h)).trans
    (by rw [Units.val_pow_eq_pow_val, Units.coe_map]; rfl)

include hσπ in
/-- **The pullback along `σ` of the class of the torsor of a character is `q` times it**, where `σ`
pulls `ζ` back to `ζ ^ q` and `q` is invertible mod `n`: `σ^*[P] = q • [P]` in `H¹(S, μ_n)`. -/
theorem rootsOfUnityPullbackMap_baseTorsor
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] (q m : ℕ)
    (hσζ : σ.appTop.hom (baseRingMap fS (𝟙 S) ζ) = baseRingMap fS (𝟙 S) ζ ^ q)
    (hqm : ((q * m : ℕ) : ZMod n) = 1) :
    rootsOfUnityPullbackMap.{u, 0, w} σ n 1
        (torsorIsoClassesEquivH1 _ (Quotient.mk _ (D.baseTorsor hζ fS π))) =
      q • torsorIsoClassesEquivH1 _ (Quotient.mk _ (D.baseTorsor hζ fS π)) := by
  have hqm' : (q * m) % n = 1 % n := by
    have := (ZMod.natCast_eq_natCast_iff' (q * m) 1 n).1 (by rw [hqm, Nat.cast_one])
    exact this
  have hζqm : ζ ^ (q * m) = ζ := by
    rw [← Nat.mod_add_div (q * m) n, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one, hqm',
      hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  have h := sheafHMap_etaleCohomologyRestrictionMap_torsorClass.{w, 0, u} σ
    (rootsOfUnitySheaf.{u, 0} S n) (rootsOfUnitySheaf.{u, 0} S n)
    (rootsOfUnityInverseImageComparison.{u, 0} σ n ≫ (m • 𝟙 (rootsOfUnitySheaf.{u, 0} S n)))
    (D.baseTorsor hζ fS π) (D.baseTorsor hζ fS π) (D.frobAlpha hζ fS π σ hσπ)
    (D.frobAlpha_app_act hζ fS π σ hσπ q m hσζ hζqm)
  rw [Sheaf.H.map_comp_apply, sheafH_map_nsmul_apply, Sheaf.H.map_id_apply] at h
  rw [rootsOfUnityPullbackMap_apply]
  set y := Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, 0} σ n) 1
    (etaleCohomologyRestrictionMap.{u, 0, w} σ (rootsOfUnitySheaf.{u, 0} S n) 1
      (torsorIsoClassesEquivH1 _ (Quotient.mk _ (D.baseTorsor hζ fS π))))
  have key : ∀ a : ℕ, a • y = (a % n) • y := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a n]
    rw [add_nsmul, mul_smul, nsmul_sheafH_rootsOfUnity_eq_zero, add_zero]
  rw [← h, ← mul_smul, key, hqm', ← key, one_smul]

end CharacterTorsorData

end AlgebraicGeometry
