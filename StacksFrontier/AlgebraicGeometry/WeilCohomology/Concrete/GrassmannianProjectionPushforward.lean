module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PushforwardCompatibleCancel
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalProjectionPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FlagTowerObject
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundlePushforward

/-!
# Stacks 0FIQ: the cycle class map commutes with pushforward along `X × G(l, n) ⟶ X`

Let data (D0), (D1), (D2') satisfy axioms (A1)–(A7) of Section 45.14
(`Stacks.WeilCohomology.WeilChernData`), with `γ` the cycle class map of Tag 0FIF, and let `X` be
a nonempty equidimensional smooth projective scheme over `k`. For `0 < l < n`, `γ` commutes with
pushforward along the projection `p : X × G(l, n) ⟶ X`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_bundleProj`: Lemma 0FIN in the form
  `WeilData.PushforwardCompatible`.
* `Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_towerHom`: `γ` commutes with
  pushforward along a tower of projective bundles.
* `Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_fst_grassmannian`: `γ` commutes with
  pushforward along the projection `X × G(l, n) ⟶ X`.

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow Stacks.FlagTower

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- A smooth projective scheme isomorphic to one of relative dimension `d` has relative
dimension `d`. -/
theorem relativeDimension_of_hom_of_inv {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) {d : ℕ}
    (hY : RelativeDimension Y.obj.hom d) : RelativeDimension X.obj.hom d := by
  have : IsIso f.hom.left :=
    ⟨⟨g.hom.left, by simpa using congrArg (fun φ ↦ φ.hom.left) hfg,
      by simpa using congrArg (fun φ ↦ φ.hom.left) hgf⟩⟩
  exact relativeDimension_of_eq (Over.w f.hom)
    (RelativeDimension.comp_isOpenImmersion f.hom.left Y.obj.hom hY)

namespace WeilChernData

open SmoothProjectiveScheme

variable {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Lemma 0FIN** in the form `WeilData.PushforwardCompatible`: `γ` commutes with pushforward
along the projection `𝐏(ℰ) ⟶ X` of a projective bundle. -/
theorem pushforwardCompatible_bundleProj (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((SmoothProjectiveScheme.toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
      (SmoothProjectiveScheme.bundleProj X E r) :=
  fun _ _ hP hX i j hij α ↦ 𝔚.cycleClass_equidimensionalPushforward_bundleProj hX hP i j hij α

/-- `γ` commutes with pushforward along the projection `towerHom s hp m E r hE hm` of a tower of
`m` projective bundles over `Y`. -/
theorem pushforwardCompatible_towerHom (m : ℕ) {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    [Smooth s] (hp : IsProjective s) (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (hm : m ≤ r) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing (towerHom s hp m E r hE hm) := by
  induction m generalizing Y r with
  | zero =>
    refine 𝔚.pushforwardCompatible_of_inverse _
      (SmoothProjectiveScheme.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _)))
      ?_ ?_
    · exact SmoothProjectiveScheme.hom_ext' (Category.comp_id _)
    · exact SmoothProjectiveScheme.hom_ext' (Category.id_comp _)
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r' : ℕ, r = r' + 1 := ⟨r - 1, by omega⟩
    have := hE
    rw [towerHom_succ s hp m E r hm]
    let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (r + 1)
    have := locallyOfFiniteType_bundleProj E r
    have := smooth_bundleProj E r
    have hdimP : ∀ c : ℕ, RelativeDimension s c →
        RelativeDimension (bundleProj E ≫ s) (r + c) := fun c hc ↦
      RelativeDimension.comp_of_flat (bundleProj E) s (relativeDimension_bundleProj E r) hc
    have hlast : 𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
        (bundleBaseHom s hp E r ≫
          SmoothProjectiveScheme.bundleProj (SmoothProjectiveScheme.mk s inferInstance hp) E r) :=
      WeilData.PushforwardCompatible.comp_of_forall (fun d _ hP _ ↦ ⟨d, hP.nonempty.elim
          fun y ↦ ⟨(bundleBaseHom s hp E r).hom.left y⟩, hP.relativeDimension⟩)
        (𝔚.cycleClass_congr _)
        (𝔚.pushforwardCompatible_of_inverse _ _ (bundleBaseHom_inv s hp E r)
          (bundleBaseInv_hom s hp E r))
        (𝔚.pushforwardCompatible_bundleProj (SmoothProjectiveScheme.mk s inferInstance hp) E r)
    have hinner : 𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
        (kernelTowerHom s hp m E r hm ≫ bundleBaseHom s hp E r ≫
          SmoothProjectiveScheme.bundleProj (SmoothProjectiveScheme.mk s inferInstance hp) E r) :=
        by
      refine WeilData.PushforwardCompatible.comp_of_forall (fun _ c hK hX ↦ ⟨r + c,
        hK.nonempty.elim fun y ↦ ⟨(kernelTowerHom s hp m E r hm).hom.left y⟩,
        hdimP c hX.relativeDimension⟩) (𝔚.cycleClass_congr _) ?_ hlast
      have := smooth_bundleProj_comp_spec s hp E r
      exact @ih _ (bundleProj E ≫ s) _ (isProjective_bundleProj_comp_spec s hp E r)
        (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E) r
        (isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE) (by omega)
    exact WeilData.PushforwardCompatible.comp_of_forall (fun d _ hS _ ↦ ⟨d, hS.nonempty.elim
        fun y ↦ ⟨(towerSuccHom s hp m E r hm).hom.left y⟩,
        relativeDimension_of_hom_of_inv _ _ (towerSuccInv_hom s hp m E r hm)
          (towerSuccHom_inv s hp m E r hm) hS.relativeDimension⟩) (𝔚.cycleClass_congr _)
      (𝔚.pushforwardCompatible_of_inverse _ _ (towerSuccHom_inv s hp m E r hm)
        (towerSuccInv_hom s hp m E r hm)) hinner

/-- Let data (D0), (D1), (D2') satisfy axioms (A1)–(A7) of Section 45.14 (`WeilChernData`), with
`γ` the cycle class map of Tag 0FIF and the pushforward on cohomology of Section 45.9 built from
the trace maps `λ` of (A6) (`WeilChernData.toWeilData`, Poincaré duality being Lemma 0FIJ). For
integers `l < n` (in particular `0 < l < n`) and a smooth projective scheme `X` over `k`, `γ`
commutes with pushforward along the projection `p : X × G(l, n) ⟶ X`: whenever `X` is nonempty and
equidimensional of dimension `d` and `X × G(l, n)` of dimension `d'`, `γ(p_*α) = p_*γ(α)` in
`H^{2q}(X)(q)` for every `α ∈ CH^i(X × G(l, n))`, `q = i + d - d'`. -/
@[stacks 0FIQ "the whole lemma, under exactly (A1)-(A7) (WeilChernData): for l < n (so in \
  particular 0 < l < n) and X nonempty equidimensional, gamma commutes with pushforward along \
  p : X × G(l, n) -> X, gamma(p_* alpha) = p_* gamma(alpha) for every alpha in CH^i(X × G(l, n)), \
  with the pushforward of Section 0FHA for toWeilData; nothing assumed"]
theorem pushforwardCompatible_fst_grassmannian {l n : ℕ} (hln : l < n)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
      (fst X (SmoothProjectiveScheme.grassmannian k l n)) := by
  set X' := (SmoothProjectiveScheme.toScheme k).obj X
  set G := SmoothProjectiveScheme.grassmannian k l n
  have := isFiniteLocallyFree_universalQuotient l n X'
  have := isFiniteLocallyFree_freeModule n X'
  set sG := (Grassmannian.schemeOver.over l n X').hom ≫ X.obj.hom
  have hpG : IsProjective sG := SmoothProjectiveScheme.isProjective (grassmannianOver X l n)
  have hpX : IsProjective X.obj.hom := SmoothProjectiveScheme.isProjective X
  set A := towerObj sG hpG (n - l) (universalQuotient l n X').target (n - l)
    (rank_universalQuotient l n X') le_rfl
  set hA := towerHom sG hpG (n - l) (universalQuotient l n X').target (n - l)
    (rank_universalQuotient l n X') le_rfl
  set B := towerObj X.obj.hom hpX (n - l) (freeModule n X') n (rank_freeModule n X')
    (Nat.sub_le n l)
  set hB := towerHom X.obj.hom hpX (n - l) (freeModule n X') n (rank_freeModule n X')
    (Nat.sub_le n l)
  let ι : SmoothProjectiveScheme.mk X.obj.hom inferInstance hpX ⟶ X :=
    SmoothProjectiveScheme.homMk (𝟙 _) (Category.id_comp _)
  let ι' : X ⟶ SmoothProjectiveScheme.mk X.obj.hom inferInstance hpX :=
    SmoothProjectiveScheme.homMk (𝟙 _) (Category.id_comp _)
  have e1 : (flagTowerIso l n X' hln).hom ≫ (towerB l n X').2 ≫ X.obj.hom =
      (towerA l n X').2 ≫ (Grassmannian.schemeOver.over l n X').hom ≫ X.obj.hom := by
    rw [← Category.assoc, flagTowerIso_hom_comp]
    exact Category.assoc _ _ _
  have e2 : (flagTowerIso l n X' hln).inv ≫ (towerA l n X').2 ≫
      (Grassmannian.schemeOver.over l n X').hom ≫ X.obj.hom = (towerB l n X').2 ≫ X.obj.hom := by
    rw [← e1, Iso.inv_hom_id_assoc]
  let ψ : A ⟶ B := SmoothProjectiveScheme.homMk (flagTowerIso l n X' hln).hom e1
  let ψ' : B ⟶ A := SmoothProjectiveScheme.homMk (flagTowerIso l n X' hln).inv e2
  have e3 : (flagTowerIso l n X' hln).hom ≫ (towerB l n X').2 ≫ 𝟙 X' =
      ((towerA l n X').2 ≫ (productGrassmannianIso k X l n).inv) ≫
        pullback.fst X.obj.hom G.obj.hom := by
    rw [Category.comp_id, flagTowerIso_hom_comp, Category.assoc, productGrassmannianIso_inv_fst]
    rfl
  have hcomp : ψ ≫ hB ≫ ι = (hA ≫ grassmannianOverHom X l n) ≫ fst X G :=
    SmoothProjectiveScheme.hom_ext' e3
  have hu : 𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
      (hA ≫ grassmannianOverHom X l n) :=
    WeilData.PushforwardCompatible.comp_of_forall (fun _ c hY hP ↦ ⟨c, hY.nonempty.elim
        fun y ↦ ⟨hA.hom.left y⟩, relativeDimension_of_hom_of_inv _ _
          (grassmannianOverHom_inv X l n) (grassmannianOverInv_hom X l n) hP.relativeDimension⟩)
      (𝔚.cycleClass_congr _) (𝔚.pushforwardCompatible_towerHom _ _ _ _ _ _ _)
      (𝔚.pushforwardCompatible_of_inverse _ _ (grassmannianOverHom_inv X l n)
        (grassmannianOverInv_hom X l n))
  have huv : 𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing
      ((hA ≫ grassmannianOverHom X l n) ≫ fst X G) := by
    rw [← hcomp]
    have hBX : 𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing (hB ≫ ι) :=
      WeilData.PushforwardCompatible.comp_of_forall (fun _ c hY hX ↦ ⟨c, hY.nonempty.elim
          fun y ↦ ⟨hB.hom.left y⟩, hX.relativeDimension⟩)
        (𝔚.cycleClass_congr _) (𝔚.pushforwardCompatible_towerHom _ _ _ _ _ _ _)
        (𝔚.pushforwardCompatible_of_inverse ι ι'
          (SmoothProjectiveScheme.hom_ext' (Category.id_comp _))
          (SmoothProjectiveScheme.hom_ext' (Category.id_comp _)))
    refine WeilData.PushforwardCompatible.comp_of_forall (fun _ c hY hX ↦ ?_)
      (𝔚.cycleClass_congr _) (𝔚.pushforwardCompatible_of_inverse ψ ψ'
        (SmoothProjectiveScheme.hom_ext' (Iso.hom_inv_id _))
        (SmoothProjectiveScheme.hom_ext' (Iso.inv_hom_id _))) hBX
    obtain ⟨e, he⟩ := exists_relativeDimension_towerObj X.obj.hom hpX (n - l) (freeModule n X') n
      (rank_freeModule n X') (Nat.sub_le n l) hX.relativeDimension
    exact ⟨e, hY.nonempty.elim fun y ↦ ⟨ψ.hom.left y⟩, he⟩
  refine WeilData.PushforwardCompatible.of_comp (fun d c hP hX ↦ ?_) hu huv
  have hGX : RelativeDimension sG d :=
    relativeDimension_of_hom_of_inv _ _ (grassmannianOverHom_inv X l n)
      (grassmannianOverInv_hom X l n) hP.relativeDimension
  obtain ⟨e, he⟩ := exists_relativeDimension_towerObj sG hpG (n - l)
    (universalQuotient l n X').target (n - l) (rank_universalQuotient l n X') le_rfl hGX
  have hP' : LocallyOfFiniteType (prod X G).obj.hom := inferInstance
  have hA' : LocallyOfFiniteType A.obj.hom := inferInstance
  exact ⟨e, he, fun p q h ↦ equidimensionalPushforward_surjective _ he hP.relativeDimension p q h
    (@properChowPushforward_towerA_productGrassmannian_surjective k _ X l n (fieldChowSituation k)
      (prod X G).obj.hom hP' A.obj.hom hA' (Over.w (hA ≫ grassmannianOverHom X l n).hom) _)⟩

end WeilChernData

end Stacks.WeilCohomology

end
