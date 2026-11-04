module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Pasting the identifications `RΓ(X, E ⊗ Ri_*W) ≅ RΓ(Xₙ, Li^*E ⊗ W)` along a composite

Abstract bookkeeping for the compatibility of the identification
`ψ : RΓ(X, E ⊗ Rq_* W) ⟶ RΓ(Y, Lq^*E ⊗ W)` with a factorization `q = t ≫ i'`. The categories,
functors and transformations are arbitrary; the geometric input is supplied as hypotheses:

* `ha`: the comparison `(q_*F)[0] ⟶ Rq_*(F[0])` is the composite of the ones of `i'` and `t`,
* `hb`: the projection formula of `q` is the one of `i'` followed by `Ri'_*` of the one of `t`,
* `hc`: the identification of `RΓ(-, Rq_* -)` is the one of `i'` followed by the one of `t`,
* `hn`: the projection formula of `i'` is natural in its second argument,
* `hB`: the comparison of `i'` is natural.

## Main results

* `CategoryTheory.tensorSectionsPasting`.
-/

@[expose] public section

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒳 : Type u₁} {𝒳₁ : Type u₂} {𝒳₀ : Type u₃} {𝒜 : Type u₄} {𝒜₁ : Type u₅} {𝒜₀ : Type u₆}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒳₁] [Category.{v₃} 𝒳₀] [Category.{v₄} 𝒜] [Category.{v₅} 𝒜₁]
  [Category.{v₆} 𝒜₀]

/-- **Pasting the tensor-sections identifications along a composite.** With `ψ_q` the composite of
the comparison `σ_q`, the projection formula `P_q` and the identification `π_q`, the identification
of `q` after the map `m = aI ≫ cI` is the identification of `i'` at the source of `a`, followed by
the one of `t` (comparison `a ≫ σ_t`, projection formula `P_t`, identification `π_t`), the
composition isomorphism `spc : Li' ⋙ Lt ⟶ Li` and the comparison `cρ`. -/
theorem tensorSectionsPasting
    (TX : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (T1 : 𝒳₁ ⥤ 𝒳₁ ⥤ 𝒳₁) (T0 : 𝒳₀ ⥤ 𝒳₀ ⥤ 𝒳₀)
    (Li' : 𝒳 ⥤ 𝒳₁) (Lt : 𝒳₁ ⥤ 𝒳₀) (Li : 𝒳 ⥤ 𝒳₀) (Ri' : 𝒳₁ ⥤ 𝒳) (Rt : 𝒳₀ ⥤ 𝒳₁) (Ri : 𝒳₀ ⥤ 𝒳)
    (GA : 𝒳 ⥤ 𝒜) (G1 : 𝒳₁ ⥤ 𝒜₁) (G0 : 𝒳₀ ⥤ 𝒜₀) (res' : 𝒜₁ ⥤ 𝒜) (rest : 𝒜₀ ⥤ 𝒜₁)
    (res : 𝒜₀ ⥤ 𝒜)
    (P' : ∀ W : 𝒳₁, TX.flip.obj (Ri'.obj W) ⟶ Li' ⋙ T1.flip.obj W ⋙ Ri')
    (Pt : ∀ W : 𝒳₀, T1.flip.obj (Rt.obj W) ⟶ Lt ⋙ T0.flip.obj W ⋙ Rt)
    (Pi : ∀ W : 𝒳₀, TX.flip.obj (Ri.obj W) ⟶ Li ⋙ T0.flip.obj W ⋙ Ri)
    (π' : Ri' ⋙ GA ⟶ G1 ⋙ res') (πt : Rt ⋙ G1 ⟶ G0 ⋙ rest) (πi : Ri ⋙ GA ⟶ G0 ⋙ res)
    (cγ : Rt ⋙ Ri' ⟶ Ri) (spc : Li' ⋙ Lt ⟶ Li) (cρ : rest ⋙ res' ⟶ res)
    {W : 𝒳₀} {S0 S1 S2 : 𝒳} {S1' S2' : 𝒳₁}
    (σi : S0 ⟶ Ri.obj W) (σ' : S1 ⟶ Ri'.obj S1') (σ'' : S2 ⟶ Ri'.obj S2') (σt : S1' ⟶ Rt.obj W)
    (aI : S2 ⟶ S1) (a : S2' ⟶ S1') (cI : S1 ⟶ S0) (m : S2 ⟶ S0) (hm : m = aI ≫ cI)
    (hB : aI ≫ σ' = σ'' ≫ Ri'.map a)
    (ha : cI ≫ σi = σ' ≫ Ri'.map σt ≫ cγ.app W)
    (hb : TX.flip.map (cγ.app W) ≫ Pi W =
      P' (Rt.obj W) ≫ whiskerRight (whiskerLeft Li' (Pt W) ≫
        whiskerRight spc (T0.flip.obj W ⋙ Rt)) Ri' ≫ whiskerLeft (Li ⋙ T0.flip.obj W) cγ)
    (hc : whiskerRight cγ GA ≫ πi = whiskerLeft Rt π' ≫ whiskerRight πt res' ≫ whiskerLeft G0 cρ)
    (hn : ∀ {W₁ W₂ : 𝒳₁} (u : W₁ ⟶ W₂), TX.flip.map (Ri'.map u) ≫ P' W₂ =
      P' W₁ ≫ whiskerLeft Li' (whiskerRight (T1.flip.map u) Ri')) :
    whiskerRight (TX.flip.map m) GA ≫
        (whiskerRight (TX.flip.map σi) GA ≫ whiskerRight (Pi W) GA ≫
          whiskerLeft (Li ⋙ T0.flip.obj W) πi) =
      (whiskerRight (TX.flip.map σ'') GA ≫ whiskerRight (P' S2') GA ≫
          whiskerLeft (Li' ⋙ T1.flip.obj S2') π') ≫
        whiskerRight (whiskerLeft Li' (whiskerRight (T1.flip.map (a ≫ σt) ≫ Pt W) G1 ≫
            whiskerLeft (Lt ⋙ T0.flip.obj W) πt) ≫
          whiskerRight spc (T0.flip.obj W ⋙ G0 ⋙ rest)) res' ≫
        whiskerLeft (Li ⋙ T0.flip.obj W ⋙ G0) cρ := by
  subst hm
  ext E
  have h0 : GA.map ((TX.obj E).map aI) ≫ GA.map ((TX.obj E).map σ') =
      GA.map ((TX.obj E).map σ'') ≫ GA.map ((TX.obj E).map (Ri'.map a)) := by
    simp only [← Functor.map_comp, hB]
  have h1 : GA.map ((TX.obj E).map cI) ≫ GA.map ((TX.obj E).map σi) =
      GA.map ((TX.obj E).map σ') ≫ GA.map ((TX.obj E).map (Ri'.map σt)) ≫
        GA.map ((TX.obj E).map (cγ.app W)) := by
    simp only [← Functor.map_comp, ha]
  have h2 := congrArg GA.map (NatTrans.congr_app hb E)
  have h3 := NatTrans.congr_app hc ((T0.obj (Li.obj E)).obj W)
  have h4 : ∀ {W₁ W₂ : 𝒳₁} (u : W₁ ⟶ W₂), GA.map ((TX.obj E).map (Ri'.map u)) ≫
      GA.map ((P' W₂).app E) = GA.map ((P' W₁).app E) ≫
        GA.map (Ri'.map ((T1.obj (Li'.obj E)).map u)) := fun u => by
    have h := NatTrans.congr_app (hn u) E
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.flip_map_app,
      Functor.flip_obj_obj, Functor.comp_obj] at h
    rw [← GA.map_comp, h, GA.map_comp]
  have h5 := π'.naturality
  have h6 : ∀ {Y₁ Y₂ : 𝒳₀} (u : Y₁ ⟶ Y₂), res'.map (G1.map (Rt.map u)) ≫ res'.map (πt.app Y₂) =
      res'.map (πt.app Y₁) ≫ res'.map (rest.map (G0.map u)) := fun u => by
    simp only [← Functor.map_comp]
    exact congrArg res'.map (πt.naturality u)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.flip_map_app,
    Functor.flip_obj_obj, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc] at h2 h3 ⊢
  rw [reassoc_of% h1, reassoc_of% h0, reassoc_of% h2, h3, reassoc_of% (h4 σt),
    reassoc_of% (h4 a)]
  simp only [reassoc_of% h5, reassoc_of% h6]
  dsimp only [Functor.flip_obj_obj]
  rw [reassoc_of% (h5 ((T1.obj (Li'.obj E)).map a))]

end CategoryTheory
