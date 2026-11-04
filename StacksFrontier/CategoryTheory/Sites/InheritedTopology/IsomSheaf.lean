module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.IsomSeparated
import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Pullback
import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Transport

/-! # The `Isom` sheaf condition for an inherited topology

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be stacks in groupoids and let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over `𝒞`. This file proves that the `Isom`
presheaves of `F` over `𝒴` are sheaves for the topology inherited from `(𝒞, J)`, which
is condition (2) of Stacks 06NX.

The family of local fibre isomorphisms is glued over the base `𝒞`, where `p` is a stack;
separatedness of the `Isom` sheaf of `q` then identifies the `𝒴`-base of the glued
morphism as an identity, which is what makes it a fibre morphism for `F`.

## Main results

* `CategoryTheory.Functor.fibre_base_id_of_cover`: separatedness of the `Isom` sheaf
  of `q`.
* `CategoryTheory.Functor.isom_isSheaf_of_isFiberedInGroupoids`: condition (2) of
  Stacks 06NX.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- A morphism of the fibre of `p` over `U` maps under `p` to an `eqToHom`. -/
private theorem FibreHom.map_eq_eqToHom {p : 𝒳 ⥤ 𝒞} {U : 𝒞} {a b : 𝒳} {ha : p.obj a = U}
    {hb : p.obj b = U} {φ : a ⟶ b} (hφ : FibreHom p a b ha hb φ) :
    p.map φ = eqToHom (ha.trans hb.symm) := by
  have : p.IsHomLift (eqToHom ha ≫ eqToHom hb.symm) φ := hφ
  simpa using CategoryTheory.IsHomLift.fac' p (eqToHom ha ≫ eqToHom hb.symm) φ

private theorem Restriction.compTo_ofCompEq_of_eq
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF₁ : F ⋙ q = p)
    {W V U : 𝒴} (g : W ⟶ V) (fbase : V ⟶ U) {hbase : W ⟶ U} (hh : hbase = g ≫ fbase)
    {h' : q.obj W ⟶ q.obj U} (e : q.map hbase = h') (hh' : h' = q.map g ≫ q.map fbase)
    (hfcart : q.IsStronglyCartesian (q.map fbase) fbase)
    (hhcart : q.IsStronglyCartesian (q.map hbase) hbase)
    (x : 𝒳) (hx : F.obj x = U)
    (xr : Restriction F fbase x hx) (xrW : Restriction F hbase x hx) :
    Restriction.compTo p (q.map g) (q.map fbase) hh'
        (Restriction.ofCompEq p q F hF₁ fbase hfcart x hx xr)
        { pt := xrW.pt
          hpt := (Restriction.ofCompEq p q F hF₁ hbase hhcart x hx xrW).hpt
          hom := xrW.hom
          isHomLift := by
            rw [← e]; exact (Restriction.ofCompEq p q F hF₁ hbase hhcart x hx xrW).isHomLift
          isCart := by
            rw [← e]; exact (Restriction.ofCompEq p q F hF₁ hbase hhcart x hx xrW).isCart }
      = Restriction.compTo F g fbase hh xr xrW := by
  subst e
  exact Restriction.compTo_ofCompEq p q F hF₁ g fbase hh hfcart hhcart x hx xr xrW

/-- The `p`-half of `isom_isSheaf_glue_lift`: since `p = F ⋙ q` is a stack in groupoids, a
compatible family of local `F`-fibre isomorphisms glues to a unique `p`-fibre isomorphism. -/
private theorem existsUnique_glue_fibreHom_comp
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hp : IsStackInGroupoids.{w} p J) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} (x y : 𝒳) (hx : F.obj x = U) (hy : F.obj y = U)
    {I : Type w} (V : I → 𝒴) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    (Vij : I → I → 𝒴)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction F (f i) x hx) (yr : ∀ i, Restriction F (f i) y hy)
    (xrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ_fib : ∀ i, FibreHom F (xr i).pt (yr i).pt (xr i).hpt (yr i).hpt (φ i))
    (hφ_iso : ∀ i, IsIso (φ i))
    (hφ_compat : ∀ i j, ∃ (γ : (xrij i j).pt ⟶ (yrij i j).pt),
      FibreHom F (xrij i j).pt (yrij i j).pt (xrij i j).hpt (yrij i j).hpt γ ∧
      IsRestrictionOf F (pr₁ i j) rfl rfl (xr i) (yr i) (xrij i j) (yrij i j) (φ i) γ ∧
      IsRestrictionOf F (pr₂ i j) (hVij i j).w (hVij i j).w (xr j) (yr j)
        (xrij i j) (yrij i j) (φ j) γ) :
    ∃! g : x ⟶ y,
      FibreHom p x y (show p.obj x = q.obj U by rw [← hF₁]; exact congrArg q.obj hx)
        (show p.obj y = q.obj U by rw [← hF₁]; exact congrArg q.obj hy) g ∧ IsIso g ∧
        ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom := by
  have hxp : p.obj x = q.obj U := by rw [← hF₁]; exact congrArg q.obj hx
  have hyp : p.obj y = q.obj U := by rw [← hF₁]; exact congrArg q.obj hy
  have hf_cart : ∀ i, q.IsStronglyCartesian (q.map (f i)) (f i) :=
    fun i => hq.isFiberedInGroupoids.isStronglyCartesian (f i)
  have hcomp_cart : ∀ i j, q.IsStronglyCartesian (q.map (pr₁ i j ≫ f i)) (pr₁ i j ≫ f i) :=
    fun i j => hq.isFiberedInGroupoids.isStronglyCartesian (pr₁ i j ≫ f i)
  set pr₁' : ∀ i j, q.obj (Vij i j) ⟶ q.obj (V i) := fun i j => q.map (pr₁ i j)
  set pr₂' : ∀ i j, q.obj (Vij i j) ⟶ q.obj (V j) := fun i j => q.map (pr₂ i j)
  have hVijC : ∀ i j, IsPullback (pr₁' i j) (pr₂' i j) (q.map (f i)) (q.map (f j)) :=
    fun i j => hq.isFiberedInGroupoids.isPullback_map (f i) (f j) (pr₁ i j) (pr₂ i j) (hVij i j)
  have hrebase : ∀ i j, q.map (pr₁ i j ≫ f i) = pr₁' i j ≫ q.map (f i) :=
    fun i j => q.map_comp _ _
  set pxr : ∀ i, Restriction p (q.map (f i)) x hxp := fun i =>
    Restriction.ofCompEq p q F hF₁ (f i) (hf_cart i) x hx (xr i)
  set pyr : ∀ i, Restriction p (q.map (f i)) y hyp := fun i =>
    Restriction.ofCompEq p q F hF₁ (f i) (hf_cart i) y hy (yr i)
  set pxrij : ∀ i j, Restriction p (pr₁' i j ≫ q.map (f i)) x hxp := fun i j =>
    let r := Restriction.ofCompEq p q F hF₁ _ (hcomp_cart i j) x hx (xrij i j)
    ⟨r.pt, r.hpt, r.hom, by rw [← hrebase i j]; exact r.isHomLift,
      by rw [← hrebase i j]; exact r.isCart⟩
  set pyrij : ∀ i j, Restriction p (pr₁' i j ≫ q.map (f i)) y hyp := fun i j =>
    let r := Restriction.ofCompEq p q F hF₁ _ (hcomp_cart i j) y hy (yrij i j)
    ⟨r.pt, r.hpt, r.hom, by rw [← hrebase i j]; exact r.isHomLift,
      by rw [← hrebase i j]; exact r.isCart⟩
  have hctx₁ : ∀ i j, Restriction.compTo p (pr₁' i j) (q.map (f i)) rfl (pxr i) (pxrij i j)
      = Restriction.compTo F (pr₁ i j) (f i) rfl (xr i) (xrij i j) := fun i j =>
    Restriction.compTo_ofCompEq_of_eq p q F hF₁ (pr₁ i j) (f i) rfl (hrebase i j) rfl
      (hf_cart i) (hcomp_cart i j) x hx (xr i) (xrij i j)
  have hcty₁ : ∀ i j, Restriction.compTo p (pr₁' i j) (q.map (f i)) rfl (pyr i) (pyrij i j)
      = Restriction.compTo F (pr₁ i j) (f i) rfl (yr i) (yrij i j) := fun i j =>
    Restriction.compTo_ofCompEq_of_eq p q F hF₁ (pr₁ i j) (f i) rfl (hrebase i j) rfl
      (hf_cart i) (hcomp_cart i j) y hy (yr i) (yrij i j)
  have hctx₂ : ∀ i j,
      Restriction.compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) (pxrij i j)
        = Restriction.compTo F (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j) := fun i j =>
    Restriction.compTo_ofCompEq_of_eq p q F hF₁ (pr₂ i j) (f j) (hVij i j).w (hrebase i j)
      (hVijC i j).w (hf_cart j) (hcomp_cart i j) x hx (xr j) (xrij i j)
  have hcty₂ : ∀ i j,
      Restriction.compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pyr j) (pyrij i j)
        = Restriction.compTo F (pr₂ i j) (f j) (hVij i j).w (yr j) (yrij i j) := fun i j =>
    Restriction.compTo_ofCompEq_of_eq p q F hF₁ (pr₂ i j) (f j) (hVij i j).w (hrebase i j)
      (hVijC i j).w (hf_cart j) (hcomp_cart i j) y hy (yr j) (yrij i j)
  refine hp.isom_isSheaf x y hxp hyp _ _ ((hJ𝒴 V f hf_cart).mp hf) _ pr₁' pr₂' hVijC
    pxr pyr pxrij pyrij φ
    (fun i => FibreHom.ofCompEq hF₁ (xr i).hpt (yr i).hpt _ _ (φ i) (hφ_fib i)) hφ_iso
    fun i j => ?_
  obtain ⟨γ, hγ_fib, hγ₁, hγ₂⟩ := hφ_compat i j
  refine ⟨γ, FibreHom.ofCompEq hF₁ (xrij i j).hpt (yrij i j).hpt _ _ γ hγ_fib, ?_, ?_⟩
  · rwa [IsRestrictionOf, hcty₁, hctx₁]
  · rwa [IsRestrictionOf, hcty₂, hctx₂]

/-- A `p`-fibre morphism `g : x ⟶ y`, for `p = F ⋙ q`, restricting on a `J𝒴`-covering family
to local `F`-fibre morphisms is an `F`-fibre morphism: its `𝒴`-base is the identity by
`fibre_base_id_of_cover`. -/
private theorem fibreHom_of_fibreHom_comp_of_cover
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p) (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} {x y : 𝒳} (hx : F.obj x = U) (hy : F.obj y = U)
    (hxp : p.obj x = q.obj U) (hyp : p.obj y = q.obj U)
    {I : Type w} {V : I → 𝒴} {f : ∀ i, V i ⟶ U} (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    {Vij : I → I → 𝒴} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    {xr : ∀ i, Restriction F (f i) x hx} {yr : ∀ i, Restriction F (f i) y hy}
    {φ : ∀ i, (xr i).pt ⟶ (yr i).pt}
    (hφ_fib : ∀ i, FibreHom F (xr i).pt (yr i).pt (xr i).hpt (yr i).hpt (φ i))
    {g : x ⟶ y} (hg : FibreHom p x y hxp hyp g)
    (hg_restr : ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom) :
    FibreHom F x y hx hy g := by
  set b : U ⟶ U := eqToHom hx.symm ≫ F.map g ≫ eqToHom hy with hb
  have hFg : F.map g = eqToHom hx ≫ b ≫ eqToHom hy.symm := by simp [hb]
  have hb_lift : q.IsHomLift (𝟙 (q.obj U)) b := by
    have hqFg : q.map (F.map g) = eqToHom (congrArg q.obj (hx.trans hy.symm)) := by
      rw [← Functor.comp_map, Functor.congr_hom hF₁ g, FibreHom.map_eq_eqToHom hg]
      simp
    refine CategoryTheory.IsHomLift.of_commsq q _ b rfl rfl ?_
    simp [hb, hqFg, eqToHom_map]
  have hbf : ∀ i, f i ≫ b = f i := by
    intro i
    have h := congrArg F.map (hg_restr i)
    rw [F.map_comp, F.map_comp, hFg, FibreHom.map_eq_eqToHom (hφ_fib i),
      CategoryTheory.IsHomLift.fac' F (eqToHom (xr i).hpt ≫ f i ≫ eqToHom hx.symm) (xr i).hom,
      CategoryTheory.IsHomLift.fac' F (eqToHom (yr i).hpt ≫ f i ≫ eqToHom hy.symm) (yr i).hom]
      at h
    exact (cancel_epi (eqToHom (xr i).hpt)).1 (by simpa using h =≫ eqToHom hy)
  have hbid : b = 𝟙 U := fibre_base_id_of_cover J J𝒴 q hq hJ𝒴 V f hf Vij pr₁ pr₂
    (fun i j => hq.isFiberedInGroupoids.isPullback_map _ _ _ _ (hVij i j)) b hb_lift hbf
  refine CategoryTheory.IsHomLift.of_commsq F _ g rfl rfl ?_
  rw [hFg, hbid]
  simp

/-- Gluing for the `Isom` presheaf of `F` over `𝒴`: a family of local fibre
isomorphisms `φ i : x|_{V i} ⟶ y|_{V i}` in `𝒳`, agreeing on the double overlaps of a
`J𝒴`-covering family, glues to a unique fibre isomorphism `g : x ⟶ y` over `U`.

The family is glued over the base `𝒞`, using that `p = F ⋙ q` is a stack in groupoids;
that `q` is a stack in groupoids is then used, through `fibre_base_id_of_cover`, to
identify the `𝒴`-base of `F.map g` as `𝟙 U`, which upgrades `g` from a fibre morphism
for `p` to a fibre morphism for `F`. -/
theorem isom_isSheaf_glue_lift
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hp : IsStackInGroupoids.{w} p J) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} (x y : 𝒳) (hx : F.obj x = U) (hy : F.obj y = U)
    {I : Type w} (V : I → 𝒴) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    (Vij : I → I → 𝒴)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction F (f i) x hx) (yr : ∀ i, Restriction F (f i) y hy)
    (xrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ_fib : ∀ i, FibreHom F (xr i).pt (yr i).pt (xr i).hpt (yr i).hpt (φ i))
    (hφ_iso : ∀ i, IsIso (φ i))
    (hφ_compat : ∀ i j, ∃ (γ : (xrij i j).pt ⟶ (yrij i j).pt),
      FibreHom F (xrij i j).pt (yrij i j).pt (xrij i j).hpt (yrij i j).hpt γ ∧
      IsRestrictionOf F (pr₁ i j) rfl rfl (xr i) (yr i) (xrij i j) (yrij i j) (φ i) γ ∧
      IsRestrictionOf F (pr₂ i j) (hVij i j).w (hVij i j).w (xr j) (yr j)
        (xrij i j) (yrij i j) (φ j) γ) :
    ∃! g : x ⟶ y,
      FibreHom F x y hx hy g ∧ IsIso g ∧
        ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom := by
  obtain ⟨g, ⟨hg, hg_iso, hg_restr⟩, hg_uniq⟩ := existsUnique_glue_fibreHom_comp J J𝒴 p q F hp hq
    hF₁ hJ𝒴 x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ_fib hφ_iso hφ_compat
  exact ⟨g, ⟨fibreHom_of_fibreHom_comp_of_cover J J𝒴 p q F hq hF₁ hJ𝒴 hx hy _ _ hf hVij hφ_fib
      hg hg_restr, hg_iso, hg_restr⟩,
    fun g' ⟨hg', hg'_iso, hg'_restr⟩ =>
      hg_uniq g' ⟨FibreHom.ofCompEq hF₁ hx hy _ _ g' hg', hg'_iso, hg'_restr⟩⟩

/-- **Condition (2) of Stacks 06NX.** For stacks in groupoids `p` and `q` over a site
`(𝒞, J)` and a 1-morphism `F` over `𝒞`, the `Isom` presheaves of `F` over `𝒴` are
sheaves for the topology inherited from `(𝒞, J)`. -/
theorem isom_isSheaf_of_isFiberedInGroupoids
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hp : IsStackInGroupoids.{w} p J) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} (x y : 𝒳) (hx : F.obj x = U) (hy : F.obj y = U)
    {I : Type w} (V : I → 𝒴) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    (Vij : I → I → 𝒴)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction F (f i) x hx) (yr : ∀ i, Restriction F (f i) y hy)
    (xrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction F (pr₁ i j ≫ f i) y hy) :
    IsomIsSheafFor F x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij :=
  isom_isSheaf_glue_lift J J𝒴 p q F hp hq hF₁ hJ𝒴 x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij

end CategoryTheory.Functor
