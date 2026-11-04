module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Restriction

/-! # Restrictions along a 1-morphism of categories over a base

Let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over `𝒞`, that is a functor with
`F ⋙ q = p` for structure functors `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞`. A restriction of an
object of `𝒳` along a morphism of `𝒴` can then be read in two ways: as an `F`-image in
`𝒴`, and as a restriction over the base `𝒞` for the composite `p = F ⋙ q`. This file
provides both readings and shows that they agree on canonical comparisons.

## Main results

* `CategoryTheory.Functor.Restriction.map`: the `F`-image of an `F`-restriction.
* `CategoryTheory.Functor.Restriction.ofCompEq`: an `F`-restriction along a
  `q`-strongly cartesian morphism, read as a `p`-restriction over `𝒞`.
* `CategoryTheory.Functor.Restriction.compTo_ofCompEq`: the two readings have the same
  canonical comparisons.
* `CategoryTheory.Functor.isHomLift_of_base_eq`: a lifting statement transports along
  equalities of the two base objects.
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- For `F : 𝒳 ⥤ 𝒴` with `F ⋙ q = p`, a morphism of `𝒳` lying over `k : V ⟶ U` for `F`
lies over `q.map k` for `p`. -/
theorem isHomLift_base_of_comp_eq
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF₁ : F ⋙ q = p)
    {a b : 𝒳} {V U : 𝒴} (k : V ⟶ U) (φ : a ⟶ b)
    (hk : F.IsHomLift k φ) :
    p.IsHomLift (q.map k) φ := by
  subst hF₁
  show (F ⋙ q).IsHomLift (q.map k) φ
  have hda : F.obj a = V := CategoryTheory.IsHomLift.domain_eq F k φ
  have hdb : F.obj b = U := CategoryTheory.IsHomLift.codomain_eq F k φ
  refine CategoryTheory.IsHomLift.of_commsq (F ⋙ q) (q.map k) φ
    (show (F ⋙ q).obj a = q.obj V from congrArg q.obj hda)
    (show (F ⋙ q).obj b = q.obj U from congrArg q.obj hdb) ?_
  have hfac := CategoryTheory.IsHomLift.fac F k φ
  have hq2 := congrArg q.map hfac
  simp only [q.map_comp, eqToHom_map] at hq2
  simp [hq2]

/-- Transport a lifting statement along equalities of the base objects: if `φ` lies over `r`
and `r` is the conjugate of `r'` by those equalities, then `φ` lies over `r'`. -/
theorem isHomLift_of_base_eq {p : 𝒳 ⥤ 𝒞} {U V U' V' : 𝒞} {za zb : 𝒳} (r : U ⟶ V)
    (φ : za ⟶ zb) (hφ : p.IsHomLift r φ) (r' : U' ⟶ V') (hU : U = U') (hV : V = V')
    (hr : eqToHom hU ≫ r' ≫ eqToHom hV.symm = r) : p.IsHomLift r' φ := by
  subst hU hV
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hr
  subst hr
  exact hφ

/-- For `F : 𝒳 ⥤ 𝒴` with `F ⋙ q = p`, a morphism of the fibre of `F` over `Wv` is a
morphism of the fibre of `p` over `q.obj Wv`. -/
theorem FibreHom.ofCompEq {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (hF₁ : F ⋙ q = p)
    {Wv : 𝒴} {za zb : 𝒳} (haF : F.obj za = Wv) (hbF : F.obj zb = Wv)
    (hap : p.obj za = q.obj Wv) (hbp : p.obj zb = q.obj Wv) (m : za ⟶ zb)
    (hm : FibreHom F za zb haF hbF m) : FibreHom p za zb hap hbp m := by
  have : F.IsHomLift (eqToHom haF ≫ eqToHom hbF.symm) m := hm
  have hFmap0 : F.map m = eqToHom (haF.trans hbF.symm) := by
    have hfac := CategoryTheory.IsHomLift.fac F (eqToHom haF ≫ eqToHom hbF.symm) m
    simp only [eqToHom_trans] at hfac
    have hfac2 := hfac.symm
    rw [← Category.assoc, comp_eqToHom_iff, eqToHom_comp_iff] at hfac2
    simpa [eqToHom_trans] using hfac2
  refine CategoryTheory.IsHomLift.of_commsq p _ m rfl rfl ?_
  rw [Functor.congr_hom hF₁.symm m]
  simp [Functor.comp_map, hFmap0, eqToHom_map, eqToHom_trans,
    eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The `F`-image of a restriction of `x` along `g : V ⟶ U` in `𝒴` is a restriction of
`F.obj x` along `q.map g` in `𝒞`, when `q` is fibred in groupoids, with underlying object
`F.obj r.pt` and cartesian arrow `F.map r.hom`. -/
noncomputable def Restriction.map
    (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hqF : q.IsFiberedInGroupoids)
    {V U : 𝒴} (g : V ⟶ U) (x : 𝒳) (hx : F.obj x = U)
    (r : Restriction F g x hx) :
    Restriction q (q.map g) (F.obj x) (by rw [hx]) := by
  have hhpt : q.obj (F.obj r.pt) = q.obj V := congrArg q.obj r.hpt
  have hhx : q.obj (F.obj x) = q.obj U := congrArg q.obj hx
  have hlift_main : q.IsHomLift (eqToHom hhpt ≫ q.map g ≫ eqToHom hhx.symm) (F.map r.hom) := by
    refine CategoryTheory.IsHomLift.of_commsq q _ _ rfl rfl ?_
    have hfac := CategoryTheory.IsHomLift.fac F (eqToHom r.hpt ≫ g ≫ eqToHom hx.symm) r.hom
    have := congrArg q.map hfac
    simp only [q.map_comp, eqToHom_map] at this ⊢
    simp [this]
  refine
    { pt := F.obj r.pt
      hpt := hhpt
      hom := F.map r.hom
      isHomLift := hlift_main
      isCart := ?_ }
  · have hmap : q.map (F.map r.hom) = eqToHom hhpt ≫ q.map g ≫ eqToHom hhx.symm := by
      simpa using (CategoryTheory.IsHomLift.fac q
        (eqToHom hhpt ≫ q.map g ≫ eqToHom hhx.symm) (F.map r.hom)).symm
    exact hmap ▸ hqF.isStronglyCartesian (F.map r.hom)

/-- For `p = F ⋙ q`, a restriction `r` of `x` along a `q`-strongly cartesian `g : V ⟶ U` in
`𝒴` is a restriction of `x` along `q.map g` in `𝒞` for the composite structure functor, with the
same underlying object `r.pt` and the same cartesian arrow `r.hom`. -/
@[implicit_reducible]
noncomputable def Restriction.ofCompEq
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF₁ : F ⋙ q = p)
    {V U : 𝒴} (g : V ⟶ U) (hgcart : q.IsStronglyCartesian (q.map g) g)
    (x : 𝒳) (hx : F.obj x = U) (r : Restriction F g x hx) :
    Restriction p (q.map g) x (by rw [← hF₁]; exact congrArg q.obj hx) := by
  refine
    { pt := r.pt
      hpt := by rw [← hF₁]; exact congrArg q.obj r.hpt
      hom := r.hom
      isHomLift := ?_
      isCart := ?_ }
  · subst hF₁
    show (F ⋙ q).IsHomLift _ r.hom
    refine CategoryTheory.IsHomLift.of_commsq (F ⋙ q) _ _ rfl rfl ?_
    have hfac := CategoryTheory.IsHomLift.fac F (eqToHom r.hpt ≫ g ≫ eqToHom hx.symm) r.hom
    have hq2 := congrArg q.map hfac
    simp only [Functor.comp_map, q.map_comp, eqToHom_map] at hq2 ⊢
    simp [hq2]
  · subst hF₁
    obtain ⟨rpt, rhpt, rhom, rhl, rcart⟩ := r
    subst rhpt
    subst hx
    have hgF : F.map rhom = g := by
      have := CategoryTheory.IsHomLift.fac F (eqToHom (rfl : F.obj rpt = F.obj rpt) ≫ g ≫
        eqToHom (rfl : F.obj x = F.obj x).symm) rhom
      simpa using this.symm
    have rcart' : F.IsStronglyCartesian g rhom := by
      have heq : (eqToHom (rfl : F.obj rpt = F.obj rpt) ≫ g ≫
        eqToHom (rfl : F.obj x = F.obj x).symm) = g := by simp
      rwa [heq] at rcart
    have hbase : (F ⋙ q).IsHomLift (q.map g) rhom := by
      refine CategoryTheory.IsHomLift.of_commsq (F ⋙ q) (q.map g) rhom rfl rfl ?_
      simp [Functor.comp_map, hgF]
    refine ⟨@fun a' g' φ' hlift => ?_⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hlift
    have hFφ' : q.IsHomLift (g' ≫ q.map g) (F.map φ') := by
      refine CategoryTheory.IsHomLift.of_commsq q (g' ≫ q.map g) (F.map φ') rfl rfl ?_
      have := CategoryTheory.IsHomLift.fac (F ⋙ q) (g' ≫ q.map g) φ'
      simpa [Functor.comp_map] using this.symm
    obtain ⟨ψ, ⟨hψ_lift, hψ_fac⟩, hψ_uniq⟩ :=
      hgcart.universal_property' (a' := F.obj a') g' (F.map φ')
    have hφ'_lift : F.IsHomLift (ψ ≫ g) φ' := by
      rw [hψ_fac]; exact CategoryTheory.IsHomLift.map F φ'
    obtain ⟨χ, ⟨hχ_lift, hχ_fac⟩, hχ_uniq⟩ :=
      rcart'.universal_property' (a' := a') ψ φ'
    refine ⟨χ, ⟨?_, hχ_fac⟩, ?_⟩
    · refine CategoryTheory.IsHomLift.of_commsq (F ⋙ q) g' χ rfl rfl ?_
      have hFχ : F.map χ = ψ := by
        have := CategoryTheory.IsHomLift.fac F ψ χ; simpa using this.symm
      have hqψ : q.map ψ = g' := by
        have := CategoryTheory.IsHomLift.fac q g' ψ; simpa using this.symm
      simp [Functor.comp_map, hFχ, hqψ]
    · rintro χ' ⟨hχ'_lift, hχ'_fac⟩
      have hqFχ' : q.IsHomLift g' (F.map χ') := by
        refine CategoryTheory.IsHomLift.of_commsq q g' (F.map χ') rfl rfl ?_
        have := CategoryTheory.IsHomLift.fac (F ⋙ q) g' χ'
        simpa [Functor.comp_map] using this.symm
      have hFχ'_fac : F.map χ' ≫ g = F.map φ' := by
        have h1 : F.map χ' ≫ F.map rhom = F.map φ' := by
          rw [← F.map_comp, hχ'_fac]
        rwa [hgF] at h1
      have hFχ'_eq : F.map χ' = ψ := hψ_uniq (F.map χ') ⟨hqFχ', hFχ'_fac⟩
      have hχ'_F : F.IsHomLift ψ χ' := by rw [← hFχ'_eq]; exact CategoryTheory.IsHomLift.map F χ'
      exact hχ_uniq χ' ⟨hχ'_F, hχ'_fac⟩

/-- The canonical comparison of two restrictions read for the composite structure
functor `p = F ⋙ q` is the canonical comparison of the two restrictions for `F`. -/
theorem Restriction.compTo_ofCompEq
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (hF₁ : F ⋙ q = p)
    {W V U : 𝒴} (g : W ⟶ V) (fbase : V ⟶ U) {hbase : W ⟶ U} (hh : hbase = g ≫ fbase)
    (hfcart : q.IsStronglyCartesian (q.map fbase) fbase)
    (hhcart : q.IsStronglyCartesian (q.map hbase) hbase)
    (x : 𝒳) (hx : F.obj x = U)
    (xr : Restriction F fbase x hx) (xrW : Restriction F hbase x hx) :
    Restriction.compTo p (q.map g) (q.map fbase) (by rw [hh, q.map_comp])
        (Restriction.ofCompEq p q F hF₁ fbase hfcart x hx xr)
        (Restriction.ofCompEq p q F hF₁ hbase hhcart x hx xrW)
      = Restriction.compTo F g fbase hh xr xrW := by
  subst hF₁
  set pxr := Restriction.ofCompEq (F ⋙ q) q F rfl fbase hfcart x hx xr
  set pxrW := Restriction.ofCompEq (F ⋙ q) q F rfl hbase hhcart x hx xrW
  have hxp : (F ⋙ q).obj x = q.obj U := congrArg q.obj hx
  have hcart2 : (F ⋙ q).IsStronglyCartesian
      (eqToHom pxr.hpt ≫ q.map fbase ≫ eqToHom hxp.symm) pxr.hom := pxr.isCart
  set bp := eqToHom pxrW.hpt ≫ q.map g ≫ eqToHom pxr.hpt.symm with hbp
  have hlift_comp : (F ⋙ q).IsHomLift
      (bp ≫ eqToHom pxr.hpt ≫ q.map fbase ≫ eqToHom hxp.symm) pxrW.hom := by
    have hbpbc : (bp ≫ eqToHom pxr.hpt ≫ q.map fbase ≫ eqToHom hxp.symm)
        = eqToHom pxrW.hpt ≫ (q.map g ≫ q.map fbase) ≫ eqToHom hxp.symm := by
      rw [hbp]; simp [Category.assoc]
    rw [hbpbc, ← q.map_comp, ← hh]; exact pxrW.isHomLift
  obtain ⟨ψ, ⟨hψ_lift, hψ_fac⟩, hψ_uniq⟩ :=
    hcart2.universal_property' (φ := pxr.hom) bp pxrW.hom
  have hmp_fac : Restriction.compTo (F ⋙ q) (q.map g) (q.map fbase)
      (by rw [hh, q.map_comp]) pxr pxrW ≫ pxr.hom = pxrW.hom :=
    Restriction.compTo_hom (F ⋙ q) (q.map g) (q.map fbase) (by rw [hh, q.map_comp]) pxr pxrW
  have hmF_fac : Restriction.compTo F g fbase hh xr xrW ≫ pxr.hom = pxrW.hom :=
    Restriction.compTo_hom F g fbase hh xr xrW
  have hmF_liftF : F.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo F g fbase hh xr xrW) := by
    have hpre : F.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ fbase ≫ eqToHom hx.symm)) xrW.hom := by
      have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
          (eqToHom xr.hpt ≫ fbase ≫ eqToHom hx.symm)
          = eqToHom xrW.hpt ≫ hbase ≫ eqToHom hx.symm := by subst hh; simp
      rw [e]; exact xrW.isHomLift
    exact CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift F
      (eqToHom xr.hpt ≫ fbase ≫ eqToHom hx.symm) xr.hom rfl xrW.hom
  have hmF_liftp : (F ⋙ q).IsHomLift
      (q.map (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm))
      (Restriction.compTo F g fbase hh xr xrW) :=
    isHomLift_base_of_comp_eq (F ⋙ q) q F rfl _ _ hmF_liftF
  have hbase_eq : q.map (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) = bp := by
    rw [hbp]; simp [q.map_comp, eqToHom_map]
  rw [hbase_eq] at hmF_liftp
  have hmp_liftp : (F ⋙ q).IsHomLift bp
      (Restriction.compTo (F ⋙ q) (q.map g) (q.map fbase) (by rw [hh, q.map_comp]) pxr pxrW) :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift (F ⋙ q) _ pxr.hom _ pxrW.hom
  rw [hψ_uniq _ ⟨hmp_liftp, hmp_fac⟩, hψ_uniq _ ⟨hmF_liftp, hmF_fac⟩]

end CategoryTheory.Functor
