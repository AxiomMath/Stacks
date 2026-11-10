module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Local uniqueness of scheme morphisms

Two morphisms of schemes over a base which induce the same map on the local rings at a point
agree on an open neighbourhood of that point, under any of four standard finiteness or
reducedness hypotheses.

## Main results

* `AlgebraicGeometry.exists_open_eq_of_stalkMap_eq` gives an open neighbourhood on which the
  two morphisms agree.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Two algebra maps out of a finite-type algebra which agree after localizing at a prime
already agree after localizing away from a single element outside that prime. -/
private lemma exists_away_eq_of_localization_eq
    {R B A L : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra R B] [Algebra R A] [Algebra A L]
    (hft : Algebra.FiniteType R B) (p : Ideal A) [p.IsPrime]
    [IsLocalization p.primeCompl L]
    (φ ψ : B →ₐ[R] A)
    (hmap : (algebraMap A L).comp φ.toRingHom =
      (algebraMap A L).comp ψ.toRingHom) :
    ∃ a : A, a ∉ p ∧
      (algebraMap A (Localization.Away a)).comp φ.toRingHom =
      (algebraMap A (Localization.Away a)).comp ψ.toRingHom := by
  classical
  obtain ⟨S, hS⟩ := hft.out
  let choice (b : B) := (IsLocalization.eq_iff_exists (M := p.primeCompl)
      (R := A) (S := L)).mp (RingHom.congr_fun hmap b)
  let d : B → A := fun b ↦ (Classical.choose (choice b)).1
  have hd1 : ∀ b ∈ S, d b ∉ p := fun b _ ↦ by
    simpa only [d, Ideal.mem_primeCompl_iff] using (Classical.choose (choice b)).property
  have hd2 : ∀ b ∈ S, d b * φ b = d b * ψ b := fun b _ ↦ by
    simpa [d] using Classical.choose_spec (choice b)
  let a : A := ∏ b ∈ S, d b
  have ha : a ∉ p := fun hp ↦ by
    obtain ⟨b, hb, hbp⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
    exact hd1 b hb hbp
  refine ⟨a, ha, RingHom.ext fun b ↦ ?_⟩
  have hgen : b ∈ Algebra.adjoin R (S : Set B) := by rw [hS]; trivial
  change algebraMap A (Localization.Away a) (φ b) =
    algebraMap A (Localization.Away a) (ψ b)
  refine Algebra.adjoin_induction (R := R) (s := (S : Set B))
    (p := fun b _ ↦ algebraMap A (Localization.Away a) (φ b) =
      algebraMap A (Localization.Away a) (ψ b)) (fun b hbS ↦ ?_) (fun r ↦ by simp)
    (fun x y _ _ hx hy ↦ by simp [hx, hy]) (fun x y _ _ hx hy ↦ by simp [hx, hy]) hgen
  have hmul : a * φ b = a * ψ b := by
    change (∏ b ∈ S, d b) * φ b = (∏ b ∈ S, d b) * ψ b
    rw [← Finset.mul_prod_erase S d hbS]
    linear_combination (∏ c ∈ S.erase b, d c) * hd2 b hbS
  exact (IsLocalization.eq_iff_exists (M := Submonoid.powers a)
    (R := A) (S := Localization.Away a)).2 ⟨⟨a, 1, by simp⟩, hmul⟩

/-- The affine case of local uniqueness: two morphisms of affine schemes over an affine base
which agree on the local ring at a point agree on a basic open neighbourhood. -/
private lemma exists_open_eq_of_stalkMap_eq_of_affine
    {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Y]
    (pX : X ⟶ S) (pY : Y ⟶ S) (f g : X ⟶ Y)
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pX)
    (x : X) (y : Y) (hfx : f x = y) (hgx : g x = y)
    (hfg : f.stalkMap x =
      Y.presheaf.stalkSpecializes
        (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes ≫ g.stalkMap x)
    [LocallyOfFiniteType pY] :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  classical
  let R := Γ(S, ⊤)
  let B := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  let : Algebra R B := pY.appTop.hom.toAlgebra
  let : Algebra R A := pX.appTop.hom.toAlgebra
  have hcomp : ∀ k : X ⟶ Y, k ≫ pY = pX →
      k.appTop.hom.comp pY.appTop.hom = pX.appTop.hom := fun k hk ↦ by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom (congrArg Scheme.Hom.appTop hk)
  let φ : B →ₐ[R] A :=
    { toRingHom := f.appTop.hom
      commutes' := RingHom.congr_fun (hcomp f hf) }
  let ψ : B →ₐ[R] A :=
    { toRingHom := g.appTop.hom
      commutes' := RingHom.congr_fun (hcomp g hg) }
  have hftRing : (pY.appTop.hom).FiniteType := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      LocallyOfFiniteType.finiteType_appLE pY (isAffineOpen_top S) (isAffineOpen_top Y)
        (by simp : (⊤ : Y.Opens) ≤ pY ⁻¹ᵁ (⊤ : S.Opens))
  have hft : Algebra.FiniteType R B := RingHom.finiteType_algebraMap.mp hftRing
  let htopX := isAffineOpen_top X
  let q := htopX.primeIdealOf ⟨x, by simp⟩
  let p := q.asIdeal
  have : p.IsPrime := q.isPrime
  let : Algebra A (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, by simp⟩
  have : IsLocalization p.primeCompl (X.presheaf.stalk x) :=
    htopX.isLocalization_stalk ⟨x, by simp⟩
  have hsec : Y.presheaf.germ ⊤ (f x) (by simp) ≫ f.stalkMap x =
      Y.presheaf.germ ⊤ (f x) (by simp) ≫
        (Y.presheaf.stalkSpecializes
          (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes ≫ g.stalkMap x) := by
    rw [hfg]
  simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.Hom.germ_stalkMap] at hsec
  have hmap : (algebraMap A (X.presheaf.stalk x)).comp φ.toRingHom =
      (algebraMap A (X.presheaf.stalk x)).comp ψ.toRingHom := by
    refine RingHom.ext fun b ↦ ?_
    have hb := congrArg (fun k ↦ k b) hsec
    simp only [CommRingCat.comp_apply] at hb
    exact hb
  obtain ⟨a, ha, hab⟩ := exists_away_eq_of_localization_eq hft p φ ψ hmap
  let V : X.Opens := X.basicOpen a
  have hxV : x ∈ V := by
    apply (Scheme.mem_basicOpen_top X a x).2
    apply (LocallyRingedSpace.notMem_prime_iff_unit_in_stalk
      X.toLocallyRingedSpace a x).mp
    change a ∉ (Spec.map (X.presheaf.germ ⊤ x (by simp))
      (IsLocalRing.closedPoint _)).asIdeal
    simpa [p, q, htopX, IsAffineOpen.primeIdealOf,
      IsAffineOpen.primeIdealOf_eq_map_closedPoint] using ha
  have hV : IsAffineOpen V := htopX.basicOpen a
  have : IsLocalization.Away a Γ(X, V) := htopX.isLocalization_basicOpen a
  let : Algebra A Γ(X, V) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let e : Localization.Away a ≃ₐ[A] Γ(X, V) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(X, V)
  let e' := e.symm.toRingEquiv.toRingHom
  let ρ : A →+* Γ(X, V) := (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
  have hρ : e'.comp ρ = algebraMap A (Localization.Away a) := RingHom.ext e.symm.commutes
  have hFG : ∀ k : X ⟶ Y, e'.comp (k.appLE ⊤ V (by simp)).hom =
      (algebraMap A (Localization.Away a)).comp k.appTop.hom := fun k ↦ by
    change e'.comp (ρ.comp k.appTop.hom) = _
    rw [← RingHom.comp_assoc, hρ]
  have hfgLE : f.appLE ⊤ V (by simp) = g.appLE ⊤ V (by simp) := by
    ext b
    exact e.symm.injective ((RingHom.congr_fun (hFG f) b).trans
      ((RingHom.congr_fun hab b).trans (RingHom.congr_fun (hFG g) b).symm))
  let f' := f.resLE ⊤ V (by simp)
  let g' := g.resLE ⊤ V (by simp)
  have hApp : ∀ k : X ⟶ Y, (k.resLE ⊤ V (by simp)).app ⊤ = (⊤ : Y.Opens).topIso.hom ≫
      k.appLE ⊤ V (by simp) ≫ V.topIso.inv := fun k ↦
    Scheme.Hom.resLE_app_top (f := k) (U := ⊤) (V := V) (e := by simp)
  have hfgApp : f'.app ⊤ = g'.app ⊤ := by
    rw [hApp f, hApp g, hfgLE]
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : Y.Opens).toScheme := isAffineOpen_top Y
  have hfgRes : f' = g' := by
    apply (cancel_mono ((⊤ : Y.Opens).toScheme.isoSpec.hom)).mp
    rw [← Scheme.isoSpec_hom_naturality f', ← Scheme.isoSpec_hom_naturality g']
    simp only [f', g', Scheme.isoSpec, asIso_hom, Scheme.Hom.app_eq_appLE]
    simpa only [Category.assoc, Scheme.Hom.appLE_eq_app] using
      congrArg (fun k ↦ (V.toScheme).toSpecΓ ≫ Spec.map k) hfgApp
  refine ⟨V, hxV, ?_⟩
  calc
    V.ι ≫ f = f' ≫ (⊤ : Y.Opens).ι := (Scheme.Hom.resLE_comp_ι f (by simp)).symm
    _ = g' ≫ (⊤ : Y.Opens).ι := by rw [hfgRes]
    _ = V.ι ≫ g := Scheme.Hom.resLE_comp_ι g (by simp)

/-- Two morphisms over a scheme which agree on the local ring at a point agree on some open
neighbourhood of that point, provided the target is locally of finite type over the base, or
the source is integral, locally Noetherian, or reduced with finitely many irreducible
components. -/
@[stacks 0BX6 "local_uniqueness", ega "I 6.5.1" "(i)"]
theorem exists_open_eq_of_stalkMap_eq
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f g : X ⟶ Y)
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pX)
    (s : S) (x : X) (y : Y) (hxs : pX x = s) (hys : pY y = s)
    (hfx : f x = y) (hgx : g x = y)
    (hfg : f.stalkMap x =
      Y.presheaf.stalkSpecializes
        (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes ≫ g.stalkMap x)
    (h : LocallyOfFiniteType pY ∨ IsIntegral X ∨ IsLocallyNoetherian X ∨
      (IsReduced X ∧ (irreducibleComponents X).Finite)) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  rcases h with _ | _ | _ | ⟨_, hX⟩
  · obtain ⟨_, ⟨Us : S.Opens, hUs, rfl⟩, hsUs, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    have hysUs : y ∈ pY ⁻¹ᵁ Us := by
      change pY y ∈ Us
      rwa [hys]
    obtain ⟨_, ⟨Uy : Y.Opens, hUy, rfl⟩, hyUy, hUyS⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hysUs (pY ⁻¹ᵁ Us).2
    let O : X.Opens := (f ⁻¹ᵁ Uy ⊓ g ⁻¹ᵁ Uy) ⊓ pX ⁻¹ᵁ Us
    have hxO : x ∈ O :=
      ⟨⟨show f x ∈ Uy by rwa [hfx], show g x ∈ Uy by rwa [hgx]⟩, show pX x ∈ Us by rwa [hxs]⟩
    obtain ⟨_, ⟨Ux : X.Opens, hUx, rfl⟩, hxUx, hUxO⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxO O.2
    have hUf : Ux ≤ f ⁻¹ᵁ Uy := hUxO.trans (inf_le_left.trans inf_le_left)
    have hUg : Ux ≤ g ⁻¹ᵁ Uy := hUxO.trans (inf_le_left.trans inf_le_right)
    have hUpX : Ux ≤ pX ⁻¹ᵁ Us := hUxO.trans inf_le_right
    let pX' := pX.resLE Us Ux hUpX
    have hUyS' : Uy ≤ pY ⁻¹ᵁ Us := hUyS
    let pY' := pY.resLE Us Uy hUyS'
    let f' := f.resLE Uy Ux hUf
    let g' := g.resLE Uy Ux hUg
    have hpYι : pY' ≫ Us.ι = Uy.ι ≫ pY := Scheme.Hom.resLE_comp_ι pY hUyS'
    have hfι : f' ≫ Uy.ι = Ux.ι ≫ f := Scheme.Hom.resLE_comp_ι f hUf
    have hgι : g' ≫ Uy.ι = Ux.ι ≫ g := Scheme.Hom.resLE_comp_ι g hUg
    have hres : ∀ (k : X ⟶ Y) (hU : Ux ≤ k ⁻¹ᵁ Uy), k ≫ pY = pX →
        k.resLE Uy Ux hU ≫ pY' = pX' := fun k hU hk ↦ by
      apply (cancel_mono Us.ι).mp
      rw [Category.assoc, hpYι, ← Category.assoc, Scheme.Hom.resLE_comp_ι k hU,
        Category.assoc, hk]
      exact (Scheme.Hom.resLE_comp_ι pX hUpX).symm
    have hf' : f' ≫ pY' = pX' := hres f hUf hf
    have hg' : g' ≫ pY' = pX' := hres g hUg hg
    let x' : Ux.toScheme := ⟨x, hxUx⟩
    let y' : Uy.toScheme := ⟨y, hyUy⟩
    have hresx : ∀ (k : X ⟶ Y) (hU : Ux ≤ k ⁻¹ᵁ Uy), k x = y → k.resLE Uy Ux hU x' = y' :=
      fun k hU hk ↦ Subtype.ext (by simpa [x', y', Scheme.Hom.coe_resLE_apply] using hk)
    have hfx' : f' x' = y' := hresx f hUf hfx
    have hgx' : g' x' = y' := hresx g hUg hgx
    have hfg' : f'.stalkMap x' =
        Uy.toScheme.presheaf.stalkSpecializes
          (Inseparable.of_eq (hfx'.trans hgx'.symm).symm).specializes ≫ g'.stalkMap x' := by
      let hfIso := Scheme.Hom.resLEStalkMap f hUf x'
      let hgIso := Scheme.Hom.resLEStalkMap g hUg x'
      let αf := hfIso.hom.left
      let αg := hgIso.hom.left
      let β := hfIso.hom.right
      let δ := Y.presheaf.stalkSpecializes
        (Inseparable.of_eq (hfx.trans hgx.symm).symm).specializes
      let δ' := Uy.toScheme.presheaf.stalkSpecializes
        (Inseparable.of_eq (hfx'.trans hgx'.symm).symm).specializes
      let hrel := (Inseparable.of_eq (hfx'.trans hgx'.symm).symm).specializes
      let δMap := Y.presheaf.stalkSpecializes (Uy.ι.base.hom.map_specializes hrel)
      have hfSq : αf ≫ f.stalkMap x = f'.stalkMap x' ≫ β := hfIso.hom.w
      have hgSq : αg ≫ g.stalkMap x = g'.stalkMap x' ≫ β := hgIso.hom.w
      have hspec : αf ≫ δ = δ' ≫ αg := by
        have qf : Uy.ι (f' x') = f x := Scheme.Hom.coe_resLE_apply f hUf x'
        have qg : Uy.ι (g' x') = g x := Scheme.Hom.coe_resLE_apply g hUg x'
        let κf := Y.presheaf.stalkSpecializes (Inseparable.of_eq qf.symm).specializes
        let κg := Y.presheaf.stalkSpecializes (Inseparable.of_eq qg.symm).specializes
        have hα : ∀ (k : X ⟶ Y) (hU : Ux ≤ k ⁻¹ᵁ Uy) (q : Uy.ι (k.resLE Uy Ux hU x') = k x),
            (Scheme.Hom.resLEStalkMap k hU x').hom.left = (Uy.stalkIso (k.resLE Uy Ux hU x')).hom ≫
              Y.presheaf.stalkSpecializes (Inseparable.of_eq q.symm).specializes := by
          intro k hU q
          simp [Scheme.Hom.resLEStalkMap, TopCat.Presheaf.stalkCongr_hom]
        have hαf : αf = (Uy.stalkIso (f' x')).hom ≫ κf := hα f hUf qf
        have hαg : αg = (Uy.stalkIso (g' x')).hom ≫ κg := hα g hUg qg
        have hcong : κf ≫ δ = δMap ≫ κg := by
          rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_comp]
        have hnat' : δMap ≫ (Uy.stalkIso (g' x')).inv =
            (Uy.stalkIso (f' x')).inv ≫ δ' := by
          rw [Scheme.Opens.stalkIso_inv (U := Uy) (x := g' x'),
            Scheme.Opens.stalkIso_inv (U := Uy) (x := f' x')]
          exact Scheme.Hom.stalkSpecializes_stalkMap (f := Uy.ι) (g' x') (f' x') hrel
        have hbase : (Uy.stalkIso (f' x')).hom ≫ δMap =
            δ' ≫ (Uy.stalkIso (g' x')).hom :=
          ((Iso.inv_comp_eq _).mp
            ((Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mp hnat').symm)).symm
        rw [hαf, hαg]
        exact (Category.assoc _ _ _).trans <| (congrArg _ hcong).trans <|
          (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ κg) hbase).trans
            (Category.assoc _ _ _)
      apply (cancel_mono β).mp
      calc
        f'.stalkMap x' ≫ β = αf ≫ f.stalkMap x := hfSq.symm
        _ = αf ≫ δ ≫ g.stalkMap x := by
          simpa [Category.assoc] using congrArg (fun k ↦ αf ≫ k) hfg
        _ = δ' ≫ αg ≫ g.stalkMap x := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ g.stalkMap x) hspec
        _ = δ' ≫ g'.stalkMap x' ≫ β := by rw [hgSq]
    have : IsAffine Us.toScheme := hUs
    have : IsAffine Ux.toScheme := hUx
    have : IsAffine Uy.toScheme := hUy
    have : LocallyOfFiniteType pY' := by
      dsimp [pY']
      infer_instance
    obtain ⟨U', hxU', hU'⟩ := exists_open_eq_of_stalkMap_eq_of_affine
      pX' pY' f' g' hf' hg' x' y' hfx' hgx' hfg'
    let U : X.Opens := Ux.ι ''ᵁ U'
    have hxU : x ∈ U := ⟨x', hxU', rfl⟩
    have hcomp : (U'.ι ≫ Ux.ι) ≫ f = (U'.ι ≫ Ux.ι) ≫ g := by
      simpa only [Category.assoc, ← hfι, ← hgι] using
        congrArg (fun k ↦ k ≫ Uy.ι) hU'
    have hU : U.ι ≫ f = U.ι ≫ g := by
      have hι' : (Ux.ι.isoImage U').inv ≫ (U'.ι ≫ Ux.ι) = U.ι := by
        rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
        simp [U]
      simpa only [← hι', Category.assoc] using
        congrArg (fun k ↦ (Ux.ι.isoImage U').inv ≫ k) hcomp
    exact ⟨U, hxU, hU⟩
  · exact spread_out_unique_of_isGermInjective f g (hfx.trans hgx.symm) hfg
  · exact spread_out_unique_of_isGermInjective f g (hfx.trans hgx.symm) hfg
  · have := X.isGermInjective_of_isReduced_of_finite_irreducibleComponents hX
    exact spread_out_unique_of_isGermInjective f g (hfx.trans hgx.symm) hfg

end AlgebraicGeometry

end
