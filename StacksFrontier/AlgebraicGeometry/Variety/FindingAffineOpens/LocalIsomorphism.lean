module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.GermInjective

/-!
# A morphism inducing an isomorphism on one local ring is an open immersion nearby

Let `f : X ⟶ S` be locally of finite type, with `S` reduced and with only finitely many
irreducible components. If the canonical map `𝒪_{S, f x} ⟶ 𝒪_{X, x}` is an isomorphism, then
`f` restricts to an open immersion on some open neighbourhood of `x`.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_res_of_isIso_stalkMap`: such an `f` is an open
  immersion on an open neighbourhood of `x`.

## References

* [Stacks Project, Tag 09NH](https://stacks.math.columbia.edu/tag/09NH)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A section of a formally unramified morphism locally of finite type is an open
immersion. -/
private theorem isOpenImmersion_of_section_of_formallyUnramified
    {X S : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ X) (hgf : g ≫ f = 𝟙 S)
    [FormallyUnramified f] [LocallyOfFiniteType f] : IsOpenImmersion g := by
  have hsection : IsOpenImmersion
      (pullback.lift (𝟙 S) g (by simp) : S ⟶ pullback (g ≫ f) f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (pullback_lift_diagonal_isPullback g f) (by infer_instance)
  have : IsIso (g ≫ f) := by rw [hgf]; infer_instance
  have : IsIso (pullback.snd (g ≫ f) f) :=
    (IsPullback.of_hasPullback (g ≫ f) f).isIso_snd_of_isIso
  have hcomp : (pullback.lift (𝟙 S) g (by simp) : S ⟶ pullback (g ≫ f) f) ≫
      pullback.snd (g ≫ f) f = g := by simp [pullback.lift_snd]
  rw [← hcomp]
  infer_instance

/-- If the induced map of localisations at a pair of corresponding primes is an isomorphism,
the algebra is unramified at the prime upstairs. -/
private theorem isUnramifiedAt_of_isIso_localRingHom
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (φ : A →+* B)
    (hφ : φ = algebraMap A B)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hqp : p = q.comap φ)
    (hiso : IsIso (CommRingCat.ofHom
      (Localization.localRingHom p q φ hqp))) :
    Algebra.IsUnramifiedAt A q := by
  let l : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q φ hqp
  let : IsScalarTower A B (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hl : l.FormallyUnramified :=
    .of_surjective (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom l)).2
  have hbase : (algebraMap A (Localization.AtPrime p)).FormallyUnramified := by
    rw [RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  have hmap : l.comp (algebraMap A (Localization.AtPrime p)) =
      algebraMap A (Localization.AtPrime q) := by
    subst φ
    ext a
    simp [l, Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]
  exact RingHom.formallyUnramified_algebraMap.mp (hmap ▸ RingHom.FormallyUnramified.comp hbase hl)

/-- **Stacks Project, Tag 09NH.** If the local-ring map of a locally finite-type morphism
is an isomorphism at `x`, and the target is reduced with finitely many irreducible
components, then the morphism is an open immersion near `x`. -/
@[stacks 09NH]
public theorem exists_isOpenImmersion_res_of_isIso_stalkMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsReduced S] [LocallyOfFiniteType f]
    (hcomponents : (irreducibleComponents S).Finite)
    (hstalk : IsIso (f.stalkMap x)) :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := by
  let s := f x
  obtain ⟨W₀, hsW₀, hW₀, hginj⟩ :=
    exists_affineOpen_germ_injective_of_isReduced S s hcomponents
  let : S.IsGermInjectiveAt s := ⟨⟨W₀, hsW₀, hW₀, hginj⟩⟩
  let φ : Spec (S.presheaf.stalk s) ⟶ X :=
    Spec.map (asIso (f.stalkMap x)).inv ≫ X.fromSpecStalk x
  have hφ : φ ≫ f = S.fromSpecStalk s := by
    show Spec.map (asIso (f.stalkMap x)).inv ≫
      X.fromSpecStalk x ≫ f = S.fromSpecStalk (f x)
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)]
    simp
  obtain ⟨W, hsW, g, hgφ, hgf⟩ :=
    AlgebraicGeometry.spread_out_of_isGermInjective' (sX := 𝟙 S) (sY := f) φ (by simpa using hφ)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ W₀ from hsW₀)
      (f ⁻¹ᵁ W₀).2
  let φR := (f.appLE W₀ V hVU).hom
  let : Algebra Γ(S, W₀) Γ(X, V) := φR.toAlgebra
  let p := (hW₀.primeIdealOf ⟨s, hsW₀⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hqp : p = q.comap φR :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE W₀ hW₀ V hV hVU hxV).1).symm
  have hloc : IsIso (CommRingCat.ofHom
      (Localization.localRingHom p q φR hqp)) :=
    (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f W₀ hW₀ V hV hVU hxV) |>.mp hstalk
  have hunram : Algebra.IsUnramifiedAt Γ(S, W₀) q :=
    isUnramifiedAt_of_isIso_localRingHom φR (by ext a; rfl) p q hqp hloc
  let : Algebra.FiniteType Γ(S, W₀) Γ(X, V) := by
    rw [← RingHom.finiteType_algebraMap]
    exact f.finiteType_appLE hW₀ hV hVU
  obtain ⟨d, hdq, hdunram⟩ :=
    Algebra.exists_unramified_of_isUnramifiedAt (R := Γ(S, W₀)) q
  let V₁ : X.Opens := X.basicOpen d
  have hV₁ : IsAffineOpen V₁ := hV.basicOpen d
  have hV₁V : V₁ ≤ V := Scheme.basicOpen_le X d
  have hxV₁ : x ∈ V₁ := by
    show x ∈ X.basicOpen d
    rw [← hV.fromSpec_image_basicOpen]
    exact ⟨hV.primeIdealOf ⟨x, hxV⟩, hdq, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  have hV₁U : V₁ ≤ f ⁻¹ᵁ W₀ := hV₁V.trans hVU
  let ρ : Γ(X, V) →+* Γ(X, V₁) := (X.presheaf.map (homOfLE hV₁V).op).hom
  let : IsLocalization.Away d Γ(X, V₁) := hV.isLocalization_basicOpen d
  let : Algebra Γ(X, V) Γ(X, V₁) := ρ.toAlgebra
  let eB : Γ(X, V₁) ≃ₐ[Γ(X, V)] Localization.Away d :=
    IsLocalization.algEquiv (Submonoid.powers d) Γ(X, V₁) (Localization.Away d)
  let F := ρ.comp φR
  let G := (algebraMap Γ(X, V) (Localization.Away d)).comp φR
  have hformalG : RingHom.FormallyUnramified G := by
    show RingHom.FormallyUnramified (algebraMap Γ(S, W₀) (Localization.Away d))
    rw [RingHom.formallyUnramified_algebraMap]
    exact hdunram.formallyUnramified
  have hfg : CommRingCat.ofHom F ≫ eB.toCommRingCatIso.hom = CommRingCat.ofHom G := by
    ext a
    show eB (ρ (φR a)) = algebraMap Γ(X, V) (Localization.Away d) (φR a)
    simpa only [RingHom.algebraMap_toAlgebra] using eB.commutes (φR a)
  have hformalComp : RingHom.FormallyUnramified F := by
    let ee : Arrow.mk (CommRingCat.ofHom F) ≅ Arrow.mk (CommRingCat.ofHom G) :=
      Arrow.isoMk (Iso.refl _) eB.toCommRingCatIso hfg.symm
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff ee |>.mpr hformalG
  let φR₁ := (f.appLE W₀ V₁ hV₁U).hom
  have hφR₁ : φR₁ = ρ.comp φR := by
    ext a
    show (f.appLE W₀ V₁ hV₁U) a = ρ (φR a)
    simpa [ρ, φR] using congrArg (fun f => f a)
      (Scheme.Hom.appLE_map (f := f) hVU (homOfLE hV₁V).op).symm
  have hformalApp : RingHom.FormallyUnramified φR₁ := hφR₁ ▸ hformalComp
  let k := f.resLE W₀ V₁ hV₁U
  have hk : FormallyUnramified k := by
    have hspec : FormallyUnramified (Spec.map k.appTop) :=
      (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
        (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f W₀ V₁ hV₁U) |>.mpr hformalApp)
    let : IsAffine W₀ := hW₀
    let : IsAffine V₁ := hV₁
    let e := arrowIsoSpecΓOfIsAffine k
    have heq : k = e.hom.left ≫ Spec.map k.appTop ≫ e.inv.right := by
      calc
        k = k ≫ e.hom.right ≫ e.inv.right := by simp
        _ = e.hom.left ≫ Spec.map k.appTop ≫ e.inv.right := by
          simp
    have hleft : FormallyUnramified e.hom.left := by infer_instance
    have hmid : FormallyUnramified (e.hom.left ≫ Spec.map k.appTop) :=
      MorphismProperty.comp_mem (@FormallyUnramified) _ _ hleft hspec
    have hright : FormallyUnramified e.inv.right := by infer_instance
    rw [heq]
    exact MorphismProperty.comp_mem (@FormallyUnramified)
      (e.hom.left ≫ Spec.map k.appTop) e.inv.right hmid hright
  have hformalV₁f : FormallyUnramified (V₁.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hV₁U]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hk (by infer_instance)
  have hgs : g ⟨s, hsW⟩ = x := by
    let c : Spec (S.presheaf.stalk s) := IsLocalRing.closedPoint _
    have hφc : φ c = x := by
      have hclosed : Spec.map (asIso (f.stalkMap x)).inv c =
          (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x)) := by
        simpa [c, s] using (Spec_closedPoint (f := (asIso (f.stalkMap x)).inv))
      show X.fromSpecStalk x (Spec.map (asIso (f.stalkMap x)).inv c) = x
      rw [hclosed, Scheme.fromSpecStalk_closedPoint]
    have hWc : W.fromSpecStalkOfMem s hsW c = ⟨s, hsW⟩ := by
      apply Subtype.ext
      show (W.fromSpecStalkOfMem s hsW ≫ W.ι) c = s
      rw [W.fromSpecStalkOfMem_ι]
      simp [c]
    have h := congrArg (fun k : Spec (S.presheaf.stalk s) ⟶ X => k c) hgφ
    change φ c = g (W.fromSpecStalkOfMem s hsW c) at h
    rw [hφc, hWc] at h
    exact h.symm
  let H : W.toScheme.Opens := g ⁻¹ᵁ V₁
  have hsH : (⟨s, hsW⟩ : W.toScheme) ∈ H := by
    show g ⟨s, hsW⟩ ∈ V₁
    rwa [hgs]
  have hrange : Set.range (H.ι ≫ g) ⊆ Set.range V₁.ι := by
    rintro y ⟨z, rfl⟩
    exact ⟨⟨g z.1, z.2⟩, rfl⟩
  let gH : H.toScheme ⟶ V₁.toScheme := IsOpenImmersion.lift V₁.ι (H.ι ≫ g) hrange
  have hsec : gH ≫ (V₁.ι ≫ f) = H.ι ≫ W.ι := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    simp [hgf]
  let jBase : H.toScheme ⟶ S := H.ι ≫ W.ι
  let F' : V₁.toScheme ⟶ S := V₁.ι ≫ f
  let P := pullback F' jBase
  let t : H.toScheme ⟶ P := pullback.lift gH (𝟙 H.toScheme) (by simpa [jBase, F'] using hsec)
  have : LocallyOfFiniteType F' := inferInstance
  have : LocallyOfFiniteType (pullback.snd F' jBase) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback F' jBase) inferInstance
  let : FormallyUnramified (pullback.snd F' jBase) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @FormallyUnramified) (IsPullback.of_hasPullback F' jBase) hformalV₁f
  have htsec : t ≫ pullback.snd F' jBase = 𝟙 H.toScheme := pullback.lift_snd _ _ _
  have htOpen : IsOpenImmersion t :=
    isOpenImmersion_of_section_of_formallyUnramified (pullback.snd F' jBase) t htsec
  have : IsOpenImmersion jBase := inferInstance
  have : IsOpenImmersion (pullback.fst F' jBase) :=
    MorphismProperty.pullback_fst F' jBase (inferInstance : IsOpenImmersion jBase)
  let jX : H.toScheme ⟶ X := H.ι ≫ g
  have hjXeq : t ≫ pullback.fst F' jBase ≫ V₁.ι = jX := by
    rw [pullback.lift_fst_assoc]
    exact IsOpenImmersion.lift_fac V₁.ι (H.ι ≫ g) hrange
  have : IsOpenImmersion jX := by
    rw [← hjXeq]
    infer_instance
  have hjf : jX ≫ f = jBase := by
    simp [jX, jBase, Category.assoc, hgf]
  let U : X.Opens := jX.opensRange
  have hxU : x ∈ U := by
    show x ∈ jX.opensRange
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨⟨⟨s, hsW⟩, hsH⟩, hgs⟩
  refine ⟨U, hxU, ?_⟩
  have huEq : U.ι ≫ f = (jX.isoOpensRange.inv ≫ H.ι) ≫ W.ι := by
    calc
      U.ι ≫ f = (jX.isoOpensRange.inv ≫ jX) ≫ f := by
        simp [U, Scheme.Hom.isoOpensRange_inv_comp]
      _ = jX.isoOpensRange.inv ≫ (jX ≫ f) := by simp
      _ = (jX.isoOpensRange.inv ≫ H.ι) ≫ W.ι := by simp [hjf, jBase]
  rw [huEq]
  infer_instance

end AlgebraicGeometry

end
