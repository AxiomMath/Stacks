module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionAffineUnits

/-!
# `μ_ℓ`-cohomology of a smooth affine curve under extension of the algebraically closed base field

Let `X` be a smooth affine curve over an algebraically closed field `k`, `k'/k` an algebraically
closed extension and `ℓ ∈ k^*`. Restriction `H^q(X, μ_ℓ) → H^q(X_{k'}, μ_ℓ)` is bijective for
every `q ≥ 1`. Through the Kummer ladder
(`Stacks.EtaleCohomology.bijective_rootsOfUnityRestriction`) this needs:

* in degree one, `Γ(X, 𝒪_X)^* → Γ(X_{k'}, 𝒪)^*` bijective modulo `ℓ`-th powers
  (`Stacks.EtaleCohomology.unitsScalarExtension_nsmul_comparison`, through the smooth projective
  compactification `X ⊂ Y` of Tag 0H1F), read on `H⁰(𝐆_m)`
  (`Stacks.EtaleCohomology.multiplicativeRestriction_zero_ofUnit`), and `Cl(X) → Cl(X_{k'})`
  injective and surjective on `ℓ`-torsion
  (`Stacks.EtaleCohomology.injective_curveClassGroupScalarExtensionMap_of_isOpenImmersion`);
* in degree two, `Cl(X)` and `Cl(X_{k'})` are `ℓ`-divisible and `H²(𝐆_m) = 0`;
* in degree at least three both sides vanish.

## Main results

* `Stacks.EtaleCohomology.multiplicativeRestriction_zero_ofUnit`: restriction on `H⁰(𝐆_m)` is
  pullback of invertible functions.
* `Stacks.EtaleCohomology.bijective_rootsOfUnityRestriction_scalarExtension_of_isAffine`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u v w

/-- **Transport of a comparison modulo `ℓ` along isomorphisms.** -/
theorem AddMonoidHom.nsmul_comparison_of_addEquiv {A B A' B' : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] (ℓ : ℕ) (e : A ≃+ B) (e' : A' ≃+ B')
    (f : A →+ A') (g : B →+ B') (hfg : ∀ a, e' (f a) = g (e a))
    (hg : (∀ b z', ℓ • z' = g b → ∃ z, ℓ • z = b) ∧ (∀ b', ∃ b z', b' = g b + ℓ • z')) :
    (∀ a z', ℓ • z' = f a → ∃ z, ℓ • z = a) ∧ (∀ a', ∃ a z', a' = f a + ℓ • z') := by
  refine ⟨fun a z' h => ?_, fun a' => ?_⟩
  · obtain ⟨z, hz⟩ := hg.1 (e a) (e' z') (by rw [← map_nsmul, h, hfg])
    exact ⟨e.symm z, by rw [← map_nsmul, hz, AddEquiv.symm_apply_apply]⟩
  · obtain ⟨b, z', hb⟩ := hg.2 (e' a')
    refine ⟨e.symm b, e'.symm z', e'.injective ?_⟩
    rw [map_add, hfg, AddEquiv.apply_symm_apply, map_nsmul, AddEquiv.apply_symm_apply, hb]

namespace Stacks.EtaleCohomology

open Stacks.Kummer

/-! ### Restriction on `H⁰(𝐆_m)` -/

/-- **The comparison on `𝐆_m` after restriction**: the section of `p⁻¹ 𝐆_{m,X}` attached to an
invertible function `x` on an étale `X`-scheme `U`, restricted along `h : T ⟶ U ×_X X'`, is carried
to the pullback of `x` along `T ⟶ U ×_X X' ⟶ U`. -/
theorem multiplicativeInverseImageComparison_app_map_ofUnit {X X' : Scheme.{u}} (p : X' ⟶ X)
    {U : X.Etale} {T : X'.Etale} (h : T ⟶ (smallEtaleBaseChange p).obj U) (x : (Γ(U.left, ⊤))ˣ) :
    (multiplicativeInverseImageComparison.{u, v} p).hom.app (op T)
        (((etaleAbelianInverseImage.{u, v} p).obj (multiplicativeSheaf.{u, v} X)).obj.map h.op
          (((etaleAbelianInverseImageDirectImageAdj.{u, v} p).unit.app
            (multiplicativeSheaf.{u, v} X)).hom.app (op U) (ofUnit x))) =
      ofUnit (Units.map (h.left ≫ pullback.fst U.hom p).appTop.hom.toMonoidHom x) := by
  have hn := ConcreteCategory.congr_hom
    ((multiplicativeInverseImageComparison.{u, v} p).hom.naturality h.op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, v} p).unit.app
      (multiplicativeSheaf.{u, v} X)).hom.app (op U) (ofUnit x))
  exact hn.trans ((congrArg ((multiplicativeSheaf.{u, v} X').obj.map h.op)
    (multiplicativeInverseImageComparison_app_ofUnit.{u, v} p U x)).trans rfl)

/-- A morphism `X' ⟶ X ×_X X'` of étale `X'`-schemes, followed by the first projection, is `p`. -/
theorem left_comp_pullback_fst_etaleMkId {X X' : Scheme.{u}} (p : X' ⟶ X)
    (h : Scheme.Etale.mk (𝟙 X') ⟶ (smallEtaleBaseChange p).obj (Scheme.Etale.mk (𝟙 X))) :
    h.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 X)).hom p = p := by
  have hw : h.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 X)).hom p = 𝟙 X' := MorphismProperty.Over.w h
  have hc := congrArg (fun φ => h.left ≫ φ)
    (pullback.condition (f := (Scheme.Etale.mk (𝟙 X)).hom) (g := p))
  exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans (hc.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) hw).trans (Category.id_comp p)))))

/-- **Restriction on `H⁰(𝐆_m)` is pullback of invertible functions**: read through
`H⁰(𝐆_m) ≅ Γ(𝒪)^*`, `multiplicativeRestriction p 0` is `p^* : Γ(X, 𝒪_X)^* → Γ(X', 𝒪_{X'})^*`. -/
theorem multiplicativeRestriction_zero_ofUnit {X X' : Scheme.{u}} (p : X' ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (x : (Γ(X, ⊤))ˣ) :
    Sheaf.H.equiv₀ (multiplicativeSheaf.{u, v} X') (isTerminalEtaleMkId X')
        (multiplicativeRestriction.{u, v, w} p 0
          ((Sheaf.H.equiv₀ (multiplicativeSheaf.{u, v} X) (isTerminalEtaleMkId X)).symm
            (ofUnit x))) =
      ofUnit (U := Scheme.Etale.mk (𝟙 X')) (Units.map p.appTop.hom.toMonoidHom x) := by
  rw [multiplicativeRestriction_apply, ← Sheaf.H.equiv₀_naturality,
    equiv₀_etaleCohomologyRestrictionMap_zero, AddEquiv.apply_symm_apply]
  refine (multiplicativeInverseImageComparison_app_map_ofUnit (U := Scheme.Etale.mk (𝟙 X)) p
    (((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange p)).from
      (Scheme.Etale.mk (𝟙 X'))) x).trans ?_
  exact congrArg (fun φ : X' ⟶ X => ofUnit.{u, v} (U := Scheme.Etale.mk (𝟙 X'))
    (Units.map φ.appTop.hom.toMonoidHom x)) (left_comp_pullback_fst_etaleMkId p _)

/-- **`H⁰(𝐆_m) ≅ Γ(𝒪)^*`.** -/
def sheafHZeroMultiplicativeAddEquiv (Z : Scheme.{u})
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) 0 ≃+ Additive (Γ(Z, ⊤))ˣ :=
  (Sheaf.H.equiv₀ (multiplicativeSheaf.{u, v} Z) (isTerminalEtaleMkId Z)).trans
    (AddEquiv.ulift (α := Additive (Γ(Z, ⊤))ˣ))

/-- The inverse of `H⁰(𝐆_m) ≅ Γ(𝒪)^*` sends `x` to the class of the section `x`. -/
theorem sheafHZeroMultiplicativeAddEquiv_symm_ofMul (Z : Scheme.{u})
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (x : (Γ(Z, ⊤))ˣ) :
    (sheafHZeroMultiplicativeAddEquiv.{u, v, w} Z).symm (Additive.ofMul x) =
      (Sheaf.H.equiv₀ (multiplicativeSheaf.{u, v} Z) (isTerminalEtaleMkId Z)).symm (ofUnit x) :=
  rfl

/-- **Restriction on `H⁰(𝐆_m)` is pullback of invertible functions**, through
`H⁰(𝐆_m) ≅ Γ(𝒪)^*`. -/
theorem sheafHZeroMultiplicativeAddEquiv_multiplicativeRestriction {X X' : Scheme.{u}}
    (p : X' ⟶ X) [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (a : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 0) :
    sheafHZeroMultiplicativeAddEquiv.{u, v, w} X' (multiplicativeRestriction.{u, v, w} p 0 a) =
      (Units.map p.appTop.hom.toMonoidHom).toAdditive
        (sheafHZeroMultiplicativeAddEquiv.{u, v, w} X a) := by
  obtain ⟨y, rfl⟩ := (sheafHZeroMultiplicativeAddEquiv.{u, v, w} X).symm.surjective a
  obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = y := ⟨Additive.toMul y, rfl⟩
  have h1 : multiplicativeRestriction.{u, v, w} p 0
      ((sheafHZeroMultiplicativeAddEquiv.{u, v, w} X).symm (Additive.ofMul x)) =
      (sheafHZeroMultiplicativeAddEquiv.{u, v, w} X').symm
        (Additive.ofMul (Units.map p.appTop.hom.toMonoidHom x)) := by
    rw [sheafHZeroMultiplicativeAddEquiv_symm_ofMul, sheafHZeroMultiplicativeAddEquiv_symm_ofMul]
    exact (AddEquiv.eq_symm_apply _).2 (multiplicativeRestriction_zero_ofUnit p x)
  rw [h1, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

/-! ### Affine curves -/

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- On an affine smooth curve over an algebraically closed field, `H¹(𝐆_m)` is `ℓ`-divisible for
`ℓ` invertible in the field. -/
private theorem exists_nsmul_eq_sheafH_one_multiplicativeSheaf {K : Type u} [Field K]
    [IsAlgClosed K] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsCurve K g] [Smooth g] [IsAffine Z]
    {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (hℓ : IsUnit (ℓ : K))
    (c : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} Z) 1) : ∃ d, ℓ • d = c :=
  (sheafH_one_multiplicativeSheaf_of_classGroup g hℓ0
    (fun _ q _ _ _ x y => exists_nsmul_eq_sub_curveClassGroup_single q hℓ x y)
    (fun _ q _ _ _ => finite_nsmul_torsion_curveClassGroup q hℓ)).1 inferInstance c

section Affine

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

/-- **Restriction of `μ_ℓ`-cohomology to `X_{k'}` is bijective in every positive degree** for a
smooth affine curve `X` over an algebraically closed field `k`, `ℓ ∈ k^*`, and an algebraically
closed extension `k'/k`. -/
theorem bijective_rootsOfUnityRestriction_scalarExtension_of_isAffine [IsAffine X] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective
      (rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) ℓ q) := by
  have hℓ0 : ℓ ≠ 0 := ne_zero_of_isUnit_natCast hℓ
  have hℓX := isUnit_natCast_globalSections_of_isUnit g hℓ
  have hℓ' : IsUnit (ℓ : k') := by
    have h := hℓ.map (algebraMap k k')
    rwa [map_natCast] at h
  obtain ⟨-, Y, qY, j, hj, hjq, hcq, hproj, -, hsq, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k g
      (isRegular_of_smooth_over_field g)
  let _ : IsOpenImmersion j := hj
  let _ : IsCurve k qY := hcq
  let _ : Smooth qY := hsq
  let _ : IsProper qY := isProper_of_isProjectiveMorphism qY hproj
  subst hjq
  have := isDominant_of_isOpenImmersion_of_isCurve j
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve (j ≫ qY)
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve qY
  set e := sheafHOneMultiplicativeAddEquivClosedPointClassGroup (j ≫ qY)
  set e' := sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' (j ≫ qY))
  have hCl := injective_curveClassGroupScalarExtensionMap_of_isOpenImmersion qY j k' hℓ
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · have hU := AddMonoidHom.nsmul_comparison_of_addEquiv ℓ
        (sheafHZeroMultiplicativeAddEquiv.{u, u + 1, u + 1} X)
        (sheafHZeroMultiplicativeAddEquiv.{u, u + 1, u + 1} (scalarExtension k k' (j ≫ qY)))
        (multiplicativeRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' (j ≫ qY)) 0) _
        (sheafHZeroMultiplicativeAddEquiv_multiplicativeRestriction.{u, u + 1, u + 1} _)
        (unitsScalarExtension_nsmul_comparison qY j k' hℓ0)
      refine bijective_rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' (j ≫ qY))
        hℓ0 hℓX 0 hU.1 hU.2 (fun b _ hb => ?_) (fun b' hb' => ?_)
      · rw [multiplicativeRestriction_one_eq] at hb
        have h1 : curveClassGroupScalarExtensionMap (j ≫ qY) k' (e b) = 0 := by
          have := congrArg e' hb
          rwa [AddEquiv.apply_symm_apply, map_zero] at this
        have h2 : e b = 0 := hCl.1 (h1.trans (map_zero _).symm)
        exact e.injective (h2.trans (map_zero e).symm)
      · obtain ⟨c, hc, hcc⟩ := hCl.2 (e' b') (by rw [← map_nsmul, hb', map_zero])
        refine ⟨e.symm c, by rw [← map_nsmul, hc, map_zero], ?_⟩
        rw [multiplicativeRestriction_one_eq, AddEquiv.apply_symm_apply, hcc,
          AddEquiv.symm_apply_apply]
    · have h2X := subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, u + 1, u + 1}
        (j ≫ qY) 2 le_rfl
      have h2X' := subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, u + 1, u + 1}
        (scalarExtensionSnd k k' (j ≫ qY)) 2 le_rfl
      refine bijective_rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' (j ≫ qY))
        hℓ0 hℓX 1 (fun a _ _ => exists_nsmul_eq_sheafH_one_multiplicativeSheaf (j ≫ qY) hℓ0 hℓ a)
        (fun a' => ?_) (fun b _ _ => Subsingleton.elim _ _)
        (fun b' _ => ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)
      obtain ⟨d', hd'⟩ := exists_nsmul_eq_sheafH_one_multiplicativeSheaf
        (scalarExtensionSnd k k' (j ≫ qY)) hℓ0 hℓ' a'
      exact ⟨0, d', by rw [map_zero, zero_add, hd']⟩
  · have := subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve.{u, u + 1, u + 1} (j ≫ qY) hℓ
      (r + 1) (by omega)
    have := subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve.{u, u + 1, u + 1}
      (scalarExtensionSnd k k' (j ≫ qY)) hℓ' (r + 1) (by omega)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

end Affine

end Stacks.EtaleCohomology

end
