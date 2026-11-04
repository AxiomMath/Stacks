module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.MayerVietorisVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# A bound on the degrees of the higher direct images over an affine target

Let `X` be a quasi-compact and quasi-separated algebraic space and `h : X ⟶ T` a morphism to an
affine algebraic space.  There is an integer `N` such that `R^p h_*𝓖 = 0` for every
quasi-coherent `𝒪_X`-module `𝓖` and every `p ≥ N`.

The proof is the induction principle of Stacks 08GP on the quasi-compact quasi-separated objects
of the spaces-étale site of `X`.  On an affine object the composite to `T` is a morphism of
affine algebraic spaces, hence affine, and its higher direct images of quasi-coherent modules
vanish by Stacks 073H.  Across an elementary distinguished square `(U ⊆ W, V ⟶ W)` with `V`
affine, the relative Mayer–Vietoris sequence of Stacks 08JK
(`AlgebraicGeometry.Space.isZero_rightDerived_succ_of_eds`) gives the bound
`max(N_U, N_V, N_{U ×_W V} + 1)` for `W` from bounds for the three other members.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_of_isAffineSpace`: the
  bound over an affine target.
* `AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_of_qcqs`: the bound for a
  morphism between quasi-compact quasi-separated algebraic spaces, by restriction to an affine
  surjective étale chart of the target (Stacks 03H6), the base change of Stacks 03LX for higher
  direct images, and faithfulness of restriction to a surjective chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

attribute [local instance 5000] modulePushforward_additive

attribute [local instance] etaleModulePullback_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A uniform vanishing bound for the higher direct images of quasi-coherent modules along a
morphism of algebraic spaces. -/
abbrev HasBoundedHigherDirectImages {Y T : AlgebraicSpaces B S hS} (h : Y ⟶ T) : Prop :=
  ∃ N : ℕ, ∀ G : Modules.{u, u} B S hS Y.1 Y.2, G.IsQuasicoherentOnSite → ∀ p : ℕ, N ≤ p →
    IsZero (((modulePushforward B S hS h).rightDerived p).obj G)

/-- The property propagated by the induction: a uniform vanishing bound for the higher direct
images of quasi-coherent modules along the composite `Y ⟶ X ⟶ T`. -/
abbrev HigherDirectImageBounded {X T : AlgebraicSpaces B S hS} (h : X ⟶ T)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Y ⟶ X.1) : Prop :=
  ∀ hY : IsAlgebraicSpace B S hS Y, HasBoundedHigherDirectImages B S hS
    ((ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ h)

/-- **The higher direct images of quasi-coherent modules along a morphism from a
quasi-compact quasi-separated algebraic space to an affine one vanish above a fixed degree.** -/
theorem exists_isZero_rightDerived_modulePushforward_of_isAffineSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) {X T : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hT : IsAffineSpace B S hS T.1) (h : X ⟶ T) :
    ∃ N : ℕ, ∀ G : Modules.{u, u} B S hS X.1 X.2, G.IsQuasicoherentOnSite → ∀ p : ℕ, N ≤ p →
      IsZero (((modulePushforward B S hS h).rightDerived p).obj G) := by
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs (HigherDirectImageBounded B S hS h)
    (fun V hV hY => show HasBoundedHigherDirectImages B S hS _ from ⟨1, fun G hG p hp =>
      isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS _
        (isAffineHom_of_isAffineSpace B S hS _ hV hT) G hG p (by omega)⟩)
    (by
      intro W V U f hcomp hsq _ _ _ _ hPU hPV hPpb
      unfold HigherDirectImageBounded HasBoundedHigherDirectImages at hPU hPV hPpb ⊢
      intro hY
      obtain ⟨NU, hNU⟩ := hPU hsq.isOpenSubspace.1
      obtain ⟨NV, hNV⟩ := hPV hsq.isAlgebraicSpace
      obtain ⟨NP, hNP⟩ := hPpb (edsInter B S hS hsq).2
      refine ⟨max NU (max NV (NP + 1)) + 1, fun G hG p hp => ?_⟩
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have eV : edsEtaleHom B S hS hsq ≫ (W.1.hom ≫ h) =
          (ObjectProperty.homMk V.1.hom.hom :
            (⟨V.1.left.1, hsq.isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ h := by
        ext1
        show f ≫ W.1.hom.hom ≫ h.hom = V.1.hom.hom ≫ h.hom
        rw [← Category.assoc, hcomp]
      refine isZero_rightDerived_succ_of_eds B S hS hsq (W.1.hom ≫ h) G q ?_ ?_ ?_
      · exact hNU _ (isQuasicoherentOnSite_etaleModulePullback B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) G hG) (q + 1)
          (by omega)
      · rw [eV]
        exact hNV _ (isQuasicoherentOnSite_etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) G hG) (q + 1)
          (by omega)
      · have e2 : edsInterHom B S hS hsq ≫ (W.1.hom ≫ h) =
            (ObjectProperty.homMk (Limits.pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) :
              edsInter B S hS hsq ⟶ X) ≫ h := rfl
        rw [e2]
        exact hNP ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj G)
          (isQuasicoherentOnSite_etaleModulePullback B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) G hG) q (by omega))
  unfold HigherDirectImageBounded HasBoundedHigherDirectImages at key
  obtain ⟨N, hN⟩ := key X.2
  have e : (ObjectProperty.homMk (𝟙 X.1) : X ⟶ X) ≫ h = h := by
    ext1
    exact Category.id_comp _
  refine ⟨N, fun G hG p hp => ?_⟩
  have := hN G hG p hp
  rwa [e] at this

/-- A faithful additive functor reflects zero objects. -/
theorem _root_.CategoryTheory.Functor.isZero_of_isZero_obj_of_faithful {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Faithful] [F.Additive] {M : C}
    (h : IsZero (F.obj M)) : IsZero M :=
  (IsZero.iff_id_eq_zero M).2 <| F.map_injective <| by
    rw [F.map_id, F.map_zero]; exact h.eq_of_src _ _

/-- **The higher direct images of quasi-coherent modules along a morphism of quasi-compact
quasi-separated algebraic spaces vanish above a fixed degree.**  Restrict to an affine
surjective étale chart `V ⟶ Y`: the restriction of `R^p f_*𝓕` to `V` is the higher direct image
along the base change `V ×_Y X ⟶ V` of the restriction of `𝓕` (Stacks 03LX), which vanishes above
the bound of `exists_isZero_rightDerived_modulePushforward_of_isAffineSpace`, and restriction to a
surjective étale chart is faithful. -/
theorem exists_isZero_rightDerived_modulePushforward_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) :
    ∃ N : ℕ, ∀ G : Modules.{u, u} B S hS X.1 X.2, G.IsQuasicoherentOnSite → ∀ p : ℕ, N ≤ p →
      IsZero (((modulePushforward B S hS f).rightDerived p).obj G) := by
  obtain ⟨U, g₀, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).1 hYqc
  let g : schemeSpace U ⟶ Y := ObjectProperty.homMk g₀
  have hVaff : IsAffineSpace B S hS (schemeSpace U).1 := isAffineSpace_yoneda B S hS U hU
  let X₀ := AlgebraicSpaces.fiberProduct B S hS f g
  have hX₀qc : IsQuasiCompactSpace B S hS X₀.1 :=
    isQuasiCompactSpace_pullback B S hS hZ f.hom g.hom X.2 Y.2 hXqc
      hVaff.isQuasiCompactSpace hYqs
  have hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1 :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ f.hom g.hom X.2 (schemeSpace U).2 Y.2 hXqs
      (hVaff.isAbsolutelyQuasiSeparated B S hS hZ)
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  obtain ⟨N, hN⟩ := exists_isZero_rightDerived_modulePushforward_of_isAffineSpace B S hS hZ
    hX₀qc hX₀qs hVaff (ObjectProperty.homMk (pullback.snd f.hom g.hom) : X₀ ⟶ schemeSpace U)
  refine ⟨N, fun G hG p hp => ?_⟩
  have := faithful_etaleModulePullback.{u, u} B S hS U g het hsurj
  have := etaleModulePullback_additive.{u, u} B S hS g het
  refine (etaleModulePullback.{u, u} B S hS g het).isZero_of_isZero_obj_of_faithful ?_
  refine IsZero.of_iso ?_
    ((moduleHigherPushforwardEtaleBaseChangeIso B S hS _ _ f g sq het p).app G).symm
  exact hN _ (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ G hG) p hp

end AlgebraicGeometry.Space

end
