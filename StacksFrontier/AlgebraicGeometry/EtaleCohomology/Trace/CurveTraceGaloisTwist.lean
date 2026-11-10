module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantPullbackDegree

/-!
# The trace `H²(C, μ_n) ≅ ℤ/n` is invariant under semilinear automorphisms

Let `C` be a smooth proper curve over an algebraically closed field `K` and `s : C ⟶ C` an
automorphism of schemes lying over an automorphism `τ` of `K` (`s ≫ q = q ≫ Spec τ`), for example
`id × Spec σ` on a base change `C' ×_{k'} K` for `σ ∈ Aut(K/k')`. Then `tr(s^* y) = tr(y)` for
`y ∈ H²(C, μ_n)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Kummer

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {n : ℕ} (hn : IsUnit (n : K))

/-- **The trace is invariant under an automorphism lying over an automorphism of the field.** -/
theorem smoothProperCurveTrace_rootsOfUnityPullbackMap_of_twist (s : C ⟶ C) [IsIso s]
    (τ : K ≃+* K) (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
    (y : Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} C n) 2) :
    smoothProperCurveTrace q hn
        (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} s n 2 y) =
      smoothProperCurveTrace q hn y := by
  rw [smoothProperCurveTrace_rootsOfUnityPullbackMap q q hn hn s 1 (fun L => by
    rw [Stacks.Picard.picardDegree_schemePullbackClassHom_of_twist q _ s τ hs, one_mul]) y,
    one_smul]

end Stacks.Kummer

namespace Stacks.EtaleCohomology

section RootsOfUnity

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of k))
  (gY : Y ⟶ Spec (.of k)) (π : X ⟶ Y) (τ : k ≃+* k)
  (hπ : π ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

include hπ in
/-- The image of `ζ` on an étale `Y`-scheme `V`, pulled back along `V ×_Y X ⟶ V`, is the image of
`τ(ζ)` on `V ×_Y X`, for `π : X ⟶ Y` lying over `Spec τ`. -/
theorem map_rootOn_pullbackFst_of_twist (V : Y.Etale) :
    Units.map (pullback.fst V.hom π).appTop.hom.toMonoidHom (Stacks.Kummer.rootOn gY hζ hn V) =
      Stacks.Kummer.rootOn gX (hζ.map_of_injective τ.injective) hn
        ((smallEtaleBaseChange π).obj V) := by
  have hs : (pullback.fst V.hom π).appTop.hom.comp (Stacks.Kummer.structMap gY V) =
      (Stacks.Kummer.structMap gX ((smallEtaleBaseChange π).obj V)).comp τ.toRingHom := by
    rw [Stacks.Kummer.structMap, Stacks.Kummer.structMap, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_ofHom τ.toRingHom, ← CommRingCat.hom_comp]
    congr 1
    rw [← Category.assoc (CommRingCat.ofHom τ.toRingHom), Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    change _ ≫ (pullback.fst V.hom π ≫ V.hom ≫ gY).appTop =
      _ ≫ (pullback.snd V.hom π ≫ gX ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)).appTop
    rw [pullback.condition_assoc, hπ]
  ext
  exact DFunLike.congr_fun hs ζ

include hπ in
/-- **The constant-sheaf comparison is the comparison on `μ_n`, over a field automorphism**: for
`π` lying over `Spec τ`, `m ↦ ζ^m` on `Y` pulls back to `m ↦ τ(ζ)^m` on `X`. -/
theorem inverseImage_rootsOfUnityConstantHom_comp_comparison_of_twist :
    (etaleAbelianInverseImage.{u, 0} π).map (Stacks.Kummer.rootsOfUnityConstantHom gY hζ hn) ≫
        Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} π n =
      (etaleAbelianInverseImageConstantIso.{u, 0} π).hom.app _ ≫
        Stacks.Kummer.rootsOfUnityConstantHom gX (hζ.map_of_injective τ.injective) hn := by
  rw [← cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} X n), Category.assoc, Category.assoc,
    Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, ← Functor.map_comp_assoc,
    Stacks.Kummer.rootsOfUnityConstantHom_comp_ι, Stacks.Kummer.rootsOfUnityConstantHom_comp_ι]
  apply (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal Y)).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} π)).homEquiv _ _).injective
  rw [constantSheaf_comp_homEquiv_apply.{u, 0}, constantSheaf_comp_homEquiv_apply.{u, 0},
    Adjunction.homEquiv_naturality_left,
    Stacks.Kummer.multiplicativeInverseImageComparison_transpose,
    Adjunction.homEquiv_naturality_right, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ← Category.assoc, ← Category.assoc, constantSheafSection_comp_homEquiv_constantIso.{u, 0} π]
  change (toSheafify Y.smallEtaleTopology _ ≫ (Stacks.Kummer.rootSheafHom gY hζ hn).hom).app _ ≫
      _ = (toSheafify X.smallEtaleTopology _ ≫
        (Stacks.Kummer.rootSheafHom gX (hζ.map_of_injective τ.injective) hn).hom).app _
  rw [Stacks.Kummer.toSheafify_rootSheafHom, Stacks.Kummer.toSheafify_rootSheafHom]
  ext ⟨m⟩
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
  change (multiplicativeDirectImageComparison.{u, 0} π).hom.app (op (etaleSiteTerminal Y))
      (Stacks.Kummer.rootHom gY hζ hn _ (z : ZMod n)) =
    Stacks.Kummer.rootHom gX (hζ.map_of_injective τ.injective) hn _ (z : ZMod n)
  rw [Stacks.Kummer.rootHom_intCast, Stacks.Kummer.rootHom_intCast, map_zsmul,
    multiplicativeDirectImageComparison_app_ofUnit,
    map_rootOn_pullbackFst_of_twist gX gY π τ hπ hζ hn]
  rfl

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

include hπ in
/-- **Pullback on `H^q(-, ℤ/n)` is pullback on `H^q(-, μ_n)`, over a field automorphism.** -/
theorem sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo_of_twist (q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod n)) q) :
    Sheaf.H.map (Stacks.Kummer.rootsOfUnityConstantHom gX (hζ.map_of_injective τ.injective) hn) q
        (etaleConstantCohomologyPullback π (ZMod n) q x) =
      rootsOfUnityPullbackMap.{u, 0, u + 1} π n q
        (Sheaf.H.map (Stacks.Kummer.rootsOfUnityConstantHom gY hζ hn) q x) := by
  rw [rootsOfUnityPullbackMap_apply, Stacks.Kummer.etaleCohomologyRestrictionMap_sheafHMap]
  change Sheaf.H.map _ q (Sheaf.H.map _ q (etaleCohomologyRestrictionMap.{u, 0, u + 1} π _ q x)) = _
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    inverseImage_rootsOfUnityConstantHom_comp_comparison_of_twist gX gY π τ hπ hζ hn]

end RootsOfUnity

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {n : ℕ} (hn : IsUnit (n : K)) {ζ : K}
  (hζ : IsPrimitiveRoot ζ n)

/-- **The trace on `H²(C, ℤ/n)` under a semilinear automorphism**: for `s : C ⟶ C` lying over
`Spec τ`, the trace through `τ(ζ)` of `s^* x` is the trace through `ζ` of `x`. -/
theorem curveConstantTrace_etaleConstantCohomologyPullback_of_twist (s : C ⟶ C) [IsIso s]
    (τ : K ≃+* K) (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) 2) :
    curveConstantTrace q hn (hζ.map_of_injective τ.injective)
        (etaleConstantCohomologyPullback s (ZMod n) 2 x) =
      curveConstantTrace q hn hζ x := by
  change Stacks.Kummer.smoothProperCurveTrace q hn
      (sheafHRootsOfUnityConstantAddEquiv q (hζ.map_of_injective τ.injective)
        (Stacks.Kummer.neZero_of_isUnit hn) 2 (etaleConstantCohomologyPullback s (ZMod n) 2 x)) =
    Stacks.Kummer.smoothProperCurveTrace q hn
      (sheafHRootsOfUnityConstantAddEquiv q hζ (Stacks.Kummer.neZero_of_isUnit hn) 2 x)
  rw [sheafHRootsOfUnityConstantAddEquiv_apply, sheafHRootsOfUnityConstantAddEquiv_apply,
    sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo_of_twist q q s τ hs hζ]
  exact Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap_of_twist q hn s τ hs _

/-- **A semilinear automorphism carries the fundamental class for `ζ` to the one for `τ(ζ)`.** -/
theorem etaleConstantCohomologyPullback_curveFundamentalClass_of_twist (s : C ⟶ C) [IsIso s]
    (τ : K ≃+* K) (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) :
    etaleConstantCohomologyPullback s (ZMod n) 2 (curveFundamentalClass q hn hζ) =
      curveFundamentalClass q hn (hζ.map_of_injective τ.injective) := by
  apply (curveConstantTrace q hn (hζ.map_of_injective τ.injective)).injective
  rw [curveConstantTrace_etaleConstantCohomologyPullback_of_twist q hn hζ s τ hs,
    curveConstantTrace_curveFundamentalClass, curveConstantTrace_curveFundamentalClass]

/-- **`s^* Θ_A(φ)` for `ζ` is `Θ_A(φ)` for `τ(ζ)`**, `s` a semilinear automorphism over
`Spec τ`. -/
theorem etaleConstantCohomologyPullback_curveConstantClass_of_twist (s : C ⟶ C) [IsIso s]
    (τ : K ≃+* K) (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) (A : Type)
    [AddCommGroup A] (φ : ZMod n →+ A) :
    etaleConstantCohomologyPullback s A 2 (curveConstantClass q hn hζ A φ) =
      curveConstantClass q hn (hζ.map_of_injective τ.injective) A φ := by
  change etaleConstantCohomologyPullback s A 2 (Sheaf.H.map (etaleConstantSheafMap C φ) 2 _) =
    Sheaf.H.map (etaleConstantSheafMap C φ) 2 _
  rw [etaleConstantCohomologyPullback_sheafHMap,
    etaleConstantCohomologyPullback_curveFundamentalClass_of_twist q hn hζ s τ hs]

end Trace

end Stacks.EtaleCohomology

end
