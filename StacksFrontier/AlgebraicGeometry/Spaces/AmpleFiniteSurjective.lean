module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource

/-!
# Ampleness along a finite surjective morphism of algebraic spaces

Let `R` be a Noetherian ring, `f : Y ⟶ X` a finite surjective morphism of algebraic spaces proper
over `R`, and `𝓛` an invertible `𝒪_X`-module.  Stacks 0GFB asserts that `X` is a scheme and `𝓛` is
ample if and only if `Y` is a scheme and `f^*𝓛` is ample.

A finite morphism is representable, so if `X` is a scheme so is `Y`, and the inverse image of an
ample module along a finite — indeed along an affine — morphism of schemes is ample (Stacks 0892).
Conversely, by Stacks 0GFA it suffices that every coherent `𝒪_X`-module `𝓕` has
`H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for all large `n`.  That property is closed under extensions, passes to
direct summands and holds on zero modules, so by the dévissage of Stacks 07US it suffices to check
it on the direct images `i_*ℐ` of quasi-coherent sheaves of ideals on reduced closed subspaces
`i : Z ⟶ X` with `|Z|` irreducible, by Noetherian induction; the induction step is that of
Stacks 07UT for `𝒢 = f'_*𝒪_{Y ×_X Z}` (`AlgebraicGeometry.Space.property_idealPushforward_of_lt`),
which needs the property for `i_*f'_*𝓜 = f_*i'_*𝓜` with `𝓜` coherent on `Y ×_X Z`.  There the
projection formula gives `f_*𝓖 ⊗ 𝓛^{⊗ n} ≅ f_*(𝓖 ⊗ (f^*𝓛)^{⊗ n})`, the cohomology of a direct
image along the affine `f` is that on `Y` (Stacks 0D2U), and on `Y` it vanishes for large `n` by
Serre's vanishing theorem, the implication (1) ⟹ (2) of Stacks 0GFA on `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_isAmple_modulePullback_of_isFinite`: if `X` is a scheme with
  `𝓛` ample and `f` is finite, then `Y` is a scheme with `f^*𝓛` ample.
* `AlgebraicGeometry.Space.exists_isAmple_of_isAmple_modulePullback`: the converse, for `f` finite
  surjective and `X` proper over a Noetherian affine scheme.
* `AlgebraicGeometry.Space.exists_isAmple_iff_exists_isAmple_modulePullback`: **Stacks 0GFB**.

## Implementation notes

The source assumes both `X` and `Y` proper over `R`; only properness of `X` is assumed here, that
of `Y` following since a finite morphism is proper.  "Proper over a Noetherian ring `R`" is read
as a proper morphism to the algebraic space represented by an affine object `V` of the site whose
ring of functions `Γ(V, 𝒪_V) = R` is Noetherian, as in
`AlgebraicGeometry.Space.tfae_isAmple_of_isProper_toAffine`.

## References

* [Stacks Project, Tag 0GFB](https://stacks.math.columbia.edu/tag/0GFB)
* [Stacks Project, Tag 0GFA](https://stacks.math.columbia.edu/tag/0GFA)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The implication (1) ⟹ (2) of Stacks 0GFB.**  Let `f : Y ⟶ X` be a finite morphism of
algebraic spaces and `𝓛` an invertible `𝒪_X`-module.  If `X` is a scheme `U` and the restriction of
`𝓛` to `U` is ample, then `Y` is a scheme and the restriction of `f^*𝓛` to it is ample.

`f` is representable, so `Y ≅ h_U ×_X Y` is represented by a scheme `U'`, and `U' ⟶ U` is a finite
morphism of schemes (Stacks 03ZQ); the restriction of `f^*𝓛` to `U'` is the inverse image of the
restriction of `𝓛` to `U`, which is ample by Stacks 0892 for the affine morphism `U' ⟶ U`
(`Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom`). -/
theorem exists_isAmple_modulePullback_of_isFinite {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFinite B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U eX.hom)]
    (hamp : Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U eX.hom)) :
    ∃ (U' : BigFppfOver B S hS) (eY : yoneda.obj U' ≅ Y.1)
      (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U')
        (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom)),
      Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U')
        (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom) := by
  have hfin := (isFinite_iff_representable B S hS f.hom Y.2 X.2).1 hf
  have hrep := hfin.1
  have hsq := hrep.isPullback eX.hom
  have : IsIso (hrep.fst eX.hom) := hsq.isIso_fst_of_isIso
  let r := hrep.snd eX.hom
  have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map r) :=
    hfin.2.property eX.hom _ _ hsq
  let eY := asIso (hrep.fst eX.hom)
  obtain ⟨e₂⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hL U (hrep.pullback eX.hom)
    eX.hom r
  let e : baseChangeModule B S hS ((modulePullback B S hS f).obj L) (hrep.pullback eX.hom)
      eY.hom ≅ Stacks.AmpleLocallyClosed.pullbackModule ((BigFppfOver.toScheme B S hS).map r)
        (baseChangeModule B S hS L U eX.hom) :=
    (baseChangeModuleCompIso B S hS f L _ eY.hom).symm ≪≫
      eqToIso (congrArg (fun p => baseChangeModule B S hS L (hrep.pullback eX.hom) p) hsq.w) ≪≫ e₂
  have hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback eX.hom))
      (baseChangeModule B S hS ((modulePullback B S hS f).obj L) (hrep.pullback eX.hom) eY.hom) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  exact ⟨hrep.pullback eX.hom, eY, hinv, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e.symm).mp
    (Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom _ _ hamp)⟩

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **The implication (2) ⟹ (1) of Stacks 0GFB.**  Let `X` be an algebraic space proper over an
affine scheme `V` with Noetherian ring of functions, `f : Y ⟶ X` finite and surjective and `𝓛` an
invertible `𝒪_X`-module.  If `Y` is a scheme `U'` and the restriction of `f^*𝓛` to `U'` is ample,
then `X` is a scheme and the restriction of `𝓛` to it is ample. -/
theorem exists_isAmple_of_isAmple_modulePullback
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {X Y : AlgebraicSpaces B S hS} (pX : X ⟶ schemeSpace V) (hpX : IsProper B S hS pX.hom)
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (U' : BigFppfOver B S hS) (eY : yoneda.obj U' ≅ Y.1)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U')
      (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom)]
    (hamp : Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U')
      (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom)) :
    ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
      (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)),
      Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  have hXN := isNoetherian_of_isProper_toAffine B S hS V inferInstance pX hpX
  have hpY : IsProper B S hS (f ≫ pX).hom := isProper_comp' B S hS f.hom pX.hom X.2
    (schemeSpace V).2 (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS Y.2 X.2 f.hom hf).1 hpX
  have hYN := isNoetherian_of_isProper_toAffine B S hS V inferInstance (f ≫ pX) hpY
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let T : ℕ → (Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2) := fun n =>
    (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
      (invertibleTensorPower B S hS X.1 X.2 L n)
  have hTeq : ∀ n, (T n).IsEquivalence := fun n =>
    @Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ _
      (@Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
        (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _ L
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) n)
  let P : Modules.{u, u} B S hS X.1 X.2 → Prop := fun F =>
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsZero ((Γ.rightDerived 1).obj
      (twistStep B S hS X.1 X.2 L n F))
  have hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M := fun M hM =>
    ⟨0, fun n _ => Functor.map_isZero (Γ.rightDerived 1) (Functor.map_isZero (T n) hM)⟩
  have hext : ClosedUnderCoherentExtensions B S hS X P := by
    rintro E hE - - - ⟨n₁, h₁⟩ ⟨n₃, h₃⟩
    refine ⟨max n₁ n₃, fun n hn => ?_⟩
    have hE' : (E.map (T n)).ShortExact := hE.map_of_exact (T n)
    exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE' Γ 1
      (h₁ n (le_of_max_le_left hn)) (h₃ n (le_of_max_le_right hn))
  have hsum : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N → ∀ r : ℕ,
      0 < r → P (⨁ fun _ : Fin r => N) → P N := by
    rintro N - r hr ⟨n₀, h⟩
    exact ⟨n₀, fun n hn =>
      isZero_obj_of_isZero_obj_biproduct (T n ⋙ Γ.rightDerived 1) N hr (h n hn)⟩
  have hbase : ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
      (M : Modules.{u, u} B S hS (pullback f (closedSubfunctorι B S hS hZ)).1
        (pullback f (closedSubfunctorι B S hS hZ)).2),
      M.IsQuasicoherentOnSite → IsCoherent B S hS _ _ M →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          ((modulePushforward B S hS (pullback.snd f (closedSubfunctorι B S hS hZ))).obj M)) := by
    intro Z hZ M _ hMc
    let iZ := closedSubfunctorι B S hS hZ
    have sq := IsPullback.of_hasPullback f iZ
    let i' := pullback.fst f iZ
    have hi'f : IsFinite B S hS i'.hom :=
      isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq.flip)
        (isFinite_of_isClosedImmersion B S hS _ hZ.2)
    let N := (modulePushforward B S hS i').obj M
    have hNc : IsCoherent B S hS Y.1 Y.2 N :=
      isCoherent_modulePushforward_of_isFinite' B S hS i' hi'f hYN.2.2 M hMc
    obtain ⟨n₀, hn₀⟩ := exists_isZero_rightDerived_twistStep_of_isAmple V (f ≫ pX) hpY
      ((modulePullback B S hS f).obj L) U' eY hamp N hNc
    have hfN : P ((modulePushforward B S hS f).obj N) := by
      refine ⟨n₀ + 1, fun n hn => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
      let Q := twistStep B S hS Y.1 Y.2 ((modulePullback B S hS f).obj L) ((d + 1 : ℕ) : ℤ) N
      have hQ := hn₀ (d + 1) (by omega) 1 one_pos
      have : N.IsQuasicoherentOnSite := hNc.toIsQuasicoherentOnSite
      have : ((modulePullback B S hS f).obj L).IsQuasicoherentOnSite :=
        isQuasicoherentOnSite_of_isInvertible B S hS Y _ (isInvertible_modulePullback_obj B S hS f
          L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL))
      have := isQuasicoherentOnSite_tensorPow_of_pos ((modulePullback B S hS f).obj L)
        inferInstance (d + 1) (Nat.succ_pos d)
      have hQqc : Q.IsQuasicoherentOnSite :=
        SheafOfModules.IsQuasicoherentOnSite.of_iso
          (twistStepSuccIsoTensorPow Y ((modulePullback B S hS f).obj L) d N).symm
          (isQuasicoherentOnSite_tensorObj B S hS Y.1 Y.2 N _)
      have hfQ := (isZero_rightDerived_iff_of_isAffineHom B S hS f hf.isAffineHom Q hQqc 1).1 hQ
      exact hfQ.of_iso ((Γ.rightDerived 1).mapIso
        (twistStepModulePushforwardIsoOfIsFinite f hf L d N))
    have hfNc : IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS f).obj N) :=
      isCoherent_modulePushforward_of_isFinite' B S hS f hf hXN.2.2 N hNc
    let e₀ : (modulePushforward B S hS f).obj N ≅ (modulePushforward B S hS iZ).obj
        ((modulePushforward B S hS (pullback.snd f iZ)).obj M) :=
      (modulePushforwardCompIso B S hS i' f).app M ≪≫
        eqToIso (congrArg (fun g => (modulePushforward B S hS g).obj M) sq.w) ≪≫
        ((modulePushforwardCompIso B S hS (pullback.snd f iZ) iZ).app M).symm
    exact property_of_iso B S hS X P hzero hext hfNc (isCoherent_of_iso B S hS X.2 e₀ hfNc) e₀
      hfN
  have hP : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F → P F := fun F hF =>
    property_of_ideal_pushforward_and_extensions B S hS X hXN P (Or.inr hzero)
      hext (fun Z hZ hint I => forall_property_idealPushforward_of_step B S hS B.contains_terminal
        X hXN P hzero hext (fun Z' hZ' hint' I' hsmall => property_idealPushforward_of_lt B S hS
          B.contains_terminal X Y hXN f hf hfs P hzero hext hsum Z' hZ' (hbase Z' hZ') hint' I'
          hsmall) Z hZ hint I) F hF
  refine exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep B.contains_terminal
    X hXN L fun F hF => ?_
  obtain ⟨n₀, hn₀⟩ := hP F hF
  exact ⟨n₀ + 1, by omega, hn₀ _ (by omega)⟩

/-- **Stacks 0GFB.**  Let `R` be a Noetherian ring, `X` an algebraic space proper over `R` — a
proper `pX : X ⟶ h_V` with `V` affine and `Γ(V, 𝒪_V) = R` — and `f : Y ⟶ X` a finite surjective
morphism of algebraic spaces.  Let `𝓛` be an invertible `𝒪_X`-module.  Then `X` is a scheme and `𝓛`
is ample on it if and only if `Y` is a scheme and `f^*𝓛` is ample on it.

A scheme is an object `U` of the site with an isomorphism `h_U ≅ X`, and `𝓛` is ample on it when
its restriction to `U` (`AlgebraicGeometry.Space.baseChangeModule`) is invertible and ample.  The
source also assumes `Y` proper over `R`; that follows, a finite morphism being proper. -/
@[stacks 0GFB]
theorem exists_isAmple_iff_exists_isAmple_modulePullback
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {X Y : AlgebraicSpaces B S hS} (pX : X ⟶ schemeSpace V) (hpX : IsProper B S hS pX.hom)
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L] :
    (∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
      (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)),
      Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)) ↔
    ∃ (U' : BigFppfOver B S hS) (eY : yoneda.obj U' ≅ Y.1)
      (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U')
        (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom)),
      Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U')
        (baseChangeModule B S hS ((modulePullback B S hS f).obj L) U' eY.hom) :=
  ⟨fun ⟨U, eX, _, hamp⟩ => exists_isAmple_modulePullback_of_isFinite f hf L U eX hamp,
    fun ⟨U', eY, _, hamp⟩ =>
      exists_isAmple_of_isAmple_modulePullback V pX hpX f hf hfs L U' eY hamp⟩

end AlgebraicGeometry.Space

end
