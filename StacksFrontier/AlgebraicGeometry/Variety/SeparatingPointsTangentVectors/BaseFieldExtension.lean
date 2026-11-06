module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical

/-!
# The closed-immersion criterion of degree two over a field that is not algebraically closed

Let `k` be a field, `X` proper over `k` with `H⁰(X, 𝒪_X) = k` and `ℒ` an invertible module on `X`.
[Stacks, Tag 0E8T] proves that a morphism `φ : X ⟶ Y` realizing the complete linear system of `ℒ`
is a closed immersion when `k` is algebraically closed and `H⁰(X, ℒ)` surjects onto the sections
over every degree-two zero-dimensional closed subscheme. This file removes the hypothesis on `k`:
it suffices that the surjectivity holds after base change to an algebraic closure `k̄`.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_pinned_of_span_of_surjectsOnDegreeTwo_baseChange`: if
  `φ` realizes a `k`-spanning family of sections of `ℒ` and the degree-two hypothesis holds on
  `X_{k̄}` for the pulled-back module, then `φ` is a closed immersion.
* `AlgebraicGeometry.isRelativelyVeryAmple_of_generatesStalks_of_surjectsOnDegreeTwo_baseChange`:
  consequently a globally generated `ℒ` satisfying the degree-two hypothesis on `X_{k̄}` is very
  ample over `k`.

## References

* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample (IsInvertibleModule)

universe u

namespace AlgebraicGeometry

/-- The canonical isomorphism `f^* g^* ≅ (f ≫ g)^*` carries the double pullback of a global section
to its pullback along the composite. -/
private theorem pullbackComp_hom_app_pullbackSectionTop {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Z.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ⊤)
        (pullbackSectionTop f ((Scheme.Modules.pullback g).obj M) (pullbackSectionTop g M s)) =
      pullbackSectionTop (f ≫ g) M s := by
  rw [← pullbackSectionTop_comp f g M s]
  exact SheafOfModules.iso_hom_app_apply_inv ((Scheme.Modules.pullbackComp f g).app M) (op ⊤) _

/-- **The closed-immersion criterion of [Stacks, Tag 0E8T] over an arbitrary field.** Let `X` be
proper over `k` with `H⁰(X, 𝒪_X) = k`, let `φ : X ⟶ Y` be a morphism over `k` to a separated
`k`-scheme with `θ : φ^* ℳ ≅ ℒ` carrying the pullbacks of sections `Tᵢ` of `ℳ` to a family `tᵢ`
spanning `H⁰(X, ℒ)` over `k`. If on every base change `X_{k̄}` to an algebraic closure the pullback
of `ℒ` surjects onto the sections over every degree-two zero-dimensional closed subscheme, then
`φ` is a closed immersion. -/
theorem isClosedImmersion_of_pinned_of_span_of_surjectsOnDegreeTwo_baseChange {k : Type u}
    [Field k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop)] (q : Y ⟶ Spec (.of k)) [IsSeparated q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p) (M : Y.Modules) (L : X.Modules) [IsInvertibleModule X L]
    (θ : (Scheme.Modules.pullback φ).obj M ≅ L) {ι : Type u} (T : ι → Γ(M, ⊤))
    (t : ι → Γ(L, ⊤)) (hpin : ∀ i, θ.hom.app ⊤ (pullbackSectionTop φ M (T i)) = t i)
    (hspan : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      ∀ σ : Γ(L, ⊤), σ ∈ Submodule.span k (Set.range t))
    (hsurj : ∀ (X' : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of (AlgebraicClosure k))),
      IsPullback g' f' p (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) →
        SurjectsOnDegreeTwo f' ((Scheme.Modules.pullback g').obj L)) :
    IsClosedImmersion φ := by
  let K := AlgebraicClosure k
  let φK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ρ := pullback.snd φK q
  let qK := pullback.fst φK q
  let φ' := pullback.fst ρ φ
  let g' := pullback.snd ρ φ
  have hsq : IsPullback g' (φ' ≫ qK) p φK := by
    have := (IsPullback.of_hasPullback ρ φ).flip.paste_vert (IsPullback.of_hasPullback φK q).flip
    rwa [hφ] at this
  have hsurj' : SurjectsOnDegreeTwo (φ' ≫ qK) ((Scheme.Modules.pullback g').obj L) :=
    hsurj _ g' _ hsq
  have : IsProper (φ' ≫ qK) := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have hφK : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) φK := by
    refine ⟨⟨⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let L' := (Scheme.Modules.pullback g').obj L
  let M' := (Scheme.Modules.pullback ρ).obj M
  have hw : φ' ≫ ρ = g' ≫ φ := pullback.condition
  let θ' : (Scheme.Modules.pullback φ').obj M' ≅ L' :=
    (Scheme.Modules.pullbackComp φ' ρ).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
      ((Scheme.Modules.pullbackComp g' φ).app M).symm ≪≫ (Scheme.Modules.pullback g').mapIso θ
  let T' : ι → Γ(M', ⊤) := fun i => pullbackSectionTop ρ M (T i)
  let t' : ι → Γ(L', ⊤) := fun i => pullbackSectionTop g' L (t i)
  have hpin' : ∀ i, θ'.hom.app ⊤ (pullbackSectionTop φ' M' (T' i)) = t' i := by
    intro i
    change ((Scheme.Modules.pullback g').map θ.hom).val.app (op ⊤)
      (((Scheme.Modules.pullbackComp g' φ).inv.app M).val.app (op ⊤)
        (((Scheme.Modules.pullbackCongr hw).hom.app M).val.app (op ⊤)
          (((Scheme.Modules.pullbackComp φ' ρ).hom.app M).val.app (op ⊤)
            (pullbackSectionTop φ' M' (T' i))))) = _
    rw [pullbackComp_hom_app_pullbackSectionTop φ' ρ M (T i),
      pullbackSectionTop_congr hw M (T i), pullbackSectionTop_comp g' φ M (T i),
      pullbackSectionTop_naturality g' θ.hom (pullbackSectionTop φ M (T i))]
    exact congrArg (pullbackSectionTop g' L) (hpin i)
  have hspan' : letI : Module K Γ(L', ⊤) := Module.compHom _ (baseRingMap (φ' ≫ qK))
      ∀ σ : Γ(L', ⊤), σ ∈ Submodule.span K (Set.range t') := by
    have : Flat φK := hφK.1.2
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
      (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mpr
        (Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X L)
    have hLc : L.IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
    have hLq : L.IsQuasicoherent := isQuasicoherent_of_isCoherent L
    let : Algebra Γ(X, ⊤) Γ(pullback ρ φ, ⊤) := g'.appTop.hom.toAlgebra
    let : Module Γ(X, ⊤) Γ(L', ⊤) := Module.compHom _ g'.appTop.hom
    have : IsScalarTower Γ(X, ⊤) Γ(pullback ρ φ, ⊤) Γ(L', ⊤) :=
      ⟨fun a b m => mul_smul (g'.appTop.hom a) b m⟩
    let lin : Γ(L, ⊤) →ₗ[Γ(X, ⊤)] Γ(L', ⊤) :=
      { toFun := pullbackSectionTop g' L
        map_add' := pullbackSectionTop_add g' L
        map_smul' := fun a s => pullbackSectionTop_smul g' L a s }
    have hbc : IsBaseChange Γ(pullback ρ φ, ⊤) lin :=
      Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections hsq L
        (fun r => by rw [appLE_top_top_eq_appTop]; rfl) lin
        (fun a => (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom_top g' L a).symm)
    let : Module K Γ(L', ⊤) := Module.compHom _ (baseRingMap (φ' ≫ qK))
    let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
    have hcomm : ∀ c : k, g'.appTop (baseRingMap p c) =
        baseRingMap (φ' ≫ qK) (algebraMap k K c) := by
      intro c
      have e : (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ g'.appTop =
          CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
            (φ' ≫ qK).appTop := by
        rw [← Scheme.Hom.comp_appTop, hsq.w, Scheme.Hom.comp_appTop, ← Category.assoc,
          ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
      exact congrArg (fun χ => χ.hom c) e
    have hI : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (φ' ≫ qK).appTop) :=
      isIso_globalSections_baseChange k K g' _ p hsq
    have hsurjK : Function.Surjective (baseRingMap (φ' ≫ qK)) :=
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (φ' ≫ qK).appTop)).2
    intro σ
    refine hbc.inductionOn σ (motive := (· ∈ Submodule.span K (Set.range t'))) (fun m => ?_)
      (fun a n hn => ?_)
      (fun _ _ => Submodule.add_mem _)
    · induction (hspan m) using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have hca : lin (c • a) = (algebraMap k K c) • lin a := by
          change pullbackSectionTop g' L (baseRingMap p c • a) =
            baseRingMap (φ' ≫ qK) (algebraMap k K c) •
              (show Γ(L', ⊤) from pullbackSectionTop g' L a)
          rw [pullbackSectionTop_smul, hcomm]
        rw [hca]
        exact Submodule.smul_mem _ _ ha
    · obtain ⟨c, rfl⟩ := hsurjK a
      exact Submodule.smul_mem _ c hn
  have hφ' : IsClosedImmersion φ' :=
    isClosedImmersion_of_pinned_of_span (φ' ≫ qK) qK φ' rfl M' L' θ' T' t' hpin' hspan' hsurj'
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have hρ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ρ :=
    MorphismProperty.pullback_snd _ _ hφK
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (IsPullback.of_hasPullback ρ φ) hρ hφ'

/-- **Very ampleness from the degree-two criterion over an arbitrary field.** Let `X` be proper
over `k` with `H⁰(X, 𝒪_X) = k` and `ℒ` an invertible module generated by its global sections. If on
every base change `X_{k̄}` to an algebraic closure the pullback of `ℒ` surjects onto the sections
over every degree-two zero-dimensional closed subscheme, then `ℒ` is very ample over `k`. -/
theorem isRelativelyVeryAmple_of_generatesStalks_of_surjectsOnDegreeTwo_baseChange {k : Type u}
    [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop)] (L : X.Modules) [IsInvertibleModule X L]
    (hgen : Stacks.ProjectiveFromSections.GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)))
    (hsurj : ∀ (X' : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of (AlgebraicClosure k))),
      IsPullback g' f' p (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) →
        SurjectsOnDegreeTwo f' ((Scheme.Modules.pullback g').obj L)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple p L := by
  classical
  obtain ⟨n, t, ht, hspan⟩ := exists_fin_basis_generatesStalks_of_generatesStalks_id p L hgen
  obtain ⟨φ, hφ, α, hiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse t ht p
  have := hiso
  let τ := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  let θ : (Scheme.Modules.pullback φ).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅ L :=
    (Scheme.Modules.pullbackComp φ τ).app
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n) ≪≫ asIso α
  have : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
    projectiveSpaceOver_isProper n (Spec (.of k))
  have hci : IsClosedImmersion φ := by
    refine isClosedImmersion_of_pinned_of_span_of_surjectsOnDegreeTwo_baseChange p
      (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) φ hφ _ L θ
      (fun i : ULift.{u} (Fin (n + 1)) => Stacks.TwistPullbackPinned.pullbackCoordSection
        τ i.down)
      (fun i : ULift.{u} (Fin (n + 1)) => t i.down) (fun i => ?_) (fun σ => ?_) hsurj
    · rw [← hα i.down, pullbackCoordSection_eq, pullbackCoordSection_eq]
      exact congrArg (fun y => (Scheme.Modules.Hom.app α ⊤) y)
        (pullbackComp_hom_app_pullbackSectionTop φ τ _ _)
    · let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (hspan σ)
  exact Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver
    (fun m => Stacks.SymGraded.hasFreeBundleTwistOne (Spec (.of k)) m) p L
    ⟨n, φ, inferInstance, hφ, ⟨θ.symm⟩⟩

end AlgebraicGeometry

end
