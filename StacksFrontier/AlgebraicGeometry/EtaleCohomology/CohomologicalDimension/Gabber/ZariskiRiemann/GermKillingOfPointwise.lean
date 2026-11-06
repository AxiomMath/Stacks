module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.PointwiseGermDeath
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# From pointwise germ death to finite families and killed-subsheaf systems

Travaux de Gabber, Exposé XVIII-A, last remark of §2. On a proper model `Y` of
`η = Spec (Frac B)` with `G = R^q j_* F` and geometric closed fibre `Y_Ω`, the pointwise
statement `AlgebraicGeometry.Scheme.ZariskiRiemann.PointwiseGermDeath` says that the germ of a
section `g ∈ G(V)` at every point `z` of `V ×_Y Y_Ω` of large transcendence degree dies on a
refinement, after restriction to an étale `W ⟶ V` reaching `z`. This file draws its two
consequences.

* **Finite families over a quasi-compact `V`.** The base change `W ×_Y Y_Ω ⟶ V ×_Y Y_Ω` is étale,
  hence open, so its image is an open neighbourhood of `z`. When `V` is quasi-compact,
  `V ×_Y Y_Ω` is quasi-compact and locally Noetherian (étale over `Y_Ω`, which is of finite type
  over `Ω`), hence a Noetherian space, in which every subset is compact; finitely many of the
  `W` therefore reach every point of large transcendence degree. This is the statement of
  `AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling` for quasi-compact `V`.
* **The killed-subsheaf system.** The construction of
  `AlgebraicGeometry.Scheme.ZariskiRiemann.killedSubsheafSystemBound_of_germKilling` uses only
  one point at a time, so it runs on `PointwiseGermDeath` directly; this gives
  `ZariskiRiemannKilling n` and, with the homological half of the limit step
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.LerayKilling`), Exposé XVIII-A, Corollary 1.2.

`GermKilling` itself quantifies over every étale `V ⟶ Y`, quasi-compact or not; for a
non-quasi-compact `V` the pointwise statement gives no finite family, since each point may need
its own refinement and infinitely many refinements need not have a common refinement killing
all the germs at once.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.GermKillingQuasiCompact` — the statement of
  `GermKilling` for quasi-compact étale `V ⟶ Y`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_finite_germ_cover_of_compactSpace`
  — over a quasi-compact `V`, finitely many of the pointwise étale neighbourhoods suffice.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.germKillingQuasiCompact_of_pointwiseGermDeath` —
  `PointwiseGermDeath n` gives the statement of `GermKilling n` for every quasi-compact `V`
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.GermKillingQuasiCompact`).
* `AlgebraicGeometry.Scheme.ZariskiRiemann.killedSubsheafSystemBound_of_pointwiseGermDeath`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.zariskiRiemannKilling_of_pointwiseGermDeath` —
  `KilledSubsheafSystemBound n` and `ZariskiRiemannKilling n` from `PointwiseGermDeath n`, given
  that refinements of proper models are cofiltered.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.fractionFieldVanishingBound_of_pointwiseGermDeath` —
  Exposé XVIII-A, Corollary 1.2 (`FractionFieldVanishingBound n`) from `PointwiseGermDeath n`,
  `RefinementsCofiltered` and `LerayKilling`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

namespace ProperModel

/-- The base change to `Y_Ω` of an étale `W ⟶ V` over `Y` is étale. -/
private theorem etale_pullbackMap_etale {B : Type u} [CommRing B] (M : ProperModel B)
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of B)) {V W : M.Y.Etale} (h : W ⟶ V) :
    Etale (pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
      h.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (MorphismProperty.Over.w h).symm) (by simp)) :=
  MorphismProperty.pullbackMap (P := @Etale) (inferInstance : Etale h.left)
    (inferInstance : Etale (𝟙 (pullback M.f x))) (MorphismProperty.Over.w h).symm
    (Category.id_comp _).symm

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)

omit [IsDomain B] in
/-- The base change `V ×_Y Y_Ω` of a quasi-compact étale `V ⟶ Y` to the geometric closed fibre
is a Noetherian space: it is quasi-compact, and étale over `Y_Ω`, which is of finite type over
the field `Ω`. -/
theorem noetherianSpace_pullback_etale {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of B))
    (V : M.Y.Etale) [CompactSpace V.left] :
    NoetherianSpace ↥(pullback V.hom (pullback.fst M.f x)) := by
  have : IsAffineHom x := isAffineHom_of_isAffine x
  have : QuasiCompact (pullback.fst M.f x) := inferInstance
  have : QuasiCompact (pullback.fst V.hom (pullback.fst M.f x)) := inferInstance
  have : CompactSpace ((𝟭 Scheme).obj V.left) := ‹CompactSpace V.left›
  have : CompactSpace ↥(pullback V.hom (pullback.fst M.f x)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom (pullback.fst M.f x))
  have hP : LocallyOfFiniteType M.f := M.isProper.toLocallyOfFiniteType
  have hΩ : IsLocallyNoetherian (Spec (.of Ω)) := inferInstance
  have h₁ : LocallyOfFiniteType (pullback.snd M.f x) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback M.f x) hP
  have : IsLocallyNoetherian (pullback M.f x) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.snd M.f x) h₁ hΩ
  have : IsLocallyNoetherian (pullback V.hom (pullback.fst M.f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd V.hom (pullback.fst M.f x))
  have : IsNoetherian (pullback V.hom (pullback.fst M.f x)) := {}
  exact IsNoetherian.noetherianSpace

omit [IsDomain B] in
/-- The base change to `Y_Ω` of an étale `W ⟶ V` over `Y` has open image in `V ×_Y Y_Ω`. -/
theorem isOpen_range_pullbackMap_etale {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of B)) {V W : M.Y.Etale} (h : W ⟶ V) :
    IsOpen (Set.range (pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
      h.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (MorphismProperty.Over.w h).symm) (by simp))) := by
  set pm := pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
      h.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (MorphismProperty.Over.w h).symm) (by simp)
  have : Etale pm := etale_pullbackMap_etale M x h
  have : Flat pm := inferInstance
  have : LocallyOfFinitePresentation pm := inferInstance
  have : UniversallyOpen pm := UniversallyOpen.of_flat pm
  exact pm.isOpenMap.isOpen_range

variable (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
  (q e : ℕ)

omit [IsDomain B] in
/-- **Over a quasi-compact `V`, finitely many pointwise neighbourhoods suffice.** Suppose that at
every point `z` of `V ×_Y Y_Ω` over a point of large transcendence degree, the section `g` of
`R^q j_* F` dies on a refinement after restriction to an étale `W ⟶ V` whose base change to
`Y_Ω` reaches `z`. If `V` is quasi-compact, finitely many such `W` reach all those points: the
images of their base changes are open, and every subset of the Noetherian space `V ×_Y Y_Ω` is
compact. -/
theorem exists_finite_germ_cover_of_compactSpace {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of B)) (V : M.Y.Etale) [CompactSpace V.left]
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op V))
    (hpt : ∀ z : ↥(pullback V.hom (pullback.fst M.f x)),
      (¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
          pullback.snd V.hom (pullback.fst M.f x) z ∈
            Scheme.trdegLESet Ω (pullback.snd M.f x) a) →
      ∃ (W : M.Y.Etale) (h : W ⟶ V),
        (∃ (M' : ProperModel B) (φ : Refinement M' M),
          φ.Kills F q (germHom W
            ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map h.op g))) ∧
        ∃ z' : ↥(pullback W.hom (pullback.fst M.f x)),
          pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
            h.left (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact (MorphismProperty.Over.w h).symm)
            (by simp) z' = z) :
    ∃ (m : ℕ) (W : Fin m → M.Y.Etale) (h : ∀ k, W k ⟶ V),
      (∀ k, ∃ (M' : ProperModel B) (φ : Refinement M' M),
        φ.Kills F q (germHom (W k)
          ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map
            (h k).op g))) ∧
      ∀ z : ↥(pullback V.hom (pullback.fst M.f x)),
        (¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
            pullback.snd V.hom (pullback.fst M.f x) z ∈
              Scheme.trdegLESet Ω (pullback.snd M.f x) a) →
        ∃ (k : Fin m) (z' : ↥(pullback (W k).hom (pullback.fst M.f x))),
          pullback.map (W k).hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
            (h k).left (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact (MorphismProperty.Over.w (h k)).symm)
            (by simp) z' = z := by
  classical
  have := M.noetherianSpace_pullback_etale x V
  set S : Set ↥(pullback V.hom (pullback.fst M.f x)) := {z | ¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
    pullback.snd V.hom (pullback.fst M.f x) z ∈ Scheme.trdegLESet Ω (pullback.snd M.f x) a}
  choose W hW hkill z' hz' using fun z : S ↦ hpt z.1 z.2
  let pmf : ∀ i : S, pullback (W i).hom (pullback.fst M.f x) ⟶
      pullback V.hom (pullback.fst M.f x) := fun i ↦
    pullback.map (W i).hom (pullback.fst M.f x) V.hom (pullback.fst M.f x) (hW i).left (𝟙 _)
      (𝟙 _) (by rw [Category.comp_id]; exact (MorphismProperty.Over.w (hW i)).symm) (by simp)
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact S).elim_finite_subcover
    (fun i : S ↦ Set.range (pmf i)) (fun i ↦ M.isOpen_range_pullbackMap_etale x (hW i))
    (fun z hz ↦ Set.mem_iUnion.2 ⟨⟨z, hz⟩, z' ⟨z, hz⟩, hz' ⟨z, hz⟩⟩)
  let ε := t.equivFin
  refine ⟨t.card, fun k ↦ W (ε.symm k), fun k ↦ hW (ε.symm k), fun k ↦ hkill _,
    fun z hz ↦ ?_⟩
  obtain ⟨i, hi, w, hw⟩ := Set.mem_iUnion₂.1 (ht hz)
  obtain ⟨k, hk⟩ : ∃ k : Fin t.card, ∃ w' : ↥(pullback (W (ε.symm k).1).hom (pullback.fst M.f x)),
      pmf (ε.symm k).1 w' = z :=
    ⟨ε ⟨i, hi⟩, by rw [ε.symm_apply_apply]; exact ⟨w, hw⟩⟩
  exact ⟨k, hk⟩

end ProperModel

/-- **`GermKilling` over quasi-compact étale `V`.** The statement of
`AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling` with the étale `V ⟶ Y` restricted to
quasi-compact ones: for every quasi-compact étale `V ⟶ Y` and every section `g` of `R^q j_* F`
over `V`, finitely many étale `V_k ⟶ V`, each with a refinement killing `g|V_k`, whose base
changes to `Y_Ω` reach every point of `V ×_Y Y_Ω` of large transcendence degree. -/
def GermKillingQuasiCompact (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ),
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ Spec (.of B)),
          x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B ∧
          ∀ (V : M.Y.Etale) [CompactSpace V.left]
            (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op V)),
            ∃ (m : ℕ) (W : Fin m → M.Y.Etale) (h : ∀ k, W k ⟶ V),
              (∀ k, ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
                φ.Kills F q (ProperModel.germHom (W k)
                  ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map
                    (h k).op g))) ∧
              ∀ z : ↥(pullback V.hom (pullback.fst M.f x)),
                (¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
                    pullback.snd V.hom (pullback.fst M.f x) z ∈
                      Scheme.trdegLESet Ω (pullback.snd M.f x) a) →
                ∃ (k : Fin m) (z' : ↥(pullback (W k).hom (pullback.fst M.f x))),
                  pullback.map (W k).hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
                    (h k).left (𝟙 _) (𝟙 _)
                    (by rw [Category.comp_id]; exact (MorphismProperty.Over.w (h k)).symm)
                    (by simp) z' = z

/-- **`GermKilling` over quasi-compact étale `V`, from pointwise germ death.** The étale
neighbourhoods given point by point by `PointwiseGermDeath n` have open images in `V ×_Y Y_Ω`,
and finitely many of them suffice when `V` is quasi-compact. -/
theorem germKillingQuasiCompact_of_pointwiseGermDeath {n : ℕ} (h : PointwiseGermDeath.{u} n) :
    GermKillingQuasiCompact.{u} n := by
  intro B _ _ _ _ e he he0 hn F hF M q
  obtain ⟨Ω, _, _, x, hx, hpt⟩ := h B e he he0 hn F hF M q
  exact ⟨Ω, inferInstance, inferInstance, x, hx, fun V _ g ↦
    M.exists_finite_germ_cover_of_compactSpace F q e x V g (hpt V g)⟩

/-- **The killed-subsheaf system from pointwise germ death.** If refinements of proper models are
cofiltered, `PointwiseGermDeath n` gives `KilledSubsheafSystemBound n`. The system is the one of
`AlgebraicGeometry.Scheme.ZariskiRiemann.killedSubsheafSystemBound_of_germKilling` (finite sets
of killed germs), and the support bound on its cokernel is checked one geometric point at a time:
a germ of `R^q j_* F` at a geometric point `s` of `Y_Ω` of large transcendence degree is the germ
of a section `g` over an étale neighbourhood `V`; pointwise germ death at the point of
`V ×_Y Y_Ω` given by `s` gives an étale `W ⟶ V` through which `s` lifts (étale maps lift
geometric points), and `g|W` lies in the subsheaf generated by the killed germ `(W, g|W)`. -/
theorem killedSubsheafSystemBound_of_pointwiseGermDeath {n : ℕ}
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hgerm : PointwiseGermDeath.{u} n) : KilledSubsheafSystemBound.{u} n := by
  classical
  intro B _ _ _ _ e he he0 hn F hF M q
  obtain ⟨Ω, _, _, x, hx, hpt⟩ := hgerm B e he he0 hn F hF M q
  refine ⟨Finset (ProperModel.KilledGerm M F q), inferInstance, inferInstance,
    ProperModel.killedGermDiagram M F q, ProperModel.killedGermι M F q,
    ProperModel.exists_refinement_kills_killedGermι M F q (hcof B),
    ProperModel.mono_colimitDesc_killedGermDiagram M F q, Ω, inferInstance, inferInstance, x, hx,
    ?_⟩
  set G := ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F
  intro y hy
  by_contra hbad
  obtain ⟨s, hs, hnz⟩ := hy
  apply hnz
  apply isZero_smallEtaleStalkAb_etaleAbelianInverseImage
  apply isZero_smallEtaleStalkAb_cokernel_of_forall_germ
  intro V ℓ g
  have hℓ : ℓ.left ≫ V.hom = s.hom ≫ pullback.fst M.f x := Over.w ℓ
  let z₀ : Spec (.of s.residueField) ⟶ pullback V.hom (pullback.fst M.f x) :=
    pullback.lift ℓ.left s.hom hℓ
  have hz₀snd : z₀ ≫ pullback.snd V.hom (pullback.fst M.f x) = s.hom := pullback.lift_snd _ _ _
  have hz₀fst : z₀ ≫ pullback.fst V.hom (pullback.fst M.f x) = ℓ.left := pullback.lift_fst _ _ _
  obtain ⟨W, hW, hkill, z', hz'⟩ := hpt V g (z₀ (default : Spec (.of s.residueField))) (by
    rintro ⟨a, ha1, ha2, ha3⟩
    refine hbad ⟨a, ha1, ha2, ?_⟩
    have hsnd : pullback.snd V.hom (pullback.fst M.f x) (z₀ default) = s.hom default := by
      rw [← Scheme.Hom.comp_apply, hz₀snd]
    rwa [hsnd, hs] at ha3)
  let pm := pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
    hW.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact (MorphismProperty.Over.w hW).symm)
    (by simp)
  have hpm : Etale pm := ProperModel.etale_pullbackMap_etale M x hW
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed pm z₀ z' hz'
  have hlsnd : l ≫ pullback.snd W.hom (pullback.fst M.f x) = s.hom := by
    simpa [pm, hz₀snd] using congrArg (· ≫ pullback.snd V.hom (pullback.fst M.f x)) hl
  have hlfst : l ≫ pullback.fst W.hom (pullback.fst M.f x) ≫ hW.left = ℓ.left := by
    simpa [pm, hz₀fst] using congrArg (· ≫ pullback.fst V.hom (pullback.fst M.f x)) hl
  let t₀ : ProperModel.KilledGerm M F q := ⟨⟨W, G.obj.map hW.op g⟩, hkill⟩
  obtain ⟨w, hw⟩ := ProperModel.exists_colimitDesc_killedGermDiagram_eq M F q t₀
  refine ⟨W, hW, Over.homMk (l ≫ pullback.fst _ _) ?_, w, ?_, hw⟩
  · simp [pullback.condition, reassoc_of% hlsnd]
  · change Over.homMk _ _ ≫ (Etale.forget _).map hW = ℓ
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).trans hlfst)

/-- **The geometric half of the Zariski–Riemann limit step from pointwise germ death**: if
refinements of proper models are cofiltered, `PointwiseGermDeath n` gives
`ZariskiRiemannKilling n`. -/
theorem zariskiRiemannKilling_of_pointwiseGermDeath {n : ℕ}
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hgerm : PointwiseGermDeath.{u} n) : ZariskiRiemannKilling.{u} n :=
  zariskiRiemannKilling_of_killedSubsheafSystemBound
    (killedSubsheafSystemBound_of_pointwiseGermDeath hcof hgerm)

/-- **Exposé XVIII-A, Corollary 1.2, from pointwise germ death**: given that refinements of proper
models are cofiltered and the homological half of the limit step (`LerayKilling`),
`PointwiseGermDeath n` gives `FractionFieldVanishingBound n`. -/
theorem fractionFieldVanishingBound_of_pointwiseGermDeath {n : ℕ}
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hL : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
      [StrictlyHenselianLocalRing B], LerayKilling B)
    (hgerm : PointwiseGermDeath.{u} n) : FractionFieldVanishingBound.{u} n :=
  fractionFieldVanishingBound_of_zariskiRiemannKilling
    (zariskiRiemannKilling_of_pointwiseGermDeath hcof hgerm) hL

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
