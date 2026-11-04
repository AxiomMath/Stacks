module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.PointwiseGermDeath
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterAbhyankarBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Germs of `R^q j_* F` at the centers of a valuation ring, and their death along refinements

This file sets up the stalk side of the germ-killing step of Gabber's Zariski–Riemann proof of
Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (last remark of §2). Let `B` be a domain with
fraction field `K`, `η = Spec K`, `M` a proper model `f : Y ⟶ Spec B` with point `j : η ⟶ Y`,
`F` an abelian sheaf on `η_étale` and `G = R^q j_* F`.

* **Stalks** (Stacks 03Q9 for `j`): for a geometric point `s` of `Y`,
  `G_s ≅ H^q(η ×_Y Spec 𝒪^{sh}_{Y,s}, F|)`
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`;
  `j` is quasi-compact and quasi-separated since `Y` is separated over `Spec B`).
* **Transition maps**: a refinement `π : Y' ⟶ Y` and a geometric point `s'` of `Y'` give the map
  `G_{π s'} = (π⁻¹ G)_{s'} ⟶ (R^q j'_* F)_{s'}`, the stalk of the base change map
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition`). A
  refinement kills a morphism `ι : K ⟶ G` exactly when `π⁻¹ ι` followed by the base change map
  vanishes on every stalk
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.kills_iff_forall_stalk`).
* **Germ death at a valuation ring** (`AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath`,
  a statement): for a valuation ring `V` of `K` dominating `B` with `rat.rank Γ_V < q`, a
  geometric point `v` of `Spec V` at its closed point and the geometric points `v ≫ c_Y` at the
  centers `c_Y : Spec V ⟶ Y`, every germ of `G` at `v ≫ c_Y` dies at `v ≫ c_{Y'}` on some
  refinement `Y' ⟶ Y`. In the source: the colimit over the models of
  `η ×_Y Spec 𝒪^{sh}_{Y, c_Y}` is `Spec (K ⊗_V V^{sh}) = Spec (Frac V^{sh})`, as `V` is the
  colimit of the local rings `𝒪_{Y, c_Y}`
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRange`) and strict henselization commutes
  with filtered colimits; `V^{sh}` is a strictly henselian valuation ring with the value group of
  `V`, so `H^q(Frac V^{sh}, F) = 0`
  (`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing_of_valuationRing`), and
  cohomology commutes with the limit (Stacks 09YQ).
* **Germ death at centers of small rank**
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.CenteredGermDeath`, a statement): a section of `G`
  over an étale `V ⟶ Y` dies on one refinement near a point `w ∈ V` over a point `y` of the
  closed fibre at which every centered valuation ring has rational rank `< q`. In the source it
  follows from `ValuationGermDeath`, the quasi-compactness of the Zariski–Riemann fibre over `y`
  and the properness of the models.
* **Pointwise germ death**: `CenteredGermDeath n` implies
  `AlgebraicGeometry.Scheme.ZariskiRiemann.PointwiseGermDeath n`
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.pointwiseGermDeath_of_centeredGermDeath`): by
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.rank_valueGroup_lt_of_not_mem_trdegLESet`
  every valuation ring centered at the image of a point of `Y_Ω` outside the locus
  `⋃ {E_a : a + q ≤ e, a + 1 ≤ e}` has rational rank `< q`.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenteredGermDeath`

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_forall_smallEtaleStalkAb_map_eq_zero` — a morphism of
  abelian étale sheaves vanishing on all stalks at geometric points is zero.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.kills_iff_forall_stalk`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.exists_geometricPoint_closedPoint`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.pointwiseGermDeath_of_centeredGermDeath`

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A morphism of abelian étale sheaves vanishing on all stalks is zero**: its kernel inclusion
is an isomorphism on every stalk, the stalk functors preserving kernels, hence an isomorphism. -/
public theorem eq_zero_of_forall_smallEtaleStalkAb_map_eq_zero {X : Scheme.{u}}
    {P Q : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : P ⟶ Q)
    (h : ∀ s : GeometricPoint X, (smallEtaleStalkAb s.hom).map φ = 0) : φ = 0 := by
  have hk : IsIso (kernel.ι φ) := by
    refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s => ?_
    have e : (smallEtaleStalkAb s.hom).map (kernel.ι φ) =
        (PreservesKernel.iso (smallEtaleStalkAb s.hom) φ).hom ≫
          kernel.ι ((smallEtaleStalkAb s.hom).map φ) := by
      simp
    rw [e]
    have : IsIso (kernel.ι ((smallEtaleStalkAb s.hom).map φ)) := by
      refine ⟨⟨kernel.lift _ (𝟙 _) (by rw [h s, comp_zero]), ?_, kernel.lift_ι _ _ _⟩⟩
      apply equalizer.hom_ext
      simp
    infer_instance
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)

/-- The point `j : η ⟶ Y` of a proper model is quasi-separated (its composite with `Y ⟶ Spec B`
is a morphism of affine schemes). -/
instance quasiSeparated_j : QuasiSeparated M.j := by
  have : QuasiSeparated (M.j ≫ M.f) := by rw [M.fac]; infer_instance
  exact QuasiSeparated.of_comp M.j M.f

/-- **Stacks 03Q9 at the point of a model.** For a geometric point `s` of `Y`, the stalk of
`R^q j_* F` at `s` is `H^q(η ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹F)`, with
`p : η ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ η` the projection (the strict henselization taken in the big étale
site `AlgebraicGeometry.BigEtaleSite.containing Y`). -/
def stalkRightDerivedIsoStrictHenselization
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (s : GeometricPoint M.Y) :
    (smallEtaleStalkAb s.hom).obj (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange
          (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j s))
          Ab.{u + 1}).rightDerived q).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource
          (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j s)).obj F) :=
  letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} (Spec (.of (FractionRing B)))
  (smallEtaleStalkAb s.hom).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforwardAb M.j)
        (smallEtaleDerivedPushforwardAb M.j) (smallEtaleDerivedPushforwardAbUnit M.j)
        (fun K : CochainComplex
            (Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology Ab.{u + 1}) ℤ =>
          Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) F q).symm ≪≫
    stalkHigherDirectImageIsoStrictHenselization _ _ M.j s F q

/-- **The transition map of stalks along a refinement.** For a refinement `π : Y' ⟶ Y` and a
geometric point `s'` of `Y'`, the map `(R^q j_* F)_{π s'} = (π⁻¹ R^q j_* F)_{s'} ⟶
(R^q j'_* F)_{s'}`: the stalk of the base change map of the square `𝟙 ≫ j = j' ≫ π`. -/
def Refinement.stalkTransition {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y) :
    (smallEtaleStalkAb (s ≫ φ.π)).obj
        (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) ⟶
      (smallEtaleStalkAb s).obj (((etaleAbelianDirectImage.{u, 0} M'.j).rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F)) :=
  ((smallEtaleStalkPullbackAbIso φ.π s).app _).inv ≫
    (smallEtaleStalkAb s).map ((smallEtalePullbackAbIsoEtaleAbelianInverseImage φ.π).hom.app _ ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
        (by rw [Category.id_comp, φ.fac]) F q)

omit [IsDomain B] in
/-- **Killing is checked on stalks.** A refinement `π` kills `ι : K ⟶ R^q j_* F` exactly when
`π⁻¹ ι` followed by the base change map vanishes on the stalk at every geometric point of
`Y'`. -/
theorem Refinement.kills_iff_forall_stalk {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) :
    φ.Kills F q ι ↔ ∀ s : GeometricPoint M'.Y,
      (smallEtaleStalkAb s.hom).map ((etaleAbelianInverseImage.{u, 0} φ.π).map ι ≫
        etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
          (by rw [Category.id_comp, φ.fac]) F q) = 0 := by
  refine ⟨fun h s => ?_, eq_zero_of_forall_smallEtaleStalkAb_map_eq_zero _⟩
  rw [Refinement.Kills] at h
  rw [h, Functor.map_zero]

end ProperModel

/-- **Germ death at a valuation ring** (the analytic input of Gabber's germ-killing step). Let
`B` be a domain with `n` invertible, `F` an abelian sheaf on `η = Spec (Frac B)` killed by `n`,
`M` a proper model, `q` a degree and `V` a valuation ring of `Frac B` dominating `B` with
`rat.rank Γ_V < q`. For a geometric point `v : Spec Ω ⟶ Spec V` at the closed point, every germ
of `R^q j_* F` at the geometric point `v ≫ c_Y` at the center of `V` dies along some refinement
`Y' ⟶ Y`: its image under the transition map at `v ≫ c_{Y'}` vanishes (the stalks at
`v ≫ c_Y` and at `(v ≫ c_{Y'}) ≫ π` being identified by `c_Y = c_{Y'} ≫ π`).

In the source: `colim_{Y'} (R^q j'_* F)_{v ≫ c_{Y'}} = colim H^q(η ×_{Y'} Spec 𝒪^{sh}_{Y', c_{Y'}})
= H^q(Spec (Frac V^{sh}), F) = 0`, by Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`),
`V = colim 𝒪_{Y', c_{Y'}}` (`AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRange`) with
strict henselization commuting with filtered colimits, Stacks 09YQ, and
`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing_of_valuationRing` for the
strictly henselian valuation ring `V^{sh}`, whose value group is that of `V`. -/
def ValuationGermDeath (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B], IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ) (V : ValuationSubring (FractionRing B))
        (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
        IsLocalHom (valuationSubringBaseMap V hV) →
        Module.rank ℤ (Additive (ValuationRing.ValueGroup V (FractionRing B))ˣ) < q →
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ Spec (.of V)),
          v (default : Spec (.of Ω)) = IsLocalRing.closedPoint V →
          ∀ γ : (smallEtaleStalkAb (v ≫ M.center V hV)).obj
              (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F),
            ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
              (eqToHom (by rw [φ.center_eq hV, Category.assoc]) ≫
                φ.stalkTransition F q (v ≫ M'.center V hV)) γ = 0

/-- **Germ death where every centered valuation ring has small rank** (the Zariski–Riemann
core of Gabber's germ-killing step, with the transcendence-degree bookkeeping removed). For `B` a
strictly henselian Noetherian local domain with `n` invertible, `F` killed by `n` on `η`, a
proper model `M`, a degree `q`, an étale `V ⟶ Y`, a section `g` of `R^q j_* F` over `V` and a
point `w ∈ V` over a point `y ∈ Y` of the closed fibre such that every valuation ring of
`Frac B` dominating `B` and centered at `y` has rational rank `< q`: there are an étale
`W ⟶ V` whose image contains `w` and a refinement of `M` killing the morphism
`ℤ_W ⟶ R^q j_* F` of `g|W`.

In the source: at each valuation ring `V'` centered at `y` the germ dies at the center of `V'` on
some refinement (`AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath`), hence on an open
neighbourhood of that center; the valuation rings whose center lies in that neighbourhood form an
open subset of the Zariski–Riemann space, whose fibre over `y` is quasi-compact, so one common
refinement `Y'` works at all points of `Y'` over `y` (points outside the closure of `j'(η)`
having zero stalks); the support of the pulled back section is closed in `V ×_Y Y'` and its image
in `V` is closed (`Y' ⟶ Y` is proper) and misses `w`. -/
def CenteredGermDeath (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B],
    IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ) (V : M.Y.Etale)
        (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op V))
        (w : ↥V.left),
        M.f (V.hom w) = IsLocalRing.closedPoint B →
        (∀ (V' : ValuationSubring (FractionRing B))
            (hV' : ∀ b : B, algebraMap B (FractionRing B) b ∈ V'),
            IsLocalHom (valuationSubringBaseMap V' hV') → M.centerPoint V' hV' = V.hom w →
            Module.rank ℤ (Additive (ValuationRing.ValueGroup V' (FractionRing B))ˣ) < q) →
        ∃ (W : M.Y.Etale) (h : W ⟶ V) (w' : ↥W.left), h.left w' = w ∧
          ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
            φ.Kills F q (ProperModel.germHom W
              ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map h.op g))

/-- The spectrum of a field has at most one point. -/
private theorem subsingleton_spec_of_field (Ω : Type u) [Field Ω] :
    Subsingleton ↥(Spec (CommRingCat.of Ω)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

/-- A geometric point of a local ring over its closed point: `Spec Ω ⟶ Spec B` for an algebraic
closure `Ω` of the residue field. -/
theorem exists_geometricPoint_closedPoint (B : Type u) [CommRing B] [IsLocalRing B] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ Spec (.of B)),
      x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B := by
  let Ω := AlgebraicClosure (IsLocalRing.ResidueField B)
  let φ : B →+* Ω := (algebraMap (IsLocalRing.ResidueField B) Ω).comp (IsLocalRing.residue B)
  have : IsLocalHom (CommRingCat.ofHom φ).hom := RingHom.isLocalHom_comp _ _
  refine ⟨Ω, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom φ), ?_⟩
  have := subsingleton_spec_of_field Ω
  rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
  exact Spec_closedPoint

/-- **Pointwise germ death from germ death at centers of small rank**: by Abhyankar's inequality
on the geometric closed fibre
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.rank_valueGroup_lt_of_not_mem_trdegLESet`),
every valuation ring centered at the image of a point of `Y_Ω` outside the locus
`⋃ {E_a : a + q ≤ e, a + 1 ≤ e}` has rational rank `< q`, and a point of `W` over the image of
`z` in `V` lifts to a point of `W ×_Y Y_Ω` over `z`. -/
theorem pointwiseGermDeath_of_centeredGermDeath {n : ℕ} (h : CenteredGermDeath.{u} n) :
    PointwiseGermDeath.{u} n := by
  intro B _ _ _ _ e he he0 hn F hF M q
  obtain ⟨Ω, _, _, x, hx⟩ := exists_geometricPoint_closedPoint B
  refine ⟨Ω, inferInstance, inferInstance, x, hx, fun V g z hz => ?_⟩
  have := subsingleton_spec_of_field Ω
  set w := pullback.fst V.hom (pullback.fst M.f x) z with hw
  set yΩ := pullback.snd V.hom (pullback.fst M.f x) z with hyΩ
  have hwy : V.hom w = pullback.fst M.f x yΩ := by
    rw [hw, hyΩ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hclosed : M.f (V.hom w) = IsLocalRing.closedPoint B := by
    rw [hwy, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Subsingleton.elim (pullback.snd M.f x yΩ) default, hx]
  obtain ⟨W, hWV, w', hw', M', φ, hkill⟩ := h B hn F hF M q V g w hclosed fun V' hV' _ hc =>
    M.rank_valueGroup_lt_of_not_mem_trdegLESet V' hV' Ω x yΩ (hc.trans hwy) e he he0 q hz
  refine ⟨W, hWV, ⟨M', φ, hkill⟩, ?_⟩
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := hWV.left)
    (g := pullback.fst V.hom (pullback.fst M.f x)) w' z hw'
  have hcond : pullback.fst hWV.left (pullback.fst V.hom (pullback.fst M.f x)) ≫ W.hom =
      (pullback.snd hWV.left (pullback.fst V.hom (pullback.fst M.f x)) ≫
        pullback.snd V.hom (pullback.fst M.f x)) ≫ pullback.fst M.f x := by
    rw [← MorphismProperty.Over.w hWV, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, pullback.condition]
  let ψ := pullback.lift _ _ hcond
  have hψ : ψ ≫ pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
      hWV.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (MorphismProperty.Over.w hWV).symm) (by simp) =
      pullback.snd hWV.left (pullback.fst V.hom (pullback.fst M.f x)) := by
    apply pullback.hom_ext
    · simp only [ψ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact pullback.condition
    · simp only [ψ, Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨ψ p, ?_⟩
  rw [← Scheme.Hom.comp_apply, hψ, hp2]

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
