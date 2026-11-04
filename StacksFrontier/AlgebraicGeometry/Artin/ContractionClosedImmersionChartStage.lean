module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartKernel
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientSurjection

/-!
# Points of a closed formal subspace over a stage of an affine chart

Let `ι : F ⟶ Q` be a closed immersion of fppf sheaves and `b : V ⟶ Q` a morphism from an
affine formal algebraic space presented as `Spf D` by an adic Noetherian ring `A`, the fibre
product `F ×_Q V` being presented by `φ : A → C`. A morphism from an object `T` of the site to a
stage `Spec (A ⧸ J)` of `Spf D` gives a point of `Q`; this file proves that the point lies in
`F` exactly when the ring map `A → A ⧸ J → Γ(T)` kills `ker φ`.

This is how the proof of **Stacks 0GHE** reads the closed immersions `W → S_{/Z}` and
`Y_{/Z} → S_{/Z}` on the infinitesimal neighbourhoods of `Z` in an affine open of `S`: their
stages are the closed subschemes cut out by the ideal `ker φ` of the chart.

## Main results

* `Ideal.closure_eq_of_isAdicRing`: every ideal of an adic Noetherian ring is closed.
* `AlgebraicGeometry.FormalSpace.exists_lift_iff_ker_le_of_stage`: the point criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Every ideal of an adic Noetherian topological ring is closed. -/
theorem Ideal.closure_eq_of_isAdicRing {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C]
    (hC : TopologicalRing.IsAdic C) (𝔞 : Ideal C) : 𝔞.closure = 𝔞 := by
  let : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  obtain ⟨⟨I, -, hIadic⟩, hT2, hCompl⟩ := hC
  have : CompleteSpace C := hCompl
  have : T2Space C := hT2
  exact Ideal.closure_eq_of_isAdic_of_isNoetherianRing hIadic 𝔞

/-- For a surjection `φ : A → C` and `K = J.map φ`, a ring map out of `A ⧸ J` killing the image of
`ker φ` kills the kernel of `A ⧸ J → C ⧸ K`. -/
private theorem Ideal.ker_quotientMap_le_of_eq_map {A C R : Type u} [CommRing A] [CommRing C]
    [CommRing R] {φ : A →+* C} (hφ : Function.Surjective φ) {J : Ideal A} {K : Ideal C}
    (hK : K = J.map φ) (hJK : J ≤ K.comap φ) (ρ : A ⧸ J →+* R)
    (h : ∀ x ∈ RingHom.ker φ, ρ (Ideal.Quotient.mk J x) = 0) :
    RingHom.ker (Ideal.quotientMap K φ hJK) ≤ RingHom.ker ρ := by
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : φ a ∈ K := Ideal.Quotient.eq_zero_iff_mem.1 (RingHom.mem_ker.1 hy)
  rw [hK, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hφ] at ha
  obtain ⟨j, hj, k, hk, rfl⟩ := Submodule.mem_sup.1 ha
  rw [RingHom.mem_ker, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
  exact h k (by simpa using hk)

namespace AlgebraicGeometry.FormalSpace

/-- If `f : X ⟶ Spec R` factors through `Spec.map q`, the induced map `R → Γ(X)` kills
`ker q`. -/
private theorem appTop_ΓSpecIso_inv_eq_zero_of_comp_specMap_eq {X : Scheme.{u}} {R R' : Type u}
    [CommRing R] [CommRing R'] (q : R →+* R') (g : X ⟶ Spec (CommRingCat.of R'))
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : g ≫ Spec.map (CommRingCat.ofHom q) = f) {x : R}
    (hx : x ∈ RingHom.ker q) : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv x) = 0 := by
  subst hf
  have key : (Spec.map (CommRingCat.ofHom q)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of R')).inv (q x) :=
    (congrArg (fun f => f.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))).symm
  show g.appTop ((Spec.map (CommRingCat.ofHom q)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv x)) = 0
  rw [key, RingHom.mem_ker.1 hx, map_zero]
  exact g.appTop.hom.map_zero

/-- A morphism `f : X ⟶ Spec R` factors through `Spec.map q` for a surjection `q : R → R'` whose
kernel the induced map `R → Γ(X)` kills. -/
private theorem exists_comp_specMap_eq_of_ker_le {X : Scheme.{u}} {R R' : Type u} [CommRing R]
    [CommRing R'] (q : R →+* R') (hq : Function.Surjective q) (f : X ⟶ Spec (CommRingCat.of R))
    (h : RingHom.ker q ≤ RingHom.ker ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom) :
    ∃ g : X ⟶ Spec (CommRingCat.of R'), g ≫ Spec.map (CommRingCat.ofHom q) = f :=
  ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (q.liftOfSurjective hq ⟨_, h⟩)), by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      q.liftOfSurjective_comp hq ⟨_, h⟩]
    exact Space.toSpecΓ_comp_specMap_appTop f⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] bigFppfOver_subcanonical

/-- The inclusion of a quotient stage into the formal spectrum, with target the formal spectrum
itself rather than the colimit defining it. -/
noncomputable def formalSpectrumStageInclusion {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (formalSpectrumDiagram D).obj J ⟶ formalSpectrum D :=
  formalSpectrumInclusion D J

/-- **Points of a closed formal subspace over a stage of a chart.** Let `ι : F ⟶ Q` be a
closed immersion, `b : V ⟶ Q`, `V ≅ Spf D` for an adic Noetherian ring `A`, and let
`φ : A → C` present the fibre product `F ×_Q V`, `C` adic Noetherian. A morphism `v` from an
object `T` of the site to the stage `Spec (A ⧸ J)` gives a point of `Q`; it lifts to `F`
exactly when the ring map `A → A ⧸ J → Γ(T)` kills `ker φ`. -/
theorem exists_lift_iff_ker_le_of_stage {F Q V : FppfSheaf B S hS} {ι : F ⟶ Q}
    (hι : IsClosedImmersion B S hS ι) (b : V ⟶ Q)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hAa : TopologicalRing.IsAdic A) (hAw : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} (eV : V ≅ formalSpectrum D)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] (hCa : TopologicalRing.IsAdic C) {E : QuotientSystem B S hS C}
    {P : FppfSheaf B S hS} {a : P ⟶ F} {t : P ⟶ V} (hsq : IsPullback a t ι b)
    (eU : P ≅ formalSpectrum E) (φ : ContinuousHom D E)
    (hφ : t = eU.hom ≫ formalSpectrumMap hAw φ ≫ eV.inv)
    {T : BigFppfOver B S hS} (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (v : T ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J)) :
    (∃ m : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ F,
      m ≫ ι = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map v ≫
        formalSpectrumStageInclusion D J ≫ eV.inv ≫ b) ↔
      ∀ x ∈ RingHom.ker φ.toRingHom,
        ((BigFppfOver.toScheme B S hS).map v).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J.1))).inv (Ideal.Quotient.mk J.1 x)) = 0 := by
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have hsurj : Function.Surjective φ.toRingHom :=
    surjective_of_isClosedImmersion_chart B S hS hι hsq hAa hCa hAw eU eV φ hφ
  obtain ⟨K, hK, hJK, sqst⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS hAw
    (Rig.weaklyAdmissible_of_isAdicRing hCa) D E φ
    (isClosedImmersion_formalSpectrumMap_and_isTaut B S hS hι hsq hAa hCa hAw eU eV φ hφ).2 J
  have hKeq : K.1 = J.1.map φ.toRingHom := by rw [hK, Ideal.closure_eq_of_isAdicRing hCa]
  let st := φ.stageMap J K hJK
  have hU : eU.hom ≫ formalSpectrumMap hAw φ = t ≫ eV.hom := by
    rw [hφ]
    simp
  constructor
  · rintro ⟨m, hm⟩
    let m' : Y.obj T ⟶ P :=
      hsq.lift m (Y.map v ≫ formalSpectrumStageInclusion D J ≫ eV.inv)
        (by simpa only [Category.assoc] using hm)
    have hm'' : (m' ≫ eU.hom) ≫ formalSpectrumMap hAw φ =
        Y.map v ≫ formalSpectrumStageInclusion D J := by
      rw [Category.assoc, hU, ← Category.assoc, hsq.lift_snd, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    obtain ⟨n₀, hn₀'⟩ : ∃ n₀, Y.map n₀ = sqst.lift (m' ≫ eU.hom) (Y.map v) hm'' :=
      ⟨_, (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).map_preimage _⟩
    have hn₀ : n₀ ≫ (BigAffineFppf.inclusion B S hS).map st = v :=
      (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective (by
        rw [Functor.map_comp]
        show Y.map n₀ ≫ _ = _
        rw [hn₀']
        exact sqst.lift_snd _ _ _)
    exact fun x hx => appTop_ΓSpecIso_inv_eq_zero_of_comp_specMap_eq
      (Ideal.quotientMap K.1 φ.toRingHom hJK) ((BigFppfOver.toScheme B S hS).map n₀)
      (by rw [← hn₀]; rfl)
      (by rw [RingHom.mem_ker, Ideal.quotientMap_mk, RingHom.mem_ker.1 hx, map_zero])
  · intro hker
    obtain ⟨g, hg⟩ := exists_comp_specMap_eq_of_ker_le (Ideal.quotientMap K.1 φ.toRingHom hJK)
      (Ideal.quotientMap_surjective hsurj) ((BigFppfOver.toScheme B S hS).map v)
      (Ideal.ker_quotientMap_le_of_eq_map hsurj hKeq hJK _ hker)
    let n₀ : T ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage K) :=
      Over.homMk (ObjectProperty.homMk g) (by
        rw [← Over.w ((BigAffineFppf.inclusion B S hS).map st), ← Category.assoc, ← Over.w v]
        congr 1
        exact ObjectProperty.hom_ext _ hg)
    have hn₀ : n₀ ≫ (BigAffineFppf.inclusion B S hS).map st = v :=
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ hg)
    refine ⟨Y.map n₀ ≫ formalSpectrumStageInclusion E K ≫ eU.inv ≫ a, ?_⟩
    have e1 : eU.inv ≫ a ≫ ι = formalSpectrumMap hAw φ ≫ eV.inv ≫ b := by
      rw [hsq.w, hφ]
      simp
    have hw : formalSpectrumStageInclusion E K ≫ formalSpectrumMap hAw φ =
      Y.map ((BigAffineFppf.inclusion B S hS).map st) ≫ formalSpectrumStageInclusion D J := sqst.w
    rw [Category.assoc, Category.assoc, Category.assoc, e1, reassoc_of% hw, ← Y.map_comp_assoc,
      hn₀]

end AlgebraicGeometry.FormalSpace
