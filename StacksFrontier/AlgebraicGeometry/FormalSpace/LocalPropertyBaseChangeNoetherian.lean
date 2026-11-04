module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartFibreProductCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented

/-!
# Base change of a local property of morphisms of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` and `Q` be local properties of
morphisms of `WAdm^{Noeth}` (Remark 0ANI) with `P` stable under base change by `Q`
(**Stacks 0GBG**): for `B → A` with `P` and `B → C` with `Q`, the completed tensor product
`A ⊗̂_B C` is adic Noetherian and `C → A ⊗̂_B C` has `P`. For morphisms `f : X ⟶ Y` and
`g : Z ⟶ Y` of locally Noetherian formal algebraic spaces over `S` such that the equivalent
conditions of Stacks 0ANG hold for `f` and `P` and for `g` and `Q`, they hold for the second
projection `X ×_Y Z ⟶ Z` and `P`. With `Q` the property that always holds this is the variant
of Stacks 0GBD for locally Noetherian formal algebraic spaces (**Stacks 0GBF**).

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isAffineEtaleCover_pullback_isNoetherian`: the fibre
  product of an affine chart of `Y` with a locally Noetherian `X` has an atlas of Noetherian
  affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.conditions_pullback_snd_of_isStableUnderBaseChangeBy`:
  **Stacks 0GBG**, the statement drawn there.
* `AlgebraicGeometry.FormalSpace.conditions_pullback_snd_of_isStableUnderBaseChangeNoetherian`:
  **Stacks 0GBF**, the variant of Stacks 0GBD for locally Noetherian formal algebraic spaces.

## Implementation notes

A local property in the sense of Situation 0CBA is a property of arrows of a category of
topological rings, invariant under isomorphism of source and target; that invariance is the
hypothesis `hPiso`, in the shape of Situation 0CBA, beside the three axioms recorded by
`TopologicalRing.PropertyIsLocalNoetherian`.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable étale map into `V ×_Y X`, composed with `pr₂`, is representable étale. -/
private theorem isRepresentableEtale_comp_pullback_snd {X Y V T : FppfSheaf B S hS}
    {v : V ⟶ Y} {f : X ⟶ Y} {u : T ⟶ pullback v f} (hu : IsRepresentableEtale B S hS u)
    (hv : IsRepresentableEtale B S hS v) :
    IsRepresentableEtale B S hS (u ≫ pullback.snd v f) :=
  IsRepresentableEtale.comp B S hS hu (isRepresentableEtale_pullback_snd B S hS v f hv)

/-- **Noetherian charts of `V ×_Y X`.** If `V ⟶ Y` is a representable étale map from an affine
formal algebraic space to a formal algebraic space and `X` is locally Noetherian, then
`V ×_Y X` has an affine étale covering as in Definition 0AIM by Noetherian affine formal
algebraic spaces. -/
theorem exists_isAffineEtaleCover_pullback_isNoetherian {X Y V : FppfSheaf B S hS}
    (v : V ⟶ Y) (f : X ⟶ Y) (hv : IsRepresentableEtale B S hS v)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hX : IsLocallyNoetherian B S hS X) :
    ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ pullback v f),
      IsAffineEtaleCover B S hS U a ∧ ∀ i, IsNoetherian B S hS (U i) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hXf, L, Xl, xl, hXlaff, hXlet, hXlsurj, hXlnoeth⟩ := hX
  have hφ : IsRepresentableEtale B S hS (pullback.snd v f) :=
    isRepresentableEtale_pullback_snd B S hS v f hv
  have hQ : ∀ l, IsFormalAlgebraicSpace B S hS (pullback (xl l) (pullback.snd v f)) := fun l ↦
    isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS (xl l) (pullback.snd v f) hXf
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hXlaff l))
      (isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS v f hY hV hXf)
  choose M T c hTaff hTet hTsurj using fun l ↦ (hQ l).2
  refine ⟨Σ l, M l, fun n ↦ T n.1 n.2,
    fun n ↦ c n.1 n.2 ≫ pullback.snd (xl n.1) (pullback.snd v f),
    ⟨fun n ↦ hTaff n.1 n.2,
      fun n ↦ isRepresentableEtale_comp_pullback_snd B S hS (hTet n.1 n.2) (hXlet n.1), ?_⟩,
    fun n ↦ ?_⟩
  · exact isLocallySurjective_sigmaDesc_comp' B S hS
      (fun l ↦ pullback.snd (xl l) (pullback.snd v f)) c
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.snd v f) xl hXlsurj) hTsurj
  · have he : IsRepresentableEtale B S hS (c n.1 n.2 ≫ pullback.fst (xl n.1) (pullback.snd v f)) :=
      IsRepresentableEtale.comp B S hS (hTet n.1 n.2)
        (isRepresentableEtale_of_isPullback B S hS
          (IsPullback.of_hasPullback (xl n.1) (pullback.snd v f)).flip hφ)
    exact isNoetherian_of_isRepresentable' B S hS _ (hTaff n.1 n.2) (hXlaff n.1) he.1
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _ he) (hXlnoeth n.1)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The fibre product of Noetherian charts is a Noetherian chart.** If `t : U ⟶ V` and
`s : W ⟶ V` are morphisms of formal spectra of Noetherian adic rings with `P` on the chart map
of `t` and `Q` on the chart map of `s`, and `P` is stable under base change by `Q`, then
`U ×_V W` is the formal spectrum of the Noetherian adic ring `A ⊗̂_R C`. -/
theorem exists_spfPresentation_pullback_of_isStableUnderBaseChangeBy
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (PU : SpfPresentation B S hS U) (hPU : TopologicalRing.IsNoetherianAdic PU.ring)
    (PV : SpfPresentation B S hS V) (hPV : TopologicalRing.IsNoetherianAdic PV.ring)
    (PW : SpfPresentation B S hS W) (hPW : TopologicalRing.IsNoetherianAdic PW.ring)
    (ht : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic P t)
    (hs : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic Q s) :
    ∃ PT : SpfPresentation B S hS (pullback t s), TopologicalRing.IsNoetherianAdic PT.ring := by
  obtain ⟨eU⟩ := PU.iso
  obtain ⟨eV⟩ := PV.iso
  obtain ⟨eW⟩ := PW.iso
  have hwA : TopologicalRing.IsWeaklyAdmissible PU.ring := hPU.1.isWeaklyAdmissible
  have hwR : TopologicalRing.IsWeaklyAdmissible PV.ring := hPV.1.isWeaklyAdmissible
  have hwC : TopologicalRing.IsWeaklyAdmissible PW.ring := hPW.1.isWeaklyAdmissible
  obtain ⟨φA, hφA, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hwR hwA
    (eU.inv ≫ t ≫ eV.hom)
  obtain ⟨φC, hφC, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hwR hwC
    (eW.inv ≫ s ≫ eV.hom)
  have hPA : P φA.toRingHom := ht PV.ring PU.ring hPV hPU hwR PV.system PU.system eU eV φA
    (by rw [hφA]; simp)
  have hQC : Q φC.toRingHom := hs PV.ring PW.ring hPV hPW hwR PV.system PW.system eW eV φC
    (by rw [hφC]; simp)
  let : Algebra PV.ring PU.ring := φA.toRingHom.toAlgebra
  let : Algebra PV.ring PW.ring := φC.toRingHom.toAlgebra
  have : IsNoetherianRing PV.ring := hPV.2
  have : IsNoetherianRing PU.ring := hPU.2
  have : IsNoetherianRing PW.ring := hPW.2
  obtain ⟨hTadic, hTnoeth, -⟩ := hPQ.baseChange hPV.1 hPU.1 hPW.1 φA.continuous φC.continuous
    hPA hQC
  obtain ⟨DT, -, E, -, -, -⟩ := exists_formalSpectrum_completedTensorProduct_iso_snd
    hwA hwC hwR PU.system PW.system PV.system t s eU eW eV
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hV) φA φC hφA hφC
  exact ⟨⟨_, DT, ⟨E⟩⟩, hTadic, hTnoeth⟩

end

/-- Let `P` and `Q` be local properties of morphisms of `WAdm^{Noeth}` (Remark 0ANI), with `P`
stable under base change by `Q`: given `B → A` and `B → C` in `WAdm^{Noeth}` with `P (B → A)` and
`Q (B → C)`, the completed tensor product `A ⊗̂_B C` is adic Noetherian and `P (C → A ⊗̂_B C)`
holds (`TopologicalRing.IsStableUnderBaseChangeBy`). Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms
of locally Noetherian formal algebraic spaces over `S` such that the equivalent conditions of
Stacks 0ANG hold for `f` and `P` and for `g` and `Q`. Then the equivalent conditions of Stacks 0ANG
hold for `pr₂ : X ×_Y Z ⟶ Z` and `P`; all three of them are concluded.

Being local in the sense of Remark 0ANI is `hPQ.isLocalP` together with `hPiso`, the invariance
of `P` under isomorphism of source and target that Situation 0CBA assumes of a property of
arrows of the category. -/
@[stacks 0GBG "the statement drawn there: the equivalent conditions of Stacks 0ANG pass from \
f and P and from g and Q to the second projection of X ×_Y Z and P, for locally Noetherian \
formal algebraic spaces; the notion of stability under base change by Q is \
TopologicalRing.IsStableUnderBaseChangeBy"]
theorem conditions_pullback_snd_of_isStableUnderBaseChangeBy
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsNoetherianAdic B → TopologicalRing.IsNoetherianAdic A →
      TopologicalRing.IsNoetherianAdic B' → TopologicalRing.IsNoetherianAdic A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic Q g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P (pullback.snd f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hYf, J, V, v, hVaff, hVet, hVsurj, hVnoeth⟩ := id hY
  choose I U a haU hUnoeth using fun j ↦
    exists_isAffineEtaleCover_pullback_isNoetherian B S hS (v j) f (hVet j) (hVaff j) hYf hX
  choose K W b hbW hWnoeth using fun j ↦
    exists_isAffineEtaleCover_pullback_isNoetherian B S hS (v j) g (hVet j) (hVaff j) hYf hZ
  let M : (Σ j, I j × K j) → FppfSheaf B S hS := fun p ↦
    pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f) (b p.1 p.2.2 ≫ pullback.fst (v p.1) g)
  let m : ∀ p, M p ⟶ pullback f g := fun p ↦
    chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2)
  have hcover : IsAffineEtaleCover B S hS M m :=
    ⟨fun p ↦ isAffineFormalAlgebraicSpace_pullback B S hS _ _
        (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hVaff p.1))
        (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hVaff p.1))
        ((haU p.1).1 p.2.1) ((hbW p.1).1 p.2.2),
      fun p ↦ isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
        (b p.1 p.2.2) (hVet p.1) ((haU p.1).2.1 p.2.1) ((hbW p.1).2.1 p.2.2),
      isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hVsurj a (fun j ↦ (haU j).2.2)
        b (fun j ↦ (hbW j).2.2)⟩
  have hwet : ∀ p : Σ j, I j × K j,
      IsRepresentableEtale B S hS (b p.1 p.2.2 ≫ pullback.snd (v p.1) g) := fun p ↦
    isRepresentableEtale_comp_pullback_snd B S hS ((hbW p.1).2.1 p.2.2) (hVet p.1)
  have hsq : ∀ p : Σ j, I j × K j, m p ≫ pullback.snd f g =
      pullback.snd (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
        (b p.1 p.2.2 ≫ pullback.fst (v p.1) g) ≫ b p.1 p.2.2 ≫ pullback.snd (v p.1) g :=
    fun p ↦ chartPullbackMap_comp_snd B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2)
  have hPf : ∀ p : Σ j, I j × K j, HasPropertyOnAffineChartMap B S hS
      TopologicalRing.IsNoetherianAdic P (a p.1 p.2.1 ≫ pullback.fst (v p.1) f) := fun p ↦
    hf _ _ (a p.1 p.2.1 ≫ pullback.snd (v p.1) f) (v p.1) _ ((haU p.1).1 p.2.1) (hVaff p.1)
      (isRepresentableEtale_comp_pullback_snd B S hS ((haU p.1).2.1 p.2.1) (hVet p.1))
      (hVet p.1) (by simp only [Category.assoc, pullback.condition])
  have hQg : ∀ p : Σ j, I j × K j, HasPropertyOnAffineChartMap B S hS
      TopologicalRing.IsNoetherianAdic Q (b p.1 p.2.2 ≫ pullback.fst (v p.1) g) := fun p ↦
    hg _ _ (b p.1 p.2.2 ≫ pullback.snd (v p.1) g) (v p.1) _ ((hbW p.1).1 p.2.2) (hVaff p.1)
      (hwet p) (hVet p.1) (by simp only [Category.assoc, pullback.condition])
  have hpres : ∀ (T : FppfSheaf B S hS), IsNoetherian B S hS T →
      ∃ PT : SpfPresentation B S hS T, TopologicalRing.IsNoetherianAdic PT.ring :=
    fun T hT ↦ exists_spfPresentation_of_isNoetherian B S hS T hT
  have hprop : ∀ p : Σ j, I j × K j, HasPropertyOnAffineChartMap B S hS
      TopologicalRing.IsNoetherianAdic P (pullback.snd (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
        (b p.1 p.2.2 ≫ pullback.fst (v p.1) g)) := fun p ↦ by
    obtain ⟨PU, hPU⟩ := hpres _ (hUnoeth p.1 p.2.1)
    obtain ⟨PV, hPV⟩ := hpres _ (hVnoeth p.1)
    exact hasPropertyOnAffineChartMap_pullback_snd B S hS P Q hPQ hPiso _ _ (hVaff p.1) PU hPU PV
      hPV (hPf p) (hQg p)
  have h3 : HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P
      (pullback.snd f g) :=
    ⟨_, M, m, hcover, fun p ↦ ⟨W p.1 p.2.2, b p.1 p.2.2 ≫ pullback.snd (v p.1) g, _,
      (hbW p.1).1 p.2.2, hwet p, hsq p, hprop p⟩⟩
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P
      (pullback.snd f g) :=
    hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover B S hS _ P hPQ.isLocalP hPiso
      (fun _ _ _ _ _ hR ↦ ⟨hR.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩)
      (fun {R₁ R₂} _ _ _ _ _ φ _ het hX ↦ by
        let := φ.toAlgebra
        have : Algebra.Etale R₁ R₂ := het
        have : IsNoetherianRing R₁ := hX.2
        exact TopologicalRing.completionOver_isNoetherianAdic φ hX
          (Algebra.FiniteType.isNoetherianRing R₁ R₂))
      (fun e he he' hX ↦ TopologicalRing.isNoetherianAdic_of_ringEquiv e he he' hX)
      (pullback.snd f g) M (fun p ↦ W p.1 p.2.2) m (fun p ↦ b p.1 p.2.2 ≫ pullback.snd (v p.1) g)
      _ hcover (fun p ↦ (hbW p.1).1 p.2.2) hwet hsq hprop
      (fun p ↦ by
        obtain ⟨PU, hPU⟩ := hpres _ (hUnoeth p.1 p.2.1)
        obtain ⟨PV, hPV⟩ := hpres _ (hVnoeth p.1)
        obtain ⟨PW, hPW⟩ := hpres _ (hWnoeth p.1 p.2.2)
        exact exists_spfPresentation_pullback_of_isStableUnderBaseChangeBy B S hS P Q hPQ _ _
          (hVaff p.1) PU hPU PV hPV PW hPW (hPf p) (hQg p))
      (fun p ↦ hpres _ (hWnoeth p.1 p.2.2))
  exact ⟨h1, hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal' B S hS _ P
    (pullback.snd f g)
    (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hYf hX.1 hZ.1) hZ.1 h1,
    h3⟩

/-- The variant of Stacks 0GBD for locally Noetherian formal algebraic spaces. Let `P` be a local
property of morphisms of `WAdm^{Noeth}` (Remark 0ANI) which is stable under base change: given
`B → A` and `B → C` in `WAdm^{Noeth}`, `P (B → A)` implies that `A ⊗̂_B C` is adic Noetherian and
that `P (C → A ⊗̂_B C)` holds (`TopologicalRing.IsStableUnderBaseChangeNoetherian`, the definition
of the remark). Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian formal algebraic
spaces over `S`. If `f` satisfies the equivalent conditions of Stacks 0ANG, then so does
`pr₂ : X ×_Y Z ⟶ Z`; all three of them are concluded.

Being local in the sense of Remark 0ANI is `hP.isLocal` together with `hPiso`, the invariance
of `P` under isomorphism of source and target that Situation 0CBA assumes. Nothing is asked of
`g`. -/
@[stacks 0GBF "the variant of Stacks 0GBD for morphisms between locally Noetherian formal \
algebraic spaces; the definition of stability under base change is \
TopologicalRing.IsStableUnderBaseChangeNoetherian"]
theorem conditions_pullback_snd_of_isStableUnderBaseChangeNoetherian
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChangeNoetherian.{u} P)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsNoetherianAdic B → TopologicalRing.IsNoetherianAdic A →
      TopologicalRing.IsNoetherianAdic B' → TopologicalRing.IsNoetherianAdic A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P (pullback.snd f g) :=
  conditions_pullback_snd_of_isStableUnderBaseChangeBy B S hS P (fun _ ↦ True)
    (hP.isStableUnderBaseChangeBy _ TopologicalRing.propertyIsLocalNoetherian_true) hPiso f g
    hX hY hZ hf (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

end AlgebraicGeometry.FormalSpace

end
