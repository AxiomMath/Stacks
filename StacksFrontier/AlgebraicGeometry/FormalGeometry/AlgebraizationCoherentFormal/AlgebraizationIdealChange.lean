module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkIdealChange
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceIdealChange
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.BlowupFibreDimension

/-!
# Algebraization along a smaller ideal with the same radical

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `J ⊆ I` be an ideal with the same radical, and let
`S'` be the situation with `I` replaced by `J`
(`Stacks.Algebraization.AlgebraizationSituation.withIdeal`; the ring, `𝔞`, `X`, `Z` and `U` are
unchanged). By [Stacks, Tag 0EHR] an object `(ℱₙ)` of `Coh(U, I𝒪_U)` corresponds to an object of
`Coh(U, J𝒪_U)`, its transfer. This file shows that the hypotheses and the conclusion of the
algebraization theorems of the chapter survive the change: the `(a, b)`-inequalities of
[Stacks, Tag 0EJ3] and the bound `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > b` pass from
`(ℱₙ)` to its transfer, and the transfer extends to `X` (in `S'`) only if `(ℱₙ)` does (in the
original situation). This is the step "we may assume `I = (f₁, …, f_d)`, see Cohomology of
Schemes, Lemma 0EHR" of the proof of [Stacks, Tag 0EJN].

## Main results

* `Stacks.Algebraization.idealOnOpen_withIdeal_le` and
  `Stacks.Algebraization.exists_pow_idealOnOpen_le_withIdeal` — the two ideal sheaves on `U` are
  mutually cofinal.
* `Stacks.Algebraization.satisfiesDepthInequalities_withIdeal` and
  `Stacks.Algebraization.depthAddDimAddDistance_gt_withIdeal` — the depth conditions transfer.
* `Stacks.Coherent.transferSystemRestrictIso` — restriction to an open commutes with the
  transfer.
* `Stacks.Algebraization.extendsToX_of_withIdeal` — extendability descends.

## References

* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
* [Stacks Project, Tag 0EJN](https://stacks.math.columbia.edu/tag/0EJN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Restriction commutes with the transfer -/

namespace Stacks.Coherent

/-- The component of `Stacks.Coherent.transferSystemRestrictIso` commutes with the transitions. -/
public theorem transferTransition_comp_restrictIdealPowerQuotientIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (K : X.IdealSheafData) (a : ℕ) (G : ℕᵒᵖ ⥤ X.Modules)
    (hG : ∀ n : ℕ, (G.obj (op n)).IsQuasicoherent) {m n : ℕ} (h : m ≤ n) :
    haveI := hG (transferIndex a m)
    haveI := hG (transferIndex a n)
    transferTransition (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) h ≫
        (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (m + 1)
          (G.obj (op (transferIndex a m)))).hom =
      (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (n + 1)
          (G.obj (op (transferIndex a n)))).hom ≫
        (Scheme.Modules.restrictFunctor f).map (transferTransition K a G h) := by
  have := hG (transferIndex a m)
  have := hG (transferIndex a n)
  apply (cancel_epi (transferProjection (K.comap f) a
    (G ⋙ Scheme.Modules.restrictFunctor f) n)).1
  calc transferProjection (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) n ≫
        transferTransition (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) h ≫
          (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (m + 1)
            (G.obj (op (transferIndex a m)))).hom
      = (transferProjection (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) n ≫
          transferTransition (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) h) ≫
          (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (m + 1)
            (G.obj (op (transferIndex a m)))).hom := (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictFunctor f).map (G.map (homOfLE (transferIndex_mono a h)).op) ≫
          transferProjection (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) m) ≫
          (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (m + 1)
            (G.obj (op (transferIndex a m)))).hom := by
        rw [transferProjection_map (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) h]
        rfl
    _ = (Scheme.Modules.restrictFunctor f).map (G.map (homOfLE (transferIndex_mono a h)).op) ≫
          (Scheme.Modules.restrictFunctor f).map (transferProjection K a G m) := by
        rw [Category.assoc]
        exact congrArg (fun z => (Scheme.Modules.restrictFunctor f).map
          (G.map (homOfLE (transferIndex_mono a h)).op) ≫ z)
          (Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso f K (m + 1)
            (G.obj (op (transferIndex a m))))
    _ = (Scheme.Modules.restrictFunctor f).map (transferProjection K a G n) ≫
          (Scheme.Modules.restrictFunctor f).map (transferTransition K a G h) := by
        rw [← Functor.map_comp, ← Functor.map_comp, transferProjection_map K a G h]
    _ = transferProjection (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) n ≫
          (Stacks.Algebraization.restrictIdealPowerQuotientIso f K (n + 1)
            (G.obj (op (transferIndex a n)))).hom ≫
          (Scheme.Modules.restrictFunctor f).map (transferTransition K a G h) := by
        rw [← Category.assoc]
        exact congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor f).map
          (transferTransition K a G h))
          (Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso f K (n + 1)
            (G.obj (op (transferIndex a n)))).symm

/-- **Restriction to an open commutes with the transfer of [Stacks, Tag 0EHR].** For an open
immersion `f : Y ⟶ X`, restricting `(G_{a(n+1)} / 𝒦 ⁿ⁺¹ G_{a(n+1)})` to `Y` gives the transfer of
the restricted system along `𝒦|_Y`. -/
public def transferSystemRestrictIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (K : X.IdealSheafData) (a : ℕ) (G : ℕᵒᵖ ⥤ X.Modules)
    (hG : ∀ n : ℕ, (G.obj (op n)).IsQuasicoherent) :
    transferSystem (K.comap f) a (G ⋙ Scheme.Modules.restrictFunctor f) ≅
      transferSystem K a G ⋙ Scheme.Modules.restrictFunctor f :=
  NatIso.ofComponents
    (fun n => haveI := hG (transferIndex a n.unop)
      Stacks.Algebraization.restrictIdealPowerQuotientIso f K (n.unop + 1)
        (G.obj (op (transferIndex a n.unop))))
    (by
      rintro ⟨n⟩ ⟨m⟩ g
      have h : m ≤ n := leOfHom g.unop
      obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
      exact transferTransition_comp_restrictIdealPowerQuotientIso f K a G hG h)

end Stacks.Coherent

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u}) {J : Ideal S.A} (hJI : J ≤ S.I)

/-- The smaller ideal is still contained in `𝔞`. -/
public theorem le_a_of_le_I (hJI : J ≤ S.I) : J ≤ S.a := hJI.trans S.I_le_a

/-! ### The two ideal sheaves -/

/-- The ideal sheaf `J𝒪_U` is contained in `I𝒪_U`. -/
public theorem idealOnOpen_withIdeal_le :
    idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI)) ≤ idealOnOpen S := by
  refine Scheme.IdealSheafData.comap_mono S.U.ι fun U => ?_
  simpa only [Scheme.IdealSheafData.ofIdealTop_ideal] using Ideal.map_mono (Ideal.map_mono hJI)

/-- The ideal sheaf `I𝒪_X` is the ideal sheaf of `Spec A` cut out by `I`. -/
public theorem idealOnX_eq_specIdealSheaf :
    idealOnX S = Stacks.LocalCohomology.specIdealSheaf S.A S.I := rfl

/-- Ideals with the same radical cut out the same closed subset of `U`. -/
public theorem support_idealOnOpen_withIdeal (hrad : J.radical = S.I.radical) :
    (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))).support = (idealOnOpen S).support := by
  rw [idealOnOpen_eq_comap_idealOnX, idealOnOpen_eq_comap_idealOnX,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  congr 1
  apply TopologicalSpace.Closeds.ext
  show ((Stacks.LocalCohomology.specIdealSheaf S.A J).support : Set (Spec (CommRingCat.of S.A))) =
    ((Stacks.LocalCohomology.specIdealSheaf S.A S.I).support : Set (Spec (CommRingCat.of S.A)))
  rw [Stacks.LocalCohomology.coe_support_specIdealSheaf,
    Stacks.LocalCohomology.coe_support_specIdealSheaf, ← PrimeSpectrum.zeroLocus_radical, hrad,
    PrimeSpectrum.zeroLocus_radical]

/-- Some positive power of `I𝒪_U` lies in `J𝒪_U`. -/
public theorem exists_pow_idealOnOpen_le_withIdeal (hrad : J.radical = S.I.radical) :
    ∃ c : ℕ, 1 ≤ c ∧ idealOnOpen S ^ c ≤ idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI)) := by
  have : IsNoetherian S.U.toScheme := ⟨⟩
  obtain ⟨c, -, hc, -, hcJ, -⟩ := Scheme.IdealSheafData.exists_pos_pow_le_and_pow_le_of_support_eq
    (support_idealOnOpen_withIdeal S hJI hrad).symm
  exact ⟨c, hc, hcJ⟩

/-! ### The depth conditions transfer -/

variable (hrad : J.radical = S.I.radical) {c : ℕ}
  (hc : idealOnOpen S ^ c ≤ idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI)))
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The transfer of `(ℱₙ)` to `Coh(U, J𝒪_U)`. -/
public abbrev transferToWithIdeal :
    Stacks.Coherent.CoherentAdicSystems (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) :=
  haveI : IsNoetherian S.U.toScheme := ⟨⟩
  (Stacks.Coherent.transferFunctor (idealOnOpen S)
    (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) c hc).obj F

/-- A prime not containing the completed local ideal for `J` transfers to one not containing it
for `I`. -/
private theorem not_completedLocalIdeal_le_transferPrime (y : S.U.toScheme)
    {p : PrimeSpectrum (completedLocalRing (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) y)}
    (hp : ¬ completedLocalIdeal (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) y ≤ p.asIdeal) :
    ¬ completedLocalIdeal (idealOnOpen S) y ≤
      (transferPrime hc (idealOnOpen_withIdeal_le S hJI) y p).asIdeal := fun h' =>
  hp ((completedLocalIdeal_le_transfer_iff hc (idealOnOpen_withIdeal_le S hJI) y p).mpr h')

include hrad in
/-- At corresponding points and primes the two quantities of the inequalities agree. -/
theorem depthAddDistance_withIdeal (y : S.U.toScheme) (z' : (S.withIdeal J (le_a_of_le_I S hJI)).Y)
    (z : S.Y) (hz : S.Yι.base z = (S.withIdeal J (le_a_of_le_I S hJI)).Yι.base z')
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) y)) :
    haveI : IsNoetherian S.U.toScheme := ⟨⟩
    depthAddDistance (S.withIdeal J (le_a_of_le_I S hJI)) (transferToWithIdeal S hJI hc F) y z' p =
        depthAddDistance S F y z
          (transferPrime hc (idealOnOpen_withIdeal_le S hJI) y p) ∧
      depthAddDimAddDistance (S.withIdeal J (le_a_of_le_I S hJI)) (transferToWithIdeal S hJI hc F)
          y z' p =
        depthAddDimAddDistance S F y z
          (transferPrime hc (idealOnOpen_withIdeal_le S hJI) y p) := by
  have : IsNoetherian S.U.toScheme := ⟨⟩
  have hdist := AlgebraizationSituation.distanceToZ_withIdeal S J (le_a_of_le_I S hJI) hrad z' z
    hz.symm
  have hdepth := completedStalkDepth_transfer hc (idealOnOpen_withIdeal_le S hJI) F y p
  have hdim := ringKrullDim_quotient_transfer hc (idealOnOpen_withIdeal_le S hJI) y p
  refine ⟨?_, ?_⟩
  · exact congrArg₂ (· + ·) (congrArg enatToEInt hdepth) (congrArg enatToEInt hdist)
  · exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (congrArg enatToEInt hdepth) (congrArg krullDimToEInt hdim))
      (congrArg enatToEInt hdist)

include hrad in
/-- **The `(a, b)`-inequalities pass to the transfer.** -/
public theorem satisfiesDepthInequalities_withIdeal {a b : ℤ}
    (h : SatisfiesDepthInequalities S F a b) :
    SatisfiesDepthInequalities (S.withIdeal J (le_a_of_le_I S hJI))
      (transferToWithIdeal S hJI hc F) a b := by
  have : IsNoetherian S.U.toScheme := ⟨⟩
  intro y z' hyz' p hp
  obtain ⟨z, hz⟩ := AlgebraizationSituation.exists_Yι_eq_of_withIdeal S J (le_a_of_le_I S hJI)
    hrad z'
  obtain ⟨h1, h2⟩ := h y z (hyz'.trans hz.symm) _
    (not_completedLocalIdeal_le_transferPrime S hJI hc y hp)
  obtain ⟨e1, e2⟩ := depthAddDistance_withIdeal S hJI hrad hc F y z' z hz p
  have hfib := adicClosedFibreThrough_transfer_eq_singleton_iff hc
    (idealOnOpen_withIdeal_le S hJI) y p
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · rw [e1, e2]
    exact h1 fun h' => hne (hfib.mpr h')
  · rw [e1]
    exact h2 (hfib.mp heq)

include hrad in
/-- **The bound `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > b` passes to the
transfer.** -/
public theorem depthAddDimAddDistance_gt_withIdeal {b : ℤ}
    (h : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
        ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
        depthAddDimAddDistance S F y z p > (b : EInt)) :
    ∀ (y : (S.withIdeal J (le_a_of_le_I S hJI)).U.toScheme)
      (z : (S.withIdeal J (le_a_of_le_I S hJI)).Y),
      (S.withIdeal J (le_a_of_le_I S hJI)).U.ι.base y =
        (S.withIdeal J (le_a_of_le_I S hJI)).Yι.base z →
      ∀ p : PrimeSpectrum (completedLocalRing
          (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) y),
        ¬ completedLocalIdeal (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) y ≤
          p.asIdeal →
        depthAddDimAddDistance (S.withIdeal J (le_a_of_le_I S hJI))
          (transferToWithIdeal S hJI hc F) y z p > (b : EInt) := by
  have : IsNoetherian S.U.toScheme := ⟨⟩
  intro y z' hyz' p hp
  obtain ⟨z, hz⟩ := AlgebraizationSituation.exists_Yι_eq_of_withIdeal S J (le_a_of_le_I S hJI)
    hrad z'
  rw [(depthAddDistance_withIdeal S hJI hrad hc F y z' z hz p).2]
  exact h y z (hyz'.trans hz.symm) _ (not_completedLocalIdeal_le_transferPrime S hJI hc y hp)

/-! ### Extendability descends -/

/-- The ideal sheaf of `V(J)` on `X` is contained in that of `V(I)`. -/
public theorem ker_withIdeal_Yι_le :
    (S.withIdeal J (le_a_of_le_I S hJI)).Yι.ker ≤ S.Yι.ker := by
  rw [← idealOnX_eq_ker_Yι, ← idealOnX_eq_ker_Yι]
  intro U
  simpa only [Scheme.IdealSheafData.ofIdealTop_ideal] using Ideal.map_mono (Ideal.map_mono hJI)

/-- **Extendability descends from the transfer.** If the transfer of `(ℱₙ)` to `Coh(U, J𝒪_U)`
extends to `X`, then so does `(ℱₙ)`: transfer the extension back to `Coh(X, I𝒪_X)`; its
restriction to `U` is the double transfer of `(ℱₙ)`, which is `(ℱₙ)`. -/
public theorem extendsToX_of_withIdeal (hc1 : 1 ≤ c)
    (h : ExtendsToX (S.withIdeal J (le_a_of_le_I S hJI))
      (toKerSystem (S.withIdeal J (le_a_of_le_I S hJI)) (transferToWithIdeal S hJI hc F))) :
    ExtendsToX S (toKerSystem S F) := by
  have : IsNoetherian S.U.toScheme := ⟨⟩
  obtain ⟨G, ⟨e⟩⟩ := h
  have e' : G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅
      Stacks.Coherent.transferSystem (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI))) c F.obj :=
    e ≪≫ eqToIso (toKerSystem_obj (S.withIdeal J (le_a_of_le_I S hJI))
      (transferToWithIdeal S hJI hc F))
  refine ⟨(Stacks.Coherent.transferFunctor _ S.Yι.ker 1
    ((pow_one (M := S.X.IdealSheafData) _).le.trans (ker_withIdeal_Yι_le S hJI))).obj G, ⟨?_⟩⟩
  rw [toKerSystem_obj]
  have hGqc : ∀ n : ℕ, (G.obj.obj (op n)).IsQuasicoherent := fun n =>
    (G.property : Stacks.Coherent.IsCoherentAdicSystem _ G.obj).isQuasicoherent n
  have hle : (idealOnOpen (S.withIdeal J (le_a_of_le_I S hJI)) : S.U.toScheme.IdealSheafData) ^ 1 ≤
      idealOnOpen S :=
    (pow_one (M := S.U.toScheme.IdealSheafData) _).le.trans (idealOnOpen_withIdeal_le S hJI)
  refine (Stacks.Coherent.transferSystemRestrictIso S.U.ι S.Yι.ker 1 G.obj hGqc).symm ≪≫
    eqToIso (congrArg (fun K => Stacks.Coherent.transferSystem K 1
      (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι)) (ker_Yι_comap_eq_idealOnOpen S)) ≪≫
    (Stacks.Coherent.transferSystemFunctor (idealOnOpen S) 1).mapIso e' ≪≫
    Stacks.Coherent.transferCompositeIso hc1 le_rfl hle F.property

end Stacks.Algebraization

end
