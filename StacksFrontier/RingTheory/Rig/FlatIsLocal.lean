module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.FlatDescent
public import StacksFrontier.RingTheory.Rig.FlatEtaleLocalization
public import StacksFrontier.RingTheory.Rig.FlatJacobson
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalProperty
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic

/-!
# Rig-flatness is a local property of morphisms of Noetherian adic rings

A continuous homomorphism of Noetherian adic topological rings is rig-flat (Stacks 0GGP) when
it is adic, topologically of finite type, and all the maps it induces between completed
principal localizations are naively rig-flat. Stacks 0GGU asserts that this is a *local
property* in the sense of Situation 0CBA, in the Noetherian form of Remark 0ANI: writing a
localization diagram as

```
B ────────→ (B')^
│             │
│ φ           │ φ'
↓             ↓
A ────────→ (A')^
```

with `B → B'` and `A → A'` étale, rig-flatness ascends from `φ` to `φ'`, descends from `φ'` to
`φ` when `A → A'` is faithfully flat, and is preserved by finite products of targets.

Ascent is Stacks 0GGS and descent is Stacks 0GGT; what has to be supplied here is that the
horizontal maps of such a diagram satisfy their hypotheses. That is
`Rig.canonicalMap_facts` — the canonical map to the completion over the base is continuous,
adic, topologically of finite type and flat — together with the input of Stacks 0GGS that is
specific to the étale situation: the reduction `B/I → (B')^/I(B')^` of the source-side
horizontal map modulo an ideal of definition is étale. That reduction is identified with the
reduction `B/I → B'/IB'` of the étale map itself, because the completion over `B` modulo `I` is
`B'/IB'`; this is `Rig.etale_quotientMap_canonicalMap`.

The finite-product axiom rests on the identification of the completed principal localization of
a finite product with the product of the completed principal localizations
(`Rig.exists_completedAway_pi_equiv`), which in turn comes from the corresponding
identifications for principal localizations (`Rig.localizationAwayPiEquiv`), for quotients
(`Rig.quotientPiEquiv`) and for adic completions (`Rig.adicCompletionPiEquiv`).

## Main definitions

* `Rig.reduceCompletionOver` and `Rig.completionOverQuotientEquiv`: the reduction of the
  completion of `A` over `B` modulo an ideal of definition of `B`, and the resulting
  identification of that reduction with `A/IA`.
* `Rig.adicCompletionCongr`: the isomorphism of adic completions induced by an isomorphism
  matching the ideals.
* `Rig.localizationAwayPiEquiv`, `Rig.quotientPiEquiv`, `Rig.quotientPiPowEquiv`,
  `Rig.adicCompletionPiEquiv`: a finite product of rings commutes with principal localization,
  with quotients, and with adic completion.

## Main results

* `Rig.rigFlat_isLocalNoetherian`: **Stacks 0GGU**.
* `Rig.rigFlat_localizationPreserves`, `Rig.rigFlat_faithfullyFlatDescent`,
  `Rig.rigFlat_finiteProductPreserves`: the three axioms separately.
* `Rig.etale_quotientMap_canonicalMap`: the reduction of the canonical map of an étale
  localization diagram modulo an ideal of definition is étale.
* `Rig.canonicalMap_facts`: the canonical map to the completion over the base is continuous,
  adic, topologically of finite type and flat.
* `Rig.exists_completedAway_pi_equiv`: the completed principal localization of a finite product
  is the product of the completed principal localizations.

## Implementation notes

The three axioms are stated against the subcategory `TopologicalRing.IsNoetherianAdic` of
Noetherian adic topological rings, which is the subcategory appearing in Remark 0ANI; the
corresponding membership condition of Situation 0ANH, a finitely generated ideal defining the
topology, is supplied by `Rig.exists_fg_isAdic_of_isAdicRing` wherever the locality of adicness
and topological finite type is invoked.

## References

* [Stacks Project, Tag 0GGU](https://stacks.math.columbia.edu/tag/0GGU)
* [Stacks Project, Tag 0GGS](https://stacks.math.columbia.edu/tag/0GGS)
* [Stacks Project, Tag 0GGT](https://stacks.math.columbia.edu/tag/0GGT)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public section

open TopologicalRing

universe u

namespace Rig

/-- A Noetherian adic topological ring has a finitely generated ideal defining its topology,
which is the membership condition of the subcategory of Situation 0ANH. -/
theorem exists_fg_isAdic_of_isAdicRing {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsNoetherianRing R] (hR : TopologicalRing.IsAdic R) :
    ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
  obtain ⟨I, -, hI⟩ := hR.1
  exact ⟨I, IsNoetherian.noetherian I, hI⟩

section EtaleQuotient

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsNoetherianRing B] [CommRing A] (f : B →+* A)
  {I : Ideal B} (hI : TopologicalRing.IsIdealOfDefinition I) (hIadic : _root_.IsAdic I)

/-- Reduction of the completion of `A` over `B` modulo an ideal of definition `I` of `B`: the
first evaluation of the `IA`-adic completion of `A`, read through the identification of the
completion over `B` with that adic completion. -/
noncomputable def reduceCompletionOver : CompletionOver f →+* A ⧸ I.map f :=
  (AdicCompletion.evalOneₐ (I.map f)).toRingHom.comp
    (CompletionOver.adicCompletionRingEquiv hI hIadic f :
      CompletionOver f →+* AdicCompletion (I.map f) A)

omit [IsNoetherianRing B] in
/-- The identification of the completion of `A` over `B` with the `IA`-adic completion of `A`
carries the canonical map from `B` to the structure map composed with `f`. -/
theorem adicCompletionRingEquiv_comp_canonicalMap :
    (CompletionOver.adicCompletionRingEquiv hI hIadic f :
        CompletionOver f →+* AdicCompletion (I.map f) A).comp
      (CompletionOver.canonicalMap f) =
      (algebraMap A (AdicCompletion (I.map f) A)).comp f := by
  rw [show (CompletionOver.adicCompletionRingEquiv hI hIadic f :
      CompletionOver f →+* AdicCompletion (I.map f) A) =
    CompletionOver.toAdicCompletion hI hIadic f from rfl,
    ← CompletionOver.ofTarget_comp f, ← RingHom.comp_assoc,
    CompletionOver.toAdicCompletion_comp_ofTarget]

omit [IsNoetherianRing B] in
/-- The reduction of the completion of `A` over `B` takes the canonical map from `B` to the
reduction of `f`. -/
theorem reduceCompletionOver_canonicalMap (b : B) :
    reduceCompletionOver f hI hIadic (CompletionOver.canonicalMap f b) =
      Ideal.Quotient.mk (I.map f) (f b) := by
  change (AdicCompletion.evalOneₐ (I.map f))
    ((CompletionOver.adicCompletionRingEquiv hI hIadic f :
      CompletionOver f →+* AdicCompletion (I.map f) A) (CompletionOver.canonicalMap f b)) = _
  rw [show (CompletionOver.adicCompletionRingEquiv hI hIadic f :
      CompletionOver f →+* AdicCompletion (I.map f) A) (CompletionOver.canonicalMap f b) =
    algebraMap A (AdicCompletion (I.map f) A) (f b) from
      congrFun (congrArg (fun g : B →+* AdicCompletion (I.map f) A ↦ (g : B → _))
        (adicCompletionRingEquiv_comp_canonicalMap f hI hIadic)) b]
  exact (AdicCompletion.evalOneₐ (I.map f)).commutes (f b)

omit [IsNoetherianRing B] in
/-- The reduction of the completion of `A` over `B` modulo an ideal of definition is
surjective. -/
theorem reduceCompletionOver_surjective :
    Function.Surjective (reduceCompletionOver f hI hIadic) :=
  (AdicCompletion.evalOneₐ_surjective (I.map f)).comp
    (CompletionOver.bijective_toAdicCompletion hI hIadic f).2

/-- The kernel of the reduction of the completion of `A` over `B` modulo an ideal of
definition `I` of `B` is the ideal generated by the image of `I`. -/
theorem ker_reduceCompletionOver :
    RingHom.ker (reduceCompletionOver f hI hIadic) =
      I.map (CompletionOver.canonicalMap f) := by
  have hJfg : (I.map f).FG := (Ideal.fg_of_isNoetherianRing I).map f
  have hmap : I.map (CompletionOver.canonicalMap f) =
      Ideal.comap (CompletionOver.adicCompletionRingEquiv hI hIadic f :
          CompletionOver f →+* AdicCompletion (I.map f) A)
        ((I.map f).map (algebraMap A (AdicCompletion (I.map f) A))) := by
    rw [Ideal.map_map, ← adicCompletionRingEquiv_comp_canonicalMap f hI hIadic,
      ← Ideal.map_map]
    exact (Ideal.comap_map_of_bijective _
      (CompletionOver.adicCompletionRingEquiv hI hIadic f).bijective).symm
  rw [hmap, ← AdicCompletion.ker_evalOneₐ_eq_map (I.map f) hJfg]
  rfl

include hI hIadic in
/-- The reduction of the completion of `A` over `B` modulo an ideal of definition of `B`
identifies that completion modulo the extended ideal with `A / IA`. -/
noncomputable def completionOverQuotientEquiv :
    CompletionOver f ⧸ I.map (CompletionOver.canonicalMap f) ≃+* A ⧸ I.map f :=
  (Ideal.quotEquivOfEq (ker_reduceCompletionOver f hI hIadic).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reduceCompletionOver_surjective f hI hIadic))

include hI hIadic in
/-- **The reduction of an étale localization is étale.** For an étale `f : B →+* A` and an
ideal of definition `I` of `B`, the map `B / I → (A)^∧ / I (A)^∧` induced by the canonical map
to the completion of `A` over `B` is étale, because it is the reduction `B / I → A / IA` of `f`
read through `Rig.completionOverQuotientEquiv`. -/
theorem etale_quotientMap_canonicalMap (hf : f.Etale) :
    (Ideal.quotientMap (I.map (CompletionOver.canonicalMap f))
      (CompletionOver.canonicalMap f) Ideal.le_comap_map).Etale := by
  have hq : (completionOverQuotientEquiv f hI hIadic).toRingHom.comp
      (Ideal.quotientMap (I.map (CompletionOver.canonicalMap f))
        (CompletionOver.canonicalMap f) Ideal.le_comap_map) =
      Ideal.quotientMap (I.map f) f Ideal.le_comap_map := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change completionOverQuotientEquiv f hI hIadic
      (Ideal.Quotient.mk (I.map (CompletionOver.canonicalMap f))
        (CompletionOver.canonicalMap f b)) = Ideal.Quotient.mk (I.map f) (f b)
    change reduceCompletionOver f hI hIadic (CompletionOver.canonicalMap f b) = _
    exact reduceCompletionOver_canonicalMap f hI hIadic b
  have hsymm : (completionOverQuotientEquiv f hI hIadic).symm.toRingHom.comp
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) =
      Ideal.quotientMap (I.map (CompletionOver.canonicalMap f))
        (CompletionOver.canonicalMap f) Ideal.le_comap_map := by
    refine RingHom.ext fun x ↦ (completionOverQuotientEquiv f hI hIadic).injective ?_
    exact ((completionOverQuotientEquiv f hI hIadic).apply_symm_apply _).trans
      (congrFun (congrArg (fun g : B ⧸ I →+* A ⧸ I.map f ↦ (g : B ⧸ I → _)) hq) x).symm
  rw [← hsymm]
  exact RingHom.Etale.respectsIso.1 _ (completionOverQuotientEquiv f hI hIadic).symm
    (TopologicalRing.quotientMap_of_isStableUnderBaseChange
      RingHom.Etale.isStableUnderBaseChange RingHom.Etale.respectsIso f hf I)

end EtaleQuotient


section CanonicalMap

/-- An adic topological ring is linearly topologized. -/
theorem isLinearTopology_of_isAdicRing {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hR : TopologicalRing.IsAdic R) : IsLinearTopology R R := by
  obtain ⟨I, -, hI⟩ := hR.1
  exact hI ▸ Ideal.isLinearTopology I

/-- **The canonical map of an étale localization diagram.** For an étale homomorphism
`f : B →+* A` out of a Noetherian adic topological ring whose completion over `B` is again
adic, the target `A` is Noetherian and the canonical map `B → (A)^∧` is continuous, adic,
topologically of finite type and flat. These are the five hypotheses that the ascent and
descent lemmas for rig-flatness ask of the horizontal maps of a localization diagram. -/
theorem canonicalMap_facts {B A : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B] [CommRing A]
    (f : B →+* A) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic (CompletionOver f)) (hf : f.Etale) :
    IsNoetherianRing A ∧ Continuous (CompletionOver.canonicalMap f) ∧
      _root_.RingHom.IsAdic (CompletionOver.canonicalMap f) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (CompletionOver.canonicalMap f) ∧
      (CompletionOver.canonicalMap f).Flat := by
  let : Algebra B A := f.toAlgebra
  let : Algebra.Etale B A := hf.toAlgebra
  have hA : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing B A
  let : IsNoetherianRing A := hA
  let : T2Space (CompletionOver f) := hC.2.1
  let : @CompleteSpace (CompletionOver f)
    (IsTopologicalAddGroup.rightUniformSpace (CompletionOver f)) := hC.2.2
  have hweak := weaklyAdmissible_of_isAdicRing hB
  refine ⟨hA, TopologicalRing.continuous_canonicalMap f,
    RingHom.isAdic_of_isTaut _ (TopologicalRing.isTaut_canonicalMap f hweak.1)
      (exists_fg_isAdic_of_isAdicRing hB),
    TopologicalRing.isTopologicallyOfFiniteType_canonicalMap f hweak.1
      (TopologicalRing.finiteType_of_etale hf),
    TopologicalRing.CompletionOver.flat_canonicalMap hB.1
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1⟩

end CanonicalMap

section Local

/-- **Rig-flatness ascends along a localization diagram** (axiom (1) of Situation 0CBA). The
horizontal maps of the diagram are flat, adic and topologically of finite type by
`Rig.canonicalMap_facts`, and the reduction of the source-side horizontal map is étale by
`Rig.etale_quotientMap_canonicalMap`, so this is Stacks 0GGS. -/
theorem rigFlat_localizationPreserves :
    TopologicalRing.LocalizationPreserves
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        IsNoetherianAdic R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hφ
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have : IsNoetherianRing (CompletionOver D.toA') := hA'.2
  have : IsNoetherianRing (CompletionOver D.toB') := hB'.2
  have := isLinearTopology_of_isAdicRing hA'.1
  have := isLinearTopology_of_isAdicRing hB'.1
  obtain ⟨-, hβcont, hβadic, hβft, hβflat⟩ :=
    canonicalMap_facts D.toA' hA.1 hA'.1 D.etaleA
  obtain ⟨-, hαcont, hαadic, hαft, hαflat⟩ :=
    canonicalMap_facts D.toB' hB.1 hB'.1 D.etaleB
  obtain ⟨hφ'adic, hφ'ft⟩ :=
    TopologicalRing.adicTopologicallyFiniteType_isLocal.localizationPreserves D
      (exists_fg_isAdic_of_isAdicRing hA.1) (exists_fg_isAdic_of_isAdicRing hB.1)
      (exists_fg_isAdic_of_isAdicRing hA'.1) (exists_fg_isAdic_of_isAdicRing hB'.1)
      ⟨hφ.1, hφ.2.1⟩
  obtain ⟨I, hIdef, hIadic⟩ := hB.1.1
  exact isRigFlat_of_flat_etale_square
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hB'.1)
    (weaklyAdmissible_of_isAdicRing hA.1) (weaklyAdmissible_of_isAdicRing hA'.1)
    D.map D.completedMap (CompletionOver.canonicalMap D.toB')
    (CompletionOver.canonicalMap D.toA')
    D.commutes.symm D.continuousMap D.continuousCompletedMap hαcont hβcont
    hφ.1 hφ'adic hαadic hβadic hφ.2.1 hφ'ft hαft hβft hαflat hβflat
    I hIdef hφ (etale_quotientMap_canonicalMap D.toB' hIdef hIadic D.etaleB)

/-- **Rig-flatness descends along a faithfully flat localization diagram** (axiom (2) of
Situation 0CBA). This is Stacks 0GGT, whose faithful flatness hypothesis on the target-side
horizontal map is `TopologicalRing.CompletionOver.faithfullyFlat_canonicalMap`. -/
theorem rigFlat_faithfullyFlatDescent :
    TopologicalRing.FaithfullyFlatDescent
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        IsNoetherianAdic R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hff hφ'
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have : IsNoetherianRing (CompletionOver D.toA') := hA'.2
  have : IsNoetherianRing (CompletionOver D.toB') := hB'.2
  have := isLinearTopology_of_isAdicRing hA'.1
  have := isLinearTopology_of_isAdicRing hB'.1
  obtain ⟨hA'noeth, hβcont, hβadic, hβft, -⟩ :=
    canonicalMap_facts D.toA' hA.1 hA'.1 D.etaleA
  obtain ⟨-, hαcont, hαadic, hαft, hαflat⟩ :=
    canonicalMap_facts D.toB' hB.1 hB'.1 D.etaleB
  let : IsNoetherianRing A' := hA'noeth
  obtain ⟨hφadic, hφft⟩ :=
    TopologicalRing.adicTopologicallyFiniteType_isLocal.faithfullyFlatDescent D
      (exists_fg_isAdic_of_isAdicRing hA.1) (exists_fg_isAdic_of_isAdicRing hB.1)
      (exists_fg_isAdic_of_isAdicRing hA'.1) (exists_fg_isAdic_of_isAdicRing hB'.1)
      hff ⟨hφ'.1, hφ'.2.1⟩
  exact RingHom.isRigFlat_of_faithfullyFlat
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hB'.1)
    (weaklyAdmissible_of_isAdicRing hA.1) (weaklyAdmissible_of_isAdicRing hA'.1)
    D.map (CompletionOver.canonicalMap D.toB') (CompletionOver.canonicalMap D.toA')
    D.completedMap D.commutes D.continuousMap hαcont hβcont D.continuousCompletedMap
    hφadic hαadic hβadic hφ'.1 hφft hαft hβft hφ'.2.1 hαflat
    (TopologicalRing.CompletionOver.faithfullyFlat_canonicalMap hA.1 hff) hφ'

section Pi

/-! ### Finite products -/

/-- An isomorphism of rings matching two ideals induces an isomorphism of the adic
completions. -/
noncomputable def adicCompletionCongr {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : I.map e.toRingHom = J) :
    AdicCompletion I R ≃+* AdicCompletion J S := by
  have hs : J.map e.symm.toRingHom = I := by
    rw [← h, Ideal.map_map]
    simp
  refine RingEquiv.ofRingHom (adicCompletionMap e.toRingHom I J h.le)
    (adicCompletionMap e.symm.toRingHom J I hs.le) ?_ ?_
  · rw [adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm] using
      adicCompletionMap_id J (by simp)
  · rw [adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp] using
      adicCompletionMap_id I (by simp)

/-- The principal localization of a finite product of rings at an element is the product of the
principal localizations at its coordinates. -/
noncomputable def localizationAwayPiEquiv {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (f : ∀ i, R i) :
    Localization.Away f ≃+* ∀ i, Localization.Away (f i) := by
  let M := Submonoid.powers f
  let S := fun i ↦ Localization.Away (f i)
  let (i : ι) : IsLocalization (M.map (Pi.evalRingHom R i)) (S i) := by
    simpa [M, Submonoid.map_powers] using
      (inferInstance : IsLocalization (Submonoid.powers (f i)) (S i))
  exact RingEquiv.ofBijective
    (IsLocalization.lift (S := Localization.Away f)
      (IsLocalization.isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M))
    (IsLocalization.bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom
      R S (Localization.Away f) M)

/-- `Rig.localizationAwayPiEquiv` is the identity on the images of the structure maps. -/
theorem localizationAwayPiEquiv_algebraMap {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (f x : ∀ i, R i) (i : ι) :
    localizationAwayPiEquiv R f (algebraMap _ (Localization.Away f) x) i =
      algebraMap (R i) (Localization.Away (f i)) (x i) := by
  simp [localizationAwayPiEquiv, IsLocalization.lift_eq]

namespace RingHom

/-- Naive rig-flatness is preserved by a finite product of targets. -/
theorem isNaivelyRigFlat_pi {R : Type*} [CommRing R] [TopologicalSpace R]
    {ι : Type*} [Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    (f : ∀ i, R →+* S i)
    (hfirst : _root_.RingHom.IsAdic (_root_.RingHom.pi f) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (_root_.RingHom.pi f))
    (hf : ∀ i, IsNaivelyRigFlat (f i)) :
    IsNaivelyRigFlat (_root_.RingHom.pi f) := by
  cases nonempty_fintype ι
  refine ⟨hfirst.1, hfirst.2, fun x hx ↦ ?_⟩
  let e := localizationAwayPiEquiv S ((_root_.RingHom.pi f) x)
  have he : e.toRingHom.comp
      ((algebraMap (∀ i, S i) (Localization.Away ((_root_.RingHom.pi f) x))).comp
        (_root_.RingHom.pi f)) =
      _root_.RingHom.pi
        (fun i ↦ (algebraMap (S i) (Localization.Away (f i x))).comp (f i)) := by
    ext r i
    exact localizationAwayPiEquiv_algebraMap S (fun i ↦ f i x) (fun i ↦ f i r) i
  apply (_root_.RingHom.Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective).mp
  rw [he]
  exact _root_.RingHom.Flat.pi _ (fun i ↦ (hf i).2.2 x hx)

/-- Naive rig-flatness transports along an isomorphism of the targets. -/
theorem isNaivelyRigFlat_of_ringEquiv {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g)
    (hfirst : _root_.RingHom.IsAdic f ∧ TopologicalRing.IsTopologicallyOfFiniteType f)
    (hg : IsNaivelyRigFlat g) : IsNaivelyRigFlat f := by
  refine ⟨hfirst.1, hfirst.2, fun x hx ↦ ?_⟩
  have hex : e (f x) = g x := DFunLike.congr_fun he x
  let E : Localization.Away (f x) ≃+* Localization.Away (g x) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (f x))
      (T := Submonoid.powers (g x)) _ _ e (by simp [Submonoid.map_powers, hex])
  have hE : E.toRingHom.comp ((algebraMap S (Localization.Away (f x))).comp f) =
      (algebraMap T (Localization.Away (g x))).comp g := by
    ext r
    change E (algebraMap S (Localization.Away (f x)) (f r)) = _
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    exact congrArg (algebraMap T (Localization.Away (g x))) (DFunLike.congr_fun he r)
  apply (_root_.RingHom.Flat.comp_iff_of_bijective_left (g := E.toRingHom) E.bijective).mp
  rw [hE]
  exact hg.2.2 x hx

end RingHom

/-- The quotient of a finite product of rings by an ideal is the product of the quotients by the
coordinate images of that ideal. -/
noncomputable def quotientPiEquiv {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i)) :
    ((∀ i, R i) ⧸ I) ≃+* ∀ i, R i ⧸ I.map (Pi.evalRingHom R i) := by
  let q : ((∀ i, R i) ⧸ I) →+* ∀ i, R i ⧸ I.map (Pi.evalRingHom R i) :=
    Ideal.Quotient.lift I
      (_root_.RingHom.pi fun i ↦ (Ideal.Quotient.mk _).comp (Pi.evalRingHom R i))
      fun x hx ↦ by
        ext i
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  refine RingEquiv.ofBijective q ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero q).mpr fun x hx ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← Ideal.piOrderIso.symm_apply_apply I]
    change ∀ i, x i ∈ I.map (Pi.evalRingHom R i)
    exact fun i ↦ Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx i)
  · intro x
    choose r hr using fun i ↦ Ideal.Quotient.mk_surjective (x i)
    exact ⟨Ideal.Quotient.mk I r, funext hr⟩

/-- The quotient of a finite product of rings by the `n`-th power of an ideal is the product of
the quotients by the `n`-th powers of the coordinate images. -/
noncomputable def quotientPiPowEquiv {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i)) (n : ℕ) :
    ((∀ i, R i) ⧸ I ^ n) ≃+* ∀ i, R i ⧸ (I.map (Pi.evalRingHom R i)) ^ n :=
  (quotientPiEquiv R (I ^ n)).trans (RingEquiv.piCongrRight fun i ↦
    (Ideal.quotientEquivAlgOfEq (R i) (Ideal.map_pow _ _ _)).toRingEquiv)

/-- `Rig.quotientPiPowEquiv` is evaluation on classes. -/
theorem quotientPiPowEquiv_mk {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i))
    (n : ℕ) (x : ∀ i, R i) (i : ι) :
    quotientPiPowEquiv R I n (Ideal.Quotient.mk (I ^ n) x) i =
      Ideal.Quotient.mk ((I.map (Pi.evalRingHom R i)) ^ n) (x i) := rfl

/-- `Rig.quotientPiPowEquiv` commutes with the transition maps of the two inverse systems. -/
theorem quotientPiPowEquiv_factorPow {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i))
    {m n : ℕ} (h : m ≤ n) (x : (∀ i, R i) ⧸ I ^ n) (i : ι) :
    quotientPiPowEquiv R I m (Ideal.Quotient.factorPow I h x) i =
      Ideal.Quotient.factorPow (I.map (Pi.evalRingHom R i)) h
        (quotientPiPowEquiv R I n x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The comparison of the adic completion of a finite product of rings with the product of the
adic completions at the coordinate images of the ideal. -/
noncomputable def adicCompletionPiMap {ι : Type*}
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i)) :
    AdicCompletion I (∀ i, R i) →+*
      ∀ i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i) :=
  _root_.RingHom.pi fun i ↦
    let : Algebra (∀ i, R i) (R i) := (Pi.evalRingHom R i).toAlgebra
    Stacks.Nagata.PthRootDescent.mapAdicCompletion I (I.map (Pi.evalRingHom R i)) le_rfl

/-- The evaluations of `Rig.adicCompletionPiMap` are the coordinates of
`Rig.quotientPiPowEquiv`. -/
theorem adicCompletionPiMap_evalₐ {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i))
    (x : AdicCompletion I (∀ i, R i)) (n : ℕ) (i : ι) :
    AdicCompletion.evalₐ (I.map (Pi.evalRingHom R i)) n (adicCompletionPiMap R I x i) =
      quotientPiPowEquiv R I n (AdicCompletion.evalₐ I n x) i := by
  let : Algebra (∀ i, R i) (R i) := (Pi.evalRingHom R i).toAlgebra
  change AdicCompletion.evalₐ _ n (Stacks.Nagata.PthRootDescent.mapAdicCompletion I _ le_rfl x) = _
  rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  rfl

/-- The adic completion of a finite product of rings is the product of the adic completions at
the coordinate images of the ideal. -/
noncomputable def adicCompletionPiEquiv {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] (I : Ideal (∀ i, R i)) :
    AdicCompletion I (∀ i, R i) ≃+*
      ∀ i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i) := by
  refine RingEquiv.ofBijective (adicCompletionPiMap R I) ⟨?_, ?_⟩
  · intro x y h
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    apply (quotientPiPowEquiv R I n).injective
    ext i
    rw [← adicCompletionPiMap_evalₐ, ← adicCompletionPiMap_evalₐ, h]
  · let g (n : ℕ) : (∀ i, AdicCompletion (I.map (Pi.evalRingHom R i)) (R i)) →+*
        (∀ i, R i) ⧸ I ^ n :=
      (quotientPiPowEquiv R I n).symm.toRingHom.comp
        (_root_.RingHom.pi fun i ↦ (AdicCompletion.evalₐ _ n).toRingHom.comp
          (Pi.evalRingHom _ i))
    have hg {m n : ℕ} (h : m ≤ n) :
        (Ideal.Quotient.factorPow I h).comp (g n) = g m := by
      ext x
      apply (quotientPiPowEquiv R I m).injective
      ext i
      change quotientPiPowEquiv R I m
        (Ideal.Quotient.factorPow I h ((quotientPiPowEquiv R I n).symm _)) i = _
      rw [quotientPiPowEquiv_factorPow, RingEquiv.apply_symm_apply]
      change Ideal.Quotient.factorPow _ h (AdicCompletion.evalₐ _ n (x i)) =
        quotientPiPowEquiv R I m ((quotientPiPowEquiv R I m).symm _) i
      rw [RingEquiv.apply_symm_apply, AdicCompletion.factorPow_evalₐ]
      rfl
    intro x
    refine ⟨AdicCompletion.liftRingHom I g (fun h ↦ hg h) x, ?_⟩
    ext i : 1
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [adicCompletionPiMap_evalₐ, AdicCompletion.evalₐ_liftRingHom]
    exact congrFun ((quotientPiPowEquiv R I n).apply_symm_apply _) i

/-- Extending an ideal along two commuting routes of a square of ring maps gives comparable
ideals. -/
private theorem map_map_le_of_comp_eq {A A' B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] (I : Ideal A) (a : A →+* A') (f : A' →+* B') (ψ : A →+* B)
    (b : B →+* B') (h : f.comp a = b.comp ψ) : (I.map a).map f ≤ (I.map ψ).map b := by
  rw [Ideal.map_map, Ideal.map_map, h]

/-- **The completed principal localization of a finite product.** The completed principal
localization of `∏ B i` over `A` at `r` is the product of those of the factors, compatibly with
the maps from the completed principal localization of `A`. -/
theorem exists_completedAway_pi_equiv {A : Type*} [CommRing A]
    {ι : Type*} [Finite ι] (B : ι → Type*) [∀ i, CommRing (B i)]
    (φ : ∀ i, A →+* B i) (I : Ideal A) (r : A) :
    ∃ e : AdicCompletion (((I.map (_root_.RingHom.pi φ)).map
        (algebraMap (∀ i, B i) (Localization.Away ((_root_.RingHom.pi φ) r)))))
        (Localization.Away ((_root_.RingHom.pi φ) r)) ≃+*
      ∀ i, AdicCompletion ((I.map (φ i)).map
        (algebraMap (B i) (Localization.Away (φ i r)))) (Localization.Away (φ i r)),
      e.toRingHom.comp (RingHom.completedAwayMap (_root_.RingHom.pi φ) I r) =
        _root_.RingHom.pi (fun i ↦ RingHom.completedAwayMap (φ i) I r) := by
  cases nonempty_fintype ι
  let S := fun i ↦ Localization.Away (φ i r)
  let L := Localization.Away ((_root_.RingHom.pi φ) r)
  let J : Ideal L := (I.map (_root_.RingHom.pi φ)).map (algebraMap (∀ i, B i) L)
  let Ji (i : ι) : Ideal (S i) := (I.map (φ i)).map (algebraMap (B i) (S i))
  let eL : L ≃+* ∀ i, S i := localizationAwayPiEquiv B ((_root_.RingHom.pi φ) r)
  let K : Ideal (∀ i, S i) := J.map eL.toRingHom
  have hJi (i : ι) : K.map (Pi.evalRingHom S i) = Ji i := by
    dsimp [K, J, Ji]
    simp only [Ideal.map_map]
    congr 1
    ext a
    exact localizationAwayPiEquiv_algebraMap B ((_root_.RingHom.pi φ) r)
      ((_root_.RingHom.pi φ) a) i
  let eC : AdicCompletion J L ≃+* AdicCompletion K (∀ i, S i) :=
    adicCompletionCongr eL J K rfl
  let eP := adicCompletionPiEquiv S K
  let eI := RingEquiv.piCongrRight (fun i ↦
    adicCompletionCongr (RingEquiv.refl (S i)) (K.map (Pi.evalRingHom S i)) (Ji i)
      (by simpa using hJi i))
  refine ⟨eC.trans (eP.trans eI), ?_⟩
  let Af := Localization.Away r
  let Ia : Ideal Af := I.map (algebraMap A Af)
  let f : Af →+* L := IsLocalization.Away.map Af L (_root_.RingHom.pi φ) r
  let fi (i : ι) : Af →+* S i := IsLocalization.Away.map Af (S i) (φ i) r
  have hcomm : f.comp (algebraMap A Af) = (algebraMap (∀ i, B i) L).comp (_root_.RingHom.pi φ) :=
    RingHom.ext fun a ↦ (IsLocalization.map_eq _ _ : f (algebraMap A Af a) = _)
  have hcomm_i (i : ι) : (fi i).comp (algebraMap A Af) =
      (algebraMap (B i) (S i)).comp (φ i) :=
    RingHom.ext fun a ↦ (IsLocalization.map_eq _ _ : fi i (algebraMap A Af a) = _)
  have hloc (i : ι) : (Pi.evalRingHom S i).comp (eL.toRingHom.comp f) = fi i := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hcomm, hcomm_i i]
    exact localizationAwayPiEquiv_algebraMap B ((_root_.RingHom.pi φ) r)
      ((_root_.RingHom.pi φ) a) i
  ext x i : 2
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  have hrefl : (K.map (Pi.evalRingHom S i)).map (RingEquiv.refl (S i)).toRingHom = Ji i := by
    simpa using hJi i
  change AdicCompletion.evalₐ (Ji i) n
    (adicCompletionMap (RingEquiv.refl (S i)).toRingHom (K.map (Pi.evalRingHom S i)) (Ji i)
        hrefl.le
      (adicCompletionPiMap S K (adicCompletionMap eL.toRingHom J K le_rfl
        (RingHom.completedAwayMap (_root_.RingHom.pi φ) I r x)) i)) = _
  rw [adicCompletionMap_evalₐ, adicCompletionPiMap_evalₐ, adicCompletionMap_evalₐ]
  have hf (i : ι) : Ia.map (fi i) ≤ Ji i := map_map_le_of_comp_eq I _ _ _ _ (hcomm_i i)
  have hmain : ∀ n, AdicCompletion.evalₐ J n
      (RingHom.completedAwayMap (_root_.RingHom.pi φ) I r x) =
      Ideal.quotientMap (J ^ n) f
        (by
          let : Algebra Af L := f.toAlgebra
          exact Stacks.Nagata.PthRootDescent.pow_le_comap_pow
            (map_map_le_of_comp_eq I _ _ _ _ hcomm) n)
        (AdicCompletion.evalₐ Ia n x) := fun n ↦ by
    let : Algebra Af L := f.toAlgebra
    exact Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion _ n x
  rw [hmain n]
  let : Algebra Af (S i) := (fi i).toAlgebra
  change _ = AdicCompletion.evalₐ (Ji i) n
    (Stacks.Nagata.PthRootDescent.mapAdicCompletion Ia (Ji i) (hf i) x)
  rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ Ia n x)
  rw [← ha]
  simp only [Ideal.quotientMap_mk, quotientPiPowEquiv_mk]
  exact congrArg (Ideal.Quotient.mk ((Ji i) ^ n)) (DFunLike.congr_fun (hloc i) a)

/-- The inverse of an isomorphism onto a finite product matching the ideals defining the
topologies is continuous. -/
theorem continuous_symm_pi_of_map_ideal {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {ι : Type*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, TopologicalSpace (S i)]
    [∀ i, IsTopologicalRing (S i)] (e : R ≃+* ∀ i, S i)
    (I : Ideal R) (J : ∀ i, Ideal (S i)) (hI : _root_.IsAdic I)
    (hJ : ∀ i, _root_.IsAdic (J i))
    (hmap : ∀ i, I.map ((Pi.evalRingHom S i).comp e.toRingHom) = J i) :
    Continuous e.symm := by
  apply continuous_of_continuousAt_zero e.symm.toRingHom
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hpre : e.symm ⁻¹' (↑(I ^ n) : Set R) =
      ⋂ i, (fun x : ∀ i, S i ↦ x i) ⁻¹' (↑(J i ^ n) : Set (S i)) := by
    ext x
    have hx : e.symm x ∈ I ^ n ↔ x ∈ (I ^ n).map e.toRingHom := by
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      refine ⟨fun h ↦ ⟨e.symm x, h, e.apply_symm_apply x⟩, ?_⟩
      rintro ⟨y, hy, rfl⟩
      simpa using hy
    change e.symm x ∈ I ^ n ↔ _
    rw [hx, ← Ideal.piOrderIso.symm_apply_apply ((I ^ n).map e.toRingHom)]
    change (∀ i, x i ∈ ((I ^ n).map e.toRingHom).map (Pi.evalRingHom S i)) ↔ _
    simp only [Ideal.map_map, Ideal.map_pow, hmap, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe]
  change e.symm ⁻¹' (↑(I ^ n) : Set R) ∈ nhds 0
  rw [hpre]
  refine IsOpen.mem_nhds (isOpen_iInter_of_finite fun i ↦
    ((isAdic_iff.mp (hJ i)).1 n).preimage (continuous_apply i)) ?_
  simp

/-- An adic completion along a finitely generated ideal, with its own adic topology, is an adic
topological ring. -/
theorem isAdic_adicCompletion {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) :
    letI : WithIdeal (AdicCompletion I R) :=
      ⟨I.map (algebraMap R (AdicCompletion I R))⟩
    TopologicalRing.IsAdic (AdicCompletion I R) := by
  let C := AdicCompletion I R
  let J := I.map (algebraMap R C)
  let : WithIdeal C := ⟨J⟩
  have hJ : _root_.IsAdic J := rfl
  have hc := hJ.isAdicComplete_iff.mp
    ((IsAdicComplete.map_algebraMap_iff I C).mpr (AdicCompletion.isAdicComplete hI))
  refine ⟨⟨J, ⟨?_, (isAdic_iff.mp hJ).2⟩, hJ⟩, hc.2, hc.1⟩
  simpa only [pow_one] using (isAdic_iff.mp hJ).1 1

/-- Topological finite type transports along an isomorphism of the targets whose inverse is
continuous. -/
theorem isTopologicallyOfFiniteType_of_ringEquiv {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (hc : Continuous e.symm)
    (hg : TopologicalRing.IsTopologicallyOfFiniteType g) :
    TopologicalRing.IsTopologicallyOfFiniteType f := by
  obtain ⟨n, p, hp, hd⟩ := hg
  refine ⟨n, e.symm.toRingHom.comp p, ?_, e.symm.surjective.denseRange.comp hd hc⟩
  rw [RingHom.comp_assoc, hp, ← he, ← RingHom.comp_assoc]
  simp

end Pi

/-- **Rig-flatness is preserved by finite products of targets** (axiom (3) of Situation 0CBA).
The completed principal localization of the product is the product of the completed principal
localizations (`Rig.exists_completedAway_pi_equiv`), under which the induced map of completed
localizations becomes the product of those of the factors; naive rig-flatness of a product of
maps is `Rig.RingHom.isNaivelyRigFlat_pi`. -/
theorem rigFlat_finiteProductPreserves :
    TopologicalRing.FiniteProductPreserves
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        IsNoetherianAdic R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) := by
  intro B _ _ _ _ hBweak hBcount ι _ A _ _ _ _ hAweak hAcount f hf hB hA hflat
  have : IsNoetherianRing B := hB.2
  have (i : ι) : IsNoetherianRing (A i) := (hA i).2
  have hfirst := TopologicalRing.adicTopologicallyFiniteType_isLocal.finiteProduct
    hBweak hBcount A hAweak hAcount f hf (exists_fg_isAdic_of_isAdicRing hB.1)
    (fun i ↦ exists_fg_isAdic_of_isAdicRing (hA i).1)
    (fun i ↦ ⟨(hflat i).1, (hflat i).2.1⟩)
  refine ⟨hfirst.1, hfirst.2, ?_⟩
  intro I hI hImap r
  have hlocal := fun i ↦ (hflat i).2.2 I hI
    (_root_.RingHom.isAdic_map_of_isAdic (f i) (hflat i).1 hI) r
  obtain ⟨e, he⟩ := exists_completedAway_pi_equiv A f I r
  let R := Localization.Away r
  let J := I.map (algebraMap B R)
  let C := AdicCompletion J R
  let K := J.map (algebraMap R C)
  let S := fun i ↦ Localization.Away (f i r)
  let Ji := fun i ↦ (I.map (f i)).map (algebraMap (A i) (S i))
  let Ci := fun i ↦ AdicCompletion (Ji i) (S i)
  let Ki := fun i ↦ (Ji i).map (algebraMap (S i) (Ci i))
  let T := Localization.Away ((_root_.RingHom.pi f) r)
  let L := (I.map (_root_.RingHom.pi f)).map (algebraMap (∀ i, A i) T)
  let D := AdicCompletion L T
  let M := L.map (algebraMap T D)
  let : WithIdeal C := ⟨K⟩
  let (i : ι) : WithIdeal (Ci i) := ⟨Ki i⟩
  let : WithIdeal D := ⟨M⟩
  let g : C →+* D := RingHom.completedAwayMap (_root_.RingHom.pi f) I r
  let gi : ∀ i, C →+* Ci i := fun i ↦ RingHom.completedAwayMap (f i) I r
  have hmap : K.map g = M := RingHom.completedAwayMap_map_ideal (_root_.RingHom.pi f) I r
  have hmapi (i : ι) : K.map (gi i) = Ki i := RingHom.completedAwayMap_map_ideal (f i) I r
  have hC := isAdic_adicCompletion J (Ideal.fg_of_isNoetherianRing J)
  have hCi := fun i ↦ isAdic_adicCompletion (Ji i) (Ideal.fg_of_isNoetherianRing (Ji i))
  have hprod := TopologicalRing.adicTopologicallyFiniteType_isLocal.finiteProduct
    (weaklyAdmissible_of_isAdicRing hC) (countablyGenerated_nhds_of_isAdicRing hC)
    Ci (fun i ↦ weaklyAdmissible_of_isAdicRing (hCi i))
    (fun i ↦ countablyGenerated_nhds_of_isAdicRing (hCi i)) gi
    (fun i ↦ continuous_adic_of_map_le K (Ki i) (gi i) (hmapi i).le)
    ⟨K, (Ideal.fg_of_isNoetherianRing J).map _, rfl⟩
    (fun i ↦ ⟨Ki i, (Ideal.fg_of_isNoetherianRing (Ji i)).map _, rfl⟩)
    (fun i ↦ ⟨(hlocal i).1, (hlocal i).2.1⟩)
  have hge : ∀ i, M.map ((Pi.evalRingHom Ci i).comp e.toRingHom) = Ki i := by
    intro i
    rw [← hmap, Ideal.map_map, RingHom.comp_assoc, he]
    exact hmapi i
  have hcont : Continuous e.symm :=
    continuous_symm_pi_of_map_ideal e M Ki rfl (fun _ ↦ rfl) hge
  have hg : _root_.RingHom.IsAdic g := ⟨K, rfl, by rw [hmap]; rfl⟩
  have hgft := isTopologicallyOfFiniteType_of_ringEquiv g (_root_.RingHom.pi gi) e he hcont
    hprod.2
  exact RingHom.isNaivelyRigFlat_of_ringEquiv g (_root_.RingHom.pi gi) e he ⟨hg, hgft⟩
    (RingHom.isNaivelyRigFlat_pi gi hprod hlocal)

/-- **Rig-flatness is a local property of arrows of `WAdm^Noeth`** (Stacks 0GGU): it ascends
along completed étale localization diagrams, descends along faithfully flat ones, and is
preserved by finite products of targets. -/
@[stacks 0GGU]
theorem rigFlat_isLocalNoetherian :
    TopologicalRing.PropertyIsLocalNoetherian
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) where
  localizationPreserves := rigFlat_localizationPreserves
  faithfullyFlatDescent := rigFlat_faithfullyFlatDescent
  finiteProduct := rigFlat_finiteProductPreserves

end Local

end Rig

end
