module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSourceRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure

/-!
# Composition of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GBI** says that if `P` is a
local property of morphisms of `WAdm^{count}` which is stable under composition (Situation
0GBH), and `f : X ⟶ Y`, `g : Y ⟶ Z` are morphisms of locally countably indexed formal algebraic
spaces over `S` satisfying the equivalent conditions of Stacks 0ANG, then so does `g ∘ f`.
**Stacks 0GBK** defines stability under composition for a local property of morphisms of
`WAdm^{Noeth}` and asserts the same for morphisms of locally Noetherian formal algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_comp_of_spfPresentation`: the
  composition axiom read on a composable pair of morphisms of affine formal algebraic spaces
  whose middle object is presented by a ring of the class, through Stacks 0AN0.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_chartFactorization_comp_of_atlas`: the
  covering of the proof of Stacks 0GBI, with intermediate charts drawn from a prescribed atlas.
* `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyCountablyIndexed`
  — **Stacks 0GBI**.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian`:
  **Stacks 0GBK**, the variant of Stacks 0GBI for locally Noetherian formal algebraic spaces.

## Implementation notes

Condition (1) of Stacks 0ANG, `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap`,
quantifies over presentations of the two charts, so composing it along `U ⟶ V ⟶ W` needs a
presentation of the middle chart `V` by a ring of the class. The proof of Stacks 0GBI chooses
its charts, and they are chosen here inside atlases of `X`, `Y` and `Z` whose members are
countably indexed, resp. Noetherian, refined by representable étale maps: those properties pass to
affine formal algebraic spaces representable étale over such a chart by clauses (1) and (5)
of Stacks 0AKQ, and they give a presentation by a ring of `WAdm^{count}` (Stacks 0AN1),
resp. by the presenting ring, which is Noetherian and adic (Stacks 0AIC). The two morphisms
`U ⟶ V` and `V ⟶ W` are then realized by continuous homomorphisms by Stacks 0AN0, and the
uniqueness clause of Stacks 0AN0 identifies their composite with any given realization of
`U ⟶ W`.

Since every chart of the covering is presented, the implication (3) ⟹ (1) of Stacks 0ANG
applies on that covering itself,
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`;
this is what the Noetherian variant uses, for which the charts of an arbitrary covering are not
known to be Noetherian. Situation 0CBA assumes `P` invariant under isomorphism of source and
target; that is the hypothesis `hPiso` of both statements, in the shape of the (3) ⟹ (1)
lemmas.

The fibre products of the proof are formal algebraic spaces by Stacks 0AJ3,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`.

## References

* [Stacks Project, Tag 0GBH](https://stacks.math.columbia.edu/tag/0GBH)
* [Stacks Project, Tag 0GBI](https://stacks.math.columbia.edu/tag/0GBI)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The composition axiom of Situation 0GBH, read on a composable pair `U ⟶ V ⟶ W` of
morphisms of affine formal algebraic spaces whose middle object is presented by a ring of the
class `C`, through the anti-equivalence of **Stacks 0AN0**. -/
theorem hasPropertyOnAffineChartMap_comp_of_spfPresentation
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcomp : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
    {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : V ⟶ W)
    (hV : ∃ PV : SpfPresentation B S hS V, C PV.ring)
    (ht : HasPropertyOnAffineChartMap B S hS C P t)
    (hs : HasPropertyOnAffineChartMap B S hS C P s) :
    HasPropertyOnAffineChartMap B S hS C P (t ≫ s) := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eW g hg
  obtain ⟨PV, hCM⟩ := hV
  obtain ⟨eV⟩ := PV.iso
  have hM := hCwa PV.ring hCM
  have hR := hCwa R hCR
  obtain ⟨gt, hgt, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hM hR
    (eU.inv ≫ t ≫ eV.hom)
  obtain ⟨gs, hgs, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hM
    (eV.inv ≫ s ≫ eW.hom)
  have hPt : P gt.toRingHom := ht PV.ring R hCM hCR hM PV.system E eU eV gt (by rw [hgt]; simp)
  have hPs : P gs.toRingHom := hs A PV.ring hCA hCM hA D PV.system eV eW gs (by rw [hgs]; simp)
  have heq : ContinuousHom.comp hM hA gt gs = g := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA hR
      (eU.inv ≫ (t ≫ s) ≫ eW.hom)).unique ?_ ?_
    · rw [← formalSpectrumMap_comp_eq hM hA gt gs, hgt, hgs]
      simp
    · rw [hg]
      simp
  rw [← heq, ContinuousHom.comp_toRingHom]
  exact hcomp hCA hCM hCR gt.toRingHom gs.toRingHom gt.continuous gs.continuous hPt hPs

/-- An affine étale covering `{Vⱼ ⟶ Y}` pulls back along a morphism `f : X ⟶ Y` of formal
algebraic spaces to an affine étale covering of `X` refining a prescribed atlas of `X`: its
members `Uᵢ` map to members `V (k i)` of the covering over `f`, and are representable étale
over members of the atlas, so they inherit every property `Q` of the members of the atlas which
passes along representable étale maps of affine formal algebraic spaces.

The members are those of atlases of the fibre products `Vⱼ ×_Y Xₗ` of the covering with the
atlas `{Xₗ ⟶ X}`, which are formal algebraic spaces by **Stacks 0AJ3**. -/
theorem exists_affineEtaleCover_pullback_refining_atlas
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) {J : Type (u + 1)} (V : J → FppfSheaf B S hS)
    (v : ∀ j, V j ⟶ Y) (hV : IsAffineEtaleCover B S hS V v) :
    ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (k : I → J) (u : ∀ i, U i ⟶ X)
      (t : ∀ i, U i ⟶ V (k i)),
      IsAffineEtaleCover B S hS U u ∧ (∀ i, Q (U i)) ∧ ∀ i, u i ≫ f = t i ≫ v (k i) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨L, Xl, xl, hXlaff, hXlet, hXlsurj, hXlQ⟩ := hXQ
  choose M Mo m hMaff hMet hMsurj using fun (l : L) (j : J) ↦
    (isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (v j) (xl l ≫ f) hY
      (hV.1 j) (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hXlaff l))).2
  let e : ∀ n : Σ l, Σ j, M l j, Mo n.1 n.2.1 n.2.2 ⟶ Xl n.1 := fun n ↦
    m n.1 n.2.1 n.2.2 ≫ pullback.snd (v n.2.1) (xl n.1 ≫ f)
  have he : ∀ n, IsRepresentableEtale B S hS (e n) := fun n ↦
    IsRepresentableEtale.comp B S hS (hMet n.1 n.2.1 n.2.2)
      (isRepresentableEtale_pullback_snd B S hS (v n.2.1) (xl n.1 ≫ f) (hV.2.1 n.2.1))
  refine ⟨Σ l, Σ j, M l j, fun n ↦ Mo n.1 n.2.1 n.2.2, fun n ↦ n.2.1, fun n ↦ e n ≫ xl n.1,
    fun n ↦ m n.1 n.2.1 n.2.2 ≫ pullback.fst (v n.2.1) (xl n.1 ≫ f),
    ⟨fun n ↦ hMaff n.1 n.2.1 n.2.2, fun n ↦ IsRepresentableEtale.comp B S hS (he n) (hXlet n.1),
      ?_⟩,
    fun n ↦ hQ (e n) (hMaff n.1 n.2.1 n.2.2) (hXlaff n.1) (he n) (hXlQ n.1), fun n ↦ ?_⟩
  · exact isLocallySurjective_sigmaDesc_comp' B S hS xl
      (fun l (p : Σ j, M l j) ↦ m l p.1 p.2 ≫ pullback.snd (v p.1) (xl l ≫ f)) hXlsurj
      (fun l ↦ isLocallySurjective_sigmaDesc_comp' B S hS
        (fun j ↦ pullback.snd (v j) (xl l ≫ f)) (m l)
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (xl l ≫ f) v hV.2.2)
        (hMsurj l))
  · simp only [e, Category.assoc, pullback.condition]

/-- The covering constructed in the proofs of **Stacks 0GBI** and **Stacks 0GBK**, with all its
charts taken inside prescribed atlases of `X`, `Y` and `Z` whose members have a property `Q`
which passes to affine formal algebraic spaces representable étale over them: an affine étale
covering `{Uᵢ ⟶ X}` with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` and `Vᵢ ⟶ Wᵢ ⟶ Z` through affine étale
charts, the `Uᵢ`, `Vᵢ`, `Wᵢ` satisfying `Q` and each `Vᵢ ⟶ Wᵢ` having `P`.

The atlas `{Wₖ ⟶ Z}` is pulled back to `Y` refining the atlas of `Y`, which gives the `Vᵢ`
and, by condition (1) for `g`, `P` on `Vᵢ ⟶ Wᵢ`; the covering `{Vᵢ ⟶ Y}` is then pulled back
to `X` refining the atlas of `X`
(`AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_pullback_refining_atlas`). -/
theorem exists_affineEtaleCover_chartFactorization_comp_of_atlas
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hYQ : HasAffineEtaleAtlasWithProperty B S hS Y Q)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (hZQ : HasAffineEtaleAtlasWithProperty B S hS Z Q)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    ∃ (I : Type (u + 1)) (U V W : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (t : ∀ i, U i ⟶ V i) (s : ∀ i, V i ⟶ W i) (v : ∀ i, V i ⟶ Y) (w : ∀ i, W i ⟶ Z),
      IsAffineEtaleCover B S hS U u ∧ (∀ i, Q (U i)) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) ∧ (∀ i, Q (V i)) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) ∧ (∀ i, Q (W i)) ∧
        (∀ i, IsRepresentableEtale B S hS (v i)) ∧
        (∀ i, IsRepresentableEtale B S hS (w i)) ∧
        (∀ i, u i ≫ f = t i ≫ v i) ∧ (∀ i, v i ≫ g = s i ≫ w i) ∧
        ∀ i, HasPropertyOnAffineChartMap B S hS C P (s i) := by
  obtain ⟨K, Wk, wk, hWkaff, hWket, hWksurj, hWkQ⟩ := hZQ
  obtain ⟨N, Vn, kn, vn, sn, hVcover, hVQ, hsq₂⟩ :=
    exists_affineEtaleCover_pullback_refining_atlas B S hS Q hQ g hYQ hZ Wk wk
      ⟨hWkaff, hWket, hWksurj⟩
  obtain ⟨I, U, ki, u, t, hUcover, hUQ, hsq₁⟩ :=
    exists_affineEtaleCover_pullback_refining_atlas B S hS Q hQ f hXQ hY Vn vn hVcover
  exact ⟨I, U, fun i ↦ Vn (ki i), fun i ↦ Wk (kn (ki i)), u, t, fun i ↦ sn (ki i),
    fun i ↦ vn (ki i), fun i ↦ wk (kn (ki i)), hUcover, hUQ, fun i ↦ hVcover.1 (ki i),
    fun i ↦ hVQ (ki i), fun i ↦ hWkaff (kn (ki i)), fun i ↦ hWkQ (kn (ki i)),
    fun i ↦ hVcover.2.1 (ki i), fun i ↦ hWket (kn (ki i)), hsq₁, fun i ↦ hsq₂ (ki i),
    fun i ↦ hg (Vn (ki i)) (Wk (kn (ki i))) (vn (ki i)) (wk (kn (ki i))) (sn (ki i))
      (hVcover.1 (ki i)) (hWkaff (kn (ki i))) (hVcover.2.1 (ki i)) (hWket (kn (ki i)))
      (hsq₂ (ki i))⟩

/-- **Stacks 0GBI**, in the form the covering of its proof produces, with every chart of the
covering presented by a ring of the class `C`: if `P` is stable under composition on arrows of
`C`, then the composite of two morphisms satisfying condition (1) of Stacks 0ANG satisfies
condition (3) on a covering whose members, and the charts of the target they factor through,
are presented by rings of `C`. The atlases of `X`, `Y` and `Z` are asked to consist of charts
with a property `Q` which passes along representable étale maps of affine formal algebraic
spaces and makes them presented by rings of `C`. -/
theorem exists_presentedSourceCover_comp_of_atlas
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcomp : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    (hQC : ∀ V : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS V → Q V →
      ∃ PV : SpfPresentation B S hS V, C PV.ring)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hYQ : HasAffineEtaleAtlasWithProperty B S hS Y Q)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (hZQ : HasAffineEtaleAtlasWithProperty B S hS Z Q)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    ∃ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (w : ∀ i, W i ⟶ Z) (t : ∀ i, U i ⟶ W i),
      IsAffineEtaleCover B S hS U u ∧ (∀ i, ∃ PU : SpfPresentation B S hS (U i), C PU.ring) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) ∧
        (∀ i, ∃ PW : SpfPresentation B S hS (W i), C PW.ring) ∧
        (∀ i, IsRepresentableEtale B S hS (w i)) ∧ (∀ i, u i ≫ f ≫ g = t i ≫ w i) ∧
        ∀ i, HasPropertyOnAffineChartMap B S hS C P (t i) := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hUQ, hVaffine, hVQ, hWaffine, hWQ, hv, hw, hsq₁,
    hsq₂, hs⟩ := exists_affineEtaleCover_chartFactorization_comp_of_atlas B S hS C P Q hQ f g
      hXQ hY hYQ hZ hZQ hg
  refine ⟨I, U, W, u, w, fun i ↦ t i ≫ s i, hUcover,
    fun i ↦ hQC (U i) (hUcover.1 i) (hUQ i), hWaffine, fun i ↦ hQC (W i) (hWaffine i) (hWQ i),
    hw, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]
  · exact hasPropertyOnAffineChartMap_comp_of_spfPresentation B S hS C P hCwa hcomp
      (t i) (s i) (hQC (V i) (hVaffine i) (hVQ i))
      (hf (U i) (V i) (u i) (v i) (t i) (hUcover.1 i) (hVaffine i) (hUcover.2.1 i) (hv i)
        (hsq₁ i)) (hs i)

/-- **Stacks 0GBI**, in the form the covering of its proof produces: condition (3) of Stacks
0ANG for the composite, from
`AlgebraicGeometry.FormalSpace.exists_presentedSourceCover_comp_of_atlas` by forgetting the
presentations. -/
theorem hasPropertyAfterSourceCover_comp_of_atlas
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcomp : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    (hQC : ∀ V : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS V → Q V →
      ∃ PV : SpfPresentation B S hS V, C PV.ring)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hYQ : HasAffineEtaleAtlasWithProperty B S hS Y Q)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (hZQ : HasAffineEtaleAtlasWithProperty B S hS Z Q)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P (f ≫ g) := by
  obtain ⟨I, U, W, u, w, t, hUcover, -, hWaffine, -, hw, hsq, ht⟩ :=
    exists_presentedSourceCover_comp_of_atlas B S hS C P hCwa hcomp Q hQ hQC f g hXQ hY hYQ hZ
      hZQ hf hg
  exact ⟨I, U, u, hUcover, fun i ↦ ⟨W i, w i, t i, hWaffine i, hw i, hsq i, ht i⟩⟩

/-- A countably indexed affine formal algebraic space is presented by a ring of `WAdm^{count}`:
this is the implication (1) ⟹ (2) of **Stacks 0AN1**. -/
theorem exists_spfPresentation_of_isCountablyIndexed (V : FppfSheaf B S hS)
    (hV : IsCountablyIndexed B S hS V) :
    ∃ PV : SpfPresentation B S hS V, TopologicalRing.IsCountablyWeaklyAdmissible PV.ring := by
  obtain ⟨M, i₁, i₂, i₃, i₄, D, hM, hc, e⟩ := exists_quotientSystem_of_isCountablyIndexed B S hS hV
  exact ⟨⟨M, D, e⟩, hM, hc⟩

/-- A Noetherian affine formal algebraic space is presented by a ring of `WAdm^{Noeth}`: its
presenting ring, through the quotient system of Stacks 0AIC. -/
theorem exists_spfPresentation_of_isNoetherian (V : FppfSheaf B S hS)
    (hV : IsNoetherian B S hS V) :
    ∃ PV : SpfPresentation B S hS V, TopologicalRing.IsNoetherianAdic PV.ring := by
  obtain ⟨-, M, i₁, i₂, i₃, i₄, ⟨-, ⟨Pr⟩⟩, hnoeth, hadic⟩ := hV
  exact ⟨⟨M, Pr.quotientSystem, ⟨Pr.formalSpectrumIso⟩⟩, hadic, hnoeth⟩

/-- **Stacks 0GBI.** Let `P` be a local property of morphisms of `WAdm^{count}` which is stable
under composition, and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally countably
indexed formal algebraic spaces over `S`. If `f` and `g` satisfy the equivalent conditions of
Stacks 0ANG, then so does `g ∘ f`: the conclusion lists all three of them. Being a local
property in the sense of Situation 0CBA is `hP.isLocal` together with `hPiso`, the invariance of
`P` under isomorphism of source and target that the situation assumes.

The covering of the proof is
`AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_chartFactorization_comp_of_atlas`, built
on the countably indexed atlas of `Y`; its intermediate charts are countably indexed by clause
(1) of Stacks 0AKQ, hence presented by rings of `WAdm^{count}` (Stacks 0AN1), and the
composition axiom applies through Stacks 0AN0. That gives condition (3) for `g ∘ f`; condition
(1) follows by the implication (3) ⟹ (1) of Stacks 0ANG, from the presented refinement of a
covering of the source and the locality of `P`, and condition (2) by (1) ⟹ (2). -/
@[stacks 0GBI]
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyCountablyIndexed
    (hP : TopologicalRing.PropertyIsStableUnderComposition P)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsCountablyWeaklyAdmissible B →
      TopologicalRing.IsCountablyWeaklyAdmissible A →
      TopologicalRing.IsCountablyWeaklyAdmissible B' →
      TopologicalRing.IsCountablyWeaklyAdmissible A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g) ∧
      HasPropertyAfterTargetCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g) ∧
      HasPropertyAfterSourceCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g) := by
  have h3 : HasPropertyAfterSourceCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g) :=
    hasPropertyAfterSourceCover_comp_of_atlas B S hS _ P (fun _ _ _ _ _ h ↦ h.1)
      (fun hA hM hR φ ψ hφ hψ hPφ hPψ ↦ hP.comp hR hM hA φ ψ hφ hψ hPφ hPψ)
      (IsCountablyIndexed B S hS)
      (fun e hV' hV he hVc ↦ isCountablyIndexed_of_isRepresentable' B S hS e hV' hV he.1 hVc)
      (fun V _ hV ↦ exists_spfPresentation_of_isCountablyIndexed B S hS V hV)
      f g hX.2 hY.1 hY.2 hZ.1 hZ.2 hf hg
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g) :=
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed B S hS
      P hP.isLocal hPiso (f ≫ g) hX hZ h3
  exact ⟨h1, hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal' B S hS _ P (f ≫ g)
    hX.1 hZ.1 h1, h3⟩

/-- **Stacks 0GBK.** A local property `P` of morphisms of `WAdm^{Noeth}` is *stable under
composition* when `P(B → A) ∧ P(C → B) ⟹ P(C → A)` for arrows of `WAdm^{Noeth}`: that is the
structure `TopologicalRing.PropertyIsStableUnderCompositionNoetherian`, whose `isLocal` field
together with `hPiso` (invariance under isomorphism of source and target, assumed by Situation
0CBA and hence by Remark 0ANI) make `P` local. The variant of Stacks 0GBI then holds for
morphisms between locally Noetherian formal algebraic spaces: if `f : X ⟶ Y` and `g : Y ⟶ Z`
satisfy the equivalent conditions of Stacks 0ANG for `P` on `WAdm^{Noeth}`, so does `g ∘ f`, and
the conclusion lists all three of them.

The covering is
`AlgebraicGeometry.FormalSpace.exists_presentedSourceCover_comp_of_atlas` built on the
Noetherian atlases of `X`, `Y` and `Z`: its charts stay Noetherian along representable étale
maps by clause (5) of Stacks 0AKQ and are then presented by their presenting rings, which are
Noetherian and adic, so the composition axiom applies through Stacks 0AN0 and gives condition
(3) on a covering with presented members. The implication (3) ⟹ (1) of Stacks 0ANG on such a
covering is
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover`,
at the class `WAdm^{Noeth}`, whose closure conditions are clauses of Stacks 0ANB; condition (2)
follows by (1) ⟹ (2). -/
@[stacks 0GBK "the variant of Stacks 0GBI for morphisms between locally Noetherian formal \
algebraic spaces; the definition of stability under composition is \
TopologicalRing.PropertyIsStableUnderCompositionNoetherian"]
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian
    (hP : TopologicalRing.PropertyIsStableUnderCompositionNoetherian P)
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
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P (f ≫ g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsNoetherianAdic P (f ≫ g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P (f ≫ g) := by
  obtain ⟨I, U, W, u, w, t, hUcover, hUpres, hWaffine, hWpres, hw, hsq, ht⟩ :=
    exists_presentedSourceCover_comp_of_atlas B S hS _ P
      (fun _ _ _ _ _ h ↦ h.1.isWeaklyAdmissible)
      (fun hA hM hR φ ψ hφ hψ hPφ hPψ ↦ hP.comp hR hM hA φ ψ hφ hψ hPφ hPψ)
      (IsNoetherian B S hS)
      (fun e hV' hV he hVn ↦ isNoetherian_of_isRepresentable' B S hS e hV' hV he.1
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS e he) hVn)
      (fun V _ hV ↦ exists_spfPresentation_of_isNoetherian B S hS V hV)
      f g hX.2 hY.1 hY.2 hZ.1 hZ.2 hf hg
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P
      (f ≫ g) :=
    hasPropertyOnEveryAffineEtaleDiagram_of_presentedSourceCover B S hS _ P hP.isLocal hPiso
      (fun _ _ _ _ _ hR ↦ ⟨hR.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩)
      (fun {R₁ R₂} _ _ _ _ _ φ _ het hX ↦ by
        let := φ.toAlgebra
        have : Algebra.Etale R₁ R₂ := het
        have : IsNoetherianRing R₁ := hX.2
        exact TopologicalRing.completionOver_isNoetherianAdic φ hX
          (Algebra.FiniteType.isNoetherianRing R₁ R₂))
      (fun e he he' hX ↦ TopologicalRing.isNoetherianAdic_of_ringEquiv e he he' hX)
      (f ≫ g) U W u w t hUcover hWaffine hw hsq ht hUpres hWpres
  exact ⟨h1, hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal' B S hS _ P (f ≫ g)
    hX.1 hZ.1 h1, ⟨I, U, u, hUcover, fun i ↦ ⟨W i, w i, t i, hWaffine i, hw i, hsq i, ht i⟩⟩⟩

end AlgebraicGeometry.FormalSpace

end
