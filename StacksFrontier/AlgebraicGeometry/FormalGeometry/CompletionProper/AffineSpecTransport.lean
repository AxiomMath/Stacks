module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineLocalTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# The completion chart of an affine base, and the descent of Stacks 088B across it

Let `Y` be a scheme with an isomorphism `e : Y ≅ Spec B` for `B` Noetherian, let `I ⊆ B` be an
ideal and let `𝒥 ⊆ 𝒪_Y` be the corresponding quasi-coherent sheaf of ideals. The **completion
chart** of `Y` is

`c = Stacks.Algebraization.adicCompletionChart : Spec (B ^∧) ⟶ Y`,

`Spec` of the completion map followed by `e⁻¹`. Read this way — as a morphism *onto `Y` itself*
rather than onto `Spec B` — it is the morphism along which the second paragraph of the proof of
[Stacks, Tag 088B] replaces `B` by `B ^∧`, and no datum of the situation over `Y` has to be
transported across `e`.

The chart is flat (`Stacks.Algebraization.flat_adicCompletionChart`) and an isomorphism over
`V(𝒥)` (`Stacks.Algebraization.isIso_pullback_snd_adicCompletionChart`), so pullback along it is
an equivalence on `Coh(Y, 𝒥)` (Stacks 0EHQ) and on the `𝒥`-power-torsion coherent modules (More
on Algebra 05EC in sheaf form). That makes the characterizing equation of Stacks 088B and the
morphism it characterizes **descend** across the chart, which is
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionChartPullback` and, at
the completion chart of an affine open `V` of a general base,
`Stacks.Algebraization.exists_isDirectImageCharacterized_morphismRestrict_of_adicCompletionChart`.
Assembled, this reduces `Stacks.Algebraization.HasAffineLocalDirectImageSolution` — the single
remaining binder behind [Stacks, Tag 088C], `hDev` and the first input of [Stacks, Tag 088E] — to
one hypothesis over the chart of each affine open,
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`.

## Main results

* `Stacks.Algebraization.adicCompletionChart`, `…flat_adicCompletionChart`,
  `…comap_adicCompletionChart` and `…isIso_pullback_snd_adicCompletionChart` — the chart and its
  three properties.
* `Stacks.Algebraization.coherentAdicPullback_adicCompletionChart_isEquivalence` and
  `…coherentIdealPowerTorsionPullback_adicCompletionChart_isEquivalence` — flat base change along
  the chart, on coherent adic systems and on power-torsion coherent modules.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionChartPullback` —
  the descent of the second paragraph of the proof of Stacks 088B across the chart.
* `Stacks.Algebraization.affineOpenAdicCompletionChart` and
  `…exists_isDirectImageCharacterized_morphismRestrict_of_adicCompletionChart` — the chart of an
  affine open of a general base, and the descent there.
* `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart` — the whole of
  Stacks 088B at a general base, reduced to the source's second paragraph read over a single
  affine chart.
* `…exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase` — **Stacks 088B
  over the base of the chart**, with no completeness hypothesis on `B`: the chart's base ring is
  `B ^∧`, which is `I B ^∧`-adically complete, so the complete affine case applies there with the
  source's own hypotheses only.
* `Stacks.Algebraization.exists_pullbackCharacterization_of_adicCompletionChartSquares` and
  `…exists_pullbackCharacterization_morphismRestrict_of_adicCompletionChartSquares` — the first
  clause of the hypothesis of `…hasAffineLocalDirectImageSolution_of_adicCompletionChart`, from
  the two base-change squares at the chart.

## What the chart does not buy

**The chart removes the transport across `AlgebraicGeometry.IsAffineOpen.isoSpec`; it does not
remove the base change.** Stacks 088B over a complete base is a statement about a proper morphism
*over* that base, and the chart points from `Spec (B ^∧)` to `Y`, so a proper morphism
`p : X' ⟶ Y` is **not** a morphism over `Spec (B ^∧)`: it does not instantiate the `π'` of
`…exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase`. The only proper
morphism over `Spec (B ^∧)` attached to `p` is the base change `X' ×_Y Spec (B ^∧)`, and
identifying its `δ` and `γ` with the pullbacks along the chart of those of `p` is the pair of
squares `hδ`, `hγ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison`, restated at the
chart as the binders of `…exists_pullbackCharacterization_of_adicCompletionChartSquares`.

So the residue identified in `CompletionProper/AdicBaseChangeSquares.lean` survives the change of
chart unchanged. What remains of the hypothesis of
`…hasAffineLocalDirectImageSolution_of_adicCompletionChart` is, over the chart of each affine open
`V`:

1. the base change of `π ∣_ V` along the chart, with the two comparisons `ι` and `θ` of the
   completed direct images and of the levels — built over `Spec B` in
   `CompletionProper/AdicBaseChangeSituation.lean`, not over the chart;
2. the source's own condition `hc` on the unit away from `V(𝒦)`, over the chart's base;
3. the square `hδ` — proved over `Spec B` as
   `Stacks.Algebraization.adicBaseChangeCompletedComparison_directImageQuotientComparison`;
4. the square `hγ` — **the one live obstruction**: every ingredient of it is proved in
   `CompletionProper/AdicBaseChangeSquares.lean`, and what fails there is the kernel's reduction
   budget on the single application that assembles them;
5. the annihilation of the levelwise kernels and cokernels of the descended `α`, which is the
   sheafification of `Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` —
   recorded as piece 3 in `CompletionProper/AffineLocalSolution.lean`.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0EHQ](https://stacks.math.columbia.edu/tag/0EHQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section Chart

variable {Y : Scheme.{u}} (B : Type u) [CommRing B] (I : Ideal B) (e : Y ≅ Spec (.of B))

/-- **The completion chart of an affine base.** -/
public abbrev adicCompletionChart : Spec (.of (AdicCompletion I B)) ⟶ Y :=
  adicCompletionSpecMap B I ≫ e.inv

/-- The inverse image of `𝒥` along `e⁻¹` is `I 𝒪_{Spec B}`. -/
public theorem comap_iso_inv_eq_adicIdealSheaf {𝒥 : Y.IdealSheafData}
    (h : (adicIdealSheaf B I).comap e.hom = 𝒥) : 𝒥.comap e.inv = adicIdealSheaf B I := by
  subst h
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- The inverse image of `𝒥` along the completion chart is `I B ^∧ 𝒪`. -/
public theorem comap_adicCompletionChart {𝒥 : Y.IdealSheafData}
    (h : (adicIdealSheaf B I).comap e.hom = 𝒥) :
    𝒥.comap (adicCompletionChart B I e) =
      adicIdealSheaf (AdicCompletion I B) (I.map (algebraMap B (AdicCompletion I B))) := by
  rw [show adicCompletionChart B I e = adicCompletionSpecMap B I ≫ e.inv from rfl,
    Scheme.IdealSheafData.comap_comp, comap_iso_inv_eq_adicIdealSheaf B I e h,
    comap_adicIdealSheaf_adicCompletionSpecMap]

variable [IsNoetherianRing B]

/-- The completion chart is flat. -/
public theorem flat_adicCompletionChart : Flat (adicCompletionChart B I e) := by
  have := flat_adicCompletionSpecMap B I
  infer_instance

/-- The closed fibre of the completion chart over `V(𝒥)` is `V(𝒥)`. -/
public theorem isIso_pullback_snd_adicCompletionChart {𝒥 : Y.IdealSheafData}
    (h : (adicIdealSheaf B I).comap e.hom = 𝒥) :
    IsIso (pullback.snd (adicCompletionChart B I e) 𝒥.subschemeι) := by
  subst h
  have := isIso_pullback_snd_adicCompletionSpecMap B I
  have hsnd : IsIso (pullback.snd (adicCompletionSpecMap B I)
      (adicIdealSheaf B I).subschemeι) := by
    rw [adicIdealSheaf_eq_ker]
    exact Stacks.Algebraization.isIso_pullback_snd_ker_subschemeι _ _ _
  set c : ((adicIdealSheaf B I).comap e.hom).subscheme ≅ (adicIdealSheaf B I).subscheme :=
    (adicIdealSheaf B I).comapIso e.hom ≪≫
      asIso (pullback.snd e.hom (adicIdealSheaf B I).subschemeι) with hcdef
  have hc : c.hom ≫ (adicIdealSheaf B I).subschemeι =
      ((adicIdealSheaf B I).comap e.hom).subschemeι ≫ e.hom := by
    rw [hcdef]
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hsq : (adicIdealSheaf B I).subschemeι ≫ e.inv =
      c.inv ≫ ((adicIdealSheaf B I).comap e.hom).subschemeι := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, e.hom_inv_id, Category.comp_id]
  have t : IsPullback (adicIdealSheaf B I).subschemeι c.inv e.inv
      ((adicIdealSheaf B I).comap e.hom).subschemeι :=
    IsPullback.of_vert_isIso ⟨hsq⟩
  have st := (IsPullback.of_hasPullback (adicCompletionSpecMap B I)
    (adicIdealSheaf B I).subschemeι).paste_vert t
  have : IsIso (st.isoPullback.hom ≫ pullback.snd (adicCompletionSpecMap B I ≫ e.inv)
      ((adicIdealSheaf B I).comap e.hom).subschemeι) := by
    rw [st.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left st.isoPullback.hom _

end Chart

section Descent

open Stacks.Coherent

variable {Y : Scheme.{u}} [IsNoetherian Y] (B : Type u) [CommRing B] [IsNoetherianRing B]
  (I : Ideal B) (e : Y ≅ Spec (.of B)) {𝒥 : Y.IdealSheafData}
  (h : (adicIdealSheaf B I).comap e.hom = 𝒥)

include h

/-- **Flat base change along the completion chart, on coherent adic systems** — Stacks 0EHQ. -/
public theorem coherentAdicPullback_adicCompletionChart_isEquivalence :
    (coherentAdicPullback (adicCompletionChart B I e) 𝒥).IsEquivalence := by
  have := flat_adicCompletionChart B I e
  have := isIso_pullback_snd_adicCompletionChart B I e h
  exact coherentAdicPullback_isEquivalence _ _

/-- **The descent of a morphism of systems along the completion chart.** -/
public theorem existsUnique_systemHom_of_adicCompletionChart
    (G H : CoherentAdicSystems 𝒥)
    (b : (coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G ⟶
      (coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj H) :
    ∃! a : G.obj ⟶ H.obj, ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback (adicCompletionChart B I e)).map (a.app n) = b.hom.app n := by
  have := coherentAdicPullback_adicCompletionChart_isEquivalence B I e h
  obtain ⟨a₀, ha₀⟩ :=
    (coherentAdicPullback (adicCompletionChart B I e) 𝒥).map_surjective b
  subst ha₀
  refine ⟨a₀.hom, fun _ => rfl, fun y hy => ?_⟩
  have h1 : (coherentAdicPullback (adicCompletionChart B I e) 𝒥).map
        (ObjectProperty.homMk y) =
      (coherentAdicPullback (adicCompletionChart B I e) 𝒥).map a₀ :=
    ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => hy n))
  exact congrArg (fun z : G ⟶ H => z.hom)
    ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).map_injective h1)

/-- **Pullback along the completion chart is an equivalence on the power-torsion coherent
modules** — More on Algebra 05EC in sheaf form. -/
public theorem coherentIdealPowerTorsionPullback_adicCompletionChart_isEquivalence :
    (coherentIdealPowerTorsionPullback (adicCompletionChart B I e) 𝒥).IsEquivalence := by
  have := flat_adicCompletionChart B I e
  have := isIso_pullback_snd_adicCompletionChart B I e h
  let R := coherentIdealPowerTorsionPushforward (adicCompletionChart B I e) 𝒥
  have : R.IsEquivalence := coherentIdealPowerTorsionPushforward_isEquivalence _ _
  let adj : coherentIdealPowerTorsionPullback (adicCompletionChart B I e) 𝒥 ⊣ R :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (adicCompletionChart B I e)).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)
  exact Functor.isEquivalence_of_iso (R.asEquivalence.symm.toAdjunction.leftAdjointUniq adj)

/-- **A morphism of power-torsion coherent modules is determined by its pullback along the
completion chart.** -/
public theorem pullback_map_injective_of_coherentIdealPowerTorsion_adicCompletionChart
    {M N : Y.Modules} (hM : coherentIdealPowerTorsion 𝒥 M)
    (hN : coherentIdealPowerTorsion 𝒥 N) {u v : M ⟶ N}
    (huv : (Scheme.Modules.pullback (adicCompletionChart B I e)).map u =
      (Scheme.Modules.pullback (adicCompletionChart B I e)).map v) : u = v := by
  let L := coherentIdealPowerTorsionPullback (adicCompletionChart B I e) 𝒥
  have : L.IsEquivalence :=
    coherentIdealPowerTorsionPullback_adicCompletionChart_isEquivalence B I e h
  let M' : (coherentIdealPowerTorsion 𝒥).FullSubcategory := ⟨M, hM⟩
  let N' : (coherentIdealPowerTorsion 𝒥).FullSubcategory := ⟨N, hN⟩
  have key : L.map (ObjectProperty.homMk (X := M') (Y := N') u) =
      L.map (ObjectProperty.homMk (X := M') (Y := N') v) :=
    ObjectProperty.hom_ext _ huv
  exact congrArg (fun k : M' ⟶ N' => k.hom) (L.map_injective key)

variable {X' : Scheme.{u}} [IsNoetherian X'] (p : X' ⟶ Y) [IsProper p]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (G : CoherentAdicSystems 𝒥)
  (β : (coherentAdicPullback p 𝒥).obj G ≅ (completionFunctor X' (𝒥.comap p)).obj 𝓕)

/-- **The characterizing equation of Stacks 088B is detected after pullback along the completion
chart.** -/
public theorem isDirectImageCharacterized_of_pullback_adicCompletionChart
    (α : G.obj ⟶ ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕)).obj)
    (hα : ∀ n : ℕ, (Scheme.Modules.pullback (adicCompletionChart B I e)).map
          (α.app (op n) ≫
            eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
              directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
        (Scheme.Modules.pullback (adicCompletionChart B I e)).map
          ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj p 𝒥 𝓕 n))) :
    IsDirectImageCharacterized p 𝒥 G 𝓕 β α := fun n =>
  pullback_map_injective_of_coherentIdealPowerTorsion_adicCompletionChart B I e h
    ⟨n, G.property.1 n, G.property.2.1 n⟩
    (coherentIdealPowerTorsion_pushforward_idealPowerQuotient p 𝒥 n 𝓕) (hα n)

/-- **The descent of the second paragraph of the proof of Stacks 088B across the completion
chart.** -/
public theorem exists_isDirectImageCharacterized_of_adicCompletionChartPullback
    (ψ : ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G).obj ⟶
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj
        ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕))).obj)
    (hψ : ∀ n : ℕ, ψ.app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            (eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
              directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
        (Scheme.Modules.pullback (adicCompletionChart B I e)).map
          ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj p 𝒥 𝓕 n))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕)).obj,
      IsDirectImageCharacterized p 𝒥 G 𝓕 β α ∧
        ∀ n : ℕᵒᵖ,
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map (α.app n) = ψ.app n := by
  obtain ⟨α, hα, -⟩ := existsUnique_systemHom_of_adicCompletionChart B I e h G
    ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕)) (ObjectProperty.homMk ψ)
  refine ⟨α, isDirectImageCharacterized_of_pullback_adicCompletionChart B I e h p 𝓕 G β α
    fun n => ?_, hα⟩
  rw [Functor.map_comp, hα (op n)]
  exact hψ n

end Descent

/-! ### The completion chart of an affine open of the base -/

section AffineOpen

open Stacks.Coherent

/-- **The completion chart of an affine open `V` of a scheme `X`**, for a quasi-coherent sheaf of
ideals `𝒥` on `X`: the morphism

`Spec (Γ(X, V) ^∧) ⟶ V`

obtained from `Spec` of the completion map of `B = Γ(X, V)` along `𝒥(V)` followed by the inverse
of `AlgebraicGeometry.IsAffineOpen.isoSpec`. This is the chart along which the second paragraph of
the proof of [Stacks, Tag 088B] replaces `B` by `B ^∧` — read, unlike the source, as a flat
morphism *onto `V` itself* rather than onto `Spec B`, so that no datum of the situation over `V`
has to be transported across `AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
public abbrev affineOpenAdicCompletionChart {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) :
    Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))) ⟶ V.1.toScheme :=
  adicCompletionChart ↥Γ(X, V.1) (J.ideal V) V.2.isoSpec

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
  (V : X.affineOpens) [IsNoetherianRing ↥Γ(X, V.1)]

/-- **The local solution of Stacks 088B for `π ∣_ V` over an affine open `V` of the base, from a
solution of the pulled-back problem over `Spec (Γ(X, V) ^∧)`.**

Let `π : X' ⟶ X` be proper between Noetherian schemes, `𝒥 ⊆ 𝒪_X` a quasi-coherent sheaf of
ideals, `(𝒢_n)` an object of `Coh(X, 𝒥)`, `𝓕` a coherent `𝒪_{X'}`-module and
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Over an affine open `V` of `X` with `B = Γ(X, V)`, a morphism `ψ` of the
systems pulled back along `Stacks.Algebraization.affineOpenAdicCompletionChart` which satisfies
the characterization of Stacks 088B for `π ∣_ V` *pulled back along that chart* descends to a
morphism over `V` which satisfies that characterization — and whose own pullback is `ψ`, so that
the descent is pinned down.

This is `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionChartPullback`
at `Y = V`, the chart of the affine open, and the restricted data of
`Stacks.Coherent.restrictDirectImageIso`: exactly the situation the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict` asks about.
**Unconditional.** -/
public theorem exists_isDirectImageCharacterized_morphismRestrict_of_adicCompletionChart
    (ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj)
    (hψ : ∀ n : ℕ, ψ.app (op n) ≫
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
              directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
        (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
          ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
              ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
              (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
              (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
            eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
              (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) :
    ∃ α : ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G).obj ⟶
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))).obj,
      IsDirectImageCharacterized (π ∣_ V.1) (J.comap V.1.ι)
          ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
          (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
          (restrictDirectImageIso π V.1 J G 𝓕 β) α ∧
        ∀ n : ℕᵒᵖ,
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map (α.app n) =
            ψ.app n :=
  exists_isDirectImageCharacterized_of_adicCompletionChartPullback ↥Γ(X, V.1) (J.ideal V)
    V.2.isoSpec (comap_adicIdealSheaf_isoSpec J V.2) (π ∣_ V.1)
    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
    (restrictDirectImageIso π V.1 J G 𝓕 β) ψ hψ

end AffineOpen

/-! ### `HasAffineLocalDirectImageSolution` over the completion of each affine chart -/

section Assembly

open Stacks.Coherent

/-- **`Stacks.Algebraization.HasAffineLocalDirectImageSolution` — the single remaining binder
behind [Stacks, Tag 088C], `hDev` and the first input of [Stacks, Tag 088E] — reduced to the
pulled-back problem over `Spec (Γ(X, V) ^∧)` for each affine open `V` of the base.**

The hypothesis asks, over each affine open `V` of `X` with `B = Γ(X, V)`, for a morphism `ψ` of
the systems pulled back along `Stacks.Algebraization.affineOpenAdicCompletionChart` —
`Spec (B ^∧) ⟶ V` — such that

* `ψ` satisfies the characterization of Stacks 088B for `π ∣_ V` and
  `Stacks.Coherent.restrictDirectImageIso` *pulled back along that chart*, and
* the morphism over `V` that `ψ` descends from (the second clause pins it down, the descent being
  unique) has its levelwise kernels and cokernels annihilated by a power of `𝒦|_V`.

Everything else is proved: the descent of the morphism and of the equation across the chart is
`Stacks.Algebraization.exists_isDirectImageCharacterized_morphismRestrict_of_adicCompletionChart`,
and the translation of a solution for `π ∣_ V` into a solution of the *restricted* problem over
`V` is `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict`.

So the whole of Stacks 088B at a general base is reduced to the second paragraph of the source
read over a single affine chart, with no transport of `π ∣_ V`, of `𝓕|_{π ⁻¹ V}`, of `(𝒢_n)|_V` or
of `β'` across `AlgebraicGeometry.IsAffineOpen.isoSpec` anywhere: the chart is a flat morphism
onto `V` itself, so the `δ` and the `γ` of the equation are those of `π ∣_ V` and are never
compared with the `δ` and `γ` of a situation over `Spec B`.

What the hypothesis still carries is the residue of the source's second paragraph that is
identified as out of reach in `CompletionProper/AdicBaseChangeSquares.lean`: the solution over
`Spec (B ^∧)`, where the base *is* complete, is
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase`,
but identifying its `δ` and `γ` — those of a proper morphism *over* `Spec (B ^∧)` — with the
pullbacks along the chart of the `δ` and `γ` of `π ∣_ V` is the pair of base-change squares `hδ`
and `hγ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison`. The
annihilation clause is the sheafification of
`Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion`, which
`CompletionProper/AffineLocalSolution.lean` records as piece 3.

No `stacks` attribute is attached: this is a reduction of a hypothesis, not a statement of the
source. -/
public theorem hasAffineLocalDirectImageSolution_of_adicCompletionChart
    (h : ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
      (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
      (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
      (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
      IsIso (π ∣_ K.support.compl) → ∀ V : X.affineOpens,
        letI : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
        ∃ ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
              (J.comap V.1.ι)).obj ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
            ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
              ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj,
          (∀ n : ℕ, ψ.app (op n) ≫
                (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                  (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                      (properPushforwardCoherent (π ∣_ V.1)
                        (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
                    directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                      (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
              (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                    (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
                  eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) ∧
            ∀ α : ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G).obj ⟶
              ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))).obj,
              (∀ n : ℕᵒᵖ,
                  (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                    (α.app n) = ψ.app n) →
                IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) α) :
    HasAffineLocalDirectImageSolution.{u} := by
  refine hasAffineLocalDirectImageSolution_of_morphismRestrict ?_
  intro X' X _ _ π _ J K G 𝓕 β hiso V
  let : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨ψ, hψ, hann⟩ := h π J K G 𝓕 β hiso V
  obtain ⟨α, hchar, hpb⟩ :=
    exists_isDirectImageCharacterized_morphismRestrict_of_adicCompletionChart π J G 𝓕 β V ψ hψ
  exact ⟨α, hchar, hann α hpb⟩

end Assembly

/-! ### Stacks 088B over the base of the completion chart -/

section ChartBase

open Stacks.Coherent

variable {Y : Scheme.{u}} (B : Type u) [CommRing B] [IsNoetherianRing B] (I : Ideal B)
  (e : Y ≅ Spec (.of B)) {𝒥 : Y.IdealSheafData}
  (h : (adicIdealSheaf B I).comap e.hom = 𝒥)

include h

/-- **Stacks 088B with `α` characterized, over the base of the completion chart.** Let `Y` be a
scheme with an isomorphism `e : Y ≅ Spec B` for `B` Noetherian, let `I ⊆ B` be an ideal and let
`𝒥 ⊆ 𝒪_Y` be the ideal sheaf corresponding to `I`. For every proper morphism
`π' : X'' ⟶ Spec (B ^∧)`, every quasi-coherent sheaf of ideals `𝒦` on `Spec (B ^∧)`, every
coherent `𝒪_{X''}`-module `𝓕'`, every object `G'` of `Coh(Spec (B ^∧), 𝒥 𝒪)` — the inverse image
of `𝒥` along `Stacks.Algebraization.adicCompletionChart` — and every isomorphism
`β' : (π')^*G' ≅ 𝓕' ^∧`, the hypothesis `hc` of the source yields a morphism

`α : G' ⟶ ((π')_*𝓕') ^∧`

characterized in the source's sense **and** with its levelwise kernels and cokernels annihilated
by a power of `𝒦`.

**No completeness hypothesis on `B`.** This is the half of the second paragraph of the proof of
Stacks 088B that the chart does discharge: the base ring of the chart's source is `B ^∧`, which is
`I B ^∧`-adically complete by `AdicCompletion.isAdicComplete_self`, so the complete affine case
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine` applies at
`A = B ^∧`, `I B ^∧` and the identity of `Spec (B ^∧)`. The ideal sheaf matches by
`Stacks.Algebraization.comap_adicCompletionChart` followed by
`Stacks.Algebraization.adicIdealSheaf_eq_baseIdealSheaf`, and — unlike
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionBase` —
the ideal sheaf over the chart's source is presented as the inverse image of `𝒥` along the chart
itself, so no datum of the situation over `Y` has to be transported across `e`.

**What this does not give.** `π'` is a binder: the statement is about a proper morphism *over*
`Spec (B ^∧)`, and `Stacks.Algebraization.affineOpenAdicCompletionChart` points from
`Spec (B ^∧)` to `Y`, not the other way, so a proper morphism `π : X' ⟶ Y` is **not** a morphism
over `Spec (B ^∧)` and does not instantiate `π'`. The only `π'` attached to `π` is the base change
`X' ×_Y Spec (B ^∧) ⟶ Spec (B ^∧)`, whose `δ` and `γ` have then to be identified with the
pullbacks along the chart of those of `π` — the two squares `hδ` and `hγ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison`. See the module
docstring.

No `stacks` attribute is attached: the affine-base form of Stacks 088B is already registered on
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`,
and this is that statement at a particular base. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion I B))) [IsProper π']
    (𝒦 : (Spec (.of (AdicCompletion I B))).IdealSheafData)
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (G' : CoherentAdicSystems (𝒥.comap (adicCompletionChart B I e)))
    (β' : (coherentAdicPullback π' (𝒥.comap (adicCompletionChart B I e))).obj G' ≅
      (completionFunctor X'' ((𝒥.comap (adicCompletionChart B I e)).comap π')).obj 𝓕')
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion I B))).ringCatSheaf,
      (G' ≅ (completionFunctor (Spec (.of (AdicCompletion I B)))
          (𝒥.comap (adicCompletionChart B I e))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj))) :
    ∃ α : G'.obj ⟶ ((completionFunctor (Spec (.of (AdicCompletion I B)))
        (𝒥.comap (adicCompletionChart B I e))).obj (properPushforwardCoherent π' 𝓕')).obj,
      IsDirectImageCharacterized π' (𝒥.comap (adicCompletionChart B I e)) G' 𝓕' β' α ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  have := isAdicComplete_map_algebraMap_adicCompletion B I
  exact exists_isDirectImageCharacterized_isKernelCokernel_of_eq_baseIdealSheaf
    (AdicCompletion I B) (I.map (algebraMap B (AdicCompletion I B)))
    (𝟙 (Spec (.of (AdicCompletion I B)))) π' _
    ((comap_adicCompletionChart B I e h).trans
      (adicIdealSheaf_eq_baseIdealSheaf (AdicCompletion I B)
        (I.map (algebraMap B (AdicCompletion I B)))))
    𝒦 𝓕' G' β' hc

end ChartBase

/-! ### The pulled-back characterization, from the chart's base change squares -/

section ChartSquares

open Stacks.Coherent

variable {Y : Scheme.{u}} [IsNoetherian Y] (B : Type u) [CommRing B] [IsNoetherianRing B]
  (I : Ideal B) (e : Y ≅ Spec (.of B)) {𝒥 : Y.IdealSheafData}
  (h : (adicIdealSheaf B I).comap e.hom = 𝒥)
  {X' : Scheme.{u}} [IsNoetherian X'] (p : X' ⟶ Y) [IsProper p]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (G : CoherentAdicSystems 𝒥)
  (β : (coherentAdicPullback p 𝒥).obj G ≅ (completionFunctor X' (𝒥.comap p)).obj 𝓕)

include h

/-- **The morphism `ψ` over the chart's base, and the pulled-back characterizing equation, from
the two base-change squares at the chart.** Let `Y ≅ Spec B` with `B` Noetherian, let `𝒥 ⊆ 𝒪_Y`
correspond to `I ⊆ B`, let `p : X' ⟶ Y` be proper, `𝓕` a coherent `𝒪_{X'}`-module, `(𝒢_n)` an
object of `Coh(Y, 𝒥)` and `β : p^*(𝒢_n) ≅ 𝓕 ^∧`. Write `c` for
`Stacks.Algebraization.adicCompletionChart`, the flat morphism `Spec (B ^∧) ⟶ Y`. Let
`π' : X'' ⟶ Spec (B ^∧)` be proper, `𝓕'` a coherent `𝒪_{X''}`-module and `β'` the corresponding
isomorphism over `Spec (B ^∧)` — in the intended application the base change of `p`, of `𝓕` and
of `β` along `c`. Given

* `ι`, a comparison `(π'_*𝓕') ^∧ ⟶ c^*((p_*𝓕) ^∧)` of the two completed direct images,
* `θ_n`, a comparison `π'_*(𝓕'/ℐ' ⁿ⁺¹𝓕') ⟶ c^*(p_*(𝓕/ℐ ⁿ⁺¹𝓕))` of the two direct images of the
  levels, and
* the two squares `hδ` and `hγ` saying that these comparisons carry the `δ` and the `γ` of the
  situation over `Spec (B ^∧)` to the pullbacks along `c` of the `δ` and the `γ` of the situation
  over `Y`,

there is a morphism `ψ` of the systems pulled back along `c` which satisfies the characterization
of Stacks 088B for `p` and `β` *pulled back along `c`* — that is, exactly the datum the first
clause of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart` asks for, and the
binder `ψ`, `hψ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionChartPullback`.

The solution over `Spec (B ^∧)` is
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase`
and `ψ := α' ≫ ι`.

**This is `Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` read
at the chart rather than at `Spec B`,** and it records exactly what the chart does
and does not buy. The chart removes every transport across `AlgebraicGeometry.IsAffineOpen.isoSpec`
— the `δ` and the `γ` on the right-hand sides of `hδ` and `hγ` are those of `p` itself, pulled
back along a flat morphism onto `Y` — but it does **not** remove the base change. The complete
affine case of Stacks 088B is a statement about a proper morphism *over* the complete base, and
`c` points from `Spec (B ^∧)` to `Y`, so `p` is not such a morphism; the only proper morphism over
`Spec (B ^∧)` attached to `p` is the base change `X' ×_Y Spec (B ^∧) ⟶ Spec (B ^∧)`, and `ι`,
`θ`, `hδ` and `hγ` are its comparison with `p`. So the residue identified in
`CompletionProper/AdicBaseChangeSquares.lean` survives the change of chart unchanged: `hδ` is
provable there and `hγ` is the single live obstruction.

No `stacks` attribute is attached: this is the assembly of a hypothesis out of two squares, not a
statement of the source. -/
public theorem exists_pullbackCharacterization_of_adicCompletionChartSquares
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion I B))) [IsProper π']
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (β' : (coherentAdicPullback π' (𝒥.comap (adicCompletionChart B I e))).obj
        ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) ≅
      (completionFunctor X'' ((𝒥.comap (adicCompletionChart B I e)).comap π')).obj 𝓕')
    (𝒦 : (Spec (.of (AdicCompletion I B))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion I B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion I B)))
            (𝒥.comap (adicCompletionChart B I e))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj)))
    (ι : ((completionFunctor (Spec (.of (AdicCompletion I B)))
          (𝒥.comap (adicCompletionChart B I e))).obj
        (properPushforwardCoherent π' 𝓕')).obj ⟶
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj
        ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕))).obj)
    (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
          (idealPowerQuotient ((𝒥.comap (adicCompletionChart B I e)).comap π') (n + 1) 𝓕'.obj) ⟶
      (Scheme.Modules.pullback (adicCompletionChart B I e)).obj
        ((Scheme.Modules.pushforward p).obj (idealPowerQuotient (𝒥.comap p) (n + 1) 𝓕.obj)))
    (hδ : ∀ n : ℕ, ι.app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            (eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
              directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
        (eqToHom (completionFunctor_obj (Spec (.of (AdicCompletion I B)))
              (𝒥.comap (adicCompletionChart B I e))
              (properPushforwardCoherent π' 𝓕') n) ≫
            directImageQuotientComparison π' (𝒥.comap (adicCompletionChart B I e))
              (n + 1) 𝓕'.obj) ≫ θ n)
    (hγ : ∀ n : ℕ,
        (directImageComparison π' (𝒥.comap (adicCompletionChart B I e))
              ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) 𝓕' β').app (op n) ≫
            eqToHom (pushforward_completion_obj π' (𝒥.comap (adicCompletionChart B I e))
              𝓕' n) ≫ θ n =
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj p 𝒥 𝓕 n))) :
    ∃ ψ : ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G).obj ⟶
        ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj
          ((completionFunctor Y 𝒥).obj (properPushforwardCoherent p 𝓕))).obj,
      ∀ n : ℕ, ψ.app (op n) ≫
            (Scheme.Modules.pullback (adicCompletionChart B I e)).map
              (eqToHom (completionFunctor_obj Y 𝒥 (properPushforwardCoherent p 𝓕) n) ≫
                directImageQuotientComparison p 𝒥 (n + 1) 𝓕.obj) =
          (Scheme.Modules.pullback (adicCompletionChart B I e)).map
            ((directImageComparison p 𝒥 G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj p 𝒥 𝓕 n)) := by
  obtain ⟨α', hα', -⟩ :=
    exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase B I e h π' 𝒦 𝓕'
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G) β' hc
  refine ⟨α' ≫ ι, fun n => ?_⟩
  rw [NatTrans.comp_app]
  exact (Category.assoc (obj := (Spec (.of (AdicCompletion I B))).Modules) _ _ _).trans
    ((congrArg (fun z => α'.app (op n) ≫ z) (hδ n)).trans
      ((Category.assoc (obj := (Spec (.of (AdicCompletion I B))).Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ θ n) (hα' n)).trans
          ((Category.assoc (obj := (Spec (.of (AdicCompletion I B))).Modules) _ _ _).trans
            (hγ n)))))

end ChartSquares

/-! ### The first clause of the hypothesis, at the completion chart of an affine open -/

section AffineOpenSquares

open Stacks.Coherent

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)
  (V : X.affineOpens) [IsNoetherianRing ↥Γ(X, V.1)]

/-- **The first clause of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`, from the two
base-change squares at the completion chart of the affine open `V`.**

`Stacks.Algebraization.exists_pullbackCharacterization_of_adicCompletionChartSquares` at
`Y = V`, `B = Γ(X, V)`, `I = 𝒥(V)`, the chart
`Stacks.Algebraization.affineOpenAdicCompletionChart`, the restricted morphism `π ∣_ V` and the
restricted data of `Stacks.Coherent.restrictDirectImageIso`. The ideal sheaf matches by
`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec`.

So the hypothesis `h` of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart` — and with it
[Stacks, Tag 088C], `hDev` and the first input of [Stacks, Tag 088E] — is reduced to, over each
affine open `V` of the base: the base change of `π ∣_ V` along the chart with its comparisons `ι`
and `θ`, the source's own condition `hc` over the chart's base, the two squares `hδ` and `hγ`,
and the annihilation of the levelwise kernels and cokernels of the descended `α`. **`hγ` is the
one of these that `CompletionProper/AdicBaseChangeSquares.lean` measures as out of reach**, and
the chart does not remove it: see the docstring of
`Stacks.Algebraization.exists_pullbackCharacterization_of_adicCompletionChartSquares`.

No `stacks` attribute is attached: this is the assembly of a hypothesis, not a statement of the
source. -/
public theorem exists_pullbackCharacterization_morphismRestrict_of_adicCompletionChartSquares
    {X'' : Scheme.{u}} [IsNoetherian X'']
    (π' : X'' ⟶ Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))) [IsProper π']
    (𝓕' : AlgebraicGeometry.SheafOfModules.CoherentModules X''.ringCatSheaf)
    (β' : (coherentAdicPullback π'
          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
        ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
          ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) ≅
      (completionFunctor X''
        (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')).obj 𝓕')
    (𝒦 : (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1)))).ringCatSheaf,
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
            ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G) ≅
          (completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
            ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π').unit.app 𝒜.obj)))
    (ι : ((completionFunctor (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
          ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))).obj
        (properPushforwardCoherent π' 𝓕')).obj ⟶
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj)
    (θ : ∀ n : ℕ, (Scheme.Modules.pushforward π').obj
          (idealPowerQuotient
            (((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)).comap π')
            (n + 1) 𝓕'.obj) ⟶
      (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).obj
        ((Scheme.Modules.pushforward (π ∣_ V.1)).obj
          (idealPowerQuotient ((J.comap V.1.ι).comap (π ∣_ V.1)) (n + 1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj)))
    (hδ : ∀ n : ℕ, ι.app (op n) ≫
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
              directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
        (eqToHom (completionFunctor_obj
              (Spec (.of (AdicCompletion (J.ideal V) ↥Γ(X, V.1))))
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
              (properPushforwardCoherent π' 𝓕') n) ≫
            directImageQuotientComparison π'
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) (n + 1) 𝓕'.obj) ≫ θ n)
    (hγ : ∀ n : ℕ,
        (directImageComparison π' ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V))
              ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)) 𝓕' β').app (op n) ≫
            eqToHom (pushforward_completion_obj π'
              ((J.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) 𝓕' n) ≫ θ n =
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
              eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) :
    ∃ ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
          (J.comap V.1.ι)).obj ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
        ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
          ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
            (properPushforwardCoherent (π ∣_ V.1)
              (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj,
      ∀ n : ℕ, ψ.app (op n) ≫
            (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
              (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                  (properPushforwardCoherent (π ∣_ V.1)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
                directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
          (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
            ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
              eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n)) :=
  exists_pullbackCharacterization_of_adicCompletionChartSquares ↥Γ(X, V.1) (J.ideal V)
    V.2.isoSpec (comap_adicIdealSheaf_isoSpec J V.2) (π ∣_ V.1)
    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
    (restrictDirectImageIso π V.1 J G 𝓕 β) π' 𝓕' β' 𝒦 hc ι θ hδ hγ

end AffineOpenSquares

end Stacks.Algebraization

end
