module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.GenericFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.AmpleAcrossPoint
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ProjectiveContraction
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveProper
import all StacksFrontier.AlgebraicGeometry.NodalContraction.FiniteType

/-!
# Contracting an exceptional curve in a quasi-projective scheme

**[Stacks, Tag 0C2N] (2).** Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism of finite type
and `E ⊆ X` an exceptional curve of the first kind lying in a fibre of `f`. If `X` is
quasi-projective over `S`, there is a contraction `b : X ⟶ X'` of `E`, and `X'` is quasi-projective
over `S`.

## The proof, and a gap in the source's

The source writes `X` as an open subscheme of a scheme `X̄` projective over `S`, applies part (1)
to `X̄` and restricts. This presumes that `E` is closed in `X̄`, which holds exactly when the point
`s ∈ S` under `E` is closed: the closure of `E` in `X̄` is proper over `S`, so its image is closed.
When `s` is not closed in `S` the curve is not closed in any compactification, and part (1) does
not apply. This happens: for a discrete valuation ring `A` with fraction field `K`, the blowup of
`𝐏²_K` in a `K`-point is quasi-projective and of finite type over `Spec A`, and its exceptional
curve lies over the generic point.

The proof here therefore works locally around `s`, where the point is closed, and handles the
neighbourhoods of the specializations of `s` separately.

* The point `s` is closed in some open neighbourhood, by Chevalley's theorem: the image `{s}` of
  `E` is constructible.
* Over an affine open `U ∋ s` in which `s` is closed, `E` is closed in the preimage of `U` in a
  projective compactification `X̄` of `X` (it is proper over the closed point,
  `AlgebraicGeometry.isClosed_range_subschemeι_comp_of_iso_projectiveLineProj`), so
  [Stacks, Tag 0C2M] contracts it there, with an ample module of class `ℒ̄(nE)`, where `ℒ̄` is
  ample relative to `X̄ ⟶ S`. Restricting to the preimage of `U` in `X` gives a contraction of `E`
  in `f⁻¹(U)` with an ample module of class `ℒ(nE)`, `ℒ = ℒ̄|_X`.
* The glueing engine `AlgebraicGeometry.exists_contraction_of_ample_chart` produces the
  contraction `b : X ⟶ X'`, the structure morphism `g`, and an invertible `ℒ'` which is ample over
  every affine open inside `U` and off the contracted point `v` over every affine open.
* Over an affine open `V ∋ s` not inside `U`, `ℒ'` is ample over a basic open `V_h ∋ s` inside `U`
  and over `g⁻¹(V) \ {v}`, and `v` has depth two;
  `AlgebraicGeometry.isAmple_pullbackModule_of_basicOpen_of_compl` glues these.

## Main results

* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_isQuasiProjective`:
  **[Stacks, Tag 0C2N] (2)**.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 054J](https://stacks.math.columbia.edu/tag/054J)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open ExceptionalCurveContraction

/-! ### Helpers -/

/-- **Relative ampleness restricts along an open immersion from a Noetherian scheme.** If `ℒ` is
ample relative to `p : Y ⟶ S` and `j : X ⟶ Y` is an open immersion with `X` Noetherian, then
`j^* ℒ` is ample relative to `j ≫ p`. -/
theorem isRelativelyAmple_comp_of_isOpenImmersion {X Y S : Scheme.{u}} [IsNoetherian X]
    (j : X ⟶ Y) [IsOpenImmersion j] (p : Y ⟶ S) (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] (hL : Stacks.RelativeAmple.IsRelativelyAmple p L) :
    haveI := Scheme.Modules.isInvertibleModule_pullback_obj j L
    Stacks.RelativeAmple.IsRelativelyAmple (j ≫ p) ((Scheme.Modules.pullback j).obj L) := by
  have := Scheme.Modules.isInvertibleModule_pullback_obj j L
  refine ⟨inferInstance, fun V hV => ?_⟩
  let i : ((j ≫ p) ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := j ∣_ (p ⁻¹ᵁ V)
  have := Scheme.Modules.isInvertibleModule_pullback_obj (p ⁻¹ᵁ V).ι L
  have := Scheme.Modules.isInvertibleModule_pullback_obj i
    ((Scheme.Modules.pullback (p ⁻¹ᵁ V).ι).obj L)
  have := Scheme.Modules.isInvertibleModule_pullback_obj ((j ≫ p) ⁻¹ᵁ V).ι
    ((Scheme.Modules.pullback j).obj L)
  have hcpt : CompactSpace ((j ≫ p) ⁻¹ᵁ V).toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (((j ≫ p) ⁻¹ᵁ V : X.Opens) : Set X))
  have : IsImmersion i := inferInstanceAs (IsImmersion (j ∣_ (p ⁻¹ᵁ V)))
  have hN : Stacks.Ample.IsAmple ((j ≫ p) ⁻¹ᵁ V).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule i
        (Stacks.AmpleLocallyClosed.pullbackModule (p ⁻¹ᵁ V).ι L)) :=
    have := Stacks.InvertiblePullback.isInvertibleModule_pullback (p ⁻¹ᵁ V).ι L
    Stacks.SectionExtension.isAmple_pullbackModule i _ (hL.2 V hV)
      (Or.inr (Or.inl ⟨hcpt, inferInstance⟩))
  have hN' : Scheme.Modules.IsAmple ((j ≫ p) ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback (p ⁻¹ᵁ V).ι).obj L)) := by
    have := Stacks.InvertiblePullback.isInvertibleModule_pullback (p ⁻¹ᵁ V).ι L
    have h2 : Scheme.Modules.IsAmple ((j ≫ p) ⁻¹ᵁ V).toScheme
        ((Scheme.Modules.pullback i).obj
          (Stacks.AmpleLocallyClosed.pullbackModule (p ⁻¹ᵁ V).ι L)) :=
      isAmple_pullback_of_isAmple_pullbackModule i _ hN
    have := Scheme.Modules.isInvertibleModule_pullback_obj i
      (Stacks.AmpleLocallyClosed.pullbackModule (p ⁻¹ᵁ V).ι L)
    exact Scheme.Modules.isAmple_of_iso ((Scheme.Modules.pullback i).mapIso
      ((Stacks.ProjectiveBundleQuotients.pullbackIso (p ⁻¹ᵁ V).ι).app L).symm) h2
  refine isAmple_pullbackModule_of_isAmple_pullback _ _ ?_
  refine Scheme.Modules.isAmple_of_iso ?_ hN'
  exact (Scheme.Modules.pullbackComp i (p ⁻¹ᵁ V).ι).app L ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι j (p ⁻¹ᵁ V))).app L ≪≫
    ((Scheme.Modules.pullbackComp ((j ≫ p) ⁻¹ᵁ V).ι j).app L).symm

/-- **A contraction composed with an isomorphism of the source is a contraction** of the inverse
image of the ideal sheaf. -/
theorem IsContractionOfExceptionalCurve.iso_comp {X₁ X X' : Scheme.{u}} {D : X.IdealSheafData}
    {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) (φ : X₁ ≅ X) :
    IsContractionOfExceptionalCurve (D.comap φ.hom) (φ.hom ≫ b) := by
  obtain ⟨hN, z, hz, hreg, hdim, hD, ε, hε⟩ := hb
  refine ⟨hN, z, hz, hreg, hdim, ?_, φ ≪≫ ε, ?_⟩
  · rw [hD, ← Scheme.IdealSheafData.comap_comp]
  · rw [Iso.trans_hom, Category.assoc, hε]

/-- The local ring of a scheme at a regular point of dimension two has depth two. -/
theorem two_le_depth_of_isRegularLocalRing {Y : Scheme.{u}} (y : Y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) :
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) := by
  have hCM :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (Y.presheaf.stalk y)).2
  change ((Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
    (Y.presheaf.stalk y) : ℕ∞) : WithBot ℕ∞) = ringKrullDim (Y.presheaf.stalk y) at hCM
  refine WithBot.coe_le_coe.mp ?_
  rw [hCM, hdim]
  norm_num

/-- **The point under an exceptional curve is closed in a neighbourhood.** For `f : X ⟶ S` of
finite type over a Noetherian scheme and a nonempty closed `E ⊆ X` mapped to the single point `s`,
there is an open `U ∋ s` meeting the closure of `s` only in `s`: the image `{s}` of `E` is
constructible by Chevalley's theorem ([Stacks, Tag 054J]). -/
theorem exists_isOpen_inter_closure_singleton_subset {X S : Scheme.{u}} [IsNoetherian S]
    [IsNoetherian X] (f : X ⟶ S) [LocallyOfFiniteType f] (E : Set X) (hE : IsClosed E)
    (s : S) (hEs : f.base '' E = {s}) :
    ∃ U : S.Opens, s ∈ U ∧ (U : Set S) ∩ closure {s} ⊆ {s} := by
  have hcE : Topology.IsConstructible E := by
    have hco : IsRetrocompact Eᶜ :=
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hE.isOpen_compl).mpr
        (NoetherianSpace.isCompact _)
    have h : Topology.IsConstructible Eᶜ :=
      BooleanSubalgebra.subset_closure ⟨hE.isOpen_compl, hco⟩
    simpa using h
  have hc := f.isConstructible_image hcE
  rw [hEs] at hc
  obtain ⟨U, hU, hsU, hUs⟩ := hc.exists_isOpen_inter_closure_singleton_subset (Set.mem_singleton s)
  exact ⟨⟨U, hU⟩, hsU, hUs⟩

/-- A point of the closed subscheme of an ideal sheaf lies in its support. -/
private theorem subschemeι_mem_support {X : Scheme.{u}} (D : X.IdealSheafData) (z : D.subscheme) :
    D.subschemeι.base z ∈ (D.support : Set X) := by
  rw [← D.range_subschemeι]
  exact ⟨z, rfl⟩

/-- The fibre of a contraction `b` over its centre `z` is the support of the contracted ideal. -/
private theorem base_eq_iff_mem_support_of_eq_comap {X Z : Scheme.{u}} {D : X.IdealSheafData}
    {b : X ⟶ Z} {z : Z} {hz : IsClosed ({z} : Set Z)}
    (hD : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)).comap b) (x : X) :
    b.base x = z ↔ x ∈ (D.support : Set X) := by
  rw [hD, Scheme.IdealSheafData.support_comap]
  simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- **The exceptional curve of an open subscheme, closed in the ambient scheme, is an exceptional
curve of the ambient scheme.** If `j : X ⟶ Y` is an open immersion and `D` an exceptional curve of
the first kind on `X` whose image in `Y` is closed, then the ideal sheaf `D̄` of that image is an
exceptional curve of the first kind on `Y`, with `j⁻¹ D̄ = D` and support inside the image of
`j`. -/
theorem exists_isExceptionalCurveOfFirstKind_of_isClosed_range {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hcl : IsClosed (Set.range (D.subschemeι ≫ j).base)) :
    ∃ (D' : Y.IdealSheafData) (e' : projectiveLineProj k ≅ D'.subscheme),
      D'.IsExceptionalCurveOfFirstKind k e' ∧ D'.comap j = D ∧
        (D'.support : Set Y) ⊆ Set.range j.base := by
  have : IsClosedImmersion (D.subschemeι ≫ j) := IsClosedImmersion.of_isPreimmersion _ hcl
  set D' := (D.subschemeι ≫ j).ker with hD'
  have hcomap : D'.comap j = D := by
    rw [hD', ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    let ψ : D.subscheme ⟶ pullback j (D.subschemeι ≫ j) := pullback.lift D.subschemeι (𝟙 _)
      (by rw [Category.id_comp])
    have : IsIso ψ := by
      refine ⟨pullback.snd _ _, ?_, ?_⟩
      · simp [ψ]
      · refine pullback.hom_ext ?_ ?_
        · rw [← cancel_mono j, Category.assoc, Category.assoc, Category.id_comp]
          simp only [ψ, pullback.lift_fst_assoc]
          rw [pullback.condition]
        · simp [ψ]
    rw [← Scheme.Hom.ker_comp_of_isIso ψ, pullback.lift_fst, D.ker_subschemeι]
  have hsupp : (D'.support : Set Y) ⊆ Set.range j.base := by
    rw [hD', Scheme.Hom.support_ker, hcl.closure_eq]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : projectiveLineProj k ≅ (D'.comap j).subscheme,
      (D'.comap j).IsExceptionalCurveOfFirstKind k e' := by
    rw [hcomap]
    exact ⟨e, hE⟩
  exact ⟨D', e' ≪≫ D'.comapSubschemeIso j hsupp,
    Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.of_comap j D' hsupp he', hcomap, hsupp⟩

/-! ### Tag 0C2N (2) -/

/-- **[Stacks, Tag 0C2N] (2).** Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism of
finite type. Let `E ⊆ X` be an exceptional curve of the first kind, cut out by `D` and presented
as `𝐏¹_k` by `e`, which lies in the fibre of `f` over a point `s`. If `X` is quasi-projective over
`S`, then there exists a contraction `b : X ⟶ X'` of `E`, and `X'` is quasi-projective over `S`:
the structure morphism factors as `b ≫ g` with `g` quasi-projective. -/
@[stacks 0C2N "(2)"]
theorem exists_isContractionOfExceptionalCurve_isQuasiProjective {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {D : X.IdealSheafData} {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (s : S)
    (hs : ∀ x ∈ (D.support : Set X), f.base x = s) (hf : IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (g : X' ⟶ S),
      IsContractionOfExceptionalCurve D b ∧ b ≫ g = f ∧ IsQuasiProjective g := by
  have := hE.isEffectiveCartierDivisor
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨d₀⟩ : Nonempty D.subscheme := inferInstance
  have hne : (D.support : Set X).Nonempty := ⟨_, subschemeι_mem_support D d₀⟩
  -- an affine neighbourhood `U` of `s` in which `s` is closed
  have him : f.base '' (D.support : Set X) = {s} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hne.some_mem, hs _ hne.some_mem⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hs x hx
  obtain ⟨U₁, hsU₁, hU₁s⟩ :=
    exists_isOpen_inter_closure_singleton_subset f D.support D.support.isClosed s him
  obtain ⟨-, ⟨U, hU, rfl⟩, hsU, hUU₁⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hsU₁ U₁.isOpen
  -- a projective compactification, and the ample module it carries
  obtain ⟨Xb, jX, p, hjX, hp, hjp⟩ :=
    Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs f hf
  have := hjX
  subst hjp
  have : IsProper p := hp.isProper
  obtain ⟨-, Lb, hLbinv, hLbamp⟩ := hp.isQuasiProjective
  have : Stacks.Ample.IsInvertibleModule Xb Lb := hLbinv
  let L : X.Modules := (Scheme.Modules.pullback jX).obj Lb
  have : Stacks.Ample.IsInvertibleModule X L :=
    Scheme.Modules.isInvertibleModule_pullback_obj jX Lb
  have hL : Stacks.RelativeAmple.IsRelativelyAmple (jX ≫ p) L :=
    isRelativelyAmple_comp_of_isOpenImmersion jX p Lb hLbamp
  -- the part of the compactification over `U`
  set Y : X.Opens := (jX ≫ p) ⁻¹ᵁ U with hYdef
  set Ub : Xb.Opens := p ⁻¹ᵁ U with hUbdef
  let jY : Y.toScheme ⟶ Ub.toScheme := jX ∣_ Ub
  have : IsOpenImmersion jY := inferInstanceAs (IsOpenImmersion (jX ∣_ Ub))
  have hjY : jY ≫ Ub.ι = Y.ι ≫ jX := morphismRestrict_ι jX Ub
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let pU : Ub.toScheme ⟶ Spec (.of Γ(S, U)) := (p ∣_ U) ≫ hU.isoSpec.hom
  have : IsProper pU := by
    have : IsProper (p ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› U
    infer_instance
  have hsuppY : (D.support : Set X) ⊆ Set.range Y.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx => show (jX ≫ p).base x ∈ U from hs x hx ▸ hsU
  have hEY := Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.comap Y.ι D hE hsuppY
  set DY := D.comap Y.ι with hDYdef
  have hDYsupp : (DY.support : Set Y.toScheme) = Y.ι.base ⁻¹' (D.support : Set X) := by
    rw [hDYdef, Scheme.IdealSheafData.support_comap]
    rfl
  -- the curve is closed in the compactification over `U`
  let sU : (Scheme.Opens.toScheme U) := ⟨s, hsU⟩
  have hsUcl : IsClosed ({sU} : Set (Scheme.Opens.toScheme U)) := by
    have hpre : (Subtype.val : U → S) ⁻¹' closure {s} = {sU} := by
      ext t
      simp only [Set.mem_preimage]
      constructor
      · intro ht
        exact Subtype.ext (hU₁s ⟨hUU₁ t.2, ht⟩)
      · rintro rfl
        exact subset_closure rfl
    have h : IsClosed ((Subtype.val : U → S) ⁻¹' closure {s}) :=
      (isClosed_closure (s := ({s} : Set S))).preimage continuous_subtype_val
    rw [hpre] at h
    exact h
  set m : Spec (.of Γ(S, U)) := hU.isoSpec.hom.base sU
  have hm : IsClosed ({m} : Set (Spec (.of Γ(S, U)))) := by
    rw [show ({m} : Set (Spec (.of Γ(S, U)))) = hU.isoSpec.hom.base '' {sU} by simp [m]]
    exact hU.isoSpec.hom.homeomorph.isClosedMap _ hsUcl
  have hjYpU : jY ≫ pU = ((jX ≫ p) ∣_ U) ≫ hU.isoSpec.hom := by
    simp only [jY, pU, morphismRestrict_comp]
    rfl
  have : LocallyOfFiniteType (DY.subschemeι ≫ jY ≫ pU) := by
    rw [hjYpU]
    infer_instance
  have hres : ∀ w : Y.toScheme, Y.ι.base w ∈ (D.support : Set X) →
      ((jX ≫ p) ∣_ U).base w = sU := fun w hw => by
    apply Subtype.ext
    have := congrArg (fun φ => φ.base w) (morphismRestrict_ι (jX ≫ p) U)
    exact this.trans (hs _ hw)
  have hzsupp : ∀ z : DY.subscheme, Y.ι.base (DY.subschemeι.base z) ∈ (D.support : Set X) :=
    fun z => by
      have hz := subschemeι_mem_support DY z
      rwa [hDYsupp] at hz
  have hcl := isClosed_range_subschemeι_comp_of_iso_projectiveLineProj DY
    (e ≪≫ (D.comapSubschemeIso Y.ι hsuppY).symm) jY pU m hm (fun z => by
      rw [hjYpU, Scheme.Hom.comp_apply, hres _ (hzsupp z)])
  obtain ⟨Db, eb, hEb, hDbY, hsuppb⟩ :=
    exists_isExceptionalCurveOfFirstKind_of_isClosed_range jY hEY hcl
  -- the contraction over `U` in the compactification, by Tag 0C2M
  let LU : Ub.toScheme.Modules := (Scheme.Modules.pullback Ub.ι).obj Lb
  have : Stacks.Ample.IsInvertibleModule Ub.toScheme LU :=
    Scheme.Modules.isInvertibleModule_pullback_obj Ub.ι Lb
  have hLU : Scheme.Modules.IsAmple Ub.toScheme LU :=
    isAmple_pullback_of_isAmple_pullbackModule Ub.ι Lb (hLbamp.2 U hU)
  obtain ⟨Ub', cb, hcb, ⟨fUb', hfUb', hfUb'p⟩, ⟨nb, hnb⟩, hLb'⟩ :=
    exists_contraction_isProper_isAmple pU LU hLU hEb
  obtain ⟨⟨Nb, hNbinv, hNbcl⟩, hNbamp⟩ := hLb' nb hnb
  have hNb : Scheme.Modules.IsAmple Ub' Nb := hNbamp Nb hNbcl
  -- restrict the contraction to the image of `Y`
  have : IsNoetherian Ub' := hcb.isNoetherian
  have := hcb.isProper
  obtain ⟨z, hz, hreg, hdim, hDz, ε, hε⟩ := hcb.exists_blowUp_iso
  have hcbz := base_eq_iff_mem_support_of_eq_comap hDz
  have hisoz : IsIso (cb ∣_ (⟨({z} : Set Ub')ᶜ, hz.isOpen_compl⟩ : Ub'.Opens)) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  have hinj : ∀ x y, x ∉ (Db.support : Set Ub.toScheme) → y ∉ (Db.support : Set Ub.toScheme) →
      cb.base x = cb.base y → x = y := by
    intro x y hx hy hxy
    let Z₀ : Ub'.Opens := ⟨({z} : Set Ub')ᶜ, hz.isOpen_compl⟩
    have hx' : x ∈ cb ⁻¹ᵁ Z₀ := fun h => hx ((hcbz x).1 h)
    have hy' : y ∈ cb ⁻¹ᵁ Z₀ := fun h => hy ((hcbz y).1 h)
    have hinj' := (cb ∣_ Z₀).isOpenEmbedding.injective
      (a₁ := ⟨x, hx'⟩) (a₂ := ⟨y, hy'⟩) (by
        apply Subtype.ext
        have h1 := congrArg (fun φ => φ.base (⟨x, hx'⟩ : (cb ⁻¹ᵁ Z₀).toScheme))
          (morphismRestrict_ι cb Z₀)
        have h2 := congrArg (fun φ => φ.base (⟨y, hy'⟩ : (cb ⁻¹ᵁ Z₀).toScheme))
          (morphismRestrict_ι cb Z₀)
        exact h1.trans (hxy.trans h2.symm))
    exact congrArg Subtype.val hinj'
  let C : Set Ub' := cb.base '' (Set.range jY.base)ᶜ
  have hCcl : IsClosed C := cb.isClosedMap _ jY.isOpenEmbedding.isOpen_range.isClosed_compl
  let V'' : Ub'.Opens := ⟨Cᶜ, hCcl.isOpen_compl⟩
  have hpreV : cb ⁻¹ᵁ V'' = jY.opensRange := by
    ext x
    constructor
    · intro hx
      by_contra hxj
      exact hx ⟨x, hxj, rfl⟩
    · rintro hxj ⟨y, hy, hyx⟩
      have hysupp : y ∉ (Db.support : Set Ub.toScheme) := fun h => hy (hsuppb h)
      by_cases hxs : x ∈ (Db.support : Set Ub.toScheme)
      · exact hysupp ((hcbz y).1 (hyx.trans ((hcbz x).2 hxs)))
      · exact hy (hinj y x hysupp hxs hyx ▸ hxj)
  -- a point of the curve in the compactification
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y.toScheme, Y.ι.base y₀ = D.subschemeι.base d₀ :=
    hsuppY (subschemeι_mem_support D d₀)
  have hy₀b : jY.base y₀ ∈ (Db.support : Set Ub.toScheme) := by
    have h1 : y₀ ∈ (DY.support : Set Y.toScheme) := by
      rw [hDYsupp]
      show Y.ι.base y₀ ∈ (D.support : Set X)
      rw [hy₀]
      exact subschemeι_mem_support D d₀
    have h3 : DY = Db.comap jY := hDbY.symm
    rwa [h3, Scheme.IdealSheafData.support_comap] at h1
  have hzV : z ∈ V'' := by
    have h1 : jY.base y₀ ∈ cb ⁻¹ᵁ V'' := by rw [hpreV]; exact ⟨y₀, rfl⟩
    have h2 := (hcbz _).2 hy₀b
    rw [← h2]
    exact h1
  have hcres := contraction_restrict Db cb z hz hreg hdim hDz ε hε V'' hzV
  let φ : Y.toScheme ≅ (cb ⁻¹ᵁ V'').toScheme := jY.isoOpensRange ≪≫ Ub.toScheme.isoOfEq hpreV.symm
  have hφ : φ.hom ≫ (cb ⁻¹ᵁ V'').ι = jY := by
    simp only [φ, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι]
  have hc := hcres.iso_comp φ
  have hDc : (Db.comap (cb ⁻¹ᵁ V'').ι).comap φ.hom = DY := by
    rw [← Scheme.IdealSheafData.comap_comp, hφ, hDbY]
  rw [hDc] at hc
  set c : Y.toScheme ⟶ V''.toScheme := φ.hom ≫ cb ∣_ V'' with hcdef
  have hcV : c ≫ V''.ι = jY ≫ cb := by
    rw [hcdef, Category.assoc, morphismRestrict_ι, ← Category.assoc, hφ]
  let gV : V''.toScheme ⟶ S := V''.ι ≫ fUb' ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U
  have := hfUb'p
  have : LocallyOfFiniteType gV := by infer_instance
  have hgV : c ≫ gV = Y.ι ≫ (jX ≫ p) := by
    show c ≫ V''.ι ≫ fUb' ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U = _
    rw [← Category.assoc c V''.ι, hcV, Category.assoc, ← Category.assoc cb, hfUb']
    simp only [pU, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
    rw [← Category.assoc, hjY, Category.assoc]
  -- the ample module over `V''`
  have : Stacks.Ample.IsInvertibleModule Ub' Nb := hNbinv
  let N : V''.toScheme.Modules := (Scheme.Modules.pullback V''.ι).obj Nb
  have : Stacks.Ample.IsInvertibleModule V''.toScheme N :=
    Scheme.Modules.isInvertibleModule_pullback_obj V''.ι Nb
  have hN : Scheme.Modules.IsAmple V''.toScheme N := by
    refine isAmple_pullback_of_isAmple_pullbackModule V''.ι Nb ?_
    exact Stacks.SectionExtension.isAmple_pullbackModule V''.ι Nb
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple _ _ hNb)
      (Or.inr (Or.inl ⟨isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (V'' : Set Ub')),
        inferInstance⟩))
  have := hEY.isEffectiveCartierDivisor
  have := hEb.isEffectiveCartierDivisor
  have := Scheme.Modules.isInvertibleModule_pullback_obj Y.ι L
  have := Scheme.Modules.isInvertibleModule_pullback_obj jY LU
  have hNcl : Stacks.Picard.schemePullbackClass c (cls N) =
      DY.exceptionalTwist nb (cls ((Scheme.Modules.pullback Y.ι).obj L)) := by
    rw [← schemePullbackClass_cls, Stacks.Picard.schemePullbackClass_comp, hcV,
      ← Stacks.Picard.schemePullbackClass_comp, hNbcl]
    show Stacks.Picard.schemePullbackClassHom jY
        (cls LU + nb • Stacks.Divisors.picardClass Db) =
      cls ((Scheme.Modules.pullback Y.ι).obj L) + nb • Stacks.Divisors.picardClass DY
    rw [map_add, map_zsmul]
    show Stacks.Picard.schemePullbackClass jY (cls LU) +
        nb • Stacks.Picard.schemePullbackClass jY (Stacks.Divisors.picardClass Db) = _
    rw [schemePullbackClass_cls, Scheme.IdealSheafData.schemePullbackClass_picardClass]
    have : Stacks.Divisors.IsEffectiveCartierDivisor (Db.comap jY) :=
      Stacks.Divisors.isPullbackDefined_of_flat jY Db inferInstance
    rw [Stacks.Divisors.picardClass_congr hDbY]
    congr 1
    exact cls_eq_of_iso ((Scheme.Modules.pullbackComp jY Ub.ι).app Lb ≪≫
      (Scheme.Modules.pullbackCongr hjY).app Lb ≪≫
      ((Scheme.Modules.pullbackComp Y.ι jX).app Lb).symm)
  -- glue, by the engine
  obtain ⟨X', b, g, L', hL'inv, hb, hg, hgft, -, hampU, R, hR, hampR⟩ :=
    exists_contraction_of_ample_chart (jX ≫ p) hE s hs L hL U hU hsU c hc gV hgV nb N hN hNcl
  have := hL'inv
  have : IsNoetherian X' := hb.isNoetherian
  have : Surjective b := ⟨surjective_of_isContractionOfExceptionalCurve D k e b hb⟩
  have := hb.isProper
  have : QuasiCompact g := inferInstance
  -- `g` is separated
  have : IsSeparated p := hp.isSeparated
  have : IsSeparated g := by
    let ψ : (Over.mk (b ≫ g) : Over S) ⟶ Over.mk g := Over.homMk b rfl
    have : Surjective ψ.left := show Surjective b from inferInstance
    have : UniversallyClosed ψ.left := show UniversallyClosed b from inferInstance
    have : IsSeparated (Over.mk (b ≫ g) : Over S).hom := by
      show IsSeparated (b ≫ g)
      rw [hg]
      infer_instance
    exact isSeparated_of_surjective_universallyClosed ψ
  -- the centre of the contraction
  obtain ⟨v, hv, hregv, hdimv, hDv, -, -⟩ := hb.exists_blowUp_iso
  have hbv := base_eq_iff_mem_support_of_eq_comap hDv
  have hvR : v ∉ R := by
    intro hvR
    have h1 : D.subschemeι.base d₀ ∈ b ⁻¹ᵁ R := by
      show b.base _ ∈ R
      rw [(hbv _).2 (subschemeι_mem_support D d₀)]
      exact hvR
    rw [hR] at h1
    exact h1 (subschemeι_mem_support D d₀)
  have hyR : ∀ y : X', y ≠ v → y ∈ R := fun y hy => by
    obtain ⟨x, rfl⟩ := b.surjective y
    have hx : x ∈ b ⁻¹ᵁ R := by
      rw [hR]
      exact fun hx => hy ((hbv x).2 hx)
    exact hx
  have hgv : g.base v = s := by
    rw [← (hbv _).2 (subschemeι_mem_support D d₀), ← Scheme.Hom.comp_apply, hg]
    exact hs _ (subschemeι_mem_support D d₀)
  have hdepth : (2 : ℕ∞) ≤ Module.depth (X'.presheaf.stalk v)
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk v)) (X'.presheaf.stalk v) :=
    two_le_depth_of_isRegularLocalRing v hregv hdimv
  -- `ℒ'` is `g`-ample
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple g L' := by
    refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple g L'
      inferInstance fun t => ?_
    obtain ⟨-, ⟨V, hV, rfl⟩, htV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
    refine ⟨V, hV, htV, ?_⟩
    by_cases hsV : s ∈ V
    · -- Lemma Q
      obtain ⟨h', hh'U, hsh'⟩ := hV.exists_basicOpen_le (V := U) ⟨s, hsU⟩ hsV
      have hbo : X'.basicOpen (g.app V h') = g ⁻¹ᵁ S.basicOpen h' :=
        (Scheme.Hom.preimage_basicOpen g h').symm
      have hvY : v ∈ g ⁻¹ᵁ V := by
        show g.base v ∈ V
        rw [hgv]
        exact hsV
      refine isAmple_pullbackModule_of_basicOpen_of_compl L' (g ⁻¹ᵁ V) (g ⁻¹ᵁ V ⊓ R)
        (isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _))
        (fun A B hA hAo hAc hB hBo hBc => NoetherianSpace.isCompact _) v hvY inf_le_left
        (fun h => hvR h.2) (fun y hy hyv => ⟨hy, hyR y hyv⟩) (g.app V h') ?_ ?_ (hampR V hV)
        ?_ ?_
      · rw [hbo]
        show g.base v ∈ S.basicOpen h'
        rw [hgv]
        exact hsh'
      · rw [hbo]
        exact hampU _ (hV.basicOpen h') hh'U
      · intro n σ
        have : Stacks.Ample.IsInvertibleModule X' (Stacks.Ample.tensorPowModule X' L' (n : ℤ)) :=
          inferInstance
        have hunit := isIso_unit_of_isInvertible_of_depth X'
          (Stacks.Ample.tensorPowModule X' L' (n : ℤ)) R fun x hx => by
            rw [show x = v from by_contra fun h => hx (hyR x h)]
            exact hdepth
        exact surjective_restriction_of_isIso_unit R _ hunit (g ⁻¹ᵁ V) σ
      · intro Ω hΩ hvΩ haff
        have : IsAffine (Scheme.Opens.toScheme V) := hV
        let q : Ω.toScheme ⟶ Scheme.Opens.toScheme V := g.resLE V Ω hΩ
        have : IsSeparated q := by
          have : IsSeparated (q ≫ Scheme.Opens.ι V) := by
            rw [Scheme.Hom.resLE_comp_ι]
            infer_instance
          exact IsSeparated.of_comp q (Scheme.Opens.ι V)
        let U' : Ω.toScheme.Opens := Ω.ι ⁻¹ᵁ (Ω ⊓ (g ⁻¹ᵁ V ⊓ R))
        have : IsAffine U'.toScheme := by
          have h1 : Ω.ι ''ᵁ U' = Ω ⊓ (g ⁻¹ᵁ V ⊓ R) := by
            rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
              ← inf_assoc, inf_idem]
          have h2 : IsAffineOpen (Ω.ι ''ᵁ U') := by rwa [h1]
          exact (Ω.ι.isAffineOpen_iff_of_isOpenImmersion.mp h2)
        have hc' : IsIso U'.ι.c := by
          refine isIso_c_ι_of_depth_ge_two Ω.toScheme U' fun x hx => ?_
          have hxv : Ω.ι.base x = v := by
            by_contra hxv
            exact hx ⟨x.2, hΩ x.2, hyR _ hxv⟩
          have hxv' : x = ⟨v, hvΩ⟩ := Subtype.ext hxv
          subst hxv'
          have := hregv
          have hreg' : IsRegularLocalRing (Ω.toScheme.presheaf.stalk ⟨v, hvΩ⟩) :=
            IsRegularLocalRing.of_ringEquiv (Ω.stalkIso ⟨v, hvΩ⟩).symm.commRingCatIsoToRingEquiv
          have hdim' : ringKrullDim (Ω.toScheme.presheaf.stalk ⟨v, hvΩ⟩) = 2 := by
            rwa [(Ω.stalkIso ⟨v, hvΩ⟩).commRingCatIsoToRingEquiv.ringKrullDim]
          exact two_le_depth_of_isRegularLocalRing _ hreg' hdim'
        exact false_of_isIso_c_of_isAffine q U' hc' ⟨v, hvΩ⟩ fun h => hvR h.2.2
    · -- affine opens avoiding `s`
      have hVR : g ⁻¹ᵁ V ⊓ R = g ⁻¹ᵁ V := by
        refine inf_eq_left.mpr fun y hy => hyR y ?_
        rintro rfl
        exact hsV (hgv ▸ hy)
      have h := hampR V hV
      rwa [hVR] at h
  exact ⟨X', b, g, hb, hg, ⟨⟨hgft, inferInstance⟩, L', hL'inv, hrel⟩⟩

end AlgebraicGeometry

end
