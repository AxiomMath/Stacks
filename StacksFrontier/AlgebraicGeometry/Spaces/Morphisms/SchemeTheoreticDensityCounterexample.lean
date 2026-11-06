module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseNotTopologicallyDense
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# A scheme-theoretic closure that is everything without scheme-theoretic density

Let `k` be a field, let `A = k[x, z₁, z₂, …]/(xⁿ zₙ)`, let `X = Spec A` and let
`U = X ∖ V(z₁, z₂, …)`, the example of Stacks 01RC. The scheme-theoretic closure of `U` in `X`
is all of `X`, yet `U` is not even topologically dense in `X`; so `U` is not a
scheme-theoretically dense open subscheme of `X` in the sense of Stacks 01RB.

Read in the big fppf site of `X`, with `X` the final object of that site and `U` the open
subspace it cuts out, this says that the scheme-theoretic closure of an open subspace of an
algebraic space being all of the space does not make the open subspace scheme-theoretically
dense in the sense of Stacks 0834, even when the closure of the inverse image of `U` is
everything over a surjective étale scheme chart.

## Main results

* `AlgebraicGeometry.Scheme.Opens.dense_of_isSchemeTheoreticallyDense`: a
  scheme-theoretically dense open subscheme is topologically dense.
* `AlgebraicGeometry.Space.Counterexample0833.not_isSchemeTheoreticallyDense_openComplement`:
  the open `U` is not a scheme-theoretically dense open subscheme of `X`, Stacks 01RB.
* `AlgebraicGeometry.Space.Counterexample0833.exists_etale_chart_not_isSchemeTheoreticallyDense`:
  in the big fppf site of `X` the open subspace `U` of the algebraic space `X` admits a
  surjective étale scheme chart over which the scheme-theoretic closure of its inverse image is
  everything, and is nevertheless not scheme-theoretically dense.
* `AlgebraicGeometry.Space.exists_schemeTheoreticClosure_eq_top_not_isSchemeTheoreticallyDense`
  is the same statement with the site, the scheme, the space and the open subspace existentially
  quantified, so that it is unconditional.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 01RC](https://stacks.math.columbia.edu/tag/01RC)
* [Stacks Project, Tag 01RD](https://stacks.math.columbia.edu/tag/01RD)
* [Stacks Project, Tag 0833](https://stacks.math.columbia.edu/tag/0833)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0835](https://stacks.math.columbia.edu/tag/0835)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.Morphisms.DenseNotTopologicallyDense

universe u

namespace AlgebraicGeometry

/-! ### Scheme-theoretic density of an open subscheme implies topological density -/

/-- A scheme-theoretically dominant morphism out of the empty scheme forces its target to be
empty. -/
theorem isEmpty_of_isSchemeTheoreticallyDominant {A Y : Scheme.{u}} (f : A ⟶ Y)
    [IsSchemeTheoreticallyDominant f] (hA : IsEmpty A) : IsEmpty Y := by
  rwa [← Scheme.Hom.ker_eq_top_iff_isEmpty (𝟙 Y), Scheme.Hom.ker_eq_bot_of_isIso,
    ← Scheme.Hom.ker_eq_bot f, Scheme.Hom.ker_eq_top_iff_isEmpty]

/-- A scheme-theoretically dense open subscheme is topologically dense. -/
theorem Scheme.Opens.dense_of_isSchemeTheoreticallyDense {X : Scheme.{u}} (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) : Dense (U : Set X) := by
  refine dense_iff_inter_open.2 fun V hVopen ⟨x, hx⟩ ↦ ?_
  by_contra hne
  let W : X.Opens := ⟨V, hVopen⟩
  have := hU W
  have hempty : IsEmpty ↥(W.ι ⁻¹ᵁ U).toScheme := ⟨fun y ↦ hne ⟨y.1.1, y.1.2, y.2⟩⟩
  exact (isEmpty_of_isSchemeTheoreticallyDominant (W.ι ⁻¹ᵁ U).ι hempty).elim
    (⟨x, hx⟩ : ↥W.toScheme)

namespace Space

/-- Small discrete limits of presheaves on the big fppf site (instance search for them times out
under Lean v4.35.0). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_SchemeTheoreticDensityCounterexample
    {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U} (J : Type) :
    Limits.HasLimitsOfShape (Discrete J) ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-! ### Open subschemes of an object of the big fppf site -/

section SiteOpens

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of `AlgebraicGeometry.Space.siteOpenObject` into the ambient object of the big
fppf site. -/
def siteOpenInclusion (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) : siteOpenObject B S hS V W ⟶ V :=
  Over.homMk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι) (by rfl)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteOpenInclusion` is the
inclusion of the open subscheme. -/
@[simp]
lemma siteOpenInclusion_map (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).map (siteOpenInclusion B S hS V W) = W.ι := by
  show B.inclusion.map (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι) = W.ι
  rw [B.inclusion.map_preimage]

/-- The presheaf map of `AlgebraicGeometry.Space.siteOpenInclusion` is an open immersion of
algebraic spaces. -/
lemma isOpenImmersion_yoneda_siteOpenInclusion (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsOpenImmersion B S hS (yoneda.map (siteOpenInclusion B S hS V W)) :=
  presheaf_yoneda_map_of_inverseImage B S hS inferInstance _
    (by rw [siteOpenInclusion_map]; infer_instance)

/-- The presheaf map of `AlgebraicGeometry.Space.siteOpenInclusion` is étale. -/
lemma isEtale_yoneda_siteOpenInclusion (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsEtale B S hS (yoneda.map (siteOpenInclusion B S hS V W)) :=
  isEtale_of_presheafEtale B S hS _ ((presheaf_yoneda_map_etale_iff B S hS _).2
    (by rw [siteOpenInclusion_map]; infer_instance))

/-- **Scheme-theoretic dominance only depends on the image subfunctor.** Of two morphisms of the
big fppf site into a common target whose presheaf maps are monomorphisms with the same image
subfunctor, one is scheme-theoretically dominant as soon as the other is. -/
lemma isSchemeTheoreticallyDominant_of_range_yoneda_eq {P R V : BigFppfOver B S hS}
    (a : P ⟶ V) (b : R ⟶ V) (ha : Mono (yoneda.map a)) (hb : Mono (yoneda.map b))
    (hrange : Subfunctor.range (yoneda.map a) = Subfunctor.range (yoneda.map b))
    (hdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map b)) :
    IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map a) := by
  have hamono : Mono a := yoneda.mono_of_mono_map ha
  have hbmono : Mono b := yoneda.mono_of_mono_map hb
  obtain ⟨l, hl⟩ : ∃ l : P ⟶ R, l ≫ b = a := by
    have hmem : a ∈ (Subfunctor.range (yoneda.map a)).obj (op P) := ⟨𝟙 P, by simp⟩
    rw [hrange] at hmem
    exact hmem
  obtain ⟨m, hm⟩ : ∃ m : R ⟶ P, m ≫ a = b := by
    have hmem : b ∈ (Subfunctor.range (yoneda.map b)).obj (op R) := ⟨𝟙 R, by simp⟩
    rw [← hrange] at hmem
    exact hmem
  have hlm : l ≫ m = 𝟙 P := by
    rw [← cancel_mono a, Category.assoc, hm, hl, Category.id_comp]
  have hml : m ≫ l = 𝟙 R := by
    rw [← cancel_mono b, Category.assoc, hl, hm, Category.id_comp]
  have : IsIso l := ⟨⟨m, hlm, hml⟩⟩
  rw [isSchemeTheoreticallyDominant_iff, ← hl, Functor.map_comp, Scheme.Hom.ker_comp_of_isIso]
  exact hdom.ker_eq_bot

end SiteOpens

namespace Counterexample0833

/-! ### The open of Stacks 01RC is not scheme-theoretically dense -/

variable (k : Type u) [Field k]

/-- The open `U` of Stacks 01RC is not a scheme-theoretically dense open subscheme of `X`. -/
theorem not_isSchemeTheoreticallyDense_openComplement :
    ¬ Scheme.Opens.IsSchemeTheoreticallyDense (openComplement k) := fun h =>
  not_dense_openComplement k (Scheme.Opens.dense_of_isSchemeTheoreticallyDense _ h)

/-- The inverse image in `X` of the basic open `D(x)` of `Spec k[x]` under the projection
`X ⟶ Spec k[x]`: a nonempty open subscheme of `X` disjoint from `U`. -/
def xFibre : (exampleScheme k).Opens :=
  (xProjection k) ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X () : xRing k)

/-- A point lies in `AlgebraicGeometry.Space.Counterexample0833.xFibre` exactly when the
projection sends it into `D(x)`. -/
lemma mem_xFibre_iff (p : exampleScheme k) :
    p ∈ (xFibre k : Set (exampleScheme k)) ↔
      (xProjection k).base p ∈
        (PrimeSpectrum.basicOpen (MvPolynomial.X () : xRing k) :
          Set (PrimeSpectrum (xRing k))) :=
  Iff.rfl

/-- The open `AlgebraicGeometry.Space.Counterexample0833.xFibre` is nonempty. -/
theorem nonempty_xFibre : (xFibre k : Set (exampleScheme k)).Nonempty := by
  let q : PrimeSpectrum (xRing k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : q ∈ PrimeSpectrum.basicOpen (MvPolynomial.X () : xRing k) := by
    rw [PrimeSpectrum.mem_basicOpen]
    simp [q]
  obtain ⟨p, hp⟩ := surjective_xProjection k q
  refine ⟨p, ?_⟩
  rw [mem_xFibre_iff, hp]
  exact hq

/-- The open `U` and the open `AlgebraicGeometry.Space.Counterexample0833.xFibre` are
disjoint. -/
theorem notMem_xFibre_of_mem_openComplement (p : exampleScheme k)
    (hp : p ∈ (openComplement k : Set (exampleScheme k))) :
    p ∉ (xFibre k : Set (exampleScheme k)) :=
  xProjection_openComplement_avoids_xOpen k p hp

/-! ### The counterexample as an open subspace of an algebraic space -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (exampleScheme k))

/-- The scheme `X = Spec A` of Stacks 01RC, as the final object of its own big fppf site. -/
abbrev baseObject : BigFppfOver B (exampleScheme k) hS :=
  siteObject B (exampleScheme k) hS hS (𝟙 (exampleScheme k))

/-- The algebraic space `X = Spec A` of Stacks 01RC over itself: the presheaf represented by the
final object of its big fppf site. -/
abbrev space : (BigFppfOver B (exampleScheme k) hS)ᵒᵖ ⥤ Type u :=
  yoneda.obj (baseObject k B hS)

/-- The open `U = X ∖ V(z₁, z₂, …)` of Stacks 01RC, as an object of the big fppf site of `X`
mapping to `X`. -/
abbrev openInclusion :
    siteOpenObject B (exampleScheme k) hS (baseObject k B hS) (openComplement k) ⟶
      baseObject k B hS :=
  siteOpenInclusion B (exampleScheme k) hS (baseObject k B hS) (openComplement k)

/-- The open `U = X ∖ V(z₁, z₂, …)` of Stacks 01RC, as an open subspace of the algebraic space
`X`. -/
abbrev openSubspace : Subfunctor (space k B hS) :=
  Subfunctor.range (yoneda.map (openInclusion k B hS))

/-- `U` is an open subspace of the algebraic space `X` in the sense of Stacks 02YU part (2). -/
theorem isOpenSubspace_openSubspace :
    IsOpenSubspace B (exampleScheme k) hS (openSubspace k B hS) :=
  isOpenSubspace_range_of_isOpenImmersion _ _
    (isOpenImmersion_yoneda_siteOpenInclusion B (exampleScheme k) hS _ _)

set_option synthInstance.maxHeartbeats 400000 in
/-- The morphism of the site representing the inverse image of `U` along a scheme chart of `X`
has that inverse image as its image subfunctor. -/
private lemma range_yoneda_snd
    {V : BigFppfOver B (exampleScheme k) hS} (φ : yoneda.obj V ⟶ space k B hS) :
    Subfunctor.range (yoneda.map ((isOpenSubspace_openSubspace k B hS).2.rep.snd φ)) =
      (openSubspace k B hS).preimage φ := by
  rw [← preimageIso_hom_ι B (exampleScheme k) hS (openSubspace k B hS)
    (isOpenSubspace_openSubspace k B hS).2.rep φ, Subfunctor.range_comp, Subfunctor.range_eq_top,
    Subfunctor.image_top, Subfunctor.range_ι]

set_option synthInstance.maxHeartbeats 400000 in
/-- The presheaf map of the morphism representing `U ×_X V` is a monomorphism. -/
private lemma mono_yoneda_snd
    {V : BigFppfOver B (exampleScheme k) hS} (φ : yoneda.obj V ⟶ space k B hS) :
    Mono (yoneda.map ((isOpenSubspace_openSubspace k B hS).2.rep.snd φ)) := by
  rw [← preimageIso_hom_ι B (exampleScheme k) hS (openSubspace k B hS)
    (isOpenSubspace_openSubspace k B hS).2.rep φ]
  infer_instance

/-- The scheme-theoretic closure of `U` in `X` is all of `X`. -/
theorem schemeTheoreticClosure_eq_top :
    schemeTheoreticClosure B (exampleScheme k) hS (openSubspace k B hS) = ⊤ := by
  have hU := isOpenSubspace_openSubspace k B hS
  have key := schemeTheoreticImageSubfunctor_preimage_eq_top_iff B (exampleScheme k) hS hU.2
    (𝟙 (space k B hS))
  rw [Subfunctor.preimage_id] at key
  refine key.2 (isSchemeTheoreticallyDominant_of_range_yoneda_eq B (exampleScheme k) hS
    (hU.2.rep.snd (𝟙 (space k B hS))) (openInclusion k B hS)
    (mono_yoneda_snd k B hS _)
    (mono_of_presheaf_isOpenImmersion
      (isOpenImmersion_yoneda_siteOpenInclusion B (exampleScheme k) hS _ _)) ?_ ?_)
  · rw [range_yoneda_snd k B hS, Subfunctor.preimage_id]
  · rw [siteOpenInclusion_map]
    exact schemeTheoreticImage_openInclusion k

/-- The open subspace `U` is not scheme-theoretically dense in `X`. -/
theorem not_isSchemeTheoreticallyDense :
    ¬ IsSchemeTheoreticallyDense B (exampleScheme k) hS (openSubspace k B hS) := by
  intro hdense
  have hU := isOpenSubspace_openSubspace k B hS
  set jD : siteOpenObject B (exampleScheme k) hS (baseObject k B hS) (xFibre k) ⟶
      baseObject k B hS :=
    siteOpenInclusion B (exampleScheme k) hS (baseObject k B hS) (xFibre k) with hjD
  have hclosure := hdense (isAlgebraicSpace_yoneda B (exampleScheme k) hS _) (yoneda.map jD)
    (isEtale_yoneda_siteOpenInclusion B (exampleScheme k) hS _ _)
  have hdom := (schemeTheoreticImageSubfunctor_preimage_eq_top_iff B (exampleScheme k) hS hU.2
    (yoneda.map jD)).1 hclosure
  have hmem : hU.2.rep.snd (yoneda.map jD) ∈
      ((openSubspace k B hS).preimage (yoneda.map jD)).obj
        (op (hU.2.rep.pullback (yoneda.map jD))) := by
    rw [← range_yoneda_snd k B hS (yoneda.map jD)]
    exact ⟨𝟙 _, by simp⟩
  obtain ⟨l, hl⟩ : ∃ l, l ≫ openInclusion k B hS =
      hU.2.rep.snd (yoneda.map jD) ≫ jD := hmem
  have hmapeq : (BigFppfOver.toScheme B (exampleScheme k) hS).map l ≫ (openComplement k).ι =
      (BigFppfOver.toScheme B (exampleScheme k) hS).map (hU.2.rep.snd (yoneda.map jD)) ≫
        (xFibre k).ι := by
    rw [← siteOpenInclusion_map B (exampleScheme k) hS (baseObject k B hS) (openComplement k),
      ← siteOpenInclusion_map B (exampleScheme k) hS (baseObject k B hS) (xFibre k),
      ← Functor.map_comp, ← Functor.map_comp, hl]
  have hmem_open : ∀ {W : (exampleScheme k).Opens} {Y : Scheme.{u}} (g : Y ⟶ W.toScheme) (p : Y),
      (g ≫ W.ι).base p ∈ (W : Set (exampleScheme k)) := fun g p => (g.base p).2
  have hempty : IsEmpty ((BigFppfOver.toScheme B (exampleScheme k) hS).obj
      (hU.2.rep.pullback (yoneda.map jD))) := by
    refine ⟨fun p => ?_⟩
    have h1 := hmem_open ((BigFppfOver.toScheme B (exampleScheme k) hS).map l) p
    rw [hmapeq] at h1
    exact notMem_xFibre_of_mem_openComplement k _ h1
      (hmem_open ((BigFppfOver.toScheme B (exampleScheme k) hS).map
        (hU.2.rep.snd (yoneda.map jD))) p)
  have hDempty : IsEmpty ((BigFppfOver.toScheme B (exampleScheme k) hS).obj
      (siteOpenObject B (exampleScheme k) hS (baseObject k B hS) (xFibre k))) :=
    isEmpty_of_isSchemeTheoreticallyDominant
      ((BigFppfOver.toScheme B (exampleScheme k) hS).map
        (hU.2.rep.snd (yoneda.map jD))) hempty
  obtain ⟨x, hx⟩ := nonempty_xFibre k
  exact hDempty.elim (⟨x, hx⟩ : ↥(xFibre k).toScheme)

/-- **The literal reading of condition (2) of Stacks 0833 does not imply condition (1).** The
identity of `X` is a surjective étale morphism from a scheme over which the scheme-theoretic
closure of the inverse image of `U` is all of `X`, and yet `U` is not scheme-theoretically dense
in `X` in the sense of Stacks 0834. -/
theorem exists_etale_chart_not_isSchemeTheoreticallyDense :
    (∃ (V : BigFppfOver B (exampleScheme k) hS) (φ : yoneda.obj V ⟶ space k B hS),
        IsSurjective B (exampleScheme k) hS φ ∧ IsEtale B (exampleScheme k) hS φ ∧
          schemeTheoreticClosure B (exampleScheme k) hS
            ((openSubspace k B hS).preimage φ) = ⊤) ∧
      ¬ IsSchemeTheoreticallyDense B (exampleScheme k) hS (openSubspace k B hS) := by
  refine ⟨⟨baseObject k B hS, 𝟙 (space k B hS), ?_, ?_, ?_⟩,
    not_isSchemeTheoreticallyDense k B hS⟩
  · show Function.Surjective (pointsMap B (exampleScheme k) hS _ _)
    rw [pointsMap_id]
    exact Function.surjective_id
  · exact isEtale_of_presheafEtale B (exampleScheme k) hS _
      (presheaf_etale_id B (exampleScheme k) hS _)
  · rw [Subfunctor.preimage_id]
    exact schemeTheoreticClosure_eq_top k B hS

end Counterexample0833

/-- **The scheme-theoretic closure of an open subspace being everything does not make it
scheme-theoretically dense, and so the literal reading of condition (2) of Stacks 0833 does not
imply condition (1).** There are a big fppf site `B`, a scheme `S` in it, an algebraic space `X`
over `S` and an open subspace `U ⊆ X` admitting a surjective étale morphism `φ : V ⟶ X` from a
scheme over which the scheme-theoretic closure of `U ×_X V` is all of `V`, while `U` is not
scheme-theoretically dense in `X` in the sense of Stacks 0834. -/
theorem exists_schemeTheoreticClosure_eq_top_not_isSchemeTheoreticallyDense
    (k : Type u) [Field k] :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U : Subfunctor X),
      IsAlgebraicSpace B S hS X ∧ IsOpenSubspace B S hS U ∧
        (∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X),
            IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
              schemeTheoreticClosure B S hS (U.preimage φ) = ⊤) ∧
        ¬ IsSchemeTheoreticallyDense B S hS U := by
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (exampleScheme k)
  exact ⟨B, _, hS, _, _, isAlgebraicSpace_yoneda B (exampleScheme k) hS _,
    Counterexample0833.isOpenSubspace_openSubspace k B hS,
    (Counterexample0833.exists_etale_chart_not_isSchemeTheoreticallyDense k B hS).1,
    (Counterexample0833.exists_etale_chart_not_isSchemeTheoreticallyDense k B hS).2⟩

end Space

end AlgebraicGeometry

end
