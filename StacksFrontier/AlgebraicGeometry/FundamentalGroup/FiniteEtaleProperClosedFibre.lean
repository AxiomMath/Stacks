module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase

/-!
# The closed fibre of a proper scheme over a henselian pair meets every open set

Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be proper, with closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`.  Every point of `X` specializes into the image of `X₀`
(`AlgebraicGeometry.exists_specializes_mem_range_pullback_fst_of_isProper`), and that single
topological fact has consequences beyond the faithfulness and conservativity it was introduced
for:

* an **open** subset of `X` containing the closed fibre is the whole of `X`, because an open set
  containing a specialization of a point contains the point;
* consequently `X` is connected as soon as its closed fibre is;
* and base change to the closed fibre cannot be made easier by passing to an open neighbourhood of
  the closed fibre: the inclusion of such a neighbourhood is an isomorphism, so the restriction
  functor on finite étale covers is an equivalence and the essential-surjectivity obligation left
  open by `isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj` is the same
  over the neighbourhood as over `X`.

The last point is recorded because the Lefschetz-style results of this chapter (Tags 0ELC, 0ELD)
state restriction from an *open neighbourhood* of a closed subscheme, in the spelling
`IsOpenImmersion.lift V.ι g hV`; in the henselian-proper situation that form carries exactly the
same content as restriction from `X`, so no route through neighbourhoods can weaken the remaining
obligation of Tag 0GS2.

The statements are proved for an arbitrary morphism `g : X₀ ⟶ X` whose image receives every point
of `X` as a specialization — the same hypothesis under which
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes` and
`AlgebraicGeometry.reflectsIsomorphisms_finiteEtaleBaseChange` are stated — and then specialized to
the closed fibre of a proper scheme over a henselian pair.

## Main results

* `eq_univ_of_isOpen_of_forall_exists_specializes` — an open set containing a subset into which
  every point specializes is everything.
* `connectedSpace_of_isConnected_of_forall_exists_specializes` — such a subset being connected
  makes the whole space connected.
* `AlgebraicGeometry.opens_eq_top_of_forall_exists_specializes` and
  `AlgebraicGeometry.isIso_opens_ι_of_forall_exists_specializes` — the scheme-theoretic forms: an
  open subscheme containing the image of `g` is `⊤`, and its inclusion is an isomorphism.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_comp_isIso` — essential surjectivity of base
  change is unchanged by postcomposing the base-change morphism with an isomorphism (the
  companion of `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_comp_of_isIso`, which
  precomposes).
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_essSurj_opens` and
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isEquivalence_opens` — restriction from
  an open neighbourhood of the image of `g` transfers to `X`.
* `AlgebraicGeometry.opens_eq_top_of_isProper_of_henselianPair` and
  `AlgebraicGeometry.connectedSpace_of_isProper_of_henselianPair` — the two geometric consequences
  for the closed fibre of a proper scheme over a henselian pair.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_closedFibre_bot` — base change to the
  closed fibre of the henselian pair `(A, ⊥)` is an equivalence for every morphism to `Spec A`.
* `AlgebraicGeometry.finiteEtaleBaseChange_essSurj_of_isEquivalence_of_isProper` — the hypothesis
  of `isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj` is implied by
  Tag 0GS2 for the proper schemes finite étale over `X`, so that reduction is tight: what it
  leaves open is exactly the essential-surjectivity half of Tag 0GS2 and nothing weaker.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
-/

@[expose] public section

open CategoryTheory Limits

universe u

/-- If every point of `α` specializes into `Z`, then an open set containing `Z` is the whole of
`α`: an open set containing a specialization of a point contains the point. -/
theorem eq_univ_of_isOpen_of_forall_exists_specializes {α : Type*} [TopologicalSpace α]
    {Z U : Set α} (hZ : ∀ x : α, ∃ z ∈ Z, x ⤳ z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    U = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨z, hzZ, hz⟩ := hZ x
  exact hz.mem_open hU (hZU hzZ)

/-- If every point of `α` specializes into a connected subset `Z`, then `α` is connected.

Given a cover of `α` by two open sets, `Z` lies in one of them unless they already meet inside
`Z`; and an open set containing `Z` is everything, so it meets the other one. -/
theorem connectedSpace_of_isConnected_of_forall_exists_specializes {α : Type*}
    [TopologicalSpace α] {Z : Set α} (hZ : ∀ x : α, ∃ z ∈ Z, x ⤳ z) (hc : IsConnected Z) :
    ConnectedSpace α := by
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  have : Nonempty α := ⟨z₀⟩
  rw [connectedSpace_iff_univ]
  refine ⟨Set.univ_nonempty, fun u v hu hv huv hxu hyv => ?_⟩
  obtain ⟨x, -, hxu⟩ := hxu
  obtain ⟨y, -, hyv⟩ := hyv
  have hZuv : Z ⊆ u ∪ v := fun z _ => huv (Set.mem_univ z)
  by_cases hzu : (Z ∩ u).Nonempty
  · by_cases hzv : (Z ∩ v).Nonempty
    · obtain ⟨w, -, hwu, hwv⟩ := hc.2 u v hu hv hZuv hzu hzv
      exact ⟨w, Set.mem_univ w, hwu, hwv⟩
    · have hZu : Z ⊆ u := fun z hzZ => (hZuv hzZ).resolve_right fun h => hzv ⟨z, hzZ, h⟩
      have hu' : u = Set.univ := eq_univ_of_isOpen_of_forall_exists_specializes hZ hu hZu
      exact ⟨y, Set.mem_univ y, hu' ▸ Set.mem_univ y, hyv⟩
  · have hZv : Z ⊆ v := fun z hzZ => (hZuv hzZ).resolve_left fun h => hzu ⟨z, hzZ, h⟩
    have hv' : v = Set.univ := eq_univ_of_isOpen_of_forall_exists_specializes hZ hv hZv
    exact ⟨x, Set.mem_univ x, hxu, hv' ▸ Set.mem_univ x⟩

namespace AlgebraicGeometry

variable {X X₀ : Scheme.{u}}

/-- An open subscheme of `X` containing the image of `g : X₀ ⟶ X` is the whole of `X`, when every
point of `X` specializes into that image. -/
theorem opens_eq_top_of_forall_exists_specializes (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') (V : X.Opens)
    (hV : Set.range g.base ⊆ Set.range V.ι.base) : V = ⊤ := by
  rw [← TopologicalSpace.Opens.coe_eq_univ]
  refine eq_univ_of_isOpen_of_forall_exists_specializes hsp V.isOpen ?_
  rw [← Scheme.Opens.range_ι]
  exact hV

/-- The inclusion of an open subscheme containing the image of `g : X₀ ⟶ X` is an isomorphism,
when every point of `X` specializes into that image: it is an open immersion whose range is the
whole of `X`. -/
theorem isIso_opens_ι_of_forall_exists_specializes (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') (V : X.Opens)
    (hV : Set.range g.base ⊆ Set.range V.ι.base) : IsIso V.ι := by
  refine (isIso_iff_isOpenImmersion_and_surjective V.ι).2 ⟨inferInstance, ⟨?_⟩⟩
  rw [← Set.range_eq_univ, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.coe_eq_univ]
  exact opens_eq_top_of_forall_exists_specializes g hsp V hV

/-- **Essential surjectivity of base change is unchanged by postcomposing the base-change
morphism with an isomorphism.** This is the companion of
`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_comp_of_isIso`, which precomposes. -/
theorem essSurj_finiteEtaleBaseChange_comp_isIso {Y₁ Y₂ P : Scheme.{u}} (g : Y₁ ⟶ Y₂)
    (θ : Y₂ ⟶ P) [IsIso θ] (h : (finiteEtaleBaseChange g).EssSurj) :
    (finiteEtaleBaseChange (g ≫ θ)).EssSurj :=
  have h₁ : (finiteEtaleBaseChange θ).EssSurj := essSurj_finiteEtaleBaseChange_of_isIso θ
  have h₂ : (finiteEtaleBaseChange θ ⋙ finiteEtaleBaseChange g).EssSurj := inferInstance
  Functor.essSurj_of_iso (finiteEtaleBaseChangeComp g θ).symm

/-- **Restriction from an open neighbourhood of the image transfers to `X`.** If every point of
`X` specializes into the image of `g : X₀ ⟶ X` and `V` is an open subscheme of `X` containing that
image, then essential surjectivity of base change along the factorisation `X₀ ⟶ V` of `g` gives
essential surjectivity of base change along `g` itself.

The factorisation is `IsOpenImmersion.lift V.ι g hV`, which is the spelling in which the
Lefschetz-style statements of this chapter restrict to an open neighbourhood of a closed
subscheme. -/
theorem essSurj_finiteEtaleBaseChange_of_essSurj_opens (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') (V : X.Opens)
    (hV : Set.range g.base ⊆ Set.range V.ι.base)
    (h : (finiteEtaleBaseChange (IsOpenImmersion.lift V.ι g hV)).EssSurj) :
    (finiteEtaleBaseChange g).EssSurj := by
  have : IsIso V.ι := isIso_opens_ι_of_forall_exists_specializes g hsp V hV
  have hc := essSurj_finiteEtaleBaseChange_comp_isIso (IsOpenImmersion.lift V.ι g hV) V.ι h
  rwa [IsOpenImmersion.lift_fac] at hc

/-- The same transfer for the full equivalence: in the situation of
`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_essSurj_opens`, base change along `g` is an
equivalence as soon as base change along its factorisation through `V` is. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isEquivalence_opens (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') (V : X.Opens)
    (hV : Set.range g.base ⊆ Set.range V.ι.base)
    (h : (finiteEtaleBaseChange (IsOpenImmersion.lift V.ι g hV)).IsEquivalence) :
    (finiteEtaleBaseChange g).IsEquivalence := by
  have : IsIso V.ι := isIso_opens_ι_of_forall_exists_specializes g hsp V hV
  have hc := isEquivalence_finiteEtaleBaseChange_comp_isIso
    (IsOpenImmersion.lift V.ι g hV) V.ι h
  rwa [IsOpenImmersion.lift_fac] at hc

/-- **`X` is connected as soon as the image of `g` is**, when every point of `X` specializes into
that image. -/
theorem connectedSpace_of_forall_exists_specializes (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') [ConnectedSpace X₀] :
    ConnectedSpace X :=
  connectedSpace_of_isConnected_of_forall_exists_specializes hsp
    (isConnected_range g.base.hom.continuous)

/-! ### The closed fibre of a proper scheme over a henselian pair -/

section Henselian

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- **An open subscheme containing the closed fibre is everything.** If `(A, I)` is a henselian
pair and `X` is proper over `Spec A`, then an open subscheme of `X` containing the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is the whole of `X`. -/
theorem opens_eq_top_of_isProper_of_henselianPair (hI : HenselianPair A I) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (V : X.Opens)
    (hV : Set.range
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base
      ⊆ Set.range V.ι.base) :
    V = ⊤ :=
  opens_eq_top_of_forall_exists_specializes _
    (exists_specializes_mem_range_pullback_fst_of_isProper A hI.le_jacobson f) V hV

/-- **A proper scheme over a henselian pair with connected closed fibre is connected.** -/
theorem connectedSpace_of_isProper_of_henselianPair (hI : HenselianPair A I) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ConnectedSpace X :=
  connectedSpace_of_forall_exists_specializes _
    (exists_specializes_mem_range_pullback_fst_of_isProper A hI.le_jacobson f)

/-- **Base change to the closed fibre of the henselian pair `(A, ⊥)` is an equivalence for every
morphism to `Spec A`.** The quotient map `A ⟶ A ⧸ ⊥` is an isomorphism of rings, so the first
projection of the closed fibre is an isomorphism of schemes and
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isIso` applies; properness is not used.

This witnesses the hypothesis of
`AlgebraicGeometry.finiteEtaleBaseChange_essSurj_of_isEquivalence_of_isProper`, which is therefore
not vacuous. -/
theorem isEquivalence_finiteEtaleBaseChange_closedFibre_bot {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of A)) :
    (finiteEtaleBaseChange (pullback.fst p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)))))).IsEquivalence := by
  have heq : CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))
      = (RingEquiv.toCommRingCatIso (RingEquiv.quotientBot A).symm).hom := by
    apply CommRingCat.hom_ext
    ext a
    rfl
  have hq : IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)))) := by
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))) := by
      rw [heq]; exact Iso.isIso_hom _
    infer_instance
  have : IsIso (pullback.fst p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))))) :=
    (MorphismProperty.isomorphisms Scheme).pullback_fst _ _ hq
  exact isEquivalence_finiteEtaleBaseChange_of_isIso _

/-- **The reduction of Tag 0GS2 to essential surjectivity is tight.** If base change to the closed
fibre is an equivalence for every scheme proper over `Spec A` — which is the conclusion of Tag
0GS2 — then the hypothesis of
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`
holds, because a scheme finite étale over a proper `X` is itself proper over `Spec A`
(`AlgebraicGeometry.isProper_comp_of_finiteEtaleOver`).

So what that reduction leaves open is exactly the essential-surjectivity half of Tag 0GS2 for the
proper schemes finite étale over `X`, and nothing weaker than it. -/
theorem finiteEtaleBaseChange_essSurj_of_isEquivalence_of_isProper
    (h : ∀ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A)), IsProper p →
      (finiteEtaleBaseChange
        (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (P : FiniteEtaleOver X) :
    (finiteEtaleBaseChange
      (pullback.fst (P.hom ≫ f)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).EssSurj :=
  (h P.left (P.hom ≫ f) (isProper_comp_of_finiteEtaleOver f P)).essSurj

end Henselian

end AlgebraicGeometry

end
