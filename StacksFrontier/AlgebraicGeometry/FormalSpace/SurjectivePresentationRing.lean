module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriterionPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticSmall
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# McQuillan's criterion produces the presenting ring (Stacks 0AIC)

Let `X` be an affine formal algebraic space over a scheme `S` with a presentation `X = colim X_i`
by affine thickenings whose section-ring projections `lim Γ(X_j, 𝒪) → Γ(X_i, 𝒪)` are surjective —
condition (4) of **Stacks 0AIC**, the condition Stacks 0AID calls *McQuillan*. This file produces
the weakly admissible topological ring presenting `X`, which is condition (1), with no ring given
in advance.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasSomeSurjectivePresentation`:
  **Stacks 0AIC**, condition (4) implies condition (1).
* `AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasAllSurjectivePresentations`:
  **Stacks 0AIC**, condition (5) implies condition (1).

## Implementation notes

*The set-theoretic hypothesis is the source's own, stated verbatim.* Stacks 0AIC begins "Let `S`
be a scheme. Let `X` be an fppf sheaf on `(Sch/S)_fppf` **which satisfies the set theoretic
condition of Remark 0AIS**", so the `SatisfiesSetTheoreticCondition` binder carried by the two
equivalences below — and by the other registrations of this tag, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealClosedImmersionCriterion`,
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation` — is a hypothesis *of the
tag*, not a grant added by this library and not something to be discharged; removing it would
state a different lemma than Stacks 0AIC. This is unlike the clause Stacks 0AIM and Stacks 0AI7
attach to their definitions, which rides inside the predicate and is therefore owed by any tag
concluding it.

*The universe obstruction, and how it is removed.* The index of a presentation lives in
`Type (u + 1)`, one universe above the schemes, so `lim Γ(X_i, 𝒪)` — the subtype of the product
over that index cut out by compatibility — is **not** a ring of `Type u`, and the presenting ring
has to be one: its quotients are schemes of the site. The source does not see this, its index
being a set. What repairs it is that the limit only has to be approximated: by
`TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family` any commutative ring of
`Type u` surjecting compatibly onto all the stage rings has a weakly admissible completion which
*is* the limit, so it suffices to find a `Type u` ring surjecting onto every stage ring.

*Such a ring exists because a presentation has only `u`-many stages up to isomorphism over `X`.*
A stage `X_i` contributes, for every object `V` of a small model of the site, the set of morphisms
`V → X` which factor through `X_i`; that datum is a `u`-small invariant of `i`, because the site
is essentially small (`AlgebraicGeometry.essentiallySmall_bigFppfOver`) and the sheaf `X` has
`u`-small sections (`AlgebraicGeometry.FormalSpace.small_of_isAffineFormalAlgebraicSpace`, which
is the set-theoretic condition of Stacks 0AIS at work). Two stages with the same invariant each
factor through the other over `X`, so choosing one index per value of the invariant gives a
`u`-small family of stages through which every stage factors, and such a factorisation is a
thickening (`AlgebraicGeometry.FormalSpace.isThickening_of_factor_stage`), hence surjective on
sections. A polynomial ring on the sections of the chosen stages, mapped into the limit by
choosing a preimage of each generator — which is exactly what condition (4) provides — therefore
surjects onto every stage ring.

*Why condition (1) is the target.* The ring produced here is a weakly admissible completion of a
polynomial ring surjecting onto the stage rings, and it carries no structure morphism to `S`:
`AlgebraicGeometry.FormalSpace.QuotientSystem` records the structure morphisms of the *quotients*
only, and `Spec` of such a ring admits no morphism to a non-affine `S` in general. Conditions (2)
and (3) ask for none either, so nothing blocks the further arrows (4) ⟹ (2) and (4) ⟹ (3), which
compose this result with the arrow (1) ⟹ (2) of
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u v w

/-- A family indexed by a possibly large type has a `u`-small family of representatives for any
`u`-small invariant of its index: choose one index per value the invariant takes. -/
private theorem exists_small_representatives {α : Type v} [Nonempty α] {β : Type w}
    [Small.{u} β] (f : α → β) :
    ∃ (K : Type u) (κ : K → α), ∀ a : α, ∃ k : K, f (κ k) = f a :=
  ⟨Shrink.{u} β, fun b ↦ Function.invFun f ((equivShrink β).symm b), fun a ↦
    ⟨equivShrink β (f a), (Function.invFun_eq ⟨a, (Equiv.symm_apply_apply _ _).symm⟩).trans
      (Equiv.symm_apply_apply _ _)⟩⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphisms into an fppf sheaf with `u`-small sections from a represented sheaf form a
`u`-small set: by the Yoneda lemma for sheaves they are the sections over the representing
object. -/
private theorem small_hom_sheafifiedYoneda {X : FppfSheaf B S hS}
    (hsmall : FunctorToTypes.Small.{u} X.obj) (T : BigFppfOver B S hS) :
    Small.{u} ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) := by
  have _ : Small.{u} (X.obj.obj (op T)) := hsmall (op T)
  exact small_map (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))

attribute [local instance] sheaf_hasColimits

/-- The stages of a presentation of an affine formal algebraic space have a `u`-small family of
representatives through which every stage factors over `X`: the morphisms from a small model of
the site which factor through a stage form a `u`-small invariant of that stage. -/
theorem exists_small_cofinal_stages {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) {I : Type (u + 1)} [Preorder I] [Nonempty I]
    (D : I ⥤ BigAffineFppf B S hS)
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ (K : Type u) (κ : K → I), ∀ i : I, ∃ (k : K) (c : D.obj i ⟶ D.obj (κ k)),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map c) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (κ k) ≫ e.inv =
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv := by
  classical
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let E := equivSmallModel.{u} (BigFppfOver B S hS)
  let Fs := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let Tf := BigAffineFppf.inclusion B S hS
  let ι : ∀ i : I, Fs.obj (Tf.obj (D.obj i)) ⟶ X := fun i ↦ colimit.ι (D ⋙ Tf ⋙ Fs) i ≫ e.inv
  let ξ : I → ((V : SmallModel (BigFppfOver B S hS)) → Set (Fs.obj (E.inverse.obj V) ⟶ X)) :=
    fun i V ↦ {g | ∃ c : E.inverse.obj V ⟶ Tf.obj (D.obj i), Fs.map c ≫ ι i = g}
  have hsmallCod : Small.{u} ((V : SmallModel (BigFppfOver B S hS)) →
      Set (Fs.obj (E.inverse.obj V) ⟶ X)) :=
    @small_Pi _ _ (small_self _) fun V ↦ @small_set _
      (small_hom_sheafifiedYoneda B S hS (small_of_isAffineFormalAlgebraicSpace B S hS hX) _)
  obtain ⟨K, κ, hκ⟩ := @exists_small_representatives I _ _ hsmallCod ξ
  refine ⟨K, κ, fun i ↦ ?_⟩
  obtain ⟨k, hk⟩ := hκ i
  let φ : Tf.obj (D.obj i) ≅ E.inverse.obj (E.functor.obj (Tf.obj (D.obj i))) :=
    E.unitIso.app (Tf.obj (D.obj i))
  have hmem : (Fs.map φ.inv ≫ ι i) ∈ ξ i (E.functor.obj (Tf.obj (D.obj i))) := ⟨φ.inv, rfl⟩
  rw [← hk] at hmem
  obtain ⟨c', hc'⟩ := hmem
  refine ⟨k, Tf.preimage (φ.hom ≫ c'), ?_⟩
  change Fs.map (Tf.map (Tf.preimage (φ.hom ≫ c'))) ≫ ι (κ k) = ι i
  rw [Tf.map_preimage, Fs.map_comp, Category.assoc, hc', ← Category.assoc, ← Fs.map_comp,
    φ.hom_inv_id, Fs.map_id, Category.id_comp]

/-- If a stage `D i` of a presentation factors over `X` through a stage `D j`, then every
section on `D i` is determined by a section on `D j`: any compatible family of sections taking
that value on `D j` takes the given value on `D i`. -/
theorem exists_stage_section_eq_of_factor {X : FppfSheaf B S hS} {I : Type (u + 1)} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] {D : I ⥤ BigAffineFppf B S hS}
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {i j : I} (c : D.obj i ⟶ D.obj j)
    (hc : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map c) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) j ≫ e.inv =
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv)
    (y : Γ((BigAffineFppf.toScheme B S hS).obj (D.obj i), ⊤)) :
    ∃ z : Γ((BigAffineFppf.toScheme B S hS).obj (D.obj j), ⊤),
      ∀ s : (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections,
        s.1 (op j) = z → s.1 (op i) = y := by
  have _ : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map c) :=
    (isThickening_of_factor_stage B S hS X I D hD e I D hD e i j c hc).1
  have _ : IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.obj i)) := (D.obj i).property
  have _ : IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.obj j)) := (D.obj j).property
  obtain ⟨z, hz⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigAffineFppf.toScheme B S hS).map c)).2 y
  refine ⟨z, fun s hs ↦ ?_⟩
  have hkey := stageΓ_apply_eq_of_over' B S hS X I D hD e (𝟙 (D.obj i)) c (by simp) hc s
  rw [stageΓ_id_apply'] at hkey
  have h₁ : s.1 (op i) = stageΓ' B S hS c (s.1 (op j)) := hkey
  rwa [h₁, hs]

/-- **Stacks 0AIC, condition (4) implies condition (1).** An affine formal algebraic space with a
presentation by affine thickenings whose section-ring projections are surjective is presented by
a weakly admissible topological ring, namely the inverse limit of the section rings of that
presentation.

The presentation has only `u`-many stages up to isomorphism over `X`, so a polynomial ring on the
sections of a `u`-small cofinal family of stages surjects compatibly onto every stage ring; the
weakly admissible completion of that polynomial ring is the presenting ring. -/
@[stacks 0AIC "(4) implies (1)"]
theorem exists_isPresentingRing_of_hasSomeSurjectivePresentation
    {X : FppfSheaf B S hS} (hX : HasSomeSurjectivePresentation B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A), IsPresentingRing B S hS A X := by
  classical
  obtain ⟨hAFAS, I, _, _, _, D, hD, ⟨e⟩, hsurj⟩ := hX
  obtain ⟨K, κ, hfac⟩ := exists_small_cofinal_stages B S hS hAFAS D e
  let L := (sectionDiagram B S hS D ⋙ forget CommRingCat.{u}).sections
  let pr : ∀ i : I, L →+* (sectionDiagram B S hS D).obj (op i) := fun i ↦
    { toFun := fun s ↦ s.1 (op i)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let gen : Type u := Σ k : K, ((sectionDiagram B S hS D).obj (op (κ k)) : Type u)
  choose σ hσ using fun g : gen ↦ hsurj (κ g.1) g.2
  let Λ := MvPolynomial gen ℤ
  let θ : Λ →+* L := MvPolynomial.eval₂Hom (Int.castRingHom L) σ
  let Rst : I → Type u := fun i ↦ Γ((BigAffineFppf.toScheme B S hS).obj (D.obj i), ⊤)
  let τ : ∀ ⦃i j : I⦄, i ≤ j → Rst j →+* Rst i := fun {_ _} h ↦
    (((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE h))).appTop).hom
  let ρ : ∀ i : I, Λ →+* Rst i := fun i ↦ (pr i).comp θ
  have hτnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (τ h)).LocallyNilpotent := by
    intro i j h
    have _ : IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.obj j)) := (D.obj j).property
    exact locallyNilpotent_ker_appTop_of_isThickening (hD (homOfLE h))
  have hρcompat : ∀ ⦃i j : I⦄ (h : i ≤ j) (x : Λ), τ h (ρ j x) = ρ i x :=
    fun _ _ h x ↦ (θ x).2 (homOfLE h).op
  have hρsurj : ∀ i : I, Function.Surjective (ρ i) := by
    intro i y
    obtain ⟨k, c, hc⟩ := hfac i
    obtain ⟨z, hz⟩ := exists_stage_section_eq_of_factor B S hS hD e c hc y
    exact ⟨MvPolynomial.X ⟨k, z⟩, (congrArg (pr i)
      (MvPolynomial.eval₂Hom_X' (Int.castRingHom L) σ ⟨k, z⟩)).trans (hz _ (hσ ⟨k, z⟩))⟩
  obtain ⟨A, hCR, hTS, hTR, hLT, π, hWA, hπsurj, hπcompat, hπker, hπbasis⟩ :=
    TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family hτnil hρsurj hρcompat
  let P : DirectedQuotients B S hS X A I :=
    { diagram := D
      isThickening := hD
      colimitIso := e
      proj := π
      proj_surjective := hπsurj
      proj_comp := fun _ _ hle ↦ RingHom.ext (hπcompat hle)
      isWeakIdealOfDefinition_ker := hπker
      hasBasis_nhds_zero := hπbasis }
  obtain ⟨Q, ⟨eQ⟩⟩ := P.exists_quotientSystem_formalSpectrum_iso
  exact ⟨A, hCR, hTS, hTR, hLT, hWA, ⟨{ Q.weakIdealColimitPresentation with
    colimitIso := eQ ≪≫ Q.weakIdealColimitPresentation.colimitIso }⟩⟩

/-- **Stacks 0AIC, condition (5) implies condition (1).** A presentation whose section-ring
projections are all surjective exists as soon as every presentation has that property. -/
@[stacks 0AIC "(5) implies (1)"]
theorem exists_isPresentingRing_of_hasAllSurjectivePresentations
    {X : FppfSheaf B S hS} (hX : HasAllSurjectivePresentations B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A), IsPresentingRing B S hS A X :=
  exists_isPresentingRing_of_hasSomeSurjectivePresentation B S hS
    (hX.hasSomeSurjectivePresentation B S hS)

/-- **Stacks 0AIC, conditions (1), (4) and (5) are equivalent.** For an fppf sheaf satisfying the
set-theoretic condition of Stacks 0AIS, being presented by a weakly admissible topological ring
is the same as having one presentation by affine thickenings with surjective section-ring
projections, and the same as having that property for every presentation. This is the form a
consumer wants: McQuillan's condition and the existence of the presenting ring may be exchanged
freely, with no ring and no structure morphism given in advance. -/
@[stacks 0AIC "(1), (4) and (5) are equivalent"]
theorem hasSomeSurjectivePresentation_iff_exists_isPresentingRing
    {X : FppfSheaf B S hS} (hX : SatisfiesSetTheoreticCondition B S hS X) :
    HasSomeSurjectivePresentation B S hS X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A X :=
  ⟨exists_isPresentingRing_of_hasSomeSurjectivePresentation B S hS,
    fun h ↦ (hasAllSurjectivePresentations_of_exists_weaklyAdmissible B S hS hX
      h).hasSomeSurjectivePresentation B S hS⟩

/-- **Stacks 0AIC, conditions (4) and (5) are equivalent to condition (1).** The statement above
for the "every presentation" form of McQuillan's condition. -/
@[stacks 0AIC "(1), (4) and (5) are equivalent"]
theorem hasAllSurjectivePresentations_iff_exists_isPresentingRing
    {X : FppfSheaf B S hS} (hX : SatisfiesSetTheoreticCondition B S hS X) :
    HasAllSurjectivePresentations B S hS X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A X :=
  ⟨exists_isPresentingRing_of_hasAllSurjectivePresentations B S hS,
    hasAllSurjectivePresentations_of_exists_weaklyAdmissible B S hS hX⟩

end AlgebraicGeometry.FormalSpace

end
