module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Quasi-separatedness of a morphism of algebraic spaces from its representable base changes

Quasi-compactness of a morphism of algebraic spaces over `S` is the assertion that every base
change along a morphism from a quasi-compact algebraic space has quasi-compact source, so
quasi-separatedness of `f : X ⟶ Y` — quasi-compactness of its relative diagonal — is a
statement quantified over *all* quasi-compact algebraic spaces mapping to `X ×_Y X`. The
results below reduce that quantification to the representable test objects with compact total
space, and deduce from it the implication (2) ⇒ (1) of Stacks 03KM, part (3): a morphism all of
whose representable base changes are quasi-separated is quasi-separated.

## Main results

* `CategoryTheory.Limits.isPullback_diagonal_pullback_snd`: the relative diagonal of a base
  change `X ×_Y T ⟶ T` of `f : X ⟶ Y` is a base change of the relative diagonal of `f`, as an
  explicit cartesian square in any category with pullbacks.
* `AlgebraicGeometry.Space.isQuasiCompact_of_forall_isQuasiCompactSpace_pullback`: a morphism of
  presheaves is quasi-compact as soon as its base changes along morphisms from representable
  presheaves with compact total scheme have quasi-compact source.
* `AlgebraicGeometry.Space.isQuasiCompact_of_presheaf`: a representable morphism all of whose
  represented base changes are quasi-compact morphisms of schemes is quasi-compact in the sense
  of Stacks 03HE. This is the bridge from the relative morphism property
  `CategoryTheory.MorphismProperty.presheaf` to the ∀-over-quasi-compact-spaces predicate.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_forall_isQuasiSeparated_pullback_snd` is the
  implication (2) ⇒ (1) of Stacks 03KM, part (3). The resulting equivalence (1) ⇔ (2) is not
  restated here: it is
  `AlgebraicGeometry.Space.isQuasiSeparated_iff_forall_pullback` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae`, which states it for the same morphisms
  under the same hypotheses.

## Implementation notes

`AlgebraicGeometry.Space.IsQuasiCompactSpace` asks only for *some* surjective étale chart with
compact total scheme, so it is inherited along a surjective étale morphism of presheaves: that
is what makes the reduction to representable test objects possible. Given a quasi-compact
algebraic space `Z` with chart `c : yoneda.obj W ⟶ Z` and a morphism `k : Z ⟶ G`, the
comparison `(yoneda.obj W) ×_G F ⟶ Z ×_G F` is a base change of `c`, hence again surjective and
étale, and a compact chart of its source is a compact chart of its target. No fppf descent is
involved; the quantifier is narrowed, not discharged.

With that reduction, (2) ⇒ (1) needs no descent either. A test morphism
`p : yoneda.obj W ⟶ X ×_Y X` has two components `p₁, p₂ : yoneda.obj W ⟶ X` with
`p₁ ≫ f = p₂ ≫ f =: g`, so it factors as a pair of sections of the base change
`X ×_Y (yoneda.obj W) ⟶ yoneda.obj W` followed by the canonical comparison
`q : (X ×_Y W) ×_W (X ×_Y W) ⟶ X ×_Y X`. Since `yoneda.obj W` is itself a quasi-compact
algebraic space when its total scheme is compact, clause (2) at `(W, g)` applies directly to
that pair of sections, and `CategoryTheory.Limits.isPullback_diagonal_pullback_snd` identifies
the two fibre products. Clause (2) is used only at the representable test objects, and its
conclusion is used only at representable test objects: the ∀-form appears on both sides of the
implication, which is why no descent lemma is required.

What is *not* available this way is any implication into (1) from a hypothesis that is only
assumed on a subfamily of test objects: (3) ⇒ (1) would need the test object `W` above to be
reduced to an affine one, (5) ⇒ (1) would need it to be reduced along the given étale atlas,
and (6) ⇒ (1) along the given Zariski covering. Each of those is a genuine descent statement
for `AlgebraicGeometry.Space.IsQuasiCompactSpace`, not a change of quantifier. The comparison
(3) ⇔ (4) with the absolute quasi-separatedness of Stacks 03BS is independent of all of this and
runs through `CategoryTheory.OverShriek.relocalizePresheafFunctor`.

The two étale helpers come from
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC`, which is imported here:
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale` and
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`, both stating the morphism implicitly.
`AlgebraicGeometry.Space.presheaf_id_of_isIso` duplicates
`AlgebraicGeometry.presheaf_id_of_iso` of
`StacksFrontier.AlgebraicGeometry.Spaces.Category`.

## References

* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-- The relative diagonal of a base change is a base change of the relative diagonal: for
`f : X ⟶ Y` and `g : T ⟶ Y`, the square whose top edge is the projection `X ×_Y T ⟶ X`, whose
left edge is the relative diagonal of `X ×_Y T ⟶ T` and whose bottom edge is the canonical
comparison `(X ×_Y T) ×_T (X ×_Y T) ⟶ X ×_Y X` is cartesian. -/
theorem isPullback_diagonal_pullback_snd {C : Type*} [Category C] [HasPullbacks C]
    {X Y T : C} (f : X ⟶ Y) (g : T ⟶ Y) :
    IsPullback (pullback.fst f g) (pullback.diagonal (pullback.snd f g))
      (pullback.diagonal f)
      (pullback.map (pullback.snd f g) (pullback.snd f g) f f
        (pullback.fst f g) (pullback.fst f g) g pullback.condition.symm
        pullback.condition.symm) := by
  set q := pullback.map (pullback.snd f g) (pullback.snd f g) f f
    (pullback.fst f g) (pullback.fst f g) g pullback.condition.symm
    pullback.condition.symm with hq
  have hcomm : (pullback.fst f g) ≫ pullback.diagonal f =
      pullback.diagonal (pullback.snd f g) ≫ q := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [hq, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
        pullback.lift_fst, pullback.lift_snd,
        pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc, Category.comp_id]
  have k₁ : ∀ s : PullbackCone (pullback.diagonal f) q,
      s.fst = s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫
        pullback.fst f g := fun s => by
    have h := s.condition =≫ pullback.fst f f
    simpa only [hq, Category.assoc, pullback.diagonal_fst, pullback.diagonal_fst_assoc,
      pullback.lift_fst, Category.comp_id] using h
  have k₂ : ∀ s : PullbackCone (pullback.diagonal f) q,
      s.fst = s.snd ≫ pullback.snd (pullback.snd f g) (pullback.snd f g) ≫
        pullback.fst f g := fun s => by
    have h := s.condition =≫ pullback.snd f f
    simpa only [hq, Category.assoc, pullback.diagonal_snd, pullback.diagonal_snd_assoc,
      pullback.lift_snd, Category.comp_id] using h
  have hcond : ∀ s : PullbackCone (pullback.diagonal f) q,
      s.fst ≫ f = (s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫
        pullback.snd f g) ≫ g := fun s => by
    rw [k₁ s]
    simp only [Category.assoc, pullback.condition]
    rw [pullback.condition_assoc]
  have hfst : ∀ s : PullbackCone (pullback.diagonal f) q,
      pullback.lift s.fst (s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫
        pullback.snd f g) (hcond s) =
      s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) := fun s => by
    refine pullback.hom_ext ?_ ?_
    · simpa only [pullback.lift_fst, Category.assoc] using k₁ s
    · simp only [pullback.lift_snd, Category.assoc]
  have hfs : ∀ s : PullbackCone (pullback.diagonal f) q,
      s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) =
      s.snd ≫ pullback.snd (pullback.snd f g) (pullback.snd f g) := fun s => by
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc] using (k₁ s).symm.trans (k₂ s)
    · simp only [Category.assoc, pullback.condition]
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s => pullback.lift s.fst
      (s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.snd f g)
      (hcond s)) (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · exact pullback.lift_fst _ _ _
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      exact hfst s
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (hfst s).trans (hfs s)
  · have hm : m = s.snd ≫ pullback.fst (pullback.snd f g) (pullback.snd f g) := by
      rw [← hm₂]
      simp
    rw [hm, ← hfst s]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Relative properties of isomorphisms and of étale charts -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The identity of a representable presheaf on the big fppf site of `S` has every relative
property whose tested property of morphisms of the site holds for the isomorphisms: every
represented base change of an identity is an isomorphism. -/
theorem presheaf_id_of_isIso (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃V W : BigFppfOver B S hS⦄ (h : V ⟶ W), IsIso h → P h) (U : BigFppfOver B S hS) :
    P.presheaf (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  exact hP snd ‹IsIso snd›

/-- Every represented base change of the identity of a representable presheaf is surjective. -/
theorem presheaf_surjective_id (U : BigFppfOver B S hS) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (𝟙 (yoneda.obj U)) := by
  refine presheaf_id_of_isIso B S hS _ ?_ U
  intro V W h hh
  have := hh
  change Surjective ((BigFppfOver.toScheme B S hS).map h)
  infer_instance

/-! ### Quasi-compactness of a representable presheaf and of a quotient -/

/-- A representable presheaf on the big fppf site of `S` whose total scheme is compact is a
quasi-compact algebraic space: its own identity is a surjective étale chart. -/
theorem isQuasiCompactSpace_yoneda (U : BigFppfOver B S hS)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    IsQuasiCompactSpace B S hS (yoneda.obj U) :=
  ⟨U, 𝟙 (yoneda.obj U), hU, presheaf_surjective_id B S hS U,
    fun _ _ hφ ↦ by simpa using hφ⟩

/-- Quasi-compactness of an algebraic space over `S` passes along a surjective étale morphism:
a compact surjective étale chart of the source, composed with the morphism, is one of the
target. -/
theorem isQuasiCompactSpace_of_surjective_etale (f : F ⟶ G)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : IsEtale B S hS f) (hF : IsQuasiCompactSpace B S hS F) :
    IsQuasiCompactSpace B S hS G := by
  obtain ⟨U, c, hU, hcsurj, hcetale⟩ := hF
  refine ⟨U, c ≫ f, hU, ?_, isEtale_comp B S hS hcetale hetale⟩
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun _ _ hf hg ↦ ⟨hg.1.comp hf.1⟩⟩
  let _ : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (F := BigFppfOver.toScheme B S hS)
  let _ : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.comp_mem P.presheaf c f hcsurj hsurj

/-! ### Reduction of quasi-compactness to compact representable test objects -/

/-- **Stacks 03HE, reduced to representable test objects.** A morphism of presheaves on the big
fppf site of `S` is quasi-compact as soon as its base change along every morphism from a
representable presheaf with compact total scheme has quasi-compact source. The quantifier over
all quasi-compact algebraic spaces is narrowed by replacing a test object by one of its compact
surjective étale charts. -/
theorem isQuasiCompact_of_forall_isQuasiCompactSpace_pullback (f : F ⟶ G)
    (h : ∀ (U : BigFppfOver B S hS),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (p : yoneda.obj U ⟶ G), IsQuasiCompactSpace B S hS (pullback p f)) :
    IsQuasiCompact B S hS f := by
  intro Z _ hZ k
  obtain ⟨U, c, hU, hcsurj, hcetale⟩ := hZ
  have hw : (pullback.fst (c ≫ k) f ≫ c) ≫ k = pullback.snd (c ≫ k) f ≫ f := by
    rw [Category.assoc]
    exact pullback.condition
  set m := pullback.lift (pullback.fst (c ≫ k) f ≫ c) (pullback.snd (c ≫ k) f) hw with hm
  have hmfst : m ≫ pullback.fst k f = pullback.fst (c ≫ k) f ≫ c := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd k f = pullback.snd (c ≫ k) f := pullback.lift_snd _ _ _
  have hsq : IsPullback m (pullback.fst (c ≫ k) f) (pullback.fst k f) c := by
    refine IsPullback.of_right ?_ hmfst (IsPullback.of_hasPullback k f).flip
    rw [hmsnd]
    exact (IsPullback.of_hasPullback (c ≫ k) f).flip
  have hmsurj := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hsq.flip hcsurj
  have hmetale := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hsq.flip
      (presheaf_etale_of_isEtale B S hS hcetale)
  exact isQuasiCompactSpace_of_surjective_etale B S hS m hmsurj
    (isEtale_of_presheaf_etale B S hS hmetale) (h U hU (c ≫ k))

/-- **The bridge from the relative morphism property to Stacks 03HE.** A morphism of presheaves
on the big fppf site of `S` all of whose represented base changes are quasi-compact morphisms of
schemes is a quasi-compact morphism of algebraic spaces: its base change along a morphism from a
representable presheaf with compact total scheme is representable with compact total scheme. -/
theorem isQuasiCompact_of_presheaf (f : F ⟶ G)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    IsQuasiCompact B S hS f := by
  refine isQuasiCompact_of_forall_isQuasiCompactSpace_pullback B S hS f (fun U hU p ↦ ?_)
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hf.rep.snd p)) :=
    hf.property_snd p
  have hcompact : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (hf.rep.pullback p)) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd p))
  exact isQuasiCompactSpace_of_iso B S hS (hf.rep.isPullback p).flip.isoPullback
    (isQuasiCompactSpace_yoneda B S hS _ hcompact)

/-! ### Stacks 03KM, part (3), (2) ⇒ (1) -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KM, part (3), (2) ⇒ (1).** A morphism of algebraic spaces over `S` whose base
change along every morphism from a representable presheaf is quasi-separated is itself
quasi-separated. -/
theorem isQuasiSeparated_of_forall_isQuasiSeparated_pullback_snd (f : X ⟶ Y)
    (hf : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsQuasiSeparated B S hS (pullback.snd f g)) :
    IsQuasiSeparated B S hS f := by
  refine isQuasiCompact_of_forall_isQuasiCompactSpace_pullback B S hS (pullback.diagonal f)
    (fun U hU p ↦ ?_)
  set g := p ≫ pullback.fst f f ≫ f with hg
  have key : ∀ a : yoneda.obj U ⟶ X, a ≫ f = g → ∃ s : yoneda.obj U ⟶ pullback f g,
      s ≫ pullback.fst f g = a ∧ s ≫ pullback.snd f g = 𝟙 _ := fun a ha ↦
    ⟨pullback.lift a (𝟙 _) (by simpa using ha), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨s₁, h₁, h₁'⟩ := key (p ≫ pullback.fst f f) (by simp [hg])
  obtain ⟨s₂, h₂, h₂'⟩ := key (p ≫ pullback.snd f f) (by simp [hg, pullback.condition])
  set σ := pullback.lift s₁ s₂ (h₁'.trans h₂'.symm) with hσ
  have hq : σ ≫ pullback.map (pullback.snd f g) (pullback.snd f g) f f
      (pullback.fst f g) (pullback.fst f g) g pullback.condition.symm
      pullback.condition.symm = p := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [hσ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₁, h₂]
  have hpaste := (IsPullback.of_hasPullback σ
    (pullback.diagonal (pullback.snd f g))).flip.paste_horiz
      (isPullback_diagonal_pullback_snd f g)
  rw [hq] at hpaste
  exact isQuasiCompactSpace_of_iso B S hS hpaste.flip.isoPullback
    (hf U g (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompactSpace_yoneda B S hS U hU) σ)

end AlgebraicGeometry.Space

end
