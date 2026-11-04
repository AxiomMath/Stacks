module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Transformations representable by algebraic spaces (Stacks 02YS)

Let `S` be a scheme contained in a big fppf site `B`. A transformation `a : F ⟶ G` of presheaves
of sets on the big fppf site of `S` is *representable by algebraic spaces* (Stacks 02YQ) when
every base change of it along a morphism from a representable presheaf is an algebraic space over
`S`. This file proves the three facts about such a transformation that say it behaves like a
representable one: its relative diagonal is representable, its source is a sheaf as soon as its
target is, and its source is an algebraic space as soon as its target is.

All three mirror statements already in the library for transformations representable *by schemes*
— `AlgebraicGeometry.relativelyRepresentable_pullback_diagonal` (Stacks 05L9),
`AlgebraicGeometry.isSheaf_of_relativelyRepresentable` (Stacks 02WD) and
`AlgebraicGeometry.Space.isAlgebraicSpace_of_relativelyRepresentable` (Stacks 02WY) — and the
`IsAlgebraicSpace` structure is verified clause by clause exactly as the last of those does it.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces`: **Stacks 02YS**.
* `relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 05LA** strengthened to representability by schemes, which is what 02YS needs. Untagged;
  the 05LA citation is on `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diagonal`.

## Implementation notes

Stacks 02YS is Chapter 80 (Bootstrap); it is proved here because three results of Chapters
81–111 depend on it — Stacks 0300, the implication (1) ⇒ (7) of Stacks 045G, and the descent
half of Stacks 04XD. Nothing new is *defined*: every notion used is
already in the library, namely `AlgebraicGeometry.IsAlgebraicSpace`,
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces` and
`CategoryTheory.Functor.relativelyRepresentable`.

**The relative diagonal is representable by schemes, not merely by algebraic spaces.** Stacks
05LA concludes only that `Δ_{F/G}` is representable by algebraic spaces, which is all it needs
there; the proof in fact gives representability by schemes, because the fibre of `Δ_{F/G}` over a
scheme-valued point `(ξ₁, ξ₂)` of `F ×_G F` is the locus in that scheme where two sections of the
algebraic space `V = h_U ×_G F` over `U` agree, and that locus is a pullback of the diagonal of
`V`, which is representable by schemes by the second clause of `IsAlgebraicSpace`. The stronger
form is what Stacks 02YS needs, since the diagonal clause it has to verify asks for
representability by schemes.

**The ordering obstruction in the source does not apply here.** Stacks remarks that the proof of
02YS "is actually slightly tricky", because it "cannot use the argument of the proof of Spaces,
Lemma 02WY" — one does not yet know there that a composition of transformations representable by
algebraic spaces is representable by algebraic spaces. That is an ordering constraint on the
source text, not a mathematical one: here `CategoryTheory.Functor.relativelyRepresentable` is a
`CategoryTheory.MorphismProperty` carrying Mathlib's `IsMultiplicative`,
`IsStableUnderBaseChange` and `RespectsIso` instances, and `MorphismProperty.presheaf` carries
`MorphismProperty.relative_isStableUnderComposition`, so the composition and diagonal steps the
02WY argument takes are available before 02YS rather than after it. Consequently 02YS is proved
below by the 02WY argument, with no appeal to Stacks 0BGQ and hence none to the quotient of an
étale equivalence relation.

**The sheaf clause is not reproved.** It is Stacks 02YR, which is
`AlgebraicGeometry.Space.isSheaf_of_isRepresentableByAlgebraicSpaces` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces`, and is applied
here rather than restated.

## References

* [Stacks Project, Tag 05LA](https://stacks.math.columbia.edu/tag/05LA)
* [Stacks Project, Tag 02YR](https://stacks.math.columbia.edu/tag/02YR)
* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A strengthening of **Stacks 05LA**: the relative diagonal of a transformation of presheaves
on the big fppf site of `S` which is representable by algebraic spaces is representable **by
schemes**, where the source concludes only representability by algebraic spaces.

The fibre of `Δ_{F/G}` over a scheme-valued point `ξ` of `F ×_G F` with components `α`, `β` is
the locus in that scheme where `α` and `β` agree. Both factor through the algebraic space
`V = h_U ×_G F` as sections `j₁`, `j₂` of its structural morphism, and that locus is the pullback
of the diagonal of `V` along `(j₁, j₂)`, hence a scheme.

Deliberately untagged: the `@[stacks 05LA]` citation belongs on
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diagonal`, which is the source's own
statement. This stronger form is kept because
`AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces` (Stacks 02YS) needs the
by-schemes conclusion to discharge the diagonal clause of `AlgebraicGeometry.IsAlgebraicSpace`,
and the by-algebraic-spaces form does not suffice there. -/
theorem relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpaces
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : Space.IsRepresentableByAlgebraicSpaces B S hS a) :
    yoneda.relativelyRepresentable (pullback.diagonal a) := by
  classical
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro U ξ₀
  set ξ : yoneda.obj U ⟶ pullback a a := yonedaEquiv.symm ξ₀
  set α : yoneda.obj U ⟶ F := ξ ≫ pullback.fst a a with hα
  set β : yoneda.obj U ⟶ F := ξ ≫ pullback.snd a a with hβ
  have hαβ : α ≫ a = β ≫ a := by
    rw [hα, hβ, Category.assoc, Category.assoc, pullback.condition]
  set V := Limits.pullback (α ≫ a) a
  have hV : IsAlgebraicSpace B S hS V := ha U (α ≫ a)
  set j₁ : yoneda.obj U ⟶ V := pullback.lift (𝟙 _) α (Category.id_comp _) with hj₁
  set j₂ : yoneda.obj U ⟶ V := pullback.lift (𝟙 _) β (by rw [Category.id_comp, hαβ]) with hj₂
  have hj₁snd : j₁ ≫ pullback.snd (α ≫ a) a = α := by rw [hj₁, pullback.lift_snd]
  have hj₂snd : j₂ ≫ pullback.snd (α ≫ a) a = β := by rw [hj₂, pullback.lift_snd]
  have hj₁fst : j₁ ≫ pullback.fst (α ≫ a) a = 𝟙 _ := by rw [hj₁, pullback.lift_fst]
  have hj₂fst : j₂ ≫ pullback.fst (α ≫ a) a = 𝟙 _ := by rw [hj₂, pullback.lift_fst]
  obtain ⟨W, w, fst, hpb⟩ := hV.diagonal_representable (prod.lift j₁ j₂)
  have hcomp₁ : fst = yoneda.map w ≫ j₁ := by
    simpa [diag] using congrArg (· ≫ Limits.prod.fst) hpb.w
  have hcomp₂ : fst = yoneda.map w ≫ j₂ := by
    simpa [diag] using congrArg (· ≫ Limits.prod.snd) hpb.w
  have hwαβ : yoneda.map w ≫ α = yoneda.map w ≫ β := by
    simpa only [Category.assoc, hj₁snd, hj₂snd] using
      congrArg (· ≫ pullback.snd (α ≫ a) a) (hcomp₁.symm.trans hcomp₂)
  have hsqw : (yoneda.map w ≫ α) ≫ pullback.diagonal a = yoneda.map w ≫ ξ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hα]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hwαβ, hβ]
  have key : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t₁ : T ⟶ F) (t₂ : T ⟶ yoneda.obj U),
      t₁ ≫ pullback.diagonal a = t₂ ≫ ξ →
      t₁ = t₂ ≫ α ∧ t₂ ≫ j₁ = t₂ ≫ j₂ := by
    intro T t₁ t₂ hcond
    have h₁ : t₁ = t₂ ≫ α := by
      simpa [hα] using congrArg (· ≫ pullback.fst a a) hcond
    have h₂ : t₁ = t₂ ≫ β := by
      simpa [hβ] using congrArg (· ≫ pullback.snd a a) hcond
    refine ⟨h₁, pullback.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, hj₁fst, hj₂fst]
    · simp only [Category.assoc, hj₁snd, hj₂snd, ← h₁, h₂]
  have hsq : IsPullback (yoneda.map w ≫ α) (yoneda.map w) (pullback.diagonal a) ξ := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsqw
      (fun s => hpb.lift (s.snd ≫ j₁) s.snd ?_) (fun s => ?_) (fun s => hpb.lift_snd _ _ _) ?_)
    · obtain ⟨-, hj⟩ := key s.pt s.fst s.snd s.condition
      apply prod.hom_ext
      · simp only [Category.assoc, diag, prod.lift_fst, Category.comp_id]
      · simp only [Category.assoc, diag, prod.lift_snd, Category.comp_id, hj]
    · obtain ⟨h₁, -⟩ := key s.pt s.fst s.snd s.condition
      rw [← Category.assoc, hpb.lift_snd, h₁]
    · intro s m _ hm₂
      refine hpb.hom_ext ?_ (hm₂.trans (hpb.lift_snd _ _ _).symm)
      rw [hpb.lift_fst, hcomp₁, ← Category.assoc, hm₂]
  exact Functor.IsRepresentable.mk' (X := W)
    ((hsq.isoIsPullback F (yoneda.obj U)
      (IsPullback.of_hasPullback (pullback.diagonal a) ξ)) ≪≫
      pullbackSymmetry (pullback.diagonal a) ξ)

/-- If `w` and `f` are in the presheaf property attached to a composition-stable scheme property,
so is the composite of `w` with the base change of `f` along `a`. -/
private theorem presheaf_comp_pullback_snd {Q : MorphismProperty Scheme.{u}}
    (hQ : Q.IsStableUnderComposition) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    {U W : BigFppfOver B S hS} (f : yoneda.obj U ⟶ G) (w : yoneda.obj W ⟶ pullback f a)
    (hw : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf w)
    (hf : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (w ≫ pullback.snd f a) := by
  have := Space.inverseImage_isStableUnderComposition B S hS hQ
  have := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda) (Q.inverseImage (BigFppfOver.toScheme B S hS))
  have := MorphismProperty.relative_isStableUnderComposition
    (F := yoneda) (Q.inverseImage (BigFppfOver.toScheme B S hS))
  exact MorphismProperty.comp_mem _ _ _ hw
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f a) hf)

/-- **Stacks 02YS.** A transformation representable by algebraic spaces to an algebraic space over
`S` has an algebraic space over `S` as its source.

The three clauses of `AlgebraicGeometry.IsAlgebraicSpace` are verified as in Stacks 02WY. The
sheaf clause is Stacks 02YR. The diagonal clause is the composite
`Δ_F = Δ_{F/G} ≫ (F ×_G F ⟶ F × F)`, representable because `Δ_{F/G}` is — this is Stacks 05LA in
the strengthened form above — and because the second factor is a base change of `Δ_G`. For the
atlas clause, base-changing a scheme atlas of `G` along `a` gives a surjective étale morphism to
`F` from an *algebraic space*, and composing it with a scheme atlas of that algebraic space gives
a scheme atlas of `F`. -/
@[stacks 02YS]
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : Space.IsRepresentableByAlgebraicSpaces B S hS a)
    (hG : IsAlgebraicSpace B S hS G) :
    IsAlgebraicSpace B S hS F := by
  classical
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    yoneda.relativelyRepresentable
  have heq : ∀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, diag X =
      pullback.diagonal (terminal.from X) ≫ (prodIsoPullback X X).inv := fun X => by cat_disch
  have hGdiag : P (pullback.diagonal (terminal.from G)) := by
    exact (MorphismProperty.cancel_right_of_respectsIso (P := P)
      (pullback.diagonal (terminal.from G)) (prodIsoPullback G G).inv).mp
        (heq G ▸ hG.diagonal_representable)
  have hFdiag : P (pullback.diagonal (terminal.from F)) := by
    simpa only [MorphismProperty.diagonal_iff, terminal.comp_from] using
      (MorphismProperty.comp_mem P.diagonal a (terminal.from G)
        (relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpaces
          B S hS a ha) hGdiag)
  have hdiag : P (diag F) := by
    rw [heq F]
    exact MorphismProperty.RespectsIso.postcomp P (prodIsoPullback F F).inv _ hFdiag
  obtain ⟨U, f, hfSurjective, hfEtale⟩ := hG.exists_atlas
  obtain ⟨W, w, hwSurjective, hwEtale⟩ := (ha U f).exists_atlas
  exact ⟨Space.isSheaf_of_isRepresentableByAlgebraicSpaces B S hS a ha hG.isSheaf, hdiag,
    W, w ≫ pullback.snd f a,
    presheaf_comp_pullback_snd B S hS surjective_isStableUnderComposition.{u} a f w hwSurjective
      hfSurjective,
    presheaf_comp_pullback_snd B S hS Space.etale_isStableUnderComposition.{u} a f w hwEtale
      hfEtale⟩

end AlgebraicGeometry

end
