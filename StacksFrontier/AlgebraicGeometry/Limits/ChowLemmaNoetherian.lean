module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Gluing
import StacksFrontier.AlgebraicGeometry.ChowNoetherianBase.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main

/-!
# Chow's lemma over a Noetherian base

Chow's lemma over a Noetherian base says that a separated morphism of finite type
`f : X ⟶ S` with `S` Noetherian admits a proper surjective `π : Y ⟶ X` together with an
immersion `Y ⟶ ℙⁿ_S` over `S`, and that `π` may be chosen to be an isomorphism above a dense
open subscheme of `X`. The last clause is what distinguishes this statement from the conclusion
`AlgebraicGeometry.HasChowModification` recorded for the quasi-compact quasi-separated case.

The geometric construction is carried out here in full. It is reduced to one named condition,
`AlgebraicGeometry.AffineImmersionIntoProjectiveSpace`: that every affine scheme locally of
finite type over `S` admits an immersion into some projective space over `S`, over `S`. That
condition is the one input the repository cannot yet supply over a general base; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.AffineImmersionIntoProjectiveSpace`: the condition on the base that every
  affine scheme locally of finite type over it immerses into a projective space over it.
* `AlgebraicGeometry.HasChowModificationIsoOnDenseOpen`: the conclusion of Chow's lemma over a
  Noetherian base, with the dense open over which the modification is an isomorphism.

## Main results

* `AlgebraicGeometry.HasChowModificationIsoOnDenseOpen.hasChowModification`: the conclusion
  above implies `AlgebraicGeometry.HasChowModification`, so no second notion of Chow
  modification is introduced.
* `AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_affineImmersion`: **Chow's lemma over
  a Noetherian base**, from `AffineImmersionIntoProjectiveSpace`.
* `AlgebraicGeometry.affineImmersionIntoProjectiveSpace_of_immersionTwistGap`: that condition
  follows from `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, the gap Tag 01VS already
  carries here, so it is not a new assumption.
* `AlgebraicGeometry.exists_projectiveFactorProduct`: a nonempty finite fibre product of
  projective spaces over `S` closed-immerses into a single projective space over `S`, by
  iterating the Segre embedding of Tag 01WD.

## Implementation notes

Finite type is expressed, as elsewhere in this development, by `LocallyOfFiniteType` together
with `QuasiCompact`.

`AffineImmersionIntoProjectiveSpace` is the only input left. It is the sole point at which the
source of Chow's lemma appeals to the theory of ample invertible sheaves: an affine scheme has
ample structure sheaf (`Stacks.Ample.isAmple_unitModule_of_isAffine`), and high powers of an
ample invertible sheaf are induced by an immersion into projective space. The second step is
itself not yet available unconditionally — it is
`Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple`, which carries
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` as a hypothesis — so routing this file
through ampleness would only move the hypothesis, not discharge it. The condition is therefore
named for what Chow's lemma actually uses, which is weaker: nothing about sheaves, and only the
affine case. That it really is weaker, and in particular that it is not a new assumption, is
`AlgebraicGeometry.affineImmersionIntoProjectiveSpace_of_immersionTwistGap`: the condition
follows from the gap Tag 01VS already carries in this repository.

Over an **affine** base the condition is the classical statement that a finite-type algebra is a
quotient of a polynomial algebra, so that `Spec A` closed-immerses into `𝔸ⁿ_S ⊆ ℙⁿ_S`. That is
also the only case [Stacks, Tag 02O5] consumes, since
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase` reduces it
to an affine base. That case is discharged in
`StacksFrontier/AlgebraicGeometry/Limits/ChowLemmaAffineBase.lean`, by
`AlgebraicGeometry.affineImmersionIntoProjectiveSpace_of_isAffine`.

The finite fibre products of projective spaces are indexed by a `List`, so that the Segre
embedding can be iterated by induction, and the product is produced **existentially** rather
than by a recursive definition: a recursive definition of the product would have to be unfolded
at every use, and under the transparency rules of Lean 4.33 that unfolding is not available to
`rw` or to instance search.

The properness of `ℙⁿ_S ⟶ S` used throughout is `AlgebraicGeometry.isProper_projectiveSpaceOver`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [EGA II, Theorem 5.6.1(a)]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The condition on a base scheme `S` that every affine scheme locally of finite type over `S`
admits an immersion into some projective space over `S`, lying over `S`.

This is the one input to Chow's lemma over a Noetherian base that the repository cannot yet
supply over a general base; see the implementation notes of this file. -/
def AffineImmersionIntoProjectiveSpace (S : Scheme.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ S), IsAffine Y → LocallyOfFiniteType g →
    ∃ (n : ℕ) (i : Y ⟶ projectiveSpaceOver n S),
      IsImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = g

/-- The conclusion of **Chow's lemma over a Noetherian base**: a proper surjective `π : Y ⟶ X`
and an immersion `i : Y ⟶ ℙⁿ_S` making the triangle over `S` commute, with `π` an isomorphism
above a dense open subscheme of `X`.

This strengthens `AlgebraicGeometry.HasChowModification` by the last clause. -/
def HasChowModificationIsoOnDenseOpen {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (Y : Scheme.{u}) (π : Y ⟶ X) (i : Y ⟶ projectiveSpaceOver n S) (U : X.Opens),
    IsProper π ∧ Surjective π ∧ IsImmersion i ∧
      π ≫ f = i ≫ (projectiveSpaceOver n S ↘ S) ∧
      Dense (U : Set X) ∧ IsIso (π ∣_ U)

/-- Chow's lemma over a Noetherian base implies the conclusion of Chow's lemma recorded for the
quasi-compact quasi-separated case: forget the dense open. -/
theorem HasChowModificationIsoOnDenseOpen.hasChowModification {X S : Scheme.{u}} {f : X ⟶ S}
    (h : HasChowModificationIsoOnDenseOpen f) : HasChowModification f := by
  obtain ⟨n, Y, π, i, -, hproper, hsurj, himm, hcomm, -, -⟩ := h
  exact ⟨n, Y, π, i, hproper, hsurj, himm, hcomm⟩

/-- **The affine-chart condition follows from the gap of Tag 01VS.** An affine scheme has ample
structure sheaf (`Stacks.Ample.isAmple_unitModule_of_isAffine`), so the conclusion of Tag 01VS
for the structure sheaf gives, at any sufficiently high tensor power, an immersion into a
projective space over the base lying over the structure morphism.

This is the route the source of Chow's lemma takes, and it is recorded so that
`AlgebraicGeometry.AffineImmersionIntoProjectiveSpace` is visibly no stronger than the condition
the repository already tracks for Tag 01VS. It is not a discharge of either: the hypothesis here
is `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, which is itself undischarged. -/
theorem affineImmersionIntoProjectiveSpace_of_immersionTwistGap (S : Scheme.{u})
    (h : ∀ (Y : Scheme.{u}) (g : Y ⟶ S), IsAffine Y →
      Stacks.AmpleProjectiveImmersion.ImmersionTwistGap g (Stacks.Ample.unitModule Y)
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule Y (Stacks.Ample.unitModule Y))) :
    AffineImmersionIntoProjectiveSpace S := by
  intro Y g hY hg
  have : IsAffine Y := hY
  have : LocallyOfFiniteType g := hg
  obtain ⟨d₀, hd₀, hd⟩ :=
    Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple g
      (Stacks.Ample.unitModule Y) (Stacks.Ample.isAmple_unitModule_of_isAffine Y) (h Y g hY)
  obtain ⟨n, i, hi, hcomm, -⟩ := hd d₀ le_rfl
  exact ⟨n, i, hi, hcomm⟩

/-! ### Finite fibre products of projective spaces over the base -/

/-- One projective factor of the finite fibre product used in Chow's lemma: an immersion of `X`
into a projective space over `S`, lying over `f`.

The projective space is the `AlgebraicGeometry.projectiveSpaceOver` model.
`AlgebraicGeometry.ProjectiveFactor` is the same notion over the
`AlgebraicGeometry.ProjectiveSpace` model; the two models are definitionally equal but carry
distinct `CanonicallyOver` instances, so `↘ S` is a different morphism in each and the two
structures are not the same type. -/
structure ProjectiveSpaceOverFactor {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the projective space. -/
  n : ℕ
  /-- The immersion into projective space. -/
  map : X ⟶ projectiveSpaceOver n S
  /-- The map is an immersion. -/
  isImmersion : IsImmersion map
  /-- The immersion lies over `f`. -/
  commutes : map ≫ (projectiveSpaceOver n S ↘ S) = f

/-- **The fibre product of a projective space over `S` with a scheme projective over `S` is
projective over `S`.** This is one step of the iterated Segre embedding of Tag 01WD. -/
theorem exists_isClosedImmersion_pullback_projectiveSpaceOver {S : Scheme.{u}} (n N : ℕ)
    {P : Scheme.{u}} (q : P ⟶ S) (e : P ⟶ projectiveSpaceOver N S) [IsClosedImmersion e]
    (heq : e ≫ (projectiveSpaceOver N S ↘ S) = q) :
    ∃ (M : ℕ) (d : pullback (projectiveSpaceOver n S ↘ S) q ⟶ projectiveSpaceOver M S),
      IsClosedImmersion d ∧
        d ≫ (projectiveSpaceOver M S ↘ S) =
          pullback.fst (projectiveSpaceOver n S ↘ S) q ≫ (projectiveSpaceOver n S ↘ S) := by
  obtain ⟨sg, hsg, hsgbase⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n N S
  have := hsg
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    (inferInstance :
      MorphismProperty.IsMultiplicative @IsClosedImmersion).toIsStableUnderComposition
  have hk : IsClosedImmersion (pullback.map (projectiveSpaceOver n S ↘ S) q
      (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver N S ↘ S) (𝟙 _) e (𝟙 _)
      (by simp) heq.symm) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance ‹_› (by simp) heq.symm
  have := hk
  refine ⟨n * N + n + N, pullback.map (projectiveSpaceOver n S ↘ S) q
    (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver N S ↘ S) (𝟙 _) e (𝟙 _)
    (by simp) heq.symm ≫ sg, inferInstance, ?_⟩
  rw [Category.assoc, hsgbase, pullback.lift_fst_assoc, Category.assoc, Category.id_comp]

/-- **The finite fibre product of a nonempty list of projective factors.** There is a scheme
`P` over `S` which is projective over `S`, carries an immersion from `X` over `f`, and carries a
projection to the projective space of each factor compatible with that immersion.

This is the whole use Chow's lemma makes of finite fibre products of projective spaces: the
scheme itself is produced existentially, so the recursion that builds it never has to be
unfolded. -/
theorem exists_projectiveFactorProduct {X S : Scheme.{u}} {f : X ⟶ S}
    (l : List (ProjectiveSpaceOverFactor f)) (hne : l ≠ []) :
    ∃ (N : ℕ) (P : Scheme.{u}) (q : P ⟶ S) (a : X ⟶ P) (e : P ⟶ projectiveSpaceOver N S),
      IsImmersion a ∧ a ≫ q = f ∧ IsClosedImmersion e ∧
        e ≫ (projectiveSpaceOver N S ↘ S) = q ∧
        ∀ b ∈ l, ∃ r : P ⟶ projectiveSpaceOver b.n S,
          r ≫ (projectiveSpaceOver b.n S ↘ S) = q ∧ a ≫ r = b.map := by
  induction l with
  | nil => simp at hne
  | cons a rest ih =>
      cases rest with
      | nil =>
          refine ⟨a.n, projectiveSpaceOver a.n S, projectiveSpaceOver a.n S ↘ S, a.map,
            𝟙 (projectiveSpaceOver a.n S), a.isImmersion, a.commutes, inferInstance,
            Category.id_comp _, ?_⟩
          intro b hb
          obtain rfl : b = a := by simpa using hb
          exact ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
      | cons c tail =>
          obtain ⟨N, P, q, a', e, ha', ha'q, he, heq, hproj⟩ := ih (by simp)
          have := a.isImmersion
          have := he
          have hcond : a.map ≫ (projectiveSpaceOver a.n S ↘ S) = a' ≫ q :=
            a.commutes.trans ha'q.symm
          have hgfst : pullback.lift a.map a' hcond ≫
              pullback.fst (projectiveSpaceOver a.n S ↘ S) q = a.map :=
            pullback.lift_fst _ _ _
          have hgsnd : pullback.lift a.map a' hcond ≫
              pullback.snd (projectiveSpaceOver a.n S ↘ S) q = a' :=
            pullback.lift_snd _ _ _
          have himm : IsImmersion (pullback.lift a.map a' hcond ≫
              pullback.fst (projectiveSpaceOver a.n S ↘ S) q) := by
            rw [hgfst]; exact a.isImmersion
          have hgimm : IsImmersion (pullback.lift a.map a' hcond) :=
            IsImmersion.of_comp _ (pullback.fst (projectiveSpaceOver a.n S ↘ S) q)
          obtain ⟨M, d, hd, hdbase⟩ :=
            exists_isClosedImmersion_pullback_projectiveSpaceOver a.n N q e heq
          refine ⟨M, pullback (projectiveSpaceOver a.n S ↘ S) q,
            pullback.fst (projectiveSpaceOver a.n S ↘ S) q ≫ (projectiveSpaceOver a.n S ↘ S),
            pullback.lift a.map a' hcond, d, hgimm, ?_, hd, hdbase, ?_⟩
          · rw [← Category.assoc, hgfst]; exact a.commutes
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ⟨pullback.fst (projectiveSpaceOver b.n S ↘ S) q, rfl, hgfst⟩
            · obtain ⟨r, hrbase, hra⟩ := hproj b hb
              refine ⟨pullback.snd (projectiveSpaceOver a.n S ↘ S) q ≫ r, ?_, ?_⟩
              · rw [Category.assoc, hrbase]
                exact pullback.condition.symm
              · rw [← Category.assoc, hgsnd]
                exact hra

/-! ### Scheme-theoretic dominance of the dense charts -/

/-- **The scheme-theoretic image of a quasi-compact immersion is dominated by it**, in the
scheme-theoretic sense: Tag 01RG makes the open subscheme `h.toImage.opensRange` of the image
scheme-theoretically dense, and the inclusion of a scheme-theoretically dense open subscheme is
scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_toImage_of_isImmersion {U Z : Scheme.{u}} (a : U ⟶ Z)
    [IsImmersion a] [QuasiCompact a] : IsSchemeTheoreticallyDominant a.toImage := by
  have hopen : IsOpenImmersion a.toImage := isOpenImmersion_toImage a (.inl inferInstance)
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense a.toImage.opensRange :=
    isSchemeTheoreticallyDense_toImage a (.inl inferInstance)
  have hm : Mono a.toImage.opensRange.ι.c :=
    (isSchemeTheoreticallyDense_opensRange_iff_mono a.toImage.opensRange.ι).mp
      (by simpa only [Scheme.Opens.opensRange_ι] using hdense)
  have h : IsSchemeTheoreticallyDominant a.toImage.opensRange.ι := by
    refine ⟨le_bot_iff.mp fun V ↦
      (a.toImage.opensRange.ι.ideal_ker_le V).trans (le_of_eq ?_)⟩
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
        ((NatTrans.mono_iff_mono_app _).mp hm (Opposite.op V.1)))
  refine ⟨?_⟩
  rw [← a.toImage.isoOpensRange_hom_ι, Scheme.Hom.ker_comp_of_isIso]
  exact h.ker_eq_bot

/-! ### Chow's lemma over a Noetherian base -/

/-- **Chow's lemma over a Noetherian base.** A separated morphism of finite type `f : X ⟶ S`
with `S` Noetherian admits a proper surjective `π : Y ⟶ X` and an immersion `Y ⟶ ℙⁿ_S` over
`S`, with `π` an isomorphism above a dense open subscheme of `X`.

The dense open is the intersection of a finite affine open cover of `X` all of whose members
contain every generic point (`exists_finite_dense_affine_open_cover`); each member immerses into
a projective space over `S` by the hypothesis, the fibre product of those projective spaces is
again projective over `S` (`exists_projectiveFactorProduct`), and the scheme-theoretic image of
the dense open in it carries proper charts over the members of the cover
(`Stacks.AlgebraicGeometry.ChowNoetherianBase.exists_chart_of_image`) which glue
(`exists_modification_of_dense_charts`).

This is Stacks Tag 0200 with its one missing input, `AffineImmersionIntoProjectiveSpace`, taken
as a hypothesis; no `@[stacks 0200]` attribute is attached for that reason. -/
theorem hasChowModificationIsoOnDenseOpen_of_affineImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : AffineImmersionIntoProjectiveSpace S) : HasChowModificationIsoOnDenseOpen f := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  obtain ⟨F, U, hAffine, hcover, hSubset, hdense⟩ :=
    exists_finite_dense_affine_open_cover (X := X)
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  by_cases hF : F.Nonempty
  · obtain ⟨V₀, hV₀⟩ := hF
    have hne : Nonempty {V : X.Opens // V ∈ F} := ⟨⟨V₀, hV₀⟩⟩
    have hnoe : ∀ V : {V : X.Opens // V ∈ F}, NoetherianSpace V.val.toScheme :=
      fun V => V.val.ι.isOpenEmbedding.isInducing.noetherianSpace
    have hcharts (V : {V : X.Opens // V ∈ F}) :
        ∃ (n : ℕ) (i : V.val.toScheme ⟶ projectiveSpaceOver n S),
          IsImmersion i ∧ i ≫ (projectiveSpaceOver n S ↘ S) = V.val.ι ≫ f := by
      have : IsAffine V.val.toScheme := hAffine V.val V.property
      exact h V.val.toScheme (V.val.ι ≫ f) inferInstance inferInstance
    choose n j hj hcomm using hcharts
    have hjimm : ∀ V, IsImmersion (j V) := hj
    let A (V : {V : X.Opens // V ∈ F}) : ProjectiveSpaceOverFactor (U.ι ≫ f) :=
      { n := n V
        map := X.homOfLE (hSubset V.val V.property) ≫ j V
        isImmersion := inferInstance
        commutes := by rw [Category.assoc, hcomm, Scheme.homOfLE_ι_assoc] }
    let l := F.attach.toList.map A
    have hmem (V : {V : X.Opens // V ∈ F}) : A V ∈ l :=
      List.mem_map.mpr ⟨V, Finset.mem_toList.mpr (F.mem_attach V), rfl⟩
    have hl : l ≠ [] := by
      intro he
      have := hmem ⟨V₀, hV₀⟩
      simp [he] at this
    obtain ⟨N, P, q, a, e, haimm, haq, he, heq, hproj⟩ := exists_projectiveFactorProduct l hl
    have := haimm
    have := he
    have hPproper : IsProper (projectiveSpaceOver N S ↘ S) := isProper_projectiveSpaceOver N S
    have hqproper : IsProper q := by rw [← heq]; infer_instance
    have hadom : IsSchemeTheoreticallyDominant a.toImage :=
      isSchemeTheoreticallyDominant_toImage_of_isImmersion a
    have hlocal (V : {V : X.Opens // V ∈ F}) :
        ∃ (W : Scheme.{u}) (k : W ⟶ a.image) (p : W ⟶ V.val.toScheme) (s : U.toScheme ⟶ W),
          IsOpenImmersion k ∧ IsProper p ∧ s ≫ k = a.toImage ∧
            s ≫ p = X.homOfLE (hSubset V.val V.property) ∧
            k ≫ a.imageι ≫ q = p ≫ V.val.ι ≫ f := by
      obtain ⟨r, hrbase, hramap⟩ := hproj (A V) (hmem V)
      exact Stacks.AlgebraicGeometry.ChowNoetherianBase.exists_chart_of_image f q U V.val
        (hSubset V.val V.property) a (n V) (j V) (hcomm V) r hrbase hramap
    choose W k p s hk hp hsk hsp hkbase using hlocal
    have hkopen : ∀ V, IsOpenImmersion (k V) := hk
    have hpproper : ∀ V, IsProper (p V) := hp
    obtain ⟨Y, i, π, t, hi, hπ, hiq, hti, htπ, hiso⟩ :=
      exists_modification_of_dense_charts f (a.imageι ≫ q) U a.toImage
        (fun V : {V : X.Opens // V ∈ F} => V.val)
        (fun x => by
          obtain ⟨V, hV, hxV⟩ := hcover x
          exact ⟨⟨V, hV⟩, hxV⟩)
        (fun V => hSubset V.val V.property) W k p s hsk hsp hkbase
    have := hi
    have := hπ
    refine ⟨N, Y, π, i ≫ a.imageι ≫ e, U, hπ,
      Stacks.AlgebraicGeometry.ChowNoetherianBase.surjective_of_proper_of_dense_open
        π U t htπ hdense, inferInstance, ?_, hdense, hiso⟩
    rw [← hiq, Category.assoc, Category.assoc, heq]
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨V, hV, -⟩ := hcover x
      exact hF ⟨V, hV⟩⟩
    have : IsAffine X := inferInstance
    obtain ⟨n, i, hi, hcomm⟩ := h X f inferInstance inferInstance
    have := hi
    exact ⟨n, X, 𝟙 X, i, ⊤, inferInstance, inferInstance, hi,
      by rw [Category.id_comp, hcomm], by simp, inferInstance⟩

end AlgebraicGeometry

end
