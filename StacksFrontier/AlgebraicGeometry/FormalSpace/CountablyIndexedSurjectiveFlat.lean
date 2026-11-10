module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Countable indexing passes to the target of a surjective flat morphism (Stacks 0AKS, forward)

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces, surjective
and flat. If `X` is countably indexed then so is `Y`.

This is the forward implication of **Stacks 0AKS**, proved by the source's own cofinality
argument. No presenting ring appears: the proof produces a *cofinal sequence of stages* of a
given presentation of `Y` and reindexes the colimit along it.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_target_of_surjective_flat`: the forward
  implication.
* `AlgebraicGeometry.FormalSpace.faithfullyFlat_of_isPullback_of_surjective_flat`: step 3 on
  its own, that a represented base change of such a morphism between affine objects of the
  site is faithfully flat on coordinate rings.

## Implementation notes

Write `X = colim_n Xₙ` for a sequential presentation (**Stacks 0AIJ**) and `Y = colim_λ Y_λ`
for a presentation by affine schemes and thickenings (**Stacks 0AI7**). The argument has four
steps.

1. Each stage `Xₙ` is an affine scheme of the site, so `Xₙ ⟶ Y` factors through some stage
   `Y_{λₙ}` of the presentation of `Y`, by **Stacks 0AIA**
   (`AlgebraicGeometry.exists_factor_through_thickening`).
2. Each `Y_λ ×_Y X` is an affine scheme of the site, by **Stacks 0AKN**
   (`…relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`), so it in turn factors
   through some stage `Xₙ` of the presentation of `X`, again by Stacks 0AIA.
3. Composing, `Y_λ ×_Y X ⟶ Y` factors through `Y_{λₙ}`; and `Y_λ ×_Y X ⟶ Y_λ` is a
   faithfully flat morphism of affine schemes, being the base change of `f` along
   `Y_λ ⟶ Y`. At a stage `Y_μ` dominating both `Y_λ` and `Y_{λₙ}` this exhibits the ideal
   cutting out `Y_{λₙ}` inside the ideal cutting out `Y_λ` *after* base change to
   `Y_λ ×_Y X`, whence before it, because a faithfully flat ring map `φ` satisfies
   `(I.map φ).comap φ = I` (`RingHom.faithfullyFlat_comap_map_eq`, Stacks 05CK). So
   `Y_λ ⟶ Y` factors through `Y_{λₙ}`.
4. Replacing `λₙ` by a monotone sequence dominating it, step 3 says the sequence of stages is
   cofinal, so `Y` is the colimit of that sequence and hence countably indexed.

Surjectivity and flatness are used *only* in step 3, and only through the morphism of affine
schemes underlying a represented base change of `f`: surjectivity on points transfers to the
scheme morphism by Stacks 03H5
(`AlgebraicGeometry.Space.surjective_of_isSurjective_yoneda_map`), flatness by reading the
every-étale-chart condition of Stacks 03MJ on identity charts, and the two together give
faithful flatness of the map of coordinate rings by
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` (Stacks 00HQ).

The cofinality step is stated as `isColimit_of_sequence_factors`, which asks only that every
colimit injection factor through a member of the sequence; it does not ask that the sequence be
cofinal in the index preorder, which the geometry does not give — the factorisation produced in
step 3 is a morphism of stages over `Y`, not an inequality of indices.

Representable flatness is taken apart into its two components rather than used through
`AlgebraicGeometry.FormalSpace.IsRepresentableFlat`, which is defined downstream of this file.

## References

* [Stacks Project, Tag 00HQ](https://stacks.math.columbia.edu/tag/00HQ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v v' w

namespace AlgebraicGeometry.FormalSpace

/-! ### A monotone sequence dominating a given one -/

/-- A sequence in a directed preorder is dominated by a monotone one. -/
private theorem exists_monotone_ge {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    (c : ℕ → I) : ∃ d : ℕ → I, Monotone d ∧ ∀ n, c n ≤ d n := by
  classical
  choose upper hleft hright using (fun i j : I => exists_ge_ge i j)
  refine ⟨fun n => Nat.rec (c 0) (fun n i => upper i (c (n + 1))) n,
    monotone_nat_of_le_succ (fun n => hleft _ _), fun n => ?_⟩
  cases n with
  | zero => exact le_rfl
  | succ n => exact hright _ _

/-! ### Cofinality of a sequence of stages -/

/-- **A sequence of stages through which every stage factors computes the colimit.** Let `c`
be a colimit cocone on `D : I ⥤ C` all of whose injections are monomorphisms, and let
`s : ℕ ⥤ I` be such that every injection `D i ⟶ c.pt` factors through `D (s n)` for some `n`.
Then the restriction of `c` to `s` is a colimit cocone.

Only the factorisation is asked for, not that `s` be cofinal in `I`: the morphism
`D i ⟶ D (s n)` need not be the image of a morphism of `I`. -/
private noncomputable def isColimit_of_sequence_factors
    {C : Type u} [Category.{v} C] {I : Type w} [Category.{v'} I]
    (D : I ⥤ C) (c : Cocone D) (hc : IsColimit c)
    (s : ℕ ⥤ I) (hm : ∀ i, Mono (c.ι.app i))
    (h : ∀ i, ∃ n, ∃ a : D.obj i ⟶ D.obj (s.obj n), a ≫ c.ι.app (s.obj n) = c.ι.app i) :
    IsColimit (c.whisker s) := by
  classical
  choose n a ha using h
  have glue {i : I} {m₁ m₂ : ℕ} (u : D.obj i ⟶ D.obj (s.obj m₁))
      (v : D.obj i ⟶ D.obj (s.obj m₂)) (huv : u ≫ c.ι.app (s.obj m₁) = v ≫ c.ι.app (s.obj m₂))
      (t : Cocone (s ⋙ D)) : u ≫ t.ι.app m₁ = v ≫ t.ι.app m₂ := by
    let := hm (s.obj (max m₁ m₂))
    let f₁ := s.map (homOfLE (le_max_left m₁ m₂))
    let f₂ := s.map (homOfLE (le_max_right m₁ m₂))
    have heq : u ≫ D.map f₁ = v ≫ D.map f₂ := by
      apply (cancel_mono (c.ι.app (s.obj (max m₁ m₂)))).1
      simpa only [Category.assoc, c.w] using huv
    calc
      u ≫ t.ι.app m₁ = u ≫ D.map f₁ ≫ t.ι.app (max m₁ m₂) := by
        rw [show D.map f₁ ≫ t.ι.app (max m₁ m₂) = t.ι.app m₁ from t.w _]
      _ = v ≫ D.map f₂ ≫ t.ι.app (max m₁ m₂) := by
        simpa only [Category.assoc] using congrArg (· ≫ t.ι.app (max m₁ m₂)) heq
      _ = v ≫ t.ι.app m₂ := by
        rw [show D.map f₂ ≫ t.ι.app (max m₁ m₂) = t.ι.app m₂ from t.w _]
  let extend (t : Cocone (s ⋙ D)) : Cocone D :=
    { pt := t.pt
      ι := { app := fun i => a i ≫ t.ι.app (n i)
             naturality := fun i j b => by
               simpa using glue (D.map b ≫ a j) (a i)
                 (by rw [Category.assoc, ha, ha, c.w]) t } }
  have hext (t : Cocone (s ⋙ D)) (j : ℕ) : (extend t).ι.app (s.obj j) = t.ι.app j := by
    simpa using glue (a (s.obj j)) (𝟙 _) (by rw [ha, Category.id_comp]) t
  refine { desc := fun t => hc.desc (extend t), fac := ?_, uniq := ?_ }
  · intro t j
    exact (hc.fac (extend t) (s.obj j)).trans (hext t j)
  · intro t m hm'
    apply hc.hom_ext
    intro i
    rw [hc.fac]
    change c.ι.app i ≫ m = a i ≫ t.ι.app (n i)
    rw [← ha i, Category.assoc]
    exact congrArg (a i ≫ ·) (hm' (n i))

/-! ### Descending a factorisation through a closed immersion -/

/-- A morphism to an affine scheme whose base change along an injection of coordinate rings
factors through a closed immersion factors through it: the ideal of the closed immersion is
carried to zero on coordinate rings after the injection, hence before it. -/
private theorem exists_factor_through_closedImmersion_of_injective
    {P A C Z : Scheme.{u}} [IsAffine Z]
    (p : P ⟶ A) (a : A ⟶ Z) (b : P ⟶ C) (c : C ⟶ Z)
    [_root_.AlgebraicGeometry.IsClosedImmersion c] (hp : Function.Injective p.appTop.hom)
    (h : p ≫ a = b ≫ c) : ∃ g : A ⟶ C, g ≫ c = a := by
  have hker : c.ker ≤ a.ker := by
    have heq : (p ≫ a).ker = a.ker := by
      rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
      congr 1
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
        RingHom.ker_comp_of_injective a.appTop.hom hp
    rw [← heq, h]
    exact Scheme.Hom.le_ker_comp b c
  exact ⟨IsClosedImmersion.lift c a hker, IsClosedImmersion.lift_fac c a hker⟩

/-- The previous lemma inside the big fppf category over `S`: the factorisation of schemes
produced there has a source and target in the site, so it is the image of a morphism of the
site, and it respects the structure morphisms because its composite with a closed immersion
over `S` does. -/
private theorem exists_factor_over_closedImmersion_of_injective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P A C Z : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (p : P ⟶ A) (a : A ⟶ Z) (b : P ⟶ C) (c : C ⟶ Z)
    (hc : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map c))
    (hp : Function.Injective
      (((BigFppfOver.toScheme B S hS).map p).appTop).hom)
    (h : p ≫ a = b ≫ c) : ∃ g : A ⟶ C, g ≫ c = a := by
  let T := BigFppfOver.toScheme B S hS
  let := hc
  obtain ⟨g, hg⟩ := exists_factor_through_closedImmersion_of_injective
    (T.map p) (T.map a) (T.map b) (T.map c) hp (by simpa using congrArg T.map h)
  let l := B.inclusion.preimage g
  have hl : l ≫ c.left = a.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    change B.inclusion.map l ≫ T.map c = T.map a
    rw [show B.inclusion.map l = g from B.inclusion.map_preimage g]
    exact hg
  exact ⟨Over.homMk l (by rw [← Over.w c, ← Category.assoc, hl]; exact Over.w a),
    Over.OverMorphism.ext hl⟩

/-! ### Faithful flatness of a represented base change -/

/-- An isomorphism out of a universe-lifted Yoneda presheaf is an étale chart of its target:
every represented base change of it is an isomorphism of the site, hence étale. This is
`AlgebraicGeometry.relative_etale_id` for an arbitrary isomorphism. -/
private theorem relative_etale_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (e : (uliftYoneda.{u + 1}).obj T ⟶ F) [IsIso e] :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) e := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) _, ?_⟩
  intro Z W g fst snd hpb
  have h1 : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have h2 : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- **A represented base change of a surjective flat morphism of fppf sheaves is faithfully
flat on coordinate rings.** Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S` which is
representable by algebraic spaces, surjective and flat, and let a cartesian square exhibit
`q : V ⟶ U` as its base change along a morphism `g` to `Y` from the sheaf represented by `U`,
with both `U` and `V` affine. Then the induced map of coordinate rings is faithfully flat.

Flatness of `q` is the every-étale-chart condition of **Stacks 03MJ** read on the comparison
isomorphism of the base change and on the identity chart of `U`; surjectivity of `q` is
surjectivity of `f` on points, transported along the base change (**Stacks 0GHR**) and then
down to the scheme morphism by **Stacks 03H5**; the two together are faithful flatness by
**Stacks 00HQ**. -/
public theorem faithfullyFlat_of_isPullback_of_surjective_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) a.hom) f.hom hrep)
    {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X} {q : V ⟶ U}
    {g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y}
    (sq : IsPullback p
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g) :
    RingHom.FaithfullyFlat (((BigFppfOver.toScheme B S hS).map q).appTop).hom := by
  let := hU
  let := hV
  let eU := sheafifiedYonedaObjIso B S hS U
  let eV := sheafifiedYonedaObjIso B S hS V
  -- flatness, from the every-étale-chart condition read on the comparison isomorphism
  have hps : IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q).hom p.hom g.hom f.hom :=
    sq.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hsq : IsPullback ((uliftYoneda.{u + 1}).map q) (eV.hom ≫ p.hom)
      (eU.hom ≫ g.hom) f.hom :=
    hps.of_iso' eV eU (Iso.refl _) (Iso.refl _)
      (sheafifiedYonedaObjIso_naturality B S hS q).symm (by simp) (by simp) (by simp)
  have hflatq : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map q) :=
    hflat U (eU.hom ≫ g.hom) V U hsq.isoPullback.hom (𝟙 ((uliftYoneda.{u + 1}).obj U)) q
      (relative_etale_of_isIso B S hS _) (relative_etale_id B S hS U)
      (by rw [Category.comp_id]; exact hsq.isoPullback_hom_fst.symm)
  -- surjectivity, transported from `f` and pushed down to the scheme morphism
  have hsurjSheaf : IsSurjective B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) :=
    IsSurjective.of_isPullback B S hS sq.flip hsurj
  have hnat : (uliftYoneda.{u + 1}).map q ≫ eU.hom = eV.hom ≫
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q).hom :=
    sheafifiedYonedaObjIso_naturality B S hS q
  have hinj : Function.Injective (Space.pointsMapULift.{u + 1} B S hS _ eU.hom) := by
    have h : Space.pointsMapULift.{u + 1} B S hS _ (inv eU.hom) ∘
        Space.pointsMapULift.{u + 1} B S hS _ eU.hom = id := by
      rw [← Space.pointsMapULift_comp, IsIso.hom_inv_id, Space.pointsMapULift_id]
    exact Function.LeftInverse.injective (congrFun h)
  have h2 : Space.IsSurjectiveULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map q) := by
    have hcomp : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _
        ((uliftYoneda.{u + 1}).map q ≫ eU.hom)) := by
      rw [hnat, Space.pointsMapULift_comp]
      exact Function.Surjective.comp hsurjSheaf
        (Space.surjective_pointsMapULift_of_isIso B S hS eV.hom)
    rw [Space.pointsMapULift_comp] at hcomp
    intro y
    obtain ⟨x, hx⟩ := hcomp (Space.pointsMapULift.{u + 1} B S hS _ eU.hom y)
    exact ⟨x, hinj hx⟩
  have hsurjq : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    Space.surjective_of_isSurjective_yoneda_map B S hS q
      ((Space.isSurjectiveULift_whiskerRight_iff B S hS (yoneda.map q)).mp h2)
  exact (AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
    ((BigFppfOver.toScheme B S hS).map q)).mp ⟨hflatq, hsurjq⟩

/-! ### Factoring an affine stage through a presentation -/

/-- **Stacks 0AIA** for a test object of the site with affine underlying scheme: a morphism to
a presented sheaf from the sheaf represented by an affine object of the site factors through a
stage of the presentation. This is
`AlgebraicGeometry.exists_factor_through_thickening` with the quasi-compact algebraic space
taken to be the presheaf represented by the object. -/
private theorem factor_affine_stage_through_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (Z : FppfSheaf B S hS)
    (e : Z ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Z) :
    ∃ i : I, ∃ k : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      k ≫ colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv = a := by
  let J := BigFppfOver.topology B S hS
  have hUobj : (Sheaf.sheafifiedYoneda J).obj U =
      (presheafToSheaf J (Type (u + 1))).obj
        (yoneda.obj U ⋙ uliftFunctor.{u + 1, u}) := by
    rw [Sheaf.sheafifiedYoneda_obj]
    rfl
  let eU := eqToIso hUobj
  obtain ⟨i, k, hk⟩ := AlgebraicGeometry.exists_factor_through_thickening
    B S hS I D hD Z e (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU) (eU.inv ≫ a)
  refine ⟨i, eU.hom ≫ k, ?_⟩
  rw [Category.assoc, congrArg (fun z => eU.hom ≫ z) hk, ← Category.assoc, eU.hom_inv_id,
    Category.id_comp]

/-! ### The forward implication of Stacks 0AKS -/

/-- **Stacks 0AKS, the forward implication.** Let `f : X ⟶ Y` be a morphism of affine formal
algebraic spaces over `S` which is representable by algebraic spaces, surjective and flat. If
`X` is countably indexed then so is `Y`.

This is the source's cofinality argument. Write `X = colim Xₙ` and `Y = colim Y_λ`. Each stage
`Xₙ ⟶ Y` factors through some `Y_{λₙ}`. Conversely each `Y_λ ×_Y X` is affine, so it factors
through some `Xₙ`, giving a morphism `Y_λ ×_Y X ⟶ Y_{λₙ}`; since `Y_λ ×_Y X ⟶ Y_λ` is
faithfully flat, the ideal cutting out `Y_{λₙ}` in a stage dominating both is contained in the
one cutting out `Y_λ`, so `Y_λ ⟶ Y` itself factors through `Y_{λₙ}`. Hence a monotone sequence
dominating the `λₙ` indexes a cofinal family of stages, and `Y` is its colimit.

The flatness hypothesis is the second component of
`AlgebraicGeometry.FormalSpace.IsRepresentableFlat`. -/
theorem isCountablyIndexed_target_of_surjective_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) a.hom) f.hom hrep)
    (hXc : IsCountablyIndexed B S hS X) :
    IsCountablyIndexed B S hS Y := by
  classical
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let H := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let inc := BigAffineFppf.inclusion B S hS
  let T := BigFppfOver.toScheme B S hS
  let FF := Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨D_X, hD_X, ⟨eX⟩⟩ := hXc
  -- lift the index of the sequential presentation of `X` into `Type (u + 1)`
  let I_X := ULift.{u + 1, 0} ℕ
  let hIndex : Monotone (ULift.down : I_X → ℕ) := fun _ _ h => h
  let eIndex := hIndex.functor
  let : Functor.Final eIndex := hIndex.final_functor_iff.mpr (fun n => ⟨ULift.up n, le_rfl⟩)
  let D_Xlift := eIndex ⋙ D_X
  have hD_Xlift : ∀ ⦃i j : I_X⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D_Xlift.map g)) :=
    fun _ _ g => hD_X (eIndex.map g)
  let Flift := D_Xlift ⋙ inc ⋙ H
  have eXlift : X ≅ colimit Flift :=
    eX ≪≫ (Functor.Final.colimitIso eIndex (D_X ⋙ inc ⋙ H)).symm
  have hY' := hY
  obtain ⟨-, I, pre, hI, hdir, D_Y, hD_Y, ⟨eY⟩⟩ := hY
  let : Preorder I := pre
  let : Nonempty I := hI
  let : IsDirected I (· ≤ ·) := hdir
  let G := D_Y ⋙ inc ⋙ H
  -- the stages of the presentation of `Y` are subobjects of `Y`
  have hGmono : ∀ i j (g : i ⟶ j), Mono (G.map g) := by
    intro i j g
    have hm : Mono ((BigAffineFppf.toScheme B S hS).map (D_Y.map g)) := by
      let := (hD_Y g).1
      infer_instance
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ T (inc.map (D_Y.map g)) hm
  have hιmono (i : I) : Mono (colimit.ι G i ≫ eY.inv) := by
    let := Sheaf.mono_colimit_ι_of_mono_transition G hGmono i
    infer_instance
  -- step 1: each stage of `X` maps into a stage of `Y`
  have hsourceStageFactor (n : ℕ) :
      ∃ i : I, ∃ k : Flift.obj (ULift.up n) ⟶ G.obj i,
        k ≫ colimit.ι G i ≫ eY.inv =
          colimit.ι Flift (ULift.up n) ≫ eXlift.inv ≫ f :=
    factor_affine_stage_through_presentation B S hS I D_Y hD_Y Y eY
      (inc.obj (D_X.obj n)) (D_X.obj n).property
      (colimit.ι Flift (ULift.up n) ≫ eXlift.inv ≫ f)
  choose targetIndex targetMap htargetMap using hsourceStageFactor
  -- Stacks 0AKN: the base change of `f` over a stage of `Y` is an affine scheme of the site
  have hfAffine := relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY' hrep
  let hRep := hfAffine.1
  -- step 2 and 3: the base change factors through a stage of `X`, and is faithfully flat
  have hfiberStageFactor (i : I) :
      ∃ n : I_X, ∃ k : H.obj (hRep.pullback (colimit.ι G i ≫ eY.inv)) ⟶ Flift.obj n,
        k ≫ colimit.ι Flift n ≫ eXlift.inv =
          hRep.fst (colimit.ι G i ≫ eY.inv) ∧
        Function.Injective
          ((T.map (hRep.snd (colimit.ι G i ≫ eY.inv))).appTop).hom := by
    let ξ := colimit.ι G i ≫ eY.inv
    have hU : IsAffine (T.obj (inc.obj (D_Y.obj i))) := (D_Y.obj i).property
    have hpb : IsAffine (T.obj (hRep.pullback ξ)) := by
      let : IsAffineHom (T.map (hRep.snd ξ)) := hfAffine.property_snd ξ
      let := hU
      exact isAffine_of_isAffineHom (T.map (hRep.snd ξ))
    have hff := faithfullyFlat_of_isPullback_of_surjective_flat B S hS f hrep hsurj hflat
      hU hpb (hRep.isPullback ξ)
    obtain ⟨n, k, hk⟩ := factor_affine_stage_through_presentation B S hS I_X D_Xlift hD_Xlift
      X eXlift (hRep.pullback ξ) hpb (hRep.fst ξ)
    exact ⟨n, k, hk, hff.injective⟩
  choose fiberSourceIndex fiberMap hfiberMap hfiberInjective using hfiberStageFactor
  -- step 3 concluded: every stage of `Y` factors through one of the chosen stages
  have hfactor (i : I) : ∃ n : ℕ, ∃ k : G.obj i ⟶ G.obj (targetIndex n),
      k ≫ colimit.ι G (targetIndex n) ≫ eY.inv = colimit.ι G i ≫ eY.inv := by
    let n := (fiberSourceIndex i).down
    let j := targetIndex n
    let ξ := colimit.ι G i ≫ eY.inv
    let p := hRep.snd ξ
    let b := FF.preimage (fiberMap i ≫ targetMap n)
    obtain ⟨k₀, hik, hjk⟩ := exists_ge_ge i j
    let a := inc.map (D_Y.map (homOfLE hik))
    let c := inc.map (D_Y.map (homOfLE hjk))
    have hw {x : I} (hx : x ≤ k₀) :
        H.map (inc.map (D_Y.map (homOfLE hx))) ≫ colimit.ι G k₀ ≫ eY.inv =
          colimit.ι G x ≫ eY.inv := by
      change G.map (homOfLE hx) ≫ colimit.ι G k₀ ≫ eY.inv = _
      rw [colimit.w_assoc]
    have ha : H.map a ≫ colimit.ι G k₀ ≫ eY.inv = ξ := hw hik
    have hc : H.map c ≫ colimit.ι G k₀ ≫ eY.inv = colimit.ι G j ≫ eY.inv := hw hjk
    have hb : H.map p ≫ ξ = H.map b ≫ colimit.ι G j ≫ eY.inv := by
      rw [show H.map b = fiberMap i ≫ targetMap n from FF.map_preimage _]
      rw [Category.assoc, htargetMap]
      change H.map p ≫ ξ =
        fiberMap i ≫ colimit.ι Flift (fiberSourceIndex i) ≫ eXlift.inv ≫ f
      rw [← Category.assoc _ _ f, ← Category.assoc _ _ f, hfiberMap]
      exact (hRep.isPullback ξ).w.symm
    have hcomm : p ≫ a = b ≫ c := by
      apply FF.map_injective
      let := hιmono k₀
      apply (cancel_mono (colimit.ι G k₀ ≫ eY.inv)).1
      change H.map (p ≫ a) ≫ (colimit.ι G k₀ ≫ eY.inv) =
        H.map (b ≫ c) ≫ (colimit.ι G k₀ ≫ eY.inv)
      simp only [Functor.map_comp, Category.assoc]
      rw [ha, hc]
      exact hb
    have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion (T.map c) := (hD_Y (homOfLE hjk)).1
    let : IsAffine (T.obj (inc.obj (D_Y.obj k₀))) := (D_Y.obj k₀).property
    obtain ⟨q, hq⟩ := exists_factor_over_closedImmersion_of_injective
      B S hS p a b c hclosed (hfiberInjective i) hcomm
    refine ⟨n, H.map q, ?_⟩
    change H.map q ≫ colimit.ι G j ≫ eY.inv = ξ
    rw [← hc, ← Category.assoc, ← H.map_comp, hq, ha]
  -- step 4: replace the chosen stages by a monotone sequence and reindex the colimit
  obtain ⟨seq, hseq, hle⟩ := exists_monotone_ge targetIndex
  let s := hseq.functor
  have hcover (i : I) : ∃ n, ∃ k : G.obj i ⟶ G.obj (s.obj n),
      k ≫ (colimit.cocone G).ι.app (s.obj n) = (colimit.cocone G).ι.app i := by
    obtain ⟨n, k, hk⟩ := hfactor i
    refine ⟨n, k ≫ G.map (homOfLE (hle n)), ?_⟩
    apply (cancel_mono eY.inv).1
    change (k ≫ G.map (homOfLE (hle n))) ≫ colimit.ι G (seq n) ≫ eY.inv =
      colimit.ι G i ≫ eY.inv
    simpa only [Category.assoc, colimit.w_assoc] using hk
  let hcolim := isColimit_of_sequence_factors G (colimit.cocone G) (colimit.isColimit G) s
    (fun i => Sheaf.mono_colimit_ι_of_mono_transition G hGmono i) hcover
  exact ⟨s ⋙ D_Y, fun _ _ g => hD_Y (s.map g),
    ⟨eY ≪≫ hcolim.coconePointUniqueUpToIso (colimit.isColimit (s ⋙ G))⟩⟩

end AlgebraicGeometry.FormalSpace

end
