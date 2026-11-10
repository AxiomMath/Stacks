module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.OpenImmersionPushout

/-!
# The cartesian transition square of a glued étale relation

Fix an étale morphism `w' : W' ⟶ U'` and a morphism `u : U ⟶ U'`, and let
`W = W' ×_{U'} U` be the base change, with projections `k : W ⟶ W'` and `w : W ⟶ U`.
Suppose moreover that `W'` sits inside a scheme `V'` as an open subscheme `j'`, that `W`
sits inside `V` as an open subscheme `j`, and that these two open subschemes are compatible
with a morphism `v : V ⟶ V'` in the strongest sense: the square

```
W  --k-->  W'
|          |
j          j'
v          v
V  --v-->  V'
```

is cartesian, i.e. `W` is the inverse image of `W'` in `V`.

Glueing `V` to `W ×_U W` along the diagonal copy of `W` produces a scheme `R` carrying an
étale equivalence relation on `V`; the same construction at the primed stage produces `R'`.
The source map `s : R ⟶ V` is the identity on the chart `V` and the first projection on the
chart `W ×_U W`, and the construction is functorial, giving `r : R ⟶ R'` over `v`.

This file proves that the resulting square

```
R  --r-->  R'
|          |
s          s'
v          v
V  --v-->  V'
```

is cartesian. This is the displayed equation inside the proof of absolute Noetherian
approximation for algebraic spaces: there `U = U_i`, `U' = U_{i'}` for `i ≥ i'` in the
directed system with `U = lim U_i`, the chart is `W_i = W_0 ×_{U_0} U_i`, and `R_i` is the
glueing of `V_i` and `W_i ×_{U_i} W_i` along `W_i`. The source justifies cartesianness by the
computation

```
(W_{i'} ×_{U_{i'}} W_{i'}) ×_{U_{i'}} U_i
  = W_{i'} ×_{U_{i'}} U_i ×_{U_i} U_i ×_{U_{i'}} W_{i'}
  = W_i ×_{U_i} W_i,
```

which is `AlgebraicGeometry.isPullback_etaleRelationTransition` below.

## Main results

* `AlgebraicGeometry.isPullback_etaleRelationTransition`: the fibre square of a base-changed
  chart is the base change of the fibre square of the chart, which is the displayed
  computation of the source.
* `AlgebraicGeometry.isPullback_gluedRelationSource_of_isPullback`: the transition square of
  the glued relations, over the source maps, is cartesian. This is stated for an arbitrary
  base-changed fibre square in place of `W ×_U W`, so it says nothing about the base `U`; in
  particular it applies when the base is an algebraic space, as it is in the source.
* `AlgebraicGeometry.isPullback_gluedRelationSource`: the same conclusion written out for the
  construction the source performs, with `Q = W ×_U W` and `W = W' ×_{U'} U`.
* `AlgebraicGeometry.exists_gluedRelation_of_isPullback`: the glueing data above exists, so
  the hypotheses of the previous results are not vacuous.

Along the way the two directions relating pushout and pullback squares of a span of open
immersions of schemes are recorded: a pushout square of a span of open immersions is
cartesian with jointly surjective legs, and conversely a cartesian square of open immersions
whose legs are jointly surjective is a pushout square.

## References

* [Stacks Project, Tag 07SV](https://stacks.math.columbia.edu/tag/07SV)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u

namespace AlgebraicGeometry

section Pushout

variable {W X Y P : Scheme.{u}} {f : W ⟶ X} {g : W ⟶ Y}
  [IsOpenImmersion f] [IsOpenImmersion g] {a : X ⟶ P} {b : Y ⟶ P}

private lemma pushout_inl_comp_isoPushout_inv (h : IsPushout f g a b) :
    pushout.inl f g ≫ h.isoPushout.inv = a := by
  rw [← h.inl_isoPushout_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma pushout_inr_comp_isoPushout_inv (h : IsPushout f g a b) :
    pushout.inr f g ≫ h.isoPushout.inv = b := by
  rw [← h.inr_isoPushout_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A leg of a pushout square of a span of open immersions of schemes is an open immersion. -/
lemma isOpenImmersion_inl_of_isPushout (h : IsPushout f g a b) : IsOpenImmersion a := by
  rw [← pushout_inl_comp_isoPushout_inv h]
  infer_instance

/-- A leg of a pushout square of a span of open immersions of schemes is an open immersion. -/
lemma isOpenImmersion_inr_of_isPushout (h : IsPushout f g a b) : IsOpenImmersion b := by
  rw [← pushout_inr_comp_isoPushout_inv h]
  infer_instance

/-- A pushout square of a span of open immersions of schemes is also cartesian: the vertex of
the span is the intersection of the two charts. -/
lemma isPullback_of_isPushout_of_isOpenImmersion (h : IsPushout f g a b) :
    IsPullback f g a b :=
  (isPullback_pushout_inl_inr f g).of_iso (Iso.refl W) (Iso.refl X) (Iso.refl Y)
    h.isoPushout.symm (by simp) (by simp)
    (by simp) (by simp)

/-- The two legs of a pushout square of a span of open immersions of schemes are jointly
surjective. -/
lemma exists_eq_of_isPushout_of_isOpenImmersion (h : IsPushout f g a b) (x : P) :
    (∃ y, a y = x) ∨ (∃ y, b y = x) := by
  have hinj : ∀ z : P, h.isoPushout.inv (h.isoPushout.hom z) = z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hmem : h.isoPushout.hom x ∈
      (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange := by
    rw [opensRange_pushout_inl_sup_opensRange_pushout_inr f g]
    trivial
  have hx : (∃ y, pushout.inl f g y = h.isoPushout.hom x) ∨
      (∃ y, pushout.inr f g y = h.isoPushout.hom x) := by simpa using hmem
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, by rw [← pushout_inl_comp_isoPushout_inv h, Scheme.Hom.comp_apply, hy, hinj]⟩
  · exact Or.inr ⟨y, by rw [← pushout_inr_comp_isoPushout_inv h, Scheme.Hom.comp_apply, hy, hinj]⟩

/-- The binary open cover of a scheme given by two jointly surjective open immersions. -/
private def binaryOpenCover {A B R : Scheme.{u}} (p : A ⟶ R) (q : B ⟶ R)
    [IsOpenImmersion p] [IsOpenImmersion q]
    (h : ∀ x : R, (∃ y, p y = x) ∨ (∃ y, q y = x)) : R.OpenCover where
  I₀ := Bool
  X i := if i then A else B
  f i := by cases i <;> dsimp <;> assumption
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ by cases i <;> dsimp <;> infer_instance⟩
    rcases h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    exacts [⟨true, y, rfl⟩, ⟨false, y, rfl⟩]

omit [IsOpenImmersion f] [IsOpenImmersion g] in
/-- A cartesian square of open immersions of schemes whose legs are jointly surjective is a
pushout square: the target is glued from the two charts along their intersection. -/
lemma isPushout_of_isPullback_of_jointly_surjective {a : X ⟶ P} {b : Y ⟶ P}
    [IsOpenImmersion a] [IsOpenImmersion b] (hp : IsPullback f g a b)
    (hc : ∀ x : P, (∃ y, a y = x) ∨ (∃ y, b y = x)) :
    IsPushout f g a b := by
  let C := binaryOpenCover a b hc
  have compatible {T : Scheme.{u}} (x : X ⟶ T) (y : Y ⟶ T) (h : f ≫ x = g ≫ y) :
      ∀ i j, pullback.fst (C.f i) (C.f j) ≫
        (show C.X i ⟶ T from by cases i <;> dsimp [C, binaryOpenCover] <;> assumption) =
      pullback.snd (C.f i) (C.f j) ≫
        (show C.X j ⟶ T from by cases j <;> dsimp [C, binaryOpenCover] <;> assumption) := by
    intro i j
    cases i <;> cases j
    · change pullback.fst b b ≫ y = pullback.snd b b ≫ y
      rw [(cancel_mono _).mp (pullback.condition (f := _) (g := _))]
    · change pullback.fst b a ≫ y = pullback.snd b a ≫ x
      rw [← hp.flip.isoPullback_inv_fst, ← hp.flip.isoPullback_inv_snd]
      simpa only [Category.assoc] using congrArg (hp.flip.isoPullback.inv ≫ ·) h.symm
    · change pullback.fst a b ≫ x = pullback.snd a b ≫ y
      rw [← hp.isoPullback_inv_fst, ← hp.isoPullback_inv_snd]
      simpa only [Category.assoc] using congrArg (hp.isoPullback.inv ≫ ·) h
    · change pullback.fst a a ≫ x = pullback.snd a a ≫ x
      rw [(cancel_mono _).mp (pullback.condition (f := _) (g := _))]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hp.w
    (fun s ↦ C.glueMorphisms _ (compatible s.inl s.inr s.condition)) ?_ ?_ ?_)
  · exact fun s ↦ C.ι_glueMorphisms _ _ true
  · exact fun s ↦ C.ι_glueMorphisms _ _ false
  · intro s m hm₀ hm₁
    refine C.hom_ext _ _ fun i ↦ ?_
    rw [C.ι_glueMorphisms]
    cases i
    exacts [hm₁, hm₀]

end Pushout

section Transition

variable {C : Type v₂} [Category.{v₁} C] {U U' W' : C} (w' : W' ⟶ U') (u : U ⟶ U')
  [HasPullback w' u] [HasPullback (pullback.snd w' u) (pullback.snd w' u)]
  [HasPullback w' w']

/-- The transition morphism `W ×_U W ⟶ W' ×_{U'} W'` of fibre squares attached to the
cartesian square expressing `W = W' ×_{U'} U`. -/
noncomputable def etaleRelationTransition :
    pullback (pullback.snd w' u) (pullback.snd w' u) ⟶ pullback w' w' :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst w' u) (pullback.snd _ _ ≫ pullback.fst w' u)
    (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, pullback.condition, Category.assoc])

/-- The first projection of `etaleRelationTransition w' u` is the first projection of
`W ×_U W` followed by `W ⟶ W'`. -/
@[simp]
lemma etaleRelationTransition_fst :
    etaleRelationTransition w' u ≫ pullback.fst w' w' =
      pullback.fst (pullback.snd w' u) (pullback.snd w' u) ≫ pullback.fst w' u :=
  pullback.lift_fst _ _ _

/-- The second projection of `etaleRelationTransition w' u` is the second projection of
`W ×_U W` followed by `W ⟶ W'`. -/
@[simp]
lemma etaleRelationTransition_snd :
    etaleRelationTransition w' u ≫ pullback.snd w' w' =
      pullback.snd (pullback.snd w' u) (pullback.snd w' u) ≫ pullback.fst w' u :=
  pullback.lift_snd _ _ _

/-- The transition morphism `W ×_U W ⟶ W' ×_{U'} W'` carries the diagonal of `W` over `U` to
the diagonal of `W'` over `U'`. -/
lemma diagonal_comp_etaleRelationTransition :
    pullback.diagonal (pullback.snd w' u) ≫ etaleRelationTransition w' u =
      pullback.fst w' u ≫ pullback.diagonal w' := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The fibre square of a base-changed chart is the base change of the fibre square of the
chart: writing `W = W' ×_{U'} U` with `k : W ⟶ W'`, the square

```
W ×_U W  -->  W' ×_{U'} W'
|             |
pr₁           pr₁
v             v
W  ---k--->   W'
```

is cartesian. This is the computation
`(W' ×_{U'} W') ×_{U'} U = W' ×_{U'} U ×_U U ×_{U'} W' = W ×_U W`. -/
theorem isPullback_etaleRelationTransition :
    IsPullback (etaleRelationTransition w' u)
      (pullback.fst (pullback.snd w' u) (pullback.snd w' u))
      (pullback.fst w' w') (pullback.fst w' u) := by
  have H' : IsPullback (etaleRelationTransition w' u ≫ pullback.snd w' w')
      (pullback.fst (pullback.snd w' u) (pullback.snd w' u)) w'
      (pullback.fst w' u ≫ w') := by
    rw [etaleRelationTransition_snd, pullback.condition]
    exact (IsPullback.of_hasPullback (pullback.snd w' u) (pullback.snd w' u)).flip.paste_horiz
      (IsPullback.of_hasPullback w' u)
  exact H'.of_right (etaleRelationTransition_fst w' u)
    (IsPullback.of_hasPullback w' w').flip

end Transition

section Glued

/-- In a cartesian square whose two vertical arrows are open immersions, the image of the
upper one is the inverse image of the image of the lower one. -/
private lemma range_eq_preimage_base_of_isPullback
    {A B X Y : Scheme.{u}} {f : A ⟶ B} {iA : A ⟶ X} {iB : B ⟶ Y} {g : X ⟶ Y}
    [IsOpenImmersion iA] [IsOpenImmersion iB] (h : IsPullback f iA iB g) :
    g.base ⁻¹' Set.range iB.base = Set.range iA.base := by
  have hr : iA.opensRange = g ⁻¹ᵁ iB.opensRange := by
    simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h (⊤ : B.Opens)
  simpa [Scheme.Hom.coe_opensRange] using (congrArg (fun O : X.Opens ↦ (O : Set X)) hr).symm

variable {U U' V V' W W' Q Q' R R' : Scheme.{u}}

/-- If `c` is an open immersion into `R'` and `l` lifts `m ≫ c` and `e` to the pullback of `s'`
and `v`, with the outer square cartesian, then `l` is the base change of `c`: it is an open
immersion, and its range is the inverse image of the range of `c`. -/
private lemma isPullback_lift_of_isPullback_comp {X X' V V' R' : Scheme.{u}}
    {s' : R' ⟶ V'} {v : V ⟶ V'} {m : X ⟶ X'} {c : X' ⟶ R'} {e : X ⟶ V}
    {l : X ⟶ pullback s' v} [IsOpenImmersion c] (h₁ : l ≫ pullback.fst s' v = m ≫ c)
    (h₂ : l ≫ pullback.snd s' v = e) (H : IsPullback m e (c ≫ s') v) :
    IsPullback m l c (pullback.fst s' v) ∧ IsOpenImmersion l ∧
      ∀ x, (∃ y, c y = pullback.fst s' v x) → ∃ y, l y = x := by
  have hpb : IsPullback m l c (pullback.fst s' v) := by
    rw [← h₂] at H
    exact H.of_bot h₁.symm (IsPullback.of_hasPullback s' v)
  have hl : IsOpenImmersion l := MorphismProperty.of_isPullback hpb inferInstance
  exact ⟨hpb, hl, fun x hx ↦ (range_eq_preimage_base_of_isPullback hpb).subset hx⟩

/-- **Stacks Project, Tag 07SV.** The displayed square of the proof of absolute Noetherian
approximation, in the form in which the proof establishes it.

The data: a morphism `v : V ⟶ V'`, open subschemes `j : W ⟶ V` and `j' : W' ⟶ V'` with `W`
the inverse image of `W'`, that is with `hj` cartesian; objects `Q`, `Q'` with sections `d`,
`d'` of projections `p`, `p'` — in the application `Q = W ×_U W`, `Q' = W' ×_{U'} W'`,
`p` and `p'` are the first projections and `d`, `d'` the diagonals — such that `Q` is the base
change of `Q'` along `k`, that is with `hQ` cartesian; and the relations `R`, `R'` obtained by
glueing `V` to `Q` along `W` and `V'` to `Q'` along `W'`, with source maps `s`, `s'` which are
the identity on the chart `V`, resp. `V'`, and `p`, resp. `p'`, followed by the open immersion
on the other chart. Then for the morphism `r : R ⟶ R'` induced by `v` and `q` the square

```
R  --r-->  R'
|          |
s          s'
v          v
V  --v-->  V'
```

is cartesian. Nothing is assumed about the base over which `Q` and `Q'` are fibre products,
so this applies verbatim when that base is an algebraic space, as it is in the source. -/
@[stacks 07SV "the displayed square is cartesian, for any base-changed fibre square over W"]
theorem isPullback_gluedRelationSource_of_isPullback
    {v : V ⟶ V'} {k : W ⟶ W'} {j : W ⟶ V} {j' : W' ⟶ V'} [IsOpenImmersion j']
    {p : Q ⟶ W} {p' : Q' ⟶ W'} {d : W ⟶ Q} {d' : W' ⟶ Q'} [IsOpenImmersion d']
    {q : Q ⟶ Q'} (hj : IsPullback k j j' v) (hQ : IsPullback q p p' k)
    (hd : d ≫ p = 𝟙 W) (hdq : d ≫ q = k ≫ d')
    {a : V ⟶ R} {b : Q ⟶ R} {a' : V' ⟶ R'} {b' : Q' ⟶ R'}
    (hR : IsPushout j d a b) (hR' : IsPushout j' d' a' b')
    {s : R ⟶ V} (hsa : a ≫ s = 𝟙 V) (hsb : b ≫ s = p ≫ j)
    {s' : R' ⟶ V'} (hsa' : a' ≫ s' = 𝟙 V') (hsb' : b' ≫ s' = p' ≫ j')
    {r : R ⟶ R'} (hra : a ≫ r = v ≫ a') (hrb : b ≫ r = q ≫ b') :
    IsPullback r s s' v := by
  have hqj : IsPullback q (p ≫ j) (p' ≫ j') v := hQ.paste_vert hj
  have hP := IsPullback.of_hasPullback s' v
  have haux : (v ≫ a') ≫ s' = 𝟙 V ≫ v := by
    rw [Category.assoc, hsa', Category.comp_id, Category.id_comp]
  have hbux : (q ≫ b') ≫ s' = (p ≫ j) ≫ v := by
    rw [Category.assoc, hsb']
    exact hqj.w
  set aP : V ⟶ pullback s' v := hP.lift (v ≫ a') (𝟙 V) haux
  set bP : Q ⟶ pullback s' v := hP.lift (q ≫ b') (p ≫ j) hbux
  have haPfst : aP ≫ pullback.fst s' v = v ≫ a' := hP.lift_fst _ _ _
  have haPsnd : aP ≫ pullback.snd s' v = 𝟙 V := hP.lift_snd _ _ _
  have hbPfst : bP ≫ pullback.fst s' v = q ≫ b' := hP.lift_fst _ _ _
  have hbPsnd : bP ≫ pullback.snd s' v = p ≫ j := hP.lift_snd _ _ _
  have ha' : IsOpenImmersion a' := isOpenImmersion_inl_of_isPushout hR'
  have hb' : IsOpenImmersion b' := isOpenImmersion_inr_of_isPushout hR'
  obtain ⟨haPpb, haPopen, haPc⟩ := isPullback_lift_of_isPullback_comp haPfst haPsnd (by
    rw [hsa']
    exact IsPullback.of_vert_isIso ⟨by simp⟩)
  obtain ⟨hbPpb, hbPopen, hbPc⟩ := isPullback_lift_of_isPullback_comp hbPfst hbPsnd (by
    rw [hsb']
    exact hqj)
  have hcomm : j ≫ aP = d ≫ bP := by
    refine hP.hom_ext ?_ ?_
    · simp only [Category.assoc, haPfst, hbPfst]
      rw [← reassoc_of% hj.w, reassoc_of% hdq, hR'.w]
    · simp [haPsnd, hbPsnd, reassoc_of% hd]
  have hPpb : IsPullback j d aP bP := by
    have H : IsPullback (d ≫ q) j b' (aP ≫ pullback.fst s' v) := by
      rw [hdq, haPfst]
      exact hj.paste_horiz (isPullback_of_isPushout_of_isOpenImmersion hR').flip
    exact (H.of_right hcomm.symm hbPpb).flip
  have hPc : ∀ x : ↥(pullback s' v), (∃ y, aP y = x) ∨ (∃ y, bP y = x) := fun x ↦
    (exists_eq_of_isPushout_of_isOpenImmersion hR' (pullback.fst s' v x)).imp (haPc x) (hbPc x)
  have hPpo : IsPushout j d aP bP :=
    isPushout_of_isPullback_of_jointly_surjective hPpb hPc
  have hw : r ≫ s' = s ≫ v := hR.hom_ext (by simp [reassoc_of% hra, reassoc_of% hsa, hsa'])
    (by simpa [reassoc_of% hrb, reassoc_of% hsb, hsb'] using hqj.w)
  set ψ : R ⟶ pullback s' v := hP.lift r s hw
  have hψfst : ψ ≫ pullback.fst s' v = r := hP.lift_fst _ _ _
  have hψsnd : ψ ≫ pullback.snd s' v = s := hP.lift_snd _ _ _
  have haψ : a ≫ ψ = aP := hP.hom_ext (by rw [Category.assoc, hψfst, hra, haPfst])
    (by rw [Category.assoc, hψsnd, hsa, haPsnd])
  have hbψ : b ≫ ψ = bP := hP.hom_ext (by rw [Category.assoc, hψfst, hrb, hbPfst])
    (by rw [Category.assoc, hψsnd, hsb, hbPsnd])
  have hiso : IsIso ψ := by
    refine ⟨hPpo.desc a b hR.w, ?_, ?_⟩
    · refine hR.hom_ext ?_ ?_
      · rw [← Category.assoc, haψ, hPpo.inl_desc, Category.comp_id]
      · rw [← Category.assoc, hbψ, hPpo.inr_desc, Category.comp_id]
    · refine hPpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hPpo.inl_desc, haψ, Category.comp_id]
      · rw [← Category.assoc, hPpo.inr_desc, hbψ, Category.comp_id]
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso ψ) hψfst hψsnd

/-- **Stacks Project, Tag 07SV.** The displayed square of the proof of absolute Noetherian
approximation, written out for the construction the source performs. Let `w' : W' ⟶ U'` be
étale, let `u : U ⟶ U'` be arbitrary, and let `W = W' ×_{U'} U`. Let `j' : W' ⟶ V'` and
`j : W ⟶ V` be open immersions with `W` the inverse image of `W'`, that is with `hj`
cartesian. Let `R` be obtained by glueing `V` to `W ×_U W` along the diagonal copy of `W`,
and `R'` likewise at the primed stage, and let `s`, `s'` be the source maps: the identity on
the chart `V`, resp. `V'`, and the first projection on the chart `W ×_U W`, resp.
`W' ×_{U'} W'`. If `r : R ⟶ R'` is the morphism induced by `v` on the glueings, then the
square formed by `r`, `s`, `s'` and `v` is cartesian. -/
@[stacks 07SV "the displayed square for R_i glued from V_i and W_i x_{U_i} W_i is cartesian"]
theorem isPullback_gluedRelationSource {u : U ⟶ U'} {v : V ⟶ V'} {w' : W' ⟶ U'} [Etale w']
    {j' : W' ⟶ V'} [IsOpenImmersion j'] {j : pullback w' u ⟶ V}
    (hj : IsPullback (pullback.fst w' u) j j' v)
    {a : V ⟶ R} {b : pullback (pullback.snd w' u) (pullback.snd w' u) ⟶ R}
    {a' : V' ⟶ R'} {b' : pullback w' w' ⟶ R'}
    (hR : IsPushout j (pullback.diagonal (pullback.snd w' u)) a b)
    (hR' : IsPushout j' (pullback.diagonal w') a' b')
    {s : R ⟶ V} (hsa : a ≫ s = 𝟙 V)
    (hsb : b ≫ s = pullback.fst (pullback.snd w' u) (pullback.snd w' u) ≫ j)
    {s' : R' ⟶ V'} (hsa' : a' ≫ s' = 𝟙 V') (hsb' : b' ≫ s' = pullback.fst w' w' ≫ j')
    {r : R ⟶ R'} (hra : a ≫ r = v ≫ a')
    (hrb : b ≫ r = etaleRelationTransition w' u ≫ b') :
    IsPullback r s s' v :=
  isPullback_gluedRelationSource_of_isPullback hj (isPullback_etaleRelationTransition w' u)
    (pullback.diagonal_fst _) (diagonal_comp_etaleRelationTransition w' u) hR hR' hsa hsb
    hsa' hsb' hra hrb

/-- The glueing data of `AlgebraicGeometry.isPullback_gluedRelationSource` exists: for an
étale `w' : W' ⟶ U'`, a morphism `u : U ⟶ U'` and compatible open immersions `j'`, `j` of the
charts into `V'`, `V`, one can glue `V` to `W ×_U W` and `V'` to `W' ×_{U'} W'`, obtain the
source maps and the induced transition morphism, and the resulting square is cartesian. -/
theorem exists_gluedRelation_of_isPullback {u : U ⟶ U'} {v : V ⟶ V'} {w' : W' ⟶ U'}
    [Etale w'] {j' : W' ⟶ V'} [IsOpenImmersion j'] {j : pullback w' u ⟶ V} [IsOpenImmersion j]
    (hj : IsPullback (pullback.fst w' u) j j' v) :
    ∃ (R R' : Scheme.{u}) (a : V ⟶ R)
      (b : pullback (pullback.snd w' u) (pullback.snd w' u) ⟶ R)
      (a' : V' ⟶ R') (b' : pullback w' w' ⟶ R') (s : R ⟶ V) (s' : R' ⟶ V') (r : R ⟶ R'),
      IsPushout j (pullback.diagonal (pullback.snd w' u)) a b ∧
      IsPushout j' (pullback.diagonal w') a' b' ∧
      a ≫ s = 𝟙 V ∧
      b ≫ s = pullback.fst (pullback.snd w' u) (pullback.snd w' u) ≫ j ∧
      a' ≫ s' = 𝟙 V' ∧ b' ≫ s' = pullback.fst w' w' ≫ j' ∧
      a ≫ r = v ≫ a' ∧ b ≫ r = etaleRelationTransition w' u ≫ b' ∧
      IsPullback r s s' v := by
  have hR : IsPushout j (pullback.diagonal (pullback.snd w' u))
      (pushout.inl j (pullback.diagonal (pullback.snd w' u)))
      (pushout.inr j (pullback.diagonal (pullback.snd w' u))) :=
    IsPushout.of_hasPushout _ _
  have hR' : IsPushout j' (pullback.diagonal w') (pushout.inl j' (pullback.diagonal w'))
      (pushout.inr j' (pullback.diagonal w')) := IsPushout.of_hasPushout _ _
  refine ⟨_, _, _, _, _, _,
    hR.desc (𝟙 V) (pullback.fst (pullback.snd w' u) (pullback.snd w' u) ≫ j) ?_,
    hR'.desc (𝟙 V') (pullback.fst w' w' ≫ j') ?_, ?_, hR, hR', hR.inl_desc _ _ _,
    hR.inr_desc _ _ _, hR'.inl_desc _ _ _, hR'.inr_desc _ _ _, ?_, ?_, ?_⟩
  · rw [Category.comp_id, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  · rw [Category.comp_id, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  · refine hR.desc (v ≫ pushout.inl j' (pullback.diagonal w'))
      (etaleRelationTransition w' u ≫ pushout.inr j' (pullback.diagonal w')) ?_
    rw [← Category.assoc, ← hj.w, Category.assoc, hR'.w, ← Category.assoc,
      ← diagonal_comp_etaleRelationTransition, Category.assoc]
  · exact hR.inl_desc _ _ _
  · exact hR.inr_desc _ _ _
  · exact isPullback_gluedRelationSource hj hR hR' (hR.inl_desc _ _ _) (hR.inr_desc _ _ _)
      (hR'.inl_desc _ _ _) (hR'.inr_desc _ _ _) (hR.inl_desc _ _ _) (hR.inr_desc _ _ _)

end Glued

end AlgebraicGeometry

end
