module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PullbackCase
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupUniversal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChangeGeneral
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullbackGeneral

/-!
# The modification of a pulled-back triple is the strict transform

Let `(X, D, M)` be a triple as in Situation 0F8S, `h : Y ⟶ X` a morphism such that the pullback
`E = h⁻¹D` is defined, and let `b : X' ⟶ X` and `c : Y' ⟶ Y` be the morphisms of Stacks tag 0GTY
for `(X, D, M)` and for `(Y, E, Lh^*M)`.  The triple `(Y', c⁻¹E, Lc^*Lh^*M)` is good, so by the
universal property of `b` there is a unique `h' : Y' ⟶ X'` with `b ∘ h' = h ∘ c`.  Stacks tag
0F8V asserts that

* over every open `W ⊆ X` over which `b⁻¹(W) ⟶ W` is a blowing up, `(h', c)` identifies `Y'|_W`
  with the strict transform of `Y_W = h⁻¹(W)` with respect to that blowing up, and
* `Lη_{𝒥'}L(h ∘ c)^*M ≅ Lh'^*Q`, where `Q = Lη_{ℐ'}Lb^*M` and `𝒥'` is the ideal sheaf of
  `(h ∘ c)⁻¹D`.

The second assertion is Stacks tag 0F9X for the good triple `(X', b⁻¹D, Lb^*M)`.  For the first,
let `b⁻¹(W) ⟶ W` be the blowing up of `W` in `ℐ`.  The strict transform of `Y_W` is the blowing
up of `Y_W` in `ℐ𝒪_{Y_W}` (Stacks tag 080E), so it suffices to see that this blowing up and
`c⁻¹(Y_W) ⟶ Y_W` have the same universal property: a morphism `T ⟶ Y_W` makes `(T, E_T, M_T)` a
good triple exactly when it makes `ℐ𝒪_T` an effective Cartier divisor.  One direction holds
because good morphisms to `W` factor through `b⁻¹(W) ≅ Bl_ℐ W`, on which `ℐ` is invertible with
support inside `D`, and an invertible ideal supported in `D` stays invertible wherever `D` does;
the other because the blowing up of `Y_W` in `ℐ𝒪_{Y_W}` maps to `Bl_ℐ W ≅ b⁻¹(W)`, which is good.

## Main results

* `ComplexAndDivisorSituation.exists_lift_isStrictTransform_and_etaDerivedPullbackObject_iso`:
  **Stacks tag 0F8V**, the strict transform assertion and the identification
  `Lη_{𝒥'}L(h ∘ c)^*M ≅ Lh'^*Q`.
* `ComplexAndDivisorSituation.isGoodOver_pullback_iff`: a morphism `g : T ⟶ Y` is good for
  `(Y, E, Lh^*M)` exactly when `h ∘ g` is good for `(X, D, M)`.
* `Stacks.Divisors.isEffectiveCartierDivisor_comap_of_support_le`: an effective Cartier divisor
  whose support lies in the support of `F` pulls back to an effective Cartier divisor along every
  morphism along which `F` does.

## Implementation notes

The source quantifies over quasi-compact opens `W` such that `b⁻¹(W) ⟶ W` is a blowing up, and
the strict transform depends on the centre of that blowing up.  Read with an arbitrary centre
the assertion is false: for `X = 𝔸¹` with `D = V(x)` and `M = 𝒪_X` the morphism `b` is the
identity, which is also the blowing up of `X` in the invertible ideal `(x - 1)`, and for
`Y = V(x - 1)` one has `Y' = Y` while the strict transform of `Y` with respect to that blowing up
is empty.  The blowing ups meant are those of Stacks tag 0GTY, whose centres are supported in
`D`; the statement here quantifies over centres `ℐ ⊆ 𝒪_W` whose support is disjoint from
`W ∖ D`, which is the admissibility condition of that tag without its finiteness condition.
Quasi-compactness of `W` is not needed.  The blowing up structure is an isomorphism
`e : Bl_ℐ W ≅ b⁻¹(W)` over `W`, and the strict transform is
`Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase ℐ) (exceptionalIdeal ℐ)`, the closed
subscheme of `Y_W ×_W Bl_ℐ W` cut out by the sections supported on the inverse image of the
exceptional divisor (Stacks tag 080D).

The morphisms `b` and `c` are taken to be any morphisms with properties (1) and (2) of Stacks tag
0GTY; the morphisms the tag constructs, `goodBlowupToBase`, are instances
(`isGoodBlowup_goodBlowupToBase`), and any two such are isomorphic over the base.

## References

* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

namespace Stacks.Divisors

/-- **An effective Cartier divisor supported in `F` pulls back wherever `F` does.**  Let `J` be
an effective Cartier divisor on `Z` whose support lies in the support of an ideal sheaf `F`, and
let `k : T ⟶ Z` be a morphism along which `F` pulls back to an effective Cartier divisor.  Then
`J` pulls back to an effective Cartier divisor along `k`.

Locally `J = (a)` with `a` a nonzerodivisor and `F ⊆ √J`; if `F𝒪_T = (y)` with `y` a
nonzerodivisor, then `y^n = r·k^♯(a)` for some `n`, so `k^♯(a)` is a nonzerodivisor. -/
theorem isEffectiveCartierDivisor_comap_of_support_le {Z T : Scheme.{u}} (k : T ⟶ Z)
    {J F : Z.IdealSheafData} (hJ : IsEffectiveCartierDivisor J) (hJF : J.support ≤ F.support)
    (hFk : IsEffectiveCartierDivisor (F.comap k)) :
    IsEffectiveCartierDivisor (J.comap k) := by
  have hrad : F ≤ J.radical :=
    calc F ≤ F.radical := F.le_radical
      _ = Scheme.IdealSheafData.vanishingIdeal F.support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ ≤ Scheme.IdealSheafData.vanishingIdeal J.support :=
        Scheme.IdealSheafData.vanishingIdeal_antimono hJF
      _ = J.radical := Scheme.IdealSheafData.vanishingIdeal_support
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun t => ?_
  obtain ⟨V, hzV, -, a, -, hJV⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le J hJ (k t) ⊤ trivial
  obtain ⟨W, htW, hWV, y, hy, hFW⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le (F.comap k) hFk t (k ⁻¹ᵁ (V : Z.Opens)) hzV
  have hJW : (J.comap k).ideal W = Ideal.span {(k.appLE V W hWV).hom a} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE J k V W hWV, hJV, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨n, hn⟩ : y ∈ (Ideal.span {(k.appLE V W hWV).hom a}).radical := by
    have hyF : y ∈ (F.comap k).ideal W := hFW ▸ Ideal.mem_span_singleton_self y
    rw [Stacks.IdealSheaf.ideal_comap_appLE F k V W hWV] at hyF
    rw [← hJW, Stacks.IdealSheaf.ideal_comap_appLE J k V W hWV]
    exact Ideal.map_radical_le _ (Ideal.map_mono (Scheme.IdealSheafData.le_def.1 hrad V) hyF)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hn
  have hreg : IsRegular (r * (k.appLE V W hWV).hom a) := hr ▸ hy.pow n
  exact ⟨W, W.2, htW, _, (isRegular_mul_iff.1 hreg).2, hJW⟩

end Stacks.Divisors

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The universal property of Stacks tag 0GTY restricts to opens.**  If `b : X' ⟶ X` has
properties (1) and (2) of the tag, then for every open `U ⊆ X` the restriction
`b⁻¹(U) ⟶ U` has the universal property of the tag relative to `U ⟶ X`. -/
theorem IsGoodBlowup.isGoodBlowupAlong_morphismRestrict {S : ComplexAndDivisorSituation.{u, d}}
    {X' : Scheme.{u}} {b : X' ⟶ S.X} (hb : S.IsGoodBlowup b) (U : S.X.Opens) :
    S.IsGoodBlowupAlong U.ι (b ∣_ U) := by
  simpa only [Category.comp_id] using
    (isGoodBlowupAlong_id_iff.2 hb).of_isPullback U.ι (isPullback_morphismRestrict b U).flip

variable (S : ComplexAndDivisorSituation.{u, d})

/-- **Goodness for a pulled-back triple is goodness of the composite.**  Let `h : Y ⟶ X` be a
morphism along which `E = h⁻¹D` is defined.  A morphism `g : T ⟶ Y` is good for `(Y, E, Lh^*M)`
if and only if `h ∘ g` is good for `(X, D, M)`: the divisors `g⁻¹E` and `(h ∘ g)⁻¹D` are the same
ideal sheaf, and `Lg^*Lh^*M ≅ L(h ∘ g)^*M`. -/
theorem isGoodOver_pullback_iff {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hE : Stacks.Divisors.IsPullbackDefined h S.D) {T : Scheme.{u}} (g : T ⟶ Y) :
    (S.pullback h hE).IsGoodOver g ↔ S.IsGoodOver (g ≫ h) := by
  have hD : (S.pullback h hE).D.comap g = S.D.comap (g ≫ h) :=
    (Scheme.IdealSheafData.comap_comp S.D g h).symm
  obtain ⟨e⟩ := S.nonempty_derivedPullbackObject_comp h hE g
  have hiff : Stacks.Divisors.IsPullbackDefined g (S.pullback h hE).D ↔
      Stacks.Divisors.IsPullbackDefined (g ≫ h) S.D := by
    change Stacks.Divisors.IsEffectiveCartierDivisor _ ↔ Stacks.Divisors.IsEffectiveCartierDivisor _
    exact iff_of_eq (congrArg _ hD)
  refine ⟨fun H => ?_, fun H => ?_⟩
  · exact ⟨hiff.1 H.pullbackDefined, isGoodTriple_pullback_of_comap_eq (S.pullback h hE) S g
      (g ≫ h) H.pullbackDefined (hiff.1 H.pullbackDefined) hD e H.isGoodTriple⟩
  · exact ⟨hiff.2 H.pullbackDefined, isGoodTriple_pullback_of_comap_eq S (S.pullback h hE)
      (g ≫ h) g H.pullbackDefined (hiff.2 H.pullbackDefined) hD.symm e.symm H.isGoodTriple⟩

variable {S} in
/-- A morphism to `W` that is good for the triple makes the centre `ℐ` of a blowing up structure
`Bl_ℐ W ≅ b⁻¹(W)` an effective Cartier divisor, when `ℐ` is supported in `D`. -/
theorem IsGoodBlowup.isEffectiveCartierDivisor_comap_of_isGoodOver {X' : Scheme.{u}}
    {b : X' ⟶ S.X} (hb : S.IsGoodBlowup b) {W : S.X.Opens} {I : W.toScheme.IdealSheafData}
    (hI : Disjoint ((W.ι ⁻¹ᵁ S.D.support.compl : W.toScheme.Opens) : Set W.toScheme)
      (I.support : Set W.toScheme))
    {e : blowUp I ≅ (b ⁻¹ᵁ W).toScheme} (he : e.hom ≫ (b ⁻¹ᵁ W).ι ≫ b = blowUpToBase I ≫ W.ι)
    {T : Scheme.{u}} (t : T ⟶ W.toScheme) (ht : S.IsGoodOver (t ≫ W.ι)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap t) := by
  obtain ⟨κ, hκ, -⟩ := hb.existsUnique_lift (t ≫ W.ι) ht
  have hrange : Set.range κ ⊆ Set.range (b ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change b (κ x) ∈ W
    rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
    exact (t x).2
  have hl : (IsOpenImmersion.lift (b ⁻¹ᵁ W).ι κ hrange ≫ e.inv) ≫ blowUpToBase I = t := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, ← he, Iso.inv_hom_id_assoc,
      reassoc_of% (IsOpenImmersion.lift_fac (b ⁻¹ᵁ W).ι κ hrange), hκ]
  rw [← hl, Scheme.IdealSheafData.comap_comp]
  refine Stacks.Divisors.isEffectiveCartierDivisor_comap_of_support_le _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
    (F := S.D.comap (blowUpToBase I ≫ W.ι)) ?_ ?_
  · intro x hx
    simp only [Scheme.IdealSheafData.support_comap] at hx ⊢
    by_contra hxD
    exact Set.disjoint_left.1 hI hxD hx
  · rw [← Scheme.IdealSheafData.comap_comp, ← Category.assoc, hl]
    exact ht.pullbackDefined

variable {S} in
/-- The blowing up of `h⁻¹(W)` in `ℐ𝒪_{h⁻¹(W)}` has the universal property of Stacks tag 0GTY
for the pulled-back triple, when `Bl_ℐ W ≅ b⁻¹(W)` and `ℐ` is supported in `D`. -/
theorem IsGoodBlowup.isGoodBlowupAlong_blowUpToBase_comap {X' Y : Scheme.{u}}
    {b : X' ⟶ S.X} (hb : S.IsGoodBlowup b) {h : Y ⟶ S.X}
    (hE : Stacks.Divisors.IsPullbackDefined h S.D) {W : S.X.Opens} {I : W.toScheme.IdealSheafData}
    (hI : Disjoint ((W.ι ⁻¹ᵁ S.D.support.compl : W.toScheme.Opens) : Set W.toScheme)
      (I.support : Set W.toScheme))
    {e : blowUp I ≅ (b ⁻¹ᵁ W).toScheme} (he : e.hom ≫ (b ⁻¹ᵁ W).ι ≫ b = blowUpToBase I ≫ W.ι) :
    (S.pullback h hE).IsGoodBlowupAlong (h ⁻¹ᵁ W).ι (blowUpToBase (I.comap (h ∣_ W))) := by
  refine ⟨?_, fun g hg => existsUnique_lift_blowUpToBase _ g ?_⟩
  · refine (S.isGoodOver_pullback_iff h hE
      (blowUpToBase (I.comap (h ∣_ W)) ≫ (h ⁻¹ᵁ W).ι)).2 ?_
    have hcart : Stacks.Divisors.IsEffectiveCartierDivisor
        (I.comap (blowUpToBase (I.comap (h ∣_ W)) ≫ h ∣_ W)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
    obtain ⟨m, hm, -⟩ := existsUnique_lift_blowUpToBase I _ hcart
    have heq : (blowUpToBase (I.comap (h ∣_ W)) ≫ (h ⁻¹ᵁ W).ι) ≫ h =
        (m ≫ e.hom ≫ (b ⁻¹ᵁ W).ι) ≫ b := by
      rw [Category.assoc, Category.assoc, Category.assoc, he, reassoc_of% hm,
        morphismRestrict_ι]
    have hdef : Stacks.Divisors.IsPullbackDefined
        ((blowUpToBase (I.comap (h ∣_ W)) ≫ (h ⁻¹ᵁ W).ι) ≫ h) S.D := by
      change Stacks.Divisors.IsEffectiveCartierDivisor (S.D.comap _)
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
      exact isPullbackDefined_blowUpToBase _ _
        (Stacks.Divisors.isPullbackDefined_of_flat (h ⁻¹ᵁ W).ι _ hE)
    rw [heq] at hdef ⊢
    exact hb.isGoodOver.comp _ hdef
  · rw [← Scheme.IdealSheafData.comap_comp]
    refine hb.isEffectiveCartierDivisor_comap_of_isGoodOver hI he _ ?_
    rw [show (g ≫ h ∣_ W) ≫ W.ι = (g ≫ (h ⁻¹ᵁ W).ι) ≫ h by
      rw [Category.assoc, morphismRestrict_ι, Category.assoc]]
    exact (S.isGoodOver_pullback_iff h hE _).1 hg

/-- **Stacks tag 0F8V.**  Let `(X, D, M)` be a triple as in Situation 0F8S, let `h : Y ⟶ X` be a
morphism such that `E = h⁻¹D` is defined, and let `b : X' ⟶ X` and `c : Y' ⟶ Y` have
properties (1) and (2) of Stacks tag 0GTY for `(X, D, M)` and for `(Y, E, Lh^*M)`.  Then:

* there is a unique `h' : Y' ⟶ X'` with `b ∘ h' = h ∘ c`;
* for every open `W ⊆ X` and every ideal sheaf `ℐ` on `W` with support inside `D` such that
  `b⁻¹(W) ⟶ W` is the blowing up of `W` in `ℐ`, the morphism `(h', c)` identifies `c⁻¹(h⁻¹W)`
  with the strict transform of `h⁻¹W` with respect to that blowing up: there is an isomorphism
  from `c⁻¹(h⁻¹W)` onto the strict transform whose composites with the two projections of
  `h⁻¹W ×_W Bl_ℐ W` are `c` and `h'`;
* `(h ∘ c)⁻¹D` is defined and `Lη_{𝒥'}L(h ∘ c)^*M ≅ Lh'^*Q`, where `Q = Lη_{ℐ'}Lb^*M`.

The last assertion of the tag, the case `c = 𝟙_Y`, is
`exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver`. -/
@[stacks 0F8V "the strict transform assertion, for every blowing up structure on b over an \
open W whose centre is supported in D, and the identification Lη_J' L(h ∘ c)^* M ≅ L(h')^* Q; \
the last assertion is `exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver`"]
theorem exists_lift_isStrictTransform_and_etaDerivedPullbackObject_iso {X' Y Y' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : S.IsGoodBlowup b) (h : Y ⟶ S.X)
    (hE : Stacks.Divisors.IsPullbackDefined h S.D) (c : Y' ⟶ Y)
    (hc : (S.pullback h hE).IsGoodBlowup c) :
    ∃ h' : Y' ⟶ X', h' ≫ b = c ≫ h ∧ (∀ k : Y' ⟶ X', k ≫ b = c ≫ h → k = h') ∧
      (∀ (W : S.X.Opens) (I : W.toScheme.IdealSheafData),
        Disjoint ((W.ι ⁻¹ᵁ S.D.support.compl : W.toScheme.Opens) : Set W.toScheme)
          (I.support : Set W.toScheme) →
        ∀ e : blowUp I ≅ (b ⁻¹ᵁ W).toScheme,
          e.hom ≫ (b ⁻¹ᵁ W).ι ≫ b = blowUpToBase I ≫ W.ι →
          ∃ φ : (c ⁻¹ᵁ (h ⁻¹ᵁ W)).toScheme ≅
              (Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase I)
                (exceptionalIdeal I)).subscheme,
            φ.hom ≫ (Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase I)
                (exceptionalIdeal I)).subschemeι ≫ pullback.fst (h ∣_ W) (blowUpToBase I) ≫
                (h ⁻¹ᵁ W).ι = (c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ c ∧
            φ.hom ≫ (Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase I)
                (exceptionalIdeal I)).subschemeι ≫ pullback.snd (h ∣_ W) (blowUpToBase I) ≫
                e.hom ≫ (b ⁻¹ᵁ W).ι = (c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ h') ∧
      ∃ hJ' : Stacks.Divisors.IsPullbackDefined (c ≫ h) S.D,
        Nonempty (S.etaDerivedPullbackObject (c ≫ h) hJ' ≅
          (derivedPullback h'.toLRSHom.toShHom).obj
            (S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined)) := by
  have hgc : S.IsGoodOver (c ≫ h) := (S.isGoodOver_pullback_iff h hE c).1 hc.isGoodOver
  obtain ⟨h', hh', huniq⟩ := hb.existsUnique_lift (c ≫ h) hgc
  obtain ⟨k, hk, ⟨i⟩⟩ :=
    S.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver b hb (c ≫ h) hgc
  obtain rfl := (huniq k hk).symm
  refine ⟨h', hh', huniq, fun W I hI e he => ?_, hgc.pullbackDefined, ⟨i.symm⟩⟩
  have hc' : (S.pullback h hE).IsGoodBlowupAlong (h ⁻¹ᵁ W).ι (c ∣_ (h ⁻¹ᵁ W)) :=
    hc.isGoodBlowupAlong_morphismRestrict (h ⁻¹ᵁ W)
  obtain ⟨ψ, hψ⟩ := (hb.isGoodBlowupAlong_blowUpToBase_comap hE hI he).exists_iso hc'
  let σ := strictTransformBlowUpIso (h ∣_ W) I
  have hσ := Over.w σ.inv
  simp only [Over.mk_hom] at hσ
  have h₁ : (ψ.hom ≫ σ.inv.left) ≫ (Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι ≫ pullback.fst (h ∣_ W) (blowUpToBase I) ≫
      (h ⁻¹ᵁ W).ι = (c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ c := by
    rw [Category.assoc, reassoc_of% hσ, reassoc_of% hψ, morphismRestrict_ι]
  refine ⟨ψ ≪≫ (Over.forget _).mapIso σ.symm, h₁, ?_⟩
  have hgood : S.IsGoodOver (((c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ h') ≫ b) := by
    rw [Category.assoc, hh']
    exact hgc.comp_of_flat _
  refine (hb.existsUnique_lift _ hgood).unique ?_ rfl
  change ((ψ.hom ≫ σ.inv.left) ≫ _ ≫ _ ≫ _ ≫ _) ≫ b = _
  calc _ = ((ψ.hom ≫ σ.inv.left) ≫ (Stacks.StrictTransform.ideal (h ∣_ W) (blowUpToBase I)
          (exceptionalIdeal I)).subschemeι ≫ pullback.fst (h ∣_ W) (blowUpToBase I) ≫
          (h ⁻¹ᵁ W).ι) ≫ h := by
        simp only [Category.assoc, he]
        rw [← pullback.condition_assoc, morphismRestrict_ι]
    _ = ((c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ c) ≫ h := by rw [h₁]
    _ = ((c ⁻¹ᵁ (h ⁻¹ᵁ W)).ι ≫ h') ≫ b := by simp only [Category.assoc, hh']

end ComplexAndDivisorSituation

end AlgebraicGeometry
