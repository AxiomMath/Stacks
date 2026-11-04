module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionRelativeCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrValuativeIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EnvelopeRelativeLift
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GysinAction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeOpenCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictedBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The composition of two relative cycles is a relative cycle

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, with `S` locally
Noetherian, and let `r, e ≥ 0`. This file proves
[Stacks, Lemma 0H6R](https://stacks.math.columbia.edu/tag/0H6R): if `α` is a relative `r`-cycle
on `X/Y` and `β` is a relative `e`-cycle on `Y/S`, then the composition `α ∘ β` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition` is a relative `(r + e)`-cycle on
`X/S`.

## Main results

* `Stacks.Chow.isRelativeCycle_compFamily` — **Stacks Project, Lemma 0H6R**.
* `Stacks.Chow.compRelativeCycles` — the induced pairing
  `z(X/Y, r) ⟶ z(Y/S, e) ⟶ z(X/S, r + e)` of Section 0H6Q.
* `Stacks.Chow.isRelativeCycle_compFamily_of_isNoetherian_dvr` — the case in which the base is
  the spectrum of a discrete valuation ring and `Y` is Noetherian, where the whole content of
  the lemma sits.

## Implementation notes

The proof is the one in the source, in three reductions.

### Reduction to a base which is the spectrum of a discrete valuation ring

The valuative condition for `α ∘ β` at a morphism `c : Spec R ⟶ S` is, by the base change
compatibility of Tag 0H6K, the valuative condition at `𝟙 (Spec R)` for the composition of the
base changes of `α` and `β` over `Spec R`; that step is already available as
`Stacks.Chow.isRelativeCycle_compFamily_of_forall_dvr`, and
`Stacks.Chow.specializationCycle_eq_of_isRelativeCycle` reads the identity at `𝟙 (Spec R)` off
the statement that the composition of the base changes is a relative cycle. The base changes are
relative cycles by the base change clause of Lemma 0H51.

### Reduction to affine schemes

Being a relative cycle is local on the source — `Stacks.Chow.isRelativeCycle_of_openCover` — and
the composition is compatible with restriction to open subschemes by Tag 0H6J
(`Stacks.Chow.restrictedFamily_compFamily`). Covering `Y` by affine opens `V` and each `X ×_Y V`
by affine opens `U` therefore reduces the lemma over `Spec R` to the case of `U ⟶ V ⟶ Spec R`
with `U` and `V` affine. Over a discrete valuation ring such a `V` is a Noetherian scheme, and
both `U ⟶ V` and `V ⟶ Spec R` are then quasi-compact, which is what the two cycle-class
inputs below need. This is the source's "since we are trying to prove an equality of cycles, we
may work locally on `Y` and `X`".

### The case of a Noetherian base and a quasi-compact morphism

Here the two non-formal inputs enter. Lemma 0H59 produces a proper, completely decomposed
`q : V' ⟶ V` with `V'` Noetherian such that `q^*α` is a combination of the cycle classes of
Equation 0H58, and `Stacks.Chow.exists_isRelativeCycle_properPushforwardFamily_eq` lifts `β`
along `q` to a relative cycle `β'` on `V'/Spec R` with `q_*β' = β`. The projection formula of
Tag 0H6N turns `α ∘ β = α ∘ q_*β'` into the proper pushforward of `q^*α ∘ β'`, which is a
relative cycle by `Stacks.Chow.isRelativeCycle_compFamily_cycleClassMap_dvr` — the case of the
lemma in which the first argument is a cycle class and the base is the spectrum of a discrete
valuation ring — and proper pushforward preserves relative cycles by the proper pushforward
clause of Lemma 0H51.

## References

* [Stacks Project, Lemma 0H6R](https://stacks.math.columbia.edu/tag/0H6R)
* [Stacks Project, Section 0H6Q](https://stacks.math.columbia.edu/tag/0H6Q)
* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Lemma 0H6J](https://stacks.math.columbia.edu/tag/0H6J)
* [Stacks Project, Lemma 0H6K](https://stacks.math.columbia.edu/tag/0H6K)
* [Stacks Project, Lemma 0H6N](https://stacks.math.columbia.edu/tag/0H6N)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The case of a Noetherian base and quasi-compact morphisms -/

/-- **Stacks Project, Lemma 0H6R over the spectrum of a discrete valuation ring, with `V`
Noetherian.** Let `R` be a discrete valuation ring, let `fU : U ⟶ V` and `gV : V ⟶ Spec R` be
locally of finite type and quasi-compact with `V` Noetherian, and let `r, e ≥ 0`. The
composition of a relative `r`-cycle on `U/V` with a relative `e`-cycle on `V/Spec R` is a
relative `(r + e)`-cycle on `U/Spec R`.

By Lemma 0H59 there is a proper, completely decomposed `q : V' ⟶ V` with `V'` Noetherian such
that `q^*γ` is a combination of the cycle classes of Equation 0H58, and `δ` lifts along `q` to a
relative cycle `δ'` with `q_*δ' = δ`. The projection formula of Tag 0H6N identifies
`γ ∘ q_*δ'` with the proper pushforward of `q^*γ ∘ δ'`, which is a relative cycle because its
first argument is a cycle class. -/
theorem isRelativeCycle_compFamily_of_isNoetherian_dvr {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {U V : Scheme.{u}} (fU : U ⟶ V) [LocallyOfFiniteType fU]
    [QuasiCompact fU] (gV : V ⟶ Spec (.of R)) [LocallyOfFiniteType gV] [QuasiCompact gV]
    [IsNoetherian V] (r e : ℕ) {γ : FamilyOfCycles fU r} {δ : FamilyOfCycles gV e}
    (hγ : IsRelativeCycle fU r γ) (hδ : IsRelativeCycle gV e δ) :
    IsRelativeCycle (fU ≫ gV) (r + e) (compFamily fU gV r e γ δ) := by
  obtain ⟨V', q, hV'noeth, hqproper, hqcd, c, hc⟩ :=
    exists_isProper_isCompletelyDecomposed_relativeCycleClassMap_eq fU r ⟨γ, hγ⟩
  have := hqproper
  have := hV'noeth
  obtain ⟨δ', hδ'rel, hδ'push⟩ :=
    exists_isRelativeCycle_properPushforwardFamily_eq gV q hqcd e hδ
  have hcc : cycleClassMap (pullback.snd fU q) r c = baseChangeFamily fU q r γ := by
    rw [← relativeCycleClassMap_val (pullback.snd fU q) c]
    exact hc
  rw [← hδ'push,
    ← properPushforwardFamily_compFamily_baseChangeFamily gV (q ≫ gV) fU q rfl r e γ δ', ← hcc]
  exact isRelativeCycle_properPushforwardFamily (pullback.snd fU q ≫ q ≫ gV) (fU ≫ gV)
    (pullback.fst fU q) (pullbackFst_comp_eq_of_base q rfl rfl) (r + e)
    (isRelativeCycle_compFamily_cycleClassMap_dvr (pullback.snd fU q) (q ≫ gV) r e c hδ'rel)

/-! ### Restricting the composition to an open subscheme of the source -/

/-- **The composition restricted to an open subscheme of the source.** For open immersions
`j : U ⟶ X` and `i : V ⟶ Y` with `f(U) ⊆ V`, the family of `(r + e)`-cycles on the fibres of
`U/S` obtained by restricting `α ∘ β` fibre by fibre is the composition of the restriction of
`α` to `U/V` with the restriction of `β` to `V/S`.

This is Tag 0H6J, `Stacks.Chow.restrictedFamily_compFamily`, for the three opens `U ⊆ X`,
`V ⊆ Y` and `S ⊆ S`, read through `Stacks.Chow.restrictedFamily_id_apply`, which identifies the
restriction along a square over the identity of the base with the fibrewise restriction along
the top edge. It is the shape in which `Stacks.Chow.isRelativeCycle_of_openCover` consumes the
compatibility. -/
theorem fiberCycleRestrict_compFamily {X Y S U V : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] (fU : U ⟶ V)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ Y) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (h' : j ≫ (f ≫ g) = fU ≫ i ≫ g) (r e : ℕ) (α : FamilyOfCycles f r)
    (β : FamilyOfCycles g e) :
    (fun s ↦ fiberCycleRestrict (f ≫ g) (fU ≫ i ≫ g) j h' s (r + e)
        (compFamily f g r e α β s)) =
      compFamily fU (i ≫ g) r e (restrictedFamily f fU j i h r α).1
        (restrictedFamily g (i ≫ g) i (𝟙 S) (by simp) e β).1 := by
  funext s
  rw [← restrictedFamily_id_apply (f ≫ g) (fU ≫ i ≫ g) j (by rw [Category.comp_id]; exact h') h'
    (r + e) (compFamily f g r e α β) s]
  exact congrFun
    (restrictedFamily_compFamily f g fU (i ≫ g) j i (𝟙 S) h (by simp) r e α β) s

/-! ### Reduction to affine schemes over the spectrum of a discrete valuation ring -/

/-- **Stacks Project, Lemma 0H6R over the spectrum of a discrete valuation ring.** Let `R` be a
discrete valuation ring, let `f : X ⟶ Y` and `g : Y ⟶ Spec R` be locally of finite type and let
`r, e ≥ 0`. The composition of a relative `r`-cycle on `X/Y` with a relative `e`-cycle on
`Y/Spec R` is a relative `(r + e)`-cycle on `X/Spec R`.

Being a relative cycle is local on the source, so it is enough to check the restriction of
`α ∘ β` to each member of an open cover of `X`. Taking the affine opens of the schemes
`X ×_Y V` for `V` running through an affine open cover of `Y` gives a cover by affine opens `U`
each of which maps into an affine open `V` of `Y`; the restriction of `α ∘ β` there is the
composition of the restrictions by Tag 0H6J, and both `U` and `V` are Noetherian over the
Noetherian base `Spec R`, so
`Stacks.Chow.isRelativeCycle_compFamily_of_isNoetherian_dvr` applies. -/
theorem isRelativeCycle_compFamily_of_dvr_base {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (.of R)) [LocallyOfFiniteType g] [IsLocallyNoetherian Y] (r e : ℕ)
    {α : FamilyOfCycles f r} {β : FamilyOfCycles g e} (hα : IsRelativeCycle f r α)
    (hβ : IsRelativeCycle g e β) :
    IsRelativeCycle (f ≫ g) (r + e) (compFamily f g r e α β) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine isRelativeCycle_of_openCover (f ≫ g) (r + e) (compFamily f g r e α β)
    (ι := (k : Y.affineCover.I₀) × (pullback f (Y.affineCover.f k)).affineCover.I₀)
    (U := fun idx ↦ (pullback f (Y.affineCover.f idx.1)).affineCover.X idx.2)
    (fU := fun idx ↦ ((pullback f (Y.affineCover.f idx.1)).affineCover.f idx.2 ≫
      pullback.snd f (Y.affineCover.f idx.1)) ≫ Y.affineCover.f idx.1 ≫ g)
    (j := fun idx ↦ (pullback f (Y.affineCover.f idx.1)).affineCover.f idx.2 ≫
      pullback.fst f (Y.affineCover.f idx.1))
    (h := fun idx ↦ by
      simp only [Category.assoc]
      rw [← Category.assoc (pullback.fst f (Y.affineCover.f idx.1)) f g, pullback.condition,
        Category.assoc])
    (fun x ↦ ?_) (fun idx ↦ ?_)
  · obtain ⟨k, y, hy⟩ := Y.affineCover.exists_eq (f x)
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := Y.affineCover.f k) x y hy.symm
    obtain ⟨l, w, hw⟩ := (pullback f (Y.affineCover.f k)).affineCover.exists_eq z
    exact ⟨⟨k, l⟩, w, by rw [Scheme.Hom.comp_apply, hw, hz]⟩
  · obtain ⟨k, l⟩ := idx
    have : IsNoetherian (Y.affineCover.X k) := ⟨⟩
    have : IsLocallyNoetherian (pullback f (Y.affineCover.f k)) :=
      isLocallyNoetherian_of_isOpenImmersion (pullback.fst f (Y.affineCover.f k))
    have : IsNoetherian ((pullback f (Y.affineCover.f k)).affineCover.X l) := ⟨⟩
    rw [fiberCycleRestrict_compFamily f g
      ((pullback f (Y.affineCover.f k)).affineCover.f l ≫ pullback.snd f (Y.affineCover.f k))
      ((pullback f (Y.affineCover.f k)).affineCover.f l ≫ pullback.fst f (Y.affineCover.f k))
      (Y.affineCover.f k) (by simp only [Category.assoc, pullback.condition]) _ r e α β]
    exact isRelativeCycle_compFamily_of_isNoetherian_dvr _ _ r e
      (isRelativeCycle_restrictedFamily f _ _ (Y.affineCover.f k) _ r hα)
      (isRelativeCycle_restrictedFamily g _ (Y.affineCover.f k) (𝟙 _) (by simp) e hβ)

/-! ### Lemma 0H6R -/

/-- **Stacks Project, Lemma 0H6R.** Let `X --f--> Y --g--> S` be morphisms of schemes, both
locally of finite type, with `S` locally Noetherian, and let `r, e ≥ 0`. If `α` is a relative
`r`-cycle on `X/Y` and `β` is a relative `e`-cycle on `Y/S`, then the composition `α ∘ β` is a
relative `(r + e)`-cycle on `X/S`.

`Y` is locally Noetherian because it is locally of finite type over the locally Noetherian
scheme `S`, which is what makes the hypothesis on `α` meaningful. -/
@[stacks 0H6R]
theorem isRelativeCycle_compFamily {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] [IsLocallyNoetherian S] (r e : ℕ)
    (α : FamilyOfCycles f r) (β : FamilyOfCycles g e) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    IsRelativeCycle f r α → IsRelativeCycle g e β →
      IsRelativeCycle (f ≫ g) (r + e) (compFamily f g r e α β) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  intro hα hβ
  refine isRelativeCycle_compFamily_of_forall_dvr f g r e α β fun R _ _ _ c ↦ ?_
  have : IsLocallyNoetherian (pullback g c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g c)
  exact specializationCycle_eq_of_isRelativeCycle
    (pullback.snd f (pullback.fst g c) ≫ pullback.snd g c) (r + e)
    (isRelativeCycle_compFamily_of_dvr_base (pullback.snd f (pullback.fst g c))
      (pullback.snd g c) r e (isRelativeCycle_baseChangeFamily f (pullback.fst g c) r hα)
      (isRelativeCycle_baseChangeFamily g c e hβ))

/-- **The pairing of Stacks Project, Section 0H6Q.** The composition of families of cycles on
fibres, read as a pairing `z(X/Y, r) ⟶ z(Y/S, e) ⟶ z(X/S, r + e)` of the groups of relative
cycles. It is Lemma 0H6R that it lands in `z(X/S, r + e)`, and Tag 0H6I that it is additive in
each argument. -/
def compRelativeCycles {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] [IsLocallyNoetherian S] (r e : ℕ) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    relativeCycles f r →+ relativeCycles g e →+ relativeCycles (f ≫ g) (r + e) :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  { toFun := fun α ↦
      { toFun := fun β ↦ ⟨compFamily f g r e α.1 β.1,
          isRelativeCycle_compFamily f g r e α.1 β.1 α.2 β.2⟩
        map_zero' := Subtype.ext (compFamily_zero_right f g r e α.1)
        map_add' := fun β₁ β₂ ↦ Subtype.ext (compFamily_add_right f g r e α.1 β₁.1 β₂.1) }
    map_zero' := AddMonoidHom.ext fun β ↦ Subtype.ext (compFamily_zero_left f g r e β.1)
    map_add' := fun α₁ α₂ ↦ AddMonoidHom.ext fun β ↦
      Subtype.ext (compFamily_add_left f g r e α₁.1 α₂.1 β.1) }

/-- The underlying family of cycles of `compRelativeCycles f g r e α β` is the composition
`compFamily f g r e α β` of the underlying families of `α` and `β`. -/
@[simp]
theorem compRelativeCycles_val {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] [IsLocallyNoetherian S] (r e : ℕ)
    [IsLocallyNoetherian Y] (α : relativeCycles f r) (β : relativeCycles g e) :
    (compRelativeCycles f g r e α β).1 = compFamily f g r e α.1 β.1 :=
  rfl

end Stacks.Chow

end
