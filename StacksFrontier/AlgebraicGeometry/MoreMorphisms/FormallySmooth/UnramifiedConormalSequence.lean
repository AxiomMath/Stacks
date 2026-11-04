module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified morphism with formally smooth source

Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `S` and assume `Z` is formally
smooth over `S`. [Stacks, Tag 06B7] asserts that the canonical sequence

```
0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
```

of [Stacks, Tag 04FC] is **short** exact, the new content over [Stacks, Tag 04FC] being
injectivity of the first arrow.

The source's proof is: let `Z ⊂ Z'` be the universal first-order thickening of `Z` over `X`; the
sequence is identified with the conormal sequence of the immersion `i : Z ⟶ Z'`; formal
smoothness of `Z ⟶ S` provides, *locally on `Z'`*, a left inverse `Z' ⟶ Z` over `S`; hence the
sequence is locally split, and [Stacks, Tag 0474] gives left exactness.

This file proves the two steps of that proof: the local left inverse, and the local splitting it
yields on the arrow `h^*Ω_{X/S} ⟶ Ω_{Z/S}`. The *conclusion* of the tag — the first arrow
`𝒞_{Z/X} ⟶ h^*Ω_{X/S}`, the sequence it begins, and its short exactness — is
`Stacks.UnramifiedConormalSequence.conormalShortComplex_shortExact` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.UnramifiedConormalShortExact`,
which gets left exactness from [Stacks, Tag 06AA] rather than from the local splitting below.

## Main results

* `Stacks.UnramifiedConormalSequence.exists_localRetraction_of_formallySmooth`: for a universal
  first-order thickening `i : Z ⟶ Z'` of `h` over `X` with structure morphism `h' : Z' ⟶ X`, and
  `Z` formally smooth over `S`, every point of `Z` has an affine open neighbourhood `V` whose
  attached open `W ⊆ Z'` admits a morphism `g : W ⟶ V` over `S` left inverse to the restriction
  `j : V ⟶ W` of `i`. This is the source's "formal smoothness of `Z ⟶ S` gives a left inverse
  `Z' ⟶ Z` over `S` locally on `Z'`", and it is the only step using the formal smoothness
  hypothesis.
* `Stacks.UnramifiedConormalSequence.forall_exists_isSplitEpi_restrict_relativeDifferentialsMap`:
  consequently the second arrow `h^*Ω_{X/S} ⟶ Ω_{Z/S}` of the sequence — the canonical map of
  [Stacks, Tag 01UV] — restricts to a *split* epimorphism on a neighbourhood of every point of
  `Z`. This is the source's "hence the sequence is locally split".

## Route

The local left inverse is the lifting property of [Stacks, Tag 02H0] applied to a first-order
thickening of *affine* schemes. The affine thickening is produced by
`Stacks.Thickenings.UniversalFirstOrderThickening.ambientOpens`: an affine open `V ⊆ Z` has an
attached open `W ⊆ Z'` with `i^{-1}W = V`, the restricted morphism `j : V ⟶ W` is again a
first-order thickening ([Stacks, Tag 04FA]) and `W` is therefore affine, by
`Stacks.Thickenings.isAffine_of_isFirstOrderThickening`. Formal smoothness of `Z ⟶ S` lifts
`V ↪ Z` along `j` to `g' : W ⟶ Z` over `S`; since `j` is surjective on points and `g' ∘ j`
factors through `V`, the lift lands in `V` and gives `g : W ⟶ V`.

The splitting is then
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_of_retraction`
of [Stacks, Tag 0474], transported twice. First along the open immersions `V ↪ Z` and `W ↪ Z'`,
which is `Stacks.UnramifiedConormalSequence.isSplitEpi_restrict_of_localRetraction` below — the
analogue of
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction`
for an arbitrary structure morphism of the source, which is what the thickening forces here, the
structure morphism of `Z` over `S` being `h ≫ p` while that of `Z'` is `h' ≫ p`. Second along
`i`, by the composition law for canonical maps on differentials: `h = i ≫ h'`, so the canonical
map of `h` is the canonical map of `i` preceded by comparison isomorphisms and by the pullback
along `i` of the canonical map of `h'`, which is an isomorphism by [Stacks, Tag 04FB],
`Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap`. Split epimorphy is unaffected by
the isomorphisms.

## What [Stacks, Tag 06B7] asserts that is not proved here

**Left exactness — the assertion of the tag — is not proved here.** It is proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.UnramifiedConormalShortExact`, by the
route the source's own proof avoids: the first arrow `𝒞_{Z/X} ⟶ h^*Ω_{X/S}` is the conormal
differential of [Stacks, Tag 01UZ] of the inclusion `i : Z ⟶ Z'` read through [Stacks, Tag 04FB],
and short exactness of the resulting sequence is [Stacks, Tag 06AA] for the immersion `i` over
`h' ≫ p`. The local splitting proved below is therefore not used by that file, and the two are
independent readings of the source's proof.

`StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic` states [Stacks, Tag 0474] only on its
second arrow, and that is the half of it used here. Nothing below is true by definition: the
statements are about the canonical map of [Stacks, Tag 01UV], characterised by a universal
property, and assert a splitting of it rather than merely its surjectivity. Surjectivity itself
is not a weaker known statement here either: [Stacks, Tag 01UZ] gives it for a morphism which is
surjective on stalks, which a formally unramified morphism need not be, so a split epimorphism
locally is strictly more than the library knows about that arrow otherwise.

## References

* [Stacks Project, Tag 06B7](https://stacks.math.columbia.edu/tag/06B7)
* [Stacks Project, Tag 04FC](https://stacks.math.columbia.edu/tag/04FC), the sequence.
* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474), the splitting criterion.
* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA), restriction of a
  universal first-order thickening to an open.
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB), the identification of
  the middle term.
* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0), formal smoothness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open Stacks.Thickenings

universe u

namespace Stacks.UnramifiedConormalSequence

/-- A split epimorphism preceded by an isomorphism is a split epimorphism. -/
private theorem isSplitEpi_of_isIso_comp {C : Type*} [Category* C] {A B D : C}
    (a : A ⟶ B) {f : B ⟶ D} [IsIso a] (hf : IsSplitEpi (a ≫ f)) : IsSplitEpi f := by
  rw [show f = inv a ≫ (a ≫ f) by simp]
  infer_instance

/-- A split epimorphism followed by an isomorphism is a split epimorphism. -/
private theorem isSplitEpi_of_comp_isIso {C : Type*} [Category* C] {A B D : C}
    {f : A ⟶ B} (b : B ⟶ D) [IsIso b] (hf : IsSplitEpi (f ≫ b)) : IsSplitEpi f := by
  rw [show f = (f ≫ b) ≫ inv b by simp]
  infer_instance

variable {Z X S : Scheme.{u}}

/-! ### A local left inverse out of formal smoothness -/

/-- **A local left inverse `Z' ⟶ Z` over `S`, from formal smoothness of `Z` over `S`.** Let
`i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X` be a universal first-order thickening of
`h : Z ⟶ X`, let `p : X ⟶ S`, and assume `Z` is formally smooth over `S`, that is
`h ≫ p : Z ⟶ S` has the lifting property of [Stacks, Tag 02H0]. Then every point `z` of `Z` has
an open neighbourhood `V` and an open `W ⊆ Z'` such that `i` restricts to `j : V ⟶ W` and `j`
admits a left inverse `g : W ⟶ V` over `S`.

This is the step of the proof of [Stacks, Tag 06B7] reading "by formal smoothness of `Z` over `S`
there exists, after replacing `Z'` by an open neighbourhood, a left inverse `Z' ⟶ Z` over `S`".
`V` is any affine open neighbourhood of `z` and `W` is the open of `Z'` attached to it by
`Stacks.Thickenings.UniversalFirstOrderThickening.ambientOpens`, which is affine because
`V ⟶ W` is a first-order thickening of `V`; the lifting property applies to that affine
first-order thickening, and the resulting lift `W ⟶ Z` factors through `V` because `V ⟶ W` is
surjective on points. -/
@[stacks 06B7 "the step of the proof using formal smoothness of Z over S: locally on the
universal first-order thickening Z' there is a left inverse Z' ⟶ Z over S"]
theorem exists_localRetraction_of_formallySmooth {Z' : Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ Z'}
    {h' : Z' ⟶ X} (hi : Stacks.Thickenings.IsUniversalFirstOrderThickening h i h') (p : X ⟶ S)
    (hZ : FormallySmooth (h ≫ p)) (z : Z) :
    ∃ (V : Z.Opens) (W : Z'.Opens) (j : V.toScheme ⟶ W.toScheme)
      (g : W.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ W.ι ∧
        j ≫ g = 𝟙 V.toScheme ∧ g ≫ (V.ι ≫ (h ≫ p)) = W.ι ≫ (h' ≫ p) := by
  let t : Stacks.Thickenings.UniversalFirstOrderThickening h := ⟨Z', i, h', hi⟩
  obtain ⟨V, hVaff, hzV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Z.Opens) from trivial)
  have hWV : i ⁻¹ᵁ t.ambientOpens V = V := t.preimage_ambientOpens V
  have hjι : i.resLE (t.ambientOpens V) V hWV.ge ≫ (t.ambientOpens V).ι = V.ι ≫ i :=
    Scheme.Hom.resLE_comp_ι i hWV.ge
  have hjfirst : IsFirstOrderThickening (i.resLE (t.ambientOpens V) V hWV.ge) :=
    (t.isUniversal_resLE (U := ⊤) le_top).isFirstOrderThickening
  have : IsAffine V.toScheme := hVaff
  have hWaff : IsAffine (t.ambientOpens V).toScheme :=
    Stacks.Thickenings.isAffine_of_isFirstOrderThickening hjfirst
  have hcomm : V.ι ≫ (h ≫ p) =
      i.resLE (t.ambientOpens V) V hWV.ge ≫ ((t.ambientOpens V).ι ≫ h' ≫ p) := by
    symm
    rw [← Category.assoc (i.resLE (t.ambientOpens V) V hWV.ge) (t.ambientOpens V).ι, hjι,
      Category.assoc, ← Category.assoc i h' p, hi.inclusion_toBase]
  obtain ⟨g', hg'S, hjg'⟩ := hZ hVaff hWaff (i.resLE (t.ambientOpens V) V hWV.ge) hjfirst V.ι
    ((t.ambientOpens V).ι ≫ h' ≫ p) hcomm
  have hrange : Set.range g'.base ⊆ Set.range V.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hjfirst.isThickening.2 x
    refine ⟨x', ?_⟩
    have heq := congrArg (fun f : V.toScheme ⟶ Z => f.base x') hjg'
    rw [← hx']
    simpa using heq.symm
  have hgι : IsOpenImmersion.lift V.ι g' hrange ≫ V.ι = g' :=
    IsOpenImmersion.lift_fac V.ι g' hrange
  refine ⟨V, t.ambientOpens V, i.resLE (t.ambientOpens V) V hWV.ge,
    IsOpenImmersion.lift V.ι g' hrange, hzV, hjι.symm, ?_, ?_⟩
  · refine (cancel_mono V.ι).1 ?_
    rw [Category.assoc, hgι, hjg', Category.id_comp]
  · rw [← Category.assoc, hgι]
    exact hg'S

/-! ### The local splitting of the second arrow -/

/-- The canonical map of a composite of squares over `𝟙 S` is the composite of the canonical maps,
up to the comparison isomorphisms. -/
private theorem relativeDifferentialsMap_comp_id {X' X'' : Scheme.{u}} (f : X' ⟶ X)
    (f' : X'' ⟶ X') {k : X'' ⟶ X} (hk : f' ≫ f = k) (p : X ⟶ S) (p' : X' ⟶ S) (p'' : X'' ⟶ S)
    (h : f ≫ p = p' ≫ 𝟙 S) (h' : f' ≫ p' = p'' ≫ 𝟙 S) (h'' : k ≫ p = p'' ≫ 𝟙 S) :
    relativeDifferentialsMap k p p'' (𝟙 S) h'' =
      (Scheme.Modules.pullbackCongr hk).inv.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentials p) ≫
          (Scheme.Modules.pullback f').map (relativeDifferentialsMap f p p' (𝟙 S) h) ≫
            relativeDifferentialsMap f' p' p'' (𝟙 S) h' :=
  ((((isRelativeDifferentialsMap_relativeDifferentialsMap f p p' (𝟙 S) h).comp
    (isRelativeDifferentialsMap_relativeDifferentialsMap f' p' p'' (𝟙 S) h')).congr_left
      hk).eq_relativeDifferentialsMap (𝟙 S) h'').symm

/-- **A left inverse of `i` over an open splits the canonical map `i^*Ω_{Z'/S} ⟶ Ω_{Z/S}` over
that open.** This is
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction`
with the structure morphism `pz : Z ⟶ S` of the source left arbitrary — only required to satisfy
`i ≫ q = pz` — instead of being the composite `i ≫ q` on the nose. Both forms are needed: a
universal first-order thickening presents the structure morphism of `Z` over `S` as `h ≫ p` and
not as `i ≫ (h' ≫ p)`, and `Ω_{Z/S}` is the relative differentials of the former.

The proof is that of the quoted statement: the canonical map of `V ↪ Z ⟶ Z'` is computed twice by
functoriality in the source morphism, once through `W` — where the factors other than the
canonical map of `j`, which is a split epimorphism by [Stacks, Tag 0474], are isomorphisms — and
once through `Z`, where the factors other than the restriction to `V` of the canonical map of `i`
are isomorphisms. -/
theorem isSplitEpi_restrict_of_localRetraction {Z' : Scheme.{u}} (i : Z ⟶ Z') (q : Z' ⟶ S)
    (pz : Z ⟶ S) (hpz : i ≫ q = pz) (V : Z.Opens) (W : Z'.Opens)
    (j : V.toScheme ⟶ W.toScheme) (hfac : V.ι ≫ i = j ≫ W.ι) (g : W.toScheme ⟶ V.toScheme)
    (hg : j ≫ g = 𝟙 V.toScheme) (hgS : g ≫ (V.ι ≫ pz) = W.ι ≫ q) :
    IsSplitEpi ((Scheme.Modules.pullback V.ι).map
      (relativeDifferentialsMap i q pz (𝟙 S) (hpz.trans (Category.comp_id pz).symm))) := by
  have hq' : j ≫ (W.ι ≫ q) = V.ι ≫ pz := by
    rw [← Category.assoc, ← hfac, Category.assoc, hpz]
  have hj := Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_of_retraction
    j (W.ι ≫ q) (V.ι ≫ pz) hq' g hg hgS
  have hVi : (V.ι ≫ i) ≫ q = (V.ι ≫ pz) ≫ 𝟙 S := by
    rw [Category.assoc, hpz, Category.comp_id]
  have hA : IsSplitEpi (relativeDifferentialsMap (V.ι ≫ i) q (V.ι ≫ pz) (𝟙 S) hVi) := by
    rw [relativeDifferentialsMap_comp_id W.ι j hfac.symm q (W.ι ≫ q) (V.ι ≫ pz) (by simp)
      (hq'.trans (Category.comp_id _).symm) hVi]
    infer_instance
  rw [relativeDifferentialsMap_comp_id i V.ι rfl q pz (V.ι ≫ pz)
    (hpz.trans (Category.comp_id pz).symm) (by simp) hVi] at hA
  exact isSplitEpi_of_comp_isIso _ (isSplitEpi_of_isIso_comp _ hA)

/-- **[Stacks, Tag 06B7]: the conormal sequence of a formally unramified morphism with formally
smooth source is locally split.** Let `h : Z ⟶ X` be formally unramified, let `p : X ⟶ S`, and
assume `Z` is formally smooth over `S`. Then the second arrow `h^*Ω_{X/S} ⟶ Ω_{Z/S}` of the
sequence of [Stacks, Tag 04FC] — the canonical map of [Stacks, Tag 01UV] — restricts to a *split*
epimorphism on a neighbourhood of every point of `Z`.

A split epimorphism being an epimorphism, this contains local surjectivity of that arrow, which
[Stacks, Tag 01UZ] supplies only for a morphism surjective on stalks; splitness is what formal
smoothness buys, and it is the source's "hence the sequence is locally split". Left exactness of
the sequence, which is the assertion of the tag, is not proved here; it is
`Stacks.UnramifiedConormalSequence.conormalShortComplex_shortExact` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.UnramifiedConormalShortExact`. -/
@[stacks 06B7 "the conclusion of the source's proof before Tag 0474 is invoked: the sequence is
locally split, i.e. the second arrow h^*Ω_{X/S} ⟶ Ω_{Z/S} restricts to a split epimorphism on a
neighbourhood of every point of Z. Left exactness, the assertion of the tag, is not this
declaration: it is conormalShortComplex_shortExact of
StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.UnramifiedConormalShortExact"]
theorem forall_exists_isSplitEpi_restrict_relativeDifferentialsMap (h : Z ⟶ X)
    [FormallyUnramified h] (p : X ⟶ S) (hZ : FormallySmooth (h ≫ p)) (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧ IsSplitEpi ((Scheme.Modules.pullback V.ι).map
      (relativeDifferentialsMap h p (h ≫ p) (𝟙 S)
        (show h ≫ p = (h ≫ p) ≫ 𝟙 S by simp))) := by
  obtain ⟨V, W, j, g, hzV, hfac, hg, hgS⟩ := exists_localRetraction_of_formallySmooth
    (universalFirstOrderThickening h).isUniversal p hZ z
  refine ⟨V, hzV, ?_⟩
  have hpz : (universalFirstOrderThickening h).inclusion ≫
      ((universalFirstOrderThickening h).toBase ≫ p) = h ≫ p := by
    rw [← Category.assoc, (universalFirstOrderThickening h).isUniversal.inclusion_toBase]
  have key := isSplitEpi_restrict_of_localRetraction (universalFirstOrderThickening h).inclusion
    ((universalFirstOrderThickening h).toBase ≫ p) (h ≫ p) hpz V W j hfac g hg hgS
  have e := relativeDifferentialsMap_comp_id (universalFirstOrderThickening h).toBase
    (universalFirstOrderThickening h).inclusion
    (universalFirstOrderThickening h).isUniversal.inclusion_toBase p
    ((universalFirstOrderThickening h).toBase ≫ p) (h ≫ p) (by simp)
    (hpz.trans (Category.comp_id _).symm) (by simp)
  have hiso : IsIso ((Scheme.Modules.pullback (universalFirstOrderThickening h).inclusion).map
      (relativeDifferentialsMap (universalFirstOrderThickening h).toBase p
        ((universalFirstOrderThickening h).toBase ≫ p) (𝟙 S)
        (show (universalFirstOrderThickening h).toBase ≫ p =
          ((universalFirstOrderThickening h).toBase ≫ p) ≫ 𝟙 S by simp))) :=
    isIso_thickeningRelativeDifferentialsMap (universalFirstOrderThickening h).isUniversal p
  rw [e, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end Stacks.UnramifiedConormalSequence

end
