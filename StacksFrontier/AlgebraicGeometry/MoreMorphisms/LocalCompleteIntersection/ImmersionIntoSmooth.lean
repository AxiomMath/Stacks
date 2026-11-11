module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ZariskiLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Immersions of opens of a local complete intersection morphism into a smooth scheme

Let `f : X ⟶ S` be a local complete intersection morphism, let `P` be smooth over `S`, let
`U ⊆ X` be open and let `i : U ⟶ P` be an immersion over `S`. Then `i` is a Koszul-regular
immersion: the Koszul-regular factorization asked for by Stacks 069F is independent of the
factorization chosen. This is **Stacks 069G**.

## Main definitions

* `AlgebraicGeometry.KoszulRegularCompSmooth`: the Koszul case of Stacks 0693, that a
  Koszul-regular immersion stays Koszul-regular after composing with a smooth morphism of the
  target.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_eq`: Koszul-regularity
  of an immersion transports along an equality of morphisms.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isOpenImmersion`: an
  open immersion is a Koszul-regular immersion.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_nhds`:
  Koszul-regularity of a closed immersion is local on the source.
* `AlgebraicGeometry.isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism`:
  Stacks 069G relative to `AlgebraicGeometry.KoszulRegularCompSmooth`. Untagged; the
  unconditional statement that carries `@[stacks 069G]` is
  `AlgebraicGeometry.isKoszulRegularImmersion_of_koszul` in
  the module `LocalCompleteIntersectionAffine` under
  `StacksDraft.AlgebraicGeometry.Descent.LocalOnSourceTopologies`.

## Implementation notes

The Koszul case of Stacks 0693 — a Koszul-regular immersion `a` followed by a smooth `p`, with
`a ≫ p` an immersion, has `a ≫ p` Koszul-regular — is the second half of the proof of
Stacks 069E, of which Stacks 069G is a restatement, and the argument below cannot do without it.
It is proved in this library, as
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence`, but that
module imports this one, so here it enters as the explicit hypothesis
`KoszulRegularCompSmooth`, whose shape is that of the converse Stacks 067S already available as
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_comp_of_smooth`. The
unconditional statement of Stacks 069G, where the hypothesis is gone and the tag sits, is
`AlgebraicGeometry.isKoszulRegularImmersion_of_koszul` in
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine`.

Given the hypothesis the proof is the one indicated by Stacks: near a point of `U` the local
complete intersection property supplies a second factorization, through a Koszul-regular
immersion `i' : W ⟶ P'` with `P'` smooth over `S`. Over the open `V = U ∩ W` the two immersions
into `P` and `P'` induce one into the fibre product `P ×_S P'`, which is Koszul-regular by
Stacks 067S over the projection to `P'` — a base change of the smooth structure morphism of `P`
— and the hypothesis then transfers Koszul-regularity to `V ⟶ P` along the projection to `P`, a
base change of the smooth structure morphism of `P'`.

That gives Koszul-regularity only near each point of the source, so the conclusion needs
Koszul-regularity to be local on the source. For a *closed* immersion `j : Z ⟶ Y` this follows
from locality on the target, because an open `V ⊆ Z` is the preimage of the open complement of
`j '' Vᶜ`: those complements, together with the complement of the closed `Set.range j`, cover `Y`.
The general immersion `i` is reduced to this case by factoring it as the closed immersion
`i.liftCoborder` into `i.coborderRange` followed by an open immersion, and the whole local
argument is run with `i.coborderRange` — itself smooth over `S` — as the smooth target.

Passing between an immersion and its restriction over an open is also Stacks 067S, applied to the
inclusion of the open, which is smooth.

## References

* [The Stacks Project, Lemma 37.62.3 (069G)](https://stacks.math.columbia.edu/tag/069G)
* [The Stacks Project, Lemma 37.62.1 (069E)](https://stacks.math.columbia.edu/tag/069E)
* [The Stacks Project, Definition 37.62.2 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 31.23.12 (0693)](https://stacks.math.columbia.edu/tag/0693)
* [The Stacks Project, Lemma 31.23.9 (067S)](https://stacks.math.columbia.edu/tag/067S)
* [The Stacks Project, Lemma 31.23.11 (067U)](https://stacks.math.columbia.edu/tag/067U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Koszul-regularity transports along an equality of immersions. The instance argument of
`IsKoszulRegularImmersion` makes the corresponding rewrite fail on the motive. -/
theorem isKoszulRegularImmersion_of_eq {Z X : Scheme.{u}} {a b : Z ⟶ X} [IsImmersion a]
    [IsImmersion b] (h : a = b) (ha : IsKoszulRegularImmersion a) : IsKoszulRegularImmersion b := by
  subst h; exact ha


/-- `H₁`-regularity transports along an equality of immersions. -/
theorem isH1RegularImmersion_of_eq {A B : Scheme.{u}} {a b : A ⟶ B} [IsImmersion a]
    [IsImmersion b] (h : a = b) (ha : IsH1RegularImmersion a) : IsH1RegularImmersion b := by
  subst h; exact ha
/-- An open immersion of schemes is a Koszul-regular immersion: it is an immersion between two
schemes smooth over its target, hence regular by Stacks 067U and Koszul-regular by Stacks 063K. -/
theorem isKoszulRegularImmersion_of_isOpenImmersion {A B : Scheme.{u}} (e : A ⟶ B)
    [IsOpenImmersion e] : IsKoszulRegularImmersion e :=
  isKoszulRegularImmersion_of_isRegularImmersion e
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth e (𝟙 B))

/-- If `a ≫ p` equals a Koszul-regular immersion `b` and `p` is smooth, then `a` is
Koszul-regular (Stacks 067S). -/
private theorem isKoszulRegularImmersion_of_comp_eq_of_smooth {Y X T : Scheme.{u}} (a : Y ⟶ X)
    (p : X ⟶ T) {b : Y ⟶ T} [IsImmersion a] [Smooth p] [IsImmersion (a ≫ p)] [IsImmersion b]
    (h : a ≫ p = b) (hb : IsKoszulRegularImmersion b) : IsKoszulRegularImmersion a := by
  subst h; exact isKoszulRegularImmersion_of_comp_of_smooth a p hb

/-- Koszul-regularity of an immersion restricted over an open of the target is inherited from
Koszul-regularity of its restriction to the preimage of that open: the two differ by the
inclusion of the open, which is smooth, so Stacks 067S applies. -/
private theorem isKoszulRegularImmersion_resLE_of_comp {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsImmersion j] (W : Y.Opens) (V : Z.Opens) (hVW : j ⁻¹ᵁ W = V)
    (h : IsKoszulRegularImmersion (V.ι ≫ j)) :
    IsKoszulRegularImmersion (j.resLE W (j ⁻¹ᵁ W) le_rfl) := by
  subst hVW
  exact isKoszulRegularImmersion_of_comp_eq_of_smooth _ W.ι (Scheme.Hom.resLE_comp_ι j le_rfl) h

/-- **Koszul-regularity of a closed immersion is local on the source.** If every point of the
source of a closed immersion `j : Z ⟶ Y` has an open neighbourhood `V` with `V ⟶ Y`
Koszul-regular, then `j` is Koszul-regular. -/
theorem isKoszulRegularImmersion_of_nhds {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j]
    (h : ∀ x : Z, ∃ V : Z.Opens, x ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ j)) :
    IsKoszulRegularImmersion j := by
  rcases isEmpty_or_nonempty Z with _ | hZ
  · exact isKoszulRegularImmersion_of_isOpenImmersion j
  choose V hxV hreg using h
  have hclosed : ∀ x : Z, IsClosed (j.base '' ((V x : Set Z)ᶜ)) := fun x =>
    j.isClosedEmbedding.isClosedMap _ (V x).isOpen.isClosed_compl
  let W : Z → Y.Opens := fun x => ⟨(j.base '' ((V x : Set Z)ᶜ))ᶜ, (hclosed x).isOpen_compl⟩
  have hpre : ∀ x : Z, j ⁻¹ᵁ W x = V x := by
    intro x
    ext z
    change j.base z ∉ j.base '' ((V x : Set Z)ᶜ) ↔ z ∈ (V x : Set Z)
    refine ⟨fun hz => by_contra fun hzV => hz ⟨z, hzV, rfl⟩, fun hz hmem => ?_⟩
    obtain ⟨z', hz', heq⟩ := hmem
    exact hz' (j.isClosedEmbedding.injective heq ▸ hz)
  have hcover : iSup W = ⊤ := by
    refine le_antisymm le_top fun y _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range j.base
    · obtain ⟨x, rfl⟩ := hy
      exact ⟨x, (hpre x).ge (hxV x)⟩
    · exact ⟨hZ.some, fun hmem => hy ⟨hmem.choose, hmem.choose_spec.2⟩⟩
  exact isKoszulRegularImmersion_of_resLE j W hcover fun x =>
    isKoszulRegularImmersion_resLE_of_comp j (W x) (V x) (hpre x) (hreg x)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- **The Koszul case of Stacks 0693.** In a commutative triangle `Y ⟶ X ⟶ T` of schemes with
`X ⟶ T` smooth and both `Y ⟶ X` and `Y ⟶ T` immersions, a Koszul-regular `Y ⟶ X` has
Koszul-regular composite `Y ⟶ T`. It is the converse of Stacks 067S. -/
def KoszulRegularCompSmooth : Prop :=
  ∀ {Y X T : Scheme.{u}} (a : Y ⟶ X) (p : X ⟶ T) [IsImmersion a] [Smooth p]
    [IsImmersion (a ≫ p)], IsKoszulRegularImmersion a → IsKoszulRegularImmersion (a ≫ p)

/-- Near each point of the source, an immersion over `S` of an open of the source of a local
complete intersection morphism into a scheme smooth over `S` is Koszul-regular. -/
private theorem exists_nhd_isKoszulRegularImmersion (hcompSmooth : KoszulRegularCompSmooth.{u})
    {X S Q : Scheme.{u}} {f : X ⟶ S} {ρ : Q ⟶ S} [Smooth ρ] {U : X.Opens}
    (j : U.toScheme ⟶ Q) [IsImmersion j] (hf : IsLocalCompleteIntersectionMorphism f)
    (hj : U.ι ≫ f = j ≫ ρ) (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧ IsKoszulRegularImmersion (V.ι ≫ j) := by
  obtain ⟨-, W, hxW, P', i', π', hi', hkos, hπ', hfac⟩ := hf (U.ι x)
  let := hi'
  let := hπ'
  refine ⟨U.ι ⁻¹ᵁ W, hxW, ?_⟩
  set V : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hkopen : IsOpenImmersion (U.ι.resLE W V le_rfl) := by
    delta Scheme.Hom.resLE; infer_instance
  set k : V.toScheme ⟶ W.toScheme := U.ι.resLE W V le_rfl
  have hk : k ≫ W.ι = V.ι ≫ U.ι := Scheme.Hom.resLE_comp_ι U.ι le_rfl
  have hab : (V.ι ≫ j) ≫ ρ = (k ≫ i') ≫ π' :=
    calc (V.ι ≫ j) ≫ ρ = V.ι ≫ j ≫ ρ := Category.assoc _ _ _
      _ = V.ι ≫ U.ι ≫ f := by rw [← hj]
      _ = (V.ι ≫ U.ι) ≫ f := (Category.assoc _ _ _).symm
      _ = (k ≫ W.ι) ≫ f := by rw [hk]
      _ = k ≫ W.ι ≫ f := Category.assoc _ _ _
      _ = k ≫ i' ≫ π' := by rw [hfac]
      _ = (k ≫ i') ≫ π' := (Category.assoc _ _ _).symm
  have hbkos : IsKoszulRegularImmersion (k ≫ i') :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp k i'
      (isKoszulRegularImmersion_of_isOpenImmersion k) hkos
  let c : V.toScheme ⟶ pullback ρ π' := pullback.lift (V.ι ≫ j) (k ≫ i') hab
  have hcf : c ≫ pullback.fst ρ π' = V.ι ≫ j := pullback.lift_fst _ _ _
  have hcs : c ≫ pullback.snd ρ π' = k ≫ i' := pullback.lift_snd _ _ _
  have hcsimm : IsImmersion (c ≫ pullback.snd ρ π') := by rw [hcs]; infer_instance
  have hcimm : IsImmersion c := IsImmersion.of_comp c (pullback.snd ρ π')
  have hcfimm : IsImmersion (c ≫ pullback.fst ρ π') := by rw [hcf]; infer_instance
  have hckos : IsKoszulRegularImmersion c :=
    isKoszulRegularImmersion_of_comp_eq_of_smooth c (pullback.snd ρ π') hcs hbkos
  exact isKoszulRegularImmersion_of_eq hcf
    (hcompSmooth c (pullback.fst ρ π') hckos)

/-- Let `f : X ⟶ S` be a local complete intersection morphism, let `π : P ⟶ S` be smooth, let
`U ⊆ X` be open and let `i : U ⟶ P` be an immersion over `S`. Then `i` is a Koszul-regular
immersion, provided the Koszul case of Stacks 0693.

This is the form of Stacks 069G relative to `KoszulRegularCompSmooth`, and it is deliberately
untagged: a declaration taking a stand-in for part of a tag's content must not carry that tag.
The hypothesis is discharged by
`AlgebraicGeometry.koszulRegularCompSmooth` in
the module `LocalCompleteIntersection.ImmersionIntoSmooth` under
`StacksDraft.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent`,
and the resulting unconditional statement, which is where `@[stacks 069G]` sits, is
`AlgebraicGeometry.isKoszulRegularImmersion_of_koszul` in
`LocalCompleteIntersectionAffine.lean:122` in the directory
`StacksFrontier/AlgebraicGeometry/Descent/LocalOnSourceTopologies/`.
Both live downstream of this module, which is why the tag cannot be here: the proof of the Koszul
case of Stacks 0693,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence`, imports
this module. -/
theorem isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism
    (hcompSmooth : KoszulRegularCompSmooth.{u}) {X S P : Scheme.{u}} (f : X ⟶ S) (π : P ⟶ S)
    [Smooth π] (U : X.Opens) (i : U.toScheme ⟶ P) [IsImmersion i]
    (hf : IsLocalCompleteIntersectionMorphism f) (hi : U.ι ≫ f = i ≫ π) :
    IsKoszulRegularImmersion i := by
  have hjf : U.ι ≫ f = i.liftCoborder ≫ (i.coborderRange.ι ≫ π) := by
    rw [← Category.assoc, i.liftCoborder_ι]; exact hi
  have hj : IsKoszulRegularImmersion i.liftCoborder :=
    isKoszulRegularImmersion_of_nhds i.liftCoborder fun x =>
      exists_nhd_isKoszulRegularImmersion hcompSmooth i.liftCoborder hf hjf x
  exact isKoszulRegularImmersion_of_eq i.liftCoborder_ι
    (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp i.liftCoborder i.coborderRange.ι hj
      (isKoszulRegularImmersion_of_isOpenImmersion i.coborderRange.ι))

end AlgebraicGeometry

end
