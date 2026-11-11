module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOverField

/-!
# `j^! ω_Y^•` is normalized relative to `ω_S^•`, for any upper-shriek formalism

Let `(S, ω_S^•)` be as in Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a morphism of
schemes of finite type over `S`, and let `ω_Y^•` be normalized relative to `ω_S^•` and a
covering `𝒱` of `Y`. Then `f^!ω_Y^•` is normalized relative to `ω_S^•` and any covering `𝒰` of
`X` whose members `f` carries into members of `𝒱`. For `f = j` an open immersion this is the
step of [Stacks, Tag 0AUC] that makes `ω_Y^•|_X = j^!ω_Y^•` a second normalized structure on
`X`.

Normalization here is the covering-indexed notion `Stacks.Duality.Normalized` of the text of
[Stacks, Tag 0AU5], and the statement holds for every upper-shriek formalism
`A : Stacks.Duality.UpperShriek 𝒟`, as defined in
`StacksFrontier/AlgebraicGeometry/Duality/NormalizedDualizingTransitivity.lean`.

[Stacks, Tag 0AUC] itself, for the upper shriek functors of Nagata compactifications, is
`Stacks.Duality.NormalizedOnOpens.isoDerivedRestrictNagata` and
`Stacks.Duality.NormalizedOnOpens.existsUnique_iso_shriekOfIsOpenImmersion_nagata` in
`StacksFrontier/AlgebraicGeometry/Duality/NormalizedOnOpensOpenImmersion.lean`; the uniqueness
[Stacks, Tag 0AU7] it rests on is `Stacks.Duality.Normalized.existsUnique_iso_nagata`.

## Main definitions

* `Stacks.Duality.Normalized.restrictOverBase` — `f^!ω_Y^•` is normalized relative to `ω_S^•`.

## Main results

* `Stacks.Duality.UpperShriek.restrictCompare_symm` — conjugating an inverse comparison is the
  inverse of conjugating the comparison.
* `Stacks.Duality.Normalized.transport_localIso_eq` — the transported normalizations of
  `ω_Y^•` agree on an overlap of `X`: the cocycle condition of the proof of [Stacks, Tag 0AUB],
  pulled back to `X`.
* `Stacks.Duality.exists_normalizedIso_restrict_of_openImmersion` — for a formalism in which
  complexes normalized on a fixed covering are unique, `ω_X^• ≅ j^!ω_Y^•` compatibly with the
  normalizations.

## Implementation notes

*The shape of the argument.* Each member `U_k` of the covering of `X` gets the normalization
`(U_k → X)^!f^!ω_Y^• ≅ (U_k → Y)^!ω_Y^• ≅ (U_k → S)^!ω_S^•`, the first comparison being
[Stacks, Tag 0ATX] and the second the transport along `U_k → V_{idx k}` of the normalization
of `ω_Y^•`, which is the map `p_{ki}^!ω_S^• → (f'_{ki})^!ω_Y^•` of the proof of
[Stacks, Tag 0AUB]. The compatibility on overlaps splits by
`Stacks.Duality.UpperShriek.restrictLocalIso_trans` into the coherence [Stacks, Tag 0ATY] for
the first halves — that is `Stacks.Duality.restrictLocalIso_upperShriekLocalIso` — and the
cocycle condition for the second (`Stacks.Duality.Normalized.transport_localIso_eq`).

*Why an arbitrary morphism.* Nothing in the argument uses more than shriekability of `f`, so
`Stacks.Duality.Normalized.restrictOverBase` is stated for an arbitrary morphism of finite-type
schemes over the base. What an open immersion adds is the reading of `j^!` as restriction,
[Stacks, Tag 0AU0].

*What is reused.* The comparison `(f^!L)|_U ≅ (U → Y)^!L` of [Stacks, Tag 0ATX] and its
compatibility with further restriction are already available, as
`Stacks.Duality.upperShriekLocalIso` and
`Stacks.Duality.restrictLocalIso_upperShriekLocalIso` in
`StacksFrontier/AlgebraicGeometry/Duality/DualizingModuleOverField.lean`, stated there for the
structure morphism of a separated scheme over the base; read at `f : X ⟶ Y` they are exactly
the first half of each normalization below, so nothing of that is restated here. The declaration
`Stacks.Duality.normalizedUpperShriek` is the same statement packaged as a
`Stacks.Duality.Normalized` relative to `L`; it is not used below only because its covering
would have to be presented as `Stacks.Duality.SeparatedCovering.overMid`, whose fields are
definitionally but not syntactically the given covering, which stops the rewrites.

*The compatible coverings.* As in [Stacks, Tag 0AUB], the covering `𝒰` of `X` and the
covering `𝒱` of `Y` come with an index map `idx` and the containments
`𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k)`; these are the `U_{ji}` of the source's proof. Nothing here chooses
a covering, so no compactification and no Nagata theorem enter.

*Why the transports are written out.* The compatibility proofs rewrite with
`Stacks.Duality.UpperShriek.restrictCompare_transport` and
`Stacks.Duality.UpperShriek.transport_eq_transport`, which match on the head symbol
`UpperShriek.transport`; abbreviating a transport behind a definition hides that head and the
rewrites stop firing. The transports therefore appear in full, as they do in the proof of
[Stacks, Tag 0AUB].

## References

* [Stacks Project, Tag 0AUC](https://stacks.math.columbia.edu/tag/0AUC)
* [Stacks Project, Tag 0AU4](https://stacks.math.columbia.edu/tag/0AU4)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v' w w'

namespace Stacks.Duality

namespace UpperShriek

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] (A : UpperShriek 𝒟)

/-- Conjugating the inverse of a comparison along `r` is the inverse of conjugating the
comparison: `Stacks.Duality.UpperShriek.restrictCompare` is a conjugation, so it commutes with
`Iso.symm` once the two sides are exchanged. -/
theorem restrictCompare_symm {W' W T Z : Scheme.{u}} {r : W' ⟶ W} {m : W ⟶ T} {n : W ⟶ Z}
    {m' : W' ⟶ T} {n' : W' ⟶ Z} (hrm : r ≫ m = m') (hrn : r ≫ n = n') (hr : IsShriekable r)
    (hm : IsShriekable m) (hn : IsShriekable n) (hm' : IsShriekable m')
    (hn' : IsShriekable n') {ω : 𝒟 T} {L : 𝒟 Z}
    (Θ : (A.shriek m hm).obj ω ≅ (A.shriek n hn).obj L) :
    A.restrictCompare hrn hrm hr hn hm hn' hm' Θ.symm =
      (A.restrictCompare hrm hrn hr hm hn hm' hn' Θ).symm :=
  Iso.ext (by simp [restrictCompare])

end UpperShriek

namespace Normalized

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]
  {A : UpperShriek 𝒟} {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  (hpe : f ≫ q = p)
  (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q) {ωS : 𝒟 S}
  {ι : Type w} {J : Type w'} {𝒰 : SeparatedCovering p ι} {𝒱 : SeparatedCovering q J}
  (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k)) (𝒩Y : Normalized A hq ωS 𝒱)

/-- **The cocycle condition for the `β_j`, pulled back to `X`.** On an overlap
`W = U_k ∩ U_{k'}` the two transports of the normalizations of `ω_Y^•` — one through
`V_{idx k}`, one through `V_{idx k'}` — agree as isomorphisms
`(W → S)^!ω_S^• ≅ (W → Y)^!ω_Y^•`.

Both factor through the overlap `V_{idx k} ∩ V_{idx k'}` of the two members of `𝒱`, where the
compatibility `Stacks.Duality.Normalized.compat` of the normalizations of `ω_Y^•` applies; that
the transports restrict compatibly is
`Stacks.Duality.UpperShriek.transport_eq_transport`. -/
theorem transport_localIso_eq (k k' : ι) :
    A.transport (resLE_comp_structure hpe (inf_le_left.trans (hle k)))
        (Scheme.Hom.resLE_comp_ι f (inf_le_left.trans (hle k)))
        (hp.isShriekable_resLE hq hpe (inf_le_left.trans (hle k))
          (hp.isShriekable_le (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k) (𝒰.shriekable k)))
        (𝒱.shriekable (idx k)) (hq.isShriekable_ι (𝒱.U (idx k)))
        (hp.isShriekable_le (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k) (𝒰.shriekable k))
        ((hp.of_comp' hq hpe).isShriekable_le
          (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k)
          (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)))
        (𝒩Y.localIso (idx k)) =
      A.transport (resLE_comp_structure hpe (inf_le_right.trans (hle k')))
        (Scheme.Hom.resLE_comp_ι f (inf_le_right.trans (hle k')))
        (hp.isShriekable_resLE hq hpe (inf_le_right.trans (hle k'))
          (hp.isShriekable_le (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k) (𝒰.shriekable k)))
        (𝒱.shriekable (idx k')) (hq.isShriekable_ι (𝒱.U (idx k')))
        (hp.isShriekable_le (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k) (𝒰.shriekable k))
        ((hp.of_comp' hq hpe).isShriekable_le
          (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k)
          (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)))
        (𝒩Y.localIso (idx k')) := by
  have hWp : IsShriekable ((𝒰.U k ⊓ 𝒰.U k').ι ≫ p) :=
    hp.isShriekable_le inf_le_left (𝒰.shriekable k)
  have hWf : IsShriekable ((𝒰.U k ⊓ 𝒰.U k').ι ≫ f) :=
    (hp.of_comp' hq hpe).isShriekable_le inf_le_left
      (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k))
  have hleW : 𝒰.U k ⊓ 𝒰.U k' ≤ f ⁻¹ᵁ (𝒱.U (idx k) ⊓ 𝒱.U (idx k')) := fun x hx =>
    ⟨hle k hx.1, hle k' hx.2⟩
  have hDq : IsShriekable ((𝒱.U (idx k) ⊓ 𝒱.U (idx k')).ι ≫ q) :=
    hq.isShriekable_le inf_le_left (𝒱.shriekable (idx k))
  have hD : ∀ {V : Y.Opens} (h : 𝒱.U (idx k) ⊓ 𝒱.U (idx k') ≤ V),
      Y.homOfLE h ≫ V.ι ≫ q = (𝒱.U (idx k) ⊓ 𝒱.U (idx k')).ι ≫ q := fun h => by
    rw [← Category.assoc, Y.homOfLE_ι]
  have hβ := 𝒩Y.compat (idx k) (idx k')
  rw [A.restrictLocalIso_eq_transport_symm hq, A.restrictLocalIso_eq_transport_symm hq] at hβ
  rw [Iso.symm_eq_iff] at hβ
  exact A.transport_eq_transport (by simp) (by simp)
    (hD inf_le_left)
    (Y.homOfLE_ι _)
    (hD inf_le_right)
    (Y.homOfLE_ι _) (resLE_comp_structure hpe hleW) (Scheme.Hom.resLE_comp_ι f hleW)
    (resLE_comp_structure hpe (inf_le_left.trans (hle k)))
    (Scheme.Hom.resLE_comp_ι f (inf_le_left.trans (hle k)))
    (resLE_comp_structure hpe (inf_le_right.trans (hle k')))
    (Scheme.Hom.resLE_comp_ι f (inf_le_right.trans (hle k')))
    (hp.isShriekable_resLE hq hpe hleW hWp) (hq.isShriekable_homOfLE inf_le_left)
    (hq.isShriekable_homOfLE inf_le_right)
    (hp.isShriekable_resLE hq hpe (inf_le_left.trans (hle k)) hWp)
    (hp.isShriekable_resLE hq hpe (inf_le_right.trans (hle k')) hWp)
    (𝒱.shriekable (idx k)) (𝒱.shriekable (idx k')) (hq.isShriekable_ι _)
    (hq.isShriekable_ι _) hDq (hq.isShriekable_ι _) hWp hWf
    (𝒩Y.localIso (idx k)) (𝒩Y.localIso (idx k')) hβ

/-- **`f^!ω_Y^•` is normalized relative to `ω_S^•`.**

Let `(S, ω_S^•)` be as in Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a morphism of schemes
of finite type over `S` and let `ω_Y^•` be normalized relative to `ω_S^•` and the covering `𝒱`
of `Y`. Then `f^!ω_Y^•` is normalized relative to `ω_S^•` and any covering `𝒰` of `X` whose
members are carried by `f` into members of `𝒱`.

The normalization on `U_k` is the composite
`(U_k → X)^!f^!ω_Y^• ≅ (U_k → Y)^!ω_Y^• ≅ (U_k → S)^!ω_S^•`: the tautological comparison
`Stacks.Duality.UpperShriek.shriekRestrictIso` followed by the inverse of the transport of
`β_{idx k}` along `U_k → V_{idx k}`. The compatibility on overlaps splits by
`Stacks.Duality.UpperShriek.restrictLocalIso_trans` into
`Stacks.Duality.UpperShriek.restrictLocalIso_shriekRestrictIso` for the first halves and
`Stacks.Duality.Normalized.transport_localIso_eq` for the second.

For `f = j` an open immersion `j^!ω_Y^•` is the restriction `ω_Y^•|_X`, by [Stacks, Tag 0AU0];
this is the covering-indexed form of the step of [Stacks, Tag 0AUC] proved, for the Nagata
formalism and every open separated over `S`, as
`Stacks.Duality.NormalizedOnOpens.shriekOfIsOpenImmersion`. -/
def restrictOverBase (hf : IsShriekable f) : Normalized A hp ωS 𝒰 where
  complex := (A.shriek f hf).obj 𝒩Y.complex
  localIso k :=
    upperShriekLocalIso A (hp.of_comp' hq hpe) hf 𝒩Y.complex
        (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)) ≪≫
      (A.transport (resLE_comp_structure hpe (hle k)) (Scheme.Hom.resLE_comp_ι f (hle k))
        (hp.isShriekable_resLE hq hpe (hle k) (𝒰.shriekable k)) (𝒱.shriekable (idx k))
        (hq.isShriekable_ι (𝒱.U (idx k))) (𝒰.shriekable k)
        (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k))
        (𝒩Y.localIso (idx k))).symm
  compat k k' := by
    have hA := A.restrictLocalIso_trans (hp.of_comp' hq hpe) hp 𝒩Y.complex ωS
      ((A.shriek f hf).obj 𝒩Y.complex) (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k)
      (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)) (𝒰.shriekable k)
      (upperShriekLocalIso A (hp.of_comp' hq hpe) hf 𝒩Y.complex
        (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)))
      (A.transport (resLE_comp_structure hpe (hle k)) (Scheme.Hom.resLE_comp_ι f (hle k))
        (hp.isShriekable_resLE hq hpe (hle k) (𝒰.shriekable k)) (𝒱.shriekable (idx k))
        (hq.isShriekable_ι (𝒱.U (idx k))) (𝒰.shriekable k)
        (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k))
        (𝒩Y.localIso (idx k))).symm
    have hB := A.restrictLocalIso_trans (hp.of_comp' hq hpe) hp 𝒩Y.complex ωS
      ((A.shriek f hf).obj 𝒩Y.complex) (inf_le_right : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k')
      (hp.isShriekable_ι_comp hq hpe (hle k') (𝒰.shriekable k')) (𝒰.shriekable k')
      (upperShriekLocalIso A (hp.of_comp' hq hpe) hf 𝒩Y.complex
        (hp.isShriekable_ι_comp hq hpe (hle k') (𝒰.shriekable k')))
      (A.transport (resLE_comp_structure hpe (hle k')) (Scheme.Hom.resLE_comp_ι f (hle k'))
        (hp.isShriekable_resLE hq hpe (hle k') (𝒰.shriekable k')) (𝒱.shriekable (idx k'))
        (hq.isShriekable_ι (𝒱.U (idx k'))) (𝒰.shriekable k')
        (hp.isShriekable_ι_comp hq hpe (hle k') (𝒰.shriekable k'))
        (𝒩Y.localIso (idx k'))).symm
    refine hA.trans (Eq.trans ?_ hB.symm)
    rw [restrictLocalIso_upperShriekLocalIso, restrictLocalIso_upperShriekLocalIso,
      A.restrictCompare_symm, A.restrictCompare_symm,
      A.restrictCompare_transport
        (hrg := show X.homOfLE (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k) ≫
            f.resLE (𝒱.U (idx k)) (𝒰.U k) (hle k) =
              f.resLE (𝒱.U (idx k)) (𝒰.U k ⊓ 𝒰.U k') (inf_le_left.trans (hle k)) by simp)
        (hg'c := resLE_comp_structure hpe (inf_le_left.trans (hle k)))
        (hg'b := Scheme.Hom.resLE_comp_ι f (inf_le_left.trans (hle k)))
        (hg' := hp.isShriekable_resLE hq hpe (inf_le_left.trans (hle k))
          (hp.isShriekable_le inf_le_left (𝒰.shriekable k))),
      A.restrictCompare_transport
        (hrg := show X.homOfLE (inf_le_right : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k') ≫
            f.resLE (𝒱.U (idx k')) (𝒰.U k') (hle k') =
              f.resLE (𝒱.U (idx k')) (𝒰.U k ⊓ 𝒰.U k') (inf_le_right.trans (hle k')) by simp)
        (hg'c := resLE_comp_structure hpe (inf_le_right.trans (hle k')))
        (hg'b := Scheme.Hom.resLE_comp_ι f (inf_le_right.trans (hle k')))
        (hg' := hp.isShriekable_resLE hq hpe (inf_le_right.trans (hle k'))
          (hp.isShriekable_le inf_le_left (𝒰.shriekable k))),
      transport_localIso_eq hpe hp hq idx hle 𝒩Y k k']

/-- The complex of `Stacks.Duality.Normalized.restrictOverBase` is `f^!ω_Y^•`, which for `f` an
open immersion is the restriction `ω_Y^•|_X` of [Stacks, Tag 0AU0]. -/
@[simp]
theorem restrictOverBase_complex (hf : IsShriekable f) :
    (restrictOverBase hpe hp hq idx hle 𝒩Y hf).complex = (A.shriek f hf).obj 𝒩Y.complex :=
  rfl

end Normalized

/-- **Uniqueness applied to `j^!ω_Y^•`, for any upper-shriek formalism.** Let `j : X ⟶ Y` be a
shriekable morphism of schemes of finite type over `S`, `ω_X^•` normalized relative to `ω_S^•`
and `𝒰`, and `ω_Y^•` normalized relative to `ω_S^•` and `𝒱`. Given, for the formalism `A`, that
any two complexes normalized relative to `ω_S^•` and `𝒰` are isomorphic compatibly with the
normalizations (the binder `h0AU7`), `ω_X^•` is isomorphic to `j^!ω_Y^•` compatibly with the
normalizations of `Stacks.Duality.Normalized.restrictOverBase`.

This is a one-line application of `h0AU7` to `Stacks.Duality.Normalized.restrictOverBase`. For
the formalism of Nagata compactifications the uniqueness is proved, as
`Stacks.Duality.Normalized.existsUnique_iso_nagata` ([Stacks, Tag 0AU7]), and
[Stacks, Tag 0AUC] is proved outright as
`Stacks.Duality.NormalizedOnOpens.isoDerivedRestrictNagata` and
`Stacks.Duality.NormalizedOnOpens.existsUnique_iso_shriekOfIsOpenImmersion_nagata`. -/
theorem exists_normalizedIso_restrict_of_openImmersion {𝒟 : Scheme.{u} → Type v}
    [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] (A : UpperShriek 𝒟) {X Y S : Scheme.{u}}
    {j : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : j ≫ q = p) (hj : IsShriekable j)
    (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q) {ωS : 𝒟 S}
    {ι : Type w} {J : Type w'} {𝒰 : SeparatedCovering p ι} {𝒱 : SeparatedCovering q J}
    (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ j ⁻¹ᵁ 𝒱.U (idx k))
    (𝒩X : Normalized A hp ωS 𝒰) (𝒩Y : Normalized A hq ωS 𝒱)
    (h0AU7 : ∀ 𝒩 𝒩' : Normalized A hp ωS 𝒰, ∃ e : 𝒩.complex ≅ 𝒩'.complex,
      ∀ k, (A.shriek (𝒰.U k).ι (hp.isShriekable_ι (𝒰.U k))).mapIso e ≪≫ 𝒩'.localIso k =
        𝒩.localIso k) :
    ∃ e : 𝒩X.complex ≅ (A.shriek j hj).obj 𝒩Y.complex,
      ∀ k, (A.shriek (𝒰.U k).ι (hp.isShriekable_ι (𝒰.U k))).mapIso e ≪≫
          (Normalized.restrictOverBase hpe hp hq idx hle 𝒩Y hj).localIso k =
        𝒩X.localIso k :=
  h0AU7 𝒩X (Normalized.restrictOverBase hpe hp hq idx hle 𝒩Y hj)

end Stacks.Duality

end
