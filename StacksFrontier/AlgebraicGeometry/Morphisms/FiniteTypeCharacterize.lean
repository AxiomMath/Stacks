module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypeAtLocally

/-!
# Characterizations of morphisms locally of finite type

Stacks 01T2 gives four equivalent forms of "`f : X ⟶ S` is locally of finite type", where
"locally of finite type" is the pointwise definition of Stacks 01T1 (2): `f` is of finite type at
every point of `X` (`AlgebraicGeometry.finiteTypeAt`). The other three conditions are: finite type
of `Γ(S, V) ⟶ Γ(X, U)` for every compatible pair of affine opens (the field of Mathlib's class
`AlgebraicGeometry.LocallyOfFiniteType`), an open covering of `S` and open coverings of the
preimages on whose pieces `f` restricts to morphisms locally of finite type, and the same with
affine coverings and finite-type ring maps. Moreover, restrictions `f.resLE V U e` of a morphism
locally of finite type are locally of finite type.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_iff_forall_finiteTypeAt`: Mathlib's class
  `AlgebraicGeometry.LocallyOfFiniteType` is the pointwise notion of Stacks 01T1 (2).
* `AlgebraicGeometry.locallyOfFiniteType_tfae`: the four conditions of Stacks 01T2.
* `AlgebraicGeometry.finiteTypeAt_resLE`: the "moreover" clause of Stacks 01T2.

## Implementation notes

In conditions (3) and (4) the inclusions `U j i ≤ f ⁻¹ᵁ V j` are existentially quantified
alongside the coverings; they follow from `⨆ i, U j i = f ⁻¹ᵁ V j` and are recorded only because
`Scheme.Hom.resLE` and `Scheme.Hom.appLE` take them as arguments. The index types live in the
universe of the schemes.

## References

* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism of schemes is locally of finite type in Mathlib's sense (finite-type maps on all
compatible pairs of affine opens) if and only if it is of finite type at every point of its
source, which is the definition of Stacks 01T1 (2). -/
@[stacks 01T2 "(1) ⇔ (2): with (1) the pointwise definition 01T1 (2)"]
theorem locallyOfFiniteType_iff_forall_finiteTypeAt :
    LocallyOfFiniteType f ↔ ∀ x : X, finiteTypeAt f x :=
  ⟨fun _ ↦ finiteTypeAt_of_locallyOfFiniteType f, LocallyOfFiniteType.of_forall_finiteTypeAt f⟩

/-- **Stacks 01T2.** For a morphism of schemes `f : X ⟶ S` the following are equivalent:
1. `f` is locally of finite type, that is, of finite type at every point of `X` (Stacks 01T1);
2. for all affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V` the ring map `Γ(S, V) ⟶ Γ(X, U)` is
   of finite type;
3. there are an open covering `S = ⋃ j, V j` and open coverings `f ⁻¹ V j = ⋃ i, U j i` such
   that each restriction `U j i ⟶ V j` is locally of finite type, that is, of finite type at
   every point of `U j i`;
4. there are an affine open covering `S = ⋃ j, V j` and affine open coverings
   `f ⁻¹ V j = ⋃ i, U j i` such that each ring map `Γ(S, V j) ⟶ Γ(X, U j i)` is of finite
   type. -/
@[stacks 01T2 "(1) ⇔ (2) ⇔ (3) ⇔ (4), with (1) the pointwise definition 01T1 (2)"]
theorem locallyOfFiniteType_tfae : List.TFAE
    [∀ x : X, finiteTypeAt f x,
      ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V →
        ∀ (e : U ≤ f ⁻¹ᵁ V), (f.appLE V U e).hom.FiniteType,
      ∃ (J : Type u) (V : J → S.Opens) (I : J → Type u) (U : ∀ j, I j → X.Opens)
        (e : ∀ j i, U j i ≤ f ⁻¹ᵁ V j), ⨆ j, V j = ⊤ ∧ (∀ j, ⨆ i, U j i = f ⁻¹ᵁ V j) ∧
          ∀ j i, ∀ y, finiteTypeAt (f.resLE (V j) (U j i) (e j i)) y,
      ∃ (J : Type u) (V : J → S.Opens) (I : J → Type u) (U : ∀ j, I j → X.Opens)
        (e : ∀ j i, U j i ≤ f ⁻¹ᵁ V j), (∀ j, IsAffineOpen (V j)) ∧
          (∀ j i, IsAffineOpen (U j i)) ∧ ⨆ j, V j = ⊤ ∧ (∀ j, ⨆ i, U j i = f ⁻¹ᵁ V j) ∧
          ∀ j i, (f.appLE (V j) (U j i) (e j i)).hom.FiniteType] := by
  tfae_have 1 ↔ 2 := by
    rw [← locallyOfFiniteType_iff_forall_finiteTypeAt, locallyOfFiniteType_iff]
    exact ⟨fun h U hU V hV e ↦ h hV hU e, fun h _ hV _ hU e ↦ h _ hU _ hV e⟩
  tfae_have 2 → 4 := fun h ↦ by
    refine ⟨S.affineOpens, fun V ↦ V.1, fun V ↦ {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1},
      fun _ U ↦ U.1.1, fun _ U ↦ U.2, fun V ↦ V.2, fun _ U ↦ U.1.2, iSup_affineOpens_eq_top S,
      fun V ↦ le_antisymm (iSup_le fun U ↦ U.2) fun x hx ↦ ?_, fun V U ↦ h _ U.1.2 _ V.2 _⟩
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ V.1).2
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  tfae_have 4 → 1 := fun ⟨J, V, I, U, e, hV, hU, hVcov, hUcov, h⟩ x ↦ by
    have hfx : f x ∈ ⨆ j, V j := hVcov ▸ trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hfx
    have hx : x ∈ ⨆ i, U j i := (hUcov j).symm ▸ hj
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨⟨V j, hV j⟩, ⟨U j i, hU j i⟩, hi, e j i, h j i⟩
  tfae_have 2 → 3 := fun h ↦ by
    have : LocallyOfFiniteType f := ⟨fun hV _ hU e ↦ h _ hU _ hV e⟩
    exact ⟨PUnit, fun _ ↦ ⊤, fun _ ↦ PUnit, fun _ _ ↦ ⊤, fun _ _ ↦ by simp,
      by simp, fun _ ↦ by simp, fun _ _ ↦ finiteTypeAt_of_locallyOfFiniteType _⟩
  tfae_have 3 → 2 := fun ⟨J, V, I, U, e, hVcov, hUcov, h⟩ ↦ by
    have : LocallyOfFiniteType f := by
      have _ : IsZariskiLocalAtSource @LocallyOfFiniteType :=
        HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
      have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
        HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
      have _ : MorphismProperty.RespectsRight @LocallyOfFiniteType @IsOpenImmersion :=
        ⟨fun i hi g hg ↦ by
          have := hi
          have := hg
          infer_instance⟩
      refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @LocallyOfFiniteType)).mpr
        fun x ↦ ?_
      have hfx : f x ∈ ⨆ j, V j := hVcov ▸ trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hfx
      have hx : x ∈ ⨆ i, U j i := (hUcov j).symm ▸ hj
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact ⟨V j, U j i, hi, e j i, LocallyOfFiniteType.of_forall_finiteTypeAt _ (h j i)⟩
    exact fun U hU V hV e ↦ f.finiteType_appLE hV hU e
  tfae_finish

/-- **Stacks 01T2, moreover clause.** If `f : X ⟶ S` is locally of finite type, that is, of
finite type at every point (Stacks 01T1), then for all opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`
the restriction `f.resLE V U e : U ⟶ V` is again of finite type at every point. -/
@[stacks 01T2 "moreover clause, in the pointwise sense of 01T1 (2)"]
theorem finiteTypeAt_resLE (h : ∀ x : X, finiteTypeAt f x) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) (y : U.toScheme) : finiteTypeAt (f.resLE V U e) y := by
  have : LocallyOfFiniteType f := LocallyOfFiniteType.of_forall_finiteTypeAt f h
  exact finiteTypeAt_of_locallyOfFiniteType _ y

end AlgebraicGeometry
