module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.BaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.CoordinateImmersion
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.ImmersionCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 02NQ

Stacks Tag 02NQ says that for a morphism of schemes `f : X ⟶ S` of finite type and an invertible
`𝒪_X`-module `L` the following are equivalent:

1. `L` is `f`-relatively very ample, and
2. there are an open covering `S = ⋃ V_j`, for each `j` an integer `n_j`, and immersions
   `i_j : X_j = f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` with `L|_{X_j} ≅ i_j^* 𝒪(1)`.

Condition (1) is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` (Stacks Tag 01VM) and condition
(2) is `Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover`, defined in
`StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Basic`. Finite type is
`LocallyOfFiniteType` together with `QuasiCompact`.

## Main results

* `Stacks.VeryAmpleFiniteTypeCover.isRelativelyVeryAmple_iff_hasProjectiveImmersionCover`:
  **Stacks Tag 02NQ.**
* `Stacks.VeryAmpleFiniteTypeCover.hasProjectiveImmersionCover_of_isRelativelyVeryAmple`:
  (1) implies (2).
* `Stacks.VeryAmpleFiniteTypeCover.isRelativelyVeryAmple_of_hasProjectiveImmersionCover`:
  (2) implies (1); it uses only quasi-compactness of `f`.
* `exists_affine_cover_hasImmersionTwistOver_of_isRelativelyVeryAmple`: the strengthening
  of (1) implies (2) that the proof produces — the covering may be taken to consist of **affine**
  opens.
* `Stacks.VeryAmpleFiniteTypeCover.hasImmersionTwistOver_morphismRestrict_of_le`: the clause of
  condition (2) at a member restricts to every smaller open of the base.

## The route

The source's (1) implies (2) is "take an affine open covering of `S` and apply Lemma 02NP to each
of the restrictions of `f` and `L`". The covering taken here is **all** the affine opens of `S`,
which cover it by `AlgebraicGeometry.iSup_affineOpens_eq_top`, so no choice is made and no
quasi-compactness of the base is used. At an affine open `V` the assumptions of Tag 02NP,
`Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, are met:
`IsAffine V.toScheme` is `AlgebraicGeometry.IsAffineOpen V`; finiteness of type of `f ∣_ V` and
invertibility of the restriction of `L` are instances; and relative very ampleness of the
restriction is `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict` — the restriction
is the base change along `V.ι`, and relative very ampleness is stable under base change (Stacks Tag
0B3F), the projective bundle of `E|_V` being `V ×_S 𝐏(E)` with `𝒪(1)` pulling back to `𝒪(1)`.

The source's (2) implies (1) is "by Lemma 01VR". The covering of (2) is first refined to the affine
opens lying inside one of its members, over which the immersion clause restricts by
`hasImmersionTwistOver_morphismRestrict_of_le`; relative very ampleness over `S` then follows from
the immersions over an affine covering by
`Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_affine_cover_hasImmersionTwistOver`, which is the
route of Tag 01VR's (2) implies (1) through `f_* L` and the morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)`.

## References

* [Stacks Project, Tag 02NQ](https://stacks.math.columbia.edu/tag/02NQ)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmpleFiniteTypeCover

variable {X S : Scheme.{u}}

/-! ### Stacks Tag 02NQ, (1) implies (2) -/

/-- **Stacks Tag 02NQ, (1) implies (2), with the covering taken to be affine.** For `f : X ⟶ S` of
finite type and `L` relatively very ample there are an open covering of `S` **by affine opens**,
for each member an integer `n`, and an immersion `f⁻¹(V) ⟶ 𝐏^n_V` over `V` carrying the hyperplane
sheaf to the restriction of `L`.

The source's condition (2) does not ask the covering to be affine; the extra clause is recorded
because it is what the proof produces and what a consumer needing an affine base can use. The
covering is *all* of the affine opens of `S`, which cover it by
`AlgebraicGeometry.iSup_affineOpens_eq_top`, so neither a choice nor quasi-compactness of `S`
enters. -/
theorem exists_affine_cover_hasImmersionTwistOver_of_isRelativelyVeryAmple (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f]
    (hL : Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    ∃ (ι : Type u) (V : ι → S.Opens), (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
      ∀ j : ι, HasImmersionTwistOver (f ∣_ V j)
        ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) := by
  refine ⟨↥S.affineOpens, fun j => (j : S.Opens), fun j => j.2,
    iSup_affineOpens_eq_top S, fun j => ?_⟩
  have : IsAffine (j : S.Opens).toScheme := j.2
  exact CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple (f ∣_ (j : S.Opens)) _
    (Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict f L hL (j : S.Opens))

/-- **Stacks Tag 02NQ, (1) implies (2).** Let `f : X ⟶ S` be of finite type and `L` an invertible
`𝒪_X`-module. If `L` is `f`-relatively very ample then there are an open covering `S = ⋃ V_j`, for
each `j` an integer `n_j`, and immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying the
hyperplane sheaf to `L|_{f⁻¹(V_j)}`.

This is the source's own proof: take an affine open covering of `S` and apply Stacks Tag 02NP,
`Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, to each of the
restrictions of `f` and `L`; relative very ampleness of the restrictions is Stacks Tag 01VR's
(1) implies (2) at the member, `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict`. -/
@[stacks 02NQ "(1) implies (2)"]
theorem hasProjectiveImmersionCover_of_isRelativelyVeryAmple (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f]
    (hL : Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    HasProjectiveImmersionCover f L := by
  obtain ⟨ι, V, -, hcov, h⟩ :=
    exists_affine_cover_hasImmersionTwistOver_of_isRelativelyVeryAmple f L hL
  exact ⟨ι, V, hcov, h⟩

/-! ### The immersion clause restricts from an open of the base to a smaller one -/

/-- **The clause of condition (2) at a member of the covering restricts to a smaller open.** If
`W ≤ V` are opens of `S` and `L|_{f⁻¹(V)}` is the hyperplane sheaf pulled back along an immersion
`f⁻¹(V) ⟶ 𝐏ⁿ_V` over `V`, then `L|_{f⁻¹(W)}` is the hyperplane sheaf pulled back along an immersion
`f⁻¹(W) ⟶ 𝐏ⁿ_W` over `W`.

`𝐏ⁿ_W` is `W ×_{⊤} 𝐏ⁿ_ℤ`, so the new morphism is
`Stacks.AmpleProjectiveImmersion.liftOver` of `f ∣_ W` and of `f⁻¹(W) ⟶ f⁻¹(V) ⟶ 𝐏ⁿ_V ⟶ 𝐏ⁿ_ℤ`.
Its composite with the canonical `𝐏ⁿ_W ⟶ 𝐏ⁿ_V` is the open immersion `f⁻¹(W) ⟶ f⁻¹(V)` followed by
the given immersion (`AlgebraicGeometry.morphismRestrict_homOfLE`), so it is an immersion by
`AlgebraicGeometry.IsImmersion.of_comp`; the twist is transported by
`Stacks.AmpleProjectiveImmersion.liftOverTwistIso` and the pseudofunctoriality of the module
pullback. This is `Stacks.AmplePowerImmersionCover.hasImmersionTwistOver_morphismRestrict` with the
base already an open of `S`, read so that the result is again stated at an open of `S`. -/
theorem hasImmersionTwistOver_morphismRestrict_of_le (f : X ⟶ S) (L : X.Modules) {V W : S.Opens}
    (hWV : W ≤ V)
    (h : HasImmersionTwistOver (f ∣_ V) ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)) :
    HasImmersionTwistOver (f ∣_ W) ((modulePullback (f ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) := by
  obtain ⟨n, i, him, hover, ⟨e⟩⟩ := h
  set k : (f ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ V).toScheme := X.homOfLE (f.preimage_mono hWV) with hk
  refine ⟨n, liftOver (f ∣_ W) (k ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n V.toScheme),
    ?_, liftOver_fst _ _, ⟨?_⟩⟩
  · have key : liftOver (f ∣_ W)
          (k ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n V.toScheme) ≫
          liftOver (pullback.fst (terminal.from W.toScheme)
              (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ S.homOfLE hWV)
            (projectiveSpaceOver.toIntegralAtUniverse n W.toScheme) = k ≫ i := by
      refine pullback.hom_ext ?_ ?_
      · simp only [liftOver, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          morphismRestrict_homOfLE, hk, hover]
      · simp only [liftOver, Category.assoc, pullback.lift_snd]
    have hI : IsImmersion (liftOver (f ∣_ W)
        (k ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n V.toScheme) ≫
        liftOver (pullback.fst (terminal.from W.toScheme)
            (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ S.homOfLE hWV)
          (projectiveSpaceOver.toIntegralAtUniverse n W.toScheme)) := by
      rw [key]
      infer_instance
    exact IsImmersion.of_comp _
      (liftOver (pullback.fst (terminal.from W.toScheme)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ S.homOfLE hWV)
        (projectiveSpaceOver.toIntegralAtUniverse n W.toScheme))
  · exact (Scheme.Modules.pullbackCongr (X.homOfLE_ι (f.preimage_mono hWV)).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp k (f ⁻¹ᵁ V).ι).app L).symm ≪≫
      (Scheme.Modules.pullback k).mapIso e ≪≫
      (Scheme.Modules.pullback k).mapIso
        ((Scheme.Modules.pullbackComp i
          (projectiveSpaceOver.toIntegralAtUniverse n V.toScheme)).app
            (twistingSheafAtUniverse n)) ≪≫
      (Scheme.Modules.pullbackComp k
          (i ≫ projectiveSpaceOver.toIntegralAtUniverse n V.toScheme)).app
        (twistingSheafAtUniverse n) ≪≫
      (liftOverTwistIso (f ∣_ W)
        (k ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n V.toScheme)).symm

/-! ### Stacks Tag 02NQ, (2) implies (1) -/

/-- **Stacks Tag 02NQ, (2) implies (1).** Let `f : X ⟶ S` be quasi-compact and `L` an invertible
`𝒪_X`-module. If there are an open covering `S = ⋃ V_j`, for each `j` an integer `n_j`, and
immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying the hyperplane sheaf to
`L|_{f⁻¹(V_j)}`, then `L` is `f`-relatively very ample.

The covering is refined to the affine opens of `S` contained in one of its members, which cover `S`
because the affine opens are a basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`); over each of
them the immersion clause is the restriction of the one over the member,
`Stacks.VeryAmpleFiniteTypeCover.hasImmersionTwistOver_morphismRestrict_of_le`, and the immersions
over an affine covering give relative very ampleness by
`Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_affine_cover_hasImmersionTwistOver`.

Only quasi-compactness of `f` is used, not the whole of the source's finite-type assumption. -/
@[stacks 02NQ "(2) implies (1)"]
theorem isRelativelyVeryAmple_of_hasProjectiveImmersionCover (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hqc : QuasiCompact f) (h : HasProjectiveImmersionCover f L) :
    Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  have : QuasiCompact f := hqc
  obtain ⟨ι, V, hcov, hj⟩ := h
  let T := {W : S.affineOpens // ∃ j, (W : S.Opens) ≤ V j}
  have hcovT : (⨆ W : T, (W.1 : S.Opens)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    obtain ⟨W, hWaff, hxW, hWV⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hxj
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hWaff⟩, j, hWV⟩, hxW⟩
  exact VeryAmpleGlue.isRelativelyVeryAmple_of_affine_cover_hasImmersionTwistOver f L
    (fun W : T => (W.1 : S.Opens)) (fun W => W.1.2) hcovT fun W =>
      hasImmersionTwistOver_morphismRestrict_of_le f L W.2.choose_spec (hj W.2.choose)

/-! ### The equivalence -/

/-- **Stacks Tag 02NQ.** For `f : X ⟶ S` of finite type and `L` an invertible `𝒪_X`-module,
relative very ampleness of `L` is equivalent to the existence of an open covering `S = ⋃ V_j`, of
an integer `n_j` for each `j`, and of immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying the
hyperplane sheaf to `L|_{f⁻¹(V_j)}`.

The two implications are
`Stacks.VeryAmpleFiniteTypeCover.hasProjectiveImmersionCover_of_isRelativelyVeryAmple` and
`Stacks.VeryAmpleFiniteTypeCover.isRelativelyVeryAmple_of_hasProjectiveImmersionCover`. -/
@[stacks 02NQ]
theorem isRelativelyVeryAmple_iff_hasProjectiveImmersionCover (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f] [hqc : QuasiCompact f] :
    Tag01VMVeryAmple.IsRelativelyVeryAmple f L ↔ HasProjectiveImmersionCover f L :=
  ⟨hasProjectiveImmersionCover_of_isRelativelyVeryAmple f L,
    isRelativelyVeryAmple_of_hasProjectiveImmersionCover f L hqc⟩

end Stacks.VeryAmpleFiniteTypeCover

end
