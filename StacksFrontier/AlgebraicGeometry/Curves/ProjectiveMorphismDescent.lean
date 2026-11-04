module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# Descent of a morphism to projective space along a dominant map to a normal curve

Let `k` be a field, let `Y` be a normal curve over `k`, let `X` be an integral `k`-scheme and let
`g : X ⟶ Y` be a dominant `k`-morphism. Let `ℒ` be an invertible `𝒪_X`-module with `n + 1`
generating global sections `s₀, …, sₙ`, so that [Stacks, Tag 01ND] attaches to them a morphism
`φ = φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ 𝐏ⁿ_k`. At a point of `X` where `sᵢ` does not vanish the
homogeneous coordinates of `φ` are the ratios `s_k / sᵢ`, and at the generic point they are
elements of the function field `K(X)`. This file shows that `φ` is the pullback along `g` of a
morphism `Y ⟶ 𝐏ⁿ_k` as soon as those generic coordinates all lie in the subfield `K(Y)` of
`K(X)`.

The coordinates lifted to `K(Y)` give a `K(Y)`-point of `𝐏ⁿ_k`, which [Stacks, Tag 0BX6] spreads
out to a rational map `Y ⇢ 𝐏ⁿ_k` and [Stacks, Tag 0BXZ] then realizes by an honest morphism
`ψ : Y ⟶ 𝐏ⁿ_k`, the curve being normal and projective space proper. The composite `g ≫ ψ` agrees
with `φ` at the generic point of `X` because both are read off the same homogeneous coordinates,
and two morphisms from an integral scheme to a separated `k`-scheme agreeing on a dense open
agree everywhere.

## Main results

* `AlgebraicGeometry.exists_hom_over_comp_eq_toProjectiveSpaceOver`: **the morphism of
  [Stacks, Tag 01ND] descends along a dominant morphism onto a normal proper curve** as soon as
  its homogeneous coordinates at the generic point lie in the function field of the curve.

## Implementation notes

The comparison of the two morphisms out of `X` is made at the generic point and then propagated.
At the generic point both composites are morphisms into the fibre product
`AlgebraicGeometry.projectiveSpaceOver`, so they are compared componentwise: on the integral
model by `AlgebraicGeometry.projectiveSpacePoint`, whose naturality in the ring turns the
`K(Y)`-point into the `K(X)`-point with the germs of the ratios as coordinates, and on the base
by the two structure morphisms. Propagation from the generic point to all of `X` goes through
Mathlib's rational maps: equality of the two `K(X)`-points is equality of the two rational maps
(`AlgebraicGeometry.Scheme.RationalMap.eq_of_fromFunctionField_eq`), hence agreement on a dense
open, and a dense open of a reduced scheme is scheme-theoretically dense
(`AlgebraicGeometry.dense_open_tfae`), so
`AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense` concludes.

The coordinates chosen in `K(Y)` are pinned to be `1` in the `i`-th slot, which is where the
hypothesis that `sᵢ` does not vanish at the generic point is used: the `i`-th ratio is `1`, so a
lift of the family can be taken to contain `1` and therefore to span the unit ideal, as
`AlgebraicGeometry.projectiveSpacePoint` requires.

## References

* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
* [Stacks Project, Tag 0BX6](https://stacks.math.columbia.edu/tag/0BX6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism to projective space built from sections descends along a dominant morphism onto
a normal proper curve as soon as its homogeneous coordinates at the generic point do.**

Here `X` is an integral `k`-scheme, `Y` a normal curve over `k` and `g : X ⟶ Y` a dominant
`k`-morphism; `L` is an invertible `𝒪_X`-module with generating global sections `s`, and `sᵢ`
does not vanish at the generic point of `X`, so the homogeneous coordinates of
`φ_{(L, (s₀, …, sₙ))}` there are the germs of the ratios `s_k / sᵢ`. If each of those germs lies
in the image of `K(Y) ⟶ K(X)` then `φ_{(L, (s₀, …, sₙ))}` factors as `g` followed by a morphism
`Y ⟶ 𝐏ⁿ_k` over `k`. -/
theorem exists_hom_over_comp_eq_toProjectiveSpaceOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsCurve k pY] [IsNormal Y]
    (g : X ⟶ Y) [IsDominant g] (hg : g ≫ pY = pX)
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    {i : Fin (n + 1)} (hη : genericPoint X ∈ Stacks.ProjectiveFromSections.nvCover s i)
    (hmem : ∀ j, X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i) (genericPoint X) hη
        (Stacks.ProjectiveFromSections.ratio s i j) ∈ (functionFieldMap g).range) :
    ∃ ψ : Y ⟶ projectiveSpaceOver n (Spec (.of k)),
      ψ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = pY ∧
      g ≫ ψ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX := by
  classical
  -- Projective space over `k` is a proper variety, for every `n`.
  have hproper : IsProper (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) := isProper_projectiveSpaceOver n (Spec (CommRingCat.of k))
  have hpvar : IsProperVariety k (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) := IsProperVariety.mk
  -- The `i`-th germ of the ratios is `1`.
  have hone : X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i) (genericPoint X) hη
      (Stacks.ProjectiveFromSections.ratio s i i) = 1 := by
    rw [Stacks.ProjectiveFromSections.ratio_self]; exact map_one _
  -- Step 1: lift the homogeneous coordinates to the function field of `Y`, keeping the `i`-th
  -- coordinate equal to `1`.
  obtain ⟨ξ, hξi, hξf⟩ : ∃ ξ : Fin (n + 1) → Y.functionField, ξ i = 1 ∧
      ∀ j, functionFieldMap g (ξ j) =
        X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i) (genericPoint X) hη
          (Stacks.ProjectiveFromSections.ratio s i j) := by
    refine ⟨Function.update (fun j => (RingHom.mem_range.mp (hmem j)).choose) i 1,
      Function.update_self _ _ _, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, map_one]; exact hone.symm
    · rw [Function.update_of_ne hj]
      exact (RingHom.mem_range.mp (hmem j)).choose_spec
  have hξ : Ideal.span (Set.range ξ) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hξi]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hξmap : Ideal.span (Set.range fun j =>
      (ConcreteCategory.hom (CommRingCat.ofHom (functionFieldMap g))) (ξ j)) = ⊤ := by
    have : (fun j => (ConcreteCategory.hom (CommRingCat.ofHom (functionFieldMap g))) (ξ j)) =
        fun j => X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i) (genericPoint X) hη
          (Stacks.ProjectiveFromSections.ratio s i j) := funext hξf
    rw [this]
    exact span_range_germ_ratio s hη
  -- Step 2: the `K(Y)`-point of `𝐏ⁿ_ℤ` with those coordinates reads over `K(X)` as the point
  -- with the germs of the ratios as coordinates.
  have hspecmap : Spec.map (CommRingCat.ofHom (functionFieldMap g)) ≫
      projectiveSpacePoint ξ hξ =
      projectiveSpacePoint
        (fun j => X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i) (genericPoint X) hη
          (Stacks.ProjectiveFromSections.ratio s i j))
        (span_range_germ_ratio s hη) := by
    rw [specMap_comp_projectiveSpacePoint (CommRingCat.ofHom (functionFieldMap g)) ξ hξ hξmap]
    have hcoord : ∀ (c : Fin (n + 1) → X.functionField)
        (hc : Ideal.span (Set.range c) = ⊤),
        (c = fun j => X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i)
            (genericPoint X) hη (Stacks.ProjectiveFromSections.ratio s i j)) →
        projectiveSpacePoint c hc = projectiveSpacePoint _
          (span_range_germ_ratio s hη) := by
      intro c hc hc'; subst hc'; rfl
    exact hcoord _ hξmap (funext hξf)
  -- Step 3: lift the `K(Y)`-point into projective space over `k`.
  obtain ⟨q, hqfst, hqsnd⟩ : ∃ q : Spec Y.functionField ⟶ projectiveSpaceOver n
        (Spec (CommRingCat.of k)),
      q ≫ (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
          Y.fromSpecStalk (genericPoint Y) ≫ pY ∧
        q ≫ pullback.snd (terminal.from (Spec (CommRingCat.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = projectiveSpacePoint ξ hξ :=
    ⟨Stacks.AmpleProjectiveImmersion.liftOver _ _,
      Stacks.AmpleProjectiveImmersion.liftOver_fst _ _,
      Stacks.AmpleProjectiveImmersion.liftOver_snd _ _⟩
  -- Steps 4, 5 and 6: spread the `K(Y)`-point out to a rational map, realize it by a morphism
  -- `ψ : Y ⟶ 𝐏ⁿ_k` over `k`, and identify `ψ` at the generic point of `Y` with the point `q`.
  obtain ⟨ψ, hψfst, hψgeneric⟩ : ∃ ψ : Y ⟶ projectiveSpaceOver n (Spec (CommRingCat.of k)),
      ψ ≫ pullback.fst (terminal.from (Spec (CommRingCat.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = pY ∧
        Y.fromSpecStalk (genericPoint Y) ≫ ψ = q := by
    let _ : Y.Over (Spec (CommRingCat.of k)) := ⟨pY⟩
    have _ : IsCurve k (Over.mk pY).hom := inferInstanceAs (IsCurve k pY)
    have _ : IsNormal (Over.mk pY).left := inferInstanceAs (IsNormal Y)
    have _ : IsProperVariety k (Over.mk (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))).hom := hpvar
    set rm := Scheme.RationalMap.ofFunctionField pY
      (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) q hqfst
      with hrm
    have hrmOver : Scheme.RationalMap.IsOver (Spec (CommRingCat.of k)) rm :=
      ⟨Scheme.PartialMap.ofFromSpecStalk pY
        (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) q hqfst,
        ⟨Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _⟩, rfl⟩
    obtain ⟨Ψ, hΨ⟩ := (toRationalMap_bijective k (Over.mk pY)
      (Over.mk (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))).2 ⟨rm, hrmOver⟩
    refine ⟨Ψ.left, Over.w Ψ, ?_⟩
    have hΨr : Ψ.left.toRationalMap = rm := congrArg Subtype.val hΨ
    have hff := congrArg Scheme.RationalMap.fromFunctionField hΨr
    rw [hrm, Scheme.RationalMap.fromFunctionField_ofFunctionField] at hff
    simp only [Scheme.RationalMap.fromFunctionField_toRationalMap, Over.mk_left,
      Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] at hff
    exact hff
  -- Step 7: `g ≫ ψ` and `φ_{(L, (s₀, …, sₙ))}` agree at the generic point of `X`.
  have hgeneric : X.fromSpecStalk (genericPoint X) ≫ (g ≫ ψ) =
      X.fromSpecStalk (genericPoint X) ≫
        Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, Category.assoc, hψfst,
        Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst, hg]
    · calc (X.fromSpecStalk (genericPoint X) ≫ g ≫ ψ) ≫
              pullback.snd (terminal.from (Spec (CommRingCat.of k)))
                (terminal.from (projectiveSpaceAtUniverse.{u} n))
          = (Spec.map (CommRingCat.ofHom (functionFieldMap g)) ≫ q) ≫
              pullback.snd (terminal.from (Spec (CommRingCat.of k)))
                (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
            rw [← hψgeneric, ← Category.assoc (X.fromSpecStalk (genericPoint X)) g ψ,
              ← functionFieldMap_fromSpecStalk g]
            simp only [Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (functionFieldMap g)) ≫ projectiveSpacePoint ξ hξ := by
            rw [Category.assoc, hqsnd]
        _ = projectiveSpacePoint
              (fun j => X.presheaf.germ (Stacks.ProjectiveFromSections.nvCover s i)
                (genericPoint X) hη (Stacks.ProjectiveFromSections.ratio s i j))
              (span_range_germ_ratio s hη) := hspecmap
        _ = (X.fromSpecStalk (genericPoint X) ≫
              Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX) ≫
              pullback.snd (terminal.from (Spec (CommRingCat.of k)))
                (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
            rw [Category.assoc, Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd,
              fromSpecStalk_comp_toProjectiveSpaceAtUniverse s hs hη]
  -- Step 8: propagate the agreement from the generic point to all of `X`.
  have hrat : (g ≫ ψ).toRationalMap =
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX).toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    simpa only [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] using hgeneric
  obtain ⟨U, hU, hUl, hUr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp hrat
  change X.homOfLE hUl ≫ (g ≫ ψ).toPartialMap.hom =
    X.homOfLE hUr ≫
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX).toPartialMap.hom at hEq
  have hover1 : (g ≫ ψ) ≫ (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = pX := by
    rw [Category.assoc, ← hg]; exact congrArg (g ≫ ·) hψfst
  have hover2 : Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX ≫
      (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = pX :=
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst s hs pX
  have _ : IsSeparated (Over.mk (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))).hom :=
    inferInstanceAs (IsSeparated (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)))
  have hι : ∀ {Z : Scheme.{u}} (f : X ⟶ Z) (hl : U ≤ f.toPartialMap.domain),
      U.ι ≫ f = X.homOfLE hl ≫ f.toPartialMap.hom := fun f hl => by
    simp [Scheme.Hom.toPartialMap, Scheme.topIso_hom, ← Scheme.homOfLE_ι X hl]
  have hfgU : U.ι ≫ (g ≫ ψ) =
      U.ι ≫ Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX := by
    rw [hι _ hUl, hι _ hUr, hEq]
  have hfinal := eq_of_isSchemeTheoreticallyDense
    (Over.homMk (g ≫ ψ) hover1 :
      Over.mk pX ⟶ Over.mk (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))
    (Over.homMk (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX) hover2)
    U (((dense_open_tfae U).out 1 3).mp hU) hfgU
  exact ⟨ψ, hψfst, congrArg Over.Hom.left hfinal⟩

end AlgebraicGeometry

end
