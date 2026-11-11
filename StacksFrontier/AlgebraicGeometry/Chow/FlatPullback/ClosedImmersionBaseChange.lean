module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Flat pullback along the inverse image of a closed subscheme

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be flat of relative dimension `r` and let `W ⊆ X` be a closed
subscheme. The scheme-theoretic inverse image `W' = f^{-1}(W)` is the closed subscheme cut out by
`W.comap f`, the restriction `g : W' ⟶ W` of `f` is again flat of relative dimension `r`, and the
square

  `W' --i'--> X'`
  `|g          |f`
  `W  --i-->  X`

is cartesian. This file proves that flat pullback commutes with proper pushforward along the two
closed immersions of that square:

  `f^*(i_* γ) = i'_*(g^* γ)`  in  `Z_{k+r}(X')`,  for `γ ∈ Z_k(W)`.

This is the closed-immersion case of
[Stacks, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG), the case the proof of
[Stacks, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS) uses to read the two sides of that
tag on the inverse image of an integral component.

## Main definitions

* `Stacks.Chow.comapRestrict` — the restriction `g : f^{-1}(W) ⟶ W` of `f`.

## Main results

* `Stacks.Chow.exists_iso_of_ker_eq` — two closed immersions with the same ideal sheaf present
  the same closed subscheme.
* `Stacks.Chow.isPullback_comapRestrict` — the square above is cartesian.
* `Stacks.Chow.flat_comapRestrict`, `Stacks.Chow.locallyOfFiniteType_comapRestrict`,
  `Stacks.Chow.relativeDimension_comapRestrict` — flatness, finite type and relative dimension of
  `g`, by base change (Stacks 02NK).
* `Stacks.Chow.comapRestrict_subschemeι`, `Stacks.Chow.comapRestrict_comp_base`,
  `Stacks.Chow.coe_support_comap` — the square commutes, `g` is a morphism over the base, and the
  support of `W'` is the preimage of the support of `W`.
* `Stacks.Chow.closedSubschemeCycleCoeff_comp_isClosedImmersion` — the multiplicity of a
  component of a closed subscheme `Z ⊆ A` is the same whether read in `A` or in an ambient scheme
  `B` of which `A` is a closed subscheme.
* `Stacks.Chow.subschemeι_genericPoint_integralComponentAt` — the generic point of the integral
  closed subscheme attached to a point maps to that point.
* `Stacks.Chow.flatPullbackWeight_comapRestrict` — the flat pullback multiplicity of a point of
  `W'` along `g` is its multiplicity along `f`.
* `Stacks.Chow.flatPullback_properPushforward_comap` — the identity above.
* `Stacks.Chow.closedSubschemeCycleCoeff_comap_subschemeι_of_eq`,
  `Stacks.Chow.flatPullbackWeight_eq_cycleAssociatedToClosedSubscheme_id` — the flat pullback
  multiplicity at a point of `f^{-1}(W)` over the generic point of `W` is that point's
  coefficient in the fundamental cycle of `f^{-1}(W)`, which is the weighting Stacks 0EPJ uses.

## Implementation notes

The weight comparison is the whole content. Both multiplicities are coefficients of the cycle of
a scheme-theoretic inverse image, and `Stacks.Chow.closedSubschemeCycleCoeff_comap_eq_pullbackFst`
turns each into a coefficient of the cycle of a categorical pullback: `X' ×_X V` for the integral
component `V` of the image point, and `W' ×_W V₀` for the integral component `V₀` of the point
itself. Pasting the cartesian square above onto the second identifies it with `X' ×_X V₀`, and
`V₀ ⊆ W ⊆ X` and `V ⊆ X` are the same closed subscheme of `X` because
`Stacks.Chow.map_integralComponentAt` says their ideal sheaves agree. Two closed immersions with
equal ideal sheaf differ by an isomorphism, which is
`Stacks.Chow.exists_iso_of_ker_eq`, and `Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso` absorbs
it.

That the square is cartesian is Mathlib's `AlgebraicGeometry.isPullback_of_isClosedImmersion`,
applied to the two closed immersions.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two closed immersions with the same ideal sheaf -/

/-- Two closed immersions into `X` with the same kernel ideal sheaf present the same closed
subscheme: each factors through the other, and a closed immersion is a monomorphism. -/
theorem exists_iso_of_ker_eq {X A B : Scheme.{u}} (a : A ⟶ X) [IsClosedImmersion a] (b : B ⟶ X)
    [IsClosedImmersion b] (h : a.ker = b.ker) : ∃ e : A ≅ B, e.hom ≫ b = a := by
  refine ⟨⟨IsClosedImmersion.lift b a (le_of_eq h.symm),
    IsClosedImmersion.lift a b (le_of_eq h), ?_, ?_⟩, IsClosedImmersion.lift_fac b a _⟩
  · refine (cancel_mono a).1 ?_
    rw [Category.assoc, IsClosedImmersion.lift_fac a b, IsClosedImmersion.lift_fac b a,
      Category.id_comp]
  · refine (cancel_mono b).1 ?_
    rw [Category.assoc, IsClosedImmersion.lift_fac b a, IsClosedImmersion.lift_fac a b,
      Category.id_comp]

/-! ### The inverse image of a closed subscheme -/

/-- The restriction `f^{-1}(W) ⟶ W` of a morphism `f : X' ⟶ X` to the scheme-theoretic inverse
image of a closed subscheme `W ⊆ X`. -/
def comapRestrict {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X) :
    (W.comap f).subscheme ⟶ W.subscheme :=
  (W.comap f).subschemeMap W f (W.le_map_comap f)

/-- The inverse image square of a closed subscheme commutes. -/
@[reassoc (attr := simp)]
theorem comapRestrict_subschemeι {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X) :
    comapRestrict W f ≫ W.subschemeι = (W.comap f).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The inverse image square of a closed subscheme is cartesian. -/
theorem isPullback_comapRestrict {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X) :
    IsPullback (W.comap f).subschemeι (comapRestrict W f) f W.subschemeι :=
  isPullback_of_isClosedImmersion (W.comap f).subschemeι W.subschemeι (comapRestrict W f) f
    (by simp) (by simp [Scheme.IdealSheafData.ker_subschemeι])

/-- Flatness is stable under base change, so the restriction of a flat morphism to the inverse
image of a closed subscheme is flat. -/
theorem flat_comapRestrict {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X) [Flat f] :
    Flat (comapRestrict W f) :=
  MorphismProperty.of_isPullback (isPullback_comapRestrict W f) inferInstance

/-- Being locally of finite type is stable under base change. -/
theorem locallyOfFiniteType_comapRestrict {X' X : Scheme.{u}} (W : X.IdealSheafData)
    (f : X' ⟶ X) [LocallyOfFiniteType f] : LocallyOfFiniteType (comapRestrict W f) :=
  MorphismProperty.of_isPullback (isPullback_comapRestrict W f) inferInstance

/-- **Stacks 02NK** for the inverse image of a closed subscheme: the restriction of a morphism of
relative dimension `r` to the inverse image of a closed subscheme again has relative
dimension `r`. -/
theorem relativeDimension_comapRestrict {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X)
    [LocallyOfFiniteType f] {r : ℕ} (hf : AlgebraicGeometry.RelativeDimension f r) :
    letI := locallyOfFiniteType_comapRestrict W f
    AlgebraicGeometry.RelativeDimension (comapRestrict W f) r := by
  let _ := locallyOfFiniteType_comapRestrict W f
  exact AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_comapRestrict W f) hf

/-- The restriction to the inverse image is a morphism over the base. -/
theorem comapRestrict_comp_base (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    (sX : X ⟶ C.S) (f : X' ⟶ X) (hbase : f ≫ sX = sX') (W : X.IdealSheafData) :
    comapRestrict W f ≫ (W.subschemeι ≫ sX) = (W.comap f).subschemeι ≫ sX' := by
  rw [← Category.assoc, comapRestrict_subschemeι, Category.assoc, hbase]

/-- The inverse image square of a closed subscheme commutes on points. -/
private theorem subschemeι_comapRestrict_base {X' X : Scheme.{u}} (W : X.IdealSheafData)
    (f : X' ⟶ X) (z : (W.comap f).subscheme) :
    W.subschemeι.base ((comapRestrict W f).base z) = f.base ((W.comap f).subschemeι.base z) :=
  congrArg (fun φ : (W.comap f).subscheme ⟶ X ↦ φ.base z) (comapRestrict_subschemeι W f)

/-- The support of the inverse image of a closed subscheme is the preimage of its support. -/
theorem coe_support_comap {X' X : Scheme.{u}} (W : X.IdealSheafData) (f : X' ⟶ X) :
    (((W.comap f).support : Closeds X') : Set X') = f.base ⁻¹' (W.support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]

/-! ### Multiplicities read in a closed subscheme of the ambient scheme -/

/-- The coefficient of the cycle of a closed subscheme `Z ⊆ A` is unchanged when `A` is itself
read as a closed subscheme of `B`: both are the length of the stalk of `Z` over itself. -/
theorem closedSubschemeCycleCoeff_comp_isClosedImmersion (C : ChowSituation.{u})
    {A B Z : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (j : A ⟶ B) [IsClosedImmersion j] (hj : j ≫ sB = sA)
    (i : Z ⟶ A) [IsClosedImmersion i] (k : ℤ) (a : A) :
    closedSubschemeCycleCoeff C sB (i ≫ j) k (j.base a) =
      closedSubschemeCycleCoeff C sA i k a := by
  have h := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    C sA sB j hj i k
  change (cycleAssociatedToClosedSubscheme C sB (i ≫ j) k).1 (j.base a) =
    (cycleAssociatedToClosedSubscheme C sA i k).1 a
  rw [← h]
  exact properPushforward_apply_image_of_isClosedImmersion C sA sB j hj k _ a

/-! ### The flat pullback multiplicity on the inverse image -/

/-- The generic point of the integral closed subscheme attached to a point maps to that point. -/
theorem subschemeι_genericPoint_integralComponentAt {X : Scheme.{u}} (x : X) :
    letI := isIntegral_integralComponentAt x
    (integralComponentAt x).subschemeι.base (genericPoint (integralComponentAt x).subscheme)
      = x :=
  genericPointOf_integralComponentAt x

/-- The multiplicity with which a point of `f^{-1}(W)` enters a flat pullback is the same read
along `f` and read along the restriction `g : f^{-1}(W) ⟶ W`.

Both multiplicities are coefficients of the cycle of a scheme-theoretic inverse image of an
integral closed subscheme, hence of a categorical pullback; pasting the cartesian square of
`Stacks.Chow.isPullback_comapRestrict` identifies the two pullbacks, the integral component of
the image point in `W` and in `X` being the same closed subscheme of `X`. -/
theorem flatPullbackWeight_comapRestrict (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X) (W : X.IdealSheafData) (j : ℤ)
    (z : (W.comap f).subscheme) :
    flatPullbackWeight C ((W.comap f).subschemeι ≫ sX') (comapRestrict W f) j z =
      flatPullbackWeight C sX' f j ((W.comap f).subschemeι.base z) := by
  set ι' := (W.comap f).subschemeι with hι'
  set g := comapRestrict W f with hg
  set V := integralComponentAt (f.base (ι'.base z)) with hV
  set V₀ := integralComponentAt (g.base z) with hV₀
  let _ : IsIntegral V.subscheme := isIntegral_integralComponentAt _
  let _ : IsIntegral V₀.subscheme := isIntegral_integralComponentAt _
  -- the two multiplicities as coefficients of categorical pullbacks
  rw [flatPullbackWeight, flatPullbackWeight,
    closedSubschemeCycleCoeff_comap_eq_pullbackFst C ((W.comap f).subschemeι ≫ sX') g
      V₀.subschemeι j z (subschemeι_genericPoint_integralComponentAt (g.base z)).symm,
    closedSubschemeCycleCoeff_comap_eq_pullbackFst C sX' f V.subschemeι j (ι'.base z)
      (subschemeι_genericPoint_integralComponentAt (f.base (ι'.base z))).symm,
    ← closedSubschemeCycleCoeff_comp_isClosedImmersion C ((W.comap f).subschemeι ≫ sX') sX' ι'
      rfl (pullback.fst g V₀.subschemeι) j z]
  -- the integral component of the image point, read in `W` and read in `X`
  have hker : (V₀.subschemeι ≫ W.subschemeι).ker = V.subschemeι.ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, hV₀, map_integralComponentAt,
      subschemeι_comapRestrict_base, hV]
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq (V₀.subschemeι ≫ W.subschemeι) V.subschemeι hker
  -- the pasted cartesian square, transported along that isomorphism
  have hsq : IsPullback (pullback.fst g V₀.subschemeι ≫ ι')
      (pullback.snd g V₀.subschemeι ≫ e.hom) f V.subschemeι := by
    have h1 : IsPullback (pullback.fst g V₀.subschemeι ≫ ι') (pullback.snd g V₀.subschemeι) f
        (V₀.subschemeι ≫ W.subschemeι) :=
      (IsPullback.of_hasPullback g V₀.subschemeι).paste_horiz (isPullback_comapRestrict W f)
    have h2 : IsPullback (V₀.subschemeι ≫ W.subschemeι) e.hom (𝟙 X) V.subschemeι :=
      IsPullback.of_vert_isIso ⟨by simpa using he.symm⟩
    simpa using h1.paste_vert h2
  have hpb := IsPullback.of_hasPullback f V.subschemeι
  exact closedSubschemeCycleCoeff_eq_of_iso C sX' (pullback.fst g V₀.subschemeι ≫ ι')
    (pullback.fst f V.subschemeι) (hsq.isoIsPullback _ _ hpb)
    (hsq.isoIsPullback_hom_fst _ _ hpb) j (ι'.base z)

/-! ### Stacks 02RG for the inverse image of a closed subscheme -/

/-- **Stacks 02RG for a closed immersion base change, on cycles.** For `f : X' ⟶ X` flat of
relative dimension `r` and `W ⊆ X` a closed subscheme, flat pullback along `f` carries the
pushforward of a `k`-cycle on `W` to the pushforward of its flat pullback along the restriction
`g : f^{-1}(W) ⟶ W`:

  `f^*(i_* γ) = i'_*(g^* γ)`  in  `Z_{k+r}(X')`.

Read at a point of `X'` in the inverse image both sides are the coefficient of `γ` at the image
point times a flat pullback multiplicity, and the two multiplicities agree by
`Stacks.Chow.flatPullbackWeight_comapRestrict`; off the inverse image both sides vanish, the left
one because the support of `i_* γ` misses the image of the point. -/
theorem flatPullback_properPushforward_comap (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (W : X.IdealSheafData)
    (γ : CycleGroup C (W.subschemeι ≫ sX) k) :
    letI := locallyOfFiniteType_comapRestrict W f
    letI := flat_comapRestrict W f
    flatPullback C sX' sX f hbase r hf k
        (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ) =
      properPushforward C ((W.comap f).subschemeι ≫ sX') sX' (W.comap f).subschemeι rfl
        (k + (r : ℤ))
        (flatPullback C ((W.comap f).subschemeι ≫ sX') (W.subschemeι ≫ sX) (comapRestrict W f)
          (comapRestrict_comp_base C sX' sX f hbase W) r
          (relativeDimension_comapRestrict W f hf) k γ) := by
  let _ := locallyOfFiniteType_comapRestrict W f
  let _ := flat_comapRestrict W f
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y' ↦ ?_)
  rw [flatPullback_apply]
  by_cases hy : y' ∈ Set.range (W.comap f).subschemeι.base
  · obtain ⟨z, hz⟩ := hy
    rw [← hz, ← subschemeι_comapRestrict_base, properPushforward_apply_image_of_isClosedImmersion,
      properPushforward_apply_image_of_isClosedImmersion, flatPullback_apply,
      flatPullbackWeight_comapRestrict]
  · have hnot : f.base y' ∉ Set.range W.subschemeι.base := fun hmem ↦ hy <| by
      rw [Scheme.IdealSheafData.range_subschemeι] at hmem ⊢
      rwa [coe_support_comap]
    rw [properPushforward_apply_of_notMem_range C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ
      hnot, zero_mul,
      properPushforward_apply_of_notMem_range C ((W.comap f).subschemeι ≫ sX') sX'
        (W.comap f).subschemeι rfl (k + (r : ℤ)) _ hy]

/-! ### The multiplicity read on the inverse image of an integral component -/

/-- The coefficient, at a point of `f^{-1}(J)`, of the cycle of `f^{-1}(I)` read in `X'` is, for
`I = J`, the coefficient of that point in the fundamental cycle of `f^{-1}(J)` read inside
`f^{-1}(J)`. Stating it for two equal ideal sheaves lets the two sides use different expressions
for the same closed subscheme. -/
theorem closedSubschemeCycleCoeff_comap_subschemeι_of_eq (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X)
    (I J : X.IdealSheafData) (hIJ : I = J) (j : ℤ) (z : (J.comap f).subscheme) :
    closedSubschemeCycleCoeff C sX' (I.comap f).subschemeι j
        ((J.comap f).subschemeι.base z) =
      (cycleAssociatedToClosedSubscheme C ((J.comap f).subschemeι ≫ sX') (𝟙 _) j).1 z := by
  subst hIJ
  have h2 := closedSubschemeCycleCoeff_eq_of_iso C sX'
    (𝟙 (I.comap f).subscheme ≫ (I.comap f).subschemeι) (I.comap f).subschemeι (Iso.refl _)
    (by simp) j ((I.comap f).subschemeι.base z)
  have h3 := closedSubschemeCycleCoeff_comp_isClosedImmersion C
    ((I.comap f).subschemeι ≫ sX') sX' (I.comap f).subschemeι rfl
    (𝟙 (I.comap f).subscheme) j z
  rw [← h2, h3]
  rfl

/-- **The flat pullback multiplicity is a multiplicity of the fundamental cycle of the inverse
image.** At a point of `f^{-1}(W)` lying over the generic point `x` of the integral closed
subscheme `W = closure {x}`, the multiplicity with which that point enters a flat pullback along
`f` is its coefficient in the fundamental cycle of `f^{-1}(W)`.

The multiplicity of `Stacks.Chow.flatPullbackWeight` is by definition a coefficient of the cycle
of `f^{-1}(closure {x})` read in `X'`; this reads it inside `f^{-1}(W)` instead, which is where
[Stacks, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ) weights its sum over the
irreducible components of that inverse image. -/
theorem flatPullbackWeight_eq_cycleAssociatedToClosedSubscheme_id (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X) (x : X) (j : ℤ)
    (z : ((integralComponentAt x).comap f).subscheme)
    (hz : f.base (((integralComponentAt x).comap f).subschemeι.base z) = x) :
    flatPullbackWeight C sX' f j (((integralComponentAt x).comap f).subschemeι.base z) =
      (cycleAssociatedToClosedSubscheme C
        (((integralComponentAt x).comap f).subschemeι ≫ sX') (𝟙 _) j).1 z := by
  rw [flatPullbackWeight]
  exact closedSubschemeCycleCoeff_comap_subschemeι_of_eq C sX' f _ (integralComponentAt x)
    (congrArg (fun t : X ↦
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({t} : Set X))) hz) j z

end Stacks.Chow

end
