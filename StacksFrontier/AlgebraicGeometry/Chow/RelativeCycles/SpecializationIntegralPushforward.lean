module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrDegreeSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension

/-!
# Specialization of a fundamental cycle, against proper pushforward

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Y` be a proper morphism of schemes locally of finite type over `R`, let `r ≥ 0` and let
`ξ` be a point of the generic fibre `X_K` of dimension `r`, that is the generic point of an
integral closed subscheme `Z ⊆ X_K` of dimension `r`. This file proves the identity

  `f_{κ,*}(sp_{X/R}[Z]) = d · sp_{Y/R}[Z']`,  `Z' = f(Z)`,  `d` the pushforward weight of `ξ`,

of [Stacks, Tag 0H4M].

## Main results

* `Stacks.Chow.fiberProperPushforward_comp`, `Stacks.Chow.fiberProperPushforward_congr` —
  functoriality of fibrewise proper pushforward, and its independence of the chosen proof that
  the morphism lies over the base.
* `Stacks.Chow.exists_fiberι_eq_genericPoint` — a scheme over `R` whose generic point lies over
  the generic point of `Spec R` has a point of its generic fibre above that generic point.
* `Stacks.Chow.fiberPushforwardWeight_of_square` — the pushforward weight is unchanged by a
  square of closed immersions.
* `Stacks.Chow.properPushforward_specializationIntegralCycle` — the identity described above.

## References

* [Stacks Project, Tag 0H4M](https://stacks.math.columbia.edu/tag/0H4M)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Functoriality of fibrewise proper pushforward -/

/-- Fibrewise proper pushforward depends on the morphism over the base alone, not on the chosen
proof that it lies over the base. -/
theorem fiberProperPushforward_congr {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [IsProper f] [IsProper f']
    (hff' : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (s : S) (r : ℕ)
    (c : FiberCycleGroup sX s r) :
    fiberProperPushforward sX sY f hf s r c = fiberProperPushforward sX sY f' hf' s r c := by
  subst hff'
  rfl

/-- **Stacks 02R5 on the fibres.** Fibrewise proper pushforward is functorial: pushing forward
along `f` and then along `g` is pushing forward along `f ≫ g`. -/
theorem fiberProperPushforward_comp {X Y Z S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] (sZ : Z ⟶ S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [IsProper f] (g : Y ⟶ Z) [IsProper g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (s : S)
    (r : ℕ) (c : FiberCycleGroup sX s r) :
    fiberProperPushforward sY sZ g hg s r (fiberProperPushforward sX sY f hf s r c) =
      fiberProperPushforward sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) s r c := by
  have hcomp := properPushforward_properPushforward
    (fieldChowSituation (S.residueField s)) (sX.fiberToSpecResidueField s)
    (sY.fiberToSpecResidueField s) (sZ.fiberToSpecResidueField s)
    (inducedFiberMap sX sY f hf s) (inducedFiberMap sY sZ g hg s)
    (inducedFiberMap_fiberToSpecResidueField sX sY f hf s)
    (inducedFiberMap_fiberToSpecResidueField sY sZ g hg s) (r : ℤ) c
  refine hcomp.trans ?_
  exact properPushforward_hom_congr (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sZ.fiberToSpecResidueField s)
    (inducedFiberMap_comp sX sY sZ f g hf hg s).symm _ _ (r : ℤ) c

/-- Fibrewise proper pushforward is additive, hence commutes with integer multiples. -/
theorem fiberProperPushforward_zsmul {X Y S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (s : S)
    (r : ℕ) (n : ℤ) (c : FiberCycleGroup sX s r) :
    fiberProperPushforward sX sY f hf s r (n • c) =
      n • fiberProperPushforward sX sY f hf s r c :=
  map_zsmul (properPushforwardHom (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
    (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)) n c

/-! ### A point of the generic fibre above the generic point -/

/-- A point of a scheme over `S` lying over `s` is the image of a point of the fibre over `s`. -/
theorem exists_fiberι_eq {X S : Scheme.{u}} (p : X ⟶ S) {s : S} {x : X} (hx : p.base x = s) :
    ∃ z : p.fiber s, (p.fiberι s).base z = x := by
  have hmem : x ∈ Set.range (p.fiberι s).base := by
    rw [Scheme.Hom.range_fiberι]
    exact hx
  exact hmem

/-- For an irreducible scheme over `S` whose generic point lies over `s`, the fibre over `s` has
a point above that generic point. -/
theorem exists_fiberι_eq_genericPoint {X S : Scheme.{u}} [IrreducibleSpace X] (p : X ⟶ S)
    {s : S} (hp : p.base (genericPoint X) = s) :
    ∃ z : p.fiber s, (p.fiberι s).base z = genericPoint X :=
  exists_fiberι_eq p hp

/-! ### The square of induced fibre maps -/

/-- A commuting square of morphisms over the base induces a commuting square of morphisms of
fibres: both composites are the fibre map of the common composite. -/
theorem inducedFiberMap_square {S X Y V V' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sV : V ⟶ S)
    (sV' : V' ⟶ S) (f : X ⟶ Y) (jX : V ⟶ X) (jY : V' ⟶ Y) (g : V ⟶ V') (hf : f ≫ sY = sX)
    (hjX : jX ≫ sX = sV) (hjY : jY ≫ sY = sV') (hg : g ≫ sV' = sV) (hsq : g ≫ jY = jX ≫ f)
    (s : S) :
    inducedFiberMap sV sV' g hg s ≫ inducedFiberMap sV' sY jY hjY s =
      inducedFiberMap sV sX jX hjX s ≫ inducedFiberMap sX sY f hf s := by
  rw [← inducedFiberMap_comp sV sV' sY g jY hg hjY s,
    ← inducedFiberMap_comp sV sX sY jX f hjX hf s]
  exact inducedFiberMap_congr sV sY _ _ s hsq _

/-- The dimension of a point of a fibre is unchanged by a closed immersion over the base: a
closed immersion induces an isomorphism on residue fields. -/
theorem fiberPointDimension_inducedFiberMap {S X V : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sV : V ⟶ S) [LocallyOfFiniteType sV] (jX : V ⟶ X)
    [IsClosedImmersion jX] (hjX : jX ≫ sX = sV) (s : S) (ξV : sV.fiber s) :
    fiberPointDimension sV s ξV =
      fiberPointDimension sX s ((inducedFiberMap sV sX jX hjX s).base ξV) := by
  have : IsIso ((inducedFiberMap sV sX jX hjX s).residueFieldMap ξV) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_isPreimmersion _ ξV
  have h := relativeDimension_comp_of_bijective_residueFieldMap
    (fieldChowSituation (S.residueField s)).dimensionFunction (inducedFiberMap sV sX jX hjX s)
    (sX.fiberToSpecResidueField s) ξV (ConcreteCategory.bijective_of_isIso _)
  rwa [inducedFiberMap_fiberToSpecResidueField] at h

/-- The pushforward weight is unchanged by a square of closed immersions: for `g : V ⟶ V'` the
restriction of `f` along closed immersions `jX`, `jY`, the weight of `g` at a point of a fibre of
`V` is the weight of `f` at its image. -/
theorem fiberPushforwardWeight_of_square {S X Y V V' : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (sV : V ⟶ S)
    [LocallyOfFiniteType sV] (sV' : V' ⟶ S) [LocallyOfFiniteType sV'] (f : X ⟶ Y)
    (jX : V ⟶ X) [IsClosedImmersion jX] (jY : V' ⟶ Y) [IsClosedImmersion jY] (g : V ⟶ V')
    (hf : f ≫ sY = sX) (hjX : jX ≫ sX = sV) (hjY : jY ≫ sY = sV') (hg : g ≫ sV' = sV)
    (hsq : g ≫ jY = jX ≫ f) (s : S) (ξV : sV.fiber s) :
    fiberPushforwardWeight sV sV' g hg s ξV =
      fiberPushforwardWeight sX sY f hf s ((inducedFiberMap sV sX jX hjX s).base ξV) := by
  have hdimX := fiberPointDimension_inducedFiberMap sX sV jX hjX s ξV
  have hdimY := fiberPointDimension_inducedFiberMap sY sV' jY hjY s
    ((inducedFiberMap sV sV' g hg s).base ξV)
  have hsquare := inducedFiberMap_square sX sY sV sV' f jX jY g hf hjX hjY hg hsq s
  have hsqpt : (inducedFiberMap sV' sY jY hjY s).base
        ((inducedFiberMap sV sV' g hg s).base ξV) =
      (inducedFiberMap sX sY f hf s).base ((inducedFiberMap sV sX jX hjX s).base ξV) := by
    have h2 : (inducedFiberMap sV sV' g hg s ≫ inducedFiberMap sV' sY jY hjY s).base ξV =
        (inducedFiberMap sV sX jX hjX s ≫ inducedFiberMap sX sY f hf s).base ξV := by
      rw [hsquare]
    simpa using h2
  have hdeg : (inducedFiberMap sV sV' g hg s).residueDegree ξV =
      (inducedFiberMap sX sY f hf s).residueDegree
        ((inducedFiberMap sV sX jX hjX s).base ξV) := by
    have h := congrArg (fun φ : sV.fiber s ⟶ sY.fiber s ↦ φ.residueDegree ξV) hsquare
    simp only [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion, one_mul,
      mul_one] at h
    exact h
  unfold fiberPushforwardWeight
  unfold fiberPointDimension at hdimX hdimY
  rw [hdimX, hdimY, hsqpt, hdeg]

/-! ### The reduction to the schematic closure -/

section Reduction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X Y : Scheme.{u}}

omit [IsDiscreteValuationRing R] in
/-- The generic point of the integral closed subscheme through a point lying over the generic
point of `Spec R` again lies over that generic point. -/
theorem base_genericPoint_integralComponentAt (sX : X ⟶ Spec (.of R)) {x₀ : X}
    (hx₀ : sX.base x₀ = genericPoint (Spec (.of R))) :
    letI := isIntegral_integralComponentAt x₀
    ((integralComponentAt x₀).subschemeι ≫ sX).base
        (genericPoint (integralComponentAt x₀).subscheme) = genericPoint (Spec (.of R)) := by
  show sX.base ((integralComponentAt x₀).subschemeι.base _) = _
  rw [subschemeι_genericPoint_integralComponentAt x₀]
  exact hx₀

/-- A point `ξ` of the generic fibre lying over `x₀` lifts to a point `ξV` of the generic fibre of
the integral component through `x₀`, whose specialization cycle is the cycle of the special
fibre. -/
private theorem exists_fiber_point_integralComponentAt (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (r : ℕ) (ξ : sX.fiber (genericPoint (Spec (.of R)))) {x₀ : X}
    (hξ : (sX.fiberι (genericPoint (Spec (.of R)))).base ξ = x₀) :
    letI := isIntegral_integralComponentAt x₀
    ∃ ξV : ((integralComponentAt x₀).subschemeι ≫ sX).fiber (genericPoint (Spec (.of R))),
      (((integralComponentAt x₀).subschemeι ≫ sX).fiberι (genericPoint (Spec (.of R)))).base ξV =
          genericPoint (integralComponentAt x₀).subscheme ∧
        (inducedFiberMap ((integralComponentAt x₀).subschemeι ≫ sX) sX
          (integralComponentAt x₀).subschemeι rfl (genericPoint (Spec (.of R)))).base ξV = ξ ∧
        specializationIntegralCycle ((integralComponentAt x₀).subschemeι ≫ sX) r ξV =
          fiberSubschemeCycle ((integralComponentAt x₀).subschemeι ≫ sX)
            (IsLocalRing.closedPoint R) r ⊥ := by
  have := isIntegral_integralComponentAt x₀
  obtain ⟨ξV, hξV⟩ := exists_fiberι_eq_genericPoint ((integralComponentAt x₀).subschemeι ≫ sX)
    (base_genericPoint_integralComponentAt sX (hξ ▸ base_fiberι sX _ ξ))
  refine ⟨ξV, hξV, ?_, ?_⟩
  · refine (sX.fiberι (genericPoint (Spec (.of R)))).isEmbedding.injective ?_
    rw [inducedFiberMap_fiberι_base, hξV, subschemeι_genericPoint_integralComponentAt, hξ]
  · change fiberSubschemeCycle _ _ r (specializationSpecialFibre _ ξV) = _
    rw [specializationSpecialFibre_eq_bot _ ξV hξV]

/-- Given a commuting square of closed immersions `jX`, `jY` under `f` and a morphism `g` between
their sources, if the specializations of the two fundamental cycles are the cycles of the whole
special fibres of the sources, the identity of [Stacks, Tag 0H4M] at `ξ` follows from the
identity for `g`. -/
private theorem properPushforward_specializationIntegralCycle_aux {V V' : Scheme.{u}}
    (sX : X ⟶ Spec (.of R)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r : ℕ) (jX : V ⟶ X)
    [IsClosedImmersion jX] (jY : V' ⟶ Y) [IsClosedImmersion jY] (g : V ⟶ V') [IsProper g]
    (hsq : g ≫ jY = jX ≫ f) (ξ : sX.fiber (genericPoint (Spec (.of R))))
    (ξV : (jX ≫ sX).fiber (genericPoint (Spec (.of R))))
    (hξV : (inducedFiberMap (jX ≫ sX) sX jX rfl (genericPoint (Spec (.of R)))).base ξV = ξ)
    (ζV' : (jY ≫ sY).fiber (genericPoint (Spec (.of R))))
    (hζV' : (inducedFiberMap (jY ≫ sY) sY jY rfl (genericPoint (Spec (.of R)))).base ζV' =
      (inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base ξ)
    (hB : specializationIntegralCycle (jX ≫ sX) r ξV =
      fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥)
    (hB' : specializationIntegralCycle (jY ≫ sY) r ζV' =
      fiberSubschemeCycle (jY ≫ sY) (IsLocalRing.closedPoint R) r ⊥)
    (hkey : fiberProperPushforward (jX ≫ sX) (jY ≫ sY) g
        (by rw [← Category.assoc, hsq, Category.assoc, hf]) (IsLocalRing.closedPoint R) r
        (fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥) =
      fiberPushforwardWeight sX sY f hf (genericPoint (Spec (.of R))) ξ •
        fiberSubschemeCycle (jY ≫ sY) (IsLocalRing.closedPoint R) r ⊥) :
    fiberProperPushforward sX sY f hf (IsLocalRing.closedPoint R) r
        (specializationIntegralCycle sX r ξ) =
      fiberPushforwardWeight sX sY f hf (genericPoint (Spec (.of R))) ξ •
        specializationIntegralCycle sY r
          ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base ξ) := by
  have hA := specializationIntegralCycle_inducedFiberMap (jX ≫ sX) sX jX rfl r ξV
  rw [hξV, hB] at hA
  have hA' := specializationIntegralCycle_inducedFiberMap (jY ≫ sY) sY jY rfl r ζV'
  rw [hζV', hB'] at hA'
  rw [hA, hA']
  have h1 := fiberProperPushforward_comp (jX ≫ sX) sX sY jX f rfl hf
    (IsLocalRing.closedPoint R) r
    (fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥)
  have h2 : fiberProperPushforward (jX ≫ sX) sY (jX ≫ f) (by rw [Category.assoc, hf])
        (IsLocalRing.closedPoint R) r
        (fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥) =
      fiberProperPushforward (jX ≫ sX) sY (g ≫ jY)
        (by rw [hsq, Category.assoc, hf])
        (IsLocalRing.closedPoint R) r
        (fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥) :=
    fiberProperPushforward_congr (jX ≫ sX) sY hsq.symm _ _ (IsLocalRing.closedPoint R) r _
  have h3 := fiberProperPushforward_comp (jX ≫ sX) (jY ≫ sY) sY g jY
    (by rw [← Category.assoc, hsq, Category.assoc, hf]) rfl (IsLocalRing.closedPoint R) r
    (fiberSubschemeCycle (jX ≫ sX) (IsLocalRing.closedPoint R) r ⊥)
  rw [h1, h2, ← h3, hkey]
  exact fiberProperPushforward_zsmul (jY ≫ sY) sY jY rfl (IsLocalRing.closedPoint R) r _ _

/-- The identity of [Stacks, Tag 0H4M] for a fundamental cycle: for a point `ξ` of the generic
fibre of `X` of dimension `r`, pushing the specialization of the fundamental cycle of `ξ` forward
along the morphism of closed fibres gives the specialization of the fundamental cycle of the
image of `ξ`, weighted by the pushforward weight of `ξ`. -/
theorem properPushforward_specializationIntegralCycle
    (sX : X ⟶ Spec (.of R)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r : ℕ)
    (ξ : sX.fiber (genericPoint (Spec (.of R))))
    (hdim : fiberPointDimension sX (genericPoint (Spec (.of R))) ξ = (r : ℤ))
 :
    fiberProperPushforward sX sY f hf (IsLocalRing.closedPoint R) r
        (specializationIntegralCycle sX r ξ) =
      fiberPushforwardWeight sX sY f hf (genericPoint (Spec (.of R))) ξ •
        specializationIntegralCycle sY r
          ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base ξ) := by
  set x₀ : X := (sX.fiberι (genericPoint (Spec (.of R)))).base ξ with hx₀def
  have := isIntegral_integralComponentAt x₀
  have := isIntegral_integralComponentAt (f.base x₀)
  have hy₀ : (sY.fiberι (genericPoint (Spec (.of R)))).base
      ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base ξ) = f.base x₀ :=
    inducedFiberMap_fiberι_base sX sY f hf _ ξ
  obtain ⟨ξV, hξV, hξVmap, hB⟩ := exists_fiber_point_integralComponentAt sX r ξ hx₀def.symm
  obtain ⟨ζV', -, hζV'map, hB'⟩ := exists_fiber_point_integralComponentAt sY r _ hy₀
  have hdimV : fiberPointDimension ((integralComponentAt x₀).subschemeι ≫ sX)
      (genericPoint (Spec (.of R))) ξV = (r : ℤ) := by
    rw [fiberPointDimension_inducedFiberMap sX ((integralComponentAt x₀).subschemeι ≫ sX)
      (integralComponentAt x₀).subschemeι rfl (genericPoint (Spec (.of R))) ξV, hξVmap]
    exact hdim
  have hsq : integralComponentMap f x₀ ≫ (integralComponentAt (f.base x₀)).subschemeι =
      (integralComponentAt x₀).subschemeι ≫ f := integralComponentMap_subschemeι f x₀
  have hgg : integralComponentMap f x₀ ≫
        ((integralComponentAt (f.base x₀)).subschemeι ≫ sY) =
      (integralComponentAt x₀).subschemeι ≫ sX := by
    rw [← Category.assoc, hsq, Category.assoc, hf]
  have hK := properPushforward_fiberSubschemeCycle_bot
    ((integralComponentAt x₀).subschemeι ≫ sX)
    ((integralComponentAt (f.base x₀)).subschemeι ≫ sY) (integralComponentMap f x₀) hgg r ξV
    hξV hdimV
  have hw := fiberPushforwardWeight_of_square sX sY ((integralComponentAt x₀).subschemeι ≫ sX)
    ((integralComponentAt (f.base x₀)).subschemeι ≫ sY) f (integralComponentAt x₀).subschemeι
    (integralComponentAt (f.base x₀)).subschemeι (integralComponentMap f x₀) hf rfl rfl hgg hsq
    (genericPoint (Spec (.of R))) ξV
  rw [hξVmap] at hw
  rw [hw] at hK
  exact properPushforward_specializationIntegralCycle_aux sX sY f hf r
    (integralComponentAt x₀).subschemeι (integralComponentAt (f.base x₀)).subschemeι
    (integralComponentMap f x₀) hsq ξ ξV hξVmap ζV' hζV'map hB hB' hK

end Reduction

end Stacks.Chow

end

