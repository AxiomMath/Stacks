module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FiberLocalization
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.StalkGenerator
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import StacksCore.Tactic.StacksAttribute

/-!
# Fibre rings of a stalk map, from integrality of the fibres

The penultimate paragraph of Stacks Tag 0BD7 is applied in the source to
`Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}`, and
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/StalkGenerator.lean` reduces its primality
hypothesis to: *every fibre ring `Ideal.Fiber 𝔭 𝒪_{X, x}` is a domain*, for `𝔭` an arbitrary
prime of `𝒪_{Y, y}`. `FiberLocalization.lean` crosses that ring with the fibre ring of an affine
chart, leaving the chart itself. This file supplies the chart, and with it the hypothesis.

The chart is a pair of affine opens `x ∈ U` of `X` and `y = f x ∈ V` of `Y` with `f(U) ⊆ V`
(`AlgebraicGeometry.exists_affine_chart_mem`); no point of `Y` other than `f x` has to be
arranged, because the point `y'` whose fibre carries the integrality hypothesis is a
generalization of `y` and so lies in every open containing `y`.

Two things then have to be proved, and the second is the one that is not formal.

* The fibre ring `Ideal.Fiber 𝔮 Γ(X, U)` of the chart, for `𝔮` a prime of `Γ(Y, V)`, is the ring
  of the scheme-theoretic fibre `X_{y'} ∩ U`, hence a domain when `X_{y'}` is integral. The
  identification is `AlgebraicGeometry.specMapFiberIsoSpecFiberRing` together with two
  comparisons of fibres: `AlgebraicGeometry.fiberCompIsoFiber`, the fibre of `g` is the fibre of
  `g ≫ m` for `m` an open immersion, and `AlgebraicGeometry.fiberCompι`, the fibre of `j ≫ f` is
  an *open subscheme* of the fibre of `f` for `j` an open immersion. The two applied to
  `Spec Γ(X, U) → Spec Γ(Y, V) → Y` and `Spec Γ(X, U) → X → Y` — the same morphism, by
  `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` — exhibit `Spec (Ideal.Fiber 𝔮 Γ(X, U))`
  as an open subscheme of `f.fiber y'`, and integrality passes to a *nonempty* open subscheme
  (`AlgebraicGeometry.isIntegral_of_isOpenImmersion`).

* That open subscheme is nonempty. This is **not** automatic: `Ideal.Fiber 𝔮 Γ(X, U)` is the
  **zero ring** whenever `X_{y'}` misses `U`, and the zero ring is not a domain, so no citation
  of integrality can prove the chart step by itself. The nonvanishing is threaded through from
  the *stalks*, inside
  `Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization`:
  Mathlib's instance `Module.FaithfullyFlat.rTensor_nontrivial`, at the faithfully flat map
  `𝒪_{Y, y} → 𝒪_{X, x}` of a flat morphism, gives `Ideal.Fiber 𝔭 𝒪_{X, x} ≠ 0`,
  `Ideal.fiberComapRingEquivOfIsLocalization` carries that to `Ideal.Fiber 𝔮 𝒪_{X, x}`, and
  `Ideal.nontrivial_fiber_of_nontrivial_fiber` descends it along
  `Ideal.Fiber 𝔮 Γ(X, U) → Ideal.Fiber 𝔮 𝒪_{X, x}`. Geometrically: `Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}`
  is surjective, so some point of `X_{y'}` is a generalization of `x`, and a generalization of `x`
  lies in every open containing `x`. So the chart has to supply integrality of the fibre ring
  only where that ring is nonzero, and that is exactly the hypothesis the `∀`-form of
  `FiberLocalization.lean` asks for.

## Main definitions

* `AlgebraicGeometry.fiberCompι`: for `j : X' ⟶ X` and `f : X ⟶ Y`, the canonical morphism
  `(j ≫ f).fiber y ⟶ f.fiber y`, an open immersion when `j` is one.
* `AlgebraicGeometry.fiberCompIsoFiber`: for `m : V' ⟶ Y` an open immersion and `g : X' ⟶ V'`,
  the fibre of `g` over `v` is the fibre of `g ≫ m` over `m v`.

## Main results

* `AlgebraicGeometry.germ_stalkMap_appLE`: the square `Γ(Y, V) → Γ(X, U) → 𝒪_{X, x}` equals
  `Γ(Y, V) → 𝒪_{Y, f x} → 𝒪_{X, x}`, which is the compatibility of the two scalar towers of the
  chart.
* `AlgebraicGeometry.exists_affine_chart_mem`: the chart.
* `AlgebraicGeometry.isDomain_fiber_appLE_of_isIntegral_fiber`: the fibre ring of the chart is a
  domain, given integrality of the fibre of `f` over the corresponding point and nonvanishing.
* `AlgebraicGeometry.forall_isDomain_fiber_stalkMap_of_chart` and
  `AlgebraicGeometry.forall_isDomain_fiber_stalkMap`: every fibre ring of `𝒪_{Y, f x} → 𝒪_{X, x}`
  is a domain, for `f` flat with integral fibres. This is exactly the hypothesis `hfib` of
  `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber`.
* `AlgebraicGeometry.forall_isPrime_map_stalkMap`: the same, delivered as the source's "by
  assumption `𝔮ᵢ = 𝔭ᵢ A` is a prime" — the hypothesis `hprime` of
  `Ideal.exists_isUnit_mul_eq_of_isUnit`.
* `AlgebraicGeometry.forall_isIntegral_fiber_id` and
  `AlgebraicGeometry.exists_flat_forall_isIntegral_fiber`: the hypothesis pair `[Flat f]` plus
  `∀ y, IsIntegral (f.fiber y)` is inhabited, by the identity of an integral scheme.

## Implementation notes

`Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization`
(`FiberLocalization.lean`) asks for integrality of the chart's fibre ring **only at the primes of
`Γ(Y, V)` where that ring is nonzero**, and the guard is what makes it usable here. Quantified
over *every* prime of `Γ(Y, V)` the hypothesis would be not merely unproved but **false** for a
general chart — for a prime outside the image of `Spec Γ(X, U) → Spec Γ(Y, V)` the fibre ring is
the zero ring, and `Ideal.surjective_comap_of_forall_isDomain_fiber` shows the unguarded form is
equivalent to a surjectivity the tag's hypotheses do not provide. With the guard,
`AlgebraicGeometry.isDomain_fiber_appLE_of_isIntegral_fiber` is the hypothesis verbatim and
`AlgebraicGeometry.forall_isDomain_fiber_stalkMap_of_chart` is one application of it; the
threading of the nonvanishing from the stalks down to the chart happens once, inside that
theorem, instead of being repeated at each consumer.

`IsIso (m.residueFieldMap v)` and `IsIso (m.stalkMap v)` are **not** found by instance search
when `m` is `hV.fromSpec` and `v : PrimeSpectrum Γ(Y, V)`, even with `IsOpenImmersion hV.fromSpec`
in the local context: the point's type has to be unfolded to `↥(Spec Γ(Y, V))` for Mathlib's
instance to apply, and that unfolding is not available to instance search. Both resolve for a
variable `v : V'` of the morphism's own source. So `fiberCompIsoFiber` takes `[IsOpenImmersion m]`
and derives the two inside its proof, rather than taking them as binders; the same statement with
`[Mono m] [IsIso (m.residueFieldMap v)]` as binders cannot be applied at the chart at all.

`IsIso (asIso g).inv` is **not** found by instance search, though `IsIso` of the `hom` of an
isomorphism bound to a **declared type** is — so `AlgebraicGeometry.forall_isIntegral_fiber_id`
names the isomorphism `Spec κ(y) ≅ (𝟙 X).fiber y` with its type written out and applies
`AlgebraicGeometry.IsIntegral.of_isIso` to `e.hom`. The direct
`IsIntegral.of_isIso (asIso g).inv` and `IsIntegral.of_isIso (asIso g).symm.hom` both fail with
`synthInstanceFailed`, while the bare `IsIso (pullback.snd (𝟙 X) _)` is `inferInstance`.

`AlgebraicGeometry.IsOpenImmersion.of_isIso` cannot fire as an instance: its section variables
leaked, so it carries an unrelated `[IsOpenImmersion f]` for an `f` with the same target.
`CategoryTheory.MorphismProperty.RespectsIso.precomp` is used instead, with the isomorphism given
explicitly — passed as `_` it is a metavariable when `IsIso` is sought and the search fails.

Nothing here states a clause of Tag 0BD7: these are statements about `Ideal.Fiber` and about
comparisons of scheme-theoretic fibres, each carrying hypotheses the tag does not (a chart, or a
point of `X`). The tag attribute is therefore withheld from every declaration below.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- **The chart's two scalar towers agree.** For `U ≤ f ⁻¹ᵁ V` and `x ∈ U`, the composite
`Γ(Y, V) → 𝒪_{Y, f x} → 𝒪_{X, x}` is the composite `Γ(Y, V) → Γ(X, U) → 𝒪_{X, x}`. It is
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap` read through the restriction that turns `f.app V`
into `f.appLE V U e`. -/
theorem germ_stalkMap_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) (x : X) (hx : x ∈ U) :
    Y.presheaf.germ V (f x) (e hx) ≫ f.stalkMap x =
      f.appLE V U e ≫ X.presheaf.germ U x hx := by
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
  exact Scheme.Hom.germ_stalkMap f V x (e hx)

/-- **The fibre of `j ≫ f` sits inside the fibre of `f`.** Pasting the pullback square defining
`f.fiber y` with the one defining the base change of `j` along `f.fiberι y`
(`CategoryTheory.Limits.pullbackRightPullbackFstIso`) presents `(j ≫ f).fiber y` as that base
change; the morphism recorded here is the second projection, so it is the base change of `j`. -/
noncomputable def fiberCompι {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    (j ≫ f).fiber y ⟶ f.fiber y :=
  (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv ≫
    pullback.snd j (pullback.fst f (Y.fromSpecResidueField y))

/-- **`AlgebraicGeometry.fiberCompι` is an open immersion when `j` is one**, being the base
change of `j` up to an isomorphism of the source. -/
theorem isOpenImmersion_fiberCompι {X' X Y : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (y : Y) : IsOpenImmersion (fiberCompι j f y) :=
  MorphismProperty.RespectsIso.precomp @IsOpenImmersion
    (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv
    (pullback.snd j (pullback.fst f (Y.fromSpecResidueField y))) inferInstance

/-- **An open immersion on the target does not change a fibre.** For `m : V' ⟶ Y` an open
immersion and `g : X' ⟶ V'`, the fibre of `g` over `v` is the fibre of `g ≫ m` over `m v`: the
right-hand leg `Y.fromSpecResidueField (m v)` factors through `m` because `m` induces an
isomorphism of residue fields, and a pullback along `m` of two morphisms that both factor through
the mono `m` is the pullback of the factors
(`AlgebraicGeometry.pullbackMap_of_comp_mono_isIso`). -/
noncomputable def fiberCompIsoFiber {X' V' Y : Scheme.{u}} (g : X' ⟶ V') (m : V' ⟶ Y)
    [IsOpenImmersion m] (v : V') : g.fiber v ≅ (g ≫ m).fiber (m v) := by
  have hr : Spec.map (m.residueFieldMap v) ≫ Y.fromSpecResidueField (m v) =
      V'.fromSpecResidueField v ≫ m :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField m v
  let m₀ : pullback g (V'.fromSpecResidueField v) ⟶
      pullback (g ≫ m) (V'.fromSpecResidueField v ≫ m) :=
    pullback.map g (V'.fromSpecResidueField v) (g ≫ m) (V'.fromSpecResidueField v ≫ m)
      (𝟙 _) (𝟙 _) m (by simp) (by simp)
  have hm₀ : IsIso m₀ := pullbackMap_of_comp_mono_isIso g (V'.fromSpecResidueField v) m
  let m₁ : pullback (g ≫ m) (V'.fromSpecResidueField v ≫ m) ⟶
      pullback (g ≫ m) (Y.fromSpecResidueField (m v)) :=
    pullback.map (g ≫ m) (V'.fromSpecResidueField v ≫ m) (g ≫ m)
      (Y.fromSpecResidueField (m v)) (𝟙 _) (Spec.map (m.residueFieldMap v)) (𝟙 _)
      (by simp) (by simp [hr])
  have hm₁ : IsIso m₁ := by
    dsimp only [m₁]
    infer_instance
  exact (@asIso _ _ _ _ m₀ hm₀) ≪≫ (@asIso _ _ _ _ m₁ hm₁)

/-- **The chart of obstruction (i) of Stacks Tag 0BD7**: affine opens `x ∈ U` of `X` and
`f x ∈ V` of `Y` with `U ≤ f ⁻¹ᵁ V`. Choose `V` affine around `f x`, then `U` affine around `x`
inside the open `f ⁻¹ᵁ V`; both steps are
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`. -/
theorem exists_affine_chart_mem {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ (V : Y.Opens) (U : X.Opens), IsAffineOpen V ∧ IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ V ∧ x ∈ U := by
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hyV
  exact ⟨V, U, hV, hU, hsub, hxU⟩

/-- **The fibre ring of the chart is a domain.** For affine opens `U ≤ f ⁻¹ᵁ V` and a prime `𝔮`
of `Γ(Y, V)`, `Spec (Ideal.Fiber 𝔮 Γ(X, U))` is an open subscheme of the scheme-theoretic fibre of
`f` over the point `hV.fromSpec 𝔮` — the fibre of `Spec Γ(X, U) → Spec Γ(Y, V)`, which is that
spectrum (`AlgebraicGeometry.specMapFiberIsoSpecFiberRing`), is unchanged by composing with the
open immersion `hV.fromSpec` (`AlgebraicGeometry.fiberCompIsoFiber`) and the resulting fibre of
`Spec Γ(X, U) → X → Y` is open in the fibre of `f` (`AlgebraicGeometry.fiberCompι`).

The nonvanishing hypothesis is not removable: when the fibre misses `U` the fibre ring is the
zero ring, which is not a domain however integral the fibre is. -/
theorem isDomain_fiber_appLE_of_isIntegral_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (hint : IsIntegral (f.fiber (hV.fromSpec q)))
    (hnt : letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Nontrivial (q.asIdeal.Fiber ↑Γ(X, U))) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    IsDomain (q.asIdeal.Fiber ↑Γ(X, U)) := by
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have hnt' : Nontrivial (q.asIdeal.Fiber ↑Γ(X, U)) := hnt
  have hcomm : Spec.map (f.appLE V U e) ≫ hV.fromSpec = hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let e₁ := specMapFiberIsoSpecFiberRing (R := ↑Γ(Y, V)) (S := ↑Γ(X, U)) q
  let e₂ : (Spec.map (f.appLE V U e)).fiber q ≅ (hU.fromSpec ≫ f).fiber (hV.fromSpec q) :=
    hcomm ▸ fiberCompIsoFiber (Spec.map (f.appLE V U e)) hV.fromSpec q
  have : Nonempty ((hU.fromSpec ≫ f).fiber (hV.fromSpec q)) :=
    ((PrimeSpectrum.nonempty_iff_nontrivial.mpr hnt').map (fun z => e₁.inv z)).map
      (fun z => e₂.hom z)
  have hoc : IsOpenImmersion (fiberCompι hU.fromSpec f (hV.fromSpec q)) :=
    isOpenImmersion_fiberCompι hU.fromSpec f (hV.fromSpec q)
  have : IsIntegral ((hU.fromSpec ≫ f).fiber (hV.fromSpec q)) :=
    isIntegral_of_isOpenImmersion (fiberCompι hU.fromSpec f (hV.fromSpec q))
  have : IsIntegral ((Spec.map (f.appLE V U e)).fiber q) := IsIntegral.of_isIso e₂.symm.hom
  exact (affine_isIntegral_iff _).mp (IsIntegral.of_isIso e₁.hom)

/-- **Obstruction (i) of Stacks Tag 0BD7 at a general prime, on a given chart.** For `f` flat
with integral fibres, and affine opens `x ∈ U ≤ f ⁻¹ᵁ V`, every fibre ring of
`𝒪_{Y, f x} → 𝒪_{X, x}` is a domain.

The four algebra structures and the two scalar towers of the chart are built here: `Γ(Y, V)` and
`Γ(X, U)` map to the two stalks by germs, to each other by `f.appLE V U e`, and the two routes
from `Γ(Y, V)` to `𝒪_{X, x}` agree by `AlgebraicGeometry.germ_stalkMap_appLE`. The two
localizations are `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`, and the crossing is
`Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization`, whose single hypothesis
is `AlgebraicGeometry.isDomain_fiber_appLE_of_isIntegral_fiber` with no adjustment: both ask for
integrality of the chart's fibre ring exactly where that ring is nonzero. -/
theorem forall_isDomain_fiber_stalkMap_of_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) (hfib : ∀ y : Y, IsIntegral (f.fiber y)) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    ∀ p : Ideal ↑(Y.presheaf.stalk (f x)), ∀ _ : p.IsPrime,
      IsDomain (p.Fiber ↑(X.presheaf.stalk x)) := by
  let _ : Algebra ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, e hx⟩
  let _ : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra ↑Γ(Y, V) ↑(X.presheaf.stalk x) :=
    ((Y.presheaf.germ V (f x) (e hx)) ≫ f.stalkMap x).hom.toAlgebra
  have _ : IsScalarTower ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower ↑Γ(Y, V) ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_appLE f V U e x hx))
  have _ := hV.isLocalization_stalk ⟨f x, e hx⟩
  have _ := hU.isLocalization_stalk ⟨x, hx⟩
  have _ : Module.FaithfullyFlat ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    Flat.faithfullyFlat_stalkMap f x
  exact Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization
    (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal.primeCompl
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    fun q hq hnt => isDomain_fiber_appLE_of_isIntegral_fiber f hV hU e ⟨q, hq⟩ (hfib _) hnt

/-- **Obstruction (i) of Stacks Tag 0BD7 at a general prime.** For a flat morphism with integral
fibres and any point `x` of `X`, every fibre ring of `𝒪_{Y, f x} → 𝒪_{X, x}` is a domain. This is
the hypothesis `hfib` of `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber`
(`StalkGenerator.lean`), at `R = 𝒪_{Y, f x}` and `A = 𝒪_{X, x}`, read off the fibre hypothesis of
the tag. -/
theorem forall_isDomain_fiber_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y)) (x : X) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    ∀ p : Ideal ↑(Y.presheaf.stalk (f x)), ∀ _ : p.IsPrime,
      IsDomain (p.Fiber ↑(X.presheaf.stalk x)) := by
  obtain ⟨V, U, hV, hU, e, hx⟩ := exists_affine_chart_mem f x
  exact forall_isDomain_fiber_stalkMap_of_chart f hV hU e hx hfib

/-- **The source's "by assumption `𝔮ᵢ = 𝔭ᵢ A` is a prime", at the stalks of a flat morphism with
integral fibres.** For `Y` integral the stalk `𝒪_{Y, f x}` is a domain, so
`Ideal.isPrime_map_of_flat_of_isDomain_fiber` turns
`AlgebraicGeometry.forall_isDomain_fiber_stalkMap` into primality of `𝔭 𝒪_{X, x}` for every prime
`𝔭` of `𝒪_{Y, f x}` — the hypothesis `hprime` of `Ideal.exists_isUnit_mul_eq_of_isUnit`. -/
theorem forall_isPrime_map_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y)) (x : X) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    ∀ p : Ideal ↑(Y.presheaf.stalk (f x)), ∀ _ : p.IsPrime,
      (p.map (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).IsPrime := by
  let _ : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have hfl : Module.Flat ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := Flat.stalkMap f x
  exact fun p hp =>
    Ideal.isPrime_map_of_flat_of_isDomain_fiber p (forall_isDomain_fiber_stalkMap f hfib x p hp)

/-- **The identity of an integral scheme has integral fibres.** The fibre of `𝟙 X` over `y` is
`Spec` of the residue field at `y`, because a pullback along an identity is the other projection,
and the spectrum of a field is integral. -/
theorem forall_isIntegral_fiber_id {X : Scheme.{u}} (y : X) :
    IsIntegral (Scheme.Hom.fiber (𝟙 X) y) := by
  have h1 : IsIntegral (Spec (X.residueField y)) := (affine_isIntegral_iff _).mpr inferInstance
  have e : Spec (X.residueField y) ≅ Scheme.Hom.fiber (𝟙 X) y :=
    (asIso (pullback.snd (𝟙 X) (X.fromSpecResidueField y))).symm
  exact h1.of_isIso e.hom

/-- **The hypothesis pair of this file is inhabited.** `[Flat f]` together with
`∀ y, IsIntegral (f.fiber y)` — hypothesis (3) of Stacks Tag 0BD7 — holds for the identity of any
integral scheme, so `AlgebraicGeometry.forall_isDomain_fiber_stalkMap` and
`AlgebraicGeometry.forall_isPrime_map_stalkMap` are not statements about an empty family. -/
theorem exists_flat_forall_isIntegral_fiber (X : Scheme.{u}) :
    ∃ (Y : Scheme.{u}) (f : X ⟶ Y), Flat f ∧ ∀ y : Y, IsIntegral (f.fiber y) :=
  ⟨X, 𝟙 X, inferInstance, forall_isIntegral_fiber_id⟩

end AlgebraicGeometry

end
