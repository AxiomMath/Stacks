module

public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.ChartAlgebra
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Separated
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0B3I over an affine base: a finite morphism is H-projective

[Stacks, Tag 0B3I] says that a finite morphism `f : X ⟶ S` is projective: there is a closed
immersion `X ⟶ 𝐏(f_*𝒪_X)` over `S`. Its proof is local on the base except for one step — the
passage from the local closed immersions into `𝐏ⁿ` to a single closed immersion into the
projective bundle of `f_*𝒪_X`. **Over an affine base that step is not needed, and what the
argument gives there is stronger than the tag's conclusion**: a closed immersion into `𝐏ⁿ_S`,
which is `Stacks.HProjective.IsHProjective`, the H-projective reading of Tag 01W8. In the source
H-projectivity implies projectivity because `𝐏ⁿ_S = 𝐏(𝒪_S^{n+1})`; in this repository that
implication is blocked by a named missing comparison, recorded under "What is not done".

## The route, and where it is the source's

The source's proof of Tag 0B3I, after reducing to an affine base, reads: write `X = Spec A`,
`S = Spec R`, choose `a₁, …, aₙ ∈ A` generating `A` as an `R`-module, note that
`R[T₀, …, Tₙ] → Sym^*_R(A)` with `T₀ ↦ 1`, `Tᵢ ↦ aᵢ` is surjective, check that the image of the
morphism lands in `D₊(T₀) ≅ 𝐀ⁿ_S` and that `X → 𝐀ⁿ_S` corresponds to the surjection
`R[x₁, …, xₙ] → A`, `xᵢ ↦ aᵢ`, and finally that the resulting immersion is a closed immersion
because `X` is finite over `S`. Each step below is one of those.

* `X` is affine and `Γ(X, 𝒪_X)` is a finite `Γ(S, 𝒪_S)`-module: Mathlib's
  `AlgebraicGeometry.isAffine_of_isAffineHom` and `AlgebraicGeometry.Scheme.Hom.finite_appTop`.
* The surjection is `Stacks.FiniteMorphismProjective.awayEval_surjective` of
  `StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.ChartAlgebra`: the degree-zero
  homogeneous localization `R[T]_{(T₀)}` is the polynomial ring on the affine coordinates `T_j / T₀`
  (`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`), and evaluating those at the generators
  is surjective. The source's `R[T] → Sym^*_R(A)` is not formed: the only consequence it has in
  the argument is this surjection onto the chart, which is obtained directly.
* `Spec` of the surjection is a closed immersion into the chart
  (`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`), and `AlgebraicGeometry.Proj.awayι`
  embeds the chart as the open `D₊(T₀)`, so the composite is an immersion:
  `Stacks.FiniteMorphismProjective.isImmersion_chartImmersion`. This replaces the source's
  verification that the image lands in `D₊(T₀)` — the morphism is *built* through the chart, so
  there is nothing to check.
* `Proj R[T₀, …, Tₙ]` is `𝐏ⁿ` over `Spec R`
  (`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`), and `𝐏ⁿ` over isomorphic bases
  is isomorphic (`Stacks.FiniteMorphismProjective.baseTransport`), which carries the immersion to
  one into `𝐏ⁿ_S` for the given affine `S`, compatibly with the structure morphisms.
* The immersion is a closed immersion because `f` is finite and `𝐏ⁿ_S ⟶ S` is separated:
  `Stacks.FiniteMorphismProjective.isClosedImmersion_of_isImmersion` of
  `StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Separated`, which is the source's last
  paragraph.

## Main definitions

* `Stacks.FiniteMorphismProjective.baseTransport`: the comparison of projective spaces over
isomorphic bases.
* `Stacks.FiniteMorphismProjective.chartImmersion`: the morphism `Spec A ⟶ Proj R[T₀, …, Tₙ]`
  attached to a family of elements of `A`, through the standard affine chart `D₊(T₀)`.

## Main results

* `Stacks.FiniteMorphismProjective.isHProjective_of_isFinite_of_isAffine`: **a finite morphism over
  an affine base is H-projective** — the content of Stacks Tag 0B3I over an affine base, at the
  stronger conclusion.
* `Stacks.FiniteMorphismProjective.isHProjective_morphismRestrict` and
  `Stacks.FiniteMorphismProjective.exists_openCover_isHProjective`: **over an arbitrary base, a
  finite morphism is H-projective over every affine open of the base, and hence over the members of
  an open cover** — the shape of Tag 01W8's "locally projective", with projectivity read
  H-projectively.
* `Stacks.FiniteMorphismProjective.isImmersion_chartImmersion`,
  `Stacks.FiniteMorphismProjective.chartImmersion_projToSpecCoeff`: the chart morphism is an
  immersion when the family generates, and it is a morphism over the base.
* `Stacks.FiniteMorphismProjective.isIso_baseTransport`: the comparison over isomorphic bases is an
isomorphism.

## Implementation notes

**The generators are indexed by the nonzero variables, not by `Fin n`.** The chart identification
of `Stacks.AlgebraicGeometry.ProjPolyChart` is stated for the subtype `{j : Fin (n + 1) // j ≠ i}`
of the variables other than the one inverted, so the generating family is reindexed along
`Fin.pred` rather than a bijection with `Fin n` being chosen; the reindexing is surjective onto
the generators, which is all the spanning hypothesis needs.

**The algebra structure on `Γ(X, 𝒪_X)` is the one attached to `f`**, by
`RingHom.toAlgebra` applied to the ring map of global sections. It is introduced inside the proof,
so no statement of this file carries it, and `Stacks.FiniteMorphismProjective.chartImmersion` is
stated for an arbitrary `R`-algebra `A` instead.

**Projective space is a pullback, so the base comparison is a lift.** `𝐏ⁿ_S` is
`AlgebraicGeometry.projectiveSpaceOver`, a fibre product of `S` and the integral model over the
terminal scheme, so an isomorphism of bases induces one of projective spaces by the universal
property, with the two triangles holding by `Limits.pullback.lift_fst` and `lift_snd`.

## Relation to Tag 0B3I over an arbitrary base

The statements here carry a hypothesis the tag does not: the base is affine, or the conclusion is
about the restriction of `f` over an affine open. Over an arbitrary base the tag is
`Stacks.FiniteMorphismProjective.isProjective_of_isFinite`, whose closed immersion into
`𝐏(f_*𝒪_X)` is `Stacks.FiniteMorphismProjective.embedding`; it is built from the same chart
argument, read directly in the charts of the projective bundle rather than in `𝐏ⁿ_S`.

## References

* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.FiniteMorphismProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Projective space is functorial in isomorphisms of the base -/

/-- The comparison of projective spaces over isomorphic bases. -/
public def baseTransport (n : ℕ) {S T : Scheme.{u}} (e : S ≅ T) :
    projectiveSpaceOver n S ⟶ projectiveSpaceOver n T :=
  pullback.lift (pullback.fst _ _ ≫ e.hom) (pullback.snd _ _) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] public theorem baseTransport_fst (n : ℕ) {S T : Scheme.{u}}
    (e : S ≅ T) :
    baseTransport n e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] public theorem baseTransport_snd (n : ℕ) {S T : Scheme.{u}}
    (e : S ≅ T) :
    baseTransport n e ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

public instance isIso_baseTransport (n : ℕ) {S T : Scheme.{u}} (e : S ≅ T) :
    IsIso (baseTransport n e) := by
  refine ⟨baseTransport n e.symm, ?_, ?_⟩ <;>
    refine pullback.hom_ext ?_ ?_ <;>
    simp

/-! ### The immersion into the polynomial model -/

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)
  (a : {j : Fin (n + 1) // j ≠ 0} → A)

/-- The morphism `Spec A ⟶ Proj R[T₀, …, Tₙ]` attached to a family of elements of `A`. -/
public def chartImmersion : Spec (CommRingCat.of A) ⟶ Proj (polyGrading R n) :=
  Spec.map (CommRingCat.ofHom (awayEval R A n a)) ≫
    Proj.awayι (polyGrading R n) (MvPolynomial.X 0) (X_mem_one R n 0) Nat.one_pos

/-- The closed immersion of `Spec A` into the standard affine chart of `Proj R[T₀, …, Tₙ]`
attached to a generating family: `Spec` of a surjection of rings. -/
public theorem isClosedImmersion_specMap_awayEval
    (hgen : Submodule.span R (Set.range a) = ⊤) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (awayEval R A n a))) :=
  IsClosedImmersion.spec_of_surjective _ (awayEval_surjective R A n a hgen)

/-- **The chart morphism is an immersion** when the family generates `A` as an `R`-module: a
closed immersion into the standard affine chart followed by the open immersion of that chart into
`Proj R[T₀, …, Tₙ]`. -/
public theorem isImmersion_chartImmersion (hgen : Submodule.span R (Set.range a) = ⊤) :
    IsImmersion (chartImmersion R A n a) := by
  have := isClosedImmersion_specMap_awayEval R A n a hgen
  exact inferInstanceAs (IsImmersion (_ ≫ _))

/-- **The chart morphism is a morphism over the base**: composed with the structure morphism of
`Proj R[T₀, …, Tₙ]` it is `Spec` of the structure map of the algebra. No hypothesis on the family
is needed. -/
@[reassoc] public theorem chartImmersion_projToSpecCoeff :
    chartImmersion R A n a ≫ projToSpecCoeff R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  have hring : (awayEval R A n a).comp
      ((fromZeroRingHom (polyGrading R n)
          (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1))))).comp
        ((GradedRing.projZeroRingHom' (polyGrading R n)).comp
          (algebraMap R (MvPolynomial (Fin (n + 1)) R)))) = algebraMap R A := by
    refine RingHom.ext fun r => ?_
    have h0 := DFunLike.congr_fun (projZeroRingHom'_comp_algebraMap R n) r
    rw [RingHom.comp_apply] at h0
    simp only [RingHom.comp_apply, h0]
    exact awayEval_coeffToAway R A n a r
  rw [chartImmersion, projToSpecCoeff, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]

/-! ### A finite morphism over an affine base -/

/-- **A finite morphism over an affine base is H-projective**: it factors as a closed immersion
into `𝐏ⁿ_S` over `S`, for `n + 1` the number of generators of `Γ(X, 𝒪_X)` as a
`Γ(S, 𝒪_S)`-module. This is the content of Stacks Tag 0B3I over an affine base, at the stronger
of the two conclusions Tag 01W8 offers; see the module documentation for what separates it from
the tag. -/
public theorem isHProjective_of_isFinite_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsFinite f] : Stacks.HProjective.IsHProjective f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let _ : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := (f.appTop).hom.toAlgebra
  have : Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.finite_appTop
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := ↥Γ(S, ⊤)) (M := ↥Γ(X, ⊤))
  set a : {j : Fin (n + 1) // j ≠ 0} → ↥Γ(X, ⊤) := fun j => g (j.1.pred j.2) with ha
  have hgen : Submodule.span ↥Γ(S, ⊤) (Set.range a) = ⊤ := by
    rw [show Set.range a = Set.range g from Set.Subset.antisymm
      (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
      (by
        rintro _ ⟨k, rfl⟩
        exact ⟨⟨k.succ, Fin.succ_ne_zero k⟩, by simp [ha]⟩)]
    exact hg
  have hmap : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop := by
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  set i : X ⟶ projectiveSpaceOver n S := X.isoSpec.hom ≫
    chartImmersion ↥Γ(S, ⊤) ↥Γ(X, ⊤) n a ≫
      projCompare ↥Γ(S, ⊤) n ≫ baseTransport n S.isoSpec.symm with hi
  have hover : i ≫ (projectiveSpaceOver n S ↘ S) = f := by
    rw [Stacks.HProjective.over_projectiveSpaceOver, hi]
    simp only [Category.assoc, baseTransport_fst]
    rw [reassoc_of% projCompare_fst, chartImmersion_projToSpecCoeff_assoc, hmap, Iso.symm_hom,
      ← Category.assoc, Iso.comp_inv_eq, Scheme.isoSpec_hom, Scheme.isoSpec_hom]
    exact (Scheme.toSpecΓ_naturality f).symm
  have himm : IsImmersion i := by
    have := isImmersion_chartImmersion ↥Γ(S, ⊤) ↥Γ(X, ⊤) n a hgen
    rw [hi]
    infer_instance
  have : IsFinite (i ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hover]; infer_instance
  exact ⟨n, i, isClosedImmersion_of_isImmersion i (projectiveSpaceOver n S ↘ S), hover⟩

/-! ### An arbitrary base, locally -/

/-- **A finite morphism is H-projective over every affine open of its base.** The restriction of
a finite morphism is finite, and an affine open is an affine scheme. -/
@[ega "II 6.1.11" "special case"]
public theorem isHProjective_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (V : S.affineOpens) : Stacks.HProjective.IsHProjective (f ∣_ (V : S.Opens)) :=
  have : IsAffine (V : S.Opens).toScheme := V.2
  isHProjective_of_isFinite_of_isAffine _

/-- **A finite morphism is H-projective over the members of an open cover of its base**, namely
the affine cover. This is the shape of Tag 01W8's "locally projective" — the base change of `f`
along each member of a cover of the base is projective — with projectivity read as
H-projectivity. -/
public theorem exists_openCover_isHProjective {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    ∃ 𝒰 : Scheme.OpenCover.{u} S,
      ∀ i : 𝒰.I₀, Stacks.HProjective.IsHProjective (pullback.snd f (𝒰.f i)) :=
  ⟨S.affineCover, fun _ => isHProjective_of_isFinite_of_isAffine _⟩

end Stacks.FiniteMorphismProjective

end
