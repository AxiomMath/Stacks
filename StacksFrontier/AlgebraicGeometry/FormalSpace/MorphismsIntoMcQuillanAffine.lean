module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.UniformGenerators
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillanRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteRepresentableOverAffineFormal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.StageEtaleSystem
public import StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit

/-!
# Morphisms of affine formal algebraic spaces into a McQuillan one (Stacks 0AJK)

Let `A` be a weakly admissible topological ring and let `(I_λ)` be a fundamental system of weak
ideals of definition of `A`, so that `X = Spf(A)` is a McQuillan affine formal algebraic space,
and let `f : Y ⟶ X` be a morphism of affine formal algebraic spaces. **Stacks 0AJK** is a
remark consisting of four numbered items. Each of them makes assertions and raises questions;
this file proves the assertions of each item, one declaration per item.

1. If `f` is a closed immersion, then `Y` is McQuillan and `f` corresponds to a continuous
   homomorphism `φ : A ⟶ B` of weakly admissible topological rings which is taut, has closed
   kernel and has dense image (Stacks 0ANQ).
2. This item is a question in its entirety (which conditions on `A` make every closed immersion
   into `X` the spectrum of a quotient `A ⟶ A/K` by a closed ideal); it asserts nothing.
3. If `f` is of finite type, then `Y = colim Spec(B_λ)` for the object `(B_λ)` of the category
   `𝒞` of Stacks 0AL1 that corresponds to `f`, and a single integer `r` bounds the number of
   generators of `B_λ` over `A/I_λ` for every `λ`. (The question whether `Y` is McQuillan is
   asserted nowhere.)
4. If `f` is of finite type and `Y` is McQuillan, then `f` corresponds to a continuous
   homomorphism `φ : A ⟶ B` of weakly admissible topological rings which is taut and makes `B`
   topologically of finite type over `A` (Stacks 0ANT); in other words `f` factors as
   `Y ⟶ 𝔸ʳ_X ⟶ X` with the first arrow a closed immersion of McQuillan affine formal algebraic
   spaces.

## Main results

* `FormalSpace.exists_formalSpectrumMap_of_relative_isAffineHom`: a morphism from a McQuillan
  affine formal algebraic space into a formal spectrum which is relatively affine is the formal
  spectrum of a continuous homomorphism.
* `FormalSpace.exists_taut_formalSpectrumMap_of_isClosedImmersion`: **Stacks 0AJK**, part (1).
* `FormalSpace.exists_finiteTypeAlgebraSystem_uniform_generatedBy`: **Stacks 0AJK**, part (3).
* `FormalSpace.exists_taut_isTopologicallyOfFiniteType_affineSpace_factorization`:
  **Stacks 0AJK**, part (4).

## Implementation notes

`X = Spf(A)` is `formalSpectrum D` for a quotient system `D` placing the quotient spectra of `A`
over `S`. In every part the statement asks of `X` only that it is an affine formal algebraic
space, which is what the remark's "morphism of affine formal algebraic spaces" says; part (1)
asks nothing of `Y` beyond being an fppf sheaf, the closed immersion making it a formal algebraic
space; so does part (4), and that `𝔸ʳ_X` is then an affine formal algebraic space in the same
site is proved, with no condition on the size of the site
(`isAffineFormalAlgebraicSpace_formalSpectrum_completionOver`).

McQuillan is condition (4) of Stacks 0AIC, `HasSomeSurjectivePresentation`. In parts (1) and (4)
the homomorphism `φ` is produced by identifying `Y` with `Spf B`: a relatively affine morphism
into `Spf A` pulls the canonical presentation of `Spf A` back to a presentation of `Y` by affine
thickenings indexed by the weak ideals of definition of `A`, whose section-ring projections are
surjective because `Y` is McQuillan (Stacks 0AIC, (4) ⟹ (5)); the limit of the section rings is
weakly admissible and presents `Y`, and Stacks 0AN0 turns `f` into `φ`. In part (4) the
relative affineness is Stacks 0AKN, a finite type morphism being representable by algebraic
spaces.

In part (3) the object `(B_λ)` of `𝒞` is the one that the anti-equivalence of Stacks 0AL1,
`finiteTypeAlgebraSystemAntiEquivalence`, sends to `f`; that functor sends an inverse system to
the colimit of the spectra of its terms, which is the remark's `Y = colim Spec(B_λ)`. The
uniform bound is `FiniteTypeAlgebraSystem.exists_uniform_generatedBy`.

In part (4) the affine space `𝔸ʳ_X` is `Spf A{x₁, …, xᵣ}`, the formal spectrum of the
completion `lim_I (A/I)[x₁, …, xᵣ]` of the polynomial ring over the weak ideals of definition of
`A`, mapping to `X` by `Spf` of the canonical homomorphism; the factorization and the closed
immersion are `exists_isClosedImmersion_affineSpace_factorization`.

## References

* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AL1](https://stacks.math.columbia.edu/tag/0AL1)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0ANQ](https://stacks.math.columbia.edu/tag/0ANQ)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The formal spectrum of a weakly admissible topological ring, when it is an affine formal
algebraic space, is a McQuillan one: Stacks 0AIC, (1) ⟹ (4). -/
theorem hasSomeSurjectivePresentation_formalSpectrum_of_isAffine
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D)) :
    HasSomeSurjectivePresentation B S hS (formalSpectrum D) :=
  (hasAllSurjectivePresentations_formalSpectrum hA D hX.1).hasSomeSurjectivePresentation

attribute [local instance] sheaf_hasColimits in
/-- **A relatively affine morphism from a McQuillan affine formal algebraic space into a formal
spectrum is the formal spectrum of a continuous homomorphism.** Let `f : Y ⟶ Spf A` be a
morphism of fppf sheaves over `S` whose base changes along represented sheaves are affine,
with `Y` McQuillan. Then `Y ≅ Spf B` for a weakly admissible topological ring `B` over `S`,
and `f` is `Spf` of a continuous homomorphism `A ⟶ B` read through that identification.

The canonical presentation of `Spf A` by its quotient spectra pulls back along `f` to a
presentation of `Y` by affine thickenings indexed by the weak ideals of definition of `A`; its
section-ring projections are surjective because `Y` is McQuillan, so the limit of its section
rings is weakly admissible and presents `Y`, and Stacks 0AN0 produces the homomorphism. -/
theorem exists_formalSpectrumMap_of_relative_isAffineHom
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {Y : FppfSheaf B S hS}
    (hYM : HasSomeSurjectivePresentation B S hS Y) (f : Y ⟶ formalSpectrum D)
    (hfAffine : (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (E : QuotientSystem B S hS C),
      TopologicalRing.IsWeaklyAdmissible C ∧
        ∃ (e : Y ≅ formalSpectrum E) (g : ContinuousHom D E),
          f = e.hom ≫ formalSpectrumMap hA g := by
  classical
  let I₀ := { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }
  let W := OrderDual I₀
  let _ : Nonempty W := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  let _ : IsDirected W (· ≤ ·) := TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  let I := ULift.{u + 1} W
  let eOrder : W ≃o I :=
    { toEquiv := Equiv.ulift.symm
      map_rel_iff' := Iff.rfl }
  let eI : W ≌ I := eOrder.equivalence
  let _ : Nonempty I := ⟨ULift.up (Classical.arbitrary W)⟩
  let _ : IsDirected I (· ≤ ·) := ⟨fun i j ↦
    let ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.down j.down
    ⟨ULift.up k, hik, hjk⟩⟩
  let Hs := BigAffineFppf.inclusion B S hS
  let Gs := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let d := eI.inverse ⋙ D.diagram
  let dcol : formalSpectrum D ≅ colimit (d ⋙ Hs ⋙ Gs) := HasColimit.isoOfEquivalence eI
    (Functor.isoWhiskerRight eI.unitIso.symm (D.diagram ⋙ Hs ⋙ Gs))
  obtain ⟨E, p, hYcol, hcart⟩ :=
    exists_affine_pullback_presentation B S hS f hfAffine d dcol
  have hEthick : ∀ ⦃i j : I⦄ (φ : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map φ)) :=
    isThickening_of_cartesian_presentation B S hS f d E p dcol hYcol hcart
      fun _ _ φ ↦ D.isThickening_map_diagram (eI.inverse.map φ)
  have hEproj : HasSurjectiveSectionProjections B S hS E :=
    (HasSomeSurjectivePresentation.hasAllSurjectivePresentations B S hS hYM).2 I inferInstance
      E hEthick ⟨hYcol⟩
  let R : W → Type u := fun w ↦
    Γ((BigAffineFppf.toScheme B S hS).obj (E.obj (ULift.up w)), ⊤)
  let t : ∀ ⦃w w' : W⦄, w ≤ w' → R w' →+* R w := fun {w w'} h ↦
    (((BigAffineFppf.toScheme B S hS).map
      (E.map (homOfLE (show (ULift.up w : I) ≤ ULift.up w' from h)))).appTop).hom
  have hnil : ∀ ⦃w w' : W⦄ (h : w ≤ w'), (RingHom.ker (t h)).LocallyNilpotent :=
    fun {w w'} h _ ha ↦ (hEthick (homOfLE (show (ULift.up w : I) ≤ ULift.up w' from h))
      ).isNilpotent_of_mem_ker_appTop_of_compactSpace ha
  have hprojsurj : ∀ w : W,
      Function.Surjective (TopologicalRing.DirectedLimit.proj t w) := by
    intro w x
    obtain ⟨s, hs⟩ := hEproj (ULift.up w) x
    exact ⟨⟨fun w' ↦ s.1 (Opposite.op (ULift.up w')), fun w₁ w₂ h ↦
      s.2 (homOfLE (show (ULift.up w₁ : I) ≤ ULift.up w₂ from h)).op⟩, hs⟩
  have hC : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.DirectedLimit t) :=
    TopologicalRing.DirectedLimit.isWeaklyAdmissible t hnil
  let P : DirectedQuotients B S hS Y (TopologicalRing.DirectedLimit t) I :=
    { diagram := E
      isThickening := hEthick
      colimitIso := hYcol
      proj := fun i ↦ TopologicalRing.DirectedLimit.proj t i.down
      proj_surjective := fun i ↦ hprojsurj i.down
      proj_comp := fun {i j} h ↦ RingHom.ext fun a ↦
        TopologicalRing.DirectedLimit.t_proj t (show i.down ≤ j.down from h) a
      isWeakIdealOfDefinition_ker := fun i ↦
        TopologicalRing.DirectedLimit.isWeakIdealOfDefinition_ker t hnil i.down
      hasBasis_nhds_zero := (TopologicalRing.DirectedLimit.hasBasis_nhds_zero t).to_hasBasis
        (fun w _ ↦ ⟨ULift.up w, trivial, subset_rfl⟩) fun i _ ↦ ⟨i.down, trivial, subset_rfl⟩ }
  obtain ⟨E', ⟨e⟩⟩ := P.exists_quotientSystem_formalSpectrum_iso
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hC (e.inv ≫ f)
  exact ⟨TopologicalRing.DirectedLimit t, inferInstance, inferInstance, inferInstance,
    inferInstance, E', hC, e, g, by rw [hg, Iso.hom_inv_id_assoc]⟩

/-- If `f = e.hom ≫ h` for an isomorphism `e`, then `h` is a base change of `f` along `𝟙`. -/
private theorem isPullback_inv_of_eq_hom_comp {Y Z X : FppfSheaf B S hS} (e : Y ≅ Z) (f : Y ⟶ X)
    (h : Z ⟶ X) (hfg : f = e.hom ≫ h) : IsPullback e.inv h f (𝟙 X) :=
  IsPullback.of_horiz_isIso ⟨by simp [hfg]⟩

/-- **Stacks 0AJK, part (1).** Let `A` be a weakly admissible topological ring over `S` whose
formal spectrum `X = Spf(A)` is an affine formal algebraic space, and let `f : Y ⟶ X` be a
closed immersion. Then `Y` is a McQuillan affine formal algebraic space, and `f` corresponds to
a continuous homomorphism `φ : A ⟶ B` of weakly admissible topological rings — `Y` is
identified with `Spf(B)` and `f` with `Spf(φ)` — which is taut, whose kernel is a closed ideal
of `A`, and whose image is dense in `B`. -/
@[stacks 0AJK "part (1), every assertion of the item: for a closed immersion `f : Y → X` into \
`X = Spf(A)`, the source `Y` is McQuillan (condition (4) of Stacks 0AIC) and `f` corresponds to \
a continuous homomorphism `φ : A → B` of weakly admissible topological rings, `Y ≅ Spf(B)` with \
`f = Spf(φ)` through that isomorphism, which is taut, has closed kernel `K` and has dense \
image. The source `Y` is an arbitrary fppf sheaf here, which generalizes the item's affine \
formal algebraic space. The question the item ends with, which conditions on `A` force \
`B = (A/K)^∧`, is a question and is asserted nowhere. Part (2) of the remark is a question in \
its entirety and asserts nothing."]
theorem exists_taut_formalSpectrumMap_of_isClosedImmersion
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    {Y : FppfSheaf B S hS} (f : Y ⟶ formalSpectrum D) (hf : IsClosedImmersion B S hS f) :
    HasSomeSurjectivePresentation B S hS Y ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
        (_ : IsLinearTopology C C) (E : QuotientSystem B S hS C),
        TopologicalRing.IsWeaklyAdmissible C ∧
          ∃ (e : Y ≅ formalSpectrum E) (g : ContinuousHom D E),
            f = e.hom ≫ formalSpectrumMap hA g ∧ RingHom.IsTaut g.toRingHom ∧
              IsClosed (RingHom.ker g.toRingHom : Set A) ∧ DenseRange g.toRingHom := by
  have hY : IsFormalAlgebraicSpace B S hS Y :=
    isFormalAlgebraicSpace_of_relativelyRepresentable_over_affineFormal B S hS f hX
      (isClosedImmersionInto_of_isClosedImmersion B S hS f hf).rep
  refine ⟨hasSomeSurjectivePresentation_of_isClosedImmersion B S hS
    (hasSomeSurjectivePresentation_formalSpectrum_of_isAffine B S hS hA D hX) hY f hf, ?_⟩
  obtain ⟨C, _, _, _, _, E, hC, e, g, hfg⟩ :=
    exists_formalSpectrumMap_of_isClosedImmersion B S hS hA D hY f hf
  have hg : IsClosedImmersion B S hS (formalSpectrumMap hA g) :=
    isClosedImmersion_of_isPullback B S hS (isPullback_inv_of_eq_hom_comp B S hS e f _ hfg) hf
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, E, hC, e, g, hfg,
    isTaut_of_isClosedImmersion_formalSpectrumMap hA hC g hg, isClosed_ker_toRingHom hC g,
    denseRange_of_isClosedImmersion_formalSpectrumMap hA hC g hg⟩

/-- **Stacks 0AJK, part (3).** Let `A` be a weakly admissible topological ring over `S` whose
formal spectrum `X = Spf(A)` is an affine formal algebraic space, let `(I_λ)` be a fundamental
system of weak ideals of definition of `A`, and let `f : Y ⟶ X` be a morphism of finite type
from an affine formal algebraic space. Then `Y = colim Spec(B_λ)` for an object `(B_λ)` of the
category `𝒞` of Stacks 0AL1 — the inverse system which the anti-equivalence of Stacks 0AL1
sends to `f` — and there is a single integer `r` such that `B_λ` is generated by `r` elements
over `A/I_λ` for every `λ`. -/
@[stacks 0AJK "part (3), every assertion of the item: a finite type morphism `f : Y → X` of \
affine formal algebraic spaces with `X = Spf(A)` gives `Y = colim Spec(B_λ)` for an object \
`(B_λ)` of the category `𝒞` of Stacks 0AL1, namely the object the anti-equivalence of Stacks \
0AL1 sends to `f` (that functor is the colimit of the spectra of the terms), and one integer \
`r` generates every `B_λ` over `A/I_λ`. The question the item ends with, whether there is an \
example in which `Y` is not McQuillan, is a question and is asserted nowhere."]
theorem exists_finiteTypeAlgebraSystem_uniform_generatedBy
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    {Y : FppfSheaf B S hS} (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (f : Y ⟶ formalSpectrum D) (hf : IsFiniteType B S hS f) :
    ∃ P : FiniteTypeAlgebraSystem A I J,
      Nonempty ((finiteTypeAlgebraSystemAntiEquivalence B S hS A hA (formalSpectrum D)
          (hasSomeSurjectivePresentation_formalSpectrum_of_isAffine B S hS hA D hX)
          D.weakIdealColimitPresentation I J).functor.obj (Opposite.op P) ≅
            ⟨Over.mk f, hY, hf⟩) ∧
        ∃ r : ℕ, ∀ i : I, P.GeneratedBy r i := by
  let e := finiteTypeAlgebraSystemAntiEquivalence B S hS A hA (formalSpectrum D)
    (hasSomeSurjectivePresentation_formalSpectrum_of_isAffine B S hS hA D hX)
    D.weakIdealColimitPresentation I J
  let P := (e.inverse.obj ⟨Over.mk f, hY, hf⟩).unop
  exact ⟨P, ⟨e.counitIso.app _⟩, P.exists_uniform_generatedBy⟩

/-- **Stacks 0AJK, part (4).** Let `A` be a weakly admissible topological ring over `S` whose
formal spectrum `X = Spf(A)` is an affine formal algebraic space, and let `f : Y ⟶ X` be a
morphism of finite type with `Y` a McQuillan affine formal algebraic space. Then `f`
corresponds to a continuous homomorphism `φ : A ⟶ B` of weakly admissible topological rings —
`Y` is identified with `Spf(B)` and `f` with `Spf(φ)` — which is taut and makes `B`
topologically of finite type over `A`. In other words `f` factors as
`Y ⟶ 𝔸ʳ_X ⟶ X`, where `𝔸ʳ_X = Spf A{x₁, …, xᵣ}` maps to `X` by `Spf` of the canonical
homomorphism and the first arrow is a closed immersion of McQuillan affine formal algebraic
spaces. -/
@[stacks 0AJK "part (4), every assertion of the item: for a finite type `f : Y → X = Spf(A)` \
with `Y` McQuillan, `f` corresponds to a continuous homomorphism `φ : A → B` of weakly \
admissible topological rings, `Y ≅ Spf(B)` with `f = Spf(φ)` through that isomorphism; `φ` is \
taut, which is derived from `f` being of finite type through Stacks 0AN5 and 0AKN; `B` is \
topologically of finite type over `A`; and `f` factors as `Y → 𝔸ʳ_X → X` with \
`𝔸ʳ_X = Spf A{x_1, ..., x_r}` the formal spectrum of the completion of `A[x_1, ..., x_r]` over \
the weak ideals of definition of `A`, the second arrow `Spf` of the canonical map and the first \
a closed immersion, both its source and its target being McQuillan affine formal algebraic \
spaces. The item's closing remark that questions (1) and (2) are then in force for \
`Y → 𝔸ʳ_X` asserts nothing further."]
theorem exists_taut_isTopologicallyOfFiniteType_affineSpace_factorization
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    {Y : FppfSheaf B S hS} (hYM : HasSomeSurjectivePresentation B S hS Y)
    (f : Y ⟶ formalSpectrum D) (hf : IsFiniteType B S hS f) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C) (E : QuotientSystem B S hS C),
      TopologicalRing.IsWeaklyAdmissible C ∧
        ∃ (e : Y ≅ formalSpectrum E) (g : ContinuousHom D E),
          f = e.hom ≫ formalSpectrumMap hA g ∧ RingHom.IsTaut g.toRingHom ∧
            TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom ∧
            ∃ (r : ℕ) (E' : QuotientSystem B S hS
                (TopologicalRing.CompletionOver (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)))
              (π : ContinuousHom D E') (ι : ContinuousHom E' E),
              π.toRingHom = TopologicalRing.CompletionOver.canonicalMap MvPolynomial.C ∧
                HasSomeSurjectivePresentation B S hS (formalSpectrum E') ∧
                IsClosedImmersion B S hS (formalSpectrumMap
                  (TopologicalRing.completionOver_isWeaklyAdmissible MvPolynomial.C hA) ι) ∧
                f = e.hom ≫ formalSpectrumMap
                  (TopologicalRing.completionOver_isWeaklyAdmissible MvPolynomial.C hA) ι ≫
                    formalSpectrumMap hA π := by
  obtain ⟨C, _, _, _, _, E, hC, e, g, hfg⟩ :=
    exists_formalSpectrumMap_of_relative_isAffineHom B S hS hA D hYM f
      (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hYM.1 hX hf.1)
  have hFT : IsFiniteType B S hS (formalSpectrumMap hA g) := by
    exact IsFiniteType.of_isPullback B S hS
      (isPullback_inv_of_eq_hom_comp B S hS e f _ hfg).flip hf
  obtain ⟨ht, hft⟩ := isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    B S hS hA hC D E g hX (isAffineFormalAlgebraicSpace_of_iso B S hS e hYM.1) hFT
  obtain ⟨r, E', π, ι, hπ, -, hE'M, -, -, hι, hcomp⟩ :=
    exists_isClosedImmersion_affineSpace_factorization B S hS hA hC D hX E g ht hft
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, E, hC, e, g, hfg, ht,
    hft, r, E', π, ι, hπ, hE'M, hι, by rwa [hcomp]⟩

end AlgebraicGeometry.FormalSpace

end
